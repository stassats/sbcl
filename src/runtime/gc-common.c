/*
 * Garbage Collection common functions for scavenging, moving and sizing
 * objects.  These are for use with both GC (stop & copy GC) and GENCGC
 */

/*
 * This software is part of the SBCL system. See the README file for
 * more information.
 *
 * This software is derived from the CMU CL system, which was
 * written at Carnegie Mellon University and released into the
 * public domain. The software is in the public domain and is
 * provided with absolutely no warranty. See the COPYING and CREDITS
 * files for more information.
 */

/*
 * For a review of garbage collection techniques (e.g. generational
 * GC) and terminology (e.g. "scavenging") see Paul R. Wilson,
 * "Uniprocessor Garbage Collection Techniques". As of 20000618, this
 * had been accepted for _ACM Computing Surveys_ and was available
 * as a PostScript preprint through
 *   <http://www.cs.utexas.edu/users/oops/papers.html>
 * as
 *   <ftp://ftp.cs.utexas.edu/pub/garbage/bigsurv.ps>.
 */

#include <stdio.h>
#include <signal.h>
#include <string.h>
#include "sbcl.h"
#include "runtime.h"
#include "os.h"
#include "interr.h"
#include "globals.h"
#include "interrupt.h"
#include "validate.h"
#include "lispregs.h"
#include "arch.h"
#include "gc.h"
#include "hopscotch.h"
#include "genesis/primitive-objects.h"
#include "genesis/static-symbols.h"
#include "genesis/layout.h"
#include "genesis/hash-table.h"
#define WANT_SCAV_TRANS_SIZE_TABLES
#include "gc-internal.h"
#include "gc-private.h"
#include "forwarding-ptr.h"
#include "var-io.h"

#ifdef LISP_FEATURE_SPARC
#define LONG_FLOAT_SIZE 4
#elif defined(LISP_FEATURE_X86) || defined(LISP_FEATURE_X86_64)
#define LONG_FLOAT_SIZE 3
#endif

os_vm_size_t dynamic_space_size = DEFAULT_DYNAMIC_SPACE_SIZE;
os_vm_size_t thread_control_stack_size = DEFAULT_CONTROL_STACK_SIZE;

sword_t (*scavtab[256])(lispobj *where, lispobj object);
static lispobj (*transother[64])(lispobj object);
sword_t (*sizetab[256])(lispobj *where);
struct weak_pointer *weak_pointers;

os_vm_size_t bytes_consed_between_gcs = 12*1024*1024;

/// These sizing macros return the number of *payload* words,
/// exclusive of the object header word. Payload length is always
/// an odd number so that total word count is an even number.

/* Each size category is designed to allow 1 bit for a GC mark bit,
 * possibly some flag bits, and the payload length in words.
 * There are three size categories for most non-vector objects,
 * differing in how many flag bits versus size bits there are.
 * The GC mark bit is always in bit index 31 of the header regardless of
 * machine word size.  Bit index 31 is chosen for consistency between 32-bit
 * and 64-bit machines. It is a natural choice for 32-bit headers by avoiding
 * intererence with other header fields. It is also chosen for 64-bit headers
 * because the upper 32 bits of headers for some objects are already occupied
 * by other data: symbol TLS index, instance layout, etc.
 */

/* The largest payload count is expressed in 23 bits. These objects
 * can't reside in immobile space as there is no room for generation bits.
 * All sorts of objects fall into this category, but mostly due to inertia.
 * There are no non-vector boxed objects whose size should be so large.
 * Header:   size |    tag
 *          -----   ------
 *        23 bits | 8 bits
 */
#define BOXED_NWORDS(obj) ((HeaderValue(obj) & 0x7FFFFF) | 1)

/* Medium-sized payload count is expressed in 15 bits. Objects in this category
 * may reside in immobile space: CODE, CLOSURE, INSTANCE, FUNCALLABLE-INSTANCE.
 * The single data bit is used as a closure's NAMED flag.
 *
 * Header:  gen# |  data |     size |    tag
 *         -----   -----    -------   ------
 *        8 bits | 1 bit |  15 bits | 8 bits
 */
#define SHORT_BOXED_NWORDS(obj) ((HeaderValue(obj) & SHORT_HEADER_MAX_WORDS) | 1)

/* Tiny payload count is expressed in 8 bits. Objects in this size category
 * can reside in immobile space: SYMBOL, FDEFN.
 * Header:  gen# | flags |   size |    tag
 *         -----   ------  ------   ------
 *        8 bits   8 bits  8 bits | 8 bits
 * FDEFN  flag bits: 1 bit for statically-linked
 * SYMBOL flag bits: 1 bit for present in initial core image
 */
#define TINY_BOXED_NWORDS(obj) ((HeaderValue(obj) & 0xFF) | 1)

/*
 * copying objects
 */

/* gc_general_copy_object is inline from gc-internal.h */

/* to copy a boxed object */
lispobj
copy_object(lispobj object, sword_t nwords)
{
    return gc_general_copy_object(object, nwords, BOXED_PAGE_FLAG);
}

static void (*scav_ptr[4])(lispobj *where, lispobj object); /* forward decl */

static inline void scav1(lispobj* object_ptr, lispobj object)
{
    // GENCGC only:
    // * With 32-bit words, is_lisp_pointer(object) returns true if object_ptr
    //   points to a forwarding pointer, so we need a sanity check inside the
    //   branch for is_lisp_pointer(). For maximum efficiency, check that only
    //   after from_space_p() returns false, so that valid pointers into
    //   from_space incur no extra test. This could be improved further by
    //   skipping the FP check if 'object' points within dynamic space, i.e.,
    //   when find_page_index() returns >= 0. That would entail injecting
    //   from_space_p() explicitly into the loop, so as to separate the
    //   "was a page found at all" condition from the page generation test.

    // * With 64-bit words, is_lisp_pointer(object) is false when object_ptr
    //   points to a forwarding pointer, and the fixnump() test also returns
    //   false, so we'll indirect through scavtab[]. This will safely invoke
    //   scav_lose(), detecting corruption without any extra cost.
    //   The major difference between that and the explicit test is that you
    //   won't see 'start' and 'n_words', but if you need those, chances are
    //   you'll want to run under an external debugger in the first place.
    //   [And btw it sure would be nice to assert statically
    //   that is_lisp_pointer(0x01) is indeed false]

#define FIX_POINTER() { \
    lispobj *ptr = native_pointer(object); \
    if (forwarding_pointer_p(ptr)) \
        *object_ptr = LOW_WORD(forwarding_pointer_value(ptr)); \
    else /* Scavenge that pointer. */ \
        scav_ptr[(object>>(N_LOWTAG_BITS-2))&3](object_ptr, object); \
    }
#ifdef LISP_FEATURE_IMMOBILE_SPACE
    page_index_t page;
    // It would be fine, though suboptimal, to use from_space_p() here.
    // If it returns false, we don't want to call immobile_space_p()
    // unless the pointer is *not* into dynamic space.
    if ((page = find_page_index((void*)object)) >= 0) {
        if (page_table[page].gen == from_space && !pinned_p(object, page))
            FIX_POINTER();
    } else if (immobile_space_p(object)) {
        lispobj *ptr = native_pointer(object);
        if (immobile_obj_gen_bits(ptr) == from_space)
            enliven_immobile_obj(ptr, 1);
    }
#else
    if (from_space_p(object)) {
        FIX_POINTER();
    } else {
#if (N_WORD_BITS == 32) && defined(LISP_FEATURE_GENCGC)
        if (forwarding_pointer_p(object_ptr))
          lose("unexpected forwarding pointer in scavenge @ %p\n",
               object_ptr);
#endif
        /* It points somewhere other than oldspace. Leave it
         * alone. */
    }
#endif
}

inline void gc_scav_pair(lispobj where[2])
{
    lispobj object = where[0];
    if (is_lisp_pointer(object))
        scav1(where, object);
    object = where[1];
    if (is_lisp_pointer(object))
        scav1(where+1, object);
}

// Scavenge a block of memory from 'start' to 'end'
// that may contain object headers.
void heap_scavenge(lispobj *start, lispobj *end)
{
    lispobj *object_ptr;

    for (object_ptr = start; object_ptr < end;) {
        lispobj object = *object_ptr;
        if (other_immediate_lowtag_p(object))
            /* It's some sort of header object or another. */
            object_ptr += (scavtab[widetag_of(object)])(object_ptr, object);
        else {  // it's a cons
            gc_scav_pair(object_ptr);
            object_ptr += 2;
        }
    }
    // This assertion is usually the one that fails when something
    // is subtly wrong with the heap, so definitely always do it.
    gc_assert_verbose(object_ptr == end, "Final object pointer %p, start %p, end %p\n",
                      object_ptr, start, end);
}

// Scavenge a block of memory from 'start' extending for 'n_words'
// that must not contain any object headers.
sword_t scavenge(lispobj *start, sword_t n_words)
{
    gc_dcheck(compacting_p());
    lispobj *end = start + n_words;
    lispobj *object_ptr;
    for (object_ptr = start; object_ptr < end; object_ptr++) {
        lispobj object = *object_ptr;
        if (is_lisp_pointer(object)) scav1(object_ptr, object);
    }
    return n_words;
}

void scav_binding_stack(lispobj* where, lispobj* end, void (*fun)(lispobj))
{
    /* The binding stack consists of pairs of words, each holding a value and
     * either a TLS index (if threads), or symbol (if no threads).
     * Here we scavenge only the entries' values.
     *
     * Were the TLS index scavenged, it can never cause a symbol to move,
     * let alone be considered live. So we are bug-for-bug compatible regardless
     * of +/- sb-thread if a symbol would otherwise be garbage at this point.
     * As a practical matter, it is technically impossible for a symbol's only
     * reason for livenesss to be the binding stack. Nonetheless it is best to
     * enforce behavioral consistency whether or not the platform has threads.
     *
     * Bindings of compile-time known symbols is fairly easy to reason about.
     * Code headers point to symbols, therefore code objects retains symbols.
     * The edge case of a PROGV binding of a freshly made symbol (via MAKE-SYMBOL)
     * is interesting. Indeed we preserve the symbol because PROGV places a reference
     * on the control stack, thereby either pinning or scavenging as the case may be.
     * If it did not, we would need a map from TLS index to symbol, updated if
     * a symbol moves, allowing death of a symbol only when no binding entry
     * mentions that index. Such complication is unnecessary at present.
     */
    struct binding* binding = (struct binding*)where;
    if (fun) { // call the specified function
        for ( ; (lispobj*)binding < end; ++binding )
            if (is_lisp_pointer(binding->value))
                fun(binding->value);

    } else {   // call scav1
        for ( ; (lispobj*)binding < end; ++binding )
            if (is_lisp_pointer(binding->value))
                scav1(&binding->value, binding->value);
    }
}
void scan_binding_stack()
{
#ifndef LISP_FEATURE_SB_THREAD
    struct thread* th;
    for_each_thread(th) { /* 'all' is exactly one */
        struct binding *binding = (struct binding*)th->binding_stack_start;
        lispobj *end = (lispobj*)get_binding_stack_pointer(th);
        for ( ; (lispobj*)binding < end; ++binding ) {
            if (is_lisp_pointer(binding->symbol) &&
                forwarding_pointer_p(native_pointer(binding->symbol)))
                binding->symbol =
                  forwarding_pointer_value(native_pointer(binding->symbol));
        }
    }
#endif
}

static lispobj trans_fun_header(lispobj object); /* forward decls */
static lispobj trans_short_boxed(lispobj object);

static sword_t
scav_fun_pointer(lispobj *where, lispobj object)
{
    gc_dcheck(lowtag_of(object) == FUN_POINTER_LOWTAG);

    /* Object is a pointer into from_space - not a FP. */
    lispobj *first_pointer = native_pointer(object);

    /* must transport object -- object may point to either a function
     * header, a funcallable instance header, or a closure header. */
    lispobj copy = widetag_of(*first_pointer) == SIMPLE_FUN_WIDETAG
      ? trans_fun_header(object) : trans_short_boxed(object);

    if (copy != object) {
        /* Set forwarding pointer */
        set_forwarding_pointer(first_pointer,copy);
    }

    CHECK_COPY_POSTCONDITIONS(copy, FUN_POINTER_LOWTAG);

    *where = copy;

    return 1;
}


static struct code *
trans_code(struct code *code)
{
    /* if object has already been transported, just return pointer */
    if (forwarding_pointer_p((lispobj *)code)) {
        return (struct code *)native_pointer(forwarding_pointer_value((lispobj*)code));
    }

    gc_dcheck(widetag_of(code->header) == CODE_HEADER_WIDETAG);

    /* prepare to transport the code vector */
    lispobj l_code = (lispobj) LOW_WORD(code) | OTHER_POINTER_LOWTAG;
    sword_t nheader_words = code_header_words(code->header);
    sword_t ncode_words = code_instruction_words(code->code_size);
    lispobj l_new_code = copy_large_object(l_code, nheader_words + ncode_words,
                                           CODE_PAGE_FLAG);

#ifdef LISP_FEATURE_GENCGC
    if (l_new_code == l_code)
        return code;
#endif

    set_forwarding_pointer((lispobj *)code, l_new_code);

    /* set forwarding pointers for all the function headers in the */
    /* code object.  also fix all self pointers */
    /* Do this by scanning the new code, since the old header is unusable */

    uword_t displacement = l_new_code - l_code;
    struct code *new_code = (struct code *) native_pointer(l_new_code);

    for_each_simple_fun(i, nfheaderp, new_code, 1, {
        /* Calculate the old raw function pointer */
        struct simple_fun* fheaderp =
          (struct simple_fun*)LOW_WORD((char*)nfheaderp - displacement);
        /* Calculate the new lispobj */
        lispobj nfheaderl = make_lispobj(nfheaderp, FUN_POINTER_LOWTAG);

        set_forwarding_pointer((lispobj *)fheaderp, nfheaderl);

        /* fix self pointer. */
        nfheaderp->self =
#if defined(LISP_FEATURE_X86) || defined(LISP_FEATURE_X86_64)
            FUN_RAW_ADDR_OFFSET +
#endif
            nfheaderl;
    })
#ifdef LISP_FEATURE_GENCGC
    /* Cheneygc doesn't need this os_flush_icache, it flushes the whole
       spaces once when all copying is done. */
    os_flush_icache((os_vm_address_t) (((sword_t *)new_code) + nheader_words),
                    ncode_words * sizeof(sword_t));

#endif

    gencgc_apply_code_fixups(code, new_code);

    return new_code;
}

static sword_t
scav_code_header(lispobj *where, lispobj header)
{
    struct code *code = (struct code *) where;
    sword_t n_header_words = code_header_words(header);

    /* Scavenge the boxed section of the code data block. */
    scavenge(where + 1, n_header_words - 1);

    /* Scavenge the boxed section of each function object in the
     * code data block. */
    for_each_simple_fun(i, function_ptr, code, 1, {
        scavenge(SIMPLE_FUN_SCAV_START(function_ptr),
                 SIMPLE_FUN_SCAV_NWORDS(function_ptr));
    })

    return n_header_words + code_instruction_words(code->code_size);
}

static lispobj
trans_code_header(lispobj object)
{
    struct code *ncode = trans_code((struct code *) native_pointer(object));
    return (lispobj) LOW_WORD(ncode) | OTHER_POINTER_LOWTAG;
}

static sword_t
size_code_header(lispobj *where)
{
    return code_header_words(((struct code *)where)->header)
         + code_instruction_words(((struct code *)where)->code_size);
}

#ifdef RETURN_PC_WIDETAG
static sword_t
scav_return_pc_header(lispobj *where, lispobj object)
{
    lose("attempted to scavenge a return PC header where=%p object=%#lx\n",
         where, (uword_t) object);
    return 0; /* bogus return value to satisfy static type checking */
}

static lispobj
trans_return_pc_header(lispobj object)
{
    struct simple_fun *return_pc = (struct simple_fun *) native_pointer(object);
    uword_t offset = HeaderValue(return_pc->header) * N_WORD_BYTES;

    /* Transport the whole code object */
    struct code *code = (struct code *) ((uword_t) return_pc - offset);
    struct code *ncode = trans_code(code);

    return ((lispobj) LOW_WORD(ncode) + offset) | OTHER_POINTER_LOWTAG;
}
#endif /* RETURN_PC_WIDETAG */

/* On the 386, closures hold a pointer to the raw address instead of the
 * function object, so we can use CALL [$FDEFN+const] to invoke
 * the function without loading it into a register. Given that code
 * objects don't move, we don't need to update anything, but we do
 * have to figure out that the function is still live. */

#if defined(LISP_FEATURE_X86) || defined(LISP_FEATURE_X86_64)
static sword_t
scav_closure(lispobj *where, lispobj header)
{
    struct closure *closure = (struct closure *)where;
    int payload_words = SHORT_BOXED_NWORDS(header);
    lispobj fun = closure->fun - FUN_RAW_ADDR_OFFSET;
    scavenge(&fun, 1);
#ifdef LISP_FEATURE_GENCGC
    /* The function may have moved so update the raw address. But
     * don't write unnecessarily. */
    if (closure->fun != fun + FUN_RAW_ADDR_OFFSET)
        closure->fun = fun + FUN_RAW_ADDR_OFFSET;
#endif
    // Payload includes 'fun' which was just looked at, so subtract it.
    scavenge(closure->info, payload_words - 1);
    return 1 + payload_words;
}
#endif

#if !(defined(LISP_FEATURE_X86) || defined(LISP_FEATURE_X86_64))
static sword_t
scav_fun_header(lispobj *where, lispobj object)
{
    lose("attempted to scavenge a function header where=%p object=%#lx\n",
         where, (uword_t) object);
    return 0; /* bogus return value to satisfy static type checking */
}
#endif /* LISP_FEATURE_X86 */

static lispobj
trans_fun_header(lispobj object)
{
    struct simple_fun *fheader = (struct simple_fun *) native_pointer(object);
    uword_t offset =
        (HeaderValue(fheader->header) & FUN_HEADER_NWORDS_MASK) * N_WORD_BYTES;

    /* Transport the whole code object */
    struct code *code = (struct code *) ((uword_t) fheader - offset);
    struct code *ncode = trans_code(code);

    return ((lispobj) LOW_WORD(ncode) + offset) | FUN_POINTER_LOWTAG;
}


/*
 * instances
 */

static lispobj
trans_instance(lispobj object)
{
    gc_dcheck(lowtag_of(object) == INSTANCE_POINTER_LOWTAG);
    lispobj header = *(lispobj*)(object - INSTANCE_POINTER_LOWTAG);
    return copy_object(object, 1 + (instance_length(header)|1));
}

static sword_t
scav_instance_pointer(lispobj *where, lispobj object)
{
    /* Object is a pointer into from space - not a FP. */
    lispobj copy = trans_instance(object);

    gc_dcheck(copy != object);

    set_forwarding_pointer(native_pointer(object), copy);
    *where = copy;

    return 1;
}


/*
 * lists and conses
 */

static lispobj trans_list(lispobj object);

static sword_t
scav_list_pointer(lispobj *where, lispobj object)
{
    gc_dcheck(lowtag_of(object) == LIST_POINTER_LOWTAG);

    lispobj copy = trans_list(object);
    gc_dcheck(copy != object);

    CHECK_COPY_POSTCONDITIONS(copy, LIST_POINTER_LOWTAG);

    *where = copy;
    return 1;
}


static lispobj
trans_list(lispobj object)
{
    /* Copy 'object'. */
    struct cons *copy = (struct cons *)
        gc_general_alloc(sizeof(struct cons), BOXED_PAGE_FLAG, ALLOC_QUICK);
    lispobj new_list_pointer = make_lispobj(copy, LIST_POINTER_LOWTAG);
    copy->car = CONS(object)->car;
    /* Grab the cdr: set_forwarding_pointer will clobber it in GENCGC  */
    lispobj cdr = CONS(object)->cdr;
    set_forwarding_pointer((lispobj *)CONS(object), new_list_pointer);

    /* Try to linearize the list in the cdr direction to help reduce
     * paging. */
    while (lowtag_of(cdr) == LIST_POINTER_LOWTAG && from_space_p(cdr)) {
        lispobj* native_cdr = (lispobj*)CONS(cdr);
        if (forwarding_pointer_p(native_cdr)) {  // Might as well fix now.
            cdr = forwarding_pointer_value(native_cdr);
            break;
        }
        /* Copy 'cdr'. */
        struct cons *cdr_copy = (struct cons*)
            gc_general_alloc(sizeof(struct cons), BOXED_PAGE_FLAG, ALLOC_QUICK);
        cdr_copy->car = ((struct cons*)native_cdr)->car;
        /* Grab the cdr before it is clobbered. */
        lispobj next = ((struct cons*)native_cdr)->cdr;
        /* Set cdr of the predecessor, and store an FP. */
        set_forwarding_pointer(native_cdr,
                               copy->cdr = make_lispobj(cdr_copy,
                                                        LIST_POINTER_LOWTAG));
        copy = cdr_copy;
        cdr = next;
    }
    copy->cdr = cdr;
    return new_list_pointer;
}


/*
 * scavenging and transporting other pointers
 */

static sword_t
scav_other_pointer(lispobj *where, lispobj object)
{
    gc_dcheck(lowtag_of(object) == OTHER_POINTER_LOWTAG);

    /* Object is a pointer into from space - not FP. */
    lispobj *first_pointer = (lispobj *)(object - OTHER_POINTER_LOWTAG);
    int tag = widetag_of(*first_pointer);
    lispobj copy = transother[other_immediate_lowtag_p(tag)?tag>>2:0](object);

    // If the object was large, then instead of transporting it,
    // gencgc might simply promote the pages and return the same pointer.
    // That decision is made in general_copy_large_object().
    if (copy != object) {
        set_forwarding_pointer(first_pointer, copy);
#ifdef LISP_FEATURE_GENCGC
        *where = copy;
#endif
    }
#ifndef LISP_FEATURE_GENCGC
    *where = copy;
#endif
    CHECK_COPY_POSTCONDITIONS(copy, OTHER_POINTER_LOWTAG);
    return 1;
}

/*
 * immediate, boxed, and unboxed objects
 */

 /* The immediate object scavenger basically wants to be "scav_cons",
  * and so returns 2. To see why it's right, observe that scavenge() will
  * not invoke a scavtab entry on any object except for one satisfying
  * is_lisp_pointer(). So if a scavtab[] function got here,
  * then it must be via heap_scavenge(). But heap_scavenge() should only
  * dispatch via scavtab[] if it thought it saw an object header.
  * So why do we act like it saw a cons? Because conses can contain an
  * immediate object that satisfies both other_immediate_lowtag_p()
  * and is_lisp_immediate(), namely, the objects specifically mentioned at
  * is_cons_half(). So heap_scavenge() is nearly testing is_cons_half()
  * but even more efficiently, by ignoring the unusual immediate widetags
  * until we get to scav_immediate.
  *
  * And just to hammer the point home: we won't blow past the end of a specific
  * range of words when scavenging a binding or control stack or anything else,
  * because scavenge() skips immediate objects all by itself,
  * or rather it skips anything not satisfying is_lisp_pointer().
  *
  * As to the unbound marker, see rev. 09c78105eabc6bf2b339f421d4ed1df4678003db
  * which says that we might see it in conses for reasons somewhat unknown.
  */
static sword_t
scav_immediate(lispobj *where, lispobj object)
{
    object = *++where;
    if (is_lisp_pointer(object)) scav1(where, object);
    return 2;
}

static lispobj
trans_immediate(lispobj object)
{
    lose("trying to transport an immediate\n");
    return NIL; /* bogus return value to satisfy static type checking */
}

static sword_t
size_immediate(lispobj *where)
{
    return 1;
}

static inline boolean bignum_logbitp_inline(int index, struct bignum* bignum)
{
    int len = HeaderValue(bignum->header);
    int word_index = index / N_WORD_BITS;
    int bit_index = index % N_WORD_BITS;
    return word_index < len ? (bignum->digits[word_index] >> bit_index) & 1 : 0;
}
boolean positive_bignum_logbitp(int index, struct bignum* bignum)
{
  /* If the bignum in the layout has another pointer to it (besides the layout)
     acting as a root, and which is scavenged first, then transporting the
     bignum causes the layout to see a FP, as would copying an instance whose
     layout that is. This is a nearly impossible scenario to create organically
     in Lisp, because mostly nothing ever looks again at that exact (EQ) bignum
     except for a few things that would cause it to be pinned anyway,
     such as it being kept in a local variable during structure manipulation.
     See 'interleaved-raw.impure.lisp' for a way to trigger this */
  if (forwarding_pointer_p((lispobj*)bignum)) {
      lispobj forwarded = forwarding_pointer_value((lispobj*)bignum);
#if 0
      fprintf(stderr, "GC bignum_logbitp(): fwd from %p to %p\n",
              (void*)bignum, (void*)forwarded);
#endif
      bignum = (struct bignum*)native_pointer(forwarded);
  }
  return bignum_logbitp_inline(index, bignum);
}

// Helper function for stepping through the tagged slots of an instance in
// scav_instance and verify_space.
void
instance_scan(void (*proc)(lispobj*, sword_t, uword_t),
              lispobj *instance_slots,
              sword_t nslots, /* number of payload words */
              lispobj layout_bitmap,
              uword_t arg)
{
  sword_t index;

  if (fixnump(layout_bitmap)) {
      if (layout_bitmap == make_fixnum(-1))
          proc(instance_slots, nslots, arg);
      else {
          sword_t bitmap = fixnum_value(layout_bitmap); // signed integer!
          for (index = 0; index < nslots ; index++, bitmap >>= 1)
              if (bitmap & 1)
                  proc(instance_slots + index, 1, arg);
      }
  } else { /* huge bitmap */
      struct bignum * bitmap;
      bitmap = (struct bignum*)native_pointer(layout_bitmap);
      for (index = 0; index < nslots ; index++)
          if (bignum_logbitp_inline(index, bitmap))
              proc(instance_slots + index, 1, arg);
  }
}

static sword_t
scav_instance(lispobj *where, lispobj header)
{
    lispobj lbitmap = make_fixnum(-1);

    if (instance_layout(where)) {
        lispobj *layout = native_pointer(instance_layout(where));
#ifdef LISP_FEATURE_COMPACT_INSTANCE_HEADER
        if (__immobile_obj_gen_bits(layout) == from_space)
            enliven_immobile_obj(layout, 1);
#else
        if (forwarding_pointer_p(layout))
            layout = native_pointer(forwarding_pointer_value(layout));
#endif
        lbitmap = ((struct layout*)layout)->bitmap;
    }
    sword_t nslots = instance_length(header) | 1;
    if (lbitmap == make_fixnum(-1))
        scavenge(where+1, nslots);
    else if (!fixnump(lbitmap)) {
        /* It is conceivable that 'lbitmap' points to from_space, AND that it
         * is stored in one of the slots of the instance about to be scanned.
         * If so, then forwarding it will deposit new bits into its first
         * one or two words, rendering it bogus for use as the instance's bitmap.
         * So scavenge it up front to fix its address */
        scav1(&lbitmap, lbitmap);
        instance_scan((void(*)(lispobj*,sword_t,uword_t))scavenge,
                      where+1, nslots, lbitmap, 0);
    } else {
        sword_t bitmap = fixnum_value(lbitmap); // signed integer!
        sword_t n = nslots;
        lispobj obj;
        for ( ; n-- ; bitmap >>= 1) {
            ++where;
            if ((bitmap & 1) && is_lisp_pointer(obj = *where))
                scav1(where, obj);
        }
    }
    return 1 + nslots;
}

#ifdef LISP_FEATURE_COMPACT_INSTANCE_HEADER
static sword_t
scav_funinstance(lispobj *where, lispobj header)
{
    // This works because the layout is in the header word of all instances,
    // ordinary and funcallable, when compact headers are enabled.
    // The trampoline slot in the funcallable-instance is raw, but can be
    // scavenged, because it points to readonly space, never oldspace.
    // (And for certain backends it looks like a fixnum, not a pointer)
    return scav_instance(where, header);
}
#endif

//// Boxed object scav/trans/size functions

#define DEF_SCAV_BOXED(suffix, sizer) \
  static sword_t __attribute__((unused)) \
  scav_##suffix(lispobj *where, lispobj header) { \
      return 1 + scavenge(where+1, sizer(header)); \
  } \
  static lispobj trans_##suffix(lispobj object) { \
      return copy_object(object, 1 + sizer(*native_pointer(object))); \
  } \
  static sword_t size_##suffix(lispobj *where) { return 1 + sizer(*where); }

DEF_SCAV_BOXED(boxed, BOXED_NWORDS)
DEF_SCAV_BOXED(short_boxed, SHORT_BOXED_NWORDS)
DEF_SCAV_BOXED(tiny_boxed, TINY_BOXED_NWORDS)

/* Bignums use the high bit as the mark, and all remaining bits
 * excluding the 8 widetag bits to convey the size.
 * To size it, shift out the high bit, the shift right by an extra bit,
 * round to odd, and add 1 for the header. */
static inline sword_t size_bignum(lispobj *where) {
    return 1 + ((*where << 1 >> (1+N_WIDETAG_BITS)) | 1);
}

static lispobj trans_bignum(lispobj object)
{
    gc_dcheck(lowtag_of(object) == OTHER_POINTER_LOWTAG);
    return copy_large_object(object, size_bignum(native_pointer(object)),
                             UNBOXED_PAGE_FLAG);
}

/* Note: on the sparc we don't have to do anything special for fdefns, */
/* 'cause the raw-addr has a function lowtag. */
#if !defined(LISP_FEATURE_SPARC) && !defined(LISP_FEATURE_ARM)
static sword_t
scav_fdefn(lispobj *where, lispobj object)
{
    struct fdefn *fdefn = (struct fdefn *)where;

    /* FSHOW((stderr, "scav_fdefn, function = %p, raw_addr = %p\n",
       fdefn->fun, fdefn->raw_addr)); */

    scavenge(where + 1, 2); // 'name' and 'fun'
#ifndef LISP_FEATURE_IMMOBILE_CODE
    lispobj raw_fun = (lispobj)fdefn->raw_addr;
    if (raw_fun > READ_ONLY_SPACE_END) {
        lispobj simple_fun = raw_fun - FUN_RAW_ADDR_OFFSET;
        scavenge(&simple_fun, 1);
        /* Don't write unnecessarily. */
        if (simple_fun != raw_fun - FUN_RAW_ADDR_OFFSET)
            fdefn->raw_addr = (char *)simple_fun + FUN_RAW_ADDR_OFFSET;
    }
#elif defined(LISP_FEATURE_X86_64)
    lispobj obj = fdefn_callee_lispobj(fdefn);
    if (obj) {
        lispobj new = obj;
        scavenge(&new, 1); // enliven
        gc_dcheck(new == obj); // must not move
    }
#else
#  error "Need to implement scav_fdefn"
#endif
    return 4;
}
#endif

static sword_t
scav_unboxed(lispobj *where, lispobj object)
{
    sword_t length = HeaderValue(object) + 1;
    return ALIGN_UP(length, 2);
}

static lispobj
trans_unboxed(lispobj object)
{
    gc_dcheck(lowtag_of(object) == OTHER_POINTER_LOWTAG);
    sword_t length = HeaderValue(*native_pointer(object)) + 1;
    return copy_unboxed_object(object, ALIGN_UP(length, 2));
}

static lispobj
trans_ratio_or_complex(lispobj object)
{
    gc_dcheck(lowtag_of(object) == OTHER_POINTER_LOWTAG);
    lispobj* x = native_pointer(object);
    lispobj a = x[1];
    lispobj b = x[2];

    /* A zero ratio or complex means it was just allocated by fixed-alloc and
       a bignum can still be written there. Not a problem with a conservative GC
       since it will be pinned down. */
    if (fixnump(a) && fixnump(b)
#ifndef LISP_FEATURE_C_STACK_IS_CONTROL_STACK
        && a && b
#endif
        )
 {
      return copy_unboxed_object(object, 4);
    }
    return copy_object(object, 4);
}

/* vector-like objects */
static lispobj
trans_vector(lispobj object)
{
    gc_dcheck(lowtag_of(object) == OTHER_POINTER_LOWTAG);

    sword_t length = fixnum_value(VECTOR(object)->length);
    return copy_large_object(object, ALIGN_UP(length + 2, 2), BOXED_PAGE_FLAG);
}

static sword_t
size_vector(lispobj *where)
{
    sword_t length = fixnum_value(((struct vector*)where)->length);
    return ALIGN_UP(length + 2, 2);
}

static inline uword_t
NWORDS(uword_t x, uword_t n_bits)
{
    /* A good compiler should be able to constant-fold this whole thing,
       even with the conditional. */
    if(n_bits <= N_WORD_BITS) {
        uword_t elements_per_word = N_WORD_BITS/n_bits;

        return ALIGN_UP(x, elements_per_word)/elements_per_word;
    }
    else {
        /* FIXME: should have some sort of assertion that N_WORD_BITS
           evenly divides n_bits */
        return x * (n_bits/N_WORD_BITS);
    }
}

#define DEF_SCAV_TRANS_SIZE_UB(nbits) \
  DEF_SPECIALIZED_VECTOR(vector_unsigned_byte_##nbits, NWORDS(length, nbits))
#define DEF_SPECIALIZED_VECTOR(name, nwords) \
  static sword_t __attribute__((unused)) scav_##name(lispobj *where, lispobj header) { \
    sword_t length = fixnum_value(((struct vector*)where)->length); \
    return ALIGN_UP(nwords + 2, 2); \
  } \
  static lispobj __attribute__((unused)) trans_##name(lispobj object) { \
    gc_dcheck(lowtag_of(object) == OTHER_POINTER_LOWTAG); \
    sword_t length = fixnum_value(VECTOR(object)->length); \
    return copy_large_object(object, ALIGN_UP(nwords + 2, 2), UNBOXED_PAGE_FLAG); \
  } \
  static sword_t __attribute__((unused)) size_##name(lispobj *where) { \
    sword_t length = fixnum_value(((struct vector*)where)->length); \
    return ALIGN_UP(nwords + 2, 2); \
  }

DEF_SPECIALIZED_VECTOR(vector_nil, 0*length)
DEF_SPECIALIZED_VECTOR(vector_bit, NWORDS(length,1))
/* NOTE: strings contain one more element of data (a terminating '\0'
 * to help interface with C functions) than indicated by the length slot.
 * This is true even for UCS4 strings, despite that C APIs are unlikely
 * to have a convention that expects 4 zero bytes. */
DEF_SPECIALIZED_VECTOR(base_string, NWORDS((length+1), 8))
DEF_SPECIALIZED_VECTOR(character_string, NWORDS((length+1), 32))
DEF_SCAV_TRANS_SIZE_UB(2)
DEF_SCAV_TRANS_SIZE_UB(4)
DEF_SCAV_TRANS_SIZE_UB(8)
DEF_SCAV_TRANS_SIZE_UB(16)
DEF_SCAV_TRANS_SIZE_UB(32)
DEF_SCAV_TRANS_SIZE_UB(64)
DEF_SCAV_TRANS_SIZE_UB(128)
#ifdef LONG_FLOAT_SIZE
DEF_SPECIALIZED_VECTOR(vector_long_float, length * LONG_FLOAT_SIZE)
DEF_SPECIALIZED_VECTOR(vector_complex_long_float, length * (2 * LONG_FLOAT_SIZE))
#endif

static lispobj
trans_weak_pointer(lispobj object)
{
    lispobj copy;
    gc_dcheck(lowtag_of(object) == OTHER_POINTER_LOWTAG);

#if defined(DEBUG_WEAK)
    printf("Transporting weak pointer from 0x%08x\n", object);
#endif

    /* Need to remember where all the weak pointers are that have */
    /* been transported so they can be fixed up in a post-GC pass. */

    copy = copy_object(object, WEAK_POINTER_NWORDS);
#ifndef LISP_FEATURE_GENCGC
    struct weak_pointer *wp = (struct weak_pointer *) native_pointer(copy);

    gc_dcheck(widetag_of(wp->header)==WEAK_POINTER_WIDETAG);
    /* Push the weak pointer onto the list of weak pointers. */
    if (weak_pointer_breakable_p(wp)) {
        wp->next = (struct weak_pointer *)LOW_WORD(weak_pointers);
        weak_pointers = wp;
    }
#endif
    return copy;
}

void scan_weak_pointers(void)
{
    struct weak_pointer *wp, *next_wp;
    for (wp = weak_pointers, next_wp = NULL; wp != NULL; wp = next_wp) {
        gc_assert(widetag_of(wp->header)==WEAK_POINTER_WIDETAG);

        next_wp = wp->next;
        wp->next = NULL;
        if (next_wp == wp) /* gencgc uses a ref to self for end of list */
            next_wp = NULL;

        lispobj pointee = wp->value;
        gc_assert(is_lisp_pointer(pointee));
        lispobj *objaddr = native_pointer(pointee);

        /* Now, we need to check whether the object has been forwarded. If
         * it has been, the weak pointer is still good and needs to be
         * updated. Otherwise, the weak pointer needs to be broken. */

        if (from_space_p(pointee)) {
            wp->value = forwarding_pointer_p(objaddr) ?
                LOW_WORD(forwarding_pointer_value(objaddr)) : UNBOUND_MARKER_WIDETAG;
        }
#ifdef LISP_FEATURE_IMMOBILE_SPACE
          else if (immobile_space_p(pointee)) {
            if (immobile_obj_gen_bits(objaddr) == from_space)
                wp->value = UNBOUND_MARKER_WIDETAG;
        }
#endif
        else
            lose("unbreakable pointer %p", wp);
    }
}


/* Hash tables */

#if N_WORD_BITS == 32
#define EQ_HASH_MASK 0x1fffffff
#elif N_WORD_BITS == 64
#define EQ_HASH_MASK 0x1fffffffffffffff
#endif

/* Compute the EQ-hash of KEY. This must match POINTER-HASH in
 * target-hash-table.lisp.  */
#define EQ_HASH(key) ((key) & EQ_HASH_MASK)

/* List of weak hash tables chained through their NEXT-WEAK-HASH-TABLE
 * slot. Set to NULL at the end of a collection.
 *
 * This is not optimal because, when a table is tenured, it won't be
 * processed automatically; only the yougest generation is GC'd by
 * default. On the other hand, all applications will need an
 * occasional full GC anyway, so it's not that bad either.  */
struct hash_table *weak_hash_tables = NULL;

/* Return true if OBJ has already survived the current GC. */
static inline int pointer_survived_gc_yet(lispobj obj)
{
#ifdef LISP_FEATURE_CHENEYGC
    // This is the most straightforward definition.
    return (!from_space_p(obj) || forwarding_pointer_p(native_pointer(obj)));
#else
    /* Check for a pointer to dynamic space before considering immobile space.
       Based on the relative size of the spaces, this should be a win because
       if the object is in the dynamic space and not the 'from' generation
       we don't want to test immobile_space_p() at all.
       Additionally, pinned_p() is both more expensive and less likely than
       forwarding_pointer_p(), so we want to reverse those conditions, which
       would not be possible with pinned_p() buried inside from_space_p(). */
    page_index_t page_index = find_page_index((void*)obj);
    if (page_index >= 0)
        return page_table[page_index].gen != from_space ||
               forwarding_pointer_p(native_pointer(obj)) ||
               pinned_p(obj, page_index);
#ifdef LISP_FEATURE_IMMOBILE_SPACE
    if (immobile_space_p(obj))
        return immobile_obj_gen_bits(native_pointer(obj)) != from_space;
#endif
    return 1;
#endif
}

#define HT_ENTRY_LIVENESS_FUN_ARRAY_NAME weak_ht_alivep_funs
#include "weak-hash-pred.inc"

/* Return the beginning of data in ARRAY (skipping the header and the
 * length) or NULL if it isn't an array of the specified widetag after
 * all. */
static inline lispobj *
get_array_data (lispobj array, int widetag, uword_t *length)
{
    if (is_lisp_pointer(array) && widetag_of(*native_pointer(array)) == widetag) {
        if (length != NULL)
            *length = fixnum_value(native_pointer(array)[1]);
        return native_pointer(array) + 2;
    } else {
        return NULL;
    }
}

/* Only need to worry about scavenging the _real_ entries in the
 * table. Phantom entries such as the hash table itself at index 0 and
 * the empty marker at index 1 were scavenged by scav_vector that
 * either called this function directly or arranged for it to be
 * called later by pushing the hash table onto weak_hash_tables. */
void scav_hash_table_entries (struct hash_table *hash_table,
                              int (*alivep[5])(lispobj,lispobj),
                              void (*scav_entry)(lispobj*))
{
    lispobj *kv_vector;
    uword_t kv_length;
    lispobj *index_vector;
    uword_t length;
    lispobj *next_vector;
    uword_t next_vector_length;
    lispobj *hash_vector;
    uword_t hash_vector_length;
    lispobj empty_symbol;
    uword_t i;

    kv_vector = get_array_data(hash_table->table,
                               SIMPLE_VECTOR_WIDETAG, &kv_length);
    if (kv_vector == NULL)
        lose("invalid kv_vector %x\n", hash_table->table);

    index_vector = get_array_data(hash_table->index_vector,
                                  SIMPLE_ARRAY_WORD_WIDETAG, &length);
    if (index_vector == NULL)
        lose("invalid index_vector %x\n", hash_table->index_vector);

    next_vector = get_array_data(hash_table->next_vector,
                                 SIMPLE_ARRAY_WORD_WIDETAG,
                                 &next_vector_length);
    if (next_vector == NULL)
        lose("invalid next_vector %x\n", hash_table->next_vector);

    hash_vector = get_array_data(hash_table->hash_vector,
                                 SIMPLE_ARRAY_WORD_WIDETAG,
                                 &hash_vector_length);
    if (hash_vector != NULL)
        gc_assert(hash_vector_length == next_vector_length);

     /* These lengths could be different as the index_vector can be a
      * different length from the others, a larger index_vector could
      * help reduce collisions. */
     gc_assert(next_vector_length*2 == kv_length);

     if ((empty_symbol = kv_vector[1]) != UNBOUND_MARKER_WIDETAG)
        lose("unexpected empty-hash-table-slot marker: %p\n", empty_symbol);

    /* Work through the KV vector. */
    int (*alivep_test)(lispobj,lispobj) = alivep[fixnum_value(hash_table->_weakness)];
#define SCAV_ENTRIES(aliveness_predicate) \
    for (i = 1; i < next_vector_length; i++) {                                 \
        lispobj old_key = kv_vector[2*i];                                      \
        lispobj __attribute__((unused)) value = kv_vector[2*i+1];              \
        if (aliveness_predicate) {                                             \
            /* Scavenge the key and value. */                                  \
            scav_entry(&kv_vector[2*i]);                                       \
            /* If an EQ-based key has moved, mark the hash-table for rehash */ \
            if (!hash_vector || hash_vector[i] == MAGIC_HASH_VECTOR_VALUE) {   \
                lispobj new_key = kv_vector[2*i];                              \
                if (old_key != new_key && new_key != empty_symbol)             \
                    hash_table->needs_rehash_p = T;                            \
    }}}
    if (alivep_test)
        SCAV_ENTRIES(alivep_test(old_key, value))
    else
        SCAV_ENTRIES(1)
}

sword_t
scav_vector (lispobj *where, lispobj header)
{
    sword_t kv_length = fixnum_value(where[1]);
    struct hash_table *hash_table;

    /* SB-VM:VECTOR-VALID-HASHING-SUBTYPE is set for EQ-based and weak
     * hash tables in the Lisp HASH-TABLE code to indicate need for
     * special GC support. */
    if (is_vector_subtype(header, VectorNormal)) {
 normal:
      scavenge(where + 2, kv_length);
      return ALIGN_UP(kv_length + 2, 2);
    }

    /* Scavenge element 0, which may be a hash-table structure. */
    scavenge(where+2, 1);
    if (!is_lisp_pointer(where[2])) {
        /* This'll happen when REHASH clears the header of old-kv-vector
         * and fills it with zero, but some other thread simulatenously
         * sets the header in %%PUTHASH.
         */
        fprintf(stderr,
                "Warning: no pointer at %p in hash table: this indicates "
                "non-fatal corruption caused by concurrent access to a "
                "hash-table from multiple threads. Any accesses to "
                "hash-tables shared between threads should be protected "
                "by locks.\n", (void*)&where[2]);
        goto normal;
    }
    hash_table = (struct hash_table *)native_pointer(where[2]);
    if (widetag_of(hash_table->header) != INSTANCE_WIDETAG) {
        lose("hash table not instance (%"OBJ_FMTX" at %p)\n",
             hash_table->header,
             hash_table);
    }

    /* Verify that vector element 1 is as expected.
       Don't bother scavenging it, since we lose() if it's not an immediate. */
    if (where[3] != UNBOUND_MARKER_WIDETAG)
        lose("unexpected empty-hash-table-slot marker: %p\n", where[3]);

    /* Scavenge hash table, which will fix the positions of the other
     * needed objects. */
    scav_instance((lispobj *)hash_table, hash_table->header);

    /* Cross-check the kv_vector. */
    if (where != native_pointer(hash_table->table)) {
        lose("hash_table table!=this table %x\n", hash_table->table);
    }

    if (!hash_table->_weakness) {
        scav_hash_table_entries(hash_table, weak_ht_alivep_funs, gc_scav_pair);
    } else {
        /* Delay scavenging of this table by pushing it onto
         * weak_hash_tables (if it's not there already) for the weak
         * object phase. */
        if (hash_table->next_weak_hash_table == NIL) {
            hash_table->next_weak_hash_table = (lispobj)weak_hash_tables;
            weak_hash_tables = hash_table;
        }
    }

    return (ALIGN_UP(kv_length + 2, 2));
}

void
scav_weak_hash_tables (int (*alivep[5])(lispobj,lispobj),
                       void (*scavenger)(lispobj*))
{
    struct hash_table *table;

    /* Scavenge entries whose triggers are known to survive. */
    for (table = weak_hash_tables; table != NULL;
         table = (struct hash_table *)table->next_weak_hash_table) {
        scav_hash_table_entries(table, alivep, scavenger);
    }
}

/* Walk through the chain whose first element is *FIRST and remove
 * dead weak entries. */
static inline void
scan_weak_hash_table_chain (struct hash_table *hash_table, lispobj *prev,
                            lispobj *kv_vector, lispobj *index_vector,
                            lispobj *next_vector, lispobj *hash_vector,
                            lispobj empty_symbol, int (*alivep_test)(lispobj,lispobj))
{
    unsigned index = *prev;
    while (index) {
        unsigned next = next_vector[index];
        lispobj key = kv_vector[2 * index];
        lispobj value = kv_vector[2 * index + 1];
        gc_assert(key != empty_symbol);
        gc_assert(value != empty_symbol);
        if (!alivep_test(key, value)) {
            gc_assert(hash_table->number_entries > 0);
            *prev = next;
            hash_table->number_entries -= make_fixnum(1);
            next_vector[index] = fixnum_value(hash_table->next_free_kv);
            hash_table->next_free_kv = make_fixnum(index);
            kv_vector[2 * index] = empty_symbol;
            kv_vector[2 * index + 1] = empty_symbol;
            if (hash_vector)
                hash_vector[index] = MAGIC_HASH_VECTOR_VALUE;
        } else {
            prev = &next_vector[index];
        }
        index = next;
    }
}

static void
scan_weak_hash_table (struct hash_table *hash_table,
                      int (*alivep[5])(lispobj,lispobj))
{
    lispobj *kv_vector;
    lispobj *index_vector;
    uword_t length = 0; /* prevent warning */
    lispobj *next_vector;
    uword_t next_vector_length = 0; /* prevent warning */
    lispobj *hash_vector;
    lispobj empty_symbol;
    int (*alivep_test)(lispobj,lispobj) = alivep[fixnum_value(hash_table->_weakness)];
    uword_t i;

    kv_vector = get_array_data(hash_table->table,
                               SIMPLE_VECTOR_WIDETAG, NULL);
    index_vector = get_array_data(hash_table->index_vector,
                                  SIMPLE_ARRAY_WORD_WIDETAG, &length);
    next_vector = get_array_data(hash_table->next_vector,
                                 SIMPLE_ARRAY_WORD_WIDETAG,
                                 &next_vector_length);
    hash_vector = get_array_data(hash_table->hash_vector,
                                 SIMPLE_ARRAY_WORD_WIDETAG, NULL);
    empty_symbol = kv_vector[1];

    for (i = 0; i < length; i++) {
        scan_weak_hash_table_chain(hash_table, &index_vector[i],
                                   kv_vector, index_vector, next_vector,
                                   hash_vector, empty_symbol, alivep_test);
    }
}

/* Remove dead entries from weak hash tables. */
void
scan_weak_hash_tables (int (*alivep[5])(lispobj,lispobj))
{
    struct hash_table *table, *next;

    for (table = weak_hash_tables; table != NULL; table = next) {
        next = (struct hash_table *)table->next_weak_hash_table;
        table->next_weak_hash_table = NIL;
        scan_weak_hash_table(table, alivep);
    }

    weak_hash_tables = NULL;
}


/*
 * initialization
 */

static sword_t
scav_lose(lispobj *where, lispobj object)
{
    lose("no scavenge function for object %p (widetag 0x%x)\n",
         (uword_t)object,
         widetag_of(*where));

    return 0; /* bogus return value to satisfy static type checking */
}

static lispobj
trans_lose(lispobj object)
{
    lose("no transport function for object %p (widetag 0x%x)\n",
         (void*)object,
         widetag_of(*native_pointer(object)));
    return NIL; /* bogus return value to satisfy static type checking */
}

static sword_t
size_lose(lispobj *where)
{
    lose("no size function for object at %p (widetag 0x%x)\n",
         (void*)where,
         widetag_of(*where));
    return 1; /* bogus return value to satisfy static type checking */
}


/*
 * initialization
 */

#include "genesis/gc-tables.h"


lispobj *search_all_gc_spaces(void *pointer)
{
    lispobj *start;
    if (((start = search_dynamic_space(pointer)) != NULL) ||
#ifdef LISP_FEATURE_IMMOBILE_SPACE
        ((start = search_immobile_space(pointer)) != NULL) ||
#endif
        ((start = search_static_space(pointer)) != NULL) ||
        ((start = search_read_only_space(pointer)) != NULL))
        return start;
    return NULL;
}

/* Find the code object for the given pc, or return NULL on
   failure. */
lispobj *
component_ptr_from_pc(lispobj *pc)
{
    lispobj *object = search_all_gc_spaces(pc);

    if (object != NULL && widetag_of(*object) == CODE_HEADER_WIDETAG)
        return object;

    return NULL;
}

/* Scan an area looking for an object which encloses the given pointer.
 * Return the object start on success, or NULL on failure. */
lispobj *
gc_search_space3(void *pointer, lispobj *start, void *limit)
{
    if (pointer < (void*)start || pointer >= limit) return NULL;

    size_t count;
#if 0
    /* CAUTION: this code is _significantly_ slower than the production version
       due to the extra checks for forwarding.  Only use it if debugging */
    for ( ; (void*)start < limit ; start += count) {
        lispobj *forwarded_start;
        if (forwarding_pointer_p(start))
            forwarded_start = native_pointer(forwarding_pointer_value(start));
        else
            forwarded_start = start;
        lispobj thing = *forwarded_start;
        count = OBJECT_SIZE(thing, forwarded_start);
        /* Check whether the pointer is within this object. */
        if (pointer < (void*)(start+count)) return start;
    }
#else
    for ( ; (void*)start < limit ; start += count) {
        lispobj thing = *start;
        count = OBJECT_SIZE(thing, start);
        /* Check whether the pointer is within this object. */
        if (pointer < (void*)(start+count)) return start;
    }
#endif
    return NULL;
}

/* Helper for valid_lisp_pointer_p (below) and
 * conservative_root_p (gencgc).
 *
 * pointer is the pointer to check validity of,
 * and start_addr is the address of the enclosing object.
 *
 * This is actually quite simple to check: because the heap state is assumed
 * consistent, and 'start_addr' is known good, having come from
 * gc_search_space(), only the 'pointer' argument is dubious.
 * So make 'start_addr' into a tagged pointer and see if that matches 'pointer'.
 * If it does, then 'pointer' is valid.
 */
int
properly_tagged_p_internal(lispobj pointer, lispobj *start_addr)
{
    // If a headerless object, confirm that 'pointer' is a list pointer.
    // Given the precondition that the heap is in a valid state,
    // it may be assumed that one check of is_cons_half() suffices;
    // we don't need to check the other half.
    lispobj header = *start_addr;
    if (is_cons_half(header))
        return make_lispobj(start_addr, LIST_POINTER_LOWTAG) == pointer;

    // Because this heap object was not deemed to be a cons,
    // it must be an object header. Don't need a check except when paranoid.
    gc_dcheck(other_immediate_lowtag_p(header));

    // The space of potential widetags has 64 elements, not 256,
    // because of the constant low 2 bits.
    int widetag = widetag_of(header);
    int lowtag = lowtag_for_widetag[widetag>>2];
    if (lowtag && make_lispobj(start_addr, lowtag) == pointer)
        return 1; // instant win

    if (widetag == CODE_HEADER_WIDETAG) {
        // Check for RETURN_PC_HEADER first since it's quicker.
        // Then consider the embedded simple-funs.
#if !defined(LISP_FEATURE_X86) && !defined(LISP_FEATURE_X86_64)
        /* The all-architecture test below is good as far as it goes,
         * but an LRA object is similar to a FUN-POINTER: It is
         * embedded within a CODE-OBJECT pointed to by start_addr, and
         * cannot be found by simply walking the heap, therefore we
         * need to check for it. -- AB, 2010-Jun-04 */
        if (lowtag_of(pointer) == OTHER_POINTER_LOWTAG) {
            lispobj *potential_lra = native_pointer(pointer);
            if ((widetag_of(potential_lra[0]) == RETURN_PC_WIDETAG) &&
                ((potential_lra - HeaderValue(potential_lra[0])) == start_addr)) {
                return 1; /* It's as good as we can verify. */
            }
        }
#endif
        if (lowtag_of(pointer) == FUN_POINTER_LOWTAG) {
            struct simple_fun *pfun =
                (struct simple_fun*)(pointer-FUN_POINTER_LOWTAG);
            for_each_simple_fun(i, function, (struct code*)start_addr, 0, {
                if (pfun == function) return 1;
            })
        }
    }
    return 0; // no good
}

/* META: Note the ambiguous word "validate" in the comment below.
 * This means "Decide whether <x> is valid".
 * But when you see os_validate() elsewhere, that doesn't mean to ask
 * whether something is valid, it says to *make* it valid.
 * I think it would be nice if we could avoid using the word in the
 * sense in which os_validate() uses it, which would entail renaming
 * a bunch of stuff, which is harder than just explaining why
 * the comments can be deceptive */

/* Used by the debugger to validate possibly bogus pointers before
 * calling MAKE-LISP-OBJ on them.
 *
 * FIXME: We would like to make this perfect, because if the debugger
 * constructs a reference to a bugs lisp object, and it ends up in a
 * location scavenged by the GC all hell breaks loose.
 *
 * Whereas conservative_root_p has to be conservative
 * and return true for all valid pointers, this could actually be eager
 * and lie about a few pointers without bad results... but that should
 * be reflected in the name.
 */
int
valid_lisp_pointer_p(lispobj pointer)
{
    lispobj *start = search_all_gc_spaces((void*)pointer);
    if (start != NULL)
        return properly_tagged_descriptor_p((void*)pointer, start);
    return 0;
}

boolean
maybe_gc(os_context_t *context)
{
    lispobj gc_happened;
    __attribute__((unused)) struct thread *thread = arch_os_get_current_thread();
    boolean were_in_lisp = !foreign_function_call_active_p(thread);

    if (were_in_lisp) {
        fake_foreign_function_call(context);
    }

    /* SUB-GC may return without GCing if *GC-INHIBIT* is set, in
     * which case we will be running with no gc trigger barrier
     * thing for a while.  But it shouldn't be long until the end
     * of WITHOUT-GCING.
     *
     * FIXME: It would be good to protect the end of dynamic space for
     * CheneyGC and signal a storage condition from there.
     */

    /* Restore the signal mask from the interrupted context before
     * calling into Lisp if interrupts are enabled. Why not always?
     *
     * Suppose there is a WITHOUT-INTERRUPTS block far, far out. If an
     * interrupt hits while in SUB-GC, it is deferred and the
     * os_context_sigmask of that interrupt is set to block further
     * deferrable interrupts (until the first one is
     * handled). Unfortunately, that context refers to this place and
     * when we return from here the signals will not be blocked.
     *
     * A kludgy alternative is to propagate the sigmask change to the
     * outer context.
     */
#if !(defined(LISP_FEATURE_WIN32) || defined(LISP_FEATURE_SB_SAFEPOINT))
    check_gc_signals_unblocked_or_lose(os_context_sigmask_addr(context));
    unblock_gc_signals(0, 0);
#endif
    FSHOW((stderr, "/maybe_gc: calling SUB_GC\n"));
    /* FIXME: Nothing must go wrong during GC else we end up running
     * the debugger, error handlers, and user code in general in a
     * potentially unsafe place. Running out of the control stack or
     * the heap in SUB-GC are ways to lose. Of course, deferrables
     * cannot be unblocked because there may be a pending handler, or
     * we may even be in a WITHOUT-INTERRUPTS. */
    gc_happened = funcall1(StaticSymbolFunction(SUB_GC), 0);
    FSHOW((stderr, "/maybe_gc: gc_happened=%s\n",
           (gc_happened == NIL)
           ? "NIL"
           : ((gc_happened == T)
              ? "T"
              : "0")));
    /* gc_happened can take three values: T, NIL, 0.
     *
     * T means that the thread managed to trigger a GC, and post-gc
     * must be called.
     *
     * NIL means that the thread is within without-gcing, and no GC
     * has occurred.
     *
     * Finally, 0 means that *a* GC has occurred, but it wasn't
     * triggered by this thread; success, but post-gc doesn't have
     * to be called.
     */
    if ((gc_happened == T) &&
        /* See if interrupts are enabled or it's possible to enable
         * them. POST-GC has a similar check, but we don't want to
         * unlock deferrables in that case and get a pending interrupt
         * here. */
        ((read_TLS(INTERRUPTS_ENABLED,thread) != NIL) ||
         (read_TLS(ALLOW_WITH_INTERRUPTS,thread) != NIL))) {
#ifndef LISP_FEATURE_WIN32
        sigset_t *context_sigmask = os_context_sigmask_addr(context);
        if (!deferrables_blocked_p(context_sigmask)) {
            thread_sigmask(SIG_SETMASK, context_sigmask, 0);
#ifndef LISP_FEATURE_SB_SAFEPOINT
            check_gc_signals_unblocked_or_lose(0);
#endif
#endif
            FSHOW((stderr, "/maybe_gc: calling POST_GC\n"));
            funcall0(StaticSymbolFunction(POST_GC));
#ifndef LISP_FEATURE_WIN32
        } else {
            FSHOW((stderr, "/maybe_gc: punting on POST_GC due to blockage\n"));
        }
#endif
    }

    if (were_in_lisp) {
        undo_fake_foreign_function_call(context);
    } else {
        /* Otherwise done by undo_fake_foreign_function_call. And
         something later wants them to be blocked. What a nice
         interface.*/
        block_blockable_signals(0);
    }

    FSHOW((stderr, "/maybe_gc: returning\n"));
    return (gc_happened != NIL);
}

#define BYTES_ZERO_BEFORE_END (1<<12)

/* There used to be a similar function called SCRUB-CONTROL-STACK in
 * Lisp and another called zero_stack() in cheneygc.c, but since it's
 * shorter to express in, and more often called from C, I keep only
 * the C one after fixing it. -- MG 2009-03-25 */

/* Zero the unused portion of the control stack so that old objects
 * are not kept alive because of uninitialized stack variables.
 *
 * "To summarize the problem, since not all allocated stack frame
 * slots are guaranteed to be written by the time you call an another
 * function or GC, there may be garbage pointers retained in your dead
 * stack locations. The stack scrubbing only affects the part of the
 * stack from the SP to the end of the allocated stack." - ram, on
 * cmucl-imp, Tue, 25 Sep 2001
 *
 * So, as an (admittedly lame) workaround, from time to time we call
 * scrub-control-stack to zero out all the unused portion. This is
 * supposed to happen when the stack is mostly empty, so that we have
 * a chance of clearing more of it: callers are currently (2002.07.18)
 * REPL, SUB-GC and sig_stop_for_gc_handler. */

/* Take care not to tread on the guard page and the hard guard page as
 * it would be unkind to sig_stop_for_gc_handler. Touching the return
 * guard page is not dangerous. For this to work the guard page must
 * be zeroed when protected. */

/* FIXME: I think there is no guarantee that once
 * BYTES_ZERO_BEFORE_END bytes are zero the rest are also zero. This
 * may be what the "lame" adjective in the above comment is for. In
 * this case, exact gc may lose badly. */
void
scrub_control_stack()
{
    scrub_thread_control_stack(arch_os_get_current_thread());
}

void
scrub_thread_control_stack(struct thread *th)
{
    os_vm_address_t guard_page_address = CONTROL_STACK_GUARD_PAGE(th);
    os_vm_address_t hard_guard_page_address = CONTROL_STACK_HARD_GUARD_PAGE(th);
#ifdef LISP_FEATURE_C_STACK_IS_CONTROL_STACK
    /* On these targets scrubbing from C is a bad idea, so we punt to
     * a routine in $ARCH-assem.S. */
    extern void arch_scrub_control_stack(struct thread *, os_vm_address_t, os_vm_address_t, size_t page_size);
    arch_scrub_control_stack(th, guard_page_address, hard_guard_page_address, os_vm_page_size);
#else
    lispobj *sp = access_control_stack_pointer(th);
 scrub:
    if ((((os_vm_address_t)sp < (hard_guard_page_address + os_vm_page_size)) &&
         ((os_vm_address_t)sp >= hard_guard_page_address)) ||
        (((os_vm_address_t)sp < (guard_page_address + os_vm_page_size)) &&
         ((os_vm_address_t)sp >= guard_page_address) &&
         (th->control_stack_guard_page_protected != NIL)))
        return;
#ifdef LISP_FEATURE_STACK_GROWS_DOWNWARD_NOT_UPWARD
    do {
        *sp = 0;
    } while (((uword_t)sp--) & (BYTES_ZERO_BEFORE_END - 1));
    if ((os_vm_address_t)sp < (hard_guard_page_address + os_vm_page_size))
        return;
    do {
        if (*sp)
            goto scrub;
    } while (((uword_t)sp--) & (BYTES_ZERO_BEFORE_END - 1));
#else
    do {
        *sp = 0;
    } while (((uword_t)++sp) & (BYTES_ZERO_BEFORE_END - 1));
    if ((os_vm_address_t)sp >= hard_guard_page_address)
        return;
    do {
        if (*sp)
            goto scrub;
    } while (((uword_t)++sp) & (BYTES_ZERO_BEFORE_END - 1));
#endif
#endif /* LISP_FEATURE_C_STACK_IS_CONTROL_STACK */
}

#if !defined(LISP_FEATURE_X86) && !defined(LISP_FEATURE_X86_64)

void
scavenge_control_stack(struct thread *th)
{
    if (!compacting_p()) {
        long nwords = (lispobj*)access_control_stack_pointer(th) - th->control_stack_start;
        gc_mark_range(th->control_stack_start, nwords);
        return;
    }
    lispobj *object_ptr;

    /* In order to properly support dynamic-extent allocation of
     * non-CONS objects, the control stack requires special handling.
     * Rather than calling scavenge() directly, grovel over it fixing
     * broken hearts, scavenging pointers to oldspace, and pitching a
     * fit when encountering unboxed data.  This prevents stray object
     * headers from causing the scavenger to blow past the end of the
     * stack (an error case checked in scavenge()).  We don't worry
     * about treating unboxed words as boxed or vice versa, because
     * the compiler isn't allowed to store unboxed objects on the
     * control stack.  -- AB, 2011-Dec-02 */

    /* FIXME: I believe that this loop could be replaced by scavenge(),
     * as it can not "... blow past the end" on header words,
     * the way that heap_scavenge() might */
    for (object_ptr = th->control_stack_start;
         object_ptr < access_control_stack_pointer(th);
         object_ptr++) {

        lispobj object = *object_ptr;
#ifdef LISP_FEATURE_GENCGC
        if (forwarding_pointer_p(object_ptr))
            lose("unexpected forwarding pointer in scavenge_control_stack: %p, start=%p, end=%p\n",
                 object_ptr, th->control_stack_start, access_control_stack_pointer(th));
#endif
        if (is_lisp_pointer(object) && from_space_p(object)) {
            /* It currently points to old space. Check for a
             * forwarding pointer. */
            lispobj *ptr = native_pointer(object);
            if (forwarding_pointer_p(ptr)) {
                /* Yes, there's a forwarding pointer. */
                *object_ptr = LOW_WORD(forwarding_pointer_value(ptr));
            } else {
                /* Scavenge that pointer. */
                long n_words_scavenged =
                    (scavtab[widetag_of(object)])(object_ptr, object);
                gc_assert(n_words_scavenged == 1);
            }
        } else if (scavtab[widetag_of(object)] == scav_lose) {
            lose("unboxed object in scavenge_control_stack: %p->%x, start=%p, end=%p\n",
                 object_ptr, object, th->control_stack_start, access_control_stack_pointer(th));
        }
    }
}

/* Scavenging Interrupt Contexts */

static int boxed_registers[] = BOXED_REGISTERS;

/* The GC has a notion of an "interior pointer" register, an unboxed
 * register that typically contains a pointer to inside an object
 * referenced by another pointer.  The most obvious of these is the
 * program counter, although many compiler backends define a "Lisp
 * Interior Pointer" register known to the runtime as reg_LIP, and
 * various CPU architectures have other registers that also partake of
 * the interior-pointer nature.  As the code for pairing an interior
 * pointer value up with its "base" register, and fixing it up after
 * scavenging is complete is horribly repetitive, a few macros paper
 * over the monotony.  --AB, 2010-Jul-14 */

/* These macros are only ever used over a lexical environment which
 * defines a pointer to an os_context_t called context, thus we don't
 * bother to pass that context in as a parameter. */

/* Define how to access a given interior pointer. */
#define ACCESS_INTERIOR_POINTER_pc \
    *os_context_pc_addr(context)
#define ACCESS_INTERIOR_POINTER_lip \
    *os_context_register_addr(context, reg_LIP)
#define ACCESS_INTERIOR_POINTER_lr \
    *os_context_lr_addr(context)
#define ACCESS_INTERIOR_POINTER_npc \
    *os_context_npc_addr(context)
#define ACCESS_INTERIOR_POINTER_ctr \
    *os_context_ctr_addr(context)

#define INTERIOR_POINTER_VARS(name) \
    uword_t name##_offset;    \
    int name##_register_pair

#define PAIR_INTERIOR_POINTER(name)                             \
    pair_interior_pointer(context,                              \
                          ACCESS_INTERIOR_POINTER_##name,       \
                          &name##_offset,                       \
                          &name##_register_pair)

/* One complexity here is that if a paired register is not found for
 * an interior pointer, then that pointer does not get updated.
 * Originally, there was some commentary about using an index of -1
 * when calling os_context_register_addr() on SPARC referring to the
 * program counter, but the real reason is to allow an interior
 * pointer register to point to the runtime, read-only space, or
 * static space without problems. */
#define FIXUP_INTERIOR_POINTER(name)                                    \
    do {                                                                \
        if (name##_register_pair >= 0) {                                \
            ACCESS_INTERIOR_POINTER_##name =                            \
                (*os_context_register_addr(context,                     \
                                           name##_register_pair)        \
                 & ~LOWTAG_MASK)                                        \
                + name##_offset;                                        \
        }                                                               \
    } while (0)


static void
pair_interior_pointer(os_context_t *context, uword_t pointer,
                      uword_t *saved_offset, int *register_pair)
{
    unsigned int i;

    /*
     * I (RLT) think this is trying to find the boxed register that is
     * closest to the LIP address, without going past it.  Usually, it's
     * reg_CODE or reg_LRA.  But sometimes, nothing can be found.
     */
    /* 0x7FFFFFFF on 32-bit platforms;
       0x7FFFFFFFFFFFFFFF on 64-bit platforms */
    *saved_offset = (((uword_t)1) << (N_WORD_BITS - 1)) - 1;
    *register_pair = -1;
    for (i = 0; i < (sizeof(boxed_registers) / sizeof(int)); i++) {
        uword_t reg;
        uword_t offset;
        int index;

        index = boxed_registers[i];
        reg = *os_context_register_addr(context, index);

        /* An interior pointer is never relative to a non-pointer
         * register (an oversight in the original implementation).
         * The simplest argument for why this is true is to consider
         * the fixnum that happens by coincide to be the word-index in
         * memory of the header for some object plus two.  This is
         * happenstance would cause the register containing the fixnum
         * to be selected as the register_pair if the interior pointer
         * is to anywhere after the first two words of the object.
         * The fixnum won't be changed during GC, but the object might
         * move, thus destroying the interior pointer.  --AB,
         * 2010-Jul-14 */

        if (is_lisp_pointer(reg) &&
            ((reg & ~LOWTAG_MASK) <= pointer)) {
            offset = pointer - (reg & ~LOWTAG_MASK);
            if (offset < *saved_offset) {
                *saved_offset = offset;
                *register_pair = index;
            }
        }
    }
}

static void
scavenge_interrupt_context(os_context_t * context)
{
    unsigned int i;

    /* FIXME: The various #ifdef noise here is precisely that: noise.
     * Is it possible to fold it into the macrology so that we have
     * one set of #ifdefs and then INTERIOR_POINTER_VARS /et alia/
     * compile out for the registers that don't exist on a given
     * platform? */

    INTERIOR_POINTER_VARS(pc);
#ifdef reg_LIP
    INTERIOR_POINTER_VARS(lip);
#endif
#ifdef ARCH_HAS_LINK_REGISTER
    INTERIOR_POINTER_VARS(lr);
#endif
#ifdef ARCH_HAS_NPC_REGISTER
    INTERIOR_POINTER_VARS(npc);
#endif
#ifdef LISP_FEATURE_PPC
    INTERIOR_POINTER_VARS(ctr);
#endif

    PAIR_INTERIOR_POINTER(pc);
#ifdef reg_LIP
    PAIR_INTERIOR_POINTER(lip);
#endif
#ifdef ARCH_HAS_LINK_REGISTER
    PAIR_INTERIOR_POINTER(lr);
#endif
#ifdef ARCH_HAS_NPC_REGISTER
    PAIR_INTERIOR_POINTER(npc);
#endif
#ifdef LISP_FEATURE_PPC
    PAIR_INTERIOR_POINTER(ctr);
#endif

    /* Scavenge all boxed registers in the context. */
    for (i = 0; i < (sizeof(boxed_registers) / sizeof(int)); i++) {
        os_context_register_t *boxed_reg;
        lispobj datum;

        /* We can't "just" cast os_context_register_addr() to a
         * pointer to lispobj and pass it to scavenge, because some
         * systems can have a wider register width than we use for
         * lisp objects, and on big-endian systems casting a pointer
         * to a narrower target type doesn't work properly.
         * Therefore, we copy the value out to a temporary lispobj
         * variable, scavenge there, and copy the value back in.
         *
         * FIXME: lispobj is unsigned, os_context_register_t may be
         * signed or unsigned, are we truncating or sign-extending
         * values here that shouldn't be modified?  Possibly affects
         * any architecture that has 32-bit and 64-bit variants where
         * we run in 32-bit mode on 64-bit hardware when the OS is set
         * up for 64-bit from the start.  Or an environment with
         * 32-bit addresses and 64-bit registers. */

        boxed_reg = os_context_register_addr(context, boxed_registers[i]);
        datum = *boxed_reg;
        if (compacting_p()) scavenge(&datum, 1); else gc_mark_obj(datum);
        *boxed_reg = datum;
    }

    /* Now that the scavenging is done, repair the various interior
     * pointers. */
    FIXUP_INTERIOR_POINTER(pc);
#ifdef reg_LIP
    FIXUP_INTERIOR_POINTER(lip);
#endif
#ifdef ARCH_HAS_LINK_REGISTER
    FIXUP_INTERIOR_POINTER(lr);
#endif
#ifdef ARCH_HAS_NPC_REGISTER
    FIXUP_INTERIOR_POINTER(npc);
#endif
#ifdef LISP_FEATURE_PPC
    FIXUP_INTERIOR_POINTER(ctr);
#endif
}

void
scavenge_interrupt_contexts(struct thread *th)
{
    int i, index;
    os_context_t *context;

    index = fixnum_value(read_TLS(FREE_INTERRUPT_CONTEXT_INDEX,th));

#if defined(DEBUG_PRINT_CONTEXT_INDEX)
    printf("Number of active contexts: %d\n", index);
#endif

    for (i = 0; i < index; i++) {
        context = th->interrupt_contexts[i];
        scavenge_interrupt_context(context);
    }
}
#endif /* x86oid targets */

void varint_unpacker_init(struct varint_unpacker* unpacker, lispobj integer)
{
  if (fixnump(integer)) {
      unpacker->word  = fixnum_value(integer);
      unpacker->limit = N_WORD_BYTES;
      unpacker->data  = (char*)&unpacker->word;
  } else {
      struct bignum* bignum = (struct bignum*)(integer - OTHER_POINTER_LOWTAG);
      unpacker->word  = 0;
      unpacker->limit = HeaderValue(bignum->header) * N_WORD_BYTES;
      unpacker->data  = (char*)bignum->digits;
  }
  unpacker->index = 0;
}

// Fetch the next varint from 'unpacker' into 'result'.
// Because there is no length prefix on the number of varints encoded,
// spurious trailing zeros might be observed. The data consumer can
// circumvent that by storing a count as the first value in the series.
// Return 1 for success, 0 for EOF.
int varint_unpack(struct varint_unpacker* unpacker, int* result)
{
    if (unpacker->index >= unpacker->limit) return 0;
    int accumulator = 0;
    int shift = 0;
    while (1) {
#ifdef LISP_FEATURE_LITTLE_ENDIAN
        int byte = unpacker->data[unpacker->index];
#else
        // bignums are little-endian in word order,
        // but machine-native within each word.
        // We could pack bytes MSB-to-LSB in the bigdigits,
        // but that seems less intuitive on the Lisp side.
        int word_index = unpacker->index / N_WORD_BYTES;
        int byte_index = unpacker->index % N_WORD_BYTES;
        int byte = (((unsigned int*)unpacker->data)[word_index]
                    >> (byte_index * 8)) & 0xFF;
#endif
        ++unpacker->index;
        accumulator |= (byte & 0x7F) << shift;
        if (!(byte & 0x80)) break;
        gc_assert(unpacker->index < unpacker->limit);
        shift += 7;
    }
    *result = accumulator;
    return 1;
}

/* Our own implementation of heapsort, because some C libraries have a qsort()
 * that calls malloc() apparently, which we MUST NOT do. */

typedef uword_t* heap;

#define swap(a,i,j) { uword_t temp=a[i];a[i]=a[j];a[j]=temp; }
static void sift_down(heap array, int start, int end)
{
     int root = start;
     while (root * 2 + 1 <= end) {
       int child = root * 2 + 1;
       if (child + 1 <= end && array[child] < array[child+1])
           ++child;
       if (array[root] < array[child]) {
           swap(array, root, child);
           root = child;
       } else {
           return;
       }
     }
}

static void heapify(heap array, int length)
{
    int start = (length - 2) / 2;
    while (start >= 0) {
        sift_down(array, start, length-1);
        --start;
    }
}

void gc_heapsort_uwords(heap array, int length)
{
    heapify(array, length);
    int end = length - 1;
    while (end > 0) {
        swap(array, end, 0);
        --end;
        sift_down(array, 0, end);
    }
}

//// Coalescing of constant vectors for SAVE-LISP-AND-DIE

static boolean coalescible_number_p(lispobj* where)
{
    int widetag = widetag_of(*where);
    return widetag == BIGNUM_WIDETAG
        // Ratios and complex integers containing pointers to bignums don't work.
        || ((widetag == RATIO_WIDETAG || widetag == COMPLEX_WIDETAG)
            && fixnump(where[1]) && fixnump(where[2]))
#ifndef LISP_FEATURE_64_BIT
        || widetag == SINGLE_FLOAT_WIDETAG
#endif
        || widetag == DOUBLE_FLOAT_WIDETAG
        || widetag == COMPLEX_SINGLE_FLOAT_WIDETAG
        || widetag == COMPLEX_DOUBLE_FLOAT_WIDETAG;
}

/// Return true of fixnums, bignums, strings, symbols.
/// Strings are considered eql-comparable,
/// because they're coalesced before comparing.
static boolean eql_comparable_p(lispobj obj)
{
    if (fixnump(obj) || obj == NIL) return 1;
    if (lowtag_of(obj) != OTHER_POINTER_LOWTAG) return 0;
    int widetag = widetag_of(*native_pointer(obj));
    return widetag == BIGNUM_WIDETAG
        || widetag == SYMBOL_WIDETAG
#ifdef SIMPLE_CHARACTER_STRING_WIDETAG
        || widetag == SIMPLE_CHARACTER_STRING_WIDETAG
#endif
        || widetag == SIMPLE_BASE_STRING_WIDETAG;
}

static boolean vector_isevery(boolean (*pred)(lispobj), struct vector* v)
{
    int i;
    for (i = fixnum_value(v->length)-1; i >= 0; --i)
        if (!pred(v->data[i])) return 0;
    return 1;
}

static void coalesce_obj(lispobj* where, struct hopscotch_table* ht)
{
    lispobj ptr = *where;
    if (lowtag_of(ptr) != OTHER_POINTER_LOWTAG)
        return;

    extern char gc_coalesce_string_literals;
    // gc_coalesce_string_literals represents the "aggressiveness" level.
    // If 1, then we share vectors tagged as +VECTOR-SHAREABLE+,
    // but if >1, those and also +VECTOR-SHAREABLE-NONSTD+.
    int mask = gc_coalesce_string_literals > 1
      ? (VECTOR_SHAREABLE|VECTOR_SHAREABLE_NONSTD)<<N_WIDETAG_BITS
      : (VECTOR_SHAREABLE                        )<<N_WIDETAG_BITS;

    lispobj* obj = native_pointer(ptr);
    lispobj header = *obj;
    int widetag = widetag_of(header);

    if ((((header & mask) != 0) // optimistically assume it's a vector
         && ((widetag == SIMPLE_VECTOR_WIDETAG
              && vector_isevery(eql_comparable_p, (struct vector*)obj))
             || specialized_vector_widetag_p(widetag)))
        || coalescible_number_p(obj)) {
        if (widetag == SIMPLE_VECTOR_WIDETAG) {
            sword_t n_elts = fixnum_value(obj[1]), i;
            for (i = 2 ; i < n_elts+2 ; ++i)
                coalesce_obj(obj + i, ht);
        }
        int index = hopscotch_get(ht, (uword_t)obj, 0);
        if (!index) // Not found
            hopscotch_insert(ht, (uword_t)obj, 1);
        else
            *where = make_lispobj((void*)ht->keys[index-1], OTHER_POINTER_LOWTAG);
    }
}

static uword_t coalesce_range(lispobj* where, lispobj* limit, uword_t arg)
{
    struct hopscotch_table* ht = (struct hopscotch_table*)arg;
    lispobj layout, bitmap, *next;
    sword_t nwords, i, j;

    for ( ; where < limit ; where = next ) {
        lispobj header = *where;
        if (is_cons_half(header)) {
            coalesce_obj(where+0, ht);
            coalesce_obj(where+1, ht);
            next = where + 2;
        } else {
            int widetag = widetag_of(header);
            nwords = sizetab[widetag](where);
            next = where + nwords;
            switch (widetag) {
            case INSTANCE_WIDETAG: // mixed boxed/unboxed objects
#ifdef LISP_FEATURE_COMPACT_INSTANCE_HEADER
            case FUNCALLABLE_INSTANCE_WIDETAG:
#endif
                layout = instance_layout(where);
                bitmap = LAYOUT(layout)->bitmap;
                for(i=1; i<nwords; ++i)
                    if (layout_bitmap_logbitp(i-1, bitmap))
                        coalesce_obj(where+i, ht);
                continue;
            case CODE_HEADER_WIDETAG:
                for_each_simple_fun(i, fun, (struct code*)where, 0, {
                    lispobj* fun_slots = SIMPLE_FUN_SCAV_START(fun);
                    for (j=0; j<SIMPLE_FUN_SCAV_NWORDS(fun); ++j)
                        coalesce_obj(fun_slots+j, ht);
                })
                nwords = code_header_words(header);
                break;
            default:
                if (unboxed_obj_widetag_p(widetag))
                    continue; // Ignore this object.
            }
            for(i=1; i<nwords; ++i)
                coalesce_obj(where+i, ht);
        }
    }
    return 0;
}

void coalesce_similar_objects()
{
    struct hopscotch_table ht;
    hopscotch_create(&ht, HOPSCOTCH_VECTOR_HASH, 0, 1<<17, 0);
#ifndef LISP_FEATURE_WIN32
    // Apparently this triggers the "Unable to recommit" lossage message
    // in handle_access_violation() in src/runtime/win32-os.c
    coalesce_range((lispobj*)STATIC_SPACE_START,
                   (lispobj*)STATIC_SPACE_END,
                   (uword_t)&ht);
#endif
#ifdef LISP_FEATURE_IMMOBILE_SPACE
    coalesce_range((lispobj*)IMMOBILE_SPACE_START,
                   immobile_fixedobj_free_pointer,
                   (uword_t)&ht);
    coalesce_range((lispobj*)IMMOBILE_VARYOBJ_SUBSPACE_START,
                   immobile_space_free_pointer,
                   (uword_t)&ht);
#endif
#ifdef LISP_FEATURE_GENCGC
    walk_generation(coalesce_range, -1, (uword_t)&ht);
#else
    // FIXME: implement
#endif
    hopscotch_destroy(&ht);
}
