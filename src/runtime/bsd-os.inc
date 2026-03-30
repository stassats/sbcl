os_vm_address_t
os_alloc_gc_space(int space_id, int attributes, os_vm_address_t addr, os_vm_size_t len)
{
    int __attribute((unused))
      executable = (space_id == READ_ONLY_CORE_SPACE_ID) ||
                   (space_id == ALIEN_LINKAGE_TABLE_CORE_SPACE_ID) ||
                   (space_id == STATIC_CODE_CORE_SPACE_ID),
      jit = (space_id == STATIC_CODE_CORE_SPACE_ID) || (space_id == DYNAMIC_CORE_SPACE_ID)
            ? 1 : (space_id == ALIEN_LINKAGE_TABLE_CORE_SPACE_ID) ? 2 : 0;

    int protection;
    int flags = 0;

    // FIXME: This probaby needs to use MAP_TRYFIXED
    if (attributes & IS_GUARD_PAGE)
        protection = OS_VM_PROT_NONE;
    else
#if defined(LISP_FEATURE_OPENBSD) && defined(MAP_STACK)
    /* OpenBSD requires MAP_STACK for pages used as stack (and RW protection).
     * Note that FreeBSD has a MAP_STACK with different behavior. */
    if (space_id == THREAD_STRUCT_CORE_SPACE_ID) {
        protection = OS_VM_PROT_READ | OS_VM_PROT_WRITE;
        flags |= MAP_STACK;
    } else {
        protection = OS_VM_PROT_ALL;
    }

#elif defined(LISP_FEATURE_DARWIN_JIT)
    if (jit) {
        if (jit == 2)
            protection = OS_VM_PROT_ALL;
        else
            protection = OS_VM_PROT_READ | OS_VM_PROT_WRITE;
        flags |= MAP_JIT;
    }
    else if (executable) {
        protection = OS_VM_PROT_READ | OS_VM_PROT_EXECUTE;
    }
    else {
        protection = OS_VM_PROT_READ | OS_VM_PROT_WRITE;
    }

#else
        protection = OS_VM_PROT_ALL;
#endif

    attributes &= ~IS_GUARD_PAGE;

#ifndef LISP_FEATURE_DARWIN // Do not use MAP_FIXED, because the OS is sane.
    /* The *BSD family of OSes seem to ignore 'addr' when it is outside
     * of some range which I could not figure out.  Sometimes it seems like the
     * condition is that any address below 4GB can't be requested without MAP_FIXED,
     * but on the other hand, asking for 0x1000 without MAP_FIXED works fine.
     * So we are forced to use MAP_FIXED even for movable mappings. Thus, the logic
     * below does not work as intended because:
     * (1) We can't detect when MAP_FIXED destroyed an existing mapping.
     *     But we can avoid the destruction by using MAP_EXCL when that flag exists,
     *     which it does not always.
     * (2) Passing MAP_FIXED when we do not require a fixed address gets MAP_FAILURE
     *     for mappings that we would have been willing to relocate.
     *     So relocation is effectively disabled.
     * (3) To mitigate the problem of point (2) we remove MAP_FIXED for the
     *     dynamic space which seems to mostly work, but might cause an opposite
     *     problem: we relocate the heap when perhaps we need not have.
     *     That is, even if the OS _could_ _have_ given the address requested,
     *     it randomly decided not to, thus forcing extra work upon us.

     * For reference,
     * FreeBSD says:
       If MAP_EXCL is not specified, a successful MAP_FIXED request replaces any
       previous mappings for the process' pages ...

     * OpenBSD says:
       Except for MAP_FIXED mappings, the system will never replace existing mappings. */

    // ALLOCATE_LOW seems never to get what we want
    if (!(attributes & MOVABLE) || (attributes & ALLOCATE_LOW)) flags |= MAP_FIXED;
#endif

#ifdef MAP_EXCL // not defined in OpenBSD, NetBSD, DragonFlyBSD
    if (flags & MAP_FIXED) flags |= MAP_EXCL;
#endif
    flags |= MAP_PRIVATE | MAP_ANON;

#ifdef __NetBSD__
    if (addr) {
        os_vm_address_t curaddr = addr;

        while (len > 0) {
            os_vm_address_t resaddr;
            os_vm_size_t curlen = MIN(max_allocation_size, len);

            resaddr = mmap(curaddr, curlen, protection, flags, -1, 0);

            if (resaddr == (os_vm_address_t) - 1) {
                perror("mmap");

                while (curaddr > addr) {
                    curaddr -= max_allocation_size;
                    munmap(curaddr, max_allocation_size);
                }

                return NULL;
            }

            curaddr += curlen;
            len -= curlen;
        }
    } else
#endif
    {
        os_vm_address_t requested = addr;
        addr = sbcl_mmap(addr, len, protection, flags, -1, 0);
        if (requested && requested != addr && !(attributes & MOVABLE)) {
            return 0;
        }

    }

    if (addr == MAP_FAILED) {
#ifdef LISP_FEATURE_OPENBSD
        if (errno == ENOTSUP)
            fprintf(stderr, "RWX mmap not supported, is the current filesystem"
                    " mounted with wxallowed?\n");
        else
#endif
            perror("mmap");
        return NULL;
    }

    return addr;
}
