/* Use the GCC __builtin_cpu_supports intrinsic to verify the presence of
   active AVX-512 extensions.  For each supported extension, output a token
   we can map to a Lisp symbol in *feature* flags, so we can use them in lisp
   as reader macros via #+ and #- flags.
*/

/* #include <stdio.h> */

/* int main(void) { */

/*     if (__builtin_cpu_supports("avx512f")) { */
/*         printf("avx512f\n"); */

/*         // Query each avx512 extension separately for *features* */
/*         if (__builtin_cpu_supports("avx512dq"))   printf("avx512dq\n"); */
/*         if (__builtin_cpu_supports("avx512ifma")) printf("avx512ifma\n"); */
/*         if (__builtin_cpu_supports("avx512pf"))   printf("avx512pf\n"); */
/*         if (__builtin_cpu_supports("avx512er"))   printf("avx512er\n"); */
/*         if (__builtin_cpu_supports("avx512cd"))   printf("avx512cd\n"); */
/*         if (__builtin_cpu_supports("avx512bw"))   printf("avx512bw\n"); */
/*         if (__builtin_cpu_supports("avx512vl"))   printf("avx512vl\n"); */
/*         if (__builtin_cpu_supports("avx512vbmi")) printf("avx512vbmi\n"); */
/*         if (__builtin_cpu_supports("avx512vnni")) printf("avx512vnni\n"); */
/*         if (__builtin_cpu_supports("avx512bf16")) printf("avx512bf16\n"); */
/*         return 1; */
/*     } */

/*     return 0; */
/* } */

/* unfortunately, some of avx512 extensions were not detectable via GCC
 * intrinsics (pf and er), so I had to use raw cpuid instead. */

#include <stdio.h>
#include <stdint.h>

int main(void) {
    uint32_t leaf0[4] = {0}; // EAX, EBX, ECX, EDX for Sub-leaf 0
    uint32_t leaf1[4] = {0}; // EAX, EBX, ECX, EDX for Sub-leaf 1

    // Sub-leaf 0
    __asm__ __volatile__(
        "cpuid"
        : "=a"(leaf0[0]), "=b"(leaf0[1]), "=c"(leaf0[2]), "=d"(leaf0[3])
        : "a"(7), "c"(0)
    );

    // does this CPU support any?
    if (!(leaf0[1] & (1u << 16))) {
        return 1;
    }
    printf("avx512f\n");

    if (leaf0[1] & (1u << 17)) printf("avx512dq\n");
    if (leaf0[1] & (1u << 21)) printf("avx512ifma\n");
    if (leaf0[1] & (1u << 26)) printf("avx512pf\n");
    if (leaf0[1] & (1u << 27)) printf("avx512er\n");
    if (leaf0[1] & (1u << 28)) printf("avx512cd\n");
    if (leaf0[1] & (1u << 30)) printf("avx512bw\n");
    if (leaf0[1] & (1u << 31)) printf("avx512vl\n");
    if (leaf0[2] & (1u << 1))  printf("avx512vbmi\n");
    if (leaf0[2] & (1u << 11)) printf("avx512vnni\n");

    // bf16 support
    __asm__ __volatile__(
        "cpuid"
        : "=a"(leaf1[0]), "=b"(leaf1[1]), "=c"(leaf1[2]), "=d"(leaf1[3])
        : "a"(7), "c"(1)
    );

    if (leaf1[0] & (1u << 5))  printf("avx512bf16\n");

    return 0;
}
