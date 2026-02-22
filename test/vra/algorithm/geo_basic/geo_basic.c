#include <stdint.h>
#include <stdio.h>
#include "../config.h"

static inline double __attribute__((annotate("scalar(range(0, 1) disabled)"))) fast_rand01(void) {
    static uint64_t state = 0xC0FFEE1234ULL;
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    uint64_t x = state * 2685821657736338717ULL;
    return (x >> 11) * (1.0 / 9007199254740992.0); // 2^53
}

static inline float __attribute__((annotate("scalar(range(" PB_XSTR(RMIN_POS) ", " PB_XSTR(RMAX_POS) ") final disabled)"))) rand_range(float min, float max) {
    return (float)(min + (max - min) * fast_rand01());
}

#if OLDVRA
float arr[R_SMALL] __attribute__((annotate("scalar(range(1, 10000))")));
#else
float arr[R_SMALL] __attribute__((annotate("scalar(range(1,1))")));
#endif

int main(int argc, char const *argv[])
{

    #if OLDVRA
    float acc_gt[2] __attribute__((annotate("scalar(range(-" PB_XSTR(R_SMALL) ", " PB_XSTR(R_SMALL) "))")));
    #else
    float acc_gt[2] __attribute__((annotate("scalar(range(1,1))")));
    #endif

    for (int i = 0; i < R_SMALL; i++) {
        arr[i] = rand_range(RMIN_POS, RMAX_POS);
    }

    float ratio1 = rand_range(RMIN_POS, RMAX_POS);
    float ratio2 = rand_range(RMIN_POS, RMAX_POS);

    for (int m = 0; m < M; ++m) {
        uint32_t cycles_high1 = 0;
        uint32_t cycles_high = 0;
        uint32_t cycles_low = 0;
        uint32_t cycles_low1 = 0;

        asm volatile("CPUID\n\t"
                    "RDTSC\n\t"
                    "mov %%edx, %0\n\t"
                    "mov %%eax, %1\n\t"
                    : "=r"(cycles_high), "=r"(cycles_low)::"%rax", "%rbx", "%rcx", "%rdx");

        #if OLDVRA
        float mul __attribute__((annotate("scalar(range(1, 10000))"))) = 1;
        float div __attribute__((annotate("scalar(range(-" PB_XSTR(R) ", " PB_XSTR(R) "))"))) = 10000;
        #else
        float mul __attribute__((annotate("scalar()"))) = 1;
        float div __attribute__((annotate("scalar()"))) = 10000;
        #endif

        for (int i = 0; i < N_SMALL; i++) {
            mul *= ratio1;
            div /= ratio2;
        }

        for (int i = 1; i < R_SMALL; i++) {
            arr[i] = arr[i - 1] * ratio1;
        }

        acc_gt[0] = mul;
        acc_gt[1] = div;

        asm volatile("RDTSCP\n\t"
                 "mov %%edx, %0\n\t"
                 "mov %%eax, %1\n\t"
                 "CPUID\n\t"
                 : "=r"(cycles_high1), "=r"(cycles_low1)::"%rax", "%rbx", "%rcx", "%rdx");
        uint64_t end = (uint64_t) cycles_high1 << 32 | cycles_low1;
        uint64_t start = (uint64_t) cycles_high << 32 | cycles_low;
        if (end > start)
        printf("Cycles: %li\n", end - start);
    }

    printf("Values Begin\n");
    for (int j = 0; j < R_SMALL; ++j)
        printf("%f\n", arr[j]);
    printf("%f\n", acc_gt[0]);
    printf("%f\n", acc_gt[1]);
    printf("Values End\n");

    return 0;
}
