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

static inline float __attribute__((annotate("scalar(range(" PB_XSTR(RMIN) ", " PB_XSTR(RMAX) ") final disabled)"))) rand_range(float min, float max) {
    return (float)(min + (max - min) * fast_rand01());
}

#if OLDVRA
float arr[R] __attribute__((annotate("scalar(range(-" PB_XSTR(R) ", " PB_XSTR(R) "))")));
#else
float arr[R] __attribute__((annotate("scalar()")));
#endif

int main(int argc, char const *argv[])
{
    #if OLDVRA
    float acc_gt[2] __attribute__((annotate("scalar(range(-" PB_XSTR(R) ", " PB_XSTR(R) "))")));
    #else
    float acc_gt[2] __attribute__((annotate("scalar()")));
    #endif

    for (int i = 0; i < R; i++) {
        arr[i] = rand_range(RMIN, RMAX);
    }

    float incr1 = rand_range(RMIN, RMAX);
    float incr2 = rand_range(RMIN, RMAX);

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
        float add __attribute__((annotate("scalar(range(-" PB_XSTR(R) ", " PB_XSTR(R) "))"))) = 0;
        float sub __attribute__((annotate("scalar(range(-" PB_XSTR(R) ", " PB_XSTR(R) "))"))) = 0;
        #else
        float add __attribute__((annotate("scalar()"))) = 0;
        float sub __attribute__((annotate("scalar()"))) = 0;
        #endif

        for (int i = 0; i < N; i++) {
            add += incr1;
            sub -= incr2;
        }

        for (int i = 1; i < R; i++) {
            arr[i] = arr[i - 1] + incr1;
        }

        acc_gt[0] = add;
        acc_gt[1] = sub;

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
    for (int j = 0; j < R; ++j)
        printf("%f\n", arr[j]);
    printf("%f\n", acc_gt[0]);
    printf("%f\n", acc_gt[1]);
    printf("Values End\n");

    return 0;
}
