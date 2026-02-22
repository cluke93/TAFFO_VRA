#include <stdint.h>
#include <stdio.h>
#include "../config.h"

static inline float __attribute__((annotate("scalar(range(0, 1) disabled)"))) fast_rand01(void) {
    static uint64_t state = 0xC0FFEE1234ULL;
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    uint64_t x = state * 2685821657736338717ULL;
    return (float)((x >> 11) * (1.0 / 9007199254740992.0)); // 2^53, cast to float
}

static inline float __attribute__((annotate("scalar(range(" PB_XSTR(RMIN) ", " PB_XSTR(RMAX) ") final disabled)"))) rand_range(float min, float max) {
    return min + (max - min) * fast_rand01();
}

#if OLDVRA
float data[R][C] __attribute__((annotate("scalar(range(-" PB_XSTR(R) ", " PB_XSTR(R) "))")));
#else
float data[R][C] __attribute__((annotate("scalar(range(0,0))")));
#endif

int main(int argc, char const *argv[])
{

    #if OLDVRA
    float sum_gt[1] __attribute__((annotate("scalar(range(-75000, 150000))")));
    float acc_gt[1] __attribute__((annotate("scalar(range(-75000, 150000))")));
    #else
    float sum_gt[1] __attribute__((annotate("scalar(range(0,0))")));
    float acc_gt[1] __attribute__((annotate("scalar(range(0,0))")));
    #endif

    for (int i = 0; i < R; i++) {
        for (int j = 0; j < C; j++) {
            data[i][j] = rand_range(RMIN, RMAX);
        }
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
        float sum __attribute__((annotate("scalar(range(-75000, 150000))"))) = 0;
        float acc __attribute__((annotate("scalar(range(-75000, 150000))"))) = 0;
        #else
        float sum __attribute__((annotate("scalar(range(0,0))"))) = 0;
        float acc __attribute__((annotate("scalar(range(0,0))"))) = 0;
        #endif

        for (int i = 0; i < R; i++) {
            for (int j = 0; j < C; j++) {
                sum += incr1;
                acc += data[i][j];
            }
            sum -= incr2;
        }

        sum_gt[0] = sum;
        acc_gt[0] = acc;

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
    printf("%f\n", sum_gt[0]);
    printf("%f\n", acc_gt[0]);
    printf("Values End\n");

    return 0;
}
