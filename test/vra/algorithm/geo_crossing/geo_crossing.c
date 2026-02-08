#include <stdint.h>
#include <stdio.h>

#ifndef M
#define M 1
#endif

#define R 100

static inline float __attribute__((annotate("scalar(range(0, 1) disabled)"))) fast_rand01(void) {
    static uint64_t state = 0xC0FFEE1234ULL;
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    uint64_t x = state * 2685821657736338717ULL;
    return (float)((x >> 11) * (1.0 / 9007199254740992.0)); // 2^53, cast to float
}

static inline float rand_range(float min, float max) {
    return min + (max - min) * fast_rand01();
}

double src_left[R] __attribute__((annotate("scalar(range(1, 16))")));
double src_right[R] __attribute__((annotate("scalar(range(1, 16))")));
double left[R] __attribute__((annotate("scalar(range(1, 1))")));
double right[R] __attribute__((annotate("scalar(range(1, 1))")));

int main(int argc, char const *argv[])
{

    for (int i = 0; i < R; i++) {
        src_left[i] = rand_range(1.002f, 15.016f);
        src_right[i] = rand_range(1.021f, 15.08f);
    }

    for (int m = 0; m < M; ++m) {
        uint32_t cycles_high1 = 0;
        uint32_t cycles_high = 0;
        uint32_t cycles_low = 0;
        uint32_t cycles_low1 = 0;

        for (int i = 0; i < R; i++) {
            left[i] = src_left[i];
            right[i] = src_right[i];
        }

        asm volatile("CPUID\n\t"
                    "RDTSC\n\t"
                    "mov %%edx, %0\n\t"
                    "mov %%eax, %1\n\t"
                    : "=r"(cycles_high), "=r"(cycles_low)::"%rax", "%rbx", "%rcx", "%rdx");

                    
        for (int i = 1; i < R; i++) {
            left[i] = right[i-1] * 1.013f;
            right[i] = left[i-1] * 3.004f;
        }

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
    for (int j = 0; j < R; ++j) {
        printf("%f\n", left[j]);
        printf("%f\n", right[j]);
    }
    printf("Values End\n");

    return 0;
}
