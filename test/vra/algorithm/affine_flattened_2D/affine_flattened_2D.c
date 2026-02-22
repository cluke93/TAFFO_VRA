#include <stdint.h>
#include <stdio.h>

#ifndef M
#define M 1
#endif

#define R 300
#define C 300

/**
 * An extra iterator k is between i and j: this increment j times the accumulation (syrk2, gemm).
 * We can consider this as flatten recurrence
 */

static inline float __attribute__((annotate("scalar(range(0, 1) disabled)"))) fast_rand01(void) {
    static uint64_t state = 0xC0FFEE1234ULL;
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    uint64_t x = state * 2685821657736338717ULL;
    return (float)((x >> 11) * (1.0 / 9007199254740992.0)); // 2^53, cast to float
}

static inline float __attribute__((annotate("scalar(range(-0.5, 1) final disabled)"))) rand_range(float min, float max) {
    return min + (max - min) * fast_rand01();
}

static inline float __attribute__((annotate("scalar(range(1, 2) final disabled)"))) rand_range2(float min, float max) {
    return min + (max - min) * fast_rand01();
}

float data[R][C] __attribute__((annotate("scalar()")));
float data2[R][C] __attribute__((annotate("scalar()")));
float dest[R][C] __attribute__((annotate("scalar()")));

int main(int argc, char const *argv[])
{

    for (int i = 0; i < R; i++) {
        for (int j = 0; j < C; j++) {
            data[i][j] = rand_range(-0.5f, 1.0f);
            data2[i][j] = rand_range2(1.0f, 2.0f);
        }
    }

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

        for (int i = 0; i < R; i++) {
            for (int j = 0; j < C; j++) {
                dest[i][j] = rand_range(1.0f, 2.0f);
            }
        }


        for (int i = 0; i < R; i++) {
            for (int k = 0; k < C; k++)
                for (int j = 0; j < i; j++)
                    dest[i][j] += data[j][k] * 1.2f * data2[i][k] + data2[j][k] * 1.2f * data[i][k];
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
    for (int i = 0; i < R; ++i)
        for (int j = 0; j <= C; j++)
            printf("%f\n", dest[i][j]);
    printf("Values End\n");

    return 0;
}
