#include <stdint.h>
#include <stdio.h>

#define M 1000
#define N 50

static inline double __attribute__((annotate("scalar(range(0, 1) disabled)"))) fast_rand01(void) {
    static uint64_t state = 0xC0FFEE1234ULL;
    state ^= state >> 12;
    state ^= state << 25;
    state ^= state >> 27;
    uint64_t x = state * 2685821657736338717ULL;
    return (x >> 11) * (1.0 / 9007199254740992.0); // 2^53
}

static inline float rand_range(float min, float max) {
    return (float)(min + (max - min) * fast_rand01());
}

float arr[N] __attribute__((annotate("scalar(range(-2, 2) final)")));

float foo(float x, float y) {
    return x + y;
}

int main(int argc, char const *argv[])
{

    float __attribute__((annotate("scalar(range(1, 1))"))) acc_gt[3];
    float __attribute__((annotate("scalar(range(1, 1))"))) res[N];

    for (int i = 0; i < N; i++) {
        arr[i] = rand_range(0.0011f, 0.009f);
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

        float __attribute__((annotate("scalar(range(1, 1))"))) mul = 1.2002334;
        float __attribute__((annotate("scalar(range(100, 100))"))) div = 128;
        float __attribute__((annotate("scalar(range(0.9, 1.2))"))) tot = 1.1231249;

        for (int i = 0; i < N; i++) {

            mul *= 1.005f;
            div /= 1.023f;

            tot *= arr[i];
            res[i] = foo(1.002,0.0000055);
        
        }

        for (int i = 1; i < N; i++) {
            res[i] = res[i - 1] * 1.0102225;
        }

        acc_gt[0] = mul;
        acc_gt[1] = div;
        acc_gt[2] = tot;

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
    for (int j = 0; j < N; ++j)
        printf("%f\n", res[j]);
    printf("%f\n", acc_gt[0]);
    printf("%f\n", acc_gt[1]);
    printf("%f\n", acc_gt[2]);
    printf("Values End\n");

    return 0;
}
