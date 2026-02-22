/**
 * Minimal PolyBench-like test
 * - init(): writes coeff and fills data
 * - kernel(): writes coeff, reduces rows into res, then divides by coeff
 * - print_res(): prints results
 */

#include <stdint.h>
#include <stdio.h>

#ifndef M
#define M 1
#endif

#define R 100
#define C 40
#define K 1000.0f

static void init_array(int r, int c, float data[R][C], float *coeff) {
  *coeff = K;

  for (int i = 0; i < r; i++) {
    for (int j = 0; j < c; j++) {
      /* i*j/coeff */
      data[i][j] = ((float)i * (float)j) / (*coeff);
    }
  }
}

static void kernel(int r, int c, float data[R][C], float res[R], float *coeff) {

  for (int i = 0; i < r; i++) {
    float acc = 0.0f;
    for (int j = 0; j < c; j++) {
      acc += data[i][j];
    }
    
    res[i] = acc / (*coeff);
  }
}

static void print_res(int r, const float res[R]) {
  puts("Values Begin");
  for (int i = 0; i < r; i++) {
    printf("%f\n", res[i]);
  }
  puts("Values End");
}

int main(void) {
    float __attribute__((annotate("scalar(range(0, 0) )"))) data[R][C];
    float __attribute__((annotate("scalar(range(0, 0) )"))) res[R];
    float coeff;

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


        init_array(R, C, data, &coeff);
        kernel(R, C, data, res, &coeff);
        
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

    print_res(R, res);

  return 0;
}
