#include <math.h>
#include <stdio.h>
#include <stdlib.h>

double deconstify(double value) {
  asm volatile("" : : "r,m"(value) : "memory");
  return value;
}

void swap(float *x, float *y) {
  float temp = *x;
  *x = *y;
  *y = temp;
}

float simple_expression(float a, float b, float c, float d) { return a * c + (b - d) * d; }

float pointer_expression(float a, float b, float c, float d, float *res) {
  *res = a * c + (b - d) * d;
  return (a + b) * (c - d) / d;
}

float conflicting_types(float a, float b, float c, float d, float *res) {
  float __attribute__((annotate("scalar( type(56 36))"))) result = a - b * (a + c / d);
  *res = result;
  return result;
}

int main() {
  float __attribute__((annotate("scalar(type(38 22))"))) a = deconstify(16.5);
  float __attribute__((annotate("scalar(type(45 20))"))) b = deconstify(4.8);
  float __attribute__((annotate("scalar(type(22 18))"))) c = deconstify(1.5);
  float __attribute__((annotate("scalar(type(47 22))"))) d = deconstify(55.22);
  float __attribute__((annotate("scalar(type(45 20))"))) e = deconstify(7.6);

  float __attribute__((annotate("scalar()"))) f = deconstify(33.6);

  float __attribute__((annotate("scalar()"))) g = simple_expression(a, b, c, d);
  float __attribute__((annotate("scalar()"))) h = pointer_expression(a, b, c, f, &d);
  swap(&e, &c);

  float __attribute__((annotate("scalar( type(34 26))"))) k = conflicting_types(a, b, g, h, &a);

  printf("Values Begin\n");
  printf("%f\n", a);
  printf("%f\n", b);
  printf("%f\n", c);
  printf("%f\n", d);
  printf("%f\n", e);
  printf("%f\n", g);
  printf("%f\n", h);
  printf("%f\n", k);
  printf("Values End\n");

  return 0;
}
