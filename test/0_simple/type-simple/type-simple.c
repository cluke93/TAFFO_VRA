#include <math.h>
#include <stdio.h>
#include <stdlib.h>

double deconstify(double value) {
  asm volatile("" : : "r,m"(value) : "memory");
  return value;
}

int main() {
  float __attribute__((annotate("scalar(type(38 22))"))) a = deconstify(16.5); 
  float __attribute__((annotate("scalar(type(45 20))"))) b = deconstify(4.8);
  float __attribute__((annotate("scalar(type(22 18))"))) c = deconstify(1.5);
  float __attribute__((annotate("scalar(type(47 22))"))) d = deconstify(55.22);
  float __attribute__((annotate("scalar(type(45 20))"))) e = deconstify(7.6);

  float __attribute__((annotate("scalar()"))) f = deconstify(33.6);

  float __attribute__((annotate("scalar()"))) g = a * c + (b - d) * d;
  float __attribute__((annotate("scalar()"))) h = (a + b) * (c - f) / f;
  float __attribute__((annotate("scalar()"))) i = f * g + h / (f - g);
  float __attribute__((annotate("scalar()"))) j = (a + b + c + d + e) / 5.0;

  float __attribute__((annotate("scalar( type(34 26))"))) k = (a + b + c + d + e) / (f + g - h + i - j);
  float __attribute__((annotate("scalar()"))) l = b + e / b - e * b;
  float __attribute__((annotate("scalar( type(56 36))"))) m = b - e / b + e * b;

  printf("Values Begin\n");
  printf("%f\n", g);
  printf("%f\n", h);
  printf("%f\n", i);
  printf("%f\n", j);
  printf("%f\n", k);
  printf("%f\n", l);
  printf("%f\n", m);
  printf("Values End\n");

  return 0;
}
