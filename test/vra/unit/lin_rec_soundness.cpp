#include "TaffoVRA/RangedRecurrences.hpp"

#include <algorithm>
#include <array>
#include <cstddef>
#include <iostream>
#include <limits>
#include <random>

struct RecurrenceResult {
  double minVal;
  double maxVal;
  double expectedMin;
  double expectedMax;
  bool inRange;
};

static RecurrenceResult runLinearRecurrence(std::mt19937_64 &rng) {
  constexpr std::size_t N = 10;
  constexpr std::size_t M = 12;

  // Positive-only ranges as requested.
  std::uniform_real_distribution<double> srcDist(0.1, 4.0);
  std::uniform_real_distribution<double> mulDist(0.05, 2.0);
  std::uniform_real_distribution<double> addDist(0.1, 1.0);

  std::array<std::array<double, M>, N> src{};
  std::array<double, N> dst{};

  for (std::size_t i = 0; i < N; ++i) {
    double acc = 0.0;
    for (std::size_t j = 0; j < M; ++j) {
      const double s = srcDist(rng);
      const double mul = mulDist(rng);
      const double add = addDist(rng);
      src[i][j] = s;
      acc += s * mul + add;
    }
    dst[i] = acc;
  }
  (void)src; // shape mirror only

  const double minVal = *std::min_element(dst.begin(), dst.end());
  const double maxVal = *std::max_element(dst.begin(), dst.end());

  const double bMin = srcDist.min() * mulDist.min() + addDist.min();
  const double bMax = srcDist.max() * mulDist.max() + addDist.max();

  auto start = std::make_shared<taffo::Range>(0.0, 0.0);
  auto a = std::make_shared<taffo::Range>(1.0, 1.0); // accumulation: x_{k+1} = x_k + b
  auto b = std::make_shared<taffo::Range>(bMin, bMax);

  taffo::LinearRangedRecurrence linear(start, a, b);
  auto expected = linear.at(M);

  const double eps = std::numeric_limits<double>::epsilon();
  const bool inRange = minVal + eps >= expected->min && maxVal - eps <= expected->max;

  return {minVal, maxVal, expected->min, expected->max, inRange};
}

int main() {
  constexpr std::size_t kTrials = 20;
  const char *green = "\033[32m";
  const char *red = "\033[31m";
  const char *reset = "\033[0m";

  std::mt19937_64 rng(0xC0FFEE1234ULL);
  bool anyFailure = false;

  std::size_t successes = 0;
  std::size_t failures = 0;
  double widestMin = std::numeric_limits<double>::infinity();
  double widestMax = -std::numeric_limits<double>::infinity();
  double expectedMin = 0.0;
  double expectedMax = 0.0;

  for (std::size_t i = 0; i < kTrials; ++i) {
    RecurrenceResult res = runLinearRecurrence(rng);
    expectedMin = res.expectedMin;
    expectedMax = res.expectedMax;
    widestMin = std::min(widestMin, res.minVal);
    widestMax = std::max(widestMax, res.maxVal);

    if (res.inRange) {
      ++successes;
    } else {
      ++failures;
      anyFailure = true;
      std::cout << red << "x" << reset << " range [" << res.minVal << ", " << res.maxVal
                << "] outside [" << res.expectedMin << ", " << res.expectedMax << "]\n";
    }
  }

  const char *mark = failures == 0 ? green : red;
  const char *sym = failures == 0 ? "\u2713" : "x";
  std::cout << mark << sym << reset << " Linear recurrence results: " << successes << "/"
            << kTrials << " succeeded, " << failures << " failed, widen range ["
            << widestMin << ", " << widestMax << "], computed by RR ["
            << expectedMin << ", " << expectedMax << "]" << std::endl;

  return anyFailure ? 1 : 0;
}
