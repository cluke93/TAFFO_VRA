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

static RecurrenceResult runFakeRecurrence1D(std::mt19937_64 &rng) {
  constexpr std::size_t N = 32;

  std::uniform_real_distribution<double> initDist(-6.0, 6.0);
  std::uniform_real_distribution<double> deltaDist(-6.0, 6.0);

  std::array<double, N> arr{};
  for (double &v : arr)
    v = initDist(rng);

  for (double &v : arr)
    v += deltaDist(rng);

  const double minVal = *std::min_element(arr.begin(), arr.end());
  const double maxVal = *std::max_element(arr.begin(), arr.end());

  const double storeMin = initDist.min() + deltaDist.min();
  const double storeMax = initDist.max() + deltaDist.max();

  auto start = std::make_shared<taffo::Range>(initDist.min(), initDist.max());
  auto store = std::make_shared<taffo::Range>(storeMin, storeMax);
  auto step = start->join(store);

  taffo::FakeRangedRecurrence fake(start, step);
  auto expected = fake.at(1);

  const double eps = std::numeric_limits<double>::epsilon();
  const bool inRange = minVal + eps >= expected->min && maxVal - eps <= expected->max;

  return {minVal, maxVal, expected->min, expected->max, inRange};
}

static RecurrenceResult runFakeRecurrence2D(std::mt19937_64 &rng) {
  constexpr std::size_t N = 16;
  constexpr std::size_t M = 16;

  std::uniform_real_distribution<double> initDist(-4.0, 4.0);
  std::uniform_real_distribution<double> mulDist(-3.0, 3.0);

  std::array<std::array<double, M>, N> mat{};
  for (auto &row : mat) {
    for (double &v : row)
      v = initDist(rng);
  }

  for (auto &row : mat) {
    for (double &v : row)
      v *= mulDist(rng);
  }

  double minVal = std::numeric_limits<double>::infinity();
  double maxVal = -std::numeric_limits<double>::infinity();
  for (const auto &row : mat) {
    const auto [rowMin, rowMax] = std::minmax_element(row.begin(), row.end());
    minVal = std::min(minVal, *rowMin);
    maxVal = std::max(maxVal, *rowMax);
  }

  const double a = initDist.min();
  const double b = initDist.max();
  const double c = mulDist.min();
  const double d = mulDist.max();
  const double prodMin = std::min({a * c, a * d, b * c, b * d});
  const double prodMax = std::max({a * c, a * d, b * c, b * d});

  auto start = std::make_shared<taffo::Range>(initDist.min(), initDist.max());
  auto store = std::make_shared<taffo::Range>(prodMin, prodMax);
  auto step = start->join(store);

  taffo::FakeRangedRecurrence fake(start, step);
  auto expected = fake.at(1);

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
    RecurrenceResult res = runFakeRecurrence1D(rng);
    expectedMin = res.expectedMin;
    expectedMax = res.expectedMax;
    widestMin = std::min(widestMin, res.minVal);
    widestMax = std::max(widestMax, res.maxVal);

    if (res.inRange) {
      ++successes;
    } else {
      ++failures;
      anyFailure = true;
      std::cout << red << "x" << reset << " range [" << res.minVal << ", "
                << res.maxVal << "] outside [" << res.expectedMin << ", "
                << res.expectedMax << "]\n";
    }
  }

  const char *mark1D = failures == 0 ? green : red;
  const char *sym1D = failures == 0 ? "\u2713" : "x";
  std::cout << mark1D << sym1D << reset << " Fake recurrence 1D results: " << successes
            << "/" << kTrials << " succeeded, " << failures << " failed, widen range ["
            << widestMin << ", " << widestMax << "], computed by RR ["
            << expectedMin << ", " << expectedMax << "]" << std::endl;

  successes = 0;
  failures = 0;
  widestMin = std::numeric_limits<double>::infinity();
  widestMax = -std::numeric_limits<double>::infinity();
  expectedMin = 0.0;
  expectedMax = 0.0;

  for (std::size_t i = 0; i < kTrials; ++i) {
    RecurrenceResult res = runFakeRecurrence2D(rng);
    expectedMin = res.expectedMin;
    expectedMax = res.expectedMax;
    widestMin = std::min(widestMin, res.minVal);
    widestMax = std::max(widestMax, res.maxVal);

    if (res.inRange) {
      ++successes;
    } else {
      ++failures;
      anyFailure = true;
      std::cout << red << "x" << reset << " range [" << res.minVal << ", "
                << res.maxVal << "] outside [" << res.expectedMin << ", "
                << res.expectedMax << "]\n";
    }
  }

  const char *mark2D = failures == 0 ? green : red;
  const char *sym2D = failures == 0 ? "\u2713" : "x";
  std::cout << mark2D << sym2D << reset << " Fake recurrence 2D results: " << successes
            << "/" << kTrials << " succeeded, " << failures << " failed, widen range ["
            << widestMin << ", " << widestMax << "], computed by RR ["
            << expectedMin << ", " << expectedMax << "]" << std::endl;

  return anyFailure ? 1 : 0;
}
