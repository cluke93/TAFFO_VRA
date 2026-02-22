#include "TaffoVRA/RangedRecurrences.hpp"

#include <algorithm>
#include <array>
#include <cmath>
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

struct CrossingResults {
  RecurrenceResult first;
  RecurrenceResult second;
};

static RecurrenceResult runGeometricRecurrence(std::mt19937_64 &rng) {
  constexpr std::size_t M = 10;

  std::uniform_real_distribution<double> ratioDist(0.75, 1.25);
  double acc = 1.0;
  for (std::size_t i = 0; i < M; ++i) {
    acc *= ratioDist(rng);
  }

  auto start = std::make_shared<taffo::Range>(1.0, 1.0);
  auto ratio = std::make_shared<taffo::Range>(0.75, 1.25);
  taffo::GeometricRangedRecurrence geo(start, ratio);
  auto expected = geo.at(M);

  const double eps = std::numeric_limits<double>::epsilon();
  const bool inRange = acc + eps >= expected->min && acc - eps <= expected->max;

  return {acc, acc, expected->min, expected->max, inRange};
}

static RecurrenceResult runFlattenedRecurrence(std::mt19937_64 &rng) {
  constexpr std::size_t N = 10;
  constexpr std::size_t M = 8;

  std::uniform_real_distribution<double> ratioDist(0.8, 1.2);
  std::array<std::array<double, M>, N> src{};
  std::array<double, N> dest{};

  for (std::size_t i = 0; i < N; ++i) {
    double acc = 1.0;
    for (std::size_t j = 0; j < M; ++j) {
      const double v = ratioDist(rng);
      src[i][j] = v;
      acc *= v;
    }
    dest[i] = acc;
  }
  (void)src; // mirrors loop shape only

  const double minVal = *std::min_element(dest.begin(), dest.end());
  const double maxVal = *std::max_element(dest.begin(), dest.end());

  auto start = std::make_shared<taffo::Range>(1.0, 1.0);
  auto ratio = std::make_shared<taffo::Range>(0.8, 1.2);
  taffo::GeometricFlattenedRangedRecurrence geoFlat(start, ratio);
  auto expected = geoFlat.at(M);

  const double eps = std::numeric_limits<double>::epsilon();
  const bool inRange = minVal + eps >= expected->min && maxVal - eps <= expected->max;

  return {minVal, maxVal, expected->min, expected->max, inRange};
}

static RecurrenceResult runDeltaRecurrence(std::mt19937_64 &rng) {
  constexpr std::size_t N = 8;
  constexpr std::size_t M = 6;

  std::uniform_real_distribution<double> innerDist(0.7, 1.3);
  std::uniform_real_distribution<double> outerDist(0.85, 1.3);

  double dest = 1.0;
  for (std::size_t i = 0; i < N; ++i) {
    double innerBlock = 1.0;
    for (std::size_t j = 0; j < M; ++j) {
      innerBlock *= innerDist(rng);
    }
    dest *= innerBlock;
    dest *= outerDist(rng);
  }

  auto innerStart = std::make_shared<taffo::Range>(1.0, 1.0);
  auto innerRatio = std::make_shared<taffo::Range>(0.7, 1.3);
  auto innerGeom = std::make_shared<taffo::GeometricRangedRecurrence>(innerStart, innerRatio);

  auto start = std::make_shared<taffo::Range>(1.0, 1.0);
  auto ratio = std::make_shared<taffo::Range>(0.85, 1.3);
  taffo::GeometricDeltaRangedRecurrence geoDelta(start, ratio, innerGeom, M);
  auto expected = geoDelta.at(N);

  const double eps = std::numeric_limits<double>::epsilon();
  const bool inRange = dest + eps >= expected->min && dest - eps <= expected->max;

  return {dest, dest, expected->min, expected->max, inRange};
}

static CrossingResults runCrossingRecurrence(std::mt19937_64 &rng) {
  constexpr std::size_t N = 12;

  std::uniform_real_distribution<double> distFirstStart(1.0, 3.5);
  std::uniform_real_distribution<double> distSecondStart(1.0, 3.0);
  std::uniform_real_distribution<double> distRatioFirst(0.8, 1.4);
  std::uniform_real_distribution<double> distRatioSecond(0.7, 1.3);

  std::array<double, N> first{};
  std::array<double, N> second{};

  first[0] = distFirstStart(rng);
  second[0] = distSecondStart(rng);

  for (std::size_t i = 1; i < N; ++i) {
    const double r1 = distRatioFirst(rng);
    const double r2 = distRatioSecond(rng);
    first[i] = second[i - 1] * r1;
    second[i] = first[i] * r2;
  }

  auto [firstMinIt, firstMaxIt] = std::minmax_element(first.begin(), first.end());
  auto [secondMinIt, secondMaxIt] = std::minmax_element(second.begin(), second.end());
  const double firstMin = *firstMinIt;
  const double firstMax = *firstMaxIt;
  const double secondMin = *secondMinIt;
  const double secondMax = *secondMaxIt;

  const double ratioMin = distRatioFirst.min() * distRatioSecond.min();
  const double ratioMax = distRatioFirst.max() * distRatioSecond.max();

  auto startFirst = std::make_shared<taffo::Range>(0.8, 4.2);
  auto startSecond = std::make_shared<taffo::Range>(1.0, 3.0);
  auto ratio = std::make_shared<taffo::Range>(ratioMin, ratioMax);

  taffo::GeometricCrossingRangedRecurrence firstRec(startFirst, ratio);
  taffo::GeometricCrossingRangedRecurrence secondRec(startSecond, ratio);

  auto expectedFirst = firstRec.at(N - 2);
  auto expectedSecond = secondRec.at(N - 1);

  const double eps = std::numeric_limits<double>::epsilon();
  const bool firstInRange = firstMin + eps >= expectedFirst->min && firstMax - eps <= expectedFirst->max;
  const bool secondInRange = secondMin + eps >= expectedSecond->min && secondMax - eps <= expectedSecond->max;

  return {{firstMin, firstMax, expectedFirst->min, expectedFirst->max, firstInRange},
          {secondMin, secondMax, expectedSecond->min, expectedSecond->max, secondInRange}};
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
    RecurrenceResult res = runGeometricRecurrence(rng);
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

  const char *markGeo = failures == 0 ? green : red;
  const char *symGeo = failures == 0 ? "\u2713" : "x";
  std::cout << markGeo << symGeo << reset << " Geometric results: " << successes << "/"
            << kTrials << " succeeded, " << failures << " failed, widen range [" << widestMin
            << ", " << widestMax << "], computed by RR [" << expectedMin << ", " << expectedMax << "]\n";

  successes = 0;
  failures = 0;
  widestMin = std::numeric_limits<double>::infinity();
  widestMax = -std::numeric_limits<double>::infinity();
  expectedMin = 0.0;
  expectedMax = 0.0;

  for (std::size_t i = 0; i < kTrials; ++i) {
    RecurrenceResult res = runFlattenedRecurrence(rng);
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

  std::cout << markGeo << symGeo << reset << " Geometric flattened results: " << successes << "/"
            << kTrials << " succeeded, " << failures << " failed, widen range ["
            << widestMin << ", " << widestMax << "], computed by RR ["
            << expectedMin << ", " << expectedMax << "]\n";

  successes = 0;
  failures = 0;
  widestMin = std::numeric_limits<double>::infinity();
  widestMax = -std::numeric_limits<double>::infinity();
  expectedMin = 0.0;
  expectedMax = 0.0;

  for (std::size_t i = 0; i < kTrials; ++i) {
    RecurrenceResult res = runDeltaRecurrence(rng);
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

  const char *markDelta = failures == 0 ? green : red;
  const char *symDelta = failures == 0 ? "\u2713" : "x";
  std::cout << markDelta << symDelta << reset << " Geometric delta results: " << successes << "/"
            << kTrials << " succeeded, " << failures << " failed, widen range ["
            << widestMin << ", " << widestMax << "], computed by RR ["
            << expectedMin << ", " << expectedMax << "]\n";

  std::size_t successesFirst = 0;
  std::size_t failuresFirst = 0;
  std::size_t successesSecond = 0;
  std::size_t failuresSecond = 0;
  double widestFirstMin = std::numeric_limits<double>::infinity();
  double widestFirstMax = -std::numeric_limits<double>::infinity();
  double widestSecondMin = std::numeric_limits<double>::infinity();
  double widestSecondMax = -std::numeric_limits<double>::infinity();
  double expectedFirstMin = 0.0;
  double expectedFirstMax = 0.0;
  double expectedSecondMin = 0.0;
  double expectedSecondMax = 0.0;

  for (std::size_t i = 0; i < kTrials; ++i) {
    CrossingResults res = runCrossingRecurrence(rng);

    expectedFirstMin = res.first.expectedMin;
    expectedFirstMax = res.first.expectedMax;
    widestFirstMin = std::min(widestFirstMin, res.first.minVal);
    widestFirstMax = std::max(widestFirstMax, res.first.maxVal);

    expectedSecondMin = res.second.expectedMin;
    expectedSecondMax = res.second.expectedMax;
    widestSecondMin = std::min(widestSecondMin, res.second.minVal);
    widestSecondMax = std::max(widestSecondMax, res.second.maxVal);

    if (res.first.inRange) {
      ++successesFirst;
    } else {
      ++failuresFirst;
      anyFailure = true;
      std::cout << red << "x" << reset << " first range [" << res.first.minVal << ", "
                << res.first.maxVal << "] outside [" << res.first.expectedMin << ", "
                << res.first.expectedMax << "]\n";
    }

    if (res.second.inRange) {
      ++successesSecond;
    } else {
      ++failuresSecond;
      anyFailure = true;
      std::cout << red << "x" << reset << " second range [" << res.second.minVal << ", "
                << res.second.maxVal << "] outside [" << res.second.expectedMin << ", "
                << res.second.expectedMax << "]\n";
    }
  }

  const char *markCrossFirst = failuresFirst == 0 ? green : red;
  const char *symCrossFirst = failuresFirst == 0 ? "\u2713" : "x";
  std::cout << markCrossFirst << symCrossFirst << reset << " Geometric crossing (first) results: "
            << successesFirst << "/" << kTrials << " succeeded, " << failuresFirst
            << " failed, widen range [" << widestFirstMin << ", " << widestFirstMax
            << "], computed by RR [" << expectedFirstMin << ", " << expectedFirstMax << "]\n";

  const char *markCrossSecond = failuresSecond == 0 ? green : red;
  const char *symCrossSecond = failuresSecond == 0 ? "\u2713" : "x";
  std::cout << markCrossSecond << symCrossSecond << reset << " Geometric crossing (second) results: "
            << successesSecond << "/" << kTrials << " succeeded, " << failuresSecond
            << " failed, widen range [" << widestSecondMin << ", " << widestSecondMax
            << "], computed by RR [" << expectedSecondMin << ", " << expectedSecondMax << "]\n";

  return anyFailure ? 1 : 0;
}
