#include "RangedRecurrences.hpp"
#include "RangeOperations.hpp"
#include "Debug/Logger.hpp"
#include <llvm/Analysis/ScalarEvolutionExpressions.h>

#include <cmath>
#include <limits>
#include <algorithm>
#include <sstream>
#include <limits>
#include <string>

#define DEBUG_TYPE "taffo-vra"

using namespace taffo;

namespace {
inline std::string rangeToString(const std::shared_ptr<Range>& R) {
  return R ? R->toString() : "<null>";
}
} // namespace

// ================= Base helpers =================

std::shared_ptr<Range>
RangedRecurrence::scaleByUInt(const std::shared_ptr<Range>& A, std::uint64_t k) {
  return handleMul(A, Range::Point(llvm::APFloat(static_cast<double>(k))).clone());
}

std::shared_ptr<Range>
RangedRecurrence::scaleByDouble(const std::shared_ptr<Range>& A, double c) {
  return handleMul(A, Range::Point(llvm::APFloat(c)).clone());
}

std::shared_ptr<Range>
RangedRecurrence::fallbackAccInclusive(std::uint64_t N) const {
  auto acc = Range::Point(llvm::APFloat(0.0)).clone();
  for (std::uint64_t t = 0; t <= N; ++t) {
    acc = handleAdd(acc, this->at(t));
  }
  return acc;
}

// ================= Init =========================

std::shared_ptr<Range> InitRangedRecurrence::at(std::uint64_t) const {
  // Immutable seed: reuse the stored range, fallback to Top to stay sound.
  return Start ? Start : Range::Top().clone();
}

std::string InitRangedRecurrence::toString() const {
  std::string s; llvm::raw_string_ostream os(s);
  os << "init(start = " << rangeToString(Start) << ")";
  return os.str();
}

// ================= Fake =========================

std::shared_ptr<Range> FakeRangedRecurrence::at(std::uint64_t i) const {
  if (i == 0)
    return Start ? Start->clone() : nullptr;
  return Step ? Step->clone() : nullptr;
}

std::string FakeRangedRecurrence::toString() const {
  std::string s; llvm::raw_string_ostream os(s);
  os << "fake(start = " << rangeToString(Start)
     << ", end = " << rangeToString(Step) << ")";
  return os.str();
}

// ================= Affine =======================

std::shared_ptr<Range> AffineRangedRecurrence::at(std::uint64_t i) const {
  if (!Start) return Range::Top().clone();
  if (i == 0) return std::make_shared<Range>(*Start);
  auto term = RangedRecurrence::scaleByUInt(Step, i);
  return handleAdd(Start, term);
}

std::string AffineRangedRecurrence::toString() const {
  std::string s; llvm::raw_string_ostream os(s);
  if (Step && Step->isTop()) {
    os << "unknown(start = " << rangeToString(Start) << ", end = TOP)";
  } else {
    os << "affine(start = " << rangeToString(Start)
       << ", step = " << rangeToString(Step) << ")";
  }
  return os.str();
}

// ================= Affine flattened =======================

std::shared_ptr<Range> AffineFlattenedRangedRecurrence::at(std::uint64_t i) const {
  if (!Start) return Range::Top().clone();
  if (i == 0) return std::make_shared<Range>(*Start);
  auto term = RangedRecurrence::scaleByUInt(Step, i);
  return handleAdd(Start, term);
}

std::string AffineFlattenedRangedRecurrence::toString() const {
  std::string s; llvm::raw_string_ostream os(s);
  if (Step && Step->isTop()) {
    os << "unknown(start = " << rangeToString(Start) << ", end = TOP)";
  } else {
    os << "affine_flattened(start = " << rangeToString(Start)
       << ", step = " << rangeToString(Step) << ")";
  }
  return os.str();
}

// ================= Affine delta =======================

std::shared_ptr<Range> AffineDeltaRangedRecurrence::at(std::uint64_t i) const {
  if (!Start) return Range::Top().clone();
  if (i == 0) return std::make_shared<Range>(*Start);

  if (!Step || !InnerAffine)
    return Range::Top().clone();

  auto stepIn = InnerAffine->getStep();
  if (!stepIn)
    return Range::Top().clone();

  std::shared_ptr<Range> innerBlock;
  if (InnerTC == 0) {
    innerBlock = Range::Point(llvm::APFloat(0.0)).clone();
  } else {
    innerBlock = RangedRecurrence::scaleByUInt(stepIn, InnerTC);
    if (!innerBlock)
      return Range::Top().clone();
  }

  auto perOuter = handleAdd(innerBlock, Step);
  if (!perOuter)
    return Range::Top().clone();

  auto totalDelta = RangedRecurrence::scaleByUInt(perOuter, i);
  if (!totalDelta)
    return Range::Top().clone();

  auto res = handleAdd(Start, totalDelta);
  return res ? res : Range::Top().clone();
}

std::string AffineDeltaRangedRecurrence::toString() const {
  std::string s; llvm::raw_string_ostream os(s);
  auto stepIn = InnerAffine ? InnerAffine->getStep() : nullptr;
  if (Step && Step->isTop()) {
    os << "unknown(start = " << rangeToString(Start) << ", end = TOP)";
  } else {
    os << "affine_delta(start = " << rangeToString(Start)
       << ", step_out = " << rangeToString(Step)
       << ", step_in = " << rangeToString(stepIn)
       << ", inner_tc = " << InnerTC << ")";
  }
  return os.str();
}

// ================= Affine crossing =======================

std::shared_ptr<Range> AffineCrossingRangedRecurrence::at(std::uint64_t i) const {
  if (!Start) return Range::Top().clone();
  if (i == 0 || i == 1) return std::make_shared<Range>(*Start);
  auto term = RangedRecurrence::scaleByUInt(Step, i - 1); //this RR values after first recurrence
  return handleAdd(Start, term);
}

std::string AffineCrossingRangedRecurrence::toString() const {
  std::string s; llvm::raw_string_ostream os(s);
  if (Step && Step->isTop()) {
    os << "unknown(start = " << rangeToString(Start) << ", end = TOP)";
  } else {
    os << "affine_crossing(start = " << rangeToString(Start)
       << ", step = " << rangeToString(Step) << ")";
  }
  return os.str();
}

// ================= Geometric flattened ====================

std::shared_ptr<Range> GeometricFlattenedRangedRecurrence::at(std::uint64_t i) const {
  if (!Start) return Range::Top().clone();
  if (!Ratio) return Range::Top().clone();
  auto powIv = GeometricRangedRecurrence::powerInterval(i, Ratio->min, Ratio->max);
  auto out = handleMul(Start, powIv);
  if (out) taffo::outward(*out);
  return out ? out : Range::Top().clone();
}

std::string GeometricFlattenedRangedRecurrence::toString() const {
  std::string s; llvm::raw_string_ostream os(s);
  if (Ratio && Ratio->isTop()) {
    os << "unknown(start = " << rangeToString(Start) << ", end = TOP)";
  } else {
    os << "geometric_flattened(start = " << rangeToString(Start)
       << ", ratio = " << rangeToString(Ratio) << ")";
  }
  return os.str();
}

// ================= Geometric delta ====================

std::shared_ptr<Range> GeometricDeltaRangedRecurrence::at(std::uint64_t i) const {
  if (!Start) return Range::Top().clone();
  if (i == 0) return std::make_shared<Range>(*Start);
  if (!Ratio || !InnerGeom) return Range::Top().clone();

  auto innerRatio = InnerGeom->getRatio();
  if (!innerRatio) return Range::Top().clone();

  std::shared_ptr<Range> innerBlock;
  if (InnerTC == 0) {
    innerBlock = Range::Point(llvm::APFloat(1.0)).clone();
  } else {
    innerBlock = GeometricRangedRecurrence::powerInterval(InnerTC, innerRatio->min, innerRatio->max);
  }
  if (!innerBlock) return Range::Top().clone();

  auto perOuter = handleMul(innerBlock, Ratio);
  if (!perOuter) return Range::Top().clone();

  auto totalPow = GeometricRangedRecurrence::powerInterval(i, perOuter->min, perOuter->max);
  if (!totalPow) return Range::Top().clone();

  auto res = handleMul(Start, totalPow);
  if (res) taffo::outward(*res);
  return res ? res : Range::Top().clone();
}

std::string GeometricDeltaRangedRecurrence::toString() const {
  std::string s; llvm::raw_string_ostream os(s);
  auto innerRatio = InnerGeom ? InnerGeom->getRatio() : nullptr;
  if (Ratio && Ratio->isTop()) {
    os << "unknown(start = " << rangeToString(Start) << ", end = TOP)";
  } else {
    os << "geometric_delta(start = " << rangeToString(Start)
       << ", ratio_out = " << rangeToString(Ratio)
       << ", ratio_in = " << rangeToString(innerRatio)
       << ", inner_tc = " << InnerTC << ")";
  }
  return os.str();
}

// ================= Geometric crossing ====================

std::shared_ptr<Range> GeometricCrossingRangedRecurrence::at(std::uint64_t i) const {
  if (!Start) return Range::Top().clone();
  if (!Ratio) return Range::Top().clone();
  if (i == 0 || i == 1) return std::make_shared<Range>(*Start);
  auto powIv = GeometricRangedRecurrence::powerInterval(i - 1, Ratio->min, Ratio->max);
  auto out = handleMul(Start, powIv);
  if (out) taffo::outward(*out);
  return out ? out : Range::Top().clone();
}

std::string GeometricCrossingRangedRecurrence::toString() const {
  std::string s; llvm::raw_string_ostream os(s);
  if (Ratio && Ratio->isTop()) {
    os << "unknown(start = " << rangeToString(Start) << ", end = TOP)";
  } else {
    os << "geometric_crossing(start = " << rangeToString(Start)
       << ", ratio = " << rangeToString(Ratio) << ")";
  }
  return os.str();
}

// ================= Geometric ====================

std::shared_ptr<Range> GeometricRangedRecurrence::powerInterval(std::uint64_t i, double rmin, double rmax) {
  if (i == 0) return std::make_shared<Range>(1.0, 1.0);
  const double a = std::pow(rmin, (double)i);
  const double b = std::pow(rmax, (double)i);
  if (i % 2 == 1) {
    return std::make_shared<Range>(std::min(a,b), std::max(a,b));
  }
  const bool crossesZero = (rmin <= 0.0 && 0.0 <= rmax);
  const double lo = crossesZero ? 0.0 : std::min(a,b);
  const double hi = std::max(a,b);
  return std::make_shared<Range>(lo, hi);
}

double GeometricRangedRecurrence::seriesSum(double r, std::uint64_t N) {
  if (r == 1.0) return (double)N + 1.0;
  const double rp = std::pow(r, (double)(N + 1));
  return (1.0 - rp) / (1.0 - r);
}

std::shared_ptr<Range> GeometricRangedRecurrence::seriesSumInterval(double rmin, double rmax, std::uint64_t N) {
  double samples[5]; int m = 0;
  samples[m++] = rmin;
  if (rmax != rmin) samples[m++] = rmax;
  if (rmin <= -1.0 && -1.0 <= rmax) samples[m++] = -1.0;
  if (rmin <=  0.0 &&  0.0 <= rmax) samples[m++] =  0.0;
  if (rmin <=  1.0 &&  1.0 <= rmax) samples[m++] =  1.0;

  double lo = +std::numeric_limits<double>::infinity();
  double hi = -std::numeric_limits<double>::infinity();
  for (int i = 0; i < m; ++i) {
    const double s = seriesSum(samples[i], N);
    lo = std::min(lo, s);
    hi = std::max(hi, s);
  }
  return std::make_shared<Range>(lo, hi);
}

std::shared_ptr<Range> GeometricRangedRecurrence::at(std::uint64_t i) const {
  if (!Start) return Range::Top().clone();
  auto powIv = powerInterval(i, Ratio->min, Ratio->max);
  auto out =  handleMul(Start, powIv);
  taffo::outward(*out);
  return out;
}

std::string GeometricRangedRecurrence::toString() const {
  std::string s; llvm::raw_string_ostream os(s);
  os << "geometric(start = " << rangeToString(Start)
     << ", ratio = " << rangeToString(Ratio) << ")";
  return os.str();
}

// ===================== Linear (ordine-1) =======================
std::shared_ptr<Range> LinearRangedRecurrence::at(std::uint64_t i) const {
  if (!Start || !A || !B)
    return nullptr;

  // x_0 = Start
  auto cur = Start->clone();

  // Se i==0, restituiamo subito
  if (i == 0)
    return cur;

  // Iterazione naive:
  //   x_{k+1} = A * x_k + B
  // per k = 0..i-1
  for (std::uint64_t k = 0; k < i; ++k) {
    // prod = A * cur
    auto prod = taffo::handleMul(A, cur);
    if (!prod)
      return nullptr;

    // cur = prod + B
    cur = taffo::handleAdd(prod, B);
    if (!cur)
      return nullptr;
  }

  return cur;
}
