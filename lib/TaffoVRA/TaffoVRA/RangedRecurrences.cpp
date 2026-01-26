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

// ================= Fake =========================

std::shared_ptr<Range> FakeRangedRecurrence::at(std::uint64_t i) const {
  if (i == 0)
    return Start ? Start->clone() : nullptr;
  return Step ? Step->clone() : nullptr;
}

std::string FakeRangedRecurrence::toString() const {
  std::string s; llvm::raw_string_ostream os(s);
  os << "{" << (Start ? Start->toString() : "<null>")
     << ", ->, " << (Step ? Step->toString() : "<null>") << "}";
  return os.str();
}

// ================= Affine =======================

std::shared_ptr<Range> AffineRangedRecurrence::at(std::uint64_t i) const {
  if (!Start) return Range::Top().clone();
  if (i == 0) return std::make_shared<Range>(*Start);
  auto term = RangedRecurrence::scaleByUInt(Step, i);
  return handleAdd(Start, term);
}

std::shared_ptr<Range> AffineRangedRecurrence::envelopeUpTo(std::uint64_t N) const {
  const double A = Start->min, B = Start->max;
  const double S = Step->min,  T = Step->max;
  const double Nd = static_cast<double>(N);
  const double lo = std::min(A + std::min(0.0, Nd*S), A + std::min(0.0, Nd*T));
  const double hi = std::max(B + std::max(0.0, Nd*S), B + std::max(0.0, Nd*T));
  return std::make_shared<Range>(lo, hi);
}

std::string AffineRangedRecurrence::toString() const {
  std::string s; llvm::raw_string_ostream os(s);
  os << "{" << Start->toString() << ", +, " << Step->toString() << "}";
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
  os << "{" << Start->toString() << ", *, " << Ratio->toString() << "}";
  return os.str();
}

// ================= Polynomial ===================

std::shared_ptr<Range> PolynomialRangedRecurrence::evalHorner(std::uint64_t n) const {
  // Horner over interval coeff: (((C_d * n + C_{d-1}) * n + ...) * n + C_0)
  if (CoeffCount() == 0) return Range::Point(llvm::APFloat(0.0)).clone();
  auto acc = std::make_shared<Range>(*Coeffs.back()); // C_d
  if (CoeffCount() == 1) return acc;
  const auto nI = Range::Point(llvm::APFloat((double)n)).clone();
  for (std::size_t j = CoeffCount()-1; j-- > 0; ) {
    acc = handleMul(acc, nI);
    acc = handleAdd(acc, Coeffs[j]);
  }
  return acc;
}

std::shared_ptr<Range> PolynomialRangedRecurrence::at(std::uint64_t n) const {
  auto out = evalHorner(n);
  taffo::outward(*out);
  return out;
}

double PolynomialRangedRecurrence::sumPowUInt(std::uint64_t N, unsigned k) {
  long double n = (long double)N;
  switch (k) {
    case 0: return (double)(n + 1.0L);
    case 1: return (double)(n*(n+1.0L)/2.0L);
    case 2: return (double)(n*(n+1.0L)*(2.0L*n+1.0L)/6.0L);
    case 3: {
      long double s1 = n*(n+1.0L)/2.0L;
      return (double)(s1*s1);
    }
    default: return std::numeric_limits<double>::quiet_NaN();
  }
}

std::shared_ptr<Range> PolynomialRangedRecurrence::sumPowUIntInterval(std::uint64_t N, unsigned k) {
  double s = sumPowUInt(N, k);
  if (std::isnan(s)) return nullptr;
  return Range::Point(llvm::APFloat(s)).clone();
}

std::string
PolynomialRangedRecurrence::toString() const {
  std::string s; llvm::raw_string_ostream os(s);
  os << "{ poly coeffs=[";
  for (std::size_t i=0;i<CoeffCount();++i) {
    if (i) os << ", ";
    os << Coeffs[i]->toString();
  }
  os << "] }";
  return os.str();
}

// ================= Cumulative ===================

std::shared_ptr<Range> CumulativeRangedRecurrence::sumExclusive(std::uint64_t N) const {
  // Σ_{t=0..N-1} step.at(t)
  if (N == 0) return Range::Point(llvm::APFloat(0.0)).clone();

  // Step Affine => implemented (N·A + H·N(N-1)/2)
  if (Step && Step->kind() == RangedRecurrence::Kind::Affine) {
    const auto *Aff = static_cast<const AffineRangedRecurrence*>(Step.get());
    const auto &A = Aff->getStart();
    const auto &H = Aff->getStep();
    const double Nd = static_cast<double>(N);
    const double tri = Nd * (Nd - 1.0) / 2.0;
    auto NA   = handleMul(A, Range::Point(llvm::APFloat(Nd)).clone());
    auto Htri = handleMul(H, Range::Point(llvm::APFloat(tri)).clone());
    return handleAdd(NA, Htri);
  }

  // Step Geometric → A · S(r, N-1)
  if (Step && Step->kind() == RangedRecurrence::Kind::Geometric) {
    const auto *Geo = static_cast<const GeometricRangedRecurrence*>(Step.get());
    const auto &A = Geo->getStart();
    const auto &R = Geo->getRatio();
    auto S = GeometricRangedRecurrence::seriesSumInterval(R->min, R->max, N-1);
    return handleMul(A, S);
  }

  auto acc = Range::Point(llvm::APFloat(0.0)).clone();
  for (std::uint64_t t = 0; t < N; ++t)
    acc = handleAdd(acc, Step->at(t));
  return acc;
}

std::shared_ptr<Range> CumulativeRangedRecurrence::productExclusive(std::uint64_t N) const {
  // Π_{t=0..N-1} step.at(t), per N=0 → 1
  if (N == 0) return Range::Point(llvm::APFloat(1.0)).clone();

  // Step Geometric → Π (A·r^t) = A^N · r^{N(N-1)/2}
  if (Step && Step->kind() == RangedRecurrence::Kind::Geometric) {
    const auto *Geo = static_cast<const GeometricRangedRecurrence*>(Step.get());
    const auto &A = Geo->getStart();
    const auto &R = Geo->getRatio();
    const std::uint64_t T = (N>0) ? (N*(N-1))/2 : 0;
    auto ApowN = GeometricRangedRecurrence::powerInterval(N, A->min, A->max);
    auto rpowT = GeometricRangedRecurrence::powerInterval(T, R->min, R->max);
    return handleMul(ApowN, rpowT);
  }

  auto acc = Range::Point(llvm::APFloat(1.0)).clone();
  for (std::uint64_t t = 0; t < N; ++t)
    acc = handleMul(acc, Step->at(t));
  return acc;
}

std::shared_ptr<Range>
CumulativeRangedRecurrence::at(std::uint64_t N) const {
  switch (Operation) {
    case Op::Add: {
      // Start + Σ step(0..N-1)
      return handleAdd(Start, sumExclusive(N));
    }
    case Op::Sub: {
      // Start - Σ step(0..N-1)
      return handleSub(Start, sumExclusive(N));
    }
    case Op::Mul: {
      // Start * Π step(0..N-1)
      return handleMul(Start, productExclusive(N));
    }
    case Op::Div: {
      // Start / Π step(0..N-1)
      auto denom = productExclusive(N);
      return handleDiv(Start, denom);
    }
  }
  return std::make_shared<Range>(-INFINITY, +INFINITY);
}

std::string
CumulativeRangedRecurrence::toString() const {
  std::string s; llvm::raw_string_ostream os(s);
  const char* op =
    (Operation==Op::Add? "!+" :
     Operation==Op::Sub? "!-" :
     Operation==Op::Mul? "!*" : "!/");
  os << "{ " << op << ", start=" << Start->toString() << ", step=" << Step->toString() << " }";
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
