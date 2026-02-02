#pragma once
#include <cstdint>
#include <memory>
#include <string>
#include <vector>
#include <functional>
#include <llvm/Support/raw_ostream.h>

#include <llvm/Analysis/ScalarEvolution.h>

#include "TaffoInfo/RangeInfo.hpp"
#include "RangeOperations.hpp"

namespace taffo {

class RangedRecurrence {
public:
  enum class Kind { Affine, Geometric, Linear, Init, Fake, Unknown };
  virtual ~RangedRecurrence() = default;

  virtual Kind kind() const noexcept { return Kind::Unknown; }
  static bool classof(const RangedRecurrence*) { return true; }

  virtual std::shared_ptr<Range> at(std::uint64_t N) const = 0;

  virtual std::string toString() const = 0;
  virtual void print(llvm::raw_ostream& OS) const { OS << toString(); }

  static const char* kindName(Kind k) {
    switch (k) {
      case Kind::Affine: return "Affine";
      case Kind::Geometric: return "Geometric";
      case Kind::Linear: return "Linear";
      case Kind::Init: return "Init";
      case Kind::Fake: return "Fake";
      default: return "Unknown";
    }
  }

  static std::shared_ptr<Range> scaleByUInt(const std::shared_ptr<Range>& A, std::uint64_t k);
  static std::shared_ptr<Range> scaleByDouble(const std::shared_ptr<Range>& A, double c);

  // Fallback “sum of at(t)” sound e semplice
  std::shared_ptr<Range> fallbackAccInclusive(std::uint64_t N) const;
};

inline llvm::raw_ostream& operator<<(llvm::raw_ostream& OS, const RangedRecurrence& R) {
  R.print(OS);
  return OS;
}

/** ====================== Init (immutable) =========================
 * at(i)      = start        (for every i)
 */
class InitRangedRecurrence final : public RangedRecurrence {
public:
  explicit InitRangedRecurrence(std::shared_ptr<Range> start)
    : Start(std::move(start)) {}

  Kind kind() const noexcept override { return Kind::Init; }
  std::shared_ptr<Range> at(std::uint64_t) const override;
  std::string toString() const override;

  const std::shared_ptr<Range>& getStart() const noexcept { return Start; }

private:
  std::shared_ptr<Range> Start;
};

/** ====================== Fake (recurrence constant) ==========================
 * at(i)      = start        (i == 0)
 *            = step         (otherwise)
 */
class FakeRangedRecurrence final : public RangedRecurrence {
public:
  FakeRangedRecurrence(std::shared_ptr<Range> start, std::shared_ptr<Range> step)
    : Start(std::move(start)), Step(std::move(step)) {}

  Kind kind() const noexcept override { return Kind::Fake; }
  std::shared_ptr<Range> at(std::uint64_t i) const override;
  std::string toString() const override;

private:
  std::shared_ptr<Range> Start;
  std::shared_ptr<Range> Step;
};

/** ====================== Affine =========================
 * at(i)      = start + i * step
 */
class AffineRangedRecurrence final : public RangedRecurrence {
public:
  AffineRangedRecurrence(std::shared_ptr<Range> start, std::shared_ptr<Range> step)
    : Start(std::move(start)), Step(std::move(step)) {}

  Kind kind() const noexcept override { return Kind::Affine; }
  static bool classof(const RangedRecurrence* RR) {
    return RR && RR->kind() == Kind::Affine;
  }

  std::shared_ptr<Range> at(std::uint64_t i) const override;
  std::shared_ptr<Range> envelopeUpTo(std::uint64_t N) const;
  std::string toString() const override;
  void print(llvm::raw_ostream& OS) const override { OS << toString(); }

  const std::shared_ptr<Range>& getStart() const noexcept { return Start; }
  const std::shared_ptr<Range>& getStep()  const noexcept { return Step;  }

private:
  std::shared_ptr<Range> Start;
  std::shared_ptr<Range> Step;
};

/** ===================== Geometric =======================
 * at(i)      = start * ratio^i
 */
class GeometricRangedRecurrence final : public RangedRecurrence {
public:
  GeometricRangedRecurrence(std::shared_ptr<Range> start, std::shared_ptr<Range> ratio)
    : Start(std::move(start)), Ratio(std::move(ratio)) {}

  Kind kind() const noexcept override { return Kind::Geometric; }
  std::shared_ptr<Range> at(std::uint64_t i) const override;
  std::string toString() const override;
  void print(llvm::raw_ostream& OS) const override { OS << toString(); }

  const std::shared_ptr<Range>& getStart() const noexcept { return Start; }
  const std::shared_ptr<Range>& getRatio()  const noexcept { return Ratio;  }

  static std::shared_ptr<Range> powerInterval(std::uint64_t i, double rmin, double rmax);
  static double seriesSum(double r, std::uint64_t N);
  static std::shared_ptr<Range> seriesSumInterval(double rmin, double rmax, std::uint64_t N);

private:
  std::shared_ptr<Range> Start;
  std::shared_ptr<Range> Ratio;
};

// ======================= Linear (order-1) =======================
// Recurrence of the form R(k) = a * R(k-1) + b
// at(k) = a^k * r_0 + b * Σ_{t=0..k-1} a^t
class LinearRangedRecurrence final : public RangedRecurrence {
public:
  LinearRangedRecurrence(std::shared_ptr<Range> start, std::shared_ptr<Range> a, std::shared_ptr<Range> b) : Start(std::move(start)),
      A(std::move(a)),
      B(std::move(b)) {}

  Kind kind() const noexcept override { return Kind::Linear; }

  std::shared_ptr<Range> at(std::uint64_t i) const override;

  std::string toString() const override {
    std::string S;
    llvm::raw_string_ostream OS(S);
    OS << "linear(start = " << (Start ? Start->toString() : "<null>")
       << ", A = " << (A ? A->toString() : "<null>")
       << ", B = " << (B ? B->toString() : "<null>") << ")";
    return OS.str();
  }

  void print(llvm::raw_ostream &OS) const override {
    OS << toString();
  }

  const std::shared_ptr<Range>& getStart() const noexcept { return Start; }
  const std::shared_ptr<Range>& getA()     const noexcept { return A; }
  const std::shared_ptr<Range>& getB()     const noexcept { return B; }

private:
  std::shared_ptr<Range> Start;  // x_0
  std::shared_ptr<Range> A;      // coefficient A
  std::shared_ptr<Range> B;      // constant term B
};

} // namespace taffo
