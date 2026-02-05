#pragma once
#include <cstdint>
#include <memory>
#include <type_traits>
#include <string>
#include <vector>
#include <functional>
#include <llvm/Support/raw_ostream.h>

#include <llvm/Analysis/ScalarEvolution.h>

#include "TaffoInfo/RangeInfo.hpp"
#include "RangeOperations.hpp"

namespace taffo {

class GeometricRangedRecurrence;

class RangedRecurrence {
public:
  enum class Kind {
    Affine,
    AffineFlattened,
    AffineDelta,
    AffineCrossing,
    Geometric,
    GeometricFlattened,
    GeometricDelta,
    GeometricCrossing,
    Linear,
    Init,
    Fake,
    Unknown
  };
  virtual ~RangedRecurrence() = default;

  virtual Kind kind() const noexcept { return Kind::Unknown; }
  static bool classof(const RangedRecurrence*) { return true; }

  virtual std::shared_ptr<Range> at(std::uint64_t N) const = 0;

  virtual std::string toString() const = 0;
  virtual void print(llvm::raw_ostream& OS) const { OS << toString(); }

  static const char* kindName(Kind k) {
    switch (k) {
      case Kind::Affine: return "Affine";
      case Kind::AffineFlattened: return "Affine flatting";
      case Kind::AffineDelta: return "Affine delta";
      case Kind::AffineCrossing: return "Affine crossing";
      case Kind::Geometric: return "Geometric";
      case Kind::GeometricFlattened: return "Geometric flatting";
      case Kind::GeometricDelta: return "Geometric delta";
      case Kind::GeometricCrossing: return "Geometric crossing";
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
  static bool classof(const RangedRecurrence* RR) {
    return RR && RR->kind() == Kind::Init;
  }
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
  static bool classof(const RangedRecurrence* RR) {
    return RR && RR->kind() == Kind::Fake;
  }
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
  std::string toString() const override;
  void print(llvm::raw_ostream& OS) const override { OS << toString(); }

  const std::shared_ptr<Range>& getStart() const noexcept { return Start; }
  const std::shared_ptr<Range>& getStep()  const noexcept { return Step;  }

private:
  std::shared_ptr<Range> Start;
  std::shared_ptr<Range> Step;
};

/** ====================== Affine flattened =========================
 * ex: dst[i] += src[i][j]
 * at(i)      = start + i * step
 */
class AffineFlattinedRangedRecurrence final : public RangedRecurrence {
public:
  AffineFlattinedRangedRecurrence(std::shared_ptr<Range> start, std::shared_ptr<Range> step)
    : Start(std::move(start)), Step(std::move(step)) {}

  Kind kind() const noexcept override { return Kind::AffineFlattened; }
  static bool classof(const RangedRecurrence* RR) {
    return RR && RR->kind() == Kind::AffineFlattened;
  }

  std::shared_ptr<Range> at(std::uint64_t i) const override;
  std::string toString() const override;
  void print(llvm::raw_ostream& OS) const override { OS << toString(); }

  const std::shared_ptr<Range>& getStart() const noexcept { return Start; }
  const std::shared_ptr<Range>& getStep()  const noexcept { return Step;  }

private:
  std::shared_ptr<Range> Start;
  std::shared_ptr<Range> Step;
};

/** ====================== Affine delta =========================
 * ex: affine op crossing two loops
 * at(i)      = start_out + TC_out * (step_out + start_in + TC_in * step_in)
 */

class AffineDeltaRangedRecurrence final : public RangedRecurrence {
public:
  AffineDeltaRangedRecurrence(std::shared_ptr<Range> start, std::shared_ptr<Range> step, std::shared_ptr<AffineRangedRecurrence> innerAffine, u_int64_t innerTC)
    : Start(std::move(start)), Step(std::move(step)), InnerAffine(innerAffine), InnerTC(innerTC) {}

  Kind kind() const noexcept override { return Kind::AffineDelta; }
  static bool classof(const RangedRecurrence* RR) {
    return RR && RR->kind() == Kind::AffineDelta;
  }

  std::shared_ptr<Range> at(std::uint64_t i) const override;
  std::string toString() const override;
  void print(llvm::raw_ostream& OS) const override { OS << toString(); }

  const std::shared_ptr<Range>& getStart() const noexcept { return Start; }
  const std::shared_ptr<Range>& getStep()  const noexcept { return Step;  }
  const std::shared_ptr<AffineRangedRecurrence>& getInnerRR()  const noexcept { return InnerAffine; }
  const u_int64_t getInnerTC()  const noexcept { return InnerTC;  }

private:
  std::shared_ptr<Range> Start;
  std::shared_ptr<Range> Step;
  std::shared_ptr<AffineRangedRecurrence> InnerAffine;
  u_int64_t InnerTC = 0;
};

/** ====================== Affine crossing =========================
 * ex: a = b + x; b = a + y
 * at(i)_a = b_start + i * (x+y)
 * at(i)_b = at(1)_a + y + i * (x+y)
 */
class AffineCrossingRangedRecurrence final : public RangedRecurrence {
public:
  AffineCrossingRangedRecurrence(std::shared_ptr<Range> start, std::shared_ptr<Range> step)
    : Start(std::move(start)), Step(std::move(step)) {}

  Kind kind() const noexcept override { return Kind::AffineCrossing; }
  static bool classof(const RangedRecurrence* RR) {
    return RR && RR->kind() == Kind::AffineCrossing;
  }

  std::shared_ptr<Range> at(std::uint64_t i) const override;
  std::string toString() const override;
  void print(llvm::raw_ostream& OS) const override { OS << toString(); }

  const std::shared_ptr<Range>& getStart() const noexcept { return Start; }
  const std::shared_ptr<Range>& getStep()  const noexcept { return Step;  }

private:
  std::shared_ptr<Range> Start;
  std::shared_ptr<Range> Step;
};

/** ====================== Geometric flattened =========================
 * ex: dst[i] *= src[i][j]
 * at(i)      = start * ratio^i
 */
class GeometricFlattenedRangedRecurrence final : public RangedRecurrence {
public:
  GeometricFlattenedRangedRecurrence(std::shared_ptr<Range> start, std::shared_ptr<Range> ratio)
    : Start(std::move(start)), Ratio(std::move(ratio)) {}

  Kind kind() const noexcept override { return Kind::GeometricFlattened; }
  static bool classof(const RangedRecurrence* RR) {
    return RR && RR->kind() == Kind::GeometricFlattened;
  }

  std::shared_ptr<Range> at(std::uint64_t i) const override;
  std::string toString() const override;
  void print(llvm::raw_ostream& OS) const override { OS << toString(); }

  const std::shared_ptr<Range>& getStart() const noexcept { return Start; }
  const std::shared_ptr<Range>& getRatio()  const noexcept { return Ratio;  }

private:
  std::shared_ptr<Range> Start;
  std::shared_ptr<Range> Ratio;
};

/** ====================== Geometric delta =========================
 * geometric op crossing two loops
 * at(i)      = start_out * (ratio_out * ratio_in^{TC_in})^i
 */
class GeometricDeltaRangedRecurrence final : public RangedRecurrence {
public:
  GeometricDeltaRangedRecurrence(std::shared_ptr<Range> start, std::shared_ptr<Range> ratio,
                                 std::shared_ptr<GeometricRangedRecurrence> innerGeom, u_int64_t innerTC)
    : Start(std::move(start)), Ratio(std::move(ratio)), InnerGeom(std::move(innerGeom)), InnerTC(innerTC) {}

  Kind kind() const noexcept override { return Kind::GeometricDelta; }
  static bool classof(const RangedRecurrence* RR) {
    return RR && RR->kind() == Kind::GeometricDelta;
  }

  std::shared_ptr<Range> at(std::uint64_t i) const override;
  std::string toString() const override;
  void print(llvm::raw_ostream& OS) const override { OS << toString(); }

  const std::shared_ptr<Range>& getStart() const noexcept { return Start; }
  const std::shared_ptr<Range>& getRatio()  const noexcept { return Ratio;  }

private:
  std::shared_ptr<Range> Start;
  std::shared_ptr<Range> Ratio;
  std::shared_ptr<GeometricRangedRecurrence> InnerGeom;
  u_int64_t InnerTC = 0;
};

/** ====================== Geometric crossing =========================
 * ex: a = b * x; b = a * y
 * at(i)_a = b_start * (x*y)^i
 * at(i)_b = at(1)_a * y * (x*y)^i
 */
class GeometricCrossingRangedRecurrence final : public RangedRecurrence {
public:
  GeometricCrossingRangedRecurrence(std::shared_ptr<Range> start, std::shared_ptr<Range> ratio)
    : Start(std::move(start)), Ratio(std::move(ratio)) {}

  Kind kind() const noexcept override { return Kind::GeometricCrossing; }
  static bool classof(const RangedRecurrence* RR) {
    return RR && RR->kind() == Kind::GeometricCrossing;
  }

  std::shared_ptr<Range> at(std::uint64_t i) const override;
  std::string toString() const override;
  void print(llvm::raw_ostream& OS) const override { OS << toString(); }

  const std::shared_ptr<Range>& getStart() const noexcept { return Start; }
  const std::shared_ptr<Range>& getRatio()  const noexcept { return Ratio;  }

private:
  std::shared_ptr<Range> Start;
  std::shared_ptr<Range> Ratio;
};

/** ===================== Geometric =======================
 * at(i)      = start * ratio^i
 */
class GeometricRangedRecurrence final : public RangedRecurrence {
public:
  GeometricRangedRecurrence(std::shared_ptr<Range> start, std::shared_ptr<Range> ratio)
    : Start(std::move(start)), Ratio(std::move(ratio)) {}

  Kind kind() const noexcept override { return Kind::Geometric; }
  static bool classof(const RangedRecurrence* RR) {
    return RR && RR->kind() == Kind::Geometric;
  }
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
  static bool classof(const RangedRecurrence* RR) {
    return RR && RR->kind() == Kind::Linear;
  }

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

namespace llvm {
template <class To>
struct isa_impl_cl<To, std::shared_ptr<taffo::RangedRecurrence>> {
  static inline bool doit(const std::shared_ptr<taffo::RangedRecurrence> &Val) {
    return isa_impl_cl<To, taffo::RangedRecurrence *>::doit(Val.get());
  }
};

template <class To>
struct isa_impl_cl<To, const std::shared_ptr<taffo::RangedRecurrence>> {
  static inline bool doit(const std::shared_ptr<taffo::RangedRecurrence> &Val) {
    return isa_impl_cl<To, taffo::RangedRecurrence *>::doit(Val.get());
  }
};

template <class To>
struct cast_retty_impl<To, std::shared_ptr<taffo::RangedRecurrence>> {
  using ret_type = std::shared_ptr<To>;
};

template <class To>
struct cast_retty_impl<To, const std::shared_ptr<taffo::RangedRecurrence>> {
  using ret_type = std::shared_ptr<const To>;
};

template <class To>
struct cast_convert_val<To, std::shared_ptr<taffo::RangedRecurrence>, std::shared_ptr<taffo::RangedRecurrence>> {
  static inline typename cast_retty<To, std::shared_ptr<taffo::RangedRecurrence>>::ret_type
  doit(const std::shared_ptr<taffo::RangedRecurrence> &Val) {
    return std::static_pointer_cast<To>(Val);
  }
};

template <class To>
struct cast_convert_val<To, const std::shared_ptr<taffo::RangedRecurrence>, std::shared_ptr<taffo::RangedRecurrence>> {
  static inline typename cast_retty<To, const std::shared_ptr<taffo::RangedRecurrence>>::ret_type
  doit(const std::shared_ptr<taffo::RangedRecurrence> &Val) {
    return std::static_pointer_cast<const To>(Val);
  }
};
} // namespace llvm
