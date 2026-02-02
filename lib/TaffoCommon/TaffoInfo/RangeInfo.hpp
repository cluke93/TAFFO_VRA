#pragma once

#include "../SerializationUtils.hpp"

#include <limits>
#include <cmath>

#include <llvm/ADT/APFloat.h>

namespace taffo {

struct Range : public Serializable, public tda::Printable {

  // ===== PROPERTIES =====

  double min = -std::numeric_limits<double>::infinity();
  double max = +std::numeric_limits<double>::infinity();

  const llvm::fltSemantics* sem;

  llvm::APFloat lower;
  llvm::APFloat upper;

  bool isLowerNegInf = true;
  bool isUpperPosInf = true;

  // ===== CONSTRUCTORS =====

  Range(const llvm::fltSemantics& S = llvm::APFloat::IEEEdouble()) 
    : sem(&S), 
      lower(llvm::APFloat::getZero(S)), upper(llvm::APFloat::getZero(S)) {}

  /// @brief Constructor by copy
  /// @param other 
  Range(const Range& other) 
    : min(other.min), max(other.max), 
      sem(other.sem),
      lower(other.lower), upper(other.upper),
      isLowerNegInf(other.isLowerNegInf), isUpperPosInf(other.isUpperPosInf) {}

  /// @brief create range by doubles
  /// @param min 
  /// @param max 
  Range(double min, double max);

  Range(const llvm::fltSemantics& S, llvm::APFloat l, llvm::APFloat u);

  Range(llvm::APFloat l, llvm::APFloat u) 
    : Range(llvm::APFloat::IEEEdouble(), l, u) {}

  std::shared_ptr<Range> clone() const {
    return std::make_shared<Range>(*this);
  }

  std::shared_ptr<Range> deepClone() const {
    auto r = std::make_shared<Range>(llvm::APFloat(lower), llvm::APFloat(upper));
    r->min = this->min;
    r->max = this->max;
    r->sem = this->sem;
    r->isLowerNegInf = this->isLowerNegInf;
    r->isUpperPosInf = this->isUpperPosInf;
    return r;
  }

  // ===== SETTERS =====
  void setLower(const llvm::APFloat& l);
  void setUpper(const llvm::APFloat& u);

  // ===== PARSER =====

  void toDouble();
  void toAPFloat();

  // ===== UTILITIES =====

  bool cross(const llvm::APFloat& v) const;
  bool cross(double val = 0.0) const;
  bool isConstant() const { return lower.compare(upper) == llvm::APFloat::cmpEqual; }
  bool isTop() const { return isLowerNegInf && isUpperPosInf; }
  bool isValid() const { return lower.compare(upper) == llvm::APFloat::cmpLessThan; }

  bool isExponentialMonotonic();

  bool isOneModular();

  Range meet(const Range& R) const;
  Range join(const Range& R) const;
  Range widen(const Range& R) const;
  Range narrow(const Range& R) const;

  std::shared_ptr<Range> meet(const std::shared_ptr<Range>& R) const;
  std::shared_ptr<Range> join(const std::shared_ptr<Range>& R) const;
  std::shared_ptr<Range> widen(const std::shared_ptr<Range>& R) const;
  std::shared_ptr<Range> narrow(const std::shared_ptr<Range>& R) const;

  // ===== DEBUG / STORAGE =====

  std::string toString() const override;
  json serialize() const override;
  void deserialize(const json& j) override;

  // ===== UTILITIES =====
  static Range Point(const llvm::APFloat& V);
  static Range Top();

private:

  void normalizeOrder();


};

inline double roundDown(double x) {
  if (std::isnan(x) || std::isinf(x)) return x;
  return std::nextafter(x, -std::numeric_limits<double>::infinity());
}
inline double roundUp(double x) {
  if (std::isnan(x) || std::isinf(x)) return x;
  return std::nextafter(x, +std::numeric_limits<double>::infinity());
}

// Spinge sia i double (min/max) sia gli APFloat (lower/upper) verso l’esterno.
// Non tocca gli infiniti.
inline void outward(taffo::Range& R) {
  // Double view
  if (!std::isinf(R.min)) R.min = roundDown(R.min);
  if (!std::isinf(R.max)) R.max = roundUp(R.max);
  // APFloat view
  if (!R.isLowerNegInf) {
    llvm::APFloat l = R.lower;
    (void)l.next(/*nextGreater=*/false); // passo verso -inf
    R.lower = std::move(l);
  }
  if (!R.isUpperPosInf) {
    llvm::APFloat u = R.upper;
    (void)u.next(/*nextGreater=*/true);  // passo verso +inf
    R.upper = std::move(u);
  }
  // Riallinea double a partire dagli APFloat aggiornati
  R.toDouble();
}

} // namespace taffo
