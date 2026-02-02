#include "RangeInfo.hpp"

using namespace llvm;
using namespace taffo;

Range::Range(const llvm::fltSemantics& S, llvm::APFloat l, llvm::APFloat u) : sem(&S), lower(llvm::APFloat::getZero(S, false)), upper(llvm::APFloat::getZero(S, false)) {

  if (&l.getSemantics() != sem) {
    bool lose = false;
    l.convert(*sem, llvm::APFloat::rmNearestTiesToEven, &lose);
  }
  if (&u.getSemantics() != sem) {
    bool lose = false;
    u.convert(*sem, llvm::APFloat::rmNearestTiesToEven, &lose);
  }
  lower = std::move(l);
  upper = std::move(u);
  isLowerNegInf = false;
  isUpperPosInf = false;

  normalizeOrder();
  toDouble();
}

Range::Range(double min, double max) : min(min), max(max), sem(&llvm::APFloat::IEEEdouble()), lower(llvm::APFloat::getZero(*sem, false)), upper(llvm::APFloat::getZero(*sem, false)) {
  if (min > max) std::swap(min, max);
  toAPFloat();
  toDouble();
}

void Range::setLower(const APFloat& l) {
  lower = l;
  if (&lower.getSemantics() != sem) {
    bool lose = false;
    lower.convert(*sem, APFloat::rmNearestTiesToEven, &lose);
  }
  isLowerNegInf = false;
  normalizeOrder();
  toDouble();
}
void Range::setUpper(const APFloat& u) {
  upper = u;
  if (&upper.getSemantics() != sem) {
    bool lose = false;
    upper.convert(*sem, APFloat::rmNearestTiesToEven, &lose);
  }
  isUpperPosInf = false;
  normalizeOrder();
  toDouble();
}

void Range::toDouble() {
  min = isLowerNegInf ? -std::numeric_limits<double>::infinity() : lower.convertToDouble();
  max = isUpperPosInf ? +std::numeric_limits<double>::infinity() : upper.convertToDouble();
  if (min > max) std::swap(min, max);
}

void Range::toAPFloat() {
  if (std::isinf(min) && min < 0) isLowerNegInf = true;
  else {
    isLowerNegInf = false;
    APFloat l(min);
    bool lose = false;
    l.convert(*sem, APFloat::rmTowardNegative, &lose);
    lower = std::move(l);
  }

  if (std::isinf(max) && max > 0) isUpperPosInf = true;
  else {
    isUpperPosInf = false;
    APFloat u(max);
    bool lose = false;
    u.convert(*sem, APFloat::rmTowardPositive, &lose);
    upper = std::move(u);
  }
  normalizeOrder();
}

bool Range::isExponentialMonotonic() {
  return min > 1.0 || max < -1.0;
}

bool Range::isOneModular() {
  return (min > 0.0 && max < 1.0) || (max < 0.0 && min > -1.0);
}

bool Range::cross(const APFloat& v) const {
  if (v.isNaN()) return false;
  APFloat x = v;
  if (&x.getSemantics() != sem) {
    bool lose = false;
    x.convert(*sem, APFloat::rmNearestTiesToEven, &lose);
  }
  
  return (isLowerNegInf || x.compare(lower) != APFloat::cmpLessThan) && 
          (isUpperPosInf || x.compare(upper) != APFloat::cmpGreaterThan);
}

bool Range::cross(double val) const { 
  return min <= val && max >= val;
}

std::string Range::toString() const {
  std::stringstream ss;
  if (isLowerNegInf) ss << "[-inf, ";
  else ss << "[" << min << ", ";
  if (isUpperPosInf) ss << "inf]";
  else ss << max << "]";
  return ss.str();
}

json Range::serialize() const {
  json j;
  j["min"] = serializeDouble(isLowerNegInf ? -std::numeric_limits<double>::infinity() : min);
  j["max"] = serializeDouble(isUpperPosInf ? std::numeric_limits<double>::infinity() : max);
  return j;
}

void Range::deserialize(const json& j) {
  min = deserializeDouble(j["min"]);
  max = deserializeDouble(j["max"]);
  normalizeOrder();
  toAPFloat();
}

void Range::normalizeOrder() {
  if (!isLowerNegInf && !isUpperPosInf && lower.compare(upper) == APFloat::cmpGreaterThan) {
    std::swap(lower, upper);
  }
}

Range Range::meet(const Range& R) const {
  Range out(*sem);

  if (isLowerNegInf && R.isLowerNegInf) out.isLowerNegInf = true;
  else {
    out.isLowerNegInf = false;
    if (isLowerNegInf) {
      out.lower = R.lower;
    } else if (R.isLowerNegInf) {
      out.lower = lower;
    } else {
      out.lower = lower.compare(R.lower) == APFloat::cmpGreaterThan ? lower : R.lower;
    }
  }

  if (isUpperPosInf && R.isUpperPosInf) out.isUpperPosInf = true;
  else {
    out.isUpperPosInf = false;
    if (isUpperPosInf) {
      out.upper = R.upper;
    } else if (R.isUpperPosInf) {
      out.upper = upper;
    } else {
      out.upper = upper.compare(R.upper) == APFloat::cmpLessThan ? upper : R.upper;
    }
  }

  out.normalizeOrder();
  out.toDouble();
  return out;
}

Range Range::join(const Range& R) const {
  Range out(*sem);

  if (isLowerNegInf || R.isLowerNegInf) out.isLowerNegInf = true;
  else {
    out.isLowerNegInf = false;
    out.lower = lower.compare(R.lower) == APFloat::cmpLessThan ? lower : R.lower;
  }

  if (isUpperPosInf || R.isUpperPosInf) out.isUpperPosInf = true;
  else {
    out.isUpperPosInf = false;
    out.upper = upper.compare(R.upper) == APFloat::cmpGreaterThan ? upper : R.upper;
  }

  out.normalizeOrder();
  out.toDouble();
  return out;
}

Range Range::widen(const Range& R) const {
  Range out(*sem);

  if (!isLowerNegInf && !R.isLowerNegInf && R.lower.compare(lower) == APFloat::cmpLessThan) {
    out.isLowerNegInf = true;
  } else {
    out.isLowerNegInf = isLowerNegInf;
    out.lower = lower;
  }

  if (!isUpperPosInf && !R.isUpperPosInf && R.upper.compare(upper) == APFloat::cmpGreaterThan) {
    out.isUpperPosInf = true;
  } else {
    out.isUpperPosInf = isUpperPosInf;
    out.upper = upper;
  }

  out.normalizeOrder();
  out.toDouble();
  return out;
}

Range Range::narrow(const Range& R) const {
  Range out(*sem);

  if (isLowerNegInf && !R.isLowerNegInf) {
    out.lower = R.lower;
  } else {
    out.lower = lower;
    out.isLowerNegInf = isLowerNegInf;
  }

  if (isUpperPosInf && !R.isUpperPosInf) {
    out.upper = R.upper;
  } else {
    out.upper = upper;
    out.isUpperPosInf = isUpperPosInf;
  }

  out.normalizeOrder();
  out.toDouble();
  return out;
}

std::shared_ptr<Range> Range::meet(const std::shared_ptr<Range>& R) const {
  if (!R) return clone();
  auto res = meet(*R);
  return std::make_shared<Range>(std::move(res));
}

std::shared_ptr<Range> Range::join(const std::shared_ptr<Range>& R) const {
  if (!R) return clone();
  auto res = join(*R);
  return std::make_shared<Range>(std::move(res));
}

std::shared_ptr<Range> Range::widen(const std::shared_ptr<Range>& R) const {
  if (!R) return clone();
  auto res = widen(*R);
  return std::make_shared<Range>(std::move(res));
}

std::shared_ptr<Range> Range::narrow(const std::shared_ptr<Range>& R) const {
  if (!R) return clone();
  auto res = narrow(*R);
  return std::make_shared<Range>(std::move(res));
}

Range Range::Point(const llvm::APFloat& V) {
  return Range(V,V);
}

Range Range::Top() {
  return Range();
}
