module ink.knowledge.approximation;

// Exact integer arithmetic, including distances between opposite word limits.
fn absolute_error(actual:Int,reference:Int)->Int {
 return choose(actual<reference,reference-actual,actual-reference);
}
fn within_absolute(actual:Int,reference:Int,budget:Int)->Bool {
 return budget>=0 && actual-reference<=budget && reference-actual<=budget;
}
// A rational relative error budget. Zero reference requires an exact result.
fn within_relative(actual:Int,reference:Int,numerator:Int,denominator:Int)->Bool {
 let scale=choose(reference<0,-reference,reference);
 return numerator>=0 && denominator>0 &&
  (actual-reference)*denominator<=scale*numerator &&
  (reference-actual)*denominator<=scale*numerator;
}
// Finite probability space: every list position has equal probability.
// This enumerates the entire declared distribution; it is not a sample estimate.
// Duplicate values deliberately carry repeated weight. Empty spaces are invalid.
fn probability_at_least<T>(space:List<T>,success:fn(T)->Bool,numerator:Int,denominator:Int)->Bool {
 let total:Int=count(space);
 let passed:Int=count(space.filter(success));
 return total>0 && numerator>=0 && denominator>0 && numerator<=denominator &&
  passed*denominator>=total*numerator;
}
