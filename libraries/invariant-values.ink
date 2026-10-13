module ink.knowledge.invariant_values;

// Module-owned representations carry ordinary checked predicates. Callers use
// the public operations; algorithms and evidence remain database definitions.
abstract refined record Unique<T> { items:List<T>, } invariant unique(value.items);

spec fn wrap_unique<T>(items:List<T>)->Unique<T>
 requires unique(items);
 ensures result.items==items;
implementation unique_direct for wrap_unique {return Unique<T>{items:items};}

fn elements<T>(value:Unique<T>)->List<T> {return value.items;}
spec fn known_unique<T>(value:Unique<T>)->Bool ensures result;
implementation unique_observation for known_unique {return unique(value.items);}

abstract refined record SortedWords { items:List<u32>, } invariant value.items.sort()==value.items;
spec fn wrap_sorted(items:List<u32>)->SortedWords
 requires items.sort()==items;
 ensures result.items==items;
implementation sorted_direct for wrap_sorted {return SortedWords{items:items};}

fn sorted_elements(value:SortedWords)->List<u32> {return value.items;}
spec fn known_sorted(value:SortedWords)->Bool ensures result;
implementation sorted_observation for known_sorted {return value.items.sort()==value.items;}

abstract refined record BoundedIndex { index:u32, limit:u32, } invariant value.index<value.limit;
spec fn bound(index:u32,limit:u32)->BoundedIndex
 requires index<limit;
 ensures result.index==index;
 ensures result.limit==limit;
implementation bound_direct for bound {return BoundedIndex{index:index,limit:limit};}

fn position(value:BoundedIndex)->u32 {return value.index;}
fn extent(value:BoundedIndex)->u32 {return value.limit;}
spec fn in_bounds(value:BoundedIndex)->Bool ensures result;
implementation bounded_observation for in_bounds {return value.index<value.limit;}

// A relational guarantee binds the index to this exact immutable sequence.
// The same predicate is available to semantic laws and physical-read proofs.
abstract refined record IndexedWords { items:List<u32>, index:u32, }
 invariant value.index<length(value.items);
fn indexed_value(value:IndexedWords,fallback:u32)->u32 {
 return value.items.at_or(value.index,fallback);
}
spec fn indexed_valid(value:IndexedWords)->Bool ensures result;
implementation indexed_observation for indexed_valid {
 return value.index<length(value.items);
}
