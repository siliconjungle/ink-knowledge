module ink.knowledge.owned_values;
// Affine accumulation over arbitrary immutable element carriers. Refinement
// guarantees are carried by checked source contracts and database fold laws.
fn copy<T>(items:List<T>)->List<T>{
 var output:Buffer<T>=Buffer.empty();
 for item in items {output=output.push(item);}
 return output.freeze();
}
