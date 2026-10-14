module ragged_components;
law append_values<T>(first:Buffer<T>,second:Buffer<T>){
 first.append(second).freeze()==first.freeze().concat(second.freeze());
 proof by normalize;
}
