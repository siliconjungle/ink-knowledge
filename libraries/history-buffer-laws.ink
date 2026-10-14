module ink.knowledge.history_buffer_laws;
law buffer_push<T>(data:Buffer<T>,value:T){data.push(value).freeze()==data.freeze().concat([value]);proof by normalize;}
law append_fold<T>(values:List<T>,data:Buffer<T>){
 foldl(values,data,fn(value,current)=>current.push(value)).freeze()==foldl(values,data.freeze(),fn(value,current)=>current.concat([value]));
 proof by induction values generalizing(data){nil=>normalize;cons(head,tail)=>calc{
  _==foldl(tail,data.push(head),fn(value,current)=>current.push(value)).freeze() by normalize;
  ==foldl(tail,data.push(head).freeze(),fn(value,current)=>current.concat([value])) by ih(data=data.push(head));
  ==foldl(tail,data.freeze().concat([head]),fn(value,current)=>current.concat([value])) by congruence(normalize,use buffer_push<T>(data,head),normalize);
  ==_ by normalize;
 };};
}
