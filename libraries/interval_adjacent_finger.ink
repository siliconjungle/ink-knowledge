module ink.knowledge.interval_adjacent_finger;
import "interval_index.ink" as intervals;
import "interval_cursor.ink" as cursor;
import "interval_finger.ink" as finger;
// Probe local links only for an adjacent integer key or an existing bound hit.
// Arbitrary jumps retain the root path without an extra neighbor traversal.
fn locate(index:intervals.Index,key:u64,hint:u32)->cursor.Found{
 let n=index.nodes.at_or(hint,intervals.nil());
 let inside=n.start<=key && (n.end==0 || key<n.end);
 let adjacent=choose(key<n.start,n.start!=0 && key==n.start-1,n.end!=0 && key==n.end);
 return choose(inside || adjacent,finger.locate(index,key,hint),cursor.locate(index,key,0));
}
