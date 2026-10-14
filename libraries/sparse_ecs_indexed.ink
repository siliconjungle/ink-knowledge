module ink.knowledge.sparse_ecs_indexed;
import "sparse_ecs.ink" as ecs;

// A maintained intersection of two optional components. Only matching entity
// slots are traversed during integration. Mutations maintain the inverse map.
// An explicit bounded sparse-set registry, inspired by packed ECS storage.
// This source is not an optimisation law. Logical slots and wrapping generation
// counters are caller-visible; native ECS adapters use the same external IDs.
// 0=create, 1=destroy, 2=set position, 3=set velocity,
// 4=remove position, 5=remove velocity, 6=integrate matching entities.
// Stale/out-of-range handles and unknown operations do nothing. Integration is
// modulo-u32. A destroyed slot advances its generation modulo 2^32. The API does
// not promise stale-handle protection after a complete generation wraparound.
fn execute(capacity:u32,commands:List<ecs.Command>)->ecs.Snapshot {
 var slots:Buffer<u32>=buffer_fill(capacity,0);
 var generations:Buffer<u32>=buffer_fill(capacity,0);
 var packed:Buffer<ecs.Row>=Buffer.empty();
 var matches:Index=Index{matching:Buffer.empty(),membership:buffer_fill(capacity,0)};
 for command in commands {
  if command.kind==6 {
   packed=repeat_until(matches.matching.len(),packed,fn(p)=>false,fn(index)=>fn(p)=>integrate_at(slots.at_or(matches.matching.at_or(index,0),0)-1,p));
  } else {
   if command.slot<capacity && command.generation==generations.at_or(command.slot,0) {
    let encoded=slots.at_or(command.slot,0);
    if command.kind==0 {
     if encoded==0 {
      packed=packed.push(ecs.Row{slot:command.slot,generation:command.generation,position:0,velocity:0,has_position:false,has_velocity:false});
      slots=slots.set(command.slot,packed.len());
     }
    } else {
     if encoded>0 {
      let index=encoded-1;
      let row=packed.at_or(index,ecs.empty_row());
      if command.kind==1 {
       matches=membership(matches,command.slot,false);
       let last=packed.at_or(packed.len()-1,ecs.empty_row());
       let count=packed.len()-1;
       packed=packed.set(index,last).truncate(count);
       slots=slots.set(last.slot,encoded).set(command.slot,0);
       generations=generations.set(command.slot,command.generation+1);
      } else {
       if command.kind==2 || command.kind==3 || command.kind==4 || command.kind==5 {
        let updated=ecs.Row{slot:row.slot,generation:row.generation,
         position:if command.kind==2 {command.value} else {if command.kind==4 {0} else {row.position}},
         velocity:if command.kind==3 {command.value} else {if command.kind==5 {0} else {row.velocity}},
         has_position:if command.kind==2 {true} else {if command.kind==4 {false} else {row.has_position}},
         has_velocity:if command.kind==3 {true} else {if command.kind==5 {false} else {row.has_velocity}}};
        packed=packed.set(index,updated);
        matches=membership(matches,command.slot,updated.has_position && updated.has_velocity);
       }
      }
     }
    }
   }
  }
 }
 let slots=slots.freeze();let packed=packed.freeze();
 let initial=Output{rows:Buffer.empty(),query:Buffer.empty()};
 let output=repeat_until(capacity,initial,fn(out)=>false,fn(slot)=>fn(out)=>snapshot_at(slot,slots.at_or(slot,0),packed,out));
 return ecs.Snapshot{generations:generations.freeze(),rows:output.rows.freeze(),query:output.query.freeze()};
}
fn integrate_at(index:u32,packed:Buffer<ecs.Row>)->Buffer<ecs.Row>{
 let row=packed.at_or(index,ecs.empty_row());
 return if row.has_position && row.has_velocity {
  packed.set(index,ecs.Row{slot:row.slot,generation:row.generation,position:row.position+row.velocity,velocity:row.velocity,has_position:true,has_velocity:true})
 } else {packed};
}
record Output {rows:Buffer<ecs.Row>,query:Buffer<u32>,}
fn snapshot_at(slot:u32,encoded:u32,packed:List<ecs.Row>,out:Output)->Output{
 if encoded==0 {return out;}
 let row=packed.at_or(encoded-1,ecs.empty_row());
 return Output{rows:out.rows.push(row),query:if row.has_position && row.has_velocity {out.query.push(slot)} else {out.query}};
}

record Index {matching:Buffer<u32>,membership:Buffer<u32>,}
fn membership(index:Index,slot:u32,present:Bool)->Index{
 let member=index.membership.at_or(slot,0);
 if present {
  if member>0 {return index;}
  let matching=index.matching.push(slot);let encoded=matching.len();
  return Index{matching:matching,membership:index.membership.set(slot,encoded)};
 }
 if member==0 {return index;}
 let final_slot=index.matching.at_or(index.matching.len()-1,0);let count=index.matching.len()-1;
 return Index{matching:index.matching.set(member-1,final_slot).truncate(count),membership:index.membership.set(final_slot,member).set(slot,0)};
}
