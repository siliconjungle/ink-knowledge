module ink.knowledge.causal_cuts;
import "causal_ranges.ink" as causal;

// Conservative critical cuts of a topologically ordered DAG. A marked cut has
// one prefix frontier node, and every later node descends from that node.
// These are algorithm results, not permission to replace another computation.
record Critical { graph:causal.Graph, cuts:List<Bool>, valid:Bool, }
record Tips { values:Map<u32,Bool>, count:u32, maximum:u32, valid:Bool, }
record Prefix {
    graph:causal.Graph, flags:Buffer<Bool>, maximum:Buffer<u32>,
    tips:Map<u32,Bool>, count:u32, index:u32, valid:Bool,
}
record Suffix {
    graph:causal.Graph, flags:Buffer<Bool>, maximum:Buffer<u32>,
    minimum:u32, index:u32, valid:Bool,
}

fn parent(t:Tips,index:u32,value:u32)->Tips {
    let present=t.values.contains(value);
    return Tips{
        values:choose(present,t.values.remove(value),t.values),
        count:t.count-choose(present,1,0),
        maximum:choose(value>t.maximum,value,t.maximum),
        valid:t.valid && value>0 && value<index,
    };
}
fn prefix_step(s:Prefix)->Prefix {
    let index=s.index;
    let parents=s.graph.nodes.at_or(index,causal.nil()).parents;
    var t:Tips=Tips{values:s.tips,count:s.count,maximum:0,valid:s.valid};
    for value in parents {t=parent(t,index,value);}
    let count=t.count+1;
    return Prefix{
        ..s,
        tips:t.values.set(index,true),
        count:count,
        valid:t.valid,
        flags:s.flags.push(count==1),
        maximum:s.maximum.push(t.maximum),
        index:index+1,
    };
}
fn suffix_step(s:Suffix)->Suffix {
    let index=s.index;
    let marked=s.flags.at_or(index,false) && index<=s.minimum;
    let parent=s.maximum.at_or(index,0);
    return Suffix{
        ..s,
        flags:s.flags.set(index,marked),
        minimum:choose(parent<s.minimum,parent,s.minimum),
        index:choose(index==0,0,index-1),
    };
}
fn critical(g:causal.Graph)->Critical {
    let count=g.nodes.len();
    if count==0 || !g.valid {return Critical{graph:g,cuts:[],valid:false};}
    let prefix=repeat_until(count-1,Prefix{
        graph:g,flags:buffer([true]),maximum:buffer([0]),
        tips:Map.empty(),count:0,index:1,valid:true,
    },fn(s)=>!s.valid,fn(i,s)=>prefix_step(s));
    let suffix=repeat_until(count,Suffix{
        graph:prefix.graph,flags:prefix.flags,maximum:prefix.maximum,
        minimum:4294967295,index:count-1,valid:prefix.valid,
    },fn(s)=>!s.valid,fn(i,s)=>suffix_step(s));
    return Critical{
        graph:suffix.graph,
        cuts:choose(suffix.valid,suffix.flags.freeze(),[]),
        valid:suffix.valid,
    };
}
