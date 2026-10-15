module objective;

// Whole-candidate forecasts supplied by the shared portfolio controller.
// Fields describe empirical/predicted costs, not proofs of future resource use.
record Cell { name:String, calls:u64, }
record Candidate {
 variant:String, artifact:String, current:Bool,
 workload:List<Cell>, window_calls:u64, total_calls:u64, state_elements:u64,
 horizon_calls:u64,
 execution_low_ns:f64, execution_high_ns:f64,
 migration_high_ns:f64, migration_margin:f64,
 total_low_ns:f64, total_high_ns:f64,
 peak_bytes:u64, migration_peak_bytes:u64, migration_pause_ns:f64,
}
record Rank { variant:String, low:f64, high:f64, }
fn rank(variant:String,low:f64,high:f64)->Rank {
 return Rank{variant:variant,low:low,high:high};
}
fn valid(rank:Rank)->Bool {
 return is_finite(rank.low) && is_finite(rank.high)
     && rank.low>=-1e100f64 && rank.high<=1e100f64 && rank.low<=rank.high;
}
