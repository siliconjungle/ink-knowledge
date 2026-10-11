module ink.knowledge.integers;
enum DivisionError { ZeroDivisor, Overflow, }
// The fallback primitives return zero for the sole signed overflow case.
// Checking the quotient/remainder identity distinguishes it without a
// compiler-specialised numerical-type branch. Instantiated T must be a word.
fn checked_div<T>(a:T,b:T)->Result<T,DivisionError> {
    if b==0 {return Err(DivisionError.ZeroDivisor);}
    let q:T=quot_or(a,b,0);
    let r:T=rem_or(a,b,0);
    if q*b+r!=a {return Err(DivisionError.Overflow);}
    return Ok(q);
}
fn checked_rem<T>(a:T,b:T)->Result<T,DivisionError> {
    if b==0 {return Err(DivisionError.ZeroDivisor);}
    let q:T=quot_or(a,b,0);
    let r:T=rem_or(a,b,0);
    if q*b+r!=a {return Err(DivisionError.Overflow);}
    return Ok(r);
}
