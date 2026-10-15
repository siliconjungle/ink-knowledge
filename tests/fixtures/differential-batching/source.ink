module batching_correspondence;
record W{a:f32,b:f32,}
fn polynomial(w:W,x:f32)->f32 {let y=w.a*x+w.b;return y*y;}
fn nonlinear(w:W,x:f32)->f32 {return sqrt(w.a*w.a+1.0)/(w.b*w.b+1.0)-w.a*x;}
fn batched(w:W,x:f32)->W{return gradient(polynomial,w,x);}
fn directions(w:W,x:f32)->W{return W{a:jvp(polynomial,w,W{a:1.0,b:0.0},x),b:jvp(polynomial,w,W{a:0.0,b:1.0},x)};}
fn nonlinear_batched(w:W,x:f32)->W{return gradient(nonlinear,w,x);}
fn nonlinear_directions(w:W,x:f32)->W{return W{a:jvp(nonlinear,w,W{a:1.0,b:0.0},x),b:jvp(nonlinear,w,W{a:0.0,b:1.0},x)};}
fn observed(w:W,x:f32)->W{return batched(w,x);}
fn observed_nonlinear(w:W,x:f32)->W{return nonlinear_batched(w,x);}
fn batch(xs:List<f32>,w:W)->List<W>{return xs.map(fn(x)=>observed_nonlinear(w,x));}
