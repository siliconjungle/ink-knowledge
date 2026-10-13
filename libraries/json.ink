module ink.knowledge.json;

// JSON is an ordinary recursive datatype. Its algorithms confer no rewrite
// authority. Number stores an exact JSON number token, never a binary float.
enum Json { Null, Boolean(Bool), Number(String), Text(String), Array(List<Json>), Object(List<Member>), }
record Member { key:String, value:Json, }
enum JsonError { ExpectedObject, ExpectedArray, ExpectedBoolean, ExpectedNumber, ExpectedString, }

fn null()->Json {return Json.Null;}
fn boolean(value:Bool)->Json {return Json.Boolean(value);}
fn number(token:String)->Json {return Json.Number(token);}
fn text(value:String)->Json {return Json.Text(value);}
fn array(values:List<Json>)->Json {return Json.Array(values);}
fn object(members:List<Member>)->Json {return Json.Object(members);}

// Missing is None; a present null is Some(Json.Null). Lookup is first-wins.
// Checked JSON ingress rejects duplicate keys; set removes old duplicates.
fn lookup(members:List<Member>,key:String)->Option<Json> {
 return foldr(members,None,fn(member)=>fn(rest)=>if member.key==key {Some(member.value)} else {rest});
}
fn get(value:Json,key:String)->Result<Option<Json>,JsonError> {
 return match value {
  Json.Null=>Err(JsonError.ExpectedObject), Json.Boolean(v)=>Err(JsonError.ExpectedObject),
  Json.Number(v)=>Err(JsonError.ExpectedObject), Json.Text(v)=>Err(JsonError.ExpectedObject),
  Json.Array(v)=>Err(JsonError.ExpectedObject), Json.Object(members)=>Ok(lookup(members,key)),
 };
}
fn members(value:Json)->Result<List<Member>,JsonError> {
 return match value {
  Json.Null=>Err(JsonError.ExpectedObject), Json.Boolean(v)=>Err(JsonError.ExpectedObject),
  Json.Number(v)=>Err(JsonError.ExpectedObject), Json.Text(v)=>Err(JsonError.ExpectedObject),
  Json.Array(v)=>Err(JsonError.ExpectedObject), Json.Object(items)=>Ok(items),
 };
}
fn elements(value:Json)->Result<List<Json>,JsonError> {
 return match value {
  Json.Null=>Err(JsonError.ExpectedArray), Json.Boolean(v)=>Err(JsonError.ExpectedArray),
  Json.Number(v)=>Err(JsonError.ExpectedArray), Json.Text(v)=>Err(JsonError.ExpectedArray),
  Json.Array(items)=>Ok(items), Json.Object(v)=>Err(JsonError.ExpectedArray),
 };
}
fn as_text(value:Json)->Result<String,JsonError> {
 return match value {
  Json.Null=>Err(JsonError.ExpectedString), Json.Boolean(v)=>Err(JsonError.ExpectedString),
  Json.Number(v)=>Err(JsonError.ExpectedString), Json.Text(v)=>Ok(v),
  Json.Array(v)=>Err(JsonError.ExpectedString), Json.Object(v)=>Err(JsonError.ExpectedString),
 };
}
fn as_number(value:Json)->Result<String,JsonError> {
 return match value {
  Json.Null=>Err(JsonError.ExpectedNumber), Json.Boolean(v)=>Err(JsonError.ExpectedNumber),
  Json.Number(v)=>Ok(v), Json.Text(v)=>Err(JsonError.ExpectedNumber),
  Json.Array(v)=>Err(JsonError.ExpectedNumber), Json.Object(v)=>Err(JsonError.ExpectedNumber),
 };
}
fn as_boolean(value:Json)->Result<Bool,JsonError> {
 return match value {
  Json.Null=>Err(JsonError.ExpectedBoolean), Json.Boolean(v)=>Ok(v),
  Json.Number(v)=>Err(JsonError.ExpectedBoolean), Json.Text(v)=>Err(JsonError.ExpectedBoolean),
  Json.Array(v)=>Err(JsonError.ExpectedBoolean), Json.Object(v)=>Err(JsonError.ExpectedBoolean),
 };
}
fn put(members:List<Member>,key:String,value:Json)->List<Member> {
 return [Member{key:key,value:value}].concat(members.filter(fn(member)=>member.key!=key));
}
fn set(value:Json,key:String,replacement:Json)->Result<Json,JsonError> {
 let items:List<Member>=members(value)?;
 return Ok(Json.Object(put(items,key,replacement)));
}
fn remove(value:Json,key:String)->Result<Json,JsonError> {
 let items:List<Member>=members(value)?;
 return Ok(Json.Object(items.filter(fn(member)=>member.key!=key)));
}
fn project(value:Json,keys:List<String>)->Result<Json,JsonError> {
 let items:List<Member>=members(value)?;
 return Ok(Json.Object(items.filter(fn(member)=>foldl(keys,false,fn(key)=>fn(found)=>found||key==member.key))));
}
