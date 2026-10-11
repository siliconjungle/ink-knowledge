# Web collection proof batch

20 new executable statements are admitted by the existing checker. Every law
also appears in a checked executable selection: two ten-function programs avoid
the planner's fixed twelve-round search cap. Three tests passed; two hash-valid
false controls (wrong self-zip operand and reversed ordered fold) were rejected.
No compiler, checker, lowering, runtime or canonical store changed in this lane.

The statements do not duplicate existing catalogue IDs or exact executable
endpoints. Old map fusion has one element sort throughout and cannot instantiate
the eight cross-type signatures. These proofs have no performance premises.

- Eight cross-type map fusions remove the intermediate list, including Bool
  masks and numeric word conversions. This can turn a GPU-ineligible chained map
  into one GPU-eligible map; that is an eligibility change, not a shader speedup.
- Five self-zip laws turn `xs.zip(xs, x+y)` (or Bool conjunction) into one map.
  Both input references are the same list. No unequal-list truncation assumption
  is used. Arithmetic operations and F32 rounding are identical.
- Four mapped ordered folds fuse `map(x*k)` into the right fold `x-acc`.
  The accumulator starts at the same value and visits the same right-to-left
  sequence. F32 multiplication/subtraction order is unchanged; no associativity,
  commutativity or distributivity premise is claimed.
- Three wrapping-integer zero-stage scans remove scan after `map(x-x)`.
  The proof normalizes the zero map, uses list induction for scan, and restores
  the original map expression. Length and every output word stay unchanged.

The self-zip and fold laws use executable arithmetic bodies because generated
applications of arbitrary curried function holes are outside the current
selection reifier's executable interface. No new trusted mechanism was added.

Useful U32 benchmark source / selected replacement pairs:

```ink
fn cross_bool(xs:List<u32>,seed:u32,factor:u32)->List<u32>{
  return xs.map(fn(x)=>x<seed).map(fn(b)=>choose(b,factor,factor+1));
}
// replacement: xs.map(fn(x)=>choose(x<seed,factor,factor+1))

fn self_zip(xs:List<u32>,seed:u32,factor:u32)->List<u32>{
  return xs.zip(xs,fn(x)=>fn(y)=>x+y);
}
// replacement: xs.map(fn(x)=>x+x)

fn ordered_fold(xs:List<u32>,seed:u32,factor:u32)->u32{
  return foldr(xs.map(fn(x)=>x*factor),seed,fn(x)=>fn(a)=>x-a);
}
// replacement: foldr(xs,seed,fn(x)=>fn(a)=>x*factor-a)

fn zero_scan(xs:List<u32>)->List<u32>{return xs.map(fn(x)=>x-x).scan();}
// replacement: xs.map(fn(x)=>x-x)
```

The first/last original GPU graphs currently fall back; self-zip is directly
GPU supported before and after. Ordered fold stays CPU-only. Compare original,
prior catalogue and this batch under the same full-call harness. Preserve raw
fallbacks and memory-transfer costs; no measurements were run in this lane.

Reproduce from knowledge checkout:

```sh
python3 -m unittest discover -s tests -p test_web_collection_laws.py -v
python3 producers/web_collection_laws.py --output-store /tmp/new-collection-store
```

Evidence is in `collection/validation.json`, `collection/tests.log`, isolated
manifest/view, exact emitted cores, selections and per-command JSON outputs.

| Law | Canonical object ID |
| --- | --- |
| `map_cross_fusion_u32_bool_u32` | `2e8ae41345f3ea7a4187b1cacca7a4e1827548db16fe4506223031ad2513c546` |
| `map_cross_fusion_i32_bool_i32` | `051617eb78ea4f23e931bf2e777411708de3e1cde9ad2a012c96130eea8a5b9f` |
| `map_cross_fusion_u64_bool_u64` | `d96233bfc848528d9d495f338ef09eb537c80056c75014ef39adf4825a62fc04` |
| `map_cross_fusion_f32_bool_f32` | `8ccefd6239cca7801ebeb8dff8ef2b8411d773edc298c0cd6a2b7fc6a525d895` |
| `map_cross_fusion_bool_u32_bool` | `a849a94f6c687c8cbeaa3e6e949319506fc13370011492f85df8315c441c3e77` |
| `map_cross_fusion_u32_u64_u32` | `abb89f0f55f6f1c376b9c2360852d671d15d70f1c8382756b5c3ba620120a0fa` |
| `map_cross_fusion_u64_u32_u64` | `82640be07884e060c3e66bdf9b32f2a34a6f30122bec5ebb1ab3a0830ab2911f` |
| `map_cross_fusion_i32_u32_i32` | `400f0643c50f7ee01867918f9958c4ae92fec10fe858572f0f832e75dff58dab` |
| `self_zip_map_u32` | `f28972292cc52bc0c4429d9c0c9dd4efb84f85adf0564d729a300c8516cafeb1` |
| `self_zip_map_i32` | `ea62825888fd7b93143790f12426fed185c1599428f2e9d89a2ba4df6103f74d` |
| `self_zip_map_u64` | `efb1180992fab131aa3fa425c52620435b7417bcb20c2f83e97c25a3ab3b042e` |
| `self_zip_map_f32` | `9f4b208971b677c1db86ea6771aba464fead1a2f70955b75bef66f8f97391ffe` |
| `self_zip_map_bool` | `53bbd6d3c933b665615bb9f4b5bbd1d101d7aafed907c5c5eebdfef4328d8c4a` |
| `map_ordered_fold_u32` | `d0ef89c9ff15a593f4b4327017f0842ff50b25d515c4050ab4d6eb44f636abe9` |
| `map_ordered_fold_i32` | `63f4eb206e1be80ac7e2eb2555e0940c5e457f6d09a6271b5d94696945379b1a` |
| `map_ordered_fold_u64` | `e614211828205b413c79402d00573d6563e0cb02377186b0dfa14c184828f6a4` |
| `map_ordered_fold_f32` | `d38986fb4f0452dcc93bc6c40fd59fad6e0b68c0aeab611aee0e9b394d6fd3aa` |
| `zero_map_scan_u32` | `ee26933325a6aca3e633b5d514ba601328772ef9e22164ff2b405340bc3562a5` |
| `zero_map_scan_i32` | `1a64d53fa7f08ddd641d3b86df5d345532d9d88fb8c72060d70663ffea354de9` |
| `zero_map_scan_u64` | `67fb8e9d06f45204a6fd669e82ac8596cabdafd2160d6e44d5c6ff8c0393d810` |
