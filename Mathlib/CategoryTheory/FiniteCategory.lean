
structure Digraph where
  vertices : Nat
  colours : Array Nat
  edges : Array (Nat × Nat)

namespace Digraph

def nautyConstructor (G : Digraph) : String := sorry

/-- This will be implemented by an unsafe call to `nauty`. -/
def canonicalLabel (G : Digraph) : Array Nat := sorry

/-- Another unsafe call to `nauty`. -/
def automorphisms (G : Digraph) : List (Array Nat) := sorry

-- We could add axioms asserting `nauty`'s correctness!
-- (One could verify that the automorphisms are automorphisms, but not that they generate all.)

end Digraph

structure PartialFiniteCategory where
  /-- `n` is the number of objects. -/
  n : Nat
  /-- `m[x][y]` is the cardinality of `C(x → y)`. -/
  m : Array (Array Nat)
  /-- `c[x][y][z][a][b]` is the composite of `a : C(x → y)` and `b : C(y → z)`, if specified. -/
  c : Array (Array (Array (Array (Array (Option Nat)))))
  -- TODO: with constraints on the sizes
  -- TODO: with an associativity constraint
  -- TODO: with identity constraints (or leave these out and enumerate semicategories?)

namespace PartialFiniteCategory

/--
A morphism of partial defined finite categories.
We only need this for setting up the groupoid structure,
for proving results about exhausitivity, not for the actual enumeration.
-/
structure Hom (C D : PartialFiniteCategory) where
  /-- `obj[x] = y` indicates `x ↦ y`. -/
  obj : Array Nat
  /-- `hom[x][y][a] = b` indicates that `a : C(x → y)` maps to `b : C(f x → f y)`. -/
  hom : Array (Array (Array Nat))

structure DeleteObject where
  x : Nat

structure DeleteMorphism where
  x : Nat
  y : Nat
  a : Nat

structure DeleteComposite where
  x : Nat
  y : Nat
  z : Nat
  a : Nat
  b : Nat

def DeleteObject.result (C : PartialFiniteCategory) (L : DeleteObject) :
    PartialFiniteCategory :=
  { C with
    n := C.n - 1
    m := (C.m.eraseIdx L.x).map fun mx => mx.eraseIdx L.x
    c := ((C.c.eraseIdx L.x).map fun cx => cx.eraseIdx L.x).map fun cxy => cxy.eraseIdx L.x }

def DeleteMorphism.result (C : PartialFiniteCategory) (L : DeleteMorphism) :
    PartialFiniteCategory :=
  { C with
    m[L.x][L.y] := C.m[L.x]![L.y]! - 1
    -- We need to:
    -- Delete `C.c[L.x][L.y][*][L.a][*]`
    -- Delete `C.c[*][L.x][L.y][*][L.a]`
    -- Decrement `C.c[L.x][*][L.y][*][*]` if `≥ L.a`
    c :=
      let c1 := (List.range C.n).foldl (init := C.c) fun c z =>
        c.modify L.x fun cx => cx.modify L.y fun cxy => cxy.modify z fun cxyz => cxyz.eraseIdx L.a
      let c2 := (List.range C.n).foldl (init := c1) fun c w =>
        c.modify w fun cw => cw.modify L.x fun cwx => cwx.modify L.y fun cwxy => cwxy.map
          fun cwxyz => cwxyz.eraseIdx L.a
      let c3 := (List.range C.n).foldl (init := c2) fun c t =>
        c.modify L.x fun cx => cx.modify t fun cxt => cxt.modify L.y fun cxty => cxty.map
          fun cxtyb => cxtyb.map fun i? => match i? with
          | none => none
          | some i => if i ≥ L.a then some (i - 1) else some i
      c3 }

def DeleteComposite.result (C : PartialFiniteCategory) (L : DeleteComposite) :
    PartialFiniteCategory :=
  { C with c[L.x][L.y][L.z][L.a][L.b] := none }

inductive Lower
  | object : DeleteObject → Lower
  | morphism : DeleteMorphism → Lower
  | composite : DeleteComposite → Lower

def Lower.result (C : PartialFiniteCategory) : Lower → PartialFiniteCategory
  | composite d => d.result C
  | morphism d => d.result C
  | object d => d.result C

structure AddMorphism where
  x : Nat
  y : Nat

structure AddComposite where
  x : Nat
  y : Nat
  z : Nat
  a : Nat
  b : Nat
  c : Nat

inductive Upper
  | object
  | morphism : AddMorphism → Upper
  | composite : AddComposite → Upper

def addObject (C : PartialFiniteCategory) : PartialFiniteCategory where
  n := C.n + 1
  m := (C.m.map fun mx => mx.push 0).push (Array.mkArray (C.n + 1) 0)
  c := (C.c.mapIdx fun x cx =>
    (cx.mapIdx fun y cxy => cxy.push (Array.mkArray C.m[x]![y]! #[])).push
      (Array.mkArray (C.n + 1) #[])).push
        (Array.mkArray (C.n + 1) (Array.mkArray (C.n + 1) #[]))

def AddMorphism.result (C : PartialFiniteCategory) (U : AddMorphism) : PartialFiniteCategory :=
  { C with
    m[U.x][U.y] := C.m[U.x]![U.x]! + 1
    c :=
      let c1 := (List.range C.n).foldl (init := C.c) fun c z =>
        c.modify U.x fun cx => cx.modify U.y fun cxy => cxy.modify z fun cxyz =>
          cxyz.push (Array.mkArray C.m[U.y]![z]! none)
      let c2 := (List.range C.n).foldl (init := c1) fun c w =>
        c.modify w fun cw => cw.modify U.x fun cwx => cwx.modify U.y fun cwxy =>
          cwxy.map fun r => r.push none
      c2 }

def AddComposite.result (C : PartialFiniteCategory) (U : AddComposite) : PartialFiniteCategory :=
  { C with
    c[U.x][U.y][U.z][U.a][U.b] := U.c }

def Upper.result (C : PartialFiniteCategory) : Upper → PartialFiniteCategory
  | object => C.addObject
  | morphism u => u.result C
  | composite u => u.result C

def Upper.inverse (C : PartialFiniteCategory) : Upper → Lower
  | object => .object { x := C.n + 1 }
  | morphism u => .morphism { u with a := C.m[u.x]![u.y]! + 1 }
  | composite u => .composite { u with }

-- Encode lower objects as digraphs, so they can be labelled by nauty.
def DeleteObject.asGraph : DeleteObject → Digraph := sorry
def DeleteMorphism.asGraph : DeleteMorphism → Digraph := sorry
def DeleteComposite.asGraph : DeleteComposite → Digraph := sorry

-- These shouldn't map to `Unit`, but some linearly ordered type TBD.
-- We just need that two lower objects (for the same partial category)
-- receive the same canonical label iff they are isomorphic.
def DeleteObject.canonicalLabel : DeleteObject → Unit := sorry
def DeleteMorphism.canonicalLabel : DeleteMorphism → Unit := sorry
def DeleteComposite.canonicalLabel : DeleteComposite → Unit := sorry

/--
* If there is an object with no morphisms, delete it! (It doesn't matter which; they're equivalent.)
* If there is a morphism with no specified composites, delete one!
  * We are allowed to have an isomorphism-invariant preference amongst which one to delete
    (e.g. perhaps something about the source and/or target having complex or simple endomorphisms?)
    but then we have to break ties in an isomorphism invariant way.
    This will require a call to nauty!
* Otherwise, delete some composite
  * Again, we can have isomorphism-invariant preferences,
    and after satisfying these preferences must make an isomorphism-invariant choice.
    (Again requiring nauty.)

Note that we are really selecting an automorphism group orbit of lower objects,
and these selections must be coherent under isomorphisms!
-/
def canonicalReduction (C : PartialFiniteCategory) : Lower :=
  if /- there is an object with no morphisms-/ False then
    /- delete it -/
    sorry
  else if /- there is a morphism with no composites -/ False then
    /- express preferences -/
    /- and then amongst the best ones choose the one with the smallest canonical label -/
    sorry
  else
    /- express preferences amongst the composites that could be deleted -/
    /- and then amongst the best ones choose the one with the smallest canonical label -/
    sorry

-- We need to check if `u.inverse` is equivalent to `u.result.canonicalReduction`.
def genuine (C : PartialFiniteCategory) (u : Upper) : Bool :=
  sorry

def candidateChildren (C : PartialFiniteCategory) : List Upper := sorry

-- If we were proving exhaustivity, we would need to show that every `u : Upper` is either
-- * not genuine, or
-- * in `candidateChildren`

-- This part would ideally be done generically for any McKay groupoid!

def genuineChildren (C : PartialFiniteCategory) : List PartialFiniteCategory :=
  -- Take the `candidateChildren`
  -- Collect into orbits (either via canonical labelling or checking pairwise isomorphism),
  -- and take a representative from each.
  -- Accept if genuine.
  -- Generate the result.
  sorry

-- Now isomorph-free exhaustive generation is "just" iterating `genuineChildren`.

end PartialFiniteCategory
