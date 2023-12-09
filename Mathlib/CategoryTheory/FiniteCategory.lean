import Mathlib.Data.Vector

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

structure Hom (C D : PartialFiniteCategory) where
  /-- If `x \mapsto   -/
  obj : Array Nat
  hom : Array (Array (Array Nat))

structure DeleteComposite where
  x : Nat
  y : Nat
  z : Nat
  a : Nat
  b : Nat

structure DeleteMorphism where
  x : Nat
  y : Nat
  a : Nat

structure DeleteObject where
  x : Nat

def DeleteComposite.result (C : PartialFiniteCategory) (L : DeleteComposite) :
    PartialFiniteCategory :=
  { C with c[L.x][L.y][L.z][L.a][L.b] := none }

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

def DeleteObject.result (C : PartialFiniteCategory) (L : DeleteObject) :
    PartialFiniteCategory :=
  { C with
    n := C.n - 1
    m := (C.m.eraseIdx L.x).map fun mx => mx.eraseIdx L.x
    c := ((C.c.eraseIdx L.x).map fun cx => cx.eraseIdx L.x).map fun cxy => cxy.eraseIdx L.x }

inductive Lower
  | composite : DeleteComposite → Lower
  | morphism : DeleteMorphism → Lower
  | object : DeleteObject → Lower

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

end PartialFiniteCategory
