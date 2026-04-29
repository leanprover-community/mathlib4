/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Tactic.Simproc.CastData
public import Mathlib.Data.Subtype

/-!
# Registration of `Subtype.val` as a `cast_data` projection

This module registers `Subtype.val` with the `@[cast_data]` attribute, so that ordinary `simp`
rewrites `(h ▸ x : Subtype q).val ↦ x.val` whenever the cast only changes an indexing argument
of the underlying subtype predicate. The simproc machinery itself lives in
`Mathlib.Tactic.Simproc.CastData`.

The registration even reaches through `def` wrappers around `Subtype` such as
```
def step (G : Gr) [GraphLike V D E Gr] (u v : V) : Type _ :=
  {d : D // d ∈ D(G) ∧ src d = u ∧ tgt d = v}
```
because the simproc whnfs at full transparency when checking the source predicate.
-/

public section

universe u v

namespace Subtype

/-- Applying `Subtype.val` after transporting along `h : a = b` is the same as applying
`Subtype.val` to the original element. The predicate `p` is indexed by `ι`, and the endpoint
changes from `a` to `b`. -/
theorem val_eqRec {α : Sort u} {ι : Sort v}
    {p : ι → α → Prop} {a b : ι} (h : a = b) (x : Subtype (p a)) :
    @Subtype.val α (p b) (h ▸ x) = x.val := by
  subst h
  rfl

end Subtype

end

attribute [cast_data] Subtype.val

/-! ### Tests -/

section
example {α ι : Type*} {i j : ι} {p : ι → α → Prop}
    (h : i = j) (x : {a // p i a}) :
    (h ▸ x : {a // p j a}).val = x.val := by simp

example {α : Type*} {i j i' : Nat} {p : Nat → Nat → α → Prop}
    (h : i = i') (x : {a // p i j a}) :
    (h ▸ x : {a // p i' j a}).val = x.val := by simp

/-- A small indexed type used only to test `@[cast_data]` on a user-registered projection. -/
private structure CastDataBox (ι α : Type*) (i j : ι) where
  val : α

private def CastDataBox.data {ι α : Type*} {i j : ι} (x : CastDataBox ι α i j) : α :=
  x.val

attribute [cast_data] CastDataBox.data

example {ι α : Type*} {i j j' : ι} (h : j = j') (x : CastDataBox ι α i j) :
    CastDataBox.data (h ▸ x : CastDataBox ι α i j') = CastDataBox.data x := by
  simp

example {ι α : Type*} {i i' j j' : ι} (hi : i = i') (hj : j = j')
    (x : CastDataBox ι α i j) :
    CastDataBox.data (hi ▸ hj ▸ x : CastDataBox ι α i' j') = CastDataBox.data x := by
  simp
end
