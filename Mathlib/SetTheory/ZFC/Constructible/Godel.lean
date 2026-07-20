/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Def

/-!
# Gödel operations and rudimentary closure

This file implements the standard Jensen--Devlin basis `F₀, ..., F₈` of
rudimentary (Gödel) operations on Mathlib's internal `ZFSet` universe.  Tuples
are right-associated Kuratowski pairs:

`⟨x, y, z⟩ = ⟨x, ⟨y, z⟩⟩`.

The resulting `rudimentaryClosure U` starts from `U ∪ {U}`.  The candidate
Gödel presentation of the definable powerset is then

`powerset U ∩ rudimentaryClosure U`.

Its equality with `Constructible.DefZF U` for transitive `U` is deliberately
not built into the definition; it is a theorem to be established separately.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Godel

/-- A right-associated Kuratowski triple. -/
def triple (x y z : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair x (ZFSet.pair y z)

/-- A set containing every possible component of a Kuratowski pair in `r`. -/
def pairField (r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.sUnion r)

theorem pair_left_mem_pairField {r x y : ZFSet.{u}}
    (h : ZFSet.pair x y ∈ r) : x ∈ pairField r := by
  rw [pairField, ZFSet.mem_sUnion]
  refine ⟨{x}, ?_, by simp⟩
  rw [ZFSet.mem_sUnion]
  exact ⟨ZFSet.pair x y, h, by simp [ZFSet.pair]⟩

theorem pair_right_mem_pairField {r x y : ZFSet.{u}}
    (h : ZFSet.pair x y ∈ r) : y ∈ pairField r := by
  rw [pairField, ZFSet.mem_sUnion]
  refine ⟨{x, y}, ?_, by simp⟩
  rw [ZFSet.mem_sUnion]
  exact ⟨ZFSet.pair x y, h, by simp [ZFSet.pair]⟩

/-- `F₀(x,y) = {x,y}`. -/
def F0 (x y : ZFSet.{u}) : ZFSet.{u} :=
  {x, y}

/-- `F₁(x,y) = x \ y`. -/
def F1 (x y : ZFSet.{u}) : ZFSet.{u} :=
  x \ y

/-- `F₂(x,y) = x × y`. -/
def F2 (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod x y

/--
`F₃(x,y) = {⟨u,z,v⟩ | z ∈ x ∧ ⟨u,v⟩ ∈ y}`.
-/
def F3 (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep
    (fun t => ∃ u z v, z ∈ x ∧ ZFSet.pair u v ∈ y ∧ t = triple u z v)
    (ZFSet.prod (pairField y) (ZFSet.prod x (pairField y)))

/--
`F₄(x,y) = {⟨u,v,z⟩ | z ∈ x ∧ ⟨u,v⟩ ∈ y}`.
-/
def F4 (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep
    (fun t => ∃ u v z, z ∈ x ∧ ZFSet.pair u v ∈ y ∧ t = triple u v z)
    (ZFSet.prod (pairField y) (ZFSet.prod (pairField y) x))

/-- `F₅(x,y) = ⋃x`; the second argument is intentionally unused. -/
def F5 (x _y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion x

/--
`F₆(x,y) = dom* x = {z | ∃ w, ⟨w,z⟩ ∈ x}`; the graph convention
places inputs in the second coordinate.
-/
def F6 (x _y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ w, ZFSet.pair w z ∈ x) (pairField x)

/-- `F₇(x,y) = {⟨z,w⟩ | z,w ∈ x ∧ z ∈ w}`. -/
def F7 (x _y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pairSep (fun z w => z ∈ w) x x

/-- The fiber `x * z = {w | ⟨w,z⟩ ∈ x}`. -/
def fiber (x z : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun w => ZFSet.pair w z ∈ x) (pairField x)

/-- `F₈(x,y) = {x * z | z ∈ y}`. -/
noncomputable def F8 (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun z : Constructible.ZFCarrier y => fiber x z.1)

@[simp]
theorem mem_F0_iff {x y z : ZFSet.{u}} : z ∈ F0 x y ↔ z = x ∨ z = y := by
  simp [F0]

@[simp]
theorem mem_F1_iff {x y z : ZFSet.{u}} : z ∈ F1 x y ↔ z ∈ x ∧ z ∉ y := by
  simp [F1]

@[simp]
theorem mem_F2_iff {x y z : ZFSet.{u}} :
    z ∈ F2 x y ↔ ∃ a ∈ x, ∃ b ∈ y, z = ZFSet.pair a b := by
  simp [F2]

@[simp]
theorem mem_F3_iff {x y t : ZFSet.{u}} :
    t ∈ F3 x y ↔
      ∃ u z v, z ∈ x ∧ ZFSet.pair u v ∈ y ∧ t = triple u z v := by
  constructor
  · exact fun h => (ZFSet.mem_sep.mp h).2
  · rintro ⟨u, z, v, hz, huv, rfl⟩
    apply ZFSet.mem_sep.mpr
    refine ⟨?_, ⟨u, z, v, hz, huv, rfl⟩⟩
    rw [triple, ZFSet.pair_mem_prod, ZFSet.pair_mem_prod]
    exact ⟨pair_left_mem_pairField huv, hz, pair_right_mem_pairField huv⟩

@[simp]
theorem mem_F4_iff {x y t : ZFSet.{u}} :
    t ∈ F4 x y ↔
      ∃ u v z, z ∈ x ∧ ZFSet.pair u v ∈ y ∧ t = triple u v z := by
  constructor
  · exact fun h => (ZFSet.mem_sep.mp h).2
  · rintro ⟨u, v, z, hz, huv, rfl⟩
    apply ZFSet.mem_sep.mpr
    refine ⟨?_, ⟨u, v, z, hz, huv, rfl⟩⟩
    rw [triple, ZFSet.pair_mem_prod, ZFSet.pair_mem_prod]
    exact ⟨pair_left_mem_pairField huv, pair_right_mem_pairField huv, hz⟩

@[simp]
theorem mem_F5_iff {x y z : ZFSet.{u}} :
    z ∈ F5 x y ↔ ∃ w ∈ x, z ∈ w := by
  simp [F5]

@[simp]
theorem mem_F6_iff {x y z : ZFSet.{u}} :
    z ∈ F6 x y ↔ ∃ w, ZFSet.pair w z ∈ x := by
  constructor
  · exact fun h => (ZFSet.mem_sep.mp h).2
  · rintro ⟨w, hw⟩
    exact ZFSet.mem_sep.mpr ⟨pair_right_mem_pairField hw, ⟨w, hw⟩⟩

@[simp]
theorem mem_F7_iff {x y q : ZFSet.{u}} :
    q ∈ F7 x y ↔
      ∃ z ∈ x, ∃ w ∈ x, q = ZFSet.pair z w ∧ z ∈ w := by
  simp [F7]

@[simp]
theorem mem_fiber_iff {x z w : ZFSet.{u}} :
    w ∈ fiber x z ↔ ZFSet.pair w z ∈ x := by
  constructor
  · exact fun h => (ZFSet.mem_sep.mp h).2
  · intro h
    exact ZFSet.mem_sep.mpr ⟨pair_left_mem_pairField h, h⟩

@[simp]
theorem mem_F8_iff {x y q : ZFSet.{u}} :
    q ∈ F8 x y ↔ ∃ z ∈ y, q = fiber x z := by
  simp [F8, eq_comm]

/-- Uniform access to the nine Gödel operations. -/
noncomputable def op (i : Fin 9) (x y : ZFSet.{u}) : ZFSet.{u} :=
  match i.1 with
  | 0 => F0 x y
  | 1 => F1 x y
  | 2 => F2 x y
  | 3 => F3 x y
  | 4 => F4 x y
  | 5 => F5 x y
  | 6 => F6 x y
  | 7 => F7 x y
  | 8 => F8 x y
  | _ => ∅

/-- One closure step under all nine binary operations. -/
noncomputable def rudimentaryStep (a : ZFSet.{u}) : ZFSet.{u} :=
  a ∪ ZFSet.range
    (fun p : Fin 9 × (Constructible.ZFCarrier a × Constructible.ZFCarrier a) =>
      op p.1 p.2.1.1 p.2.2.1)

@[simp]
theorem mem_rudimentaryStep_iff {a z : ZFSet.{u}} :
    z ∈ rudimentaryStep a ↔
      z ∈ a ∨
        ∃ i : Fin 9, ∃ x ∈ a, ∃ y ∈ a, op i x y = z := by
  rw [rudimentaryStep, ZFSet.mem_union, ZFSet.mem_range]
  constructor
  · rintro (hz | ⟨p, rfl⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨p.1, p.2.1.1, p.2.1.2, p.2.2.1, p.2.2.2, rfl⟩
  · rintro (hz | ⟨i, x, hx, y, hy, rfl⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨⟨i, ⟨⟨x, hx⟩, ⟨y, hy⟩⟩⟩, rfl⟩

theorem subset_rudimentaryStep (a : ZFSet.{u}) : a ⊆ rudimentaryStep a := by
  intro z hz
  exact mem_rudimentaryStep_iff.mpr (Or.inl hz)

/-- One closure step is monotone in its input set. -/
theorem rudimentaryStep_mono {a b : ZFSet.{u}} (hab : a ⊆ b) :
    rudimentaryStep a ⊆ rudimentaryStep b := by
  intro z hz
  rcases mem_rudimentaryStep_iff.mp hz with
    hz | ⟨i, x, hx, y, hy, rfl⟩
  · exact mem_rudimentaryStep_iff.mpr (Or.inl (hab hz))
  · exact mem_rudimentaryStep_iff.mpr
      (Or.inr ⟨i, x, hab hx, y, hab hy, rfl⟩)

/-- The `n`-th finite closure stage. -/
noncomputable def rudimentaryIter (seed : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => seed
  | n + 1 => rudimentaryStep (rudimentaryIter seed n)

/-- Closure of a set under all nine Gödel operations. -/
noncomputable def closure (seed : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.iUnion (rudimentaryIter seed)

@[simp]
theorem mem_closure_iff {seed z : ZFSet.{u}} :
    z ∈ closure seed ↔ ∃ n : Nat, z ∈ rudimentaryIter seed n := by
  simp [closure]

theorem rudimentaryIter_subset_succ (seed : ZFSet.{u}) (n : Nat) :
    rudimentaryIter seed n ⊆ rudimentaryIter seed (n + 1) := by
  exact subset_rudimentaryStep _

theorem rudimentaryIter_mono (seed : ZFSet.{u}) {m n : Nat} (hmn : m ≤ n) :
    rudimentaryIter seed m ⊆ rudimentaryIter seed n := by
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n _ ih =>
      exact ih.trans (rudimentaryIter_subset_succ seed n)

/-- Every finite closure stage is monotone in the seed. -/
theorem rudimentaryIter_mono_seed {a b : ZFSet.{u}} (hab : a ⊆ b) (n : Nat) :
    rudimentaryIter a n ⊆ rudimentaryIter b n := by
  induction n with
  | zero => exact hab
  | succ n ih => exact rudimentaryStep_mono ih

theorem seed_subset_closure (seed : ZFSet.{u}) : seed ⊆ closure seed := by
  intro z hz
  exact mem_closure_iff.mpr ⟨0, hz⟩

/-- Rudimentary closure is monotone in its seed. -/
theorem closure_mono {a b : ZFSet.{u}} (hab : a ⊆ b) :
    closure a ⊆ closure b := by
  intro z hz
  rcases mem_closure_iff.mp hz with ⟨n, hn⟩
  exact mem_closure_iff.mpr ⟨n, rudimentaryIter_mono_seed hab n hn⟩

/-- The finite closure really is closed under every operation in the basis. -/
theorem op_mem_closure {seed x y : ZFSet.{u}} {i : Fin 9}
    (hx : x ∈ closure seed) (hy : y ∈ closure seed) :
    op i x y ∈ closure seed := by
  rcases mem_closure_iff.mp hx with ⟨m, hm⟩
  rcases mem_closure_iff.mp hy with ⟨n, hn⟩
  let k := max m n
  have hxk : x ∈ rudimentaryIter seed k :=
    rudimentaryIter_mono seed (Nat.le_max_left m n) hm
  have hyk : y ∈ rudimentaryIter seed k :=
    rudimentaryIter_mono seed (Nat.le_max_right m n) hn
  apply mem_closure_iff.mpr
  refine ⟨k + 1, ?_⟩
  exact mem_rudimentaryStep_iff.mpr
    (Or.inr ⟨i, x, hxk, y, hyk, rfl⟩)

/-- A set is closed under the Jensen--Devlin basis of Gödel operations. -/
def ClosedUnderOps (a : ZFSet.{u}) : Prop :=
  ∀ (i : Fin 9) (x y : ZFSet.{u}), x ∈ a → y ∈ a → op i x y ∈ a

/-- Every `closure seed` is closed under all nine operations. -/
theorem closure_closedUnderOps (seed : ZFSet.{u}) :
    ClosedUnderOps (closure seed) := by
  intro i x y hx hy
  exact op_mem_closure hx hy

/--
`closure seed` is the least internally represented set containing `seed` and
closed under all nine operations.
-/
theorem closure_minimal {seed a : ZFSet.{u}} (hseed : seed ⊆ a)
    (ha : ClosedUnderOps a) : closure seed ⊆ a := by
  have hiter : ∀ n : Nat, rudimentaryIter seed n ⊆ a := by
    intro n
    induction n with
    | zero => exact hseed
    | succ n ih =>
        intro z hz
        rcases mem_rudimentaryStep_iff.mp hz with
          hz | ⟨i, x, hx, y, hy, rfl⟩
        · exact ih hz
        · exact ha i x y (ih hx) (ih hy)
  intro z hz
  rcases mem_closure_iff.mp hz with ⟨n, hn⟩
  exact hiter n hn

/-- Closing an already closed finite-operation closure adds no new sets. -/
@[simp]
theorem closure_idem (seed : ZFSet.{u}) :
    closure (closure seed) = closure seed := by
  apply le_antisymm
  · exact closure_minimal Set.Subset.rfl (closure_closedUnderOps seed)
  · exact seed_subset_closure (closure seed)

/-- The seed `U ∪ {U}` used in the Gödel presentation of `Def(U)`. -/
def rudimentarySeed (U : ZFSet.{u}) : ZFSet.{u} :=
  insert U U

@[simp]
theorem mem_rudimentarySeed_iff {U z : ZFSet.{u}} :
    z ∈ rudimentarySeed U ↔ z = U ∨ z ∈ U := by
  simp [rudimentarySeed]

/-- Rudimentary closure of `U ∪ {U}`. -/
noncomputable def rudimentaryClosure (U : ZFSet.{u}) : ZFSet.{u} :=
  closure (rudimentarySeed U)

theorem subset_rudimentaryClosure (U : ZFSet.{u}) :
    U ⊆ rudimentaryClosure U := by
  intro z hz
  exact seed_subset_closure _ (mem_rudimentarySeed_iff.mpr (Or.inr hz))

theorem self_mem_rudimentaryClosure (U : ZFSet.{u}) :
    U ∈ rudimentaryClosure U :=
  seed_subset_closure _ (mem_rudimentarySeed_iff.mpr (Or.inl rfl))

theorem op_mem_rudimentaryClosure {U x y : ZFSet.{u}} {i : Fin 9}
    (hx : x ∈ rudimentaryClosure U) (hy : y ∈ rudimentaryClosure U) :
    op i x y ∈ rudimentaryClosure U :=
  op_mem_closure hx hy

/--
`rudimentaryClosure U` is minimal among operation-closed sets containing both
every element of `U` and `U` itself.
-/
theorem rudimentaryClosure_minimal {U a : ZFSet.{u}}
    (hU : U ⊆ a) (hself : U ∈ a) (ha : ClosedUnderOps a) :
    rudimentaryClosure U ⊆ a := by
  apply closure_minimal
  · intro z hz
    rcases mem_rudimentarySeed_iff.mp hz with rfl | hz
    · exact hself
    · exact hU hz
  · exact ha

/--
The Gödel-operations candidate for `Def(U)`.  For transitive `U`, the classical
Gödel theorem identifies this set with `Constructible.DefZF U`.
-/
noncomputable def godelDef (U : ZFSet.{u}) : ZFSet.{u} :=
  U.powerset ∩ rudimentaryClosure U

@[simp]
theorem mem_godelDef_iff {U z : ZFSet.{u}} :
    z ∈ godelDef U ↔ z ⊆ U ∧ z ∈ rudimentaryClosure U := by
  simp [godelDef]

theorem godelDef_subset_powerset (U : ZFSet.{u}) :
    godelDef U ⊆ U.powerset := by
  intro z hz
  exact ZFSet.mem_powerset.mpr (mem_godelDef_iff.mp hz).1

/-- A transitive set is contained in its Gödel-operation definable powerset. -/
theorem subset_godelDef {U : ZFSet.{u}} (hU : U.IsTransitive) :
    U ⊆ godelDef U := by
  intro z hz
  exact mem_godelDef_iff.mpr
    ⟨hU.subset_of_mem hz, subset_rudimentaryClosure U hz⟩

/-- The Gödel-operation candidate preserves transitivity. -/
theorem godelDef_isTransitive {U : ZFSet.{u}} (hU : U.IsTransitive) :
    (godelDef U).IsTransitive := by
  intro z hz x hx
  have hzU : z ⊆ U := (mem_godelDef_iff.mp hz).1
  exact subset_godelDef hU (hzU hx)

@[simp]
theorem godelDef_empty : godelDef (∅ : ZFSet.{u}) = {∅} := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    have hz0 : z = ∅ := (ZFSet.eq_empty z).2 fun y hy =>
      ZFSet.notMem_empty y ((mem_godelDef_iff.mp hz).1 hy)
    simp [hz0]
  · intro hz
    have hz0 : z = ∅ := by simpa using hz
    subst z
    exact mem_godelDef_iff.mpr
      ⟨Set.Subset.rfl, self_mem_rudimentaryClosure (∅ : ZFSet.{u})⟩

/-- The Gödel-operation and formula presentations agree at the empty stage. -/
theorem DefZF_eq_godelDef_empty :
    Constructible.DefZF (∅ : ZFSet.{u}) = godelDef ∅ := by
  rw [Constructible.DefZF_empty, godelDef_empty]

end Constructible.Godel
