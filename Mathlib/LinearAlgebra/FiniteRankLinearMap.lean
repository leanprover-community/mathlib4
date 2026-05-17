/-
Copyright (c) 2026 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Anatole Dedecker, Yongxi Lin
-/
module

public import Mathlib.RingTheory.Finiteness.Cofinite
public import Mathlib.Algebra.Module.Submodule.EqLocus

/-!
# `HasFiniteRank` predicate on linear maps, and the associated equivalence relation

In this file, we define:

* `LinearMap.HasFiniteRank`: a predicate expressing that a linear map has finitely generated range.
* `LinearMap.FiniteRank`: the submodule of `E →ₗ[K] F` consisting of finite rank linear maps
* `LinearMap.FiniteRankSetoid.setoid`: the setoid on `E →ₗ[K] F` identifying linear maps which
  differ by a finite rank linear map. Equivalently, two linear maps are equivalent for this
  relation if and only if they agree on a co-finitely generated subspace of the domain.
  This is an instance in the scope `LinearMap.FiniteRankSetoid`,
  so opening this scope allows this relation to be denoted by `≈`.
* `LinearMap.QuasiInverse`: two linear maps `u` and `v` are **quasi-inverses** if we have
  `u ∘ₗ v ≈ id` and `v ∘ₗ u ≈ id` modulo finite rank linear maps.
-/

@[expose] public section

open LinearMap Submodule

namespace LinearMap

variable {K V V' V₂ V₂' V₃ : Type*}

section Semiring

variable [Semiring K]
  [AddCommMonoid V] [Module K V]
  [AddCommMonoid V₂] [Module K V₂]
  [AddCommMonoid V₃] [Module K V₃]

/-- A linear map **has finite rank** if its range is finitely generated. -/
def HasFiniteRank (f : V →ₗ[K] V₂) := f.range.FG

lemma hasFiniteRank_iff_range {f : V →ₗ[K] V₂} :
    f.HasFiniteRank ↔ f.range.FG :=
  Iff.rfl

alias ⟨HasFiniteRank.fg_range, _⟩ := hasFiniteRank_iff_range

@[simp] lemma HasFiniteRank.zero : (0 : V →ₗ[K] V₂).HasFiniteRank := by
  simp [HasFiniteRank, Submodule.fg_bot]

lemma HasFiniteRank.comp_left {u : V →ₗ[K] V₂} (h : u.HasFiniteRank)
    (v : V₂ →ₗ[K] V₃) : (v ∘ₗ u).HasFiniteRank := by
  rw [LinearMap.HasFiniteRank, LinearMap.range_comp] at *
  exact Submodule.FG.map v h

end Semiring

section Ring

variable [Ring K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

lemma HasFiniteRank.comp_right [IsNoetherianRing K] {v : V₂ →ₗ[K] V₃} (h : v.HasFiniteRank)
    (u : V →ₗ[K] V₂) : (v ∘ₗ u).HasFiniteRank := by
  rw [LinearMap.HasFiniteRank, LinearMap.range_comp] at *
  exact .of_le h map_le_range

@[simp] lemma HasFiniteRank.neg {f : V →ₗ[K] V₂}
    (hf : f.HasFiniteRank) : (-f).HasFiniteRank := by
  rwa [HasFiniteRank, LinearMap.range_neg]

@[simp] lemma HasFiniteRank.add [IsNoetherianRing K] {f g : V →ₗ[K] V₂}
    (hf : f.HasFiniteRank) (hg : g.HasFiniteRank) : (f + g).HasFiniteRank :=
  .of_le (hf.sup hg) (range_add_le f g)

@[simp] lemma HasFiniteRank.sub [IsNoetherianRing K] {f g : V →ₗ[K] V₂}
    (hf : f.HasFiniteRank) (hg : g.HasFiniteRank) : (f - g).HasFiniteRank :=
  sub_eq_add_neg f g ▸ hf.add hg.neg

theorem hasFiniteRank_iff_ker {f : V →ₗ[K] V₂} :
    f.HasFiniteRank ↔ f.ker.CoFG :=
  range_fg_iff_ker_cofg

alias ⟨HasFiniteRank.cofg_ker, _⟩ := hasFiniteRank_iff_ker

end Ring

section CommRing

variable [CommRing K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

@[simp] lemma HasFiniteRank.smul [IsNoetherianRing K] {f : V →ₗ[K] V₂}
    (hf : f.HasFiniteRank) (c : K) : (c • f).HasFiniteRank :=
  .of_le hf <| range_smul_le_range _ _

variable (K V V₂) in
/-- `LinearMap.FiniteRank` is the submodule of `V →ₗ[K] W` consiting
of finite rank linear maps. -/
def FiniteRank [IsNoetherianRing K] : Submodule K (V →ₗ[K] V₂) where
  carrier := {u | u.HasFiniteRank}
  add_mem' hu hv := by simp_all
  zero_mem' := by simp
  smul_mem' c hu := by simp_all

end CommRing

section Setoid

variable [CommRing K] [IsNoetherianRing K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

namespace FiniteRankSetoid

/-- This is the equivalence relation on linear maps such that `u ≈ v` precisely
when `u - v` is a finite rank linear map. Equivalently, `u ≈ v` if and only if `u` and `v`
agree on a co-finitely generated subspace of the domain
(see `LinearMap.FiniteRankSetoid.equiv_iff_eqLocus`).

This setoid is declared as an instance in scope `LinearMap.FiniteRankSetoid`. -/
scoped instance setoid : Setoid (V →ₗ[K] V₂) := (LinearMap.FiniteRank K V V₂).quotientRel

lemma equiv_iff {u v : V →ₗ[K] V₂} : u ≈ v ↔ (u - v).HasFiniteRank := by
  exact Submodule.quotientRel_def _

lemma equiv_iff_eqLocus {u v : V →ₗ[K] V₂} : u ≈ v ↔ (LinearMap.eqLocus u v).CoFG := by
  rw [equiv_iff, hasFiniteRank_iff_ker, eqLocus_eq_ker_sub]

lemma equiv_of_eqOn {u v : V →ₗ[K] V₂} {A : Submodule K V} (A_coFG : A.CoFG)
    (eqOn_A : Set.EqOn u v A) : u ≈ v :=
  equiv_iff_eqLocus.mpr <| A_coFG.of_le <| le_eqLocus.mpr eqOn_A

@[gcongr]
lemma equiv_comp_right {u : V →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃} (h' : v ≈ v') :
    v ∘ₗ u ≈ v' ∘ₗ u := by
  rw [equiv_iff] at *
  exact h'.comp_right u

@[gcongr]
lemma equiv_comp_left {u v : V →ₗ[K] V₂} {u' : V₂ →ₗ[K] V₃} (h : u ≈ v) :
    u' ∘ₗ u ≈ u' ∘ₗ v := by
  rw [equiv_iff] at *
  simpa only [LinearMap.comp_sub] using h.comp_left u'

lemma equiv_comp {u v : V →ₗ[K] V₂} {u' v' : V₂ →ₗ[K] V₃} (h : u ≈ v) (h' : u' ≈ v') :
    u' ∘ₗ u ≈ v' ∘ₗ v := by
  grw [equiv_comp_right h', equiv_comp_left h]

end FiniteRankSetoid

end Setoid

section QuasiInverse

variable [CommRing K] [IsNoetherianRing K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

open scoped LinearMap.FiniteRankSetoid

/-- `u` is a **left quasi-inverse** to `v` if `u ∘ₗ v ≈ id` modulo
finite rank linear maps. -/
def LeftQuasiInverse (u : V →ₗ[K] V₂) (v : V₂ →ₗ[K] V) := u ∘ₗ v ≈ .id

/-- `u` is a **right quasi-inverse** to `v` if `v ∘ₗ u ≈ id` modulo
finite rank linear maps. -/
def RightQuasiInverse (u : V₃ →ₗ[K] V₂) (v : V₂ →ₗ[K] V₃) := v ∘ₗ u ≈ .id

/-- `u` is a **quasi-inverse** to `v` if `u ∘ₗ v ≈ id` and `v ∘ₗ u ≈ id` modulo
finite rank linear maps. -/
def QuasiInverse (u : V₃ →ₗ[K] V₂) (v : V₂ →ₗ[K] V₃) :=
  u.LeftQuasiInverse v ∧ u.RightQuasiInverse v

lemma LeftQuasiInverse.equiv {u : V₃ →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    (h : u.LeftQuasiInverse v) : u ∘ₗ v ≈ .id := h

lemma RightQuasiInverse.equiv {u : V₃ →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    (h : u.RightQuasiInverse v) : v ∘ₗ u ≈ .id := h

@[symm]
lemma QuasiInverse.symm {u : V₃ →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    (h : u.QuasiInverse v) : v.QuasiInverse u :=
  And.symm h

lemma LeftQuasiInverse.congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.LeftQuasiInverse v) (hu : u' ≈ u) (hv : v' ≈ v) :
    u'.LeftQuasiInverse v' := by
  unfold LeftQuasiInverse at *
  grw [hu, hv]
  assumption

lemma leftQuasiInverse_congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (hu : u' ≈ u) (hv : v' ≈ v) :
    u.LeftQuasiInverse v ↔ u'.LeftQuasiInverse v' :=
  ⟨fun H ↦ H.congr hu hv, fun H ↦ H.congr (Setoid.symm hu) (Setoid.symm hv)⟩

lemma RightQuasiInverse.congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.RightQuasiInverse v) (hu : u' ≈ u) (hv : v' ≈ v) :
    u'.RightQuasiInverse v' := by
  unfold RightQuasiInverse at *
  grw [hu, hv]
  assumption

lemma rightQuasiInverse_congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (hu : u' ≈ u) (hv : v' ≈ v) :
    u.RightQuasiInverse v ↔ u'.RightQuasiInverse v' :=
  ⟨fun H ↦ H.congr hu hv, fun H ↦ H.congr (Setoid.symm hu) (Setoid.symm hv)⟩

lemma QuasiInverse.congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.QuasiInverse v) (hu : u' ≈ u) (hv : v' ≈ v) :
    u'.QuasiInverse v' :=
  ⟨h.1.congr hu hv, h.2.congr hu hv⟩

lemma quasiInverse_congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (hu : u' ≈ u) (hv : v' ≈ v) :
    u.QuasiInverse v ↔ u'.QuasiInverse v' := by
  simp [QuasiInverse, leftQuasiInverse_congr hu hv, rightQuasiInverse_congr hu hv]

lemma QuasiInverse.equiv_of_left {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.QuasiInverse v) (h' : u'.QuasiInverse v') (hu : u ≈ u') :
    v ≈ v' :=
  calc
    v = v ∘ₗ .id := by simp
    _ ≈ v ∘ₗ (u' ∘ₗ v') := by grw [h'.1.equiv]
    _ ≈ v ∘ₗ (u ∘ₗ v') := by grw [hu]
    _ = (v ∘ₗ u) ∘ₗ v' := by rw [comp_assoc]
    _ ≈ .id ∘ₗ v' := by grw [h.2.equiv]
    _ = v' := by simp

lemma QuasiInverse.equiv_of_right {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.QuasiInverse v) (h' : u'.QuasiInverse v') (hv : v ≈ v') :
    u ≈ u' :=
  h.symm.equiv_of_left h'.symm hv

/-- Left quasi-inverses compose in the opposite order. -/
lemma LeftQuasiInverse.comp {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} {u' : V₂ →ₗ[K] V}
    {v' : V₃ →ₗ[K] V₂} (hu : u'.LeftQuasiInverse u) (hv : v'.LeftQuasiInverse v) :
    (u' ∘ₗ v').LeftQuasiInverse (v ∘ₗ u) :=
  calc
    _ = u' ∘ₗ (v' ∘ₗ v) ∘ₗ u := rfl
    _ ≈ u' ∘ₗ .id ∘ₗ u := by grw [hv.equiv]
    _ ≈ .id := hu.equiv

/-- Right quasi-inverses compose in the opposite order. -/
lemma RightQuasiInverse.comp {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} {u' : V₂ →ₗ[K] V}
    {v' : V₃ →ₗ[K] V₂} (hu : u'.RightQuasiInverse u) (hv : v'.RightQuasiInverse v) :
    (u' ∘ₗ v').RightQuasiInverse (v ∘ₗ u) :=
  calc
    _ = v ∘ₗ (u ∘ₗ u') ∘ₗ v' := rfl
    _ ≈ v ∘ₗ .id ∘ₗ v' := by grw [hu.equiv]
    _ ≈ .id := hv.equiv

/-- Quasi-inverses compose in the opposite order. -/
lemma QuasiInverse.comp {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃} {u' : V₂ →ₗ[K] V}
    {v' : V₃ →ₗ[K] V₂} (hu : u'.QuasiInverse u) (hv : v'.QuasiInverse v) :
    (u' ∘ₗ v').QuasiInverse (v ∘ₗ u) :=
  ⟨hu.1.comp hv.1, hu.2.comp hv.2⟩

/-- If `u'` is a right quasi-inverse of `u` and `w` is a left quasi-inverse of `v ∘ₗ u`,
then `u ∘ₗ w` is a left quasi-inverse of `v`. -/
lemma LeftQuasiInverse.of_comp_left {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    {u' : V₂ →ₗ[K] V} {w : V₃ →ₗ[K] V} (hu : u'.RightQuasiInverse u)
    (hw : w.LeftQuasiInverse (v ∘ₗ u)) :
    (u ∘ₗ w).LeftQuasiInverse v := by
  calc
    _ = ((u ∘ₗ w) ∘ₗ v) ∘ₗ .id := rfl
    _ ≈ ((u ∘ₗ w) ∘ₗ v) ∘ₗ (u ∘ₗ u') := by grw [hu.equiv]
    _ = u ∘ₗ (w ∘ₗ (v ∘ₗ u)) ∘ₗ u' := rfl
    _ ≈ u ∘ₗ .id ∘ₗ u' := by grw [hw.equiv]
    _ ≈ .id := hu.equiv

/-- If `u'` is a quasi-inverse of `u` and `w` is a quasi-inverse of `v ∘ₗ u`, then
`u ∘ₗ w` is a quasi-inverse of `v`. -/
lemma QuasiInverse.of_comp_left {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    {u' : V₂ →ₗ[K] V} {w : V₃ →ₗ[K] V} (hu : u'.QuasiInverse u)
    (hw : w.QuasiInverse (v ∘ₗ u)) :
    (u ∘ₗ w).QuasiInverse v :=
  ⟨LeftQuasiInverse.of_comp_left hu.2 hw.1, hw.2⟩

/-- If `v'` is a left quasi-inverse of `v` and `w` is a right quasi-inverse of `v ∘ₗ u`,
then `w ∘ₗ v` is a right quasi-inverse of `u`. -/
lemma RightQuasiInverse.of_comp_right {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    {v' : V₃ →ₗ[K] V₂} {w : V₃ →ₗ[K] V} (hv : v'.LeftQuasiInverse v)
    (hw : w.RightQuasiInverse (v ∘ₗ u)) :
    (w ∘ₗ v).RightQuasiInverse u := by
  calc
    _ = .id ∘ₗ (u ∘ₗ (w ∘ₗ v)) := rfl
    _ ≈ (v' ∘ₗ v) ∘ₗ (u ∘ₗ (w ∘ₗ v)) := by grw [hv.equiv]
    _ = v' ∘ₗ ((v ∘ₗ u) ∘ₗ w) ∘ₗ v := rfl
    _ ≈ v' ∘ₗ .id ∘ₗ v := by grw [hw.equiv]
    _ ≈ .id := hv.equiv

/-- If `v'` is a quasi-inverse of `v` and `w` is a quasi-inverse of `v ∘ₗ u`, then
`w ∘ₗ v` is a quasi-inverse of `u`. -/
lemma QuasiInverse.of_comp_right {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    {v' : V₃ →ₗ[K] V₂} {w : V₃ →ₗ[K] V} (hv : v'.QuasiInverse v)
    (hw : w.QuasiInverse (v ∘ₗ u)) :
    (w ∘ₗ v).QuasiInverse u :=
  ⟨hw.1, RightQuasiInverse.of_comp_right hv.1 hw.2⟩

end QuasiInverse

end LinearMap
