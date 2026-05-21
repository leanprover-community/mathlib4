/-
Copyright (c) 2026 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Anatole Dedecker
-/
module

public import Mathlib.RingTheory.Finiteness.Cofinite
public import Mathlib.Algebra.Module.Submodule.EqLocus

/-!
# `HasFiniteRange` predicate on linear maps, and the associated equivalence relation

In this file, we define:

* `LinearMap.HasFiniteRange`: a predicate expressing that a linear map has finitely generated range.
* `LinearMap.FiniteRange`: the submodule of `E →ₗ[K] F` consisting of finite rank linear maps
* `LinearMap.FiniteRangeSetoid.setoid`: the setoid on `E →ₗ[K] F` identifying linear maps which
  differ by a finite rank linear map. Equivalently, two linear maps are equivalent for this
  relation if and only if they agree on a co-finitely generated subspace of the domain.
  This is an instance in the scope `LinearMap.FiniteRangeSetoid`,
  so opening this scope allows this relation to be denoted by `≈`.
-/

@[expose] public section

open LinearMap Submodule Module

namespace LinearMap

variable {K V V' V₂ V₂' V₃ : Type*}

section Semiring

variable [Semiring K]
  [AddCommMonoid V] [Module K V]
  [AddCommMonoid V₂] [Module K V₂]
  [AddCommMonoid V₃] [Module K V₃]

/-- A linear map **has finite range** if its range is finitely generated. -/
def HasFiniteRange (f : V →ₗ[K] V₂) := f.range.FG

lemma hasFiniteRange_iff_range {f : V →ₗ[K] V₂} :
    f.HasFiniteRange ↔ f.range.FG :=
  Iff.rfl

alias ⟨HasFiniteRange.fg_range, _⟩ := hasFiniteRange_iff_range

@[simp] lemma HasFiniteRange.zero : (0 : V →ₗ[K] V₂).HasFiniteRange := by
  simp [HasFiniteRange, Submodule.fg_bot]

lemma HasFiniteRange.comp_left {u : V →ₗ[K] V₂} (h : u.HasFiniteRange)
    (v : V₂ →ₗ[K] V₃) : (v ∘ₗ u).HasFiniteRange := by
  rw [LinearMap.HasFiniteRange, LinearMap.range_comp] at *
  exact Submodule.FG.map v h

/-- A linear map **has Noetherian range** if its range is a Noetherian module. -/
def HasNoetherianRange (f : V →ₗ[K] V₂) := IsNoetherian K f.range

lemma hasNoetherianRange_iff_range {f : V →ₗ[K] V₂} :
    f.HasNoetherianRange ↔ IsNoetherian K f.range :=
  Iff.rfl

alias ⟨HasNoetherianRange.isNoetherian_range, _⟩ := hasNoetherianRange_iff_range

@[simp] lemma HasNoetherianRange.zero : (0 : V →ₗ[K] V₂).HasNoetherianRange := by
  simp [HasNoetherianRange, isNoetherian_submodule, Submodule.fg_bot]

lemma HasNoetherianRange.comp_left {u : V →ₗ[K] V₂} (h : u.HasNoetherianRange)
    (v : V₂ →ₗ[K] V₃) : (v ∘ₗ u).HasNoetherianRange := by
  rw [LinearMap.HasNoetherianRange, LinearMap.range_comp] at *
  sorry --missing API

lemma HasNoetherianRange.hasFiniteRange {u : V →ₗ[K] V₂} (h : u.HasNoetherianRange) :
    u.HasFiniteRange :=
  have := h.isNoetherian_range; FG.of_finite

end Semiring

section Ring

variable [Ring K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

lemma HasFiniteRange.comp_right [IsNoetherianRing K] {v : V₂ →ₗ[K] V₃} (h : v.HasFiniteRange)
    (u : V →ₗ[K] V₂) : (v ∘ₗ u).HasFiniteRange := by
  rw [LinearMap.HasFiniteRange, LinearMap.range_comp] at *
  exact .of_le h map_le_range

@[simp] lemma HasFiniteRange.neg {f : V →ₗ[K] V₂}
    (hf : f.HasFiniteRange) : (-f).HasFiniteRange := by
  rwa [HasFiniteRange, LinearMap.range_neg]

@[simp] lemma HasFiniteRange.add [IsNoetherianRing K] {f g : V →ₗ[K] V₂}
    (hf : f.HasFiniteRange) (hg : g.HasFiniteRange) : (f + g).HasFiniteRange :=
  .of_le (hf.sup hg) (range_add_le f g)

@[simp] lemma HasFiniteRange.sub [IsNoetherianRing K] {f g : V →ₗ[K] V₂}
    (hf : f.HasFiniteRange) (hg : g.HasFiniteRange) : (f - g).HasFiniteRange :=
  sub_eq_add_neg f g ▸ hf.add hg.neg

theorem HasFiniteRange_iff_ker {f : V →ₗ[K] V₂} :
    f.HasFiniteRange ↔ f.ker.CoFG :=
  range_fg_iff_ker_cofg

alias ⟨HasFiniteRange.cofg_ker, _⟩ := HasFiniteRange_iff_ker

end Ring

section CommRing

variable [CommRing K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

@[simp] lemma HasFiniteRange.smul [IsNoetherianRing K] {f : V →ₗ[K] V₂}
    (hf : f.HasFiniteRange) (c : K) : (c • f).HasFiniteRange :=
  .of_le hf <| range_smul_le_range _ _

variable (K V V₂) in
/-- `LinearMap.FiniteRange` is the submodule of `V →ₗ[K] W` consiting
of finite rank linear maps. -/
def FiniteRange [IsNoetherianRing K] : Submodule K (V →ₗ[K] V₂) where
  carrier := {u | u.HasFiniteRange}
  add_mem' hu hv := by simp_all
  zero_mem' := by simp
  smul_mem' c hu := by simp_all

end CommRing

section Setoid

variable [CommRing K] [IsNoetherianRing K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

namespace FiniteRangeSetoid

/-- This is the equivalence relation on linear maps such that `u ≈ v` precisely
when `u - v` is a finite rank linear map. Equivalently, `u ≈ v` if and only if `u` and `v`
agree on a co-finitely generated subspace of the domain
(see `LinearMap.FiniteRangeSetoid.equiv_iff_eqLocus`).

This setoid is declared as an instance in scope `LinearMap.FiniteRangeSetoid`. -/
scoped instance setoid : Setoid (V →ₗ[K] V₂) := (LinearMap.FiniteRange K V V₂).quotientRel

lemma equiv_iff {u v : V →ₗ[K] V₂} : u ≈ v ↔ (u - v).HasFiniteRange := by
  exact Submodule.quotientRel_def _

lemma equiv_iff_eqLocus {u v : V →ₗ[K] V₂} : u ≈ v ↔ (LinearMap.eqLocus u v).CoFG := by
  rw [equiv_iff, HasFiniteRange_iff_ker, eqLocus_eq_ker_sub]

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

end FiniteRangeSetoid

end Setoid

end LinearMap
