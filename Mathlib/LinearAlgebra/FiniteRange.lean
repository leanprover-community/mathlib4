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

/-- A linear map **has Noetherian range** if its range is a Noetherian module. -/
def HasNoetherianRange (f : V →ₗ[K] V₂) := IsNoetherian K f.range

lemma hasNoetherianRange_iff_range {f : V →ₗ[K] V₂} :
    f.HasNoetherianRange ↔ IsNoetherian K f.range :=
  Iff.rfl

lemma hasFiniteRange_iff_range {f : V →ₗ[K] V₂} :
    f.HasFiniteRange ↔ f.range.FG :=
  Iff.rfl

alias ⟨HasFiniteRange.fg_range, _⟩ := hasFiniteRange_iff_range
alias ⟨HasNoetherianRange.isNoetherian_range, _⟩ := hasNoetherianRange_iff_range

@[simp] lemma HasFiniteRange.zero : (0 : V →ₗ[K] V₂).HasFiniteRange := by
  simp [HasFiniteRange, Submodule.fg_bot]

@[simp] lemma HasNoetherianRange.zero : (0 : V →ₗ[K] V₂).HasNoetherianRange := by
  simp [HasNoetherianRange, isNoetherian_submodule, Submodule.fg_bot]

lemma HasFiniteRange.comp_left {u : V →ₗ[K] V₂} (h : u.HasFiniteRange)
    (v : V₂ →ₗ[K] V₃) : (v ∘ₗ u).HasFiniteRange := by
  rw [LinearMap.HasFiniteRange, LinearMap.range_comp] at *
  exact Submodule.FG.map v h

lemma HasNoetherianRange.comp_left {u : V →ₗ[K] V₂} (h : u.HasNoetherianRange)
    (v : V₂ →ₗ[K] V₃) : (v ∘ₗ u).HasNoetherianRange := by
  rw [LinearMap.HasNoetherianRange, LinearMap.range_comp] at *
  infer_instance

lemma HasNoetherianRange.hasFiniteRange {u : V →ₗ[K] V₂} (h : u.HasNoetherianRange) :
    u.HasFiniteRange :=
  have := h.isNoetherian_range; FG.of_finite

end Semiring

section Ring

variable [Ring K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

lemma HasFiniteRange.hasNoetherianRange [IsNoetherianRing K] {u : V →ₗ[K] V₂}
    (h : u.HasFiniteRange) : u.HasNoetherianRange := by
  rw [HasNoetherianRange]
  have := Finite.of_fg h.fg_range
  infer_instance

lemma hasNoetherianRange_iff_hasFiniteRange [IsNoetherianRing K] {u : V →ₗ[K] V₂} :
    u.HasNoetherianRange ↔ u.HasFiniteRange :=
  ⟨HasNoetherianRange.hasFiniteRange, HasFiniteRange.hasNoetherianRange⟩

lemma HasNoetherianRange.comp_right {v : V₂ →ₗ[K] V₃} (h : v.HasNoetherianRange)
    (u : V →ₗ[K] V₂) : (v ∘ₗ u).HasNoetherianRange := by
  rw [HasNoetherianRange, LinearMap.range_comp] at *
  exact isNoetherian_of_le map_le_range

lemma HasFiniteRange.comp_right [IsNoetherianRing K] {v : V₂ →ₗ[K] V₃} (h : v.HasFiniteRange)
    (u : V →ₗ[K] V₂) : (v ∘ₗ u).HasFiniteRange :=
  h.hasNoetherianRange.comp_right _ |>.hasFiniteRange

@[simp] lemma HasNoetherianRange.neg {f : V →ₗ[K] V₂}
    (hf : f.HasNoetherianRange) : (-f).HasNoetherianRange := by
  rwa [HasNoetherianRange, LinearMap.range_neg]

@[simp] lemma HasFiniteRange.neg {f : V →ₗ[K] V₂}
    (hf : f.HasFiniteRange) : (-f).HasFiniteRange := by
  rwa [HasFiniteRange, LinearMap.range_neg]

@[simp] lemma HasNoetherianRange.add {f g : V →ₗ[K] V₂}
    (hf : f.HasNoetherianRange) (hg : g.HasNoetherianRange) : (f + g).HasNoetherianRange := by
  rw [HasNoetherianRange] at *
  exact isNoetherian_of_le (range_add_le f g)

@[simp] lemma HasFiniteRange.add [IsNoetherianRing K] {f g : V →ₗ[K] V₂}
    (hf : f.HasFiniteRange) (hg : g.HasFiniteRange) : (f + g).HasFiniteRange :=
  hf.hasNoetherianRange.add hg.hasNoetherianRange |>.hasFiniteRange

@[simp] lemma HasNoetherianRange.sub {f g : V →ₗ[K] V₂}
    (hf : f.HasNoetherianRange) (hg : g.HasNoetherianRange) : (f - g).HasNoetherianRange :=
  sub_eq_add_neg f g ▸ hf.add hg.neg

@[simp] lemma HasFiniteRange.sub [IsNoetherianRing K] {f g : V →ₗ[K] V₂}
    (hf : f.HasFiniteRange) (hg : g.HasFiniteRange) : (f - g).HasFiniteRange :=
  sub_eq_add_neg f g ▸ hf.add hg.neg

theorem hasNoetherianRange_iff_quotient_ker {f : V →ₗ[K] V₂} :
    f.HasNoetherianRange ↔ IsNoetherian K (V ⧸ f.ker) :=
  f.quotKerEquivRange.isNoetherian_iff.symm

theorem hasFiniteRange_iff_ker {f : V →ₗ[K] V₂} :
    f.HasFiniteRange ↔ f.ker.CoFG :=
  range_fg_iff_ker_cofg

alias ⟨HasNoetherianRange.quotient_ker, _⟩ := hasNoetherianRange_iff_quotient_ker
alias ⟨HasFiniteRange.cofg_ker, _⟩ := hasFiniteRange_iff_ker

end Ring

section CommRing

variable [CommRing K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

@[simp] lemma HasNoetherianRange.smul {f : V →ₗ[K] V₂}
    (hf : f.HasNoetherianRange) (c : K) : (c • f).HasNoetherianRange :=
  hf.comp_left (lsmul K V₂ c)

@[simp] lemma HasFiniteRange.smul {f : V →ₗ[K] V₂}
    (hf : f.HasFiniteRange) (c : K) : (c • f).HasFiniteRange :=
  hf.comp_left (lsmul K V₂ c)

variable (K V V₂) in
/-- `LinearMap.FiniteRange` is the submodule of `V →ₗ[K] W` consisting of linear maps satisfying
`LinearMap.HasNoetherianRange`. The reason for this discrepancy is that the more natural notion
`LinearMap.HasFiniteRange` only gives rise to a submodule when `K` is noetherian, in which case
it agrees with `LinearMap.HasNoetherianRange`. -/
def finiteRange : Submodule K (V →ₗ[K] V₂) where
  carrier := {u | u.HasNoetherianRange}
  add_mem' hu hv := by simp_all
  zero_mem' := by simp
  smul_mem' c hu := by simp_all

lemma mem_finiteRange_iff_hasNoetherianRange {f : V →ₗ[K] V₂} :
    f ∈ finiteRange K V V₂ ↔ f.HasNoetherianRange :=
  Iff.rfl

lemma mem_finiteRange_iff_hasFiniteRange [IsNoetherianRing K] {f : V →ₗ[K] V₂} :
    f ∈ finiteRange K V V₂ ↔ f.HasFiniteRange := by
  rw [mem_finiteRange_iff_hasNoetherianRange, hasNoetherianRange_iff_hasFiniteRange]

end CommRing

section Setoid

variable [CommRing K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

namespace FiniteRangeSetoid

/-- TODO: rewrite this


This is the equivalence relation on linear maps such that `u ≈ v` precisely
when `u - v` is a finite rank linear map. Equivalently, `u ≈ v` if and only if `u` and `v`
agree on a co-finitely generated subspace of the domain
(see `LinearMap.FiniteRangeSetoid.equiv_iff_eqLocus`).

This setoid is declared as an instance in scope `LinearMap.FiniteRangeSetoid`. -/
scoped instance setoid : Setoid (V →ₗ[K] V₂) := (LinearMap.finiteRange K V V₂).quotientRel

lemma equiv_iff_hasNoetherianRange {u v : V →ₗ[K] V₂} : u ≈ v ↔ (u - v).HasNoetherianRange :=
  Submodule.quotientRel_def _

lemma equiv_iff_hasFiniteRange [IsNoetherianRing K] {u v : V →ₗ[K] V₂} :
    u ≈ v ↔ (u - v).HasFiniteRange := by
  rw [equiv_iff_hasNoetherianRange, hasNoetherianRange_iff_hasFiniteRange]

lemma equiv_iff_isNoetherian_quotient_eqLocus {u v : V →ₗ[K] V₂} :
    u ≈ v ↔ IsNoetherian K (V ⧸ eqLocus u v) := by
  rw [equiv_iff_hasNoetherianRange, hasNoetherianRange_iff_quotient_ker, eqLocus_eq_ker_sub]

lemma equiv_iff_eqLocus_coFG [IsNoetherianRing K] {u v : V →ₗ[K] V₂} :
    u ≈ v ↔ (eqLocus u v).CoFG := by
  rw [equiv_iff_hasFiniteRange, hasFiniteRange_iff_ker, eqLocus_eq_ker_sub]

lemma equiv_of_eqOn_of_isNoetherian {u v : V →ₗ[K] V₂} (A : Submodule K V)
    [quot_A_noeth : IsNoetherian K (V ⧸ A)] (eqOn_A : Set.EqOn u v A) : u ≈ v := by
  have A_le : A ≤ eqLocus u v := le_eqLocus.mpr eqOn_A
  rw [equiv_iff_isNoetherian_quotient_eqLocus]
  refine isNoetherian_of_surjective (A.mapQ (eqLocus u v) id A_le) (by simp [range_mapQ])

lemma equiv_of_eqOn_coFG [IsNoetherianRing K] {u v : V →ₗ[K] V₂} {A : Submodule K V}
    (A_coFG : A.CoFG) (eqOn_A : Set.EqOn u v A) : u ≈ v :=
  equiv_iff_eqLocus_coFG.mpr <| A_coFG.of_le <| le_eqLocus.mpr eqOn_A

@[gcongr]
lemma equiv_comp_right {u : V →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃} (h' : v ≈ v') :
    v ∘ₗ u ≈ v' ∘ₗ u := by
  rw [equiv_iff_hasNoetherianRange] at *
  exact h'.comp_right u

@[gcongr]
lemma equiv_comp_left {u v : V →ₗ[K] V₂} {u' : V₂ →ₗ[K] V₃} (h : u ≈ v) :
    u' ∘ₗ u ≈ u' ∘ₗ v := by
  rw [equiv_iff_hasNoetherianRange] at *
  simpa only [LinearMap.comp_sub] using h.comp_left u'

lemma equiv_comp {u v : V →ₗ[K] V₂} {u' v' : V₂ →ₗ[K] V₃} (h : u ≈ v) (h' : u' ≈ v') :
    u' ∘ₗ u ≈ v' ∘ₗ v := by
  grw [equiv_comp_right h', equiv_comp_left h]

end FiniteRangeSetoid

end Setoid

end LinearMap
