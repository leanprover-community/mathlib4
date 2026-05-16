/-
Copyright (c) 2026 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Anatole Dedecker
-/
module

public import Mathlib.RingTheory.Finiteness.Cofinite
public import Mathlib.Algebra.Module.Submodule.EqLocus

/-!
# `HasFiniteRank` predicate on linear maps, and the associated equivalence relation

In this file, we define:

* `LinearMap.HasFiniteRank`: a predicate expressing that a linear map has finitely generated range
  or, equivalently, co-finitely-generated kernel.
* `LinearMap.FiniteRank`: the submodule of `E →ₗ[K] F` consisting of finite rank linear maps
* `LinearMap.FiniteRankSetoid.setoid`: the setoid on `E →ₗ[K] F` identifying linear maps which
  differ by a finite rank linear map. This is an instance in the scope `LinearMap.FiniteRankSetoid`,
  so opening this scope allows this relation to be denoted by `≈`.
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

end LinearMap
