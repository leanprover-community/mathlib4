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

In this file, we define `LinearMap.HasFiniteRank`, which expresses that a linear map
has finitely generated range or, equivalently, co-finitely-generated kernel.

TODO
-/

@[expose] public section

open LinearMap Submodule

namespace LinearMap

variable {K V V' V₂ V₃ : Type*}

section Semiring

variable [Semiring K]
  [AddCommMonoid V] [Module K V]
  [AddCommMonoid V₂] [Module K V₂]
  [AddCommMonoid V₃] [Module K V₃]

def HasFiniteRank (f : V →ₗ[K] V₂) := f.range.FG

theorem hasFiniteRank_iff_range {f : V →ₗ[K] V₂} :
    f.HasFiniteRank ↔ f.range.FG :=
  Iff.rfl

alias ⟨HasFiniteRank.fg_range, _⟩ := hasFiniteRank_iff_range

@[simp] theorem HasFiniteRank.zero : (0 : V →ₗ[K] V₂).HasFiniteRank := by
  simp [HasFiniteRank, range_zero, Submodule.fg_bot]

@[simp] def HasFiniteRank.smul {f : V →ₗ[K] V₂}
    (hf : f.HasFiniteRank) (c : K) : (c • f).HasFiniteRank := by
  unfold LinearMap.HasFiniteRank at *
  rw [← Submodule.fg_iff_finiteDimensional] at *
  exact hf.of_le <| LinearMap.range_smul_le _ c

end Semiring

section Ring

variable [Ring K]
  [AddCommGroup V] [Module K V]
  [AddCommMonoid V'] [Module K V']
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

@[simp] lemma HasFiniteRank.neg {f : V' →ₗ[K] V₂}
    (hf : f.HasFiniteRank) : (-f).HasFiniteRank := by
  rwa [HasFiniteRank, LinearMap.range_neg]

@[simp] lemma HasFiniteRank.add [IsNoetherianRing K] {f g : V' →ₗ[K] V₂}
    (hf : f.HasFiniteRank) (hg : g.HasFiniteRank) : (f + g).HasFiniteRank :=
  .of_le (hf.sup hg) (range_add_le f g)

@[simp] lemma HasFiniteRank.sub [IsNoetherianRing K] {f g : V' →ₗ[K] V₂}
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
  [AddCommMonoid V'] [Module K V']
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

variable (K V' V₂) in
def FiniteRank [IsNoetherianRing K] : Submodule K (V' →ₗ[K] V₂) where
  carrier := {u | u.HasFiniteRank}
  add_mem' hu hv := by simp_all
  zero_mem' := by simp
  smul_mem' c hu := by sorry

end CommRing

section Setoid

variable [CommRing K] [IsNoetherianRing K]
  [AddCommGroup V] [Module K V]
  [AddCommMonoid V'] [Module K V']
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

namespace FiniteRankSetoid

scoped instance setoid : Setoid (V' →ₗ[K] V₂) := (LinearMap.FiniteRank K V' V₂).quotientRel

lemma equiv_iff {u v : V' →ₗ[K] V₂} : u ≈ v ↔ (u - v).HasFiniteRank := by
  exact Submodule.quotientRel_def _

lemma equiv_iff_eqLocus {u v : V →ₗ[K] V₂} : u ≈ v ↔ (LinearMap.eqLocus u v).CoFG := by
  rw [equiv_iff, hasFiniteRank_iff_ker, eqLocus_eq_ker_sub]

lemma equiv_of_eqOn {u v : V →ₗ[K] V₂} {A : Submodule K V} (A_coFG : A.CoFG)
    (eqOn_A : Set.EqOn u v A) : u ≈ v :=
  equiv_iff_eqLocus.mpr <| A_coFG.of_le <| le_eqLocus.mpr eqOn_A

lemma equiv_comp {u v : V →ₗ[K] V₂} {u' v' : V₂ →ₗ[K] V₃} (h : u ≈ v) (h' : u' ≈ v') :
    u' ∘ₗ u ≈ v' ∘ₗ v := by
  rw [equiv_iff] at *
  exact h.comp_sub_comp h'

@[gcongr]
lemma equiv_comp_right {u : V →ₗ[K] V₂} {u' v' : V₂ →ₗ[K] V₃} (h' : u' ≈ v') :
    u' ∘ₗ u ≈ v' ∘ₗ u :=
  equiv_comp (Quotient.exact rfl) h'

@[gcongr]
lemma equiv_comp_left {u v : V →ₗ[K] V₂} {u' : V₂ →ₗ[K] V₃} (h : u ≈ v) :
    u' ∘ₗ u ≈ u' ∘ₗ v :=
  equiv_comp h (Quotient.exact rfl)

end FiniteRankSetoid

end Setoid

end LinearMap
