/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness of (sub)modules and finitely supported functions

-/

open Function (Surjective)
open Finsupp

namespace Submodule

variable {R M N P : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup P] [Module R P]

open Set

/-- If 0 → M' → M → M'' → 0 is exact and M' and M'' are
finitely generated then so is M. -/
theorem fg_of_fg_map_of_fg_inf_ker (f : M →ₗ[R] P) {s : Submodule R M}
    (hs1 : (s.map f).FG)
    (hs2 : (s ⊓ LinearMap.ker f).FG) : s.FG := by
  haveI := Classical.decEq R
  haveI := Classical.decEq M
  haveI := Classical.decEq P
  obtain ⟨t1, ht1⟩ := hs1
  obtain ⟨t2, ht2⟩ := hs2
  have : ∀ y ∈ t1, ∃ x ∈ s, f x = y := by
    intro y hy
    have : y ∈ s.map f := by
      rw [← ht1]
      exact subset_span hy
    rcases mem_map.1 this with ⟨x, hx1, hx2⟩
    exact ⟨x, hx1, hx2⟩
  have : ∃ g : P → M, ∀ y ∈ t1, g y ∈ s ∧ f (g y) = y := by
    choose g hg1 hg2 using this
    exists fun y => if H : y ∈ t1 then g y H else 0
    intro y H
    constructor
    · simp only [dif_pos H]
      apply hg1
    · simp only [dif_pos H]
      apply hg2
  obtain ⟨g, hg⟩ := this
  clear this
  exists t1.image g ∪ t2
  rw [Finset.coe_union, span_union, Finset.coe_image]
  apply le_antisymm
  · refine sup_le (span_le.2 <| image_subset_iff.2 ?_) (span_le.2 ?_)
    · intro y hy
      exact (hg y hy).1
    · intro x hx
      have : x ∈ span R t2 := subset_span hx
      rw [ht2] at this
      exact this.1
  intro x hx
  have : f x ∈ s.map f := by
    rw [mem_map]
    exact ⟨x, hx, rfl⟩
  rw [← ht1, ← Set.image_id (t1 : Set P), Finsupp.mem_span_image_iff_linearCombination] at this
  rcases this with ⟨l, hl1, hl2⟩
  refine
    mem_sup.2
      ⟨(linearCombination R id).toFun ((lmapDomain R R g : (P →₀ R) → M →₀ R) l), ?_,
        x - linearCombination R id ((lmapDomain R R g : (P →₀ R) → M →₀ R) l), ?_,
        add_sub_cancel _ _⟩
  · rw [← Set.image_id (g '' ↑t1), Finsupp.mem_span_image_iff_linearCombination]
    refine ⟨_, ?_, rfl⟩
    haveI : Inhabited P := ⟨0⟩
    rw [← Finsupp.lmapDomain_supported _ _ g, mem_map]
    refine ⟨l, hl1, ?_⟩
    rfl
  rw [ht2, mem_inf]
  constructor
  · apply s.sub_mem hx
    rw [Finsupp.linearCombination_apply, Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index]
    · refine s.sum_mem ?_
      intro y hy
      exact s.smul_mem _ (hg y (hl1 hy)).1
    · exact zero_smul _
    · exact fun _ _ _ => add_smul _ _ _
  · rw [LinearMap.mem_ker, f.map_sub, ← hl2]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.lmapDomain_apply]
    rw [Finsupp.sum_mapDomain_index, Finsupp.sum, Finsupp.sum, map_sum]
    · rw [sub_eq_zero]
      refine Finset.sum_congr rfl fun y hy => ?_
      unfold id
      rw [f.map_smul, (hg y (hl1 hy)).2]
    · exact zero_smul _
    · exact fun _ _ _ => add_smul _ _ _

/-- The kernel of the composition of two linear maps is finitely generated if both kernels are and
the first morphism is surjective. -/
theorem fg_ker_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf1 : (LinearMap.ker f).FG) (hf2 : (LinearMap.ker g).FG)
    (hsur : Function.Surjective f) : (LinearMap.ker (g.comp f)).FG := by
  rw [LinearMap.ker_comp]
  apply fg_of_fg_map_of_fg_inf_ker f
  · rwa [Submodule.map_comap_eq, LinearMap.range_eq_top.2 hsur, top_inf_eq]
  · rwa [inf_of_le_right (show (LinearMap.ker f) ≤
      (LinearMap.ker g).comap f from comap_mono bot_le)]

theorem _root_.Module.Finite.of_submodule_quotient (N : Submodule R M) [Module.Finite R N]
    [Module.Finite R (M ⧸ N)] : Module.Finite R M where
  fg_top := fg_of_fg_map_of_fg_inf_ker N.mkQ
    (by simpa only [map_top, range_mkQ] using Module.finite_def.mp ‹_›) <| by
    simpa only [top_inf_eq, ker_mkQ] using Module.Finite.iff_fg.mp ‹_›

end Submodule

section

variable {R V} [Semiring R] [AddCommMonoid V] [Module R V]

instance Module.Finite.finsupp {ι : Type*} [_root_.Finite ι] [Module.Finite R V] :
    Module.Finite R (ι →₀ V) :=
  Module.Finite.equiv (Finsupp.linearEquivFunOnFinite R V ι).symm

end

namespace AddMonoidAlgebra
variable {ι R S : Type*} [Finite ι] [Semiring R] [Semiring S] [Module R S] [Module.Finite R S]

instance moduleFinite : Module.Finite R S[ι] := .finsupp

end AddMonoidAlgebra

namespace MonoidAlgebra
variable {ι R S : Type*} [Finite ι] [Semiring R] [Semiring S] [Module R S] [Module.Finite R S]

instance moduleFinite : Module.Finite R (MonoidAlgebra S ι) := .finsupp

end MonoidAlgebra

namespace FreeAbelianGroup
variable {σ : Type*} [Finite σ]

instance : Module.Finite ℤ (FreeAbelianGroup σ) :=
  .of_surjective _ (FreeAbelianGroup.equivFinsupp σ).toIntLinearEquiv.symm.surjective

instance : AddMonoid.FG (FreeAbelianGroup σ) := by
  rw [← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]; infer_instance

end FreeAbelianGroup
