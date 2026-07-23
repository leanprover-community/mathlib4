/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness of (sub)modules and finitely supported functions

-/

public section

open Function (Surjective)
open Finsupp

namespace LinearMap

variable {R M N ι : Type*} (S : Type*) [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N] [Semiring S] [Module S N] [SMulCommClass R S N]

/-- The linear map from `Hom(M,N)^(ι)` to `Hom(M,N^(ι))`. This is the `Finsupp` version of
the forward direction of `LinearEquiv.linearMapPi`. -/
@[expose, simps!] noncomputable def finsuppLinearMap : (ι →₀ M →ₗ[R] N) →ₗ[S] M →ₗ[R] ι →₀ N :=
  have := SMulCommClass.symm
  LinearMap.flip
  { toFun := (Finsupp.mapRange.linearMap <| flip id ·)
    map_add' := fun _ _ ↦ by ext; simp
    map_smul' := fun _ _ ↦ by ext; simp }

variable (R M N ι)

theorem finsuppLinearMap_injective :
    Function.Injective (finsuppLinearMap S : (ι →₀ M →ₗ[R] N) → M →ₗ[R] ι →₀ N) :=
  fun _ _ eq ↦ by ext i m; exact congr($eq m i)

theorem finsuppLinearMap_bijective_of_moduleFinite [Module.Finite R M] :
    Function.Bijective (finsuppLinearMap S : (ι →₀ M →ₗ[R] N) → M →ₗ[R] ι →₀ N) := by
  have ⟨s, span_s⟩ := Module.finite_def.mp ‹Module.Finite R M›
  classical refine ⟨finsuppLinearMap_injective ..,
    fun x ↦ ⟨.onFinset (s.sup fun m ↦ (x m).support) (lapply · ∘ₗ x) fun i h ↦ ?_, ?_⟩⟩
  · contrapose! h; exact LinearMap.ext_on span_s (by simpa using! h)
  · ext; rfl

theorem finsuppLinearMap_bijective_of_finite [Finite ι] :
    Function.Bijective (finsuppLinearMap S : (ι →₀ M →ₗ[R] N) → M →ₗ[R] ι →₀ N) where
  left := finsuppLinearMap_injective ..
  right x := ⟨equivFunOnFinite.symm fun i ↦ lapply i ∘ₗ x, by ext; simp⟩

end LinearMap

namespace Submodule

variable {R M N P : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup P] [Module R P]

open Set

/-- If 0 → M' → M → M'' → 0 is exact and M' and M'' are
finitely generated then so is M. -/
theorem fg_of_fg_map_of_fg_inf_ker (f : M →ₗ[R] P) {s : Submodule R M}
    (hs1 : (s.map f).FG)
    (hs2 : (s ⊓ LinearMap.ker f).FG) : s.FG := by
  have := Classical.decEq R
  have := Classical.decEq M
  have := Classical.decEq P
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
    have : Inhabited P := ⟨0⟩
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

/-- If $M → N → P → 0$ is exact and $M$ and $P$ are finitely generated then so is $N$.

This is the `Module.Finite` version of `Submodule.fg_of_fg_map_of_fg_inf_ker`. -/
@[stacks 0519 "(1)"]
lemma _root_.Module.Finite.of_exact {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h_exact : Function.Exact f g) (h_surj : Function.Surjective g)
    [Module.Finite R M] [Module.Finite R P] : Module.Finite R N := by
  refine ⟨(⊤ : Submodule R _).fg_of_fg_map_of_fg_inf_ker g ?_ ?_⟩
  · rw [← LinearMap.range_eq_top] at h_surj
    rw [Submodule.map_top, h_surj]
    exact Module.Finite.fg_top
  · simp [LinearMap.exact_iff.1 h_exact]

theorem _root_.Module.Finite.of_submodule_quotient (N : Submodule R M) [Module.Finite R N]
    [Module.Finite R (M ⧸ N)] : Module.Finite R M :=
  .of_exact (LinearMap.exact_subtype_mkQ N) (Quotient.mk_surjective _)

end Submodule

section

variable {R V} [Semiring R] [AddCommMonoid V] [Module R V]

instance Module.Finite.finsupp {ι : Type*} [_root_.Finite ι] [Module.Finite R V] :
    Module.Finite R (ι →₀ V) :=
  Module.Finite.equiv (Finsupp.linearEquivFunOnFinite R V ι).symm

end

namespace AddMonoidAlgebra
variable {M R S : Type*} [Finite M] [Semiring R] [Semiring S] [Module R S] [Module.Finite R S]

instance moduleFinite : Module.Finite R S[M] := .equiv <| .symm <| coeffLinearEquiv _

end AddMonoidAlgebra

namespace MonoidAlgebra
variable {M R S : Type*} [Finite M] [Semiring R] [Semiring S] [Module R S] [Module.Finite R S]

instance moduleFinite : Module.Finite R S[M] := .equiv <| .symm <| coeffLinearEquiv _

end MonoidAlgebra

namespace FreeAbelianGroup
variable {σ : Type*} [Finite σ]

instance : Module.Finite ℤ (FreeAbelianGroup σ) :=
  .of_surjective _ (FreeAbelianGroup.equivFinsupp σ).toIntLinearEquiv.symm.surjective

instance : AddMonoid.FG (FreeAbelianGroup σ) := by
  rw [← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]; infer_instance

end FreeAbelianGroup
