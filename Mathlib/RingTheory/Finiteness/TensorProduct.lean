/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Bilinear
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Finiteness of the tensor product of (sub)modules

TODO: this file can probably be merged with `RingTheory.TensorProduct.Finite`,
although the two files are currently incomparable in the import graph:
we will need further cleanup of the lemmas involved before we can do this.
-/

open Function (Surjective)
open Finsupp

namespace Submodule

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

open Set

variable {P : Type*} [AddCommMonoid P] [Module R P]
variable (f : M →ₗ[R] P)

variable {f}

open TensorProduct LinearMap in
/-- Every `x : I ⊗ M` is the image of some `y : J ⊗ M`, where `J ≤ I` is finitely generated,
under the tensor product of `J.inclusion ‹J ≤ I› : J → I` and the identity `M → M`. -/
theorem exists_fg_le_eq_rTensor_inclusion {R M N : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] {I : Submodule R N} (x : I ⊗ M) :
      ∃ (J : Submodule R N) (_ : J.FG) (hle : J ≤ I) (y : J ⊗ M),
        x = rTensor M (J.inclusion hle) y := by
  induction x with
  | zero => exact ⟨⊥, fg_bot, zero_le _, 0, rfl⟩
  | tmul i m => exact ⟨R ∙ i.val, fg_span_singleton i.val,
      (span_singleton_le_iff_mem _ _).mpr i.property,
      ⟨i.val, mem_span_singleton_self _⟩ ⊗ₜ[R] m, rfl⟩
  | add x₁ x₂ ihx₁ ihx₂ =>
    obtain ⟨J₁, hfg₁, hle₁, y₁, rfl⟩ := ihx₁
    obtain ⟨J₂, hfg₂, hle₂, y₂, rfl⟩ := ihx₂
    refine ⟨J₁ ⊔ J₂, hfg₁.sup hfg₂, sup_le hle₁ hle₂,
      rTensor M (J₁.inclusion (le_sup_left : J₁ ≤ J₁ ⊔ J₂)) y₁ +
        rTensor M (J₂.inclusion (le_sup_right : J₂ ≤ J₁ ⊔ J₂)) y₂, ?_⟩
    rewrite [map_add, ← rTensor_comp_apply, ← rTensor_comp_apply]
    rfl

end Submodule

section ModuleAndAlgebra

variable (R A B M N : Type*)

/-- Porting note: reminding Lean about this instance for Module.Finite.base_change -/
noncomputable local instance
    [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M] [Module R M] :
    Module A (TensorProduct R A M) :=
  haveI : SMulCommClass R A A := IsScalarTower.to_smulCommClass
  TensorProduct.leftModule

instance Module.Finite.base_change [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]
    [Module R M] [h : Module.Finite R M] : Module.Finite A (TensorProduct R A M) := by
  classical
    obtain ⟨s, hs⟩ := h.out
    refine ⟨⟨s.image (TensorProduct.mk R A M 1), eq_top_iff.mpr ?_⟩⟩
    rintro x -
    induction x with
    | zero => exact zero_mem _
    | tmul x y =>
      -- Porting note: new TC reminder
      haveI : IsScalarTower R A (TensorProduct R A M) := TensorProduct.isScalarTower_left
      rw [Finset.coe_image, ← Submodule.span_span_of_tower R, Submodule.span_image, hs,
        Submodule.map_top, LinearMap.range_coe]
      change _ ∈ Submodule.span A (Set.range <| TensorProduct.mk R A M 1)
      rw [← mul_one x, ← smul_eq_mul, ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ x (Submodule.subset_span <| Set.mem_range_self y)
    | add x y hx hy => exact Submodule.add_mem _ hx hy

instance Module.Finite.tensorProduct [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [hM : Module.Finite R M] [hN : Module.Finite R N] :
    Module.Finite R (TensorProduct R M N) where
  out := (TensorProduct.map₂_mk_top_top_eq_top R M N).subst (hM.out.map₂ _ hN.out)

end ModuleAndAlgebra

section NontrivialTensorProduct

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

lemma Module.exists_isPrincipal_quotient_of_finite  :
    ∃ N : Submodule R M, N ≠ ⊤ ∧ Submodule.IsPrincipal (⊤ : Submodule R (M ⧸ N)) := by
  obtain ⟨n, f, hf⟩ := @Module.Finite.exists_fin R M _ _ _ _
  let s := { m : ℕ | Submodule.span R (f '' (Fin.val ⁻¹' (Set.Iio m))) ≠ ⊤ }
  have hns : ∀ x ∈ s, x < n := by
    refine fun x hx ↦ lt_iff_not_le.mpr fun e ↦ ?_
    have : (Fin.val ⁻¹' Set.Iio x : Set (Fin n)) = Set.univ := by ext y; simpa using y.2.trans_le e
    simp [s, this, hf] at hx
  have hs₁ : s.Nonempty := ⟨0, by simp [s, show Set.Iio 0 = ∅ by ext; simp]⟩
  have hs₂ : BddAbove s := ⟨n, fun x hx ↦ (hns x hx).le⟩
  have hs := Nat.sSup_mem hs₁ hs₂
  refine ⟨_, hs, ⟨⟨Submodule.mkQ _ (f ⟨_, hns _ hs⟩), ?_⟩⟩⟩
  have := not_not.mp (not_mem_of_csSup_lt (Order.lt_succ _) hs₂)
  rw [← Set.image_singleton, ← Submodule.map_span,
    ← (Submodule.comap_injective_of_surjective (Submodule.mkQ_surjective _)).eq_iff,
    Submodule.comap_map_eq, Submodule.ker_mkQ, Submodule.comap_top, ← this, ← Submodule.span_union,
    Order.Iio_succ_eq_insert (sSup s), ← Set.union_singleton, Set.preimage_union, Set.image_union,
    ← @Set.image_singleton _ _ f, Set.union_comm]
  congr!
  ext
  simp [Fin.ext_iff]

lemma Module.exists_surjective_quotient_of_finite :
    ∃ (I : Ideal R) (f : M →ₗ[R] R ⧸ I), I ≠ ⊤ ∧ Function.Surjective f := by
  obtain ⟨N, hN, ⟨x, hx⟩⟩ := Module.exists_isPrincipal_quotient_of_finite R M
  let f := (LinearMap.toSpanSingleton R _ x).quotKerEquivOfSurjective
    (by rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, hx])
  refine ⟨_, f.symm.toLinearMap.comp N.mkQ, fun e ↦ ?_, f.symm.surjective.comp N.mkQ_surjective⟩
  obtain rfl : x = 0 := by simpa using LinearMap.congr_fun (LinearMap.ker_eq_top.mp e) 1
  rw [ne_eq, ← Submodule.subsingleton_quotient_iff_eq_top, ← not_nontrivial_iff_subsingleton,
    not_not] at hN
  simp at hx

open TensorProduct
instance : Nontrivial (M ⊗[R] M) := by
  obtain ⟨I, ϕ, hI, hϕ⟩ := Module.exists_surjective_quotient_of_finite R M
  let ψ : M ⊗[R] M →ₗ[R] R ⧸ I :=
    (LinearMap.mul' R (R ⧸ I)).comp (TensorProduct.map ϕ ϕ)
  have : Nontrivial (R ⧸ I) := by
    rwa [← not_subsingleton_iff_nontrivial, Submodule.subsingleton_quotient_iff_eq_top]
  have : Function.Surjective ψ := by
    intro x; obtain ⟨x, rfl⟩ := hϕ x; obtain ⟨y, hy⟩ := hϕ 1; exact ⟨x ⊗ₜ y, by simp [ψ, hy]⟩
  exact this.nontrivial

end NontrivialTensorProduct
