/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Bilinear
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Finiteness of the tensor product of (sub)modules

In this file we show that the supremum of two subalgebras that are finitely generated as modules,
is again finitely generated.

-/

open Function (Surjective)
open Finsupp

namespace Submodule

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
  [AddCommMonoid N] [Module R M] [Module R N] {I : Submodule R N}

open TensorProduct LinearMap
/-- Every `x : N ⊗ M` is the image of some `y : J ⊗ M`, where `J` is a finitely generated
submodule of `N`, under the tensor product of the inclusion `J → N` and the identity `M → M`. -/
theorem exists_fg_le_eq_rTensor_subtype (x : N ⊗ M) :
    ∃ (J : Submodule R N) (_ : J.FG) (y : J ⊗ M), x = rTensor M J.subtype y := by
  induction x with
  | zero => exact ⟨⊥, fg_bot, 0, rfl⟩
  | tmul i m => exact ⟨R ∙ i, fg_span_singleton i, ⟨i, mem_span_singleton_self _⟩ ⊗ₜ[R] m, rfl⟩
  | add x₁ x₂ ihx₁ ihx₂ =>
    obtain ⟨J₁, fg₁, y₁, rfl⟩ := ihx₁
    obtain ⟨J₂, fg₂, y₂, rfl⟩ := ihx₂
    refine ⟨J₁ ⊔ J₂, fg₁.sup fg₂,
      rTensor M (J₁.inclusion le_sup_left) y₁ + rTensor M (J₂.inclusion le_sup_right) y₂, ?_⟩
    rw [map_add, ← rTensor_comp_apply, ← rTensor_comp_apply]
    rfl

theorem exists_fg_le_subset_range_rTensor_subtype (s : Set (N ⊗[R] M)) (hs : s.Finite) :
    ∃ (J : Submodule R N) (_ : J.FG), s ⊆ LinearMap.range (rTensor M J.subtype) := by
  choose J fg y eq using exists_fg_le_eq_rTensor_subtype (R := R) (M := M) (N := N)
  rw [← Set.finite_coe_iff] at hs
  refine ⟨⨆ x : s, J x, fg_iSup _ fun _ ↦ fg _, fun x hx ↦
    ⟨rTensor M (inclusion <| le_iSup _ ⟨x, hx⟩) (y x), .trans ?_ (eq x).symm⟩⟩
  rw [← comp_apply, ← rTensor_comp]; rfl

open TensorProduct LinearMap
/-- Every `x : I ⊗ M` is the image of some `y : J ⊗ M`, where `J ≤ I` is finitely generated,
under the tensor product of `J.inclusion ‹J ≤ I› : J → I` and the identity `M → M`. -/
theorem exists_fg_le_eq_rTensor_inclusion (x : I ⊗ M) :
    ∃ (J : Submodule R N) (_ : J.FG) (hle : J ≤ I) (y : J ⊗ M),
      x = rTensor M (J.inclusion hle) y := by
  obtain ⟨J, fg, y, rfl⟩ := exists_fg_le_eq_rTensor_subtype x
  refine ⟨J.map I.subtype, fg.map _, I.map_subtype_le J, rTensor M (I.subtype.submoduleMap J) y, ?_⟩
  rw [← LinearMap.rTensor_comp_apply]; rfl

theorem exists_fg_le_subset_range_rTensor_inclusion (s : Set (I ⊗[R] M)) (hs : s.Finite) :
    ∃ (J : Submodule R N) (_ : J.FG) (hle : J ≤ I),
      s ⊆ LinearMap.range (rTensor M (J.inclusion hle)) := by
  choose J fg hle y eq using exists_fg_le_eq_rTensor_inclusion (M := M) (I := I)
  rw [← Set.finite_coe_iff] at hs
  refine ⟨⨆ x : s, J x, fg_iSup _ fun _ ↦ fg _, iSup_le fun _ ↦ hle _, fun x hx ↦
    ⟨rTensor M (inclusion <| le_iSup _ ⟨x, hx⟩) (y x), .trans ?_ (eq x).symm⟩⟩
  rw [← comp_apply, ← rTensor_comp]; rfl

end Submodule

section ModuleAndAlgebra

variable (R A B M N : Type*)

instance Module.Finite.base_change [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]
    [Module R M] [h : Module.Finite R M] : Module.Finite A (TensorProduct R A M) := by
  classical
    obtain ⟨s, hs⟩ := h.fg_top
    refine ⟨⟨s.image (TensorProduct.mk R A M 1), eq_top_iff.mpr ?_⟩⟩
    rintro x -
    induction x with
    | zero => exact zero_mem _
    | tmul x y =>
      rw [Finset.coe_image, ← Submodule.span_span_of_tower R, Submodule.span_image, hs,
        Submodule.map_top, LinearMap.coe_range, ← mul_one x, ← smul_eq_mul,
        ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ x (Submodule.subset_span <| Set.mem_range_self y)
    | add x y hx hy => exact Submodule.add_mem _ hx hy

instance Module.Finite.tensorProduct [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [hM : Module.Finite R M] [hN : Module.Finite R N] :
    Module.Finite R (TensorProduct R M N) where
  fg_top := (TensorProduct.map₂_mk_top_top_eq_top R M N).subst (hM.fg_top.map₂ _ hN.fg_top)

end ModuleAndAlgebra

section NontrivialTensorProduct

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

lemma Module.exists_isPrincipal_quotient_of_finite :
    ∃ N : Submodule R M, N ≠ ⊤ ∧ Submodule.IsPrincipal (⊤ : Submodule R (M ⧸ N)) := by
  obtain ⟨n, f, hf⟩ := @Module.Finite.exists_fin R M _ _ _ _
  let s := { m : ℕ | Submodule.span R (f '' (Fin.val ⁻¹' (Set.Iio m))) ≠ ⊤ }
  have hns : ∀ x ∈ s, x < n := by
    refine fun x hx ↦ lt_iff_not_ge.mpr fun e ↦ ?_
    have : (Fin.val ⁻¹' Set.Iio x : Set (Fin n)) = Set.univ := by ext y; simpa using y.2.trans_le e
    simp [s, this, hf] at hx
  have hs₁ : s.Nonempty := ⟨0, by simp [s]⟩
  have hs₂ : BddAbove s := ⟨n, fun x hx ↦ (hns x hx).le⟩
  have hs := Nat.sSup_mem hs₁ hs₂
  refine ⟨_, hs, ⟨⟨Submodule.mkQ _ (f ⟨_, hns _ hs⟩), ?_⟩⟩⟩
  have := not_not.mp (notMem_of_csSup_lt (Order.lt_succ _) hs₂)
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

theorem Subalgebra.finite_sup {K L : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L]
    (E1 E2 : Subalgebra K L) [Module.Finite K E1] [Module.Finite K E2] :
    Module.Finite K ↥(E1 ⊔ E2) := by
  rw [← E1.range_val, ← E2.range_val, ← Algebra.TensorProduct.productMap_range]
  exact Module.Finite.range (Algebra.TensorProduct.productMap E1.val E2.val).toLinearMap

open TensorProduct in
lemma RingHom.surjective_of_tmul_eq_tmul_of_finite {R S}
    [CommRing R] [Ring S] [Algebra R S] [Module.Finite R S]
    (h₁ : ∀ s : S, s ⊗ₜ[R] 1 = 1 ⊗ₜ s) : Function.Surjective (algebraMap R S) := by
  let R' := LinearMap.range (Algebra.ofId R S).toLinearMap
  rcases subsingleton_or_nontrivial (S ⧸ R') with h | _
  · rwa [Submodule.subsingleton_quotient_iff_eq_top, LinearMap.range_eq_top] at h
  have : Subsingleton ((S ⧸ R') ⊗[R] (S ⧸ R')) := by
    refine subsingleton_of_forall_eq 0 fun y ↦ ?_
    induction y with
    | zero => rfl
    | add a b e₁ e₂ => rwa [e₁, zero_add]
    | tmul x y =>
      obtain ⟨x, rfl⟩ := R'.mkQ_surjective x
      obtain ⟨y, rfl⟩ := R'.mkQ_surjective y
      obtain ⟨s, hs⟩ : ∃ s, 1 ⊗ₜ[R] s = x ⊗ₜ[R] y := by
        use x * y
        trans x ⊗ₜ 1 * 1 ⊗ₜ y
        · simp [h₁]
        · simp
      have : R'.mkQ 1 = 0 := (Submodule.Quotient.mk_eq_zero R').mpr ⟨1, map_one (algebraMap R S)⟩
      rw [← map_tmul R'.mkQ R'.mkQ, ← hs, map_tmul, this, zero_tmul]
  cases false_of_nontrivial_of_subsingleton ((S ⧸ R') ⊗[R] (S ⧸ R'))
