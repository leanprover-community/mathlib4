/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Algebras which are commutative ring epimorphisms
-/

@[expose] public section

noncomputable section
open Function TensorProduct

namespace Algebra

section Semiring

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

/-- A commutative `R`-algebra `A` is epi, if the multiplication map `A ⊗[R] A → A` is injective. -/
protected class IsEpi : Prop where
  injective_lift_mul : Injective <| lift <| LinearMap.mul R A

/-- See also `CommRingCat.epi_iff_epi`. -/
lemma isEpi_iff_forall_one_tmul_eq :
    Algebra.IsEpi R A ↔ ∀ a : A, 1 ⊗ₜ[R] a = a ⊗ₜ[R] 1 := by
  refine ⟨fun h a ↦ IsEpi.injective_lift_mul <| by simp, fun h ↦ ⟨fun x y hxy ↦ ?_⟩⟩
  have h' (x : A ⊗[R] A) : ∃ a : A, x = a ⊗ₜ 1 := by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul u v =>
      use u * v
      calc u ⊗ₜ[R] v = u ⊗ₜ[R] 1 * 1 ⊗ₜ[R] v := by simp
                   _ = u ⊗ₜ[R] 1 * v ⊗ₜ[R] 1 := by rw [h]
                   _ = (u * v) ⊗ₜ[R] 1 := by simp
    | add u v hu hv =>
      obtain ⟨u, rfl⟩ := hu
      obtain ⟨v, rfl⟩ := hv
      exact ⟨u  + v, by simp [add_tmul]⟩
  obtain ⟨a, rfl⟩ := h' x
  obtain ⟨b, rfl⟩ := h' y
  aesop

/-- See also `Algebra.isEpi_iff_surjective_algebraMap_of_finite`. -/
lemma isEpi_of_surjective_algebraMap (h : Surjective (algebraMap R A)) :
    Algebra.IsEpi R A := by
  refine (isEpi_iff_forall_one_tmul_eq R A).mpr fun a ↦ ?_
  obtain ⟨r, rfl⟩ := h a
  rw [algebraMap_eq_smul_one, smul_tmul]

end Semiring

-- TODO Generalise to any localization
instance (R A : Type*) [CommRing R] [IsDomain R] [Field A] [Algebra R A] [IsFractionRing R A] :
    Algebra.IsEpi R A := by
  refine (isEpi_iff_forall_one_tmul_eq R A).mpr fun x ↦ ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  set f := algebraMap R A with hf
  replace hb : f b ≠ 0 := by aesop
  calc 1 ⊗ₜ[R] (f a / f b)
       = 1 ⊗ₜ[R] (a • (1 / f b)) := by rw [← smul_div_assoc, algebraMap_eq_smul_one a]
     _ = f a ⊗ₜ[R] (1 / f b) := by rw [← smul_tmul, algebraMap_eq_smul_one a]
     _ = (b • (f a / f b)) ⊗ₜ[R] (1 / f b) := by rw [smul_def, mul_div_cancel₀ _ hb]
     _ = (f a / f b) ⊗ₜ[R] (b • (1 / f b)) := by rw [smul_tmul]
     _ = (f a / f b) ⊗ₜ[R] 1 := by rw [smul_def, mul_div_cancel₀ _ hb]

section Ring

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

lemma isEpi_iff_surjective_algebraMap_of_finite [Module.Finite R A] :
    Algebra.IsEpi R A ↔ Surjective (algebraMap R A) := by
  refine ⟨fun h ↦ ?_, isEpi_of_surjective_algebraMap R A⟩
  let R' := (Algebra.linearMap R A).range
  rcases subsingleton_or_nontrivial (A ⧸ R') with h | _
  · rwa [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top] at h
  have : Subsingleton ((A ⧸ R') ⊗[R] (A ⧸ R')) := by
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
        · simp [(isEpi_iff_forall_one_tmul_eq R A).mp]
        · simp
      have : R'.mkQ 1 = 0 := (Submodule.Quotient.mk_eq_zero R').mpr ⟨1, map_one (algebraMap R A)⟩
      rw [← map_tmul R'.mkQ R'.mkQ, ← hs, map_tmul, this, zero_tmul]
  cases false_of_nontrivial_of_subsingleton ((A ⧸ R') ⊗[R] (A ⧸ R'))

@[deprecated (since := "2026-01-13")]
alias _root_.RingHom.surjective_of_tmul_eq_tmul_of_finite :=
  isEpi_iff_surjective_algebraMap_of_finite

end Ring

section CommSemiring

variable (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] [Algebra.IsEpi R A]

variable {A} in
lemma tmul_comm (a b : A) :
    a ⊗ₜ[R] b = b ⊗ₜ[R] a := by
  have (a b : A) := calc a ⊗ₜ[R] b
      = a • (1 ⊗ₜ[R] b) := by rw [tmul_eq_smul_one_tmul]
    _ = a • (b ⊗ₜ[R] 1) := by rw [(isEpi_iff_forall_one_tmul_eq R A).mp inferInstance b]
    _ = a • (b • (1 ⊗ₜ[R] 1)) := by rw [tmul_eq_smul_one_tmul]
  rw [this a b, this b a, smul_comm]

section Module

variable (M : Type*) [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- If an `R`-algebra `A` is epi, then the scalar multiplication `A ⊗[R] M → M` is injective, for
any `A`-module `M`. -/
lemma injective_lift_lsmul :
    Injective (lift <| LinearMap.restrictScalars₁₂ R R (LinearMap.lsmul A M)) := by
  /- Morally the proof is to recognise that we can construct the map `A ⊗[R] M → M` as a
  composition of (`A`-linear) equivalences:
  ```
  A ⊗[R] M ≃  A ⊗[R] (A ⊗[A] M)
           ≃ (A ⊗[R] A) ⊗[A] M
           ≃ A ⊗[A] M
           ≃ M
  ```
  However the second equivalence above requires a version of heterogeneous tensor product
  associativity which is problematic in Mathlib because `TensorProduct.leftModule` prioritises the
  left factor in any tensor product. We therefore formalise a slightly lower level proof below. -/
  suffices ∀ (a : A) (m : M), 1 ⊗ₜ[R] (a • m) = a ⊗ₜ[R] m by
    let f : M →ₗ[R] A ⊗[R] M :=
      { toFun m := 1 ⊗ₜ m
        map_add' m n := tmul_add _ _ _
        map_smul' r m := tmul_smul _ _ _ }
    have aux : f ∘ₗ (lift <| LinearMap.restrictScalars₁₂ R R (LinearMap.lsmul A M)) = .id := by
      ext a m; simpa using this a m
    exact HasLeftInverse.injective ⟨f, fun x ↦ congr($aux x)⟩
  intro a m
  let f : A ⊗[R] A →ₗ[R] A ⊗[R] M := lift
    { toFun x :=
      { toFun y := x ⊗ₜ (y • m)
        map_add' := by simp [add_smul, tmul_add]
        map_smul' := by simp }
      map_add' := by intros; ext; simp [add_tmul]
      map_smul' := by intros; ext; simp [smul_tmul'] }
  simpa [f] using congr_arg f (tmul_comm R 1 a)

/-- A heterogeneous variant of `TensorProduct.lid` when `R → A` is epi. -/
def _root_.TensorProduct.lid' : A ⊗[R] M ≃ₗ[A] M :=
  .ofBijective
    (AlgebraTensorModule.lift <| LinearMap.restrictScalarsₗ R A M M A ∘ₗ LinearMap.lsmul A M)
    ⟨injective_lift_lsmul R A M, fun m ↦ ⟨1 ⊗ₜ m, by simp⟩⟩

@[simp] lemma _root_.TensorProduct.lid'_apply_tmul (a : A) (m : M) :
    TensorProduct.lid' R A M (a ⊗ₜ m) = a • m :=
  rfl

@[simp] lemma _root_.TensorProduct.lid'_symm_apply (m : M) :
    (TensorProduct.lid' R A M).symm m = 1 ⊗ₜ m :=
  (TensorProduct.lid' R A M).injective <| by simp

end Module

end CommSemiring

end Algebra
