/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Smooth.Basic

/-!
# Smooth algebras are flat

Let `A` be a smooth `R`-algebra. In this file we show that then `A` is `R`-flat.
The proof proceeds in two steps:

1. If `R` is Noetherian, let `R[X₁, ..., Xₙ] →ₐ[R] A` be surjective with kernel `I`. By
  formal smoothness we construct a section `A →ₐ[R] AdicCompletion I R[X₁, ..., Xₙ]`
  of the canonical map `AdicCompletion I R[X₁, ..., Xₙ] →ₐ[R] R[X₁, ..., Xₙ] ⧸ I ≃ₐ[R] A`.
  Since `R` is Noetherian, `AdicCompletion I R` is `R`-flat so `A` is a retract
  of a flat `R`-module and hence flat.
2. (TODO @chrisflav): In the general case, we choose a model of `A` over a finitely generated
  `ℤ`-subalgebra of `R` and apply 1.


## References

- [Conde-Lago, A short proof of smooth implies flat][condelago2016shortproofsmoothimplies]
-/

@[expose] public section

universe u v

namespace Algebra

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

namespace FormallySmooth

variable {R A} {S : Type*} [CommRing S] [Algebra R S]
variable {ι : Type*} (f : S →ₐ[R] A) (hf : Function.Surjective f)

open RingHom

variable [FormallySmooth R A]

/--
(Implementation): Lift `A →ₐ[R] S ⧸ I` inductively to `A →ₐ[R] S ⧸ I ^ m` using formal
smoothness.
Note that, since `B ≃ₐ[A] R ⧸ I ≃ₐ[A] R ⧸ (I ^ m) ⧸ (I ⧸ (I ^ m))`, we could also
lift this directly, but then we don't have compatibility with the transition maps.
-/
noncomputable def sectionAdicCompletionAux : (m : ℕ) → A →ₐ[R] S ⧸ (ker f ^ m)
  | 0 =>
    haveI : Subsingleton (S ⧸ ker f ^ 0) := by simp [Ideal.Quotient.subsingleton_iff]
    default
  | 1 =>
    (Ideal.quotientKerAlgEquivOfSurjective hf).symm.trans
      (Ideal.quotientEquivAlgOfEq R (by simp)) |>.toAlgHom
  | m + 2 =>
    letI T := S ⧸ ker f ^ (m + 1 + 1)
    letI J : Ideal T := (ker f ^ (m + 1)).map (Ideal.Quotient.mkₐ _ (ker f ^ (m + 1 + 1)))
    letI q : A →ₐ[R] T ⧸ J :=
      (DoubleQuot.quotQuotEquivQuotOfLEₐ R
        (Ideal.pow_le_pow_right (I := ker f) (m + 1).le_succ)).symm.toAlgHom.comp
      (sectionAdicCompletionAux (m + 1))
    haveI : J ^ (m + 1 + 1) = 0 := by
      rw [← Ideal.map_pow, Submodule.zero_eq_bot, ← pow_mul]
      exact eq_bot_mono (Ideal.map_mono <| Ideal.pow_le_pow_right (by simp))
        (Ideal.map_quotient_self _)
    FormallySmooth.lift J ⟨m + 1 + 1, this⟩ q

@[simp]
lemma sectionAdicCompletionAux_one (p : S) : sectionAdicCompletionAux f hf 1 (f p) = p := by
  simp [sectionAdicCompletionAux]

@[simp]
lemma factorₐ_comp_sectionAdicCompletionAux (m : ℕ) :
    (Ideal.Quotient.factorₐ _ (Ideal.pow_le_pow_right m.le_succ)).comp
      (sectionAdicCompletionAux f hf (m + 1)) = sectionAdicCompletionAux f hf m := by
  cases m with
  | zero =>
    ext
    apply eq_of_zero_eq_one
    simp [subsingleton_iff_zero_eq_one, Ideal.Quotient.subsingleton_iff]
  | succ m =>
    rw [sectionAdicCompletionAux, ← DoubleQuot.quotQuotEquivQuotOfLEₐ_comp_mkₐ]
    ext
    simp

@[simp]
lemma factorₐ_comp_sectionAdicCompletionAux_of_le {m n : ℕ} (hn : m ≤ n) :
    (Ideal.Quotient.factorₐ _ (Ideal.pow_le_pow_right hn)).comp (sectionAdicCompletionAux f hf n) =
      sectionAdicCompletionAux f hf m := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [← Ideal.Quotient.factorₐ_comp _
      (Ideal.pow_le_pow_right n.le_succ) (Ideal.pow_le_pow_right hmn), AlgHom.comp_assoc]
    simpa

/-- If `A` is formally smooth over `R`, any surjective map `S →ₐ[R] A` admits a section
to the projection `AdicCompletion.kerProj`. -/
noncomputable def sectionAdicCompletion : A →ₐ[R] AdicCompletion (ker f) S :=
  AdicCompletion.liftAlgHom (ker f) (sectionAdicCompletionAux f hf)
    (factorₐ_comp_sectionAdicCompletionAux_of_le f hf)

@[simp]
lemma evalₐ_sectionAdicCompletion_apply (p : S) :
    AdicCompletion.evalₐ (ker f) 1 (sectionAdicCompletion f hf (f p)) = p := by
  simp [sectionAdicCompletion]

@[simp]
lemma kerProj_sectionAdicCompletion (x : A) :
    AdicCompletion.kerProj hf (sectionAdicCompletion f hf x) = x := by
  obtain ⟨x, rfl⟩ := hf x
  simp [AdicCompletion.kerProj]

/-- The constructed section is indeed a section for `AdicCompletion.kerProj`. -/
lemma kerProj_comp_sectionAdicCompletion :
    (AdicCompletion.kerProj hf).comp (sectionAdicCompletion f hf) = AlgHom.id R A :=
  AlgHom.ext fun x ↦ kerProj_sectionAdicCompletion _ _ x

include hf in
lemma flat_of_algHom_of_isNoetherianRing [Module.Flat R S] [IsNoetherianRing S] :
    Module.Flat R A := by
  have : Module.Flat R (AdicCompletion (ker f) S) := .trans _ S _
  refine Module.Flat.of_retract (sectionAdicCompletion f hf).toLinearMap
    (AdicCompletion.kerProj hf).toLinearMap ?_
  ext
  simp

end FormallySmooth

/-- If `A` is `R`-smooth and `R` is Noetherian, then `A` is `R`-flat. -/
instance Smooth.flat_of_isNoetherianRing [IsNoetherianRing R] [Algebra.Smooth R A] :
    Module.Flat R A := by
  obtain ⟨k, f, hf⟩ := (FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  exact FormallySmooth.flat_of_algHom_of_isNoetherianRing f hf

end Algebra
