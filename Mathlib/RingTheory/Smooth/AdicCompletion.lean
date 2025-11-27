/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Smooth.Basic

/-!
# Formally smooth algebras and adic completion

Let `S` be an `R`-algebra and `I` an ideal of `S`. In this file we show that if `S ⧸ I` is
formally smooth over `R`, the canonical projection `AdicCompletion I S →ₐ[R] S ⧸ I`
(`AdicCompletion.kerProj`) has a section.

Instead of working with an ideal `I` and `S ⧸ I`, we work with a surjective algebra map `S →ₐ[R] A`.

This is used in the proof that a smooth algebra over a Noetherian ring is flat
(see `Mathlib.RingTheory.Smooth.Flat`).
-/

@[expose] public section

universe u v

namespace Algebra.FormallySmooth

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {S : Type*} [CommRing S] [Algebra R S]
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

/-- If `A` is formally smooth over `R`, the projection from the adic completion of
`S` at the kernel of `f : S →ₐ[R] A` has a section. -/
lemma exists_kerProj_comp_eq_id : ∃ (g : A →ₐ[R] AdicCompletion (ker f) S),
    (AdicCompletion.kerProj hf).comp g = AlgHom.id R A :=
  ⟨sectionAdicCompletion f hf, kerProj_comp_sectionAdicCompletion f hf⟩

end FormallySmooth

end Algebra
