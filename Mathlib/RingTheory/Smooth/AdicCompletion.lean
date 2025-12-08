/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Smooth.Basic

/-!
# Formally smooth algebras and adic completion

Let `A` be a formally smooth `R`-algebra. Then any algebra map
`A →ₐ[R] S ⧸ I` lifts to an algebra map `A →ₐ[R] S` if `S` is `I`-adically complete.

This is used in the proof that a smooth algebra over a Noetherian ring is flat
(see `Mathlib.RingTheory.Smooth.Flat`).
-/

universe u v

namespace Algebra.FormallySmooth

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {S : Type*} [CommRing S] [Algebra R S] (I : Ideal S) (f : A →ₐ[R] S ⧸ I)

open RingHom

variable [FormallySmooth R A]

/--
(Implementation): Lift `A →ₐ[R] S ⧸ I` inductively to `A →ₐ[R] S ⧸ I ^ m` using formal
smoothness.
-/
noncomputable def liftAdicCompletionAux : (m : ℕ) → A →ₐ[R] S ⧸ (I ^ m)
  | 0 =>
    haveI : Subsingleton (S ⧸ I ^ 0) := by simp
    default
  | 1 => (Ideal.quotientEquivAlgOfEq R (show I = I ^ 1 by simp)).toAlgHom.comp f
  | m + 2 =>
    letI T := S ⧸ I ^ (m + 1 + 1)
    letI J : Ideal T := (I ^ (m + 1)).map (Ideal.Quotient.mkₐ R (I ^ (m + 1 + 1)))
    letI q : A →ₐ[R] T ⧸ J :=
      (DoubleQuot.quotQuotEquivQuotOfLEₐ R
        (Ideal.pow_le_pow_right (I := I) (m + 1).le_succ)).symm.toAlgHom.comp
      (liftAdicCompletionAux (m + 1))
    haveI : J ^ (m + 1 + 1) = 0 := by
      rw [← Ideal.map_pow, Submodule.zero_eq_bot, ← pow_mul]
      exact eq_bot_mono (Ideal.map_mono <| Ideal.pow_le_pow_right (by simp))
        (Ideal.map_quotient_self _)
    FormallySmooth.lift J ⟨m + 1 + 1, this⟩ q

@[simp]
lemma factorₐ_comp_liftAdicCompletionAux (m : ℕ) :
    (Ideal.Quotient.factorₐ _ (Ideal.pow_le_pow_right m.le_succ)).comp
      (liftAdicCompletionAux I f (m + 1)) = liftAdicCompletionAux I f m := by
  cases m with
  | zero =>
    ext
    apply eq_of_zero_eq_one
    simp [subsingleton_iff_zero_eq_one]
  | succ m =>
    rw [liftAdicCompletionAux, ← DoubleQuot.quotQuotEquivQuotOfLEₐ_comp_mkₐ]
    ext
    simp

@[simp]
lemma factorₐ_comp_liftAdicCompletionAux_of_le {m n : ℕ} (hn : m ≤ n) :
    (Ideal.Quotient.factorₐ _ (Ideal.pow_le_pow_right hn)).comp (liftAdicCompletionAux I f n) =
      liftAdicCompletionAux I f m := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [← Ideal.Quotient.factorₐ_comp _
      (Ideal.pow_le_pow_right n.le_succ) (Ideal.pow_le_pow_right hmn), AlgHom.comp_assoc]
    simpa

/-- If `A` is formally smooth over `R`, any map `A →ₐ[R] S ⧸ I` lifts
to `A →ₐ[R] AdicCompletion I S`. -/
public lemma exists_adicCompletionEvalOneₐ_comp_eq {I : Ideal S} (f : A →ₐ[R] S ⧸ I) :
    ∃ (g : A →ₐ[R] AdicCompletion I S),
      ((AdicCompletion.evalOneₐ I).restrictScalars R).comp g = f := by
  refine ⟨AdicCompletion.liftAlgHom I (liftAdicCompletionAux I f)
    (factorₐ_comp_liftAdicCompletionAux_of_le I f), ?_⟩
  ext
  simp [liftAdicCompletionAux]

/-- If `A` is formally smooth over `R`, any map `A →ₐ[R] S ⧸ I` lifts
to `A →ₐ[R] S` if `S` is `I`-adically complete.
See `Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq` for a version
about `AdicCompletion`. -/
public lemma exists_mkₐ_comp_eq_of_isAdicComplete {I : Ideal S} [IsAdicComplete I S]
    (f : A →ₐ[R] S ⧸ I) :
    ∃ (g : A →ₐ[R] S), (Ideal.Quotient.mkₐ _ _).comp g = f := by
  obtain ⟨g, hg⟩ := exists_adicCompletionEvalOneₐ_comp_eq f
  refine ⟨AlgHom.comp ((AdicCompletion.ofAlgEquiv I).symm.toAlgHom.restrictScalars R) g, ?_⟩
  ext x
  simpa using congr($hg x)

/-- If `A` is formally smooth over `R`, the projection from the adic completion of
`S` at the kernel of `f : S →ₐ[R] A` has a section. -/
public lemma exists_kerProj_comp_eq_id (f : S →ₐ[R] A) (hf : Function.Surjective f) :
    ∃ (g : A →ₐ[R] AdicCompletion (ker f) S),
    (AdicCompletion.kerProj hf).comp g = AlgHom.id R A := by
  obtain ⟨g, hg⟩ := exists_adicCompletionEvalOneₐ_comp_eq
    (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom
  use g
  ext x
  simpa using congr(Ideal.quotientKerAlgEquivOfSurjective hf ($hg x))

end FormallySmooth

end Algebra
