/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser
-/
import Mathlib.RingTheory.MvPolynomial.Homogeneous.Basic
import Mathlib.Algebra.Polynomial.Roots.Card

/-!
#

-/


namespace MvPolynomial

variable {σ : Type*} {τ : Type*} {R : Type*} {S : Type*}

namespace IsHomogeneous

section IsDomain

variable {R σ : Type*} [CommRing R] [IsDomain R] {F G : MvPolynomial σ R} {n : ℕ}

open Cardinal Polynomial

private
lemma exists_eval_ne_zero_of_totalDegree_le_card_aux {N : ℕ} {F : MvPolynomial (Fin N) R} {n : ℕ}
    (hF : F.IsHomogeneous n) (hF₀ : F ≠ 0) (hnR : n ≤ #R) :
    ∃ r, eval r F ≠ 0 := by
  induction N generalizing n with
  | zero =>
    use 0
    contrapose! hF₀
    ext d
    simpa only [Subsingleton.elim d 0, eval_zero, coeff_zero] using hF₀
  | succ N IH =>
    have hdeg : natDegree (finSuccEquiv R N F) < n + 1 := by
      linarith [natDegree_finSuccEquiv F, degreeOf_le_totalDegree F 0, hF.totalDegree hF₀]
    obtain ⟨i, hi⟩ : ∃ i : ℕ, (finSuccEquiv R N F).coeff i ≠ 0 := by
      contrapose! hF₀
      exact (finSuccEquiv _ _).injective <| Polynomial.ext <| by simpa using hF₀
    have hin : i ≤ n := by
      contrapose! hi
      exact coeff_eq_zero_of_natDegree_lt <| (Nat.le_of_lt_succ hdeg).trans_lt hi
    obtain hFn | hFn := ne_or_eq ((finSuccEquiv R N F).coeff n) 0
    · exact hF.exists_eval_ne_zero_of_coeff_finSuccEquiv_ne_zero_aux hFn
    have hin : i < n := hin.lt_or_eq.elim id <| by aesop
    obtain ⟨j, hj⟩ : ∃ j, i + (j + 1) = n := (Nat.exists_eq_add_of_lt hin).imp <| by intros; omega
    obtain ⟨r, hr⟩ : ∃ r, (eval r) (Polynomial.coeff ((finSuccEquiv R N) F) i) ≠ 0 :=
      IH (hF.finSuccEquiv_coeff_isHomogeneous _ _ hj) hi (.trans (by norm_cast; omega) hnR)
    set φ : R[X] := Polynomial.map (eval r) (finSuccEquiv _ _ F) with hφ
    have hφ₀ : φ ≠ 0 := fun hφ₀ ↦ hr <| by
      rw [← coeff_eval_eq_eval_coeff, ← hφ, hφ₀, Polynomial.coeff_zero]
    have hφR : φ.natDegree < #R := by
      refine lt_of_lt_of_le ?_ hnR
      norm_cast
      refine lt_of_le_of_lt (natDegree_map_le _ _) ?_
      suffices (finSuccEquiv _ _ F).natDegree ≠ n by omega
      rintro rfl
      refine leadingCoeff_ne_zero.mpr ?_ hFn
      simpa using (finSuccEquiv R N).injective.ne hF₀
    obtain ⟨r₀, hr₀⟩ : ∃ r₀, Polynomial.eval r₀ φ ≠ 0 :=
      φ.exists_eval_ne_zero_of_natDegree_lt_card hφ₀ hφR
    use Fin.cons r₀ r
    rwa [eval_eq_eval_mv_eval']

/-- See `MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero`
for a version that assumes `Infinite R`. -/
lemma eq_zero_of_forall_eval_eq_zero_of_le_card
    (hF : F.IsHomogeneous n) (h : ∀ r : σ → R, eval r F = 0) (hnR : n ≤ #R) :
    F = 0 := by
  contrapose! h
  -- reduce to the case where σ is finite
  obtain ⟨k, f, hf, F, rfl⟩ := exists_fin_rename F
  have hF₀ : F ≠ 0 := by rintro rfl; simp at h
  have hF : F.IsHomogeneous n := by rwa [rename_isHomogeneous_iff hf] at hF
  obtain ⟨r, hr⟩ := exists_eval_ne_zero_of_totalDegree_le_card_aux hF hF₀ hnR
  obtain ⟨r, rfl⟩ := (Function.factorsThrough_iff _).mp <| (hf.factorsThrough r)
  use r
  rwa [eval_rename]

/-- See `MvPolynomial.IsHomogeneous.funext`
for a version that assumes `Infinite R`. -/
lemma funext_of_le_card (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous n)
    (h : ∀ r : σ → R, eval r F = eval r G) (hnR : n ≤ #R) :
    F = G := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_eval_eq_zero_of_le_card (hF.sub hG) _ hnR
  simpa [sub_eq_zero] using h

/-- See `MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero_of_le_card`
for a version that assumes `n ≤ #R`. -/
lemma eq_zero_of_forall_eval_eq_zero [Infinite R] {F : MvPolynomial σ R} {n : ℕ}
    (hF : F.IsHomogeneous n) (h : ∀ r : σ → R, eval r F = 0) : F = 0 := by
  apply eq_zero_of_forall_eval_eq_zero_of_le_card hF h
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

/-- See `MvPolynomial.IsHomogeneous.funext_of_le_card`
for a version that assumes `n ≤ #R`. -/
lemma funext [Infinite R] {F G : MvPolynomial σ R} {n : ℕ}
    (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous n)
    (h : ∀ r : σ → R, eval r F = eval r G) : F = G := by
  apply funext_of_le_card hF hG h
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

end IsDomain

end IsHomogeneous

end MvPolynomial
