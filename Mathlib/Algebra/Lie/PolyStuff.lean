import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.MvPolynomial.Equiv
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.RingTheory.MvPolynomial.Homogeneous

open BigOperators

variable {R σ : Type*} [CommRing R]

-- Mathlib.Data.Finsupp.Fin
lemma Finsupp.cons_support {n : ℕ} {M : Type*} [Zero M] (y : M) (s : Fin n →₀ M) :
    (s.cons y).support ⊆ insert 0 (Finset.map (Fin.succEmb n).toEmbedding s.support) := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_map, mem_support_iff, ne_eq,
    RelEmbedding.coe_toEmbedding, Fin.val_succEmb]
  apply (Fin.eq_zero_or_eq_succ i).imp id (Exists.imp _)
  rintro i rfl
  simpa [Finsupp.mem_support_iff] using hi

namespace MvPolynomial -- move this

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]
variable (f : R →+* S) (k : σ → τ) (g : τ → R) (p : MvPolynomial σ R)

-- move later??
lemma IsHomogeneous.finSuccEquiv_coeff_isHomogeneous {N : ℕ}
    {φ : MvPolynomial (Fin (N+1)) R} {n : ℕ} (hφ : φ.IsHomogeneous n) (i j : ℕ) (h : i + j = n) :
    ((finSuccEquiv _ _ φ).coeff i).IsHomogeneous j := by
  intro d hd
  rw [finSuccEquiv_coeff_coeff] at hd
  have aux : 0 ∉ Finset.map (Fin.succEmb N).toEmbedding d.support := by simp [Fin.succ_ne_zero]
  simpa [Finset.sum_subset_zero_on_sdiff (g := d.cons i)
    (d.cons_support i) (by simp) (fun _ _ ↦ rfl), Finset.sum_insert aux, ← h] using hφ hd

end MvPolynomial

namespace MvPolynomial.IsHomogeneous

open Polynomial in
private
lemma exists_eval_ne_zero_of_totalDegree_le_card_aux₀
    {N : ℕ} {F : MvPolynomial (Fin (Nat.succ N)) R} {n : ℕ} (hF : IsHomogeneous F n)
    (hdeg : natDegree ((finSuccEquiv R N) F) < n + 1) (hFn : ((finSuccEquiv R N) F).coeff n ≠ 0) :
    ∃ r, (eval r) F ≠ 0 := by
  use Fin.cons 1 0
  have aux : ∀ i ∈ Finset.range n, constantCoeff ((finSuccEquiv R N F).coeff i) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    apply (hF.finSuccEquiv_coeff_isHomogeneous i (n-i) (by omega)).coeff_eq_zero
    simp only [Finsupp.support_zero, Finsupp.coe_zero, Pi.zero_apply, Finset.sum_const_zero]
    omega
  simp_rw [eval_eq_eval_mv_eval', eval_one_map, Polynomial.eval_eq_sum_range' hdeg,
    eval_zero, one_pow, mul_one, map_sum, Finset.sum_range_succ, Finset.sum_eq_zero aux, zero_add]
  contrapose! hFn
  ext d
  rw [coeff_zero]
  obtain rfl | hd := eq_or_ne d 0
  · apply hFn
  · contrapose! hd
    ext i
    rw [Finsupp.coe_zero, Pi.zero_apply]
    by_cases hi : i ∈ d.support
    · have := hF.finSuccEquiv_coeff_isHomogeneous n 0 (add_zero _) hd
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ zero_le')] at this
      exact this i hi
    · simpa using hi

variable {σ : Type*} [IsDomain R] {F : MvPolynomial σ R} {n : ℕ}

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
    · exact hF.exists_eval_ne_zero_of_totalDegree_le_card_aux₀ hdeg hFn
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

open Cardinal in
lemma exists_eval_ne_zero_of_totalDegree_le_card
    (hF : F.IsHomogeneous n) (hF₀ : F ≠ 0) (h : n ≤ #R) :
    ∃ r : σ → R, eval r F ≠ 0 := by
  -- reduce to the case where σ is finite
  obtain ⟨k, f, hf, F, rfl⟩ := exists_fin_rename F
  have hF₀ : F ≠ 0 := by rintro rfl; simp at hF₀
  have hF : F.IsHomogeneous n := by rwa [rename_isHomogeneous_iff hf] at hF
  obtain ⟨r, hr⟩ := exists_eval_ne_zero_of_totalDegree_le_card_aux hF hF₀ h
  obtain ⟨r, rfl⟩ := (Function.factorsThrough_iff _).mp <| (hf.factorsThrough r)
  use r
  rwa [eval_rename]

open Cardinal in
/-- See `MvPolynomial.IsHomogeneous.funext` for a version that assumes `Infinite R`. -/
lemma funext_of_le_card (hF : F.IsHomogeneous n) (hF₀ : ∀ r : σ → R, eval r F = 0) (h : n ≤ #R) :
    F = 0 := by
  contrapose! hF₀
  exact exists_eval_ne_zero_of_totalDegree_le_card hF hF₀ h

/-- See `MvPolynomial.IsHomogeneous.funext_of_le_card` for a version that assumes `n ≤ #R`. -/
lemma funext [Infinite R] {F : MvPolynomial σ R} {n : ℕ}
    (hF : F.IsHomogeneous n) (hF₀ : ∀ r : σ → R, eval r F = 0) : F = 0 := by
  apply funext_of_le_card hF hF₀
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

end MvPolynomial.IsHomogeneous
