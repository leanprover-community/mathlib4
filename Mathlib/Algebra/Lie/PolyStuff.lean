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
    (φ : MvPolynomial (Fin (N+1)) R) (n : ℕ) (hφ : φ.IsHomogeneous n) (i j : ℕ) (h : i + j = n) :
    ((finSuccEquiv _ _ φ).coeff i).IsHomogeneous j := by
  intro d hd
  rw [finSuccEquiv_coeff_coeff] at hd
  have aux : 0 ∉ Finset.map (Fin.succEmb N).toEmbedding d.support := by
    simp [Fin.succ_ne_zero]
  simpa [Finset.sum_subset_zero_on_sdiff (g := d.cons i)
    (d.cons_support i) (by simp) (fun _ _ ↦ rfl), Finset.sum_insert aux, ← h] using hφ hd

end MvPolynomial

namespace MvPolynomial.IsHomogeneous

open Polynomial in
private
lemma exists_eval_ne_zero_of_totalDegree_le_card_aux₀
    (N : ℕ) (F : MvPolynomial (Fin (Nat.succ N)) R) (n : ℕ) (hF : IsHomogeneous F n)
    (aux : natDegree ((finSuccEquiv R N) F) < n + 1) (hFn : ((finSuccEquiv R N) F).coeff n ≠ 0) :
    ∃ r, (eval r) F ≠ 0 := by
  use Fin.cons 1 0
  rw [eval_eq_eval_mv_eval', eval_one_map, Polynomial.eval_eq_sum_range' aux]
  simp only [eval_zero, one_pow, mul_one, map_sum]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
  · contrapose! hFn
    have := hF.finSuccEquiv_coeff_isHomogeneous _ _ n 0 (add_zero _)
    ext d
    rw [coeff_zero]
    obtain rfl | hd := eq_or_ne d 0
    · apply hFn
    · contrapose! hd
      specialize this hd
      push_neg at this
      ext i
      rw [Finsupp.coe_zero, Pi.zero_apply]
      if hi : i ∈ d.support
      then
        rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ zero_le')] at this
        exact this i hi
      else
        simpa using hi
  · intro i hi
    rw [Finset.mem_range] at hi
    have := hF.finSuccEquiv_coeff_isHomogeneous _ _ i (n-i) (by omega)
    apply this.coeff_eq_zero
    simp only [Finsupp.support_zero, Finsupp.coe_zero, Pi.zero_apply, Finset.sum_const_zero]
    omega

open Cardinal Polynomial
private
lemma exists_eval_ne_zero_of_totalDegree_le_card_aux
    [IsDomain R] {N : ℕ} (F : MvPolynomial (Fin N) R) (n : ℕ)
    (hF₀ : F ≠ 0) (hF : F.IsHomogeneous n) (hnR : n ≤ #R) :
    ∃ r, eval r F ≠ 0 := by
  induction N generalizing n with
  | zero =>
    use 0
    contrapose! hF₀
    ext d
    obtain rfl : d = 0 := Subsingleton.elim _ _
    simpa only [eval_zero, coeff_zero] using hF₀
  | succ N IH =>
    have aux :=
      calc natDegree ((finSuccEquiv R N) F)
          = degreeOf 0 F  := natDegree_finSuccEquiv _
        _ ≤ F.totalDegree := degreeOf_le_totalDegree _ _
        _ = n             := hF.totalDegree hF₀
        _ < n + 1         := Nat.lt_succ_self n
    obtain ⟨i, hi⟩ : ∃ i : ℕ, (finSuccEquiv _ _ F).coeff i ≠ 0 := by
      contrapose! hF₀
      apply (finSuccEquiv _ _).injective
      apply Polynomial.ext
      simp only [hF₀, map_zero, Polynomial.coeff_zero, forall_const]
    have hin : i ≤ n := by
      contrapose! hi
      apply coeff_eq_zero_of_natDegree_lt
      omega
    by_cases hFn : ((finSuccEquiv R N) F).coeff n = 0
    swap
    · apply hF.exists_eval_ne_zero_of_totalDegree_le_card_aux₀ <;> assumption
    have hin : i < n := by
      contrapose! hi
      obtain rfl : i = n := le_antisymm hin hi
      exact hFn
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt hin
    rw [add_assoc] at hj
    specialize IH _ _ hi (hF.finSuccEquiv_coeff_isHomogeneous _ _ _ _ hj.symm) (le_trans _ hnR)
    · norm_cast; omega
    rcases IH with ⟨r, hr⟩
    let φ : R[X] := Polynomial.map (eval r) (finSuccEquiv _ _ F)
    have hφ₀ : φ ≠ 0 := by
      contrapose! hr with hφ₀
      dsimp only at hφ₀
      rw [← coeff_eval_eq_eval_coeff, hφ₀, Polynomial.coeff_zero]
    have hφR : φ.natDegree < #R := by
      refine lt_of_lt_of_le ?_ hnR
      norm_cast
      refine lt_of_le_of_lt (natDegree_map_le _ _) ?_
      suffices (finSuccEquiv _ _ F).natDegree ≠ n by omega
      rintro rfl
      refine leadingCoeff_ne_zero.mpr ?_ hFn
      simpa using (finSuccEquiv R N).injective.ne hF₀
    obtain ⟨r₀, hr₀⟩ := φ.exists_eval_ne_zero_of_natDegree_lt_card hφ₀ hφR
    use Fin.cons r₀ r
    rwa [eval_eq_eval_mv_eval']

open Cardinal in
lemma MvPolynomial.IsHomogeneous.exists_eval_ne_zero_of_totalDegree_le_card
    {σ : Type*} [IsDomain R]
    (F : MvPolynomial σ R) (n : ℕ)
    (hF₀ : F ≠ 0) (hF : F.IsHomogeneous n) (h : n ≤ #R) :
    ∃ r : σ → R, eval r F ≠ 0 := by
  -- reduce to the case where σ is finite
  obtain ⟨k, f, hf, F, rfl⟩ := exists_fin_rename F
  have hF₀ : F ≠ 0 := by rintro rfl; simp at hF₀
  have hF : F.IsHomogeneous n := by rwa [rename_isHomogeneous_iff hf] at hF
  obtain ⟨r, hr⟩ := exists_eval_ne_zero_of_totalDegree_le_card_aux F n hF₀ hF h
  obtain ⟨r, rfl⟩ := (Function.factorsThrough_iff _).mp <| (hf.factorsThrough r)
  use r
  rwa [eval_rename]
