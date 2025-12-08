module

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Ideal.GoingDown

@[expose] public section

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma coeff_mem_pow_of_mem_adjoin_C_mul_X {R : Type*} [CommRing R]
    {I : Ideal R} {P : R[X]} (hP : P ∈ Algebra.adjoin R { C r * X | r ∈ I }) (i : ℕ) :
    P.coeff i ∈ I ^ i := by
  induction hP using Algebra.adjoin_induction generalizing i with
  | mem x hx =>
    obtain ⟨r, hrI, rfl⟩ := hx
    simp +contextual [coeff_X, apply_ite, hrI, @eq_comm _ 1]
  | algebraMap r => simp +contextual [coeff_C, apply_ite]
  | add x y hx hy _ _ => aesop
  | mul x y _ _ hx hy =>
    rw [coeff_mul]
    refine sum_mem fun ⟨j₁, j₂⟩ hj ↦ ?_
    obtain rfl : j₁ + j₂ = i := by simpa using hj
    exact pow_add I j₁ j₂ ▸ Ideal.mul_mem_mul (hx _) (hy _)

attribute [local instance] Polynomial.algebra in
lemma exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral
    {I : Ideal R} {x : S}
    (hx : IsIntegral (Algebra.adjoin R { C r * X | r ∈ I }) (C x * X)) :
    ∃ p : R[X], p.Monic ∧ aeval x p = 0 ∧ ∀ i, p.coeff i ∈ I ^ (p.natDegree - i) := by
  cases subsingleton_or_nontrivial R
  · use 0; simp [Monic, Subsingleton.elim (α := R) 0 1]
  obtain ⟨p, hp, e⟩ := hx
  let q : R[X] := ∑ i ∈ Finset.range (p.natDegree + 1),
    C ((p.coeff i).1.coeff (p.natDegree - i)) * X ^ i
  have hq : q.natDegree = p.natDegree := by
    refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_sum_le_of_forall_le _ _ ?_) ?_
    · exact fun i hi ↦ (natDegree_C_mul_X_pow_le _ _).trans (by simpa [Nat.lt_succ_iff] using hi)
    · simp [q, hp]
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [← hq] using show q.coeff p.natDegree = 1 by simp [q, hp]
  · replace e := congr(($e).coeff p.natDegree)
    simp only [eval₂_eq_sum_range, finset_sum_coeff, coeff_zero] at e
    simp only [q, map_sum, map_mul, aeval_C, map_pow, aeval_X]
    refine (Finset.sum_congr rfl fun i hi ↦ ?_).trans e
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hi
    rw [mul_pow, mul_left_comm, ← map_pow, coeff_C_mul, coeff_mul_X_pow', if_pos hi, mul_comm]
    simp [Subalgebra.algebraMap_def]
  · rw [hq]
    simp [q, Nat.lt_succ_iff, apply_ite, coeff_mem_pow_of_mem_adjoin_C_mul_X (p.coeff _).2]

lemma exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map [Algebra.IsIntegral R S]
    {I : Ideal R} {x : S} (hx : x ∈ I.map (algebraMap R S)) :
    ∃ p : R[X], p.Monic ∧ aeval x p = 0 ∧ ∀ i, p.coeff i ∈ I ^ (p.natDegree - i) := by
  classical
  let A : Subalgebra R R[X] := Algebra.adjoin R { C r * X | r ∈ I }
  letI := Polynomial.algebra R S
  refine exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral ?_
  induction hx using Submodule.span_induction with
  | zero => simp [isIntegral_zero]
  | add x y _ _ hx hy  => simpa [add_mul] using hx.add hy
  | mem x h =>
    obtain ⟨x, hx, rfl⟩ := h
    simpa using isIntegral_algebraMap (R := A) (A := S[X])
      (x := ⟨C x * X, Algebra.subset_adjoin ⟨x, hx, rfl⟩⟩)
  | smul a x _ hx =>
    simp only [smul_eq_mul, map_mul, mul_assoc]
    refine .mul ?_ hx
    exact ((Algebra.IsIntegral.isIntegral (R := R) a).map (IsScalarTower.toAlgHom R S _)).tower_top

@[stacks 00H5]
lemma exists_monic_aeval_eq_zero_forall_mem_of_mem_map [Algebra.IsIntegral R S]
    {I : Ideal R} {x : S} (hx : x ∈ I.map (algebraMap R S)) :
    ∃ p : R[X], p.Monic ∧ aeval x p = 0 ∧ ∀ i ≠ p.natDegree, p.coeff i ∈ I := by
  obtain ⟨p, hp, e, h⟩ := exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map hx
  refine ⟨p, hp, e, fun i hi ↦ ?_⟩
  obtain hi | hi := hi.lt_or_gt
  · exact Ideal.pow_le_self (by cutsat) (h _)
  · simp [coeff_eq_zero_of_natDegree_lt hi]

end Polynomial

open Polynomial

lemma _root_.IsIntegrallyClosed.minpoly_smul
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [FaithfulSMul R S]
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed R]
    {r : R} (hr : r ≠ 0) {s : S} (hs : IsIntegral R s) :
    minpoly R (r • s) = (minpoly R s).scaleRoots r := by
  let K := FractionRing R
  let L := FractionRing S
  let : Algebra K L := FractionRing.liftAlgebra _ _
  apply map_injective _ (FaithfulSMul.algebraMap_injective R K)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L (hs.smul r),
    map_scaleRoots _ _ _ (by simpa [minpoly.ne_zero_iff]),
    ← minpoly.isIntegrallyClosed_eq_field_fractions K L hs]
  simp_rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R K L]
  refine eq_of_monic_of_associated (minpoly.monic ?_) ?_
    (associated_of_dvd_dvd (minpoly.dvd _ _ ?_) ?_)
  · refine isIntegral_algebraMap.mul (hs.map (IsScalarTower.toAlgHom R S L)).tower_top
  · simpa [monic_scaleRoots_iff] using minpoly.monic
      (hs.map (IsScalarTower.toAlgHom R S L)).tower_top
  · exact scaleRoots_aeval_eq_zero (minpoly.aeval _ _)
  · rw [← Polynomial.scaleRoots_dvd_iff _ _ (r := (algebraMap R K r)⁻¹) (IsUnit.mk0 _ (by simpa)),
      ← scaleRoots_mul, mul_inv_cancel₀ (by simpa), scaleRoots_one]
    refine minpoly.dvd _ _ ?_
    nth_rw 1 [← inv_mul_cancel_left₀ (b := algebraMap S L s)
      (a := algebraMap K L (algebraMap R K r)) (by simpa), ← map_inv₀]
    exact scaleRoots_aeval_eq_zero (minpoly.aeval _ _)

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma Polynomial.coeff_mem_radical_span_coeff_of_dvd
    (p : R[X]) (q : R[X]) (hp : p.Monic) (hq : q.Monic)
    (H : q ∣ p) (i : ℕ) (hi : i ≠ q.natDegree) :
    q.coeff i ∈ (Ideal.span { p.coeff i | i < p.natDegree }).radical := by
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro P ⟨hPJ, hP⟩
  have : p.map (Ideal.Quotient.mk P) = X ^ p.natDegree := by
    ext i
    obtain hi | rfl | hi := lt_trichotomy i p.natDegree
    · simpa [hi.ne, Ideal.Quotient.eq_zero_iff_mem] using hPJ (Ideal.subset_span ⟨_, hi, rfl⟩)
    · simp [hp]
    · simp [coeff_eq_zero_of_natDegree_lt hi, hi.ne']
  obtain ⟨j, hj, a, ha⟩ :=
    (dvd_prime_pow (prime_X (R := R ⧸ P)) _).mp (this ▸ map_dvd (Ideal.Quotient.mk P) H)
  obtain ⟨r, hr, e⟩ := isUnit_iff.mp a⁻¹.isUnit
  rw [← Units.eq_mul_inv_iff_mul_eq, ← e] at ha
  obtain rfl : j = q.natDegree := by
    simpa [hq.natDegree_map, hr.ne_zero] using congr(($ha).natDegree).symm
  simpa [hi, Ideal.Quotient.eq_zero_iff_mem] using congr(($ha).coeff i)

@[stacks 00H8]
instance [IsDomain S] [FaithfulSMul R S] [Algebra.IsIntegral R S] [IsIntegrallyClosed R] :
    Algebra.HasGoingDown R S := by
  have := (FaithfulSMul.algebraMap_injective R S).isDomain
  constructor
  intro p _ Q _ hpQ
  let SQ := Localization.AtPrime Q
  suffices (p.map (algebraMap _ SQ)).comap (algebraMap _ SQ) ≤ p by
    obtain ⟨P, hP, e⟩ :=
      (Ideal.comap_map_eq_self_iff_of_isPrime _).mp (this.antisymm Ideal.le_comap_map)
    refine ⟨P.under S, ?_, inferInstance, ⟨by rw [Ideal.under_under, ← e]⟩⟩
    exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal_of_isPrime P)).trans_eq
      Localization.AtPrime.comap_maximalIdeal
  intro x hx
  obtain ⟨a, ha, haQ⟩ : ∃ a, x • a ∈ Ideal.map (algebraMap R S) p ∧ a ∉ Q := by
    simpa [Algebra.smul_def, IsScalarTower.algebraMap_eq R S SQ, ← Ideal.map_map,
      IsLocalization.mem_map_algebraMap_iff Q.primeCompl, ← map_mul] using hx
  obtain ⟨f, hfm, hfa, hf⟩ := exists_monic_aeval_eq_zero_forall_mem_of_mem_map ha
  obtain ⟨i, hi, hip⟩ : ∃ i ≠ (minpoly R a).natDegree, (minpoly R a).coeff i ∉ p := by
    set g := minpoly R a
    by_contra! H
    have : g.map (Ideal.Quotient.mk p) = X ^ g.natDegree := by
      ext i
      obtain hi | rfl | hi := lt_trichotomy i g.natDegree
      · simpa [hi.ne, Ideal.Quotient.eq_zero_iff_mem] using H _ hi.ne
      · simp [g, minpoly.monic (Algebra.IsIntegral.isIntegral _)]
      · simp [coeff_eq_zero_of_natDegree_lt hi, hi.ne']
    have : Ideal.Quotient.mk (Ideal.map (algebraMap R S) p) (a ^ (minpoly R a).natDegree) = 0 := by
      simpa [← Ideal.Quotient.algebraMap_eq, aeval_algebraMap_apply, g] using
        congr(aeval (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p) a) $this).symm
    exact haQ (‹Q.IsPrime›.mem_of_pow_mem _
      (Ideal.map_le_iff_le_comap.mpr hpQ.le (Ideal.Quotient.eq_zero_iff_mem.mp this)))
  by_cases hx0 : x = 0; · simp [hx0]
  have := Polynomial.coeff_mem_radical_span_coeff_of_dvd _ _ hfm
    (minpoly.monic (Algebra.IsIntegral.isIntegral _))
    (minpoly.isIntegrallyClosed_dvd (Algebra.IsIntegral.isIntegral _) hfa)
  simp only [IsIntegrallyClosed.minpoly_smul hx0 (Algebra.IsIntegral.isIntegral _),
    natDegree_scaleRoots, coeff_scaleRoots, Ideal.radical_eq_sInf, Submodule.mem_sInf,
    Set.mem_setOf_eq, and_imp] at this
  refine ‹p.IsPrime›.mem_of_pow_mem _ ((‹p.IsPrime›.mem_or_mem
    (this i hi p ?_ inferInstance)).resolve_left hip)
  simp +contextual [Ideal.span_le, Set.subset_def, LT.lt.ne, hf]
