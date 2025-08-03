/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!

# Krull dimension and non zero-divisors

## Main results
- `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`: If `r` is not a zero divisor, then
  `dim R/r + 1 ≤ dim R`.
- `ringKrullDim_succ_le_ringKrullDim_polynomial`: `dim R + 1 ≤ dim R[X]`.
- `ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial`: `dim R + #σ ≤ dim R[σ]`.
-/

open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S]

lemma ringKrullDim_quotient (I : Ideal R) :
    ringKrullDim (R ⧸ I) = Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) := by
  rw [ringKrullDim, Order.krullDim_eq_of_orderIso I.primeSpectrumQuotientOrderIsoZeroLocus]

lemma ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    {r : R} (hr : r ∈ R⁰) :
    ringKrullDim (R ⧸ Ideal.span {r}) + 1 ≤ ringKrullDim R := by
  by_cases hr' : Ideal.span {r} = ⊤
  · rw [hr', ringKrullDim_eq_bot_of_subsingleton]
    simp
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) (Ideal.span {r})) := by
    rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty, ne_eq,
      PrimeSpectrum.zeroLocus_empty_iff_eq_top]
  have := Ideal.Quotient.nontrivial hr'
  have := (Ideal.Quotient.mk (Ideal.span {r})).domain_nontrivial
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_length, ringKrullDim,
    Order.krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add,
    ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
  intro l
  obtain ⟨p, hp, hp'⟩ := Ideal.exists_minimalPrimes_le (J := l.head.1.asIdeal) bot_le
  let p' : PrimeSpectrum R := ⟨p, hp.1.1⟩
  have hp' : p' < l.head := lt_of_le_of_ne hp' fun h ↦ Set.disjoint_iff.mp
    (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp)
    ⟨show r ∈ p by simpa [← h] using l.head.2, hr⟩
  refine le_trans ?_ (le_iSup _ ((l.map Subtype.val (fun _ _ ↦ id)).cons p' hp'))
  simp

/-- If `R →+* S` is surjective whose kernel contains a nonzerodivisor, then `dim S + 1 ≤ dim R`. -/
lemma ringKrullDim_succ_le_of_surjective (f : R →+* S) (hf : Function.Surjective f)
    {r : R} (hr : r ∈ R⁰) (hr' : f r = 0) : ringKrullDim S + 1 ≤ ringKrullDim R := by
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  gcongr
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ f (RingHom.ker f
    |>.span_singleton_le_iff_mem.mpr hr')) (Ideal.Quotient.lift_surjective_of_surjective _ _ hf)

open Polynomial in
lemma ringKrullDim_succ_le_ringKrullDim_polynomial :
    ringKrullDim R + 1 ≤ ringKrullDim R[X] :=
  ringKrullDim_succ_le_of_surjective constantCoeff (⟨C ·, coeff_C_zero⟩)
    X_mem_nonzeroDivisors coeff_X_zero

open MvPolynomial in
@[simp]
lemma ringKrullDim_mvPolynomial_of_isEmpty (σ : Type*) [IsEmpty σ] :
    ringKrullDim (MvPolynomial σ R) = ringKrullDim R :=
  ringKrullDim_eq_of_ringEquiv (isEmptyRingEquiv _ _)

open MvPolynomial in
lemma ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial (σ : Type*) [Finite σ] :
    ringKrullDim R + Nat.card σ ≤ ringKrullDim (MvPolynomial σ R) := by
  induction σ using Finite.induction_empty_option with
  | of_equiv e H =>
    convert ← H using 1
    · rw [Nat.card_congr e]
    · exact ringKrullDim_eq_of_ringEquiv (renameEquiv _ e).toRingEquiv
  | h_empty => simp
  | h_option IH =>
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one,
      ← add_assoc] at IH ⊢
    refine (add_le_add_right IH _).trans (ringKrullDim_succ_le_ringKrullDim_polynomial.trans ?_)
    exact (ringKrullDim_eq_of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv).ge

open MvPolynomial in
lemma ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial (σ : Type*) :
    ringKrullDim R + ENat.card σ ≤ ringKrullDim (MvPolynomial σ R) := by
  nontriviality R
  cases finite_or_infinite σ
  · rw [ENat.card_eq_coe_natCard]
    push_cast
    exact ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial _
  · simp only [ENat.card_eq_top_of_infinite, WithBot.coe_top]
    suffices ringKrullDim (MvPolynomial σ R) = ⊤ by aesop
    rw [WithBot.eq_top_iff_forall_ge]
    intro n
    let ι := Infinite.natEmbedding σ ∘ Fin.val (n := n + 1)
    have := Function.invFun_surjective (f := ι) ((Infinite.natEmbedding σ).2.comp Fin.val_injective)
    refine le_trans ?_ (ringKrullDim_le_of_surjective
      (rename (R := R) _).toRingHom (rename_surjective _ this))
    refine le_trans ?_ (ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial _)
    simp only [ENat.some_eq_coe, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_add,
      Nat.cast_one]
    trans n + 1
    · norm_cast
      simp
    · exact WithBot.le_add_self Order.bot_lt_krullDim.ne' _

open PowerSeries in
lemma ringKrullDim_succ_le_ringKrullDim_powerseries :
    ringKrullDim R + 1 ≤ ringKrullDim (PowerSeries R) :=
  ringKrullDim_succ_le_of_surjective (constantCoeff R) (⟨C R ·, rfl⟩)
    MvPowerSeries.X_mem_nonzeroDivisors constantCoeff_X

section Noetherian

variable [IsNoetherianRing R]
open Ideal

/-- If `I ≤ m` and `m` is maximal, the height of `m` is bounded by the height of `m ⧸ I R` plus
the span rank of `I`. -/
lemma Ideal.height_le_height_add_spanFinrank_of_le {I m : Ideal R} [m.IsMaximal] (hrm : I ≤ m) :
    m.height ≤ (m.map (algebraMap R (R ⧸ I))).height + I.spanFinrank := by
  classical
  let m' := m.map (algebraMap R (R ⧸ I))
  have : m'.IsMaximal := .map_of_surjective_of_ker_le Quotient.mk_surjective <| by simpa [span_le]
  have : m'.LiesOver m :=
    ⟨by simpa only [under, m'] using IsMaximal.eq_of_le inferInstance IsPrime.ne_top' le_comap_map⟩
  change m.height ≤ m'.height + I.spanFinrank
  obtain ⟨s, hms, hs⟩ := exists_finset_card_eq_height_of_isNoetherianRing m'
  have hsm' : (s : Set (R ⧸ I)) ⊆ (m' : Set _) := fun _ hx ↦ hms.1.2 (subset_span hx)
  have : Set.SurjOn (Ideal.Quotient.mk I) m s := by
    refine Set.SurjOn.mono subset_rfl hsm' fun x hx ↦ ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨x, by simpa [hrm, sup_of_le_left, m'] using hx⟩
  obtain ⟨o, himgo, hcardo, ho⟩ := s.exists_image_eq_and_card_le_of_surjOn (m : Set R) this
  have hI : I.FG := IsNoetherian.noetherian I
  let t : Finset R := o ∪ (Submodule.FG.finite_generators hI).toFinset
  suffices h : m.height ≤ t.card by
    refine le_trans h (hs ▸ ?_)
    norm_cast
    have : (Submodule.FG.finite_generators hI).toFinset.card = I.spanFinrank := by
      rw [← Set.ncard_eq_toFinset_card (hs := Submodule.FG.finite_generators hI)]
      exact Submodule.FG.generators_ncard hI
    exact le_trans (Finset.card_union_le o _) (by simp [hcardo, this])
  refine Ideal.height_le_card_of_mem_minimalPrimes ⟨⟨inferInstance, ?_⟩, fun q ⟨_, hleq⟩ hqle ↦ ?_⟩
  · simp only [Finset.coe_union, t, span_le, Set.union_subset_iff]
    refine ⟨ho, le_trans (show _ ⊆ (I : Set _) from ?_) hrm⟩
    conv_rhs => rw [← Submodule.span_generators I]
    simp only [Set.Finite.coe_toFinset, submodule_span_eq, subset_span]
  · have : I ≤ q := by
      refine le_trans ?_ hleq
      conv_lhs => rw [← Submodule.span_generators I]
      simp [t, span_union]
    have h2 : m' ≤ Ideal.map (Ideal.Quotient.mk I) q := by
      refine hms.2 ⟨map_quotientMk_isPrime_of_isPrime this, ?_⟩ (map_mono hqle)
      simp only [← himgo, Finset.coe_image, ← map_span]
      exact map_mono (le_trans (span_mono <| by simp [t]) hleq)
    apply Ideal.comap_mono (f := Ideal.Quotient.mk I) at h2
    simp only [comap_map_quotientMk, this, sup_of_le_right, m'] at h2
    exact le_trans le_comap_map h2

/-- If `m` is a maximal ideal generated by `s`, the height of `m` is bounded
by the sum of the height of the image of `m` in `R ⧸ (s)` and the cardinality of `s`. -/
lemma Ideal.height_le_height_add_encard_of_subset (s : Set R) {m : Ideal R} [m.IsMaximal]
    (hrm : s ⊆ m) : m.height ≤ (m.map (algebraMap R (R ⧸ span s))).height + s.encard := by
  apply le_trans (Ideal.height_le_height_add_spanFinrank_of_le (I := span s) (m := m) ?_) ?_
  · rwa [span_le]
  · gcongr
    exact Submodule.spanFinrank_span_le_encard _

lemma Ideal.height_le_height_succ_of_mem {r : R} {m : Ideal R} [m.IsMaximal] (hrm : r ∈ m) :
    m.height ≤ (m.map (Ideal.Quotient.mk (span {r}))).height + 1 := by
  convert Ideal.height_le_height_add_encard_of_subset {r} (m := m) ?_
  · simp
  · simpa

/-- If `r` is an nonzerodivisor contained in an ideal of maximal height,
`dim (R / (r)) = dim R - 1`. -/
lemma ringKrullDim_quotient_succ_of_mem_nonZeroDivisors {r : R}
    (hr : r ∈ nonZeroDivisors R) {m : Ideal R} [m.IsMaximal]
    (h : m.height = ringKrullDim R) (hm : r ∈ m) :
    ringKrullDim (R ⧸ span {r}) + 1 = ringKrullDim R := by
  refine le_antisymm (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr) (h ▸ ?_)
  trans (m.map (algebraMap R (R ⧸ span {r}))).height + 1
  · norm_cast
    exact Ideal.height_le_height_succ_of_mem hm
  · gcongr
    have : (Ideal.map (algebraMap R (R ⧸ span {r})) m).IsMaximal :=
      IsMaximal.map_of_surjective_of_ker_le Quotient.mk_surjective (by simp [span_le, hm])
    exact Ideal.height_le_ringKrullDim_of_ne_top IsPrime.ne_top'

/-- If `r` is an nonzerodivisor in the Jacobson radical of `R` and `R` is Noetherian,
`dim (R / (r)) = dim R - 1`. -/
lemma ringKrullDim_quotient_succ_of_mem_nonZeroDivisors_of_mem_jacobson
    {r : R} (hr₁ : r ∈ nonZeroDivisors R) (hr₂ : r ∈ Ring.jacobson R) :
    ringKrullDim (R ⧸ span {r}) + 1 = ringKrullDim R := by
  refine le_antisymm (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr₁) ?_
  nontriviality R
  rw [ringKrullDim_le_iff_isMaximal_height_le]
  intro m hm
  have hrm : r ∈ m := by
    simp only [Ring.jacobson_eq_sInf_isMaximal, Submodule.mem_sInf, Set.mem_setOf_eq] at hr₂
    exact hr₂ _ hm
  trans (m.map (algebraMap R (R ⧸ span {r}))).height + 1
  · norm_cast
    exact Ideal.height_le_height_succ_of_mem hrm
  · gcongr
    have : (Ideal.map (algebraMap R (R ⧸ span {r})) m).IsMaximal :=
      .map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simp [span_le, hrm])
    exact Ideal.height_le_ringKrullDim_of_ne_top IsPrime.ne_top'

lemma ringKrullDim_eq_succ_of_surjective_of_mem_jacobson
    {f : R →+* S} (hf : Function.Surjective f) {r : R} (hr₁ : r ∈ nonZeroDivisors R)
    (hr₂ : r ∈ Ring.jacobson R) (hr₃ : RingHom.ker f = span {r}) :
    ringKrullDim R = ringKrullDim S + 1 := by
  refine (ringKrullDim_quotient_succ_of_mem_nonZeroDivisors_of_mem_jacobson hr₁ hr₂).symm.trans ?_
  congr
  rw [← hr₃]
  exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hf)

end Noetherian
