import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Ideal.MinimalPrime

variable (R : Type*) [CommRing R]

@[mk_iff]
class RingKrullDimZero : Prop where
  isMaximal_of_isPrime : ∀ (I : Ideal R) [I.IsPrime], I.IsMaximal

alias Ideal.isMaximal_of_isPrime := RingKrullDimZero.isMaximal_of_isPrime

variable {R} [RingKrullDimZero R] (I : Ideal R)

variable {I} in
lemma Ideal.IsPrime.isMaximal (hI : I.IsPrime) : I.IsMaximal :=
  I.isMaximal_of_isPrime

variable {I} in
lemma Ideal.isMaximal_iff_isPrime : I.IsMaximal ↔ I.IsPrime :=
  ⟨fun h ↦ h.isPrime, fun h ↦ h.isMaximal⟩

lemma Ideal.jacobson_eq_radical : I.jacobson = I.radical := by
  simp [jacobson, radical_eq_sInf, Ideal.isMaximal_iff_isPrime]

lemma RingKrullDimZero.mem_minimalPrimes_iff {I J : Ideal R} :
    I ∈ J.minimalPrimes ↔ I.IsPrime ∧ J ≤ I :=
  ⟨fun H ↦ H.1, fun H ↦ ⟨H, fun _ h e ↦ (h.1.isMaximal.eq_of_le H.1.ne_top e).ge⟩⟩

lemma RingKrullDimZero.mem_minimalPrimes_iff_le {I J : Ideal R} [I.IsPrime] :
    I ∈ J.minimalPrimes ↔ J ≤ I := by
  rwa [mem_minimalPrimes_iff, and_iff_right]

variable (R) in
lemma RingKrullDimZero.minimalPrimes_eq_setOf_isPrime :
    minimalPrimes R = { I | I.IsPrime } := by
  ext; simp [minimalPrimes, mem_minimalPrimes_iff]

variable (R) in
lemma RingKrullDimZero.minimalPrimes_eq_setOf_isMaximal :
    minimalPrimes R = { I | I.IsMaximal } := by
  ext; simp [minimalPrimes_eq_setOf_isPrime, Ideal.isMaximal_iff_isPrime]

omit [RingKrullDimZero R] in
lemma ringKrullDimZero_iff_ringKrullDim_eq_zero [Nontrivial R] :
    RingKrullDimZero R ↔ ringKrullDim R = 0 := by
  rw [ringKrullDimZero_iff, ringKrullDim, Order.krullDim_eq_iSup_coheight_of_nonempty]
  simp only [WithBot.coe_eq_zero, ENat.iSup_eq_zero, Order.coheight_eq_zero,
    (PrimeSpectrum.equivSubtype R).forall_congr_left, Subtype.forall, PrimeSpectrum.isMax_iff]
  rfl

instance (priority := 100) [Subsingleton R] : RingKrullDimZero R :=
  ⟨fun _ hI ↦ (hI.ne_top (Subsingleton.elim _ _)).elim⟩

omit [RingKrullDimZero R] in
lemma ringKrullDimZero_iff_ringKrullDim_le_zero :
    RingKrullDimZero R ↔ ringKrullDim R ≤ 0 := by
  cases subsingleton_or_nontrivial R
  · simp only [ringKrullDim_eq_bot_of_subsingleton, bot_le, iff_true]
    infer_instance
  · simp [ringKrullDimZero_iff_ringKrullDim_eq_zero, le_antisymm_iff,
      ringKrullDim_nonneg_of_nontrivial]
