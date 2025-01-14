import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Ideal.MinimalPrime
import Mathlib.RingTheory.PrimeSpectrum

variable {R : Type*} [CommRing R] (I : Ideal R)

open Ideal

/-- The height of a prime ideal is defined as the supremum of the lengths of strictly decreasing
chains of prime ideals below it. -/
noncomputable def Ideal.primeHeight [hI : I.IsPrime] : WithTop ℕ :=
  Order.height (⟨I, hI⟩ : PrimeSpectrum R)

/-- The height of an ideal is defined as the infimum of the heights of minimal prime ideals
containing it. -/
noncomputable def Ideal.height : WithTop ℕ :=
  ⨅ J ∈ I.minimalPrimes, @Ideal.primeHeight _ _ J (minimalPrimes_isPrime ‹_›)

/-- For a prime ideal, its height equals its prime height. -/
lemma Ideal.height_eq_primeHeight [I.IsPrime] : I.height = I.primeHeight := by
  unfold height primeHeight
  simp_rw [Ideal.minimalPrimes_eq_subsingleton_self]
  simp

/-- An ideal has finite height if it is either the top ideal or its height is not top. -/
class Ideal.FiniteHeight : Prop where
  eq_top_or_height_ne_top : I = ⊤ ∨ I.height ≠ ⊤

lemma Ideal.finiteHeight_iff_lt {I : Ideal R} :
  Ideal.FiniteHeight I ↔ I = ⊤ ∨ I.height < ⊤ := by
  constructor
  · intro h
    cases h.eq_top_or_height_ne_top with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (lt_of_le_of_ne le_top h)
  · intro h
    constructor
    cases h with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (ne_top_of_lt h)

lemma Ideal.height_ne_top {I : Ideal R} (hI : I ≠ ⊤) [h : I.FiniteHeight] :
  I.height ≠ ⊤ :=
  (h.eq_top_or_height_ne_top).resolve_left hI

lemma Ideal.height_lt_top {I : Ideal R} (hI : I ≠ ⊤) [h : I.FiniteHeight] :
  I.height < ⊤ := by
  exact lt_of_le_of_ne le_top (Ideal.height_ne_top hI)

lemma Ideal.primeHeight_ne_top (I : Ideal R) [I.FiniteHeight] [h : I.IsPrime] :
  I.primeHeight ≠ ⊤ := by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_ne_top (by exact h.ne_top)

lemma Ideal.primeHeight_lt_top (I : Ideal R) [I.FiniteHeight] [h : I.IsPrime] :
  I.primeHeight < ⊤ := by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_lt_top (by exact h.ne_top)

lemma Ideal.primeHeight_mono {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I ≤ J) :
  I.primeHeight ≤ J.primeHeight := by
  unfold primeHeight
  gcongr
  exact h

lemma Ideal.primeHeight_add_one_le_of_lt {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I < J) :
  I.primeHeight + 1 ≤ J.primeHeight := by
  unfold primeHeight
  exact Order.height_add_one_le h

lemma Ideal.primeHeight_strict_mono {I J : Ideal R} [I.IsPrime] [J.IsPrime]
  (h : I < J) [I.FiniteHeight] :
  I.primeHeight < J.primeHeight := by
  unfold primeHeight
  gcongr
  · exact I.primeHeight_ne_top.lt_top
  · exact h

lemma Ideal.height_strict_mono_of_is_prime {I J : Ideal R} [I.IsPrime]
  (h : I < J) [I.FiniteHeight] :
  I.height < J.height := by
  rw [Ideal.height_eq_primeHeight I, Ideal.height]
  obtain h := Ideal.nonempty_minimalPrimes J

  sorry
  -- rw [Ideal.height_eq_primeHeight I, Ideal.height]
  /-
    rw [ideal.height_eq_prime_height I, ideal.height,
    ← enat.coe_to_nat_eq_self.mpr (ideal.prime_height_ne_top I),
    with_top.coe_lt_iff_add_one_le, le_infi₂_iff],
  simp_rw [← with_top.coe_lt_iff_add_one_le, enat.coe_to_nat_eq_self.mpr
    (ideal.prime_height_ne_top I)],
  intros K hK,
  haveI := hK.1.1,
  cases hn : K.prime_height with n,
  { rw with_top.none_eq_top, exact ideal.prime_height_lt_top _ },
  haveI : K.finite_height := ⟨or.inr _⟩,
  { exact hn ▸ ideal.prime_height_strict_mono (e.trans_le hK.1.2) },
  { rw [ideal.height_eq_prime_height, hn], exact with_top.coe_ne_top }
  -/
  sorry -- The rest of the proof needs additional helper lemmas

theorem Ideal.minimalPrimes_eq_empty_iff (I : Ideal R) :
    I.minimalPrimes = ∅ ↔ I = ⊤ := by
  constructor
  · intro e
    by_contra h
    have ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I h
    have ⟨p, hp⟩ := Ideal.exists_minimalPrimes_le hM'
    show p ∈ (∅ : Set (Ideal R))
    rw [← e]; exact hp.1
  · intro h
    rw [h]
    sorry
    -- exact minimalPrimes_top

theorem Ideal.minimalPrimes_top : (⊤ : Ideal R).minimalPrimes = ∅ := by
  ext p
  constructor
  · intro h
    have := h.1.1
    sorry
    -- exact absurd (Eq.refl ⊤) (this rfl)
  · intro h
    exact False.elim (Set.not_mem_empty p h)

theorem Ideal.height_top : (⊤ : Ideal R).height = ⊤ := by
  simp only [height, minimalPrimes_top]
  sorry

theorem Ideal.height_mono {I J : Ideal R} (h : I ≤ J) : I.height ≤ J.height := by
  simp only [height]
  apply le_iInf
  intro p hp
  -- obtain ⟨q, hq, e⟩ := Ideal.exists_minimalPrimes_le (h.trans hp)
  sorry
#min_imports
theorem withTop.supr_add {ι : Sort*} [Nonempty ι]
    (f : ι → WithTop ℕ) (x : WithTop ℕ) :
    ⨆ i, f i + x = (⨆ i, f i) + x := by
  cases x
  case top =>
    simp only [add_top]
    apply le_antisymm
    · apply ciSup_le
      intro i
      exact le_top
    · simp
  case coe x =>
    have : ↑x ≤ ⨆ i, f i + ↑x := by
      sorry
    sorry

theorem withTop.supr₂_add {ι : Sort*} {p : ι → Prop} (hs : ∃ i, p i)
    (f : ∀ (i : ι), p i → WithTop ℕ) (x : WithTop ℕ) :
    (⨆ (i : ι) (h : p i), f i h) + x = ⨆ (i : ι) (h : p i), f i h + x := by
  haveI : Nonempty { i // p i } := ⟨⟨_, hs.choose_spec⟩⟩
  sorry

/-- The Krull dimension of a commutative ring, defined as the supremum of lengths of chains of
prime ideals -/
noncomputable def krullDimension (R : Type*) [CommRing R] : WithTop ℕ :=
  ⨆ (c : Set (Ideal R)) (h : IsChain (· ≤ ·) c) (h' : ∀ I ∈ c, I.IsPrime), ENat.card c

/-- A ring has finite Krull dimension if its Krull dimension is not ⊤ -/
class FiniteKrullDimensional (R : Type*) [CommRing R] : Prop where
  krullDimensionNeTop : krullDimension R ≠ ⊤

variable {R : Type*} [CommRing R]

lemma krullDimensionNeTop [h : FiniteKrullDimensional R] :
  krullDimension R ≠ ⊤ :=
h.krullDimensionNeTop

lemma krullDimensionLtTop [FiniteKrullDimensional R] :
  krullDimension R < ⊤ := by
  exact Ne.lt_top (krullDimensionNeTop)

lemma finiteKrullDimensionalIffLt :
  FiniteKrullDimensional R ↔ krullDimension R < ⊤ := by
  constructor
  · intro h
    exact krullDimensionLtTop
  · intro h
    exact ⟨ne_top_of_lt h⟩

lemma krullDimensionOfSubsingleton [Subsingleton R] :
  krullDimension R = 0 := by
  sorry

instance (priority := 100) finiteKrullDimensionalOfSubsingleton [Subsingleton R] :
  FiniteKrullDimensional R := by
  rw [finiteKrullDimensionalIffLt, krullDimensionOfSubsingleton]
  exact WithTop.top_pos

lemma Ideal.primeHeightLeKrullDimension {I : Ideal R} [I.IsPrime] :
    I.height ≤ krullDimension R := by
  sorry  -- The original uses le_supr₂ which needs to be adapted

instance Ideal.finiteHeightOfFiniteDimensional {I : Ideal R} [FiniteKrullDimensional R] (priority := 900):
    Ideal.FiniteHeight I := by
  rw [Ideal.finiteHeight_iff_lt, or_iff_not_imp_left]
  intro e
  obtain ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I e
  refine' (Ideal.height_mono hM').trans_lt _
  refine' (lt_of_le_of_lt _ (krullDimensionLtTop (R := R)))
  apply M.primeHeightLeKrullDimension

theorem krullDimensionSucc [Nontrivial R] :
    krullDimension R + 1 = Set.chainHeight {I : Ideal R | I.IsPrime} := by
  have h : ∃ I : Ideal R, I.IsPrime := by
    -- We know such an ideal exists in any nontrivial ring
    sorry
  sorry
