/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Jiedong Jiang, Jingting Wang, Andrew Yang, Shouxin Zhang
-/
import Mathlib.Algebra.Module.SpanRank
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
/-!
# The Height of an Ideal

In this file, we define the height of a prime ideal and the height of an ideal.

# Main definitions

* `Ideal.primeHeight` : The height of a prime ideal $\mathfrak{p}$. We define it as the supremum of
 the lengths of strictly decreasing chains of prime ideals below it. This definition is implemented
 via `Order.height`.

* `Ideal.height` : The height of an ideal. We defined it as the infimum of the `primeHeight` of the
minimal prime ideals of I.

-/

variable {R : Type*} [CommRing R] (I : Ideal R)

open Ideal

/-- The height of a prime ideal is defined as the supremum of the lengths of strictly decreasing
chains of prime ideals below it. -/
noncomputable def Ideal.primeHeight [hI : I.IsPrime] : ℕ∞ :=
  Order.height (⟨I, hI⟩ : PrimeSpectrum R)

/-- The height of an ideal is defined as the infimum of the heights of its minimal prime ideals. -/
noncomputable def Ideal.height : ℕ∞ :=
  ⨅ J ∈ I.minimalPrimes, @Ideal.primeHeight _ _ J (minimalPrimes_isPrime ‹_›)

/-- For a prime ideal, its height equals its prime height. -/
lemma Ideal.height_eq_primeHeight [I.IsPrime] : I.height = I.primeHeight := by
  unfold height primeHeight
  simp_rw [Ideal.minimalPrimes_eq_subsingleton_self]
  simp

/-- An ideal has finite height if it is either the unit ideal or its height is finite.
We include the unit ideal in order to have the instance `IsNoetherianRing R → FiniteHeight I`. -/
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
    I.height < ⊤ :=
  (Ideal.height_ne_top hI).lt_top

lemma Ideal.primeHeight_ne_top (I : Ideal R) [I.FiniteHeight] [h : I.IsPrime] :
    I.primeHeight ≠ ⊤ := by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_ne_top h.ne_top

lemma Ideal.primeHeight_lt_top (I : Ideal R) [I.FiniteHeight] [h : I.IsPrime] :
    I.primeHeight < ⊤ := by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_lt_top h.ne_top

@[gcongr]
lemma Ideal.primeHeight_mono {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I ≤ J) :
    I.primeHeight ≤ J.primeHeight := by
  unfold primeHeight
  gcongr
  exact h

lemma Ideal.primeHeight_add_one_le_of_lt {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I < J) :
    I.primeHeight + 1 ≤ J.primeHeight := by
  unfold primeHeight
  exact Order.height_add_one_le h

@[gcongr]
lemma Ideal.primeHeight_strict_mono {I J : Ideal R} [I.IsPrime] [J.IsPrime]
    (h : I < J) [I.FiniteHeight] :
    I.primeHeight < J.primeHeight := by
  unfold primeHeight
  gcongr
  · exact I.primeHeight_ne_top.lt_top
  · exact h

@[simp]
theorem Ideal.height_top : (⊤ : Ideal R).height = ⊤ := by
  simp [height, minimalPrimes_top, iInf₂_eq_top]

@[gcongr]
theorem Ideal.height_mono {I J : Ideal R} (h : I ≤ J) : I.height ≤ J.height := by
  simp only [height]
  apply le_iInf₂; intro p hp; have := Ideal.minimalPrimes_isPrime hp
  obtain ⟨q, hq, e⟩ := Ideal.exists_minimalPrimes_le (h.trans hp.1.2)
  haveI := Ideal.minimalPrimes_isPrime hq
  exact (iInf₂_le q hq).trans (Ideal.primeHeight_mono e)

@[gcongr]
lemma Ideal.height_strict_mono_of_is_prime {I J : Ideal R} [I.IsPrime]
    (h : I < J) [I.FiniteHeight] : I.height < J.height := by
  rw [Ideal.height_eq_primeHeight I]
  by_cases hJ : J = ⊤
  · rw [hJ, height_top]; exact I.primeHeight_lt_top
  · rw [← ENat.add_one_le_iff I.primeHeight_ne_top, Ideal.height]
    apply le_iInf₂; intro K hK; haveI := Ideal.minimalPrimes_isPrime hK
    have : I < K := lt_of_lt_of_le h hK.1.2
    exact Ideal.primeHeight_add_one_le_of_lt this

lemma Ideal.primeHeight_le_ringKrullDim {I : Ideal R} [I.IsPrime] :
    I.primeHeight ≤ ringKrullDim R := Order.height_le_krullDim _

lemma Ideal.height_le_ringKrullDim_of_ne_top {I : Ideal R} (h : I ≠ ⊤):
    I.height ≤ ringKrullDim R := by
  rw [Ideal.height]
  have : Nonempty (I.minimalPrimes) := Ideal.nonempty_minimalPrimes h
  rcases this with ⟨P, hP⟩; haveI := hP.1.1
  refine le_trans ?_ (Ideal.primeHeight_le_ringKrullDim (I := P))
  norm_cast; apply iInf₂_le; exact hP

instance (priority := 900) Ideal.finiteHeightOfFiniteRingKrullDim {I : Ideal R}
    [FiniteRingKrullDim R] : I.FiniteHeight := by
  by_cases h : I = ⊤
  · exact ⟨Or.inl h⟩
  · refine ⟨Or.inr ?_⟩
    have h1 := ringKrullDim_lt_top (R := R)
    have h2 := Ideal.height_le_ringKrullDim_of_ne_top h
    rw [← lt_top_iff_ne_top];
    exact WithBot.coe_lt_coe.mp (lt_of_le_of_lt h2 h1)

/-- If J has finite height and I ≤ J, then I has finite height -/
lemma Ideal.finiteHeight_of_le {I J : Ideal R} (e : I ≤ J) (hJ : J ≠ ⊤) [FiniteHeight J] :
    FiniteHeight I where
  eq_top_or_height_ne_top := Or.inr <| by
    rw [← lt_top_iff_ne_top]
    exact (height_mono e).trans_lt (height_lt_top hJ)

/-- If J is a prime ideal containing I, and its height is less than or equal to the height of I,
then J is a minimal prime over I -/
lemma Ideal.mem_minimalPrimes_of_height_eq {I J : Ideal R} (e : I ≤ J) [J.IsPrime]
    [hJ : FiniteHeight J] (e' : J.height ≤ I.height) : J ∈ I.minimalPrimes := by
  obtain ⟨p, h₁, h₂⟩ := Ideal.exists_minimalPrimes_le e
  convert h₁; refine (eq_of_le_of_not_lt h₂ ?_).symm
  intro h₃
  have := h₁.1.1
  have := finiteHeight_of_le h₂ (by exact IsPrime.ne_top')
  exact lt_irrefl _
     ((height_strict_mono_of_is_prime h₃).trans_le (e'.trans <| height_mono h₁.1.2))

/-- A prime ideal has height zero if and only if it is minimal -/
lemma Ideal.primeHeight_eq_zero_iff {I : Ideal R} [I.IsPrime] :
  primeHeight I = 0 ↔ I ∈ minimalPrimes R := by
  rw [Ideal.primeHeight, Order.height_eq_zero, minimalPrimes, Ideal.minimalPrimes]
  simp only [bot_le, and_true, Set.mem_setOf_eq, Minimal, IsMin]
  constructor
  · intro h; by_contra h'; push_neg at h'
    obtain ⟨P, ⟨hP₁, ⟨hP₂, hP₃⟩⟩⟩ := h' (inferInstance)
    exact hP₃ (h (b := ⟨P, hP₁⟩) hP₂)
  · rintro ⟨hI, hI'⟩; intro b hb
    exact hI' (y := b.asIdeal) b.isPrime hb

theorem Ideal.isMaximal_of_primeHeight_eq_ringKrullDim {I : Ideal R} [hI : I.IsPrime]
 [h : FiniteRingKrullDim R] (e : I.primeHeight = ringKrullDim R) : I.IsMaximal := by
  have h : I ≠ ⊤ := by
    intro h
    simp only [h, ← Ideal.height_eq_primeHeight, Ideal.height_top, WithBot.coe_top] at e
    exact ringKrullDim_ne_top e.symm
  obtain ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I h
  rcases lt_or_eq_of_le hM' with (hM' | hM')
  · have h1 := Ideal.primeHeight_strict_mono hM'
    have h2 := e ▸ M.primeHeight_le_ringKrullDim
    simp only [WithBot.coe_le_coe] at h2
    absurd h1; rw [not_lt]; exact h2
  · exact hM' ▸ hM

/-- The prime height of the maximal ideal equals the Krull dimension in a local ring -/
theorem IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim [IsLocalRing R]:
    (IsLocalRing.maximalIdeal R).primeHeight = ringKrullDim R := by
  rw [ringKrullDim, Ideal.primeHeight, ← Order.height_top_eq_krullDim]; rfl

/-- The height of the maximal ideal equals the Krull dimension in a local ring -/
theorem IsLocalRing.maximalIdeal_height_eq_ringKrullDim [IsLocalRing R]:
    (IsLocalRing.maximalIdeal R).height = ringKrullDim R := by
  rw [Ideal.height_eq_primeHeight, IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim]

/-- For a local ring with finite Krull dimension, a prime ideal has height equal to the Krull
dimension if and only if it is the maximal ideal -/
theorem Ideal.primeHeight_eq_ringKrullDim_iff [FiniteRingKrullDim R] [IsLocalRing R] {I : Ideal R}
    [hI : I.IsPrime] : Ideal.primeHeight I = ringKrullDim R ↔ I = IsLocalRing.maximalIdeal R := by
  constructor
  · intro h
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_primeHeight_eq_ringKrullDim h)
  · intro h
    simp_rw [h]
    exact IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim

theorem IsLocalization.primeHeight_comap (S : Submonoid R) {A : Type*} [CommRing A] [Algebra R A]
    [IsLocalization S A] (J : Ideal A) [J.IsPrime] :
    (J.comap (algebraMap R A)).primeHeight = J.primeHeight := by
  rw [Ideal.primeHeight, Ideal.primeHeight, ← WithBot.coe_inj, Order.height_eq_krullDim_Iic,
    Order.height_eq_krullDim_Iic]
  let e := IsLocalization.orderIsoOfPrime S A
  have H : ∀ p : Ideal R, p ≤ J.comap (algebraMap R A) → Disjoint (S : Set R) p := by
    intro p hp
    exact Set.disjoint_of_subset_right hp (e ⟨_, hJ⟩).2.2
  refine Order.krullDim_eq_of_orderIso ?_
  exact
  { toFun := fun I => ⟨⟨I.1.1.comap (algebraMap R A), (e ⟨_, I.1.2⟩).2.1⟩, Ideal.comap_mono I.2⟩
    invFun := fun I => ⟨⟨_, (e.symm ⟨_, I.1.2, H _ I.2⟩).2⟩, Ideal.map_le_iff_le_comap.mpr I.2⟩
    left_inv := fun I => Subtype.ext <| PrimeSpectrum.ext_iff.mpr <| by
      have := (e.left_inv ⟨_, I.1.2⟩)
      apply_fun (fun I ↦ I.1) at this
      exact this
    right_inv := fun I => Subtype.ext <| PrimeSpectrum.ext_iff.mpr <| by
      have := (e.right_inv ⟨_, I.1.2, H _ I.2⟩)
      apply_fun (fun I ↦ I.1) at this
      exact this
    map_rel_iff' := fun {I₁ I₂} => @RelIso.map_rel_iff _ _ _ _ e ⟨_, I₁.1.2⟩ ⟨_, I₂.1.2⟩ }

theorem IsLocalization.height_comap (S : Submonoid R) {A : Type*} [CommRing A] [Algebra R A]
    [IsLocalization S A] (J : Ideal A) : (J.comap (algebraMap R A)).height = J.height := by
  rw [Ideal.height, Ideal.height]
  simp_rw [IsLocalization.primeHeight_comap S A, IsLocalization.minimalPrimes_comap S A,
    ← Ideal.height_eq_primeHeight, iInf_image]

theorem IsLocalization.AtPrime.ringKrullDim_eq_height (I : Ideal R) [I.IsPrime] (A : Type*)
    [CommRing A] [Algebra R A] [IsLocalization.AtPrime A I] :
    ringKrullDim A = I.height := by
  haveI := IsLocalization.AtPrime.isLocalRing A I
  rw [← IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim,
      IsLocalization.primeHeight_comap I.primeCompl A,
      ← IsLocalization.AtPrime.comap_maximalIdeal A I,
      Ideal.height_eq_primeHeight]

lemma mem_minimalPrimes_of_primeHeight_eq_height {I J : Ideal R} [J.IsPrime] (e : I ≤ J)
    (e' : J.primeHeight = I.height) [J.FiniteHeight] : J ∈ I.minimalPrimes := by
  rw [← J.height_eq_primeHeight] at e'
  exact mem_minimalPrimes_of_height_eq e (e' ▸ le_refl _)

lemma exists_spanRank_le_and_le_height_of_le_height [IsNoetherianRing R] (I : Ideal R) (r : ℕ)
  (hr : ↑r ≤ I.height) :
  ∃ J ≤ I, J.spanRank ≤ r ∧ ↑r ≤ J.height := by
  induction r with
  | zero =>
    refine ⟨⊥, bot_le, ?_, zero_le _⟩
    rw [Submodule.spanRank_bot]
    exact rfl.le
  | succ r ih =>
    obtain ⟨J, h₁, h₂, h₃⟩ := ih ((WithTop.coe_le_coe.mpr r.le_succ).trans hr)
    let S := { K | K ∈ J.minimalPrimes ∧ Ideal.height K = r }
    have hS : Set.Finite S := Set.Finite.subset J.minimalPrimes_finite_of_isNoetherianRing
      (fun _ h => h.1)
    have : ¬↑I ⊆ ⋃ K ∈ hS.toFinset, (K : Set R) := by
      refine (Ideal.subset_union_prime ⊥ ⊥ ?_).not.mpr ?_
      · rintro K hK - -
        rw [Set.Finite.mem_toFinset] at hK
        exact hK.1.1.1
      · push_neg
        intro K hK e
        have := hr.trans (Ideal.height_mono e)
        rw [Set.Finite.mem_toFinset] at hK
        rw [hK.2, ← not_lt] at this
        norm_cast at this
        exact this r.lt_succ_self
    simp_rw [Set.not_subset, Set.mem_iUnion, not_exists, Set.Finite.mem_toFinset] at this
    obtain ⟨x, hx₁, hx₂⟩ := this
    refine ⟨J ⊔ Ideal.span {x}, sup_le h₁ ?_, ?_, ?_⟩
    · rwa [Ideal.span_le, Set.singleton_subset_iff]
    · refine Submodule.spanRank_sup_le_sum_spanRank.trans ?_
      push_cast
      refine add_le_add h₂ ?_
      refine (Submodule.spanRank_span_set_finite (Set.toFinite _)).trans ?_
      simp
    · refine le_iInf₂ ?_
      intro p hp
      haveI := hp.1.1
      by_cases h : p.height = ⊤
      · rw [← p.height_eq_primeHeight, h]
        exact le_top
      haveI : p.FiniteHeight := ⟨Or.inr h⟩
      have := Ideal.height_mono (le_sup_left.trans hp.1.2)
      suffices h : ↑r ≠ p.primeHeight by
        push_cast
        have := h₃.trans this
        rw [Ideal.height_eq_primeHeight] at this
        exact Order.add_one_le_of_lt (lt_of_le_of_ne this h)
      intro e
      apply hx₂ p
      · have : J.height = p.primeHeight := by
          apply le_antisymm
          · rwa [← p.height_eq_primeHeight]
          · rwa [← e]
        refine ⟨mem_minimalPrimes_of_primeHeight_eq_height (le_sup_left.trans hp.1.2) this.symm, ?_⟩
        rwa [p.height_eq_primeHeight, eq_comm]
      · apply hp.1.2
        apply Ideal.mem_sup_right
        apply Ideal.subset_span
        exact Set.mem_singleton x
