/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Jiedong Jiang, Jingting Wang, Andrew Yang, Shouxin Zhang
-/
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Ideal.MinimalPrime
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
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
  lt_of_le_of_ne le_top (Ideal.height_ne_top hI)

lemma Ideal.primeHeight_ne_top (I : Ideal R) [I.FiniteHeight] [h : I.IsPrime] :
    I.primeHeight ≠ ⊤ := by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_ne_top (by exact h.ne_top)

lemma Ideal.primeHeight_lt_top (I : Ideal R) [I.FiniteHeight] [h : I.IsPrime] :
    I.primeHeight < ⊤ := by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_lt_top (by exact h.ne_top)

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
  simp only [height, minimalPrimes_top]
  rw [iInf₂_eq_top]; intro i hi; exact False.elim hi

@[gcongr]
theorem Ideal.height_mono {I J : Ideal R} (h : I ≤ J) : I.height ≤ J.height := by
  simp only [height]
  apply le_iInf₂; intro p hp; haveI := hp.1.1
  obtain ⟨q, hq, e⟩ := Ideal.exists_minimalPrimes_le (h.trans hp.1.2)
  haveI := hq.1.1
  exact (iInf₂_le q hq).trans (Ideal.primeHeight_mono e)

@[gcongr]
lemma Ideal.height_strict_mono_of_is_prime {I J : Ideal R} [I.IsPrime]
    (h : I < J) [I.FiniteHeight] : I.height < J.height := by
  rw [Ideal.height_eq_primeHeight I]
  by_cases hJ : J = ⊤
  · rw [hJ, height_top]; exact I.primeHeight_lt_top
  · rw [← ENat.add_one_le_iff I.primeHeight_ne_top, Ideal.height]
    apply le_iInf₂; intro K hK; haveI := hK.1.1
    have : I < K := lt_of_lt_of_le h hK.1.2
    exact Ideal.primeHeight_add_one_le_of_lt this

theorem ENat.iSup₂_add {ι : Type*} {p : ι → Prop} (hs : ∃ i, p i)
    (f : ∀ (i : ι), p i → ℕ∞) (x : ℕ∞) :
    (⨆ (i : ι) (h : p i), f i h) + x = ⨆ (i : ι) (h : p i), f i h + x := by
  haveI : Nonempty { i // p i } := ⟨⟨_, hs.choose_spec⟩⟩
  rw [iSup_subtype', iSup_subtype', ENat.iSup_add]

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
  convert h₁
  sorry
  -- refine eq_of_le_of_not_lt h₂ ?_
  -- intro h₃
  -- have := h₁.1.1
  -- have := finiteHeightOfLe h₂ (by exact IsPrime.ne_top)
  -- exact lt_irrefl _
  --   ((height_strict_mono_of_is_prime h₃).trans_le (e'.trans $ height_mono h₁.1.2))

/-- A prime ideal has height zero if and only if it is minimal -/
lemma Ideal.primeHeight_eq_zero_iff {I : Ideal R} [I.IsPrime] :
  primeHeight I = 0 ↔ I ∈ minimalPrimes R := by
  rw [Ideal.primeHeight, Order.height_eq_zero]
  constructor
  · intro h
    sorry
  · sorry

theorem Ideal.isMaximal_of_primeHeight_eq_ringKrullDim {I : Ideal R} [hI : I.IsPrime]
 [h : FiniteRingKrullDim R] (e : I.primeHeight = ringKrullDim R) : I.IsMaximal := by
  have h : I ≠ ⊤ := sorry
  obtain ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I h

  sorry
  -- cases' subsingleton_or_nontrivial R
  -- exact (h.1 <| Subsingleton.elim _ _).elim
  -- by_contra h'
  -- obtain ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I h'

  -- have IneBot : I ≠ ⊥ := I.isPrime_proper
  -- have MneBot : M ≠ ⊥ := M.isMaximal_proper

  -- have height_le : I.primeHeight ≤ M.primeHeight := by
  --   apply Ideal.primeHeight_mono
  --   exact hM'

  -- have M_height_le : (M.primeHeight) ≤ ringKrullDim R :=
  --   Ideal.primeHeight_le_ringKrullDim

  -- have height_strict : I.primeHeight < M.primeHeight := by
  --   apply lt_of_le_of_ne height_le
  --   intro h_eq
  --   apply h'
  --   sorry -- need a lemma about equality of heights implying equality of ideals

  -- have := lt_of_lt_of_le (WithBot.coe_lt_coe.mpr height_strict) M_height_le
  -- rw [e] at this
  -- exact lt_irrefl _ this

  --   casesI subsingleton_or_nontrivial R,
  -- { exact ((h.1 : _) $ subsingleton.elim _ _).elim },
  -- have := congr_arg (λ x : with_top ℕ, x + 1) e,
  -- dsimp at this,
  -- rw [ideal.prime_height_succ] at this,
  -- refine ⟨⟨h.1, _⟩⟩,
  -- intros J hJ,
  -- by_contra e',
  -- obtain ⟨M, hM, hM'⟩ := ideal.exists_le_maximal J e',
  -- have H : (insert M (set_of ideal.is_prime ∩ set.Iic I)).chain_height =
  --   krull_dimension R + 1 + 1,
  -- { rw [← this, set.chain_height_insert_of_forall_lt],
  --   intros I' hI',
  --   calc I' ≤ I : hI'.2
  --       ... < J : hJ
  --       ... ≤ M : hM' },
  -- have : krull_dimension R + 1 + 1 ≤ set.chain_height (set_of ideal.is_prime),
  -- { rw ← H, apply set.chain_height_le_of_subset, rintros K (rfl|⟨h, _⟩), exacts [hM.is_prime, h]}
  -- cases h : krull_dimension R with x,
  -- { exact krull_dimension_ne_top R h },
  -- { rw [← krull_dimension_succ, h] at this, linarith [with_top.coe_le_coe.mp this] }
  -- have height_strict : I.primeHeight < M.primeHeight := by
  --   apply lt_of_le_of_ne height_le
  --   intro h_eq
  --   apply h'
  --   sorry -- need a lemma about equality of heights implying equality of ideals

  -- have := lt_of_lt_of_le (WithBot.coe_lt_coe.mpr height_strict) M_height_le
  -- rw [e] at this
  -- exact lt_irrefl _ this


/-- The prime height of the maximal ideal equals the Krull dimension -/
theorem LocalRing.maximalIdeal_primeHeight_eq_ringKrullDim [IsLocalRing R]:
    (IsLocalRing.maximalIdeal R).primeHeight = ringKrullDim R := by
  apply le_antisymm
  · apply Ideal.primeHeight_le_ringKrullDim
  · sorry

/-- The height of the maximal ideal equals the Krull dimension -/
theorem LocalRing.maximalIdeal_height_eq_ringKrullDim [IsLocalRing R]:
    (IsLocalRing.maximalIdeal R).height = ringKrullDim R := by
  rw [Ideal.height_eq_primeHeight, LocalRing.maximalIdeal_primeHeight_eq_ringKrullDim]


/-- For a local ring with finite Krull dimension, a prime ideal has height equal to the Krull
dimension if and only if it is the maximal ideal -/
theorem Ideal.primeHeight_eq_ringKrullDim_iff [FiniteRingKrullDim R] [IsLocalRing R] {I : Ideal R}
    [hI : I.IsPrime] : Ideal.primeHeight I = ringKrullDim R ↔ I = IsLocalRing.maximalIdeal R := by
  constructor
  · intro h
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_primeHeight_eq_ringKrullDim h)
  · intro h
    simp_rw [h]
    exact LocalRing.maximalIdeal_primeHeight_eq_ringKrullDim


-- lemma set.chain_height_univ {α : Type*} [preorder α] (s : set α) :
--   (set.univ : set s).chain_height = s.chain_height :=
-- begin
--   conv_rhs { rw [← @subtype.range_coe _ s, ← set.image_univ] },
--   rw set.chain_height_image,
--   intros x y, refl,
-- end

-- lemma order_iso.chain_height_eq {α β : Type*} [preorder α] [preorder β]
--   (e : α ≃o β) : (set.univ : set α).chain_height = (set.univ : set β).chain_height :=
-- begin
--   rw [← set.range_iff_surjective.mpr e.surjective, ← set.image_univ, set.chain_height_image],
--   exact λ _ _, e.lt_iff_lt.symm
-- end

-- theorem set.chain_height_univ {α : Type*} [Preorder α] (s : Set α) :
--   (Set.univ : Set s).chainHeight = s.chainHeight := by
--   conv_rhs =>
--     rw [← Subtype.range_val s, ← Set.image_univ]
--   rw [Set.chainHeight_image]
--   intro x y
--   rfl

-- theorem OrderIso.chain_height_eq {α β : Type*} [Preorder α] [Preorder β]
--   (e : α ≃o β) : (Set.univ : Set α).chainHeight = (Set.univ : Set β).chainHeight := by
--   rw [← Set.range_iff_surjective.mpr e.surjective, ← Set.image_univ, Set.chainHeight_image]
--   exact fun _ _ => (e.lt_iff_lt).symm

theorem ENat.add_inj_of_ne_top {n : ℕ∞} (hn : n ≠ ⊤) : Function.Injective (fun a => a + n) := by
  intro a b e
  exact le_antisymm
    ((WithTop.add_le_add_iff_right hn).mp e.le)
    ((WithTop.add_le_add_iff_right hn).mp e.ge)









-- lemma Ideal.mem_minimal_primes_of_height_eq
--   {I J : Ideal R} (e : I ≤ J) [JPrime : J.IsPrime] [hJ : Ideal.FiniteHeight J]
--     (e' : J.height ≤ I.height) : J ∈ I.minimalPrimes := by
--   obtain ⟨p, h₁, h₂⟩ := Ideal.exists_minimalPrimes_le e
--   convert h₁
--   apply (eq_of_le_of_not_lt h₂ ?_).symm
--   intro h₃
--   letI := h₁.1.1
--   letI := Ideal.finite_height_of_le h₂ <| Ideal.IsPrime.ne_top JPrime
--   replace h₃ :=Ideal.height_strict_mono_of_is_prime h₃
--   contrapose! h₃
--   exact e'.trans <| Ideal.height_mono h₁.1.2

-- lemma Ideal.primeHeight_eq_zero_iff {I : Ideal R} [I.IsPrime] :
--   I.primeHeight = 0 ↔ I ∈ minimalPrimes R := by
--   unfold Ideal.primeHeight
--   rw [Set.chainHeight_eq_zero_iff]
--   constructor
--   . intro h
--     refine' ⟨by simp_all only [bot_le, and_self], fun J hJ hJI => ?_⟩
--     rw [@Set.eq_empty_iff_forall_not_mem] at h
--     specialize h J
--     simp only [Set.mem_setOf_eq, true_and, hJ] at h
--     rw [propext (LE.le.not_gt_iff_eq hJI)] at h
--     simp_rw [h, le_refl]
--   . intro hI
--     ext ⟨J, hJ⟩
--     simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
--     intro hJ_prime hJ_lt_I
--     exact not_le_of_lt hJ_lt_I (hI.2 ⟨hJ_prime, bot_le⟩ hJ_lt_I.le)

-- theorem Ideal.isMaximal_of_prime_height_eq_krullDimension {I : Ideal R} [h : I.IsPrime] [FiniteKrullDimensional R]
--     (e : I.primeHeight = krullDimension R) : I.IsMaximal := by
--   rcases subsingleton_or_nontrivial R with h' | _
--   . exact (h.1 <| Subsingleton.elim I ⊤).elim
--   . have := congrArg (fun x : WithTop ℕ => x + 1) e
--     dsimp at this
--     rw [Ideal.primeHeight_succ] at this
--     refine ⟨h.1, ?_⟩
--     intro J hJ
--     by_contra e'
--     obtain ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal J e'
--     have H : (insert M (setOf Ideal.IsPrime ∩ Set.Iic I)).chainHeight =
--       krullDimension R + (1 : WithTop ℕ) + (1 : WithTop ℕ) := by
--       rw [← this, Set.chainHeight_insert_of_forall_lt]; rfl
--       intro I' hI'
--       calc
--         I' ≤ I := hI'.2
--         _ < J := hJ
--         _ ≤ M := hM'
--     have : krullDimension R + (1 : WithTop ℕ) + (1 : WithTop ℕ) ≤
--       Set.chainHeight (setOf <| Ideal.IsPrime (α := R)) := by
--       rw [← H]
--       apply Set.chainHeight_mono
--       rintro K (rfl | ⟨hK, _⟩)
--       · exact hM.isPrime
--       · exact hK
--     cases h_dim : krullDimension R with
--     | top => exact krullDimensionNeTop h_dim
--     | coe x =>
--       rw [← krullDimensionSucc, h_dim] at this
--       linarith [WithTop.coe_le_coe.mp this]
