/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SetFamily.Compression.UV

/-!
# Kruskal-Katona theorem

This file proves the Kruskal-Katona theorem. This is a sharp statement about how many sets of size
`k - 1` are covered by a family of sets of size `k`, given only its size.

## Main declarations

The key results proved here are:
* `Finset.kruskal_katona`: The basic Kruskal-Katona theorem. Given a set family `𝒜` consisting of
  `r`-sets, and `𝒞` an initial segment of the colex order of the same size, the shadow of `𝒞` is
  smaller than the shadow of `𝒜`. In particular, this shows that the minimum shadow size is
  achieved by initial segments of colex.
* `Finset.iterated_kruskal_katona`: An iterated form of the Kruskal-Katona theorem, stating that the
  minimum iterated shadow size is given by initial segments of colex.

## TODO

* Define the `k`-cascade representation of a natural and prove the corresponding version of
  Kruskal-Katona.
* Abstract away from `Fin n` so that it also applies to `ℕ`. Probably `LocallyFiniteOrderBot`
  will help here.
* Characterise the equality case.

## References

* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

kruskal-katona, kruskal, katona, shadow, initial segments, intersecting
-/

-- TODO: There's currently a diamond. See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/DecidableEq.20diamond.20on.20Fin
-- import Mathlib.Order.Fin.Basic
-- example (n : ℕ) : instDecidableEqFin n = instDecidableEq_mathlib := rfl
attribute [-instance] instDecidableEqFin

open Nat
open scoped FinsetFamily

namespace Finset
namespace Colex
variable {α : Type*} [LinearOrder α] {𝒜 𝒜₁ 𝒜₂ : Finset (Finset α)} {s t : Finset α} {r : ℕ}

/-- This is important for iterating Kruskal-Katona: the shadow of an initial segment is also an
initial segment. -/
lemma shadow_initSeg [Fintype α] (hs : s.Nonempty) :
    ∂ (initSeg s) = initSeg (erase s <| min' s hs) := by
  -- This is a pretty painful proof, with lots of cases.
  ext t
  simp only [mem_shadow_iff_insert_mem, mem_initSeg, exists_prop]
  constructor
  -- First show that if t ∪ a ≤ s, then t ≤ s - min s
  · rintro ⟨a, ha, hst, hts⟩
    constructor
    · rw [card_erase_of_mem (min'_mem _ _), hst, card_insert_of_not_mem ha, add_tsub_cancel_right]
    · simpa [ha] using erase_le_erase_min' hts hst.ge (mem_insert_self _ _)
  -- Now show that if t ≤ s - min s, there is j such that t ∪ j ≤ s
  -- We choose j as the smallest thing not in t
  simp_rw [le_iff_eq_or_lt, lt_iff_exists_filter_lt, mem_sdiff, filter_inj, and_assoc]
  simp only [toColex_inj, ofColex_toColex, ne_eq, and_imp]
  rintro cards' (rfl | ⟨k, hks, hkt, z⟩)
  -- If t = s - min s, then use j = min s so t ∪ j = s
  · refine ⟨min' s hs, not_mem_erase _ _, ?_⟩
    rw [insert_erase (min'_mem _ _)]
    exact ⟨rfl, Or.inl rfl⟩
  set j := min' tᶜ ⟨k, mem_compl.2 hkt⟩
  -- Assume first t < s - min s, and take k as the colex witness for this
  have hjk : j ≤ k := min'_le _ _ (mem_compl.2 ‹k ∉ t›)
  have : j ∉ t := mem_compl.1 (min'_mem _ _)
  have hcard : card s = card (insert j t) := by
    rw [card_insert_of_not_mem ‹j ∉ t›, ← ‹_ = card t›, card_erase_add_one (min'_mem _ _)]
  refine ⟨j, ‹_›, hcard, ?_⟩
  -- Cases on j < k or j = k
  obtain hjk | r₁ := hjk.lt_or_eq
  -- if j < k, k is our colex witness for t ∪ {j} < s
  · refine Or.inr ⟨k, mem_of_mem_erase ‹_›, fun hk ↦ hkt <| mem_of_mem_insert_of_ne hk hjk.ne',
      fun x hx ↦ ?_⟩
    simpa only [mem_insert, z hx, (hjk.trans hx).ne', mem_erase, Ne, false_or,
      and_iff_right_iff_imp] using fun _ ↦ ((min'_le _ _ <| mem_of_mem_erase hks).trans_lt hx).ne'
  -- if j = k, all of range k is in t so by sizes t ∪ {j} = s
  refine Or.inl (eq_of_subset_of_card_le (fun a ha ↦ ?_) hcard.ge).symm
  rcases lt_trichotomy k a with (lt | rfl | gt)
  · apply mem_insert_of_mem
    rw [z lt]
    refine mem_erase_of_ne_of_mem (lt_of_le_of_lt ?_ lt).ne' ha
    apply min'_le _ _ (mem_of_mem_erase ‹_›)
  · rw [r₁]; apply mem_insert_self
  · apply mem_insert_of_mem
    rw [← r₁] at gt
    by_contra
    apply (min'_le tᶜ _ _).not_lt gt
    rwa [mem_compl]

/-- The shadow of an initial segment is also an initial segment. -/
protected lemma IsInitSeg.shadow [Finite α] (h₁ : IsInitSeg 𝒜 r) : IsInitSeg (∂ 𝒜) (r - 1) := by
  cases nonempty_fintype α
  obtain rfl | hr := Nat.eq_zero_or_pos r
  · have : 𝒜 ⊆ {∅} := fun s hs ↦ by rw [mem_singleton, ← Finset.card_eq_zero]; exact h₁.1 hs
    have := shadow_monotone this
    simp only [subset_empty, le_eq_subset, shadow_singleton_empty] at this
    simp [this]
  obtain rfl | h𝒜 := 𝒜.eq_empty_or_nonempty
  · simp
  obtain ⟨s, rfl, rfl⟩ := h₁.exists_initSeg h𝒜
  rw [shadow_initSeg (card_pos.1 hr), ← card_erase_of_mem (min'_mem _ _)]
  exact isInitSeg_initSeg

end Colex

open Finset Colex Nat UV
open scoped FinsetFamily

variable {α : Type*} [LinearOrder α] {s U V : Finset α} {n : ℕ}

namespace UV

/-- Applying the compression makes the set smaller in colex. This is intuitive since a portion of
the set is being "shifted down" as `max U < max V`. -/
lemma toColex_compress_lt_toColex {hU : U.Nonempty} {hV : V.Nonempty} (h : max' U hU < max' V hV)
    (hA : compress U V s ≠ s) : toColex (compress U V s) < toColex s := by
  rw [compress, ite_ne_right_iff] at hA
  rw [compress, if_pos hA.1, lt_iff_exists_filter_lt]
  simp_rw [mem_sdiff (s := s), filter_inj, and_assoc]
  refine ⟨_, hA.1.2 <| max'_mem _ hV, not_mem_sdiff_of_mem_right <| max'_mem _ _, fun a ha ↦ ?_⟩
  have : a ∉ V := fun H ↦ ha.not_le (le_max' _ _ H)
  have : a ∉ U := fun H ↦ ha.not_lt ((le_max' _ _ H).trans_lt h)
  simp [‹a ∉ U›, ‹a ∉ V›]

/-- These are the compressions which we will apply to decrease the "measure" of a family of sets.-/
private def UsefulCompression (U V : Finset α) : Prop :=
  Disjoint U V ∧ U.card = V.card ∧ ∃ (HU : U.Nonempty) (HV : V.Nonempty), max' U HU < max' V HV

private instance UsefulCompression.instDecidableRel : @DecidableRel (Finset α) UsefulCompression :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Applying a good compression will decrease measure, keep cardinality, keep sizes and decrease
shadow. In particular, 'good' means it's useful, and every smaller compression won't make a
difference. -/
private lemma compression_improved (𝒜 : Finset (Finset α)) (h₁ : UsefulCompression U V)
    (h₂ : ∀ ⦃U₁ V₁⦄, UsefulCompression U₁ V₁ → U₁.card < U.card → IsCompressed U₁ V₁ 𝒜) :
    (∂ (𝓒 U V 𝒜)).card ≤ (∂ 𝒜).card := by
  obtain ⟨UVd, same_size, hU, hV, max_lt⟩ := h₁
  refine card_shadow_compression_le _ _ fun x Hx ↦ ⟨min' V hV, min'_mem _ _, ?_⟩
  obtain hU' | hU' := eq_or_lt_of_le (succ_le_iff.2 hU.card_pos)
  · rw [← hU'] at same_size
    have : erase U x = ∅ := by rw [← Finset.card_eq_zero, card_erase_of_mem Hx, ← hU']
    have : erase V (min' V hV) = ∅ := by
      rw [← Finset.card_eq_zero, card_erase_of_mem (min'_mem _ _), ← same_size]
    rw [‹erase U x = ∅›, ‹erase V (min' V hV) = ∅›]
    exact isCompressed_self _ _
  refine h₂ ⟨UVd.mono (erase_subset ..) (erase_subset ..), ?_, ?_, ?_, ?_⟩ (card_erase_lt_of_mem Hx)
  · rw [card_erase_of_mem (min'_mem _ _), card_erase_of_mem Hx, same_size]
  · rwa [← card_pos, card_erase_of_mem Hx, tsub_pos_iff_lt]
  · rwa [← Finset.card_pos, card_erase_of_mem (min'_mem _ _), ← same_size, tsub_pos_iff_lt]
  · exact (Finset.max'_subset _ <| erase_subset _ _).trans_lt (max_lt.trans_le <| le_max' _ _ <|
      mem_erase.2 ⟨(min'_lt_max'_of_card _ (by rwa [← same_size])).ne', max'_mem _ _⟩)

/-- If we're compressed by all useful compressions, then we're an initial segment. This is the other
key Kruskal-Katona part. -/
lemma isInitSeg_of_compressed {ℬ : Finset (Finset α)} {r : ℕ} (h₁ : (ℬ : Set (Finset α)).Sized r)
    (h₂ : ∀ U V, UsefulCompression U V → IsCompressed U V ℬ) : IsInitSeg ℬ r := by
  refine ⟨h₁, ?_⟩
  rintro A B hA ⟨hBA, sizeA⟩
  by_contra hB
  have hAB : A ≠ B := ne_of_mem_of_not_mem hA hB
  have hAB' : A.card = B.card := (h₁ hA).trans sizeA.symm
  have hU : (A \ B).Nonempty := sdiff_nonempty.2 fun h ↦ hAB <| eq_of_subset_of_card_le h hAB'.ge
  have hV : (B \ A).Nonempty :=
    sdiff_nonempty.2 fun h ↦ hAB.symm <| eq_of_subset_of_card_le h hAB'.le
  have disj : Disjoint (B \ A) (A \ B) := disjoint_sdiff.mono_left sdiff_subset
  have smaller : max' _ hV < max' _ hU := by
    obtain hlt | heq | hgt := lt_trichotomy (max' _ hU) (max' _ hV)
    · rw [← compress_sdiff_sdiff A B] at hAB hBA
      cases hBA.not_lt <| toColex_compress_lt_toColex hlt hAB
    · exact (disjoint_right.1 disj (max'_mem _ hU) <| heq.symm ▸ max'_mem _ _).elim
    · assumption
  refine hB ?_
  rw [← (h₂ _ _ ⟨disj, card_sdiff_comm hAB'.symm, hV, hU, smaller⟩).eq]
  exact mem_compression.2 (Or.inr ⟨hB, A, hA, compress_sdiff_sdiff _ _⟩)

attribute [-instance] Fintype.decidableForallFintype

/-- This measures roughly how compressed the family is.

Note that this does depend on the order of the ground set, unlike the Kruskal-Katona theorem itself
(although `kruskal_katona` currently is stated in an order-dependent manner). -/
private def familyMeasure (𝒜 : Finset (Finset (Fin n))) : ℕ := ∑ A in 𝒜, ∑ a in A, 2 ^ (a : ℕ)

/-- Applying a compression strictly decreases the measure. This helps show that "compress until we
can't any more" is a terminating process. -/
private lemma familyMeasure_compression_lt_familyMeasure {U V : Finset (Fin n)} {hU : U.Nonempty}
    {hV : V.Nonempty} (h : max' U hU < max' V hV) {𝒜 : Finset (Finset (Fin n))} (a : 𝓒 U V 𝒜 ≠ 𝒜) :
    familyMeasure (𝓒 U V 𝒜) < familyMeasure 𝒜 := by
  rw [compression] at a ⊢
  have q : ∀ Q ∈ 𝒜.filter fun A ↦ compress U V A ∉ 𝒜, compress U V Q ≠ Q := by
    simp_rw [mem_filter]
    intro Q hQ h
    rw [h] at hQ
    exact hQ.2 hQ.1
  have uA : (𝒜.filter fun A => compress U V A ∈ 𝒜) ∪ 𝒜.filter (fun A ↦ compress U V A ∉ 𝒜) = 𝒜 :=
    filter_union_filter_neg_eq _ _
  have ne₂ : (𝒜.filter fun A ↦ compress U V A ∉ 𝒜).Nonempty := by
    refine nonempty_iff_ne_empty.2 fun z ↦ a ?_
    rw [filter_image, z, image_empty, union_empty]
    rwa [z, union_empty] at uA
  rw [familyMeasure, familyMeasure, sum_union compress_disjoint]
  conv_rhs => rw [← uA]
  rw [sum_union (disjoint_filter_filter_neg _ _ _), add_lt_add_iff_left, filter_image,
    sum_image compress_injOn]
  refine sum_lt_sum_of_nonempty ne₂ fun A hA ↦ ?_
  simp_rw [← sum_image Fin.val_injective.injOn]
  rw [geomSum_lt_geomSum_iff_toColex_lt_toColex le_rfl,
    toColex_image_lt_toColex_image Fin.val_strictMono]
  exact toColex_compress_lt_toColex h <| q _ hA

/-- The main Kruskal-Katona helper: use induction with our measure to keep compressing until
we can't any more, which gives a set family which is fully compressed and has the nice properties we
want. -/
private lemma kruskal_katona_helper {r : ℕ} (𝒜 : Finset (Finset (Fin n)))
    (h : (𝒜 : Set (Finset (Fin n))).Sized r) :
    ∃ ℬ : Finset (Finset (Fin n)), (∂ ℬ).card ≤ (∂ 𝒜).card ∧ 𝒜.card = ℬ.card ∧
      (ℬ : Set (Finset (Fin n))).Sized r ∧ ∀ U V, UsefulCompression U V → IsCompressed U V ℬ := by
  classical
  -- Are there any compressions we can make now?
  set usable : Finset (Finset (Fin n) × Finset (Fin n)) :=
    univ.filter fun t ↦ UsefulCompression t.1 t.2 ∧ ¬ IsCompressed t.1 t.2 𝒜
  obtain husable | husable := usable.eq_empty_or_nonempty
  -- No. Then where we are is the required set family.
  · refine ⟨𝒜, le_rfl, rfl, h, fun U V hUV ↦ ?_⟩
    rw [eq_empty_iff_forall_not_mem] at husable
    by_contra h
    exact husable ⟨U, V⟩ <| mem_filter.2 ⟨mem_univ _, hUV, h⟩
  -- Yes. Then apply the smallest compression, then keep going
  obtain ⟨⟨U, V⟩, hUV, t⟩ := exists_min_image usable (fun t ↦ t.1.card) husable
  rw [mem_filter] at hUV
  have h₂ : ∀ U₁ V₁, UsefulCompression U₁ V₁ → U₁.card < U.card → IsCompressed U₁ V₁ 𝒜 := by
    rintro U₁ V₁ huseful hUcard
    by_contra h
    exact hUcard.not_le <| t ⟨U₁, V₁⟩ <| mem_filter.2 ⟨mem_univ _, huseful, h⟩
  have p1 : (∂ (𝓒 U V 𝒜)).card ≤ (∂ 𝒜).card := compression_improved _ hUV.2.1 h₂
  obtain ⟨-, hUV', hu, hv, hmax⟩ := hUV.2.1
  have := familyMeasure_compression_lt_familyMeasure hmax hUV.2.2
  obtain ⟨t, q1, q2, q3, q4⟩ := UV.kruskal_katona_helper (𝓒 U V 𝒜) (h.uvCompression hUV')
  exact ⟨t, q1.trans p1, (card_compression _ _ _).symm.trans q2, q3, q4⟩
termination_by familyMeasure 𝒜

end UV

-- Finally we can prove Kruskal-Katona.
section KK
variable {r k i : ℕ} {𝒜 𝒞 : Finset <| Finset <| Fin n}

/-- The **Kruskal-Katona theorem**.

Given a set family `𝒜` consisting of `r`-sets, and `𝒞` an initial segment of the colex order of the
same size, the shadow of `𝒞` is smaller than the shadow of `𝒜`. In particular, this gives that the
minimum shadow size is achieved by initial segments of colex. -/
theorem kruskal_katona (h𝒜r : (𝒜 : Set (Finset (Fin n))).Sized r) (h𝒞𝒜 : 𝒞.card ≤ 𝒜.card)
    (h𝒞 : IsInitSeg 𝒞 r) : (∂ 𝒞).card ≤ (∂ 𝒜).card := by
  -- WLOG `|𝒜| = |𝒞|`
  obtain ⟨𝒜', h𝒜, h𝒜𝒞⟩ := exists_subset_card_eq h𝒞𝒜
  -- By `kruskal_katona_helper`, we find a fully compressed family `ℬ` of the same size as `𝒜`
  -- whose shadow is no bigger.
  obtain ⟨ℬ, hℬ𝒜, h𝒜ℬ, hℬr, hℬ⟩ := UV.kruskal_katona_helper 𝒜' (h𝒜r.mono (by gcongr))
  -- This means that `ℬ` is an initial segment of the same size as `𝒞`. Hence they are equal and
  -- we are done.
  suffices ℬ = 𝒞 by subst 𝒞; exact hℬ𝒜.trans (by gcongr)
  have hcard : card ℬ = card 𝒞 := h𝒜ℬ.symm.trans h𝒜𝒞
  obtain h𝒞ℬ | hℬ𝒞 := h𝒞.total (UV.isInitSeg_of_compressed hℬr hℬ)
  · exact (eq_of_subset_of_card_le h𝒞ℬ hcard.le).symm
  · exact eq_of_subset_of_card_le hℬ𝒞 hcard.ge

/-- An iterated form of the Kruskal-Katona theorem. In particular, the minimum possible iterated
shadow size is attained by initial segments. -/
theorem iterated_kk (h₁ : (𝒜 : Set (Finset (Fin n))).Sized r) (h₂ : 𝒞.card ≤ 𝒜.card)
    (h₃ : IsInitSeg 𝒞 r) : (∂^[k] 𝒞).card ≤ (∂^[k] 𝒜).card := by
  induction k generalizing r 𝒜 𝒞 with
  | zero => simpa
  | succ _ ih =>
    refine ih h₁.shadow (kruskal_katona h₁ h₂ h₃) ?_
    convert h₃.shadow

end KK
end Finset
