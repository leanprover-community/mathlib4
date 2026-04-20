/-
Copyright (c) 2026 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.SetTheory.Cardinal.Regular

import Mathlib.Order.Club
import Mathlib.Order.CompleteLatticeIntervals

/-!
# Δ-systems

A family of sets forms a Δ-system if they share the same pairwise intersection. This file proves the
Δ-system lemma, which says for any regular cardinal `θ` and infinite cardinal `κ < θ`, if
`∀ c < θ, c ^< κ < θ`, any `θ`-sized family of sets whose cardinalities are less than `κ` must
contain a `θ`-sized Δ-system (this condition is called Δ-system property for `θ` and `κ`, noted as
`Δ(θ, k)`). As a special case, `Δ(ℵ₁, ℵ₀)` ensures any uncountable family of finite sets must
contain an uncountable Δ-system.

## Main statements

* `Cardinal.IsRegular.delta_system_property_of_powerlt_lt`: Δ-system lemma for any regular cardinal
  `θ` and infinite cardinal `κ < θ`.
* `Cardinal.IsRegular.exists_pairwise_inter_eq_finset` and
  `Uncountable.exists_pairwise_inter_eq_finset`: Δ-system lemma specialized for families
  of finite sets.

## TODO

* Prove that `Δ(θ, κ)` is equivalent to `∀ c < θ, c ^< κ < θ` for any regular `θ` and infinite
  `κ < θ`. (See <https://mathoverflow.net/questions/130879>.)
* Prove that `Δ(θ, κ)` does not hold for singluar `θ`.

## References

* [Kenneth Kunen, *Set Theory: An Introduction to Independence Proofs.*][kunen1980set]
* [Kenneth Kunen, *Set Theory.*][kunen2011set]
-/

@[expose] public section

universe u v

namespace Cardinal

/-- For cardinals `θ` and `κ`, the Δ-system property says any `θ`-sized family of sets whose
cardinalities are less than `κ` must contain a `θ`-sized Δ-system. Also noted as `Δ(θ, κ)`. -/
def DeltaSystemProperty (θ κ : Cardinal.{u}) :=
  ∀ ι α (f : ι → Set α), #ι = θ → (∀ i, #(f i) < κ) →
    ∃ (s : Set ι) (t : Set α), #s = θ ∧ s.Pairwise (f · ∩ f · = t)

variable {θ κ μ : Cardinal.{u}}

open Order Ordinal Set

@[gcongr]
theorem DeltaSystemProperty.mono (h : κ ≤ μ) (hμ : DeltaSystemProperty θ μ) :
    DeltaSystemProperty θ κ :=
  fun ι α f hι hf => hμ ι α f hι fun i => (hf i).trans_le h

/-- An alternative formalization of Δ-system property, with weaker assumption and stronger
conclusion. -/
theorem DeltaSystemProperty.exists_pairwise_eq (h : DeltaSystemProperty θ κ) (hκ : 0 < κ)
    {ι α : Type u} {f : ι → Set α} (hι : θ ≤ #ι) (hf : ∀ i, #(f i) < κ) :
    ∃ (s : Set ι) (t : Set α), #s = θ ∧ #t < κ ∧ s.Pairwise (f · ∩ f · = t) := by
  rw [le_mk_iff_exists_set] at hι
  rcases hι with ⟨s, hs⟩
  rcases h s α (f ∘ Subtype.val) hs (by grind) with ⟨s', t, hs', ht⟩
  rcases s'.subsingleton_or_nontrivial with hs'' | ⟨x, hx, y, hy, hxy⟩
  · exact ⟨s', ∅, by rwa [mk_image_eq Subtype.val_injective], by simpa, .image <| hs''.pairwise _⟩
  · refine ⟨s', t, by rwa [mk_image_eq Subtype.val_injective], ?_, .image ht⟩
    rw [← ht hx hy hxy]
    exact (mk_le_mk_of_subset inter_subset_left).trans_lt (hf _)

namespace IsRegular

private lemma deltaSystemProperty_aux (hκμ : κ ≤ μ) (hμθ : μ < θ) (hκ : ℵ₀ ≤ κ) (hμ : μ.IsRegular)
    (hθ : θ.IsRegular) (hθ' : ∀ c < θ, c ^< κ < θ) {f : Iio θ.ord → Set (Iio θ.ord)}
    (hf : ∀ i, #(f i) < Cardinal.lift.{u + 1} κ) :
    ∃ (s : Set (Iio θ.ord)) (t : Set (Iio θ.ord)),
      #s = Cardinal.lift.{u + 1} θ ∧ s.Pairwise (f · ∩ f · = t) := by
  haveI : Nonempty (Iio θ.ord) := ⟨0, by simp [hθ.pos]⟩
  haveI : NoMaxOrder (Iio θ.ord) := noMaxOrder_Iio_ord hθ.aleph0_le
  haveI : Fact (¬ IsMin θ.ord) := ⟨by simp [← pos_iff_ne_zero, hθ.pos]⟩
  have : ℵ₀ < Order.cof (Iio θ.ord) := by
    simpa [← lift_ord, ← lift_cof, hθ.cof_ord] using hμ.aleph0_le.trans_lt hμθ
  have : typeLT (Iio θ.ord) ≤ (Order.cof (Iio θ.ord)).ord := by
    simp [← lift_ord, ← lift_cof, hθ.cof_ord]
  rcases exists_isStationary_preimage_singleton (f := fun i => sSup (Set.Iio i ∩ f i))
    (by assumption) (by assumption) (hθ.isStationary_setOf_cof_eq hμ hμθ)
    (by
      intro ⟨i, hi⟩
      simp only [mem_setOf_eq, gt_iff_lt] at hi ⊢
      rw [← Subtype.coe_lt_coe, Iio.coe_sSup (bddAbove_Iio.mono inter_subset_left)]
      apply Ordinal.sSup_lt_of_lt_cof
      · grw [mk_image_eq Subtype.val_injective, mk_le_mk_of_subset inter_subset_right]
        apply (hf i).trans_le
        simpa [← lift_cof, hi]
      · simp +contextual [← Subtype.coe_lt_coe]) with ⟨ξ, hξ⟩
  have : ∃ ν : Iio θ.ord, ξ < ν := by
    rcases (isSuccLimit_ord hθ.aleph0_le).lt_iff_exists_lt.1 ξ.2 with ⟨ν, hν, hν'⟩
    exact ⟨⟨ν, hν⟩, hν'⟩
  rcases this with ⟨ν, hν⟩
  rcases exists_isStationary_preimage_singleton_of_cardinalMk_range_lt_cof
    (f := fun i => f i ∩ Iio ν) (by assumption)
    (hξ.inter_isClub (by assumption)
      (isClub_almost_fixed_points (f := sSup ∘ f) (by assumption) (by assumption)))
    (by
      grw [mk_range_le_powerlt (Cardinal.lift.{u + 1} κ) (Iio ν)]
      · rw [mk_Iio_Iio_ord_eq, ← lift_aleph0.{u + 1, u}]
        simp only [← lift_max, ← lift_powerlt, ← lift_mul, Ordinal.cof_Iio, ← lift_cof, lift_lt]
        rw [hθ.cof_ord, mul_eq_max_of_aleph0_le_left hκ]
        · refine max_lt (hκμ.trans_lt hμθ) (hθ' _ (max_lt ?_ (hμ.aleph0_le.trans_lt hμθ)))
          rw [← lt_ord]
          exact ν.2
        · simpa [powerlt_eq_zero_iff] using pos_iff_ne_zero.1 (aleph0_pos.trans_le hκ)
      · grind
      · exact fun i => (mk_le_mk_of_subset inter_subset_left).trans_lt (hf _)) with ⟨w, hw⟩
  refine ⟨_, w, hθ.card_eq_of_isStationary hw, ?_⟩
  intro i hi j hj hij
  wlog hij' : i < j generalizing i j
  · rw [inter_comm]
    exact this hj hi hij.symm (lt_of_le_of_ne (le_of_not_gt hij') hij.symm)
  simp only [mem_setOf_eq, coe_setOf, Function.comp_apply, mem_image, mem_preimage,
    mem_singleton_iff, Subtype.exists, mem_inter_iff, exists_and_left, exists_prop,
    exists_eq_right_right] at hi hj
  rcases hi with ⟨hi₁, ⟨-, hi₃⟩, hi₄⟩
  rcases hj with ⟨hj₁, ⟨hj₂, hj₃⟩, hj₄⟩
  nth_rw 1 [← inter_self w, ← hi₁, ← hj₁, ← inter_inter_distrib_right,
    inter_eq_self_of_subset_left (t := Iio ν)]
  intro x hx
  simp only [mem_inter_iff, mem_Iio] at hx ⊢
  apply hν.trans_le'
  rw [← hj₂]
  apply le_csSup (bddAbove_Iio.mono inter_subset_left)
  simp only [mem_inter_iff, mem_Iio, hx.2, and_true]
  apply (hj₄ _ hij').trans_le'
  refine le_csSup (bddAbove_Iio_of_lt_cof ?_) hx.1
  grw [hf]
  simpa [hθ.cof_ord] using hκμ.trans_lt hμθ

/-- **Δ-system lemma**: `Δ(θ, κ)` holds for any regular cardinal `θ` and infinite cardinal `κ < θ`
such that `∀ c < θ, c ^< κ < θ`. -/
theorem deltaSystemProperty_of_powerlt_lt (h : κ < θ) (hκ : ℵ₀ ≤ κ) (hθ : θ.IsRegular)
    (hθ' : ∀ c < θ, c ^< κ < θ) : DeltaSystemProperty θ κ := by
  intro ι α f hι hf
  have : ∃ μ ≥ κ, μ < θ ∧ μ.IsRegular := by
    rcases lt_or_eq_of_le (cof_ord_le κ) with hκ' | hκ'
    · refine ⟨Order.succ κ, Order.le_succ _, ?_, isRegular_succ hκ⟩
      apply (hθ' _ h).trans_le'
      rw [Order.succ_le_iff]
      apply (lt_power_cof_ord hκ).trans_le
      exact le_powerlt _ hκ'
    · exact ⟨κ, le_rfl, h, hκ, hκ'.ge⟩
  rcases this with ⟨μ, hμ, hμ', hμ''⟩
  haveI : Nonempty ι := by simp [← mk_ne_zero_iff, hι, ← pos_iff_ne_zero, hθ.pos]
  have : #(⋃ i, f i) ≤ θ := by
    refine mk_iUnion_le_sum_mk.trans <| (sum_le_mk_mul_iSup _).trans <|
      (mul_le_mul_right (ciSup_mono bddAbove_of_small fun i => (hf i).le) _).trans ?_
    rw [ciSup_const,
      mul_eq_left (hκ.trans h.le |>.trans hι.ge) (h.le.trans hι.ge) (aleph0_pos.trans_le hκ).ne',
      hι]
  rw [← card_ord θ, ← Cardinal.lift_le, ← mk_Iio_ordinal, ← Cardinal.lift_id #(Iio θ.ord),
    Cardinal.lift_mk_le.{u + 1}] at this
  rcases this with ⟨g⟩
  rw [← Cardinal.lift_inj.{u, u + 1}, ← card_ord θ, ← mk_Iio_ordinal,
    ← Cardinal.lift_id #(Iio θ.ord), Cardinal.lift_mk_eq.{u, u + 1, u + 1}] at hι
  rcases hι with ⟨e⟩
  rcases deltaSystemProperty_aux
    (f := fun i => Set.range ((Set.embeddingOfSubset _ _ (Set.subset_iUnion f (e.symm i))).trans g))
    hμ hμ' hκ hμ'' hθ hθ' (fun _ => by
      rw [← Cardinal.lift_id'.{u, u + 1} #_,
        mk_range_eq_of_injective (Function.Embedding.injective _), Cardinal.lift_lt]
      apply hf) with ⟨s, t, hs, ht⟩
  refine ⟨e.symm '' s, Subtype.val '' (g ⁻¹' t), ?_, ?_⟩
  · rw [← Cardinal.lift_inj, mk_image_eq_of_injOn_lift _ _ e.symm.injective.injOn]
    simp [hs]
  · refine .image (ht.imp fun i j h => ?_)
    simp only [← h, preimage_inter, image_inter Subtype.val_injective, Function.onFun_apply]
    congr <;> ext i <;> simp only [embeddingOfSubset, mem_image, mem_preimage, mem_range,
      Function.Embedding.trans_apply, Function.Embedding.coeFn_mk, EmbeddingLike.apply_eq_iff_eq,
      Subtype.exists] <;> grind

/-- `Δ(θ, ℵ₀)` holds for any uncountable regular cardinal `θ`. -/
theorem deltaSystemProperty_aleph0 (hθ : θ.IsRegular) (hθ' : θ ≠ ℵ₀) :
    DeltaSystemProperty θ ℵ₀ := by
  replace hθ' := hθ.aleph0_le.lt_of_ne' hθ'
  apply deltaSystemProperty_of_powerlt_lt hθ' le_rfl hθ
  intro c hc
  apply (powerlt_aleph0_le _).trans_lt
  simp [hc, hθ']

/-- **Δ-system lemma** for `Δ(θ, ℵ₀)`: for any uncountable regular cardinal `θ`, any `θ`-sized
family of finite sets must contain a `θ`-sized Δ-system. -/
theorem exists_pairwise_inter_eq_finset (hθ : θ.IsRegular) (hθ' : θ ≠ ℵ₀) {ι : Type u} {α : Type v}
    [DecidableEq α] (f : ι → Finset α) (hι : θ ≤ #ι) :
    ∃ (s : Set ι) (t : Finset α), #s = θ ∧ s.Pairwise (f · ∩ f · = t) := by
  rcases (deltaSystemProperty_aleph0 hθ.lift (by simpa)).exists_pairwise_eq
    aleph0_pos (f := fun i : ULift.{v} ι => Equiv.ulift.symm '' (f i.down : Set α)) (by simpa)
    (by simp) with ⟨s, t, hs, ht, ht'⟩
  rw [lt_aleph0_iff_subtype_finite, setOf_mem_eq] at ht
  refine ⟨Equiv.ulift '' s, Equiv.ulift.finsetCongr ht.toFinset, ?_, ?_⟩
  · rw [← lift_inj.{u, v}, ← lift_umax, mk_image_eq_lift _ _ Equiv.ulift.injective, hs, lift_lift]
  · apply Pairwise.image
    convert ht'
    simp_rw [← Equiv.ulift.finsetCongr.symm_apply_eq]
    simp [Finset.map_inter, ← Finset.coe_inj]

end IsRegular

end Cardinal

open Cardinal

/-- **Δ-system lemma** for `Δ(ℵ₁, ℵ₀)`: any uncountable family of finite sets must contain an
uncountable Δ-system. -/
theorem Uncountable.exists_pairwise_inter_eq_finset {ι : Type u} {α : Type v}
    [Uncountable ι] [DecidableEq α] (f : ι → Finset α) :
    ∃ (s : Set ι) (t : Finset α), Uncountable s ∧ s.Pairwise (f · ∩ f · = t) := by
  rcases isRegular_aleph_one.exists_pairwise_inter_eq_finset aleph0_lt_aleph_one.ne' f (by simp)
    with ⟨s, t, hs, ht⟩
  refine ⟨s, t, ?_, ht⟩
  simp [← aleph0_lt_mk_iff, hs]
