/-
Copyright (c) 2026 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.SetTheory.Cardinal.Pigeonhole

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

* Prove that `Δ(θ, κ)` is equivalent to `∀ c < θ, c ^< κ < θ` for any regular cardinal `θ` and
  infinite cardinal `κ < θ`. (See <https://mathoverflow.net/questions/130879>.)
* Prove that `Δ(θ, κ)` does not hold for singluar `θ`.

## References

* [Kenneth Kunen, *Set Theory: An Introduction to Independence Proofs.*][kunen1980set]
-/

@[expose] public section

universe u v

namespace Cardinal

/-- For cardinals `θ` and `κ`, the Δ-system property says any `θ`-sized family of sets whose
cardinalities are less than `κ` must contain a `θ`-sized Δ-system. Also noted as `Δ(θ, κ)`. -/
def DeltaSystemProperty (θ κ : Cardinal.{u}) :=
  ∀ ι α (f : ι → Set α), #ι = θ → (∀ i, #(f i) < κ) →
    ∃ (s : Set ι) (t : Set α), #s = θ ∧ s.Pairwise (f · ∩ f · = t) 

variable {θ κ : Cardinal.{u}}

open Order Ordinal Set

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

variable (h : κ < θ) (hκ : ℵ₀ ≤ κ) (hθ : θ.IsRegular) (hθ' : ∀ c < θ, c ^< κ < θ)

include h hκ hθ hθ' in
private lemma delta_system_property_aux {ι : Type u} {ρ : Ordinal.{u}} {f : ι → Set θ.ord.ToType}
    (hι : θ ≤ #ι) (hf : ∀ i, #(f i) < κ) (hρ : ρ < κ.ord) (hρ' : ∀ i, typeLT (f i) = ρ) :
    ∃ (s : Set ι) (t : Set θ.ord.ToType), θ ≤ #s ∧ s.Pairwise (f · ∩ f · = t) := by
  classical
  rcases (zero_le ρ).eq_or_lt with rfl | hρ''
  · simp only [type_eq_zero_iff_isEmpty, isEmpty_coe_sort] at hρ'
    exact ⟨Set.univ, ∅, by simpa, by simp [hρ', Set.Pairwise]⟩
  simp_rw [← type_toType ρ, type_eq] at hρ'
  have g₁ : ∀ i, ρ.ToType ≃o f i := fun i => OrderIso.ofRelIsoLT (Classical.choice (hρ' i)).symm
  haveI : Nonempty θ.ord.ToType := by simpa using ((zero_le κ).trans_lt h).ne'
  letI := WellFoundedLT.toOrderBot (α := θ.ord.ToType)
  letI := WellFoundedLT.conditionallyCompleteLinearOrderBot θ.ord.ToType
  by_cases hξ₀ : ∀ ξ : ρ.ToType, Bounded (· < ·) {(g₁ i ξ).1 | i}
  · simp only [Bounded, mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at hξ₀
    choose b hb using hξ₀
    have : BddAbove (range b) := by
      rw [bddAbove_def]
      refine ⟨Ordinal.ToType.mk ⟨⨆ x, (b x).toOrd.1, ?_⟩, ?_⟩
      · rw [mem_Iio]
        apply iSup_lt_ord_of_isRegular hθ
        · simpa [← lt_ord] using hρ.trans (ord_lt_ord.2 h)
        · exact fun i => (b i).toOrd.2
      · simp only [mem_range, forall_exists_index, forall_apply_eq_imp_iff,
          ← ToType.mk.symm_apply_le, ← Subtype.coe_le_coe]
        exact le_ciSup (Ordinal.bddAbove_of_small _)
    let b₀ := iSup b
    have : ∀ i, Subtype.val '' range (g₁ i) ⊆ Iio b₀ := by
      intro i x hx
      simp only [mem_image, mem_range, ↓existsAndEq, true_and] at hx
      rcases hx with ⟨x, rfl⟩
      exact (hb _ _).trans_le <| le_ciSup this x
    simp_rw [← OrderIso.coe_toEquiv, Equiv.range_eq_univ, image_univ, Subtype.range_val] at this
    have : #(range f) < θ := by
      apply (mk_range_le_powerlt κ (Iio b₀) this hf).trans_lt
      rw [mul_eq_max_of_aleph0_le_left hκ]
      · simp only [sup_lt_iff, h, true_and]
        apply hθ'
        simp only [sup_lt_iff, hκ.trans_lt h, and_true]
        exact mk_Iio_ord_toType _
      · simpa [powerlt_eq_zero_iff] using (aleph0_pos.trans_le hκ).ne'
    rcases infinite_pigeonhole_card_range f θ hι hθ.aleph0_le (by rwa [hθ.cof_eq]) with ⟨t, ht⟩
    refine ⟨_, t, ht, ?_⟩
    grind [Set.Pairwise]
  haveI : Nonempty ρ.ToType := by simpa using hρ''.ne'
  letI := Classical.inhabited_of_nonempty (α := ρ.ToType) inferInstance
  letI := WellFoundedLT.toOrderBot (α := ρ.ToType)
  letI := WellFoundedLT.conditionallyCompleteLinearOrderBot ρ.ToType
  let ξ₀ : ρ.ToType := sInf {ξ : ρ.ToType | Unbounded (· < ·) {(g₁ i ξ).1 | (i : ι)}}
  replace hξ₀ : Unbounded (· < ·) {(g₁ i ξ₀).1 | i} := by
    simp_rw [not_forall, not_bounded_iff] at hξ₀
    apply csInf_mem (s := {ξ | Unbounded (· < ·) {(g₁ i ξ).1 | i}})
    simpa [nonempty_def]
  have hξ₀' : ∀ ξ < ξ₀, Bounded (· < ·) {(g₁ i ξ).1 | (i : ι)} := by
    intro ξ hξ
    apply notMem_of_lt_csInf' at hξ
    simpa using hξ
  choose! α hα using hξ₀'
  simp only [mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at hα
  let α₀ := ⨆ ξ : Iio ξ₀, α ξ
  haveI : NoMaxOrder (θ.ord.ToType) := noMaxOrder hθ.aleph0_le
  have hα₀ : ∀ i, ∀ ξ < ξ₀, g₁ i ξ < α₀ := by
    intro i ξ hξ
    rw [← succ_le_iff]
    refine le_ciSup_of_le ?_ ⟨ξ, hξ⟩ ?_
    · refine ⟨Ordinal.ToType.mk ⟨⨆ ξ : Iio ξ₀, α ξ, ?_⟩, ?_⟩
      · rw [mem_Iio]
        apply iSup_lt_ord_of_isRegular hθ
        · apply (mk_set_le _).trans_lt
          apply h.trans'
          simpa [← lt_ord]
        · exact fun i => (α i).toOrd.2
      · simp only [mem_upperBounds, mem_range, Subtype.exists, mem_Iio, exists_prop,
          ← ToType.mk.symm_apply_le, ← Subtype.coe_le_coe, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂]
        intro ξ hξ
        exact le_ciSup (Ordinal.bddAbove_range _) (⟨ξ, hξ⟩ : Iio ξ₀)
    · rw [succ_le_iff]
      exact hα ξ hξ i
  haveI : Nonempty ι := by simpa [← mk_ne_zero_iff] using hθ.pos.trans_le hι |>.ne'
  let g₂ : θ.ord.ToType → ι := WellFoundedLT.fix fun x ih =>
    Classical.epsilon fun i => α₀ < g₁ i ξ₀ ∧ ∀ y hy ξ, (g₁ (ih y hy) ξ).1 < g₁ i ξ₀
  have hg₂ : ∀ μ, α₀ < g₁ (g₂ μ) ξ₀ ∧ ∀ ν < μ, ∀ ξ, (g₁ (g₂ ν) ξ).1 < g₁ (g₂ μ) ξ₀ := by
    intro μ
    suffices ∃ i, α₀ < g₁ i ξ₀ ∧ ∀ ν < μ, ∀ ξ, (g₁ (g₂ ν) ξ).1 < g₁ i ξ₀ by
      apply Classical.epsilon_spec at this
      unfold g₂
      rwa [WellFoundedLT.fix_eq]
    let o : Ordinal := succ (max α₀ (⨆ ν : Iio μ, ⨆ ξ, g₁ (g₂ ν) ξ))
    have ho : o < θ.ord := by
      apply (Cardinal.isSuccLimit_ord hθ.aleph0_le).succ_lt
      refine max_lt α₀.toOrd.2 ?_
      apply iSup_lt_ord_of_isRegular hθ
      · apply mk_Iio_ord_toType
      · intro
        apply iSup_lt_ord_of_isRegular hθ
        · apply h.trans'
          simpa [← lt_ord]
        · exact fun _ => (Ordinal.ToType.toOrd _).2
    rcases hξ₀ (Ordinal.ToType.mk ⟨o, ho⟩) with ⟨_, ⟨i, rfl⟩, hi⟩
    simp only [not_lt, ← ToType.mk.le_symm_apply, ← Subtype.coe_le_coe, succ_le_iff, sup_lt_iff,
      Subtype.coe_lt_coe, OrderIso.lt_iff_lt, o] at hi
    rcases hi with ⟨hi₁, hi₂⟩
    refine ⟨i, hi₁, fun ν hν ξ => ?_⟩
    rw [← ToType.mk.symm.lt_iff_lt]
    apply hi₂.trans_le'
    exact le_ciSup_of_le (Ordinal.bddAbove_range _) ⟨ν, hν⟩ <|
      le_ciSup_of_le (Ordinal.bddAbove_range _) ξ le_rfl
  have hg₂' : Function.Injective g₂ := by
    intro x y h
    by_contra! h'
    rcases lt_or_gt_of_ne h' with h' | h'
    · have := (hg₂ _).2 _ h' ξ₀
      rw [h] at this
      simp at this
    · have := (hg₂ _).2 _ h' ξ₀
      rw [h] at this
      simp at this
  have hg₂'' : ∀ x y, x ≠ y → f (g₂ x) ∩ f (g₂ y) ⊆ Iio α₀ := by
    intro x y h
    wlog h' : x < y generalizing x y
    · rw [inter_comm]
      exact this _ _ h.symm (lt_of_le_of_ne (le_of_not_gt h') h.symm)
    intro z
    simp only [mem_inter_iff, mem_Iio, and_imp]
    intro hzx hzy
    by_contra hz
    let ξx := (g₁ (g₂ x)).symm ⟨z, hzx⟩
    let ξy := (g₁ (g₂ y)).symm ⟨z, hzy⟩
    have hξy : ξ₀ ≤ ξy := by
      by_contra!
      apply hα₀ (g₂ y) at this
      simp only [OrderIso.apply_symm_apply, ξy] at this
      contradiction
    simp only [(g₁ (g₂ y)).le_symm_apply, ← Subtype.coe_le_coe, ξy] at hξy
    apply ((hg₂ _).2 _ h' ξx).trans_le at hξy
    simp [ξx] at hξy
  let g₃ : θ.ord.ToType → Set θ.ord.ToType := fun x => f (g₂ x) ∩ Set.Iio α₀
  have hg₃ : ∀ x, g₃ x ⊆ Set.Iio α₀ := by simp [g₃]
  have hg₃' : #(Set.range g₃) < θ := by
    refine (mk_range_le_powerlt κ (Iio α₀) hg₃ ?_).trans_lt ?_
    · intro i
      refine (mk_le_mk_of_subset ?_).trans_lt (hf (g₂ i))
      grind
    · rw [mul_eq_max_of_aleph0_le_left hκ]
      · apply max_lt h
        apply hθ'
        apply max_lt
        · exact mk_Iio_ord_toType _
        · exact hκ.trans_lt h
      · simp [powerlt_eq_zero_iff, (aleph0_pos.trans_le hκ).ne']
  rcases infinite_pigeonhole_card_range g₃ θ (by rw [mk_ord_toType]) hθ.aleph0_le
    (by rwa [hθ.cof_eq]) with ⟨r, hr⟩
  refine ⟨g₂ '' (g₃ ⁻¹' {r}), r, ?_, ?_⟩
  · rwa [mk_image_eq hg₂']
  · apply Pairwise.image
    intro x hx y hy hxy
    simp only [mem_preimage, mem_singleton_iff, g₃] at hx hy
    simpa [← inter_inter_distrib_right, inter_self, inter_eq_left.2 (hg₂'' x y hxy)]
      using congr_arg₂ (· ∩ ·) hx hy

include h hκ hθ hθ' in
/-- **Δ-system lemma**: `Δ(θ, κ)` holds for any regular cardinal `θ` and infinite cardinal `κ < θ`
such that `∀ c < θ, c ^< κ < θ`. -/
theorem delta_system_property_of_powerlt_lt : DeltaSystemProperty θ κ := by
  intro ι α f hι hf
  haveI : Nonempty ι := by
    simpa [mk_ne_zero_iff] using (aleph0_pos.trans_le hκ |>.trans h |>.trans_le hι.ge).ne'
  have : #(⋃ i, f i) ≤ θ := by
    refine mk_iUnion_le_sum_mk.trans <| (sum_le_mk_mul_iSup _).trans <|
      (mul_le_mul_right (ciSup_mono (bddAbove_of_small _) fun i => (hf i).le) _).trans ?_
    rw [ciSup_const,
      mul_eq_left (hκ.trans h.le |>.trans hι.ge) (h.le.trans hι.ge) (aleph0_pos.trans_le hκ).ne',
      hι]
  rw [← card_ord θ, ← mk_toType, le_def] at this
  rcases this with ⟨g⟩
  let g' : ι → Set θ.ord.ToType := fun i =>
    Set.range ((Set.embeddingOfSubset _ _ (Set.subset_iUnion f i)).trans g)
  have hg : ∀ i, #(g' i) < κ := fun i => mk_range_le.trans_lt (hf i)
  have hg' : ∀ i, typeLT (g' i) < κ.ord := by simpa [lt_ord, card_type]
  rcases infinite_pigeonhole_card (fun i => Ordinal.ToType.mk ⟨typeLT (g' i), hg' i⟩) _ hι.ge
    (hκ.trans h.le) (by rwa [mk_ord_toType, hθ.cof_eq]) with ⟨ρ, hs⟩
  generalize hρ : (_ ⁻¹' {ρ}) = s at hs
  have : ∃ ρ', ρ = Ordinal.ToType.mk ρ' := ⟨ρ.toOrd, by simp⟩
  rcases this with ⟨⟨ρ, hρ'⟩, rfl⟩
  simp only [mem_Iio] at hρ'
  apply (subset_of_eq ∘ Eq.symm) at hρ
  simp_rw [subset_def, mem_preimage, mem_singleton_iff, ToType.mk.eq_iff_eq, Subtype.mk_eq_mk]
    at hρ
  rcases delta_system_property_aux (ι := s) (f := g' ∘ Subtype.val) h hκ hθ hθ' hs (by grind) hρ'
    (by grind) with ⟨s', t, hs', ht⟩
  refine ⟨Subtype.val '' s', Subtype.val '' (g ⁻¹' t), ?_, ?_⟩
  · rw [mk_image_eq Subtype.val_injective]
    refine hs'.antisymm' <| (mk_set_le _).trans <| (mk_set_le _).trans ?_
    rw [hι]
  · refine .image (ht.imp fun x y h => ?_)
    simp only [Function.comp_apply] at h
    rw [Function.onFun_apply, ← h, preimage_inter, image_inter Subtype.val_injective]
    congr <;> ext i <;> simp only [embeddingOfSubset, mem_image, mem_preimage, mem_range,
      Function.Embedding.trans_apply, Function.Embedding.coeFn_mk, Subtype.exists, g'] <;> grind

include hθ in
/-- `Δ(θ, ℵ₀)` holds for any uncountable regular cardinal `θ`. -/
theorem delta_system_property_aleph0 (hθ' : ℵ₀ < θ) : DeltaSystemProperty θ ℵ₀ := by
  apply delta_system_property_of_powerlt_lt hθ' le_rfl hθ
  intro c hc
  apply (powerlt_aleph0_le _).trans_lt
  simp [hc, hθ']

include hθ in
/-- **Δ-system lemma** for `Δ(θ, ℵ₀)`: for any uncountable regular cardinal `θ`, any `θ`-sized
family of finite sets must contain a `θ`-sized Δ-system. -/
theorem exists_pairwise_inter_eq_finset (hθ' : ℵ₀ < θ) {ι : Type u} {α : Type v} [DecidableEq α]
    (f : ι → Finset α) (hι : θ ≤ #ι) :
    ∃ (s : Set ι) (t : Finset α), #s = θ ∧ s.Pairwise (f · ∩ f · = t) := by
  rcases (delta_system_property_aleph0 hθ.lift (aleph0_lt_lift.{u, v}.2 hθ')).exists_pairwise_eq
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
  rcases isRegular_aleph_one.exists_pairwise_inter_eq_finset aleph0_lt_aleph_one f
    (by simp [← succ_aleph0]) with ⟨s, t, hs, ht⟩
  refine ⟨s, t, ?_, ht⟩
  simpa [← aleph0_lt_mk_iff, hs] using aleph0_lt_aleph_one
