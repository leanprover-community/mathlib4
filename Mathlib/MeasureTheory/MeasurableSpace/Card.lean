/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Violeta Hernández Palacios
-/
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Ordinal

/-!
# Cardinal of sigma-algebras

If a sigma-algebra is generated by a set of sets `s`, then the cardinality of the sigma-algebra is
bounded by `(max #s 2) ^ ℵ₀`. This is stated in `MeasurableSpace.cardinal_generate_measurable_le`
and `MeasurableSpace.cardinalMeasurableSet_le`.

In particular, if `#s ≤ 𝔠`, then the generated sigma-algebra has cardinality at most `𝔠`, see
`MeasurableSpace.cardinal_measurableSet_le_continuum`.

For the proof, we rely on an explicit inductive construction of the sigma-algebra generated by
`s` (instead of the inductive predicate `GenerateMeasurable`). This transfinite inductive
construction is parameterized by an ordinal `< ω₁`, and the cardinality bound is preserved along
each step of the construction. We show in `MeasurableSpace.generateMeasurable_eq_rec` that this
indeed generates this sigma-algebra.
-/


universe u v

variable {α : Type u}

open Cardinal Ordinal Set MeasureTheory

namespace MeasurableSpace

/-- Transfinite induction construction of the sigma-algebra generated by a set of sets `s`. At each
step, we add all elements of `s`, the empty set, the complements of already constructed sets, and
countable unions of already constructed sets.

We index this construction by an arbitrary ordinal for simplicity, but by `ω₁` we will have
generated all the sets in the sigma-algebra.

This construction is very similar to that of the Borel hierarchy. -/
def generateMeasurableRec (s : Set (Set α)) (i : Ordinal) : Set (Set α) :=
  let S := ⋃ j < i, generateMeasurableRec s j
  s ∪ {∅} ∪ compl '' S ∪ Set.range fun f : ℕ → S => ⋃ n, (f n).1
termination_by i

theorem self_subset_generateMeasurableRec (s : Set (Set α)) (i : Ordinal) :
    s ⊆ generateMeasurableRec s i := by
  unfold generateMeasurableRec
  apply_rules [subset_union_of_subset_left]
  exact subset_rfl

theorem empty_mem_generateMeasurableRec (s : Set (Set α)) (i : Ordinal) :
    ∅ ∈ generateMeasurableRec s i := by
  unfold generateMeasurableRec
  exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_singleton ∅)))

theorem compl_mem_generateMeasurableRec {s : Set (Set α)} {i j : Ordinal} (h : j < i) {t : Set α}
    (ht : t ∈ generateMeasurableRec s j) : tᶜ ∈ generateMeasurableRec s i := by
  unfold generateMeasurableRec
  exact mem_union_left _ (mem_union_right _ ⟨t, mem_iUnion₂.2 ⟨j, h, ht⟩, rfl⟩)

theorem iUnion_mem_generateMeasurableRec {s : Set (Set α)} {i : Ordinal} {f : ℕ → Set α}
    (hf : ∀ n, ∃ j < i, f n ∈ generateMeasurableRec s j) :
    ⋃ n, f n ∈ generateMeasurableRec s i := by
  unfold generateMeasurableRec
  exact mem_union_right _ ⟨fun n => ⟨f n, let ⟨j, hj, hf⟩ := hf n; mem_iUnion₂.2 ⟨j, hj, hf⟩⟩, rfl⟩

theorem generateMeasurableRec_mono (s : Set (Set α)) : Monotone (generateMeasurableRec s) := by
  intro i j h x hx
  rcases h.eq_or_lt with (rfl | h)
  · exact hx
  · convert iUnion_mem_generateMeasurableRec fun _ => ⟨i, h, hx⟩
    exact (iUnion_const x).symm

/-- An inductive principle for the elements of `generateMeasurableRec`. -/
@[elab_as_elim]
theorem generateMeasurableRec_induction {s : Set (Set α)} {i : Ordinal} {t : Set α}
    {p : Set α → Prop} (hs : ∀ t ∈ s, p t) (h0 : p ∅)
    (hc : ∀ u, p u → (∃ j < i, u ∈ generateMeasurableRec s j) → p uᶜ)
    (hn : ∀ f : ℕ → Set α,
      (∀ n, p (f n) ∧ ∃ j < i, f n ∈ generateMeasurableRec s j) → p (⋃ n, f n)) :
    t ∈ generateMeasurableRec s i → p t := by
  suffices H : ∀ k ≤ i, ∀ t ∈ generateMeasurableRec s k, p t from H i le_rfl t
  intro k
  apply WellFoundedLT.induction k
  intro k IH hk t
  replace IH := fun j hj => IH j hj (hj.le.trans hk)
  unfold generateMeasurableRec
  rintro (((ht | rfl) | ht) | ⟨f, rfl⟩)
  · exact hs t ht
  · exact h0
  · simp_rw [mem_image, mem_iUnion₂] at ht
    obtain ⟨u, ⟨⟨j, hj, hj'⟩, rfl⟩⟩ := ht
    exact hc u (IH j hj u hj') ⟨j, hj.trans_le hk, hj'⟩
  · apply hn
    intro n
    obtain ⟨j, hj, hj'⟩ := mem_iUnion₂.1 (f n).2
    use IH j hj _ hj', j, hj.trans_le hk

theorem generateMeasurableRec_omega1 (s : Set (Set α)) :
    generateMeasurableRec s (ω₁ : Ordinal.{v}) =
      ⋃ i < (ω₁ : Ordinal.{v}), generateMeasurableRec s i := by
  apply (iUnion₂_subset fun i h => generateMeasurableRec_mono s h.le).antisymm'
  intro t ht
  rw [mem_iUnion₂]
  refine generateMeasurableRec_induction ?_ ?_ ?_ ?_ ht
  · intro t ht
    exact ⟨0, omega_pos 1, self_subset_generateMeasurableRec s 0 ht⟩
  · exact ⟨0, omega_pos 1, empty_mem_generateMeasurableRec s 0⟩
  · rintro u - ⟨j, hj, hj'⟩
    exact ⟨_, (isLimit_omega 1).succ_lt hj,
      compl_mem_generateMeasurableRec (Order.lt_succ j) hj'⟩
  · intro f H
    choose I hI using fun n => (H n).1
    simp_rw [exists_prop] at hI
    refine ⟨_, Ordinal.lsub_lt_ord_lift ?_ fun n => (hI n).1,
      iUnion_mem_generateMeasurableRec fun n => ⟨_, Ordinal.lt_lsub I n, (hI n).2⟩⟩
    rw [mk_nat, lift_aleph0, isRegular_aleph_one.cof_omega_eq]
    exact aleph0_lt_aleph_one

theorem generateMeasurableRec_subset (s : Set (Set α)) (i : Ordinal) :
    generateMeasurableRec s i ⊆ { t | GenerateMeasurable s t } := by
  apply WellFoundedLT.induction i
  exact fun i IH t ht => generateMeasurableRec_induction .basic .empty
    (fun u _ ⟨j, hj, hj'⟩ => .compl _ (IH j hj hj')) (fun f H => .iUnion _ fun n => (H n).1) ht

/-- `generateMeasurableRec s ω₁` generates precisely the smallest sigma-algebra containing `s`. -/
theorem generateMeasurable_eq_rec (s : Set (Set α)) :
    { t | GenerateMeasurable s t } = generateMeasurableRec s ω₁ := by
  apply (generateMeasurableRec_subset s _).antisymm'
  intro t ht
  induction' ht with u hu u _ IH f _ IH
  · exact self_subset_generateMeasurableRec s _ hu
  · exact empty_mem_generateMeasurableRec s _
  · rw [generateMeasurableRec_omega1, mem_iUnion₂] at IH
    obtain ⟨i, hi, hi'⟩ := IH
    exact generateMeasurableRec_mono _ ((isLimit_omega 1).succ_lt hi).le
      (compl_mem_generateMeasurableRec (Order.lt_succ i) hi')
  · simp_rw [generateMeasurableRec_omega1, mem_iUnion₂, exists_prop] at IH
    exact iUnion_mem_generateMeasurableRec IH

/-- `generateMeasurableRec` is constant for ordinals `≥ ω₁`. -/
theorem generateMeasurableRec_of_omega1_le (s : Set (Set α)) {i : Ordinal.{v}} (hi : ω₁ ≤ i) :
    generateMeasurableRec s i = generateMeasurableRec s (ω₁ : Ordinal.{v}) := by
  apply (generateMeasurableRec_mono s hi).antisymm'
  rw [← generateMeasurable_eq_rec]
  exact generateMeasurableRec_subset s i

/-- At each step of the inductive construction, the cardinality bound `≤ #s ^ ℵ₀` holds. -/
theorem cardinal_generateMeasurableRec_le (s : Set (Set α)) (i : Ordinal.{v}) :
    #(generateMeasurableRec s i) ≤ max #s 2 ^ ℵ₀ := by
  suffices ∀ i ≤ ω₁, #(generateMeasurableRec s i) ≤ max #s 2 ^ ℵ₀ by
    obtain hi | hi := le_or_lt i ω₁
    · exact this i hi
    · rw [generateMeasurableRec_of_omega1_le s hi.le]
      exact this _ le_rfl
  intro i
  apply WellFoundedLT.induction i
  intro i IH hi
  have A : 𝔠 ≤ max #s 2 ^ ℵ₀ := power_le_power_right (le_max_right _ _)
  have B := aleph0_le_continuum.trans A
  have C : #(⋃ j < i, generateMeasurableRec s j) ≤ max #s 2 ^ ℵ₀ := by
    apply mk_iUnion_Ordinal_lift_le_of_le _ B _
    · intro j hj
      exact IH j hj (hj.trans_le hi).le
    · rw [lift_power, lift_aleph0]
      rw [← Ordinal.lift_le.{u}, lift_omega, Ordinal.lift_one, ← ord_aleph] at hi
      have H := card_le_of_le_ord hi
      rw [← Ordinal.lift_card] at H
      apply H.trans <| aleph_one_le_continuum.trans <| power_le_power_right _
      rw [lift_max, Cardinal.lift_ofNat]
      exact le_max_right _ _
  rw [generateMeasurableRec]
  apply_rules [(mk_union_le _ _).trans, add_le_of_le (aleph_one_le_continuum.trans A),
    mk_image_le.trans]
  · exact (self_le_power _ one_le_aleph0).trans (power_le_power_right (le_max_left _ _))
  · rw [mk_singleton]
    exact one_lt_aleph0.le.trans B
  · apply mk_range_le.trans
    simp only [mk_pi, prod_const, Cardinal.lift_uzero, mk_denumerable, lift_aleph0]
    have := @power_le_power_right _ _ ℵ₀ C
    rwa [← power_mul, aleph0_mul_aleph0] at this

/-- If a sigma-algebra is generated by a set of sets `s`, then the sigma-algebra has cardinality at
most `max #s 2 ^ ℵ₀`. -/
theorem cardinal_generateMeasurable_le (s : Set (Set α)) :
    #{ t | GenerateMeasurable s t } ≤ max #s 2 ^ ℵ₀ := by
  rw [generateMeasurable_eq_rec.{u, 0}]
  exact cardinal_generateMeasurableRec_le s _

/-- If a sigma-algebra is generated by a set of sets `s`, then the sigma
algebra has cardinality at most `max #s 2 ^ ℵ₀`. -/
theorem cardinal_measurableSet_le (s : Set (Set α)) :
    #{ t | @MeasurableSet α (generateFrom s) t } ≤ max #s 2 ^ ℵ₀ :=
  cardinal_generateMeasurable_le s

/-- If a sigma-algebra is generated by a set of sets `s` with cardinality at most the continuum,
then the sigma algebra has the same cardinality bound. -/
theorem cardinal_generateMeasurable_le_continuum {s : Set (Set α)} (hs : #s ≤ 𝔠) :
    #{ t | GenerateMeasurable s t } ≤ 𝔠 := by
  apply (cardinal_generateMeasurable_le s).trans
  rw [← continuum_power_aleph0]
  exact_mod_cast power_le_power_right (max_le hs (nat_lt_continuum 2).le)

/-- If a sigma-algebra is generated by a set of sets `s` with cardinality at most the continuum,
then the sigma algebra has the same cardinality bound. -/
theorem cardinal_measurableSet_le_continuum {s : Set (Set α)} :
    #s ≤ 𝔠 → #{ t | @MeasurableSet α (generateFrom s) t } ≤ 𝔠 :=
  cardinal_generateMeasurable_le_continuum

end MeasurableSpace
