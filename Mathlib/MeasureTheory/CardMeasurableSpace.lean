/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Violeta Hernández Palacios

! This file was ported from Lean 3 source module measure_theory.card_measurable_space
! leanprover-community/mathlib commit f2b108e8e97ba393f22bf794989984ddcc1da89b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.MeasurableSpaceDef
import Mathbin.SetTheory.Cardinal.Cofinality
import Mathbin.SetTheory.Cardinal.Continuum

/-!
# Cardinal of sigma-algebras

If a sigma-algebra is generated by a set of sets `s`, then the cardinality of the sigma-algebra is
bounded by `(max (#s) 2) ^ ℵ₀`. This is stated in `measurable_space.cardinal_generate_measurable_le`
and `measurable_space.cardinal_measurable_set_le`.

In particular, if `#s ≤ 𝔠`, then the generated sigma-algebra has cardinality at most `𝔠`, see
`measurable_space.cardinal_measurable_set_le_continuum`.

For the proof, we rely on an explicit inductive construction of the sigma-algebra generated by
`s` (instead of the inductive predicate `generate_measurable`). This transfinite inductive
construction is parameterized by an ordinal `< ω₁`, and the cardinality bound is preserved along
each step of the construction. We show in `measurable_space.generate_measurable_eq_rec` that this
indeed generates this sigma-algebra.
-/


universe u

variable {α : Type u}

open Cardinal

open Cardinal Set

-- mathport name: exprω₁
local notation "ω₁" => (aleph 1 : Cardinal.{u}).ord.out.α

namespace MeasurableSpace

/-- Transfinite induction construction of the sigma-algebra generated by a set of sets `s`. At each
step, we add all elements of `s`, the empty set, the complements of already constructed sets, and
countable unions of already constructed sets. We index this construction by an ordinal `< ω₁`, as
this will be enough to generate all sets in the sigma-algebra.

This construction is very similar to that of the Borel hierarchy. -/
def generateMeasurableRec (s : Set (Set α)) : ω₁ → Set (Set α)
  | i =>
    let S := ⋃ j : Iio i, generate_measurable_rec j.1
    s ∪ {∅} ∪ compl '' S ∪ Set.range fun f : ℕ → S => ⋃ n, (f n).1decreasing_by
  exact j.2
#align measurable_space.generate_measurable_rec MeasurableSpace.generateMeasurableRec

theorem self_subset_generateMeasurableRec (s : Set (Set α)) (i : ω₁) :
    s ⊆ generateMeasurableRec s i :=
  by
  unfold generate_measurable_rec
  apply_rules [subset_union_of_subset_left]
  exact subset_rfl
#align measurable_space.self_subset_generate_measurable_rec MeasurableSpace.self_subset_generateMeasurableRec

theorem empty_mem_generateMeasurableRec (s : Set (Set α)) (i : ω₁) :
    ∅ ∈ generateMeasurableRec s i :=
  by
  unfold generate_measurable_rec
  exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_singleton ∅)))
#align measurable_space.empty_mem_generate_measurable_rec MeasurableSpace.empty_mem_generateMeasurableRec

theorem compl_mem_generateMeasurableRec {s : Set (Set α)} {i j : ω₁} (h : j < i) {t : Set α}
    (ht : t ∈ generateMeasurableRec s j) : tᶜ ∈ generateMeasurableRec s i :=
  by
  unfold generate_measurable_rec
  exact mem_union_left _ (mem_union_right _ ⟨t, mem_Union.2 ⟨⟨j, h⟩, ht⟩, rfl⟩)
#align measurable_space.compl_mem_generate_measurable_rec MeasurableSpace.compl_mem_generateMeasurableRec

theorem unionᵢ_mem_generateMeasurableRec {s : Set (Set α)} {i : ω₁} {f : ℕ → Set α}
    (hf : ∀ n, ∃ j < i, f n ∈ generateMeasurableRec s j) : (⋃ n, f n) ∈ generateMeasurableRec s i :=
  by
  unfold generate_measurable_rec
  exact
    mem_union_right _
      ⟨fun n =>
        ⟨f n,
          let ⟨j, hj, hf⟩ := hf n
          mem_Union.2 ⟨⟨j, hj⟩, hf⟩⟩,
        rfl⟩
#align measurable_space.Union_mem_generate_measurable_rec MeasurableSpace.unionᵢ_mem_generateMeasurableRec

theorem generateMeasurableRec_subset (s : Set (Set α)) {i j : ω₁} (h : i ≤ j) :
    generateMeasurableRec s i ⊆ generateMeasurableRec s j := fun x hx =>
  by
  rcases eq_or_lt_of_le h with (rfl | h)
  · exact hx
  · convert Union_mem_generate_measurable_rec fun n => ⟨i, h, hx⟩
    exact (Union_const x).symm
#align measurable_space.generate_measurable_rec_subset MeasurableSpace.generateMeasurableRec_subset

/-- At each step of the inductive construction, the cardinality bound `≤ (max (#s) 2) ^ ℵ₀` holds.
-/
theorem cardinal_generateMeasurableRec_le (s : Set (Set α)) (i : ω₁) :
    (#generateMeasurableRec s i) ≤ max (#s) 2 ^ aleph0.{u} :=
  by
  apply (aleph 1).ord.out.wo.wf.induction i
  intro i IH
  have A := aleph_0_le_aleph 1
  have B : aleph 1 ≤ max (#s) 2 ^ aleph0.{u} :=
    aleph_one_le_continuum.trans (power_le_power_right (le_max_right _ _))
  have C : ℵ₀ ≤ max (#s) 2 ^ aleph0.{u} := A.trans B
  have J : (#⋃ j : Iio i, generate_measurable_rec s j.1) ≤ max (#s) 2 ^ aleph0.{u} :=
    by
    apply (mk_Union_le _).trans
    have D : (⨆ j : Iio i, #generate_measurable_rec s j) ≤ _ := csupᵢ_le' fun ⟨j, hj⟩ => IH j hj
    apply (mul_le_mul' ((mk_subtype_le _).trans (aleph 1).mk_ord_out.le) D).trans
    rw [mul_eq_max A C]
    exact max_le B le_rfl
  rw [generate_measurable_rec]
  apply_rules [(mk_union_le _ _).trans, add_le_of_le C, mk_image_le.trans]
  · exact (le_max_left _ _).trans (self_le_power _ one_lt_aleph_0.le)
  · rw [mk_singleton]
    exact one_lt_aleph_0.le.trans C
  · apply mk_range_le.trans
    simp only [mk_pi, Subtype.val_eq_coe, prod_const, lift_uzero, mk_denumerable, lift_aleph_0]
    have := @power_le_power_right _ _ ℵ₀ J
    rwa [← power_mul, aleph_0_mul_aleph_0] at this
#align measurable_space.cardinal_generate_measurable_rec_le MeasurableSpace.cardinal_generateMeasurableRec_le

/-- `generate_measurable_rec s` generates precisely the smallest sigma-algebra containing `s`. -/
theorem generateMeasurable_eq_rec (s : Set (Set α)) :
    { t | GenerateMeasurable s t } = ⋃ i, generateMeasurableRec s i :=
  by
  ext t; refine' ⟨fun ht => _, fun ht => _⟩
  · inhabit ω₁
    induction' ht with u hu u hu IH f hf IH
    · exact mem_Union.2 ⟨default, self_subset_generate_measurable_rec s _ hu⟩
    · exact mem_Union.2 ⟨default, empty_mem_generate_measurable_rec s _⟩
    · rcases mem_Union.1 IH with ⟨i, hi⟩
      obtain ⟨j, hj⟩ := exists_gt i
      exact mem_Union.2 ⟨j, compl_mem_generate_measurable_rec hj hi⟩
    · have : ∀ n, ∃ i, f n ∈ generate_measurable_rec s i := fun n => by simpa using IH n
      choose I hI using this
      refine'
        mem_Union.2
          ⟨Ordinal.enum (· < ·) (Ordinal.lsub fun n => Ordinal.typein.{u} (· < ·) (I n)) _,
            Union_mem_generate_measurable_rec fun n => ⟨I n, _, hI n⟩⟩
      · rw [Ordinal.type_lt]
        refine' Ordinal.lsub_lt_ord_lift _ fun i => Ordinal.typein_lt_self _
        rw [mk_denumerable, lift_aleph_0, is_regular_aleph_one.cof_eq]
        exact aleph_0_lt_aleph_one
      · rw [← Ordinal.typein_lt_typein (· < ·), Ordinal.typein_enum]
        apply Ordinal.lt_lsub fun n : ℕ => _
  · rcases ht with ⟨t, ⟨i, rfl⟩, hx⟩
    revert t
    apply (aleph 1).ord.out.wo.wf.induction i
    intro j H t ht
    unfold generate_measurable_rec at ht
    rcases ht with (((h | h) | ⟨u, ⟨-, ⟨⟨k, hk⟩, rfl⟩, hu⟩, rfl⟩) | ⟨f, rfl⟩)
    · exact generate_measurable.basic t h
    · convert generate_measurable.empty
    · exact generate_measurable.compl u (H k hk u hu)
    · apply generate_measurable.union _ fun n => _
      obtain ⟨-, ⟨⟨k, hk⟩, rfl⟩, hf⟩ := (f n).Prop
      exact H k hk _ hf
#align measurable_space.generate_measurable_eq_rec MeasurableSpace.generateMeasurable_eq_rec

/-- If a sigma-algebra is generated by a set of sets `s`, then the sigma-algebra has cardinality at
most `(max (#s) 2) ^ ℵ₀`. -/
theorem cardinal_generateMeasurable_le (s : Set (Set α)) :
    (#{ t | GenerateMeasurable s t }) ≤ max (#s) 2 ^ aleph0.{u} :=
  by
  rw [generate_measurable_eq_rec]
  apply (mk_Union_le _).trans
  rw [(aleph 1).mk_ord_out]
  refine'
    le_trans
      (mul_le_mul' aleph_one_le_continuum
        (csupᵢ_le' fun i => cardinal_generate_measurable_rec_le s i))
      _
  have := power_le_power_right (le_max_right (#s) 2)
  rw [mul_eq_max aleph_0_le_continuum (aleph_0_le_continuum.trans this)]
  exact max_le this le_rfl
#align measurable_space.cardinal_generate_measurable_le MeasurableSpace.cardinal_generateMeasurable_le

/-- If a sigma-algebra is generated by a set of sets `s`, then the sigma
algebra has cardinality at most `(max (#s) 2) ^ ℵ₀`. -/
theorem cardinal_measurableSet_le (s : Set (Set α)) :
    (#{ t | @MeasurableSet α (generateFrom s) t }) ≤ max (#s) 2 ^ aleph0.{u} :=
  cardinal_generateMeasurable_le s
#align measurable_space.cardinal_measurable_set_le MeasurableSpace.cardinal_measurableSet_le

/-- If a sigma-algebra is generated by a set of sets `s` with cardinality at most the continuum,
then the sigma algebra has the same cardinality bound. -/
theorem cardinal_generateMeasurable_le_continuum {s : Set (Set α)} (hs : (#s) ≤ 𝔠) :
    (#{ t | GenerateMeasurable s t }) ≤ 𝔠 :=
  (cardinal_generateMeasurable_le s).trans
    (by
      rw [← continuum_power_aleph_0]
      exact_mod_cast power_le_power_right (max_le hs (nat_lt_continuum 2).le))
#align measurable_space.cardinal_generate_measurable_le_continuum MeasurableSpace.cardinal_generateMeasurable_le_continuum

/-- If a sigma-algebra is generated by a set of sets `s` with cardinality at most the continuum,
then the sigma algebra has the same cardinality bound. -/
theorem cardinal_measurableSet_le_continuum {s : Set (Set α)} :
    (#s) ≤ 𝔠 → (#{ t | @MeasurableSet α (generateFrom s) t }) ≤ 𝔠 :=
  cardinal_generateMeasurable_le_continuum
#align measurable_space.cardinal_measurable_set_le_continuum MeasurableSpace.cardinal_measurableSet_le_continuum

end MeasurableSpace

