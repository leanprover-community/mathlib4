/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module measure_theory.constructions.pi
! leanprover-community/mathlib commit fd5edc43dc4f10b85abfe544b88f82cf13c5f844
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Constructions

/-!
# Product measures

In this file we define and prove properties about finite products of measures
(and at some point, countable products of measures).

## Main definition

* `MeasureTheory.Measure.pi`: The product of finitely many σ-finite measures.
  Given `μ : (i : ι) → Measure (α i)` for `[Fintype ι]` it has type `Measure ((i : ι) → α i)`.

To apply Fubini along some subset of the variables, use
`MeasureTheory.measurePreserving_piEquivPiSubtypeProd` to reduce to the situation of a product
of two measures: this lemma states that the bijection
`MeasurableEquiv.piEquivPiSubtypeProd α p` between `(∀ i : ι, α i)` and
`((i : {i // p i}) → α i) × ((i : {i // ¬ p i}) → α i)` maps a product measure to a direct product
of product measures, to which one can apply the usual Fubini for direct product of measures.

## Implementation Notes

We define `MeasureTheory.OuterMeasure.pi`, the product of finitely many outer measures, as the
maximal outer measure `n` with the property that `n (pi univ s) ≤ ∏ i, m i (s i)`,
where `pi univ s` is the product of the sets `{s i | i : ι}`.

We then show that this induces a product of measures, called `MeasureTheory.Measure.pi`.
For a collection of σ-finite measures `μ` and a collection of measurable sets `s` we show that
`Measure.pi μ (pi univ s) = ∏ i, m i (s i)`. To do this, we follow the following steps:
* We know that there is some ordering on `ι`, given by an element of `[Countable ι]`.
* Using this, we have an equivalence `MeasurableEquiv.piMeasurableEquivTProd` between
  `∀ ι, α i` and an iterated product of `α i`, called `List.tprod α l` for some list `l`.
* On this iterated product we can easily define a product measure `MeasureTheory.Measure.tprod`
  by iterating `MeasureTheory.Measure.prod`
* Using the previous two steps we construct `MeasureTheory.Measure.pi'` on `(i : ι) → α i` for
  countable `ι`.
* We know that `MeasureTheory.Measure.pi'` sends products of sets to products of measures, and
  since `MeasureTheory.Measure.pi` is the maximal such measure (or at least, it comes from an outer
  measure which is the maximal such outer measure), we get the same rule for
  `MeasureTheory.Measure.pi`.

## Tags

finitary product measure

-/


noncomputable section

open Function Set MeasureTheory.OuterMeasure Filter MeasurableSpace Encodable

open scoped Classical BigOperators Topology ENNReal

universe u v

variable {ι ι' : Type _} {α : ι → Type _}

/-! We start with some measurability properties -/


/-- Boxes formed by π-systems form a π-system. -/
theorem IsPiSystem.pi {C : ∀ i, Set (Set (α i))} (hC : ∀ i, IsPiSystem (C i)) :
    IsPiSystem (pi univ '' pi univ C) := by
  rintro _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩ hst
  rw [← pi_inter_distrib] at hst⊢; rw [univ_pi_nonempty_iff] at hst
  exact mem_image_of_mem _ fun i _ => hC i _ (hs₁ i (mem_univ i)) _ (hs₂ i (mem_univ i)) (hst i)
#align is_pi_system.pi IsPiSystem.pi

/-- Boxes form a π-system. -/
theorem isPiSystem_pi [∀ i, MeasurableSpace (α i)] :
    IsPiSystem (pi univ '' pi univ fun i => { s : Set (α i) | MeasurableSet s }) :=
  IsPiSystem.pi fun _ => isPiSystem_measurableSet
#align is_pi_system_pi isPiSystem_pi

section Finite

variable [Finite ι] [Finite ι']

/-- Boxes of countably spanning sets are countably spanning. -/
theorem IsCountablySpanning.pi {C : ∀ i, Set (Set (α i))} (hC : ∀ i, IsCountablySpanning (C i)) :
    IsCountablySpanning (pi univ '' pi univ C) := by
  choose s h1s h2s using hC
  cases nonempty_encodable (ι → ℕ)
  let e : ℕ → ι → ℕ := fun n => (@decode (ι → ℕ) _ n).iget
  refine' ⟨fun n => Set.pi univ fun i => s i (e n i), fun n =>
    mem_image_of_mem _ fun i _ => h1s i _, _⟩
  simp_rw [(surjective_decode_iget (ι → ℕ)).iUnion_comp fun x => Set.pi univ fun i => s i (x i),
    iUnion_univ_pi s, h2s, pi_univ]
#align is_countably_spanning.pi IsCountablySpanning.pi

/-- The product of generated σ-algebras is the one generated by boxes, if both generating sets
  are countably spanning. -/
theorem generateFrom_pi_eq {C : ∀ i, Set (Set (α i))} (hC : ∀ i, IsCountablySpanning (C i)) :
    (@MeasurableSpace.pi _ _ fun i => generateFrom (C i)) =
    generateFrom (pi univ '' pi univ C) := by
  cases nonempty_encodable ι
  apply le_antisymm
  · refine' iSup_le _; intro i; rw [comap_generateFrom]
    apply generateFrom_le; rintro _ ⟨s, hs, rfl⟩; dsimp
    choose t h1t h2t using hC
    simp_rw [eval_preimage, ← h2t]
    rw [← @iUnion_const _ ℕ _ s]
    have : Set.pi univ (update (fun i' : ι => iUnion (t i')) i (⋃ _i' : ℕ, s)) =
        Set.pi univ fun k => ⋃ j : ℕ,
        @update ι (fun i' => Set (α i')) _ (fun i' => t i' j) i s k := by
      ext; simp_rw [mem_univ_pi]; apply forall_congr'; intro i'
      by_cases i' = i
      · subst h; simp
      · rw [← Ne.def] at h; simp [h]
    rw [this, ← iUnion_univ_pi]
    apply MeasurableSet.iUnion
    intro n; apply measurableSet_generateFrom
    apply mem_image_of_mem; intro j _; dsimp only
    by_cases h : j = i; subst h; rwa [update_same]; rw [update_noteq h]; apply h1t
  · apply generateFrom_le; rintro _ ⟨s, hs, rfl⟩
    rw [univ_pi_eq_iInter]; apply MeasurableSet.iInter; intro i
    apply @measurable_pi_apply _ _ (fun i => generateFrom (C i))
    exact measurableSet_generateFrom (hs i (mem_univ i))
#align generate_from_pi_eq generateFrom_pi_eq

/-- If `C` and `D` generate the σ-algebras on `α` resp. `β`, then rectangles formed by `C` and `D`
  generate the σ-algebra on `α × β`. -/
theorem generateFrom_eq_pi [h : ∀ i, MeasurableSpace (α i)] {C : ∀ i, Set (Set (α i))}
    (hC : ∀ i, generateFrom (C i) = h i) (h2C : ∀ i, IsCountablySpanning (C i)) :
    generateFrom (pi univ '' pi univ C) = MeasurableSpace.pi := by
  rw [← funext hC, generateFrom_pi_eq h2C]
#align generate_from_eq_pi generateFrom_eq_pi

/-- The product σ-algebra is generated from boxes, i.e. `s ×ˢ t` for sets `s : set α` and
  `t : set β`. -/
theorem generateFrom_pi [∀ i, MeasurableSpace (α i)] :
    generateFrom (pi univ '' pi univ fun i => { s : Set (α i) | MeasurableSet s }) =
      MeasurableSpace.pi :=
  generateFrom_eq_pi (fun _ => generateFrom_measurableSet) fun _ =>
    isCountablySpanning_measurableSet
#align generate_from_pi generateFrom_pi

end Finite

namespace MeasureTheory

variable [Fintype ι] {m : ∀ i, OuterMeasure (α i)}

/-- An upper bound for the measure in a finite product space.
  It is defined to by taking the image of the set under all projections, and taking the product
  of the measures of these images.
  For measurable boxes it is equal to the correct measure. -/
@[simp]
def piPremeasure (m : ∀ i, OuterMeasure (α i)) (s : Set (∀ i, α i)) : ℝ≥0∞ :=
  ∏ i, m i (eval i '' s)
#align measure_theory.pi_premeasure MeasureTheory.piPremeasure

theorem piPremeasure_pi {s : ∀ i, Set (α i)} (hs : (pi univ s).Nonempty) :
    piPremeasure m (pi univ s) = ∏ i, m i (s i) := by simp [hs, piPremeasure]
#align measure_theory.pi_premeasure_pi MeasureTheory.piPremeasure_pi

theorem piPremeasure_pi' {s : ∀ i, Set (α i)} : piPremeasure m (pi univ s) = ∏ i, m i (s i) := by
  cases isEmpty_or_nonempty ι
  · simp [piPremeasure]
  cases' (pi univ s).eq_empty_or_nonempty with h h
  · rcases univ_pi_eq_empty_iff.mp h with ⟨i, hi⟩
    have : ∃ i, m i (s i) = 0 := ⟨i, by simp [hi]⟩
    simpa [h, Finset.card_univ, zero_pow (Fintype.card_pos_iff.mpr ‹_›), @eq_comm _ (0 : ℝ≥0∞),
      Finset.prod_eq_zero_iff, piPremeasure]
  · simp [h, piPremeasure]
#align measure_theory.pi_premeasure_pi' MeasureTheory.piPremeasure_pi'

theorem piPremeasure_pi_mono {s t : Set (∀ i, α i)} (h : s ⊆ t) :
    piPremeasure m s ≤ piPremeasure m t :=
  Finset.prod_le_prod' fun i _ => (m i).mono' (image_subset _ h)
#align measure_theory.pi_premeasure_pi_mono MeasureTheory.piPremeasure_pi_mono

theorem piPremeasure_pi_eval {s : Set (∀ i, α i)} :
    piPremeasure m (pi univ fun i => eval i '' s) = piPremeasure m s := by
  simp [piPremeasure_pi']; rfl
#align measure_theory.pi_premeasure_pi_eval MeasureTheory.piPremeasure_pi_eval

namespace OuterMeasure

/-- `OuterMeasure.pi m` is the finite product of the outer measures `{m i | i : ι}`.
  It is defined to be the maximal outer measure `n` with the property that
  `n (pi univ s) ≤ ∏ i, m i (s i)`, where `pi univ s` is the product of the sets
  `{s i | i : ι}`. -/
protected def pi (m : ∀ i, OuterMeasure (α i)) : OuterMeasure (∀ i, α i) :=
  boundedBy (piPremeasure m)
#align measure_theory.outer_measure.pi MeasureTheory.OuterMeasure.pi

theorem pi_pi_le (m : ∀ i, OuterMeasure (α i)) (s : ∀ i, Set (α i)) :
    OuterMeasure.pi m (pi univ s) ≤ ∏ i, m i (s i) := by
  cases' (pi univ s).eq_empty_or_nonempty with h h; simp [h]
  exact (boundedBy_le _).trans_eq (piPremeasure_pi h)
#align measure_theory.outer_measure.pi_pi_le MeasureTheory.OuterMeasure.pi_pi_le

theorem le_pi {m : ∀ i, OuterMeasure (α i)} {n : OuterMeasure (∀ i, α i)} :
    n ≤ OuterMeasure.pi m ↔
      ∀ s : ∀ i, Set (α i), (pi univ s).Nonempty → n (pi univ s) ≤ ∏ i, m i (s i) := by
  rw [OuterMeasure.pi, le_boundedBy']; constructor
  · intro h s hs; refine' (h _ hs).trans_eq (piPremeasure_pi hs)
  · intro h s hs; refine' le_trans (n.mono <| subset_pi_eval_image univ s) (h _ _)
    simp [univ_pi_nonempty_iff, hs]
#align measure_theory.outer_measure.le_pi MeasureTheory.OuterMeasure.le_pi

end OuterMeasure

namespace Measure

variable [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))

section Tprod

open List

variable {δ : Type _} {π : δ → Type _} [∀ x, MeasurableSpace (π x)]

-- for some reason the equation compiler doesn't like this definition
/-- A product of measures in `tprod α l`. -/
protected def tprod (l : List δ) (μ : ∀ i, Measure (π i)) : Measure (TProd π l) := by
  induction' l with i l ih
  · exact dirac PUnit.unit
  · have := (μ i).prod (α := π i) ih
    exact this
#align measure_theory.measure.tprod MeasureTheory.Measure.tprod

@[simp]
theorem tprod_nil (μ : ∀ i, Measure (π i)) : Measure.tprod [] μ = dirac PUnit.unit :=
  rfl
#align measure_theory.measure.tprod_nil MeasureTheory.Measure.tprod_nil

@[simp]
theorem tprod_cons (i : δ) (l : List δ) (μ : ∀ i, Measure (π i)) :
    Measure.tprod (i :: l) μ = (μ i).prod (Measure.tprod l μ) :=
  rfl
#align measure_theory.measure.tprod_cons MeasureTheory.Measure.tprod_cons

instance sigmaFinite_tprod (l : List δ) (μ : ∀ i, Measure (π i)) [∀ i, SigmaFinite (μ i)] :
    SigmaFinite (Measure.tprod l μ) := by
  induction l with
  | nil => rw [tprod_nil]; infer_instance
  | cons i l ih => rw [tprod_cons]; exact @prod.instSigmaFinite _ _ _ _ _ _ ih _
#align measure_theory.measure.sigma_finite_tprod MeasureTheory.Measure.sigmaFinite_tprod

theorem tprod_tprod (l : List δ) (μ : ∀ i, Measure (π i)) [∀ i, SigmaFinite (μ i)]
    (s : ∀ i, Set (π i)) :
    Measure.tprod l μ (Set.tprod l s) = (l.map fun i => (μ i) (s i)).prod := by
  induction' l with i l ih; · simp
  rw [tprod_cons, Set.tprod, prod_prod, map_cons, prod_cons, ih]
#align measure_theory.measure.tprod_tprod MeasureTheory.Measure.tprod_tprod

end Tprod

section Encodable

open List MeasurableEquiv

variable [Encodable ι]

/-- The product measure on an encodable finite type, defined by mapping `Measure.tprod` along the
  equivalence `MeasurableEquiv.piMeasurableEquivTProd`.
  The definition `MeasureTheory.Measure.pi` should be used instead of this one. -/
def pi' : Measure (∀ i, α i) :=
  Measure.map (TProd.elim' mem_sortedUniv) (Measure.tprod (sortedUniv ι) μ)
#align measure_theory.measure.pi' MeasureTheory.Measure.pi'

theorem pi'_pi [∀ i, SigmaFinite (μ i)] (s : ∀ i, Set (α i)) :
    pi' μ (pi univ s) = ∏ i, μ i (s i) := by
  rw [pi']
  simp only [TProd.elim'] -- Porting note: new step
  erw [← MeasurableEquiv.piMeasurableEquivTProd_symm_apply, MeasurableEquiv.map_apply,
    MeasurableEquiv.piMeasurableEquivTProd_symm_apply, elim_preimage_pi, tprod_tprod _ μ, ←
    List.prod_toFinset, sortedUniv_toFinset] <;>
  exact sortedUniv_nodup ι
#align measure_theory.measure.pi'_pi MeasureTheory.Measure.pi'_pi

end Encodable

theorem pi_caratheodory :
    MeasurableSpace.pi ≤ (OuterMeasure.pi fun i => (μ i).toOuterMeasure).caratheodory := by
  refine' iSup_le _
  intro i s hs
  rw [MeasurableSpace.comap] at hs
  rcases hs with ⟨s, hs, rfl⟩
  apply boundedBy_caratheodory
  intro t
  simp_rw [piPremeasure]
  refine' Finset.prod_add_prod_le' (Finset.mem_univ i) _ _ _
  · simp [image_inter_preimage, image_diff_preimage, measure_inter_add_diff _ hs, le_refl]
  · rintro j - _; apply mono'; apply image_subset; apply inter_subset_left
  · rintro j - _; apply mono'; apply image_subset; apply diff_subset
#align measure_theory.measure.pi_caratheodory MeasureTheory.Measure.pi_caratheodory

/-- `Measure.pi μ` is the finite product of the measures `{μ i | i : ι}`.
  It is defined to be measure corresponding to `MeasureTheory.OuterMeasure.pi`. -/
protected irreducible_def pi : Measure (∀ i, α i) :=
  toMeasure (OuterMeasure.pi fun i => (μ i).toOuterMeasure) (pi_caratheodory μ)
#align measure_theory.measure.pi MeasureTheory.Measure.pi

theorem pi_pi_aux [∀ i, SigmaFinite (μ i)] (s : ∀ i, Set (α i)) (hs : ∀ i, MeasurableSet (s i)) :
    Measure.pi μ (pi univ s) = ∏ i, μ i (s i) := by
  refine' le_antisymm _ _
  · rw [Measure.pi, toMeasure_apply _ _ (MeasurableSet.pi countable_univ fun i _ => hs i)]
    apply OuterMeasure.pi_pi_le
  · haveI : Encodable ι := Fintype.toEncodable ι
    rw [← pi'_pi μ s]
    simp_rw [← pi'_pi μ s, Measure.pi,
      toMeasure_apply _ _ (MeasurableSet.pi countable_univ fun i _ => hs i)]
    suffices (pi' μ).toOuterMeasure ≤ OuterMeasure.pi fun i => (μ i).toOuterMeasure by exact this _
    clear hs s
    rw [OuterMeasure.le_pi]
    intro s _
    exact (pi'_pi μ s).le
#align measure_theory.measure.pi_pi_aux MeasureTheory.Measure.pi_pi_aux

variable {μ}

/-- `Measure.pi μ` has finite spanning sets in rectangles of finite spanning sets. -/
def FiniteSpanningSetsIn.pi {C : ∀ i, Set (Set (α i))}
    (hμ : ∀ i, (μ i).FiniteSpanningSetsIn (C i)) :
    (Measure.pi μ).FiniteSpanningSetsIn (pi univ '' pi univ C) := by
  haveI := fun i => (hμ i).sigmaFinite
  haveI := Fintype.toEncodable ι
  refine' ⟨fun n => Set.pi univ fun i => (hμ i).set ((@decode (ι → ℕ) _ n).iget i),
    fun n => _, fun n => _, _⟩ <;>
  -- TODO (kmill) If this let comes before the refine, while the noncomputability checker
  -- correctly sees this definition is computable, the Lean VM fails to see the binding is
  -- computationally irrelevant. The `noncomputable section` doesn't help because all it does
  -- is insert `noncomputable` for you when necessary.
  let e : ℕ → ι → ℕ := fun n => (@decode (ι → ℕ) _ n).iget
  · refine' mem_image_of_mem _ fun i _ => (hμ i).set_mem _
  · calc
      Measure.pi μ (Set.pi univ fun i => (hμ i).set (e n i)) ≤
          Measure.pi μ (Set.pi univ fun i => toMeasurable (μ i) ((hμ i).set (e n i))) :=
        measure_mono (pi_mono fun i _ => subset_toMeasurable _ _)
      _ = ∏ i, μ i (toMeasurable (μ i) ((hμ i).set (e n i))) :=
        (pi_pi_aux μ _ fun i => measurableSet_toMeasurable _ _)
      _ = ∏ i, μ i ((hμ i).set (e n i)) := by simp only [measure_toMeasurable]
      _ < ∞ := ENNReal.prod_lt_top fun i _ => ((hμ i).finite _).ne
  · simp_rw [(surjective_decode_iget (ι → ℕ)).iUnion_comp fun x =>
        Set.pi univ fun i => (hμ i).set (x i),
      iUnion_univ_pi fun i => (hμ i).set, (hμ _).spanning, Set.pi_univ]
#align measure_theory.measure.finite_spanning_sets_in.pi MeasureTheory.Measure.FiniteSpanningSetsIn.pi

/-- A measure on a finite product space equals the product measure if they are equal on rectangles
  with as sides sets that generate the corresponding σ-algebras. -/
theorem pi_eq_generateFrom {C : ∀ i, Set (Set (α i))}
    (hC : ∀ i, generateFrom (C i) = by apply_assumption) (h2C : ∀ i, IsPiSystem (C i))
    (h3C : ∀ i, (μ i).FiniteSpanningSetsIn (C i)) {μν : Measure (∀ i, α i)}
    (h₁ : ∀ s : ∀ i, Set (α i), (∀ i, s i ∈ C i) → μν (pi univ s) = ∏ i, μ i (s i)) :
    Measure.pi μ = μν := by
  have h4C : ∀ (i) (s : Set (α i)), s ∈ C i → MeasurableSet s := by
    intro i s hs; rw [← hC]; exact measurableSet_generateFrom hs
  refine'
    (FiniteSpanningSetsIn.pi h3C).ext
      (generateFrom_eq_pi hC fun i => (h3C i).isCountablySpanning).symm (IsPiSystem.pi h2C) _
  rintro _ ⟨s, hs, rfl⟩
  rw [mem_univ_pi] at hs
  haveI := fun i => (h3C i).sigmaFinite
  simp_rw [h₁ s hs, pi_pi_aux μ s fun i => h4C i _ (hs i)]
#align measure_theory.measure.pi_eq_generate_from MeasureTheory.Measure.pi_eq_generateFrom

variable [∀ i, SigmaFinite (μ i)]

/-- A measure on a finite product space equals the product measure if they are equal on
  rectangles. -/
theorem pi_eq {μ' : Measure (∀ i, α i)}
    (h : ∀ s : ∀ i, Set (α i), (∀ i, MeasurableSet (s i)) → μ' (pi univ s) = ∏ i, μ i (s i)) :
    Measure.pi μ = μ' :=
  pi_eq_generateFrom (fun _ => generateFrom_measurableSet) (fun _ => isPiSystem_measurableSet)
    (fun i => (μ i).toFiniteSpanningSetsIn) h
#align measure_theory.measure.pi_eq MeasureTheory.Measure.pi_eq

variable (μ)

theorem pi'_eq_pi [Encodable ι] : pi' μ = Measure.pi μ :=
  Eq.symm <| pi_eq fun s _ => pi'_pi μ s
#align measure_theory.measure.pi'_eq_pi MeasureTheory.Measure.pi'_eq_pi

@[simp]
theorem pi_pi (s : ∀ i, Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i) := by
  haveI : Encodable ι := Fintype.toEncodable ι
  rw [← pi'_eq_pi, pi'_pi]
#align measure_theory.measure.pi_pi MeasureTheory.Measure.pi_pi

nonrec theorem pi_univ : Measure.pi μ univ = ∏ i, μ i univ := by rw [← pi_univ, pi_pi μ]
#align measure_theory.measure.pi_univ MeasureTheory.Measure.pi_univ

theorem pi_ball [∀ i, MetricSpace (α i)] (x : ∀ i, α i) {r : ℝ} (hr : 0 < r) :
    Measure.pi μ (Metric.ball x r) = ∏ i, μ i (Metric.ball (x i) r) := by rw [ball_pi _ hr, pi_pi]
#align measure_theory.measure.pi_ball MeasureTheory.Measure.pi_ball

theorem pi_closedBall [∀ i, MetricSpace (α i)] (x : ∀ i, α i) {r : ℝ} (hr : 0 ≤ r) :
    Measure.pi μ (Metric.closedBall x r) = ∏ i, μ i (Metric.closedBall (x i) r) := by
  rw [closedBall_pi _ hr, pi_pi]
#align measure_theory.measure.pi_closed_ball MeasureTheory.Measure.pi_closedBall

instance pi.sigmaFinite : SigmaFinite (Measure.pi μ) :=
  (FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).sigmaFinite
#align measure_theory.measure.pi.sigma_finite MeasureTheory.Measure.pi.sigmaFinite

theorem pi_of_empty {α : Type _} [IsEmpty α] {β : α → Type _} {m : ∀ a, MeasurableSpace (β a)}
    (μ : ∀ a : α, Measure (β a)) (x : ∀ a, β a := isEmptyElim) : Measure.pi μ = dirac x := by
  haveI : ∀ a, SigmaFinite (μ a) := isEmptyElim
  refine' pi_eq fun s _ => _
  rw [Fintype.prod_empty, dirac_apply_of_mem]
  exact isEmptyElim (α := α)
#align measure_theory.measure.pi_of_empty MeasureTheory.Measure.pi_of_empty

theorem pi_eval_preimage_null {i : ι} {s : Set (α i)} (hs : μ i s = 0) :
    Measure.pi μ (eval i ⁻¹' s) = 0 := by
  -- WLOG, `s` is measurable
  rcases exists_measurable_superset_of_null hs with ⟨t, hst, _, hμt⟩
  suffices : Measure.pi μ (eval i ⁻¹' t) = 0
  exact measure_mono_null (preimage_mono hst) this
  clear! s
  -- Now rewrite it as `Set.pi`, and apply `pi_pi`
  rw [← univ_pi_update_univ, pi_pi]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hμt]
#align measure_theory.measure.pi_eval_preimage_null MeasureTheory.Measure.pi_eval_preimage_null

theorem pi_hyperplane (i : ι) [NoAtoms (μ i)] (x : α i) :
    Measure.pi μ { f : ∀ i, α i | f i = x } = 0 :=
  show Measure.pi μ (eval i ⁻¹' {x}) = 0 from pi_eval_preimage_null _ (measure_singleton x)
#align measure_theory.measure.pi_hyperplane MeasureTheory.Measure.pi_hyperplane

theorem ae_eval_ne (i : ι) [NoAtoms (μ i)] (x : α i) : ∀ᵐ y : ∀ i, α i ∂Measure.pi μ, y i ≠ x :=
  compl_mem_ae_iff.2 (pi_hyperplane μ i x)
#align measure_theory.measure.ae_eval_ne MeasureTheory.Measure.ae_eval_ne

variable {μ}

theorem tendsto_eval_ae_ae {i : ι} : Tendsto (eval i) (Measure.pi μ).ae (μ i).ae := fun _ hs =>
  pi_eval_preimage_null μ hs
#align measure_theory.measure.tendsto_eval_ae_ae MeasureTheory.Measure.tendsto_eval_ae_ae

theorem ae_pi_le_pi : (Measure.pi μ).ae ≤ Filter.pi fun i => (μ i).ae :=
  le_iInf fun _ => tendsto_eval_ae_ae.le_comap
#align measure_theory.measure.ae_pi_le_pi MeasureTheory.Measure.ae_pi_le_pi

theorem ae_eq_pi {β : ι → Type _} {f f' : ∀ i, α i → β i} (h : ∀ i, f i =ᵐ[μ i] f' i) :
    (fun (x : ∀ i, α i) i => f i (x i)) =ᵐ[Measure.pi μ] fun x i => f' i (x i) :=
  (eventually_all.2 fun i => tendsto_eval_ae_ae.eventually (h i)).mono fun _ hx => funext hx
#align measure_theory.measure.ae_eq_pi MeasureTheory.Measure.ae_eq_pi

theorem ae_le_pi {β : ι → Type _} [∀ i, Preorder (β i)] {f f' : ∀ i, α i → β i}
    (h : ∀ i, f i ≤ᵐ[μ i] f' i) :
    (fun (x : ∀ i, α i) i => f i (x i)) ≤ᵐ[Measure.pi μ] fun x i => f' i (x i) :=
  (eventually_all.2 fun i => tendsto_eval_ae_ae.eventually (h i)).mono fun _ hx => hx
#align measure_theory.measure.ae_le_pi MeasureTheory.Measure.ae_le_pi

theorem ae_le_set_pi {I : Set ι} {s t : ∀ i, Set (α i)} (h : ∀ i ∈ I, s i ≤ᵐ[μ i] t i) :
    Set.pi I s ≤ᵐ[Measure.pi μ] Set.pi I t :=
  ((eventually_all_finite I.toFinite).2 fun i hi => tendsto_eval_ae_ae.eventually (h i hi)).mono
    fun _ hst hx i hi => hst i hi <| hx i hi
#align measure_theory.measure.ae_le_set_pi MeasureTheory.Measure.ae_le_set_pi

theorem ae_eq_set_pi {I : Set ι} {s t : ∀ i, Set (α i)} (h : ∀ i ∈ I, s i =ᵐ[μ i] t i) :
    Set.pi I s =ᵐ[Measure.pi μ] Set.pi I t :=
  (ae_le_set_pi fun i hi => (h i hi).le).antisymm (ae_le_set_pi fun i hi => (h i hi).symm.le)
#align measure_theory.measure.ae_eq_set_pi MeasureTheory.Measure.ae_eq_set_pi

section Intervals

variable [∀ i, PartialOrder (α i)] [∀ i, NoAtoms (μ i)]

theorem pi_Iio_ae_eq_pi_Iic {s : Set ι} {f : ∀ i, α i} :
    (pi s fun i => Iio (f i)) =ᵐ[Measure.pi μ] pi s fun i => Iic (f i) :=
  ae_eq_set_pi fun _ _ => Iio_ae_eq_Iic
#align measure_theory.measure.pi_Iio_ae_eq_pi_Iic MeasureTheory.Measure.pi_Iio_ae_eq_pi_Iic

theorem pi_Ioi_ae_eq_pi_Ici {s : Set ι} {f : ∀ i, α i} :
    (pi s fun i => Ioi (f i)) =ᵐ[Measure.pi μ] pi s fun i => Ici (f i) :=
  ae_eq_set_pi fun _ _ => Ioi_ae_eq_Ici
#align measure_theory.measure.pi_Ioi_ae_eq_pi_Ici MeasureTheory.Measure.pi_Ioi_ae_eq_pi_Ici

theorem univ_pi_Iio_ae_eq_Iic {f : ∀ i, α i} :
    (pi univ fun i => Iio (f i)) =ᵐ[Measure.pi μ] Iic f := by
  rw [← pi_univ_Iic]; exact pi_Iio_ae_eq_pi_Iic
#align measure_theory.measure.univ_pi_Iio_ae_eq_Iic MeasureTheory.Measure.univ_pi_Iio_ae_eq_Iic

theorem univ_pi_Ioi_ae_eq_Ici {f : ∀ i, α i} :
    (pi univ fun i => Ioi (f i)) =ᵐ[Measure.pi μ] Ici f := by
  rw [← pi_univ_Ici]; exact pi_Ioi_ae_eq_pi_Ici
#align measure_theory.measure.univ_pi_Ioi_ae_eq_Ici MeasureTheory.Measure.univ_pi_Ioi_ae_eq_Ici

theorem pi_Ioo_ae_eq_pi_Icc {s : Set ι} {f g : ∀ i, α i} :
    (pi s fun i => Ioo (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Icc (f i) (g i) :=
  ae_eq_set_pi fun _ _ => Ioo_ae_eq_Icc
#align measure_theory.measure.pi_Ioo_ae_eq_pi_Icc MeasureTheory.Measure.pi_Ioo_ae_eq_pi_Icc

theorem pi_Ioo_ae_eq_pi_Ioc {s : Set ι} {f g : ∀ i, α i} :
    (pi s fun i => Ioo (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Ioc (f i) (g i) :=
  ae_eq_set_pi fun _ _ => Ioo_ae_eq_Ioc
#align measure_theory.measure.pi_Ioo_ae_eq_pi_Ioc MeasureTheory.Measure.pi_Ioo_ae_eq_pi_Ioc

theorem univ_pi_Ioo_ae_eq_Icc {f g : ∀ i, α i} :
    (pi univ fun i => Ioo (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g := by
  rw [← pi_univ_Icc]; exact pi_Ioo_ae_eq_pi_Icc
#align measure_theory.measure.univ_pi_Ioo_ae_eq_Icc MeasureTheory.Measure.univ_pi_Ioo_ae_eq_Icc

theorem pi_Ioc_ae_eq_pi_Icc {s : Set ι} {f g : ∀ i, α i} :
    (pi s fun i => Ioc (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Icc (f i) (g i) :=
  ae_eq_set_pi fun _ _ => Ioc_ae_eq_Icc
#align measure_theory.measure.pi_Ioc_ae_eq_pi_Icc MeasureTheory.Measure.pi_Ioc_ae_eq_pi_Icc

theorem univ_pi_Ioc_ae_eq_Icc {f g : ∀ i, α i} :
    (pi univ fun i => Ioc (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g := by
  rw [← pi_univ_Icc]; exact pi_Ioc_ae_eq_pi_Icc
#align measure_theory.measure.univ_pi_Ioc_ae_eq_Icc MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc

theorem pi_Ico_ae_eq_pi_Icc {s : Set ι} {f g : ∀ i, α i} :
    (pi s fun i => Ico (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Icc (f i) (g i) :=
  ae_eq_set_pi fun _ _ => Ico_ae_eq_Icc
#align measure_theory.measure.pi_Ico_ae_eq_pi_Icc MeasureTheory.Measure.pi_Ico_ae_eq_pi_Icc

theorem univ_pi_Ico_ae_eq_Icc {f g : ∀ i, α i} :
    (pi univ fun i => Ico (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g := by
  rw [← pi_univ_Icc]; exact pi_Ico_ae_eq_pi_Icc
#align measure_theory.measure.univ_pi_Ico_ae_eq_Icc MeasureTheory.Measure.univ_pi_Ico_ae_eq_Icc

end Intervals

/-- If one of the measures `μ i` has no atoms, them `Measure.pi µ`
has no atoms. The instance below assumes that all `μ i` have no atoms. -/
theorem pi_noAtoms (i : ι) [NoAtoms (μ i)] : NoAtoms (Measure.pi μ) :=
  ⟨fun x => flip measure_mono_null (pi_hyperplane μ i (x i)) (singleton_subset_iff.2 rfl)⟩
#align measure_theory.measure.pi_has_no_atoms MeasureTheory.Measure.pi_noAtoms

instance [h : Nonempty ι] [∀ i, NoAtoms (μ i)] : NoAtoms (Measure.pi μ) :=
  h.elim fun i => pi_noAtoms i

instance [∀ i, TopologicalSpace (α i)] [∀ i, LocallyFiniteMeasure (μ i)] :
    LocallyFiniteMeasure (Measure.pi μ) := by
  refine' ⟨fun x => _⟩
  choose s hxs ho hμ using fun i => (μ i).exists_isOpen_measure_lt_top (x i)
  refine' ⟨pi univ s, set_pi_mem_nhds finite_univ fun i _ => IsOpen.mem_nhds (ho i) (hxs i), _⟩
  rw [pi_pi]
  exact ENNReal.prod_lt_top fun i _ => (hμ i).ne

variable (μ)

@[to_additive]
instance pi.isMulLeftInvariant [∀ i, Group (α i)] [∀ i, MeasurableMul (α i)]
    [∀ i, MulLeftInvariant (μ i)] : MulLeftInvariant (Measure.pi μ) := by
  refine' ⟨fun v => (pi_eq fun s hs => _).symm⟩
  rw [map_apply (measurable_const_mul _) (MeasurableSet.univ_pi hs),
    show (· * ·) v ⁻¹' univ.pi s = univ.pi fun i => (· * ·) (v i) ⁻¹' s i by rfl, pi_pi]
  simp_rw [measure_preimage_mul]
#align measure_theory.measure.pi.is_mul_left_invariant MeasureTheory.Measure.pi.isMulLeftInvariant
#align measure_theory.measure.pi.is_add_left_invariant MeasureTheory.Measure.pi.isAddLeftInvariant

@[to_additive]
instance pi.isMulRightInvariant [∀ i, Group (α i)] [∀ i, MeasurableMul (α i)]
    [∀ i, MulRightInvariant (μ i)] : MulRightInvariant (Measure.pi μ) := by
  refine' ⟨fun v => (pi_eq fun s hs => _).symm⟩
  rw [map_apply (measurable_mul_const _) (MeasurableSet.univ_pi hs),
    show (· * v) ⁻¹' univ.pi s = univ.pi fun i => (· * v i) ⁻¹' s i by rfl, pi_pi]
  simp_rw [measure_preimage_mul_right]
#align measure_theory.measure.pi.is_mul_right_invariant MeasureTheory.Measure.pi.isMulRightInvariant
#align measure_theory.measure.pi.is_add_right_invariant MeasureTheory.Measure.pi.isAddRightInvariant

@[to_additive]
instance pi.isInvInvariant [∀ i, Group (α i)] [∀ i, MeasurableInv (α i)]
    [∀ i, InvInvariant (μ i)] : InvInvariant (Measure.pi μ) := by
  refine' ⟨(Measure.pi_eq fun s hs => _).symm⟩
  have A : Inv.inv ⁻¹' pi univ s = Set.pi univ fun i => Inv.inv ⁻¹' s i := by ext; simp
  simp_rw [Measure.inv, Measure.map_apply measurable_inv (MeasurableSet.univ_pi hs), A, pi_pi,
    measure_preimage_inv]
#align measure_theory.measure.pi.is_inv_invariant MeasureTheory.Measure.pi.isInvInvariant
#align measure_theory.measure.pi.is_neg_invariant MeasureTheory.Measure.pi.isNegInvariant

instance pi.openPosMeasure [∀ i, TopologicalSpace (α i)] [∀ i, OpenPosMeasure (μ i)] :
    OpenPosMeasure (MeasureTheory.Measure.pi μ) := by
  constructor
  rintro U U_open ⟨a, ha⟩
  obtain ⟨s, ⟨hs, hsU⟩⟩ := isOpen_pi_iff'.1 U_open a ha
  refine' ne_of_gt (lt_of_lt_of_le _ (measure_mono hsU))
  simp only [pi_pi]
  rw [CanonicallyOrderedCommSemiring.prod_pos]
  intro i _
  apply (hs i).1.measure_pos (μ i) ⟨a i, (hs i).2⟩
#align measure_theory.measure.pi.is_open_pos_measure MeasureTheory.Measure.pi.openPosMeasure

instance pi.finiteMeasureOnCompacts [∀ i, TopologicalSpace (α i)]
    [∀ i, FiniteMeasureOnCompacts (μ i)] :
    FiniteMeasureOnCompacts (MeasureTheory.Measure.pi μ) := by
  constructor
  intro K hK
  suffices Measure.pi μ (Set.univ.pi fun j => Function.eval j '' K) < ⊤ by
    exact lt_of_le_of_lt (measure_mono (univ.subset_pi_eval_image K)) this
  rw [Measure.pi_pi]
  refine' WithTop.prod_lt_top _
  exact fun i _ => ne_of_lt (IsCompact.measure_lt_top (IsCompact.image hK (continuous_apply i)))
#align measure_theory.measure.pi.is_finite_measure_on_compacts MeasureTheory.Measure.pi.finiteMeasureOnCompacts

@[to_additive]
instance pi.isHaarMeasure [∀ i, Group (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, HaarMeasure (μ i)] [∀ i, MeasurableMul (α i)] : HaarMeasure (Measure.pi μ) where
#align measure_theory.measure.pi.is_haar_measure MeasureTheory.Measure.pi.isHaarMeasure
#align measure_theory.measure.pi.is_add_haar_measure MeasureTheory.Measure.pi.isAddHaarMeasure

end Measure

instance MeasureSpace.pi [∀ i, MeasureSpace (α i)] : MeasureSpace (∀ i, α i) :=
  ⟨Measure.pi fun _ => volume⟩
#align measure_theory.measure_space.pi MeasureTheory.MeasureSpace.pi

theorem volume_pi [∀ i, MeasureSpace (α i)] :
    (volume : Measure (∀ i, α i)) = Measure.pi fun _ => volume :=
  rfl
#align measure_theory.volume_pi MeasureTheory.volume_pi

theorem volume_pi_pi [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))]
    (s : ∀ i, Set (α i)) : volume (pi univ s) = ∏ i, volume (s i) :=
  Measure.pi_pi (fun _ => volume) s
#align measure_theory.volume_pi_pi MeasureTheory.volume_pi_pi

theorem volume_pi_ball [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))]
    [∀ i, MetricSpace (α i)] (x : ∀ i, α i) {r : ℝ} (hr : 0 < r) :
    volume (Metric.ball x r) = ∏ i, volume (Metric.ball (x i) r) :=
  Measure.pi_ball _ _ hr
#align measure_theory.volume_pi_ball MeasureTheory.volume_pi_ball

theorem volume_pi_closedBall [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))]
    [∀ i, MetricSpace (α i)] (x : ∀ i, α i) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.closedBall x r) = ∏ i, volume (Metric.closedBall (x i) r) :=
  Measure.pi_closedBall _ _ hr
#align measure_theory.volume_pi_closed_ball MeasureTheory.volume_pi_closedBall

open Measure

/-- We intentionally restrict this only to the nondependent function space, since type-class
inference cannot find an instance for `ι → ℝ` when this is stated for dependent function spaces. -/
@[to_additive "We intentionally restrict this only to the nondependent function space, since
type-class inference cannot find an instance for `ι → ℝ` when this is stated for dependent function
spaces."]
instance Pi.isMulLeftInvariant_volume {α} [Group α] [MeasureSpace α]
    [SigmaFinite (volume : Measure α)] [MeasurableMul α] [MulLeftInvariant (volume : Measure α)] :
    MulLeftInvariant (volume : Measure (ι → α)) :=
  pi.isMulLeftInvariant _
#align measure_theory.pi.is_mul_left_invariant_volume MeasureTheory.Pi.isMulLeftInvariant_volume
#align measure_theory.pi.is_add_left_invariant_volume MeasureTheory.Pi.isAddLeftInvariant_volume

/-- We intentionally restrict this only to the nondependent function space, since type-class
inference cannot find an instance for `ι → ℝ` when this is stated for dependent function spaces. -/
@[to_additive "We intentionally restrict this only to the nondependent function space, since
type-class inference cannot find an instance for `ι → ℝ` when this is stated for dependent function
spaces."]
instance Pi.isInvInvariant_volume {α} [Group α] [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    [MeasurableInv α] [InvInvariant (volume : Measure α)] :
    InvInvariant (volume : Measure (ι → α)) :=
  pi.isInvInvariant _
#align measure_theory.pi.is_inv_invariant_volume MeasureTheory.Pi.isInvInvariant_volume
#align measure_theory.pi.is_neg_invariant_volume MeasureTheory.Pi.isNegInvariant_volume

/-!
### Measure preserving equivalences

In this section we prove that some measurable equivalences (e.g., between `Fin 1 → α` and `α` or
between `Fin 2 → α` and `α × α`) preserve measure or volume. These lemmas can be used to prove that
measures of corresponding sets (images or preimages) have equal measures and functions `f ∘ e` and
`f` have equal integrals, see lemmas in the `MeasureTheory.measurePreserving` prefix.
-/


section MeasurePreserving

theorem measurePreserving_piEquivPiSubtypeProd {ι : Type u} {α : ι → Type v} [Fintype ι]
    {m : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd α p) (Measure.pi μ)
      ((Measure.pi fun i : Subtype p => μ i).prod (Measure.pi fun i => μ i)) := by
  set e := (MeasurableEquiv.piEquivPiSubtypeProd α p).symm
  refine' MeasurePreserving.symm e _
  refine' ⟨e.measurable, (pi_eq fun s _ => _).symm⟩
  have : e ⁻¹' pi univ s =
      (pi univ fun i : { i // p i } => s i) ×ˢ pi univ fun i : { i // ¬p i } => s i :=
    Equiv.preimage_piEquivPiSubtypeProd_symm_pi p s
  rw [e.map_apply, this, prod_prod, pi_pi, pi_pi]
  exact Fintype.prod_subtype_mul_prod_subtype p fun i => μ i (s i)
#align measure_theory.measure_preserving_pi_equiv_pi_subtype_prod MeasureTheory.measurePreserving_piEquivPiSubtypeProd

theorem volume_preserving_piEquivPiSubtypeProd {ι : Type _} (α : ι → Type _) [Fintype ι]
    [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))] (p : ι → Prop)
    [DecidablePred p] : MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd α p) :=
  measurePreserving_piEquivPiSubtypeProd (fun _ => volume) p
#align measure_theory.volume_preserving_pi_equiv_pi_subtype_prod MeasureTheory.volume_preserving_piEquivPiSubtypeProd

theorem measurePreserving_piFinSuccAboveEquiv {n : ℕ} {α : Fin (n + 1) → Type u}
    {m : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (i : Fin (n + 1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAboveEquiv α i) (Measure.pi μ)
      ((μ i).prod <| Measure.pi fun j => μ (i.succAbove j)) := by
  set e := (MeasurableEquiv.piFinSuccAboveEquiv α i).symm
  refine' MeasurePreserving.symm e _
  refine' ⟨e.measurable, (pi_eq fun s _ => _).symm⟩
  rw [e.map_apply, i.prod_univ_succAbove _, ← pi_pi, ← prod_prod]
  congr 1 with ⟨x, f⟩
  simp [i.forall_iff_succAbove]
#align measure_theory.measure_preserving_pi_fin_succ_above_equiv MeasureTheory.measurePreserving_piFinSuccAboveEquiv

theorem volume_preserving_piFinSuccAboveEquiv {n : ℕ} (α : Fin (n + 1) → Type u)
    [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume : Measure (α i))] (i : Fin (n + 1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAboveEquiv α i) :=
  measurePreserving_piFinSuccAboveEquiv (fun _ => volume) i
#align measure_theory.volume_preserving_pi_fin_succ_above_equiv MeasureTheory.volume_preserving_piFinSuccAboveEquiv

theorem measurePreserving_funUnique {β : Type u} {m : MeasurableSpace β} (μ : Measure β)
    (α : Type v) [Unique α] :
    MeasurePreserving (MeasurableEquiv.funUnique α β) (Measure.pi fun _ : α => μ) μ := by
  set e := MeasurableEquiv.funUnique α β
  have : (piPremeasure fun _ : α => μ.toOuterMeasure) = Measure.map e.symm μ := by
    ext1 s
    rw [piPremeasure, Fintype.prod_unique, e.symm.map_apply]
    congr 1; exact e.toEquiv.image_eq_preimage s
  simp only [Measure.pi, OuterMeasure.pi, this, boundedBy_measure, toOuterMeasure_toMeasure]
  exact (e.symm.measurable.measurePreserving _).symm e.symm
#align measure_theory.measure_preserving_fun_unique MeasureTheory.measurePreserving_funUnique

theorem volume_preserving_funUnique (α : Type u) (β : Type v) [Unique α] [MeasureSpace β] :
    MeasurePreserving (MeasurableEquiv.funUnique α β) volume volume :=
  measurePreserving_funUnique volume α
#align measure_theory.volume_preserving_fun_unique MeasureTheory.volume_preserving_funUnique

theorem measurePreserving_piFinTwo {α : Fin 2 → Type u} {m : ∀ i, MeasurableSpace (α i)}
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.piFinTwo α) (Measure.pi μ) ((μ 0).prod (μ 1)) := by
  refine' ⟨MeasurableEquiv.measurable _, (Measure.prod_eq fun s t _ _ => _).symm⟩
  rw [MeasurableEquiv.map_apply, MeasurableEquiv.piFinTwo_apply, Fin.preimage_apply_01_prod,
    Measure.pi_pi, Fin.prod_univ_two]
  rfl
#align measure_theory.measure_preserving_pi_fin_two MeasureTheory.measurePreserving_piFinTwo

theorem volume_preserving_piFinTwo (α : Fin 2 → Type u) [∀ i, MeasureSpace (α i)]
    [∀ i, SigmaFinite (volume : Measure (α i))] :
    MeasurePreserving (MeasurableEquiv.piFinTwo α) volume volume :=
  measurePreserving_piFinTwo _
#align measure_theory.volume_preserving_pi_fin_two MeasureTheory.volume_preserving_piFinTwo

theorem measurePreserving_finTwoArrow_vec {α : Type u} {m : MeasurableSpace α} (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] :
    MeasurePreserving MeasurableEquiv.finTwoArrow (Measure.pi ![μ, ν]) (μ.prod ν) :=
  haveI : ∀ i, SigmaFinite (![μ, ν] i) := Fin.forall_fin_two.2 ⟨‹_›, ‹_›⟩
  measurePreserving_piFinTwo _
#align measure_theory.measure_preserving_fin_two_arrow_vec MeasureTheory.measurePreserving_finTwoArrow_vec

theorem measurePreserving_finTwoArrow {α : Type u} {m : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] :
    MeasurePreserving MeasurableEquiv.finTwoArrow (Measure.pi fun _ => μ) (μ.prod μ) := by
  simpa only [Matrix.vec_single_eq_const, Matrix.vecCons_const] using
    measurePreserving_finTwoArrow_vec μ μ
#align measure_theory.measure_preserving_fin_two_arrow MeasureTheory.measurePreserving_finTwoArrow

theorem volume_preserving_finTwoArrow (α : Type u) [MeasureSpace α]
    [SigmaFinite (volume : Measure α)] :
    MeasurePreserving (@MeasurableEquiv.finTwoArrow α _) volume volume :=
  measurePreserving_finTwoArrow volume
#align measure_theory.volume_preserving_fin_two_arrow MeasureTheory.volume_preserving_finTwoArrow

theorem measurePreserving_pi_empty {ι : Type u} {α : ι → Type v} [IsEmpty ι]
    {m : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i)) :
    MeasurePreserving (MeasurableEquiv.ofUniqueOfUnique (∀ i, α i) Unit) (Measure.pi μ)
      (Measure.dirac ()) := by
  set e := MeasurableEquiv.ofUniqueOfUnique (∀ i, α i) Unit
  refine' ⟨e.measurable, _⟩
  rw [Measure.pi_of_empty, Measure.map_dirac e.measurable]
#align measure_theory.measure_preserving_pi_empty MeasureTheory.measurePreserving_pi_empty

theorem volume_preserving_pi_empty {ι : Type u} (α : ι → Type v) [IsEmpty ι]
    [∀ i, MeasureSpace (α i)] :
    MeasurePreserving (MeasurableEquiv.ofUniqueOfUnique (∀ i, α i) Unit) volume volume :=
  measurePreserving_pi_empty fun _ => volume
#align measure_theory.volume_preserving_pi_empty MeasureTheory.volume_preserving_pi_empty

end MeasurePreserving

end MeasureTheory
