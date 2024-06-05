/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue

/-!
# Marginals of multivariate functions

In this file, we define a convenient way to compute integrals of multivariate functions, especially
if you want to write expressions where you integrate only over some of the variables that the
function depends on. This is common in induction arguments involving integrals of multivariate
functions.
This constructions allows working with iterated integrals and applying Tonelli's theorem
and Fubini's theorem, without using measurable equivalences by changing the representation of your
space (e.g. `((ι ⊕ ι') → ℝ) ≃ (ι → ℝ) × (ι' → ℝ)`).

## Main Definitions

* Assume that `∀ i : ι, π i` is a product of measurable spaces with measures `μ i` on `π i`,
  `f : (∀ i, π i) → ℝ≥0∞` is a function and `s : Finset ι`.
  Then `lmarginal μ s f` or `∫⋯∫⁻_s, f ∂μ` is the function that integrates `f`
  over all variables in `s`. It returns a function that still takes the same variables as `f`,
  but is constant in the variables in `s`. Mathematically, if `s = {i₁, ..., iₖ}`,
  then `lmarginal μ s f` is the expression
  $$
  \vec{x}\mapsto \int\cdots\int f(\vec{x}[\vec{y}])dy_{i_1}\cdots dy_{i_k}.
  $$
  where $\vec{x}[\vec{y}]$ is the vector $\vec{x}$ with $x_{i_j}$ replaced by $y_{i_j}$ for all
  $1 \le j \le k$.
  If `f` is the distribution of a random variable, this is the marginal distribution of all
  variables not in `s` (but not the most general notion, since we only consider product measures
  here).
  Note that the notation `∫⋯∫⁻_s, f ∂μ` is not a binder, and returns a function.

## Main Results

* `lmarginal_union` is the analogue of Tonelli's theorem for iterated integrals. It states that
  for measurable functions `f` and disjoint finsets `s` and `t` we have
  `∫⋯∫⁻_s ∪ t, f ∂μ = ∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ`.

## Implementation notes

The function `f` can have an arbitrary product as its domain (even infinite products), but the
set `s` of integration variables is a `Finset`. We are assuming that the function `f` is measurable
for most of this file. Note that asking whether it is `AEMeasurable` is not even well-posed,
since there is no well-behaved measure on the domain of `f`.

## Todo

* Define the marginal function for functions taking values in a Banach space.

-/


open scoped Classical ENNReal
open Set Function Equiv Finset

noncomputable section

namespace MeasureTheory

section LMarginal

variable {δ δ' : Type*} {π : δ → Type*} [∀ x, MeasurableSpace (π x)]
variable {μ : ∀ i, Measure (π i)} [∀ i, SigmaFinite (μ i)] [DecidableEq δ]
variable {s t : Finset δ} {f g : (∀ i, π i) → ℝ≥0∞} {x y : ∀ i, π i} {i : δ}

/-- Integrate `f(x₁,…,xₙ)` over all variables `xᵢ` where `i ∈ s`. Return a function in the
  remaining variables (it will be constant in the `xᵢ` for `i ∈ s`).
  This is the marginal distribution of all variables not in `s` when the considered measure
  is the product measure. -/
def lmarginal (μ : ∀ i, Measure (π i)) (s : Finset δ) (f : (∀ i, π i) → ℝ≥0∞)
    (x : ∀ i, π i) : ℝ≥0∞ :=
  ∫⁻ y : ∀ i : s, π i, f (updateFinset x s y) ∂Measure.pi fun i : s => μ i

-- Note: this notation is not a binder. This is more convenient since it returns a function.
@[inherit_doc]
notation "∫⋯∫⁻_" s ", " f " ∂" μ:70 => lmarginal μ s f

@[inherit_doc]
notation "∫⋯∫⁻_" s ", " f => lmarginal (fun _ ↦ volume) s f

variable (μ)

theorem _root_.Measurable.lmarginal (hf : Measurable f) : Measurable (∫⋯∫⁻_s, f ∂μ) := by
  refine Measurable.lintegral_prod_right ?_
  refine hf.comp ?_
  rw [measurable_pi_iff]; intro i
  by_cases hi : i ∈ s
  · simp [hi, updateFinset]
    exact measurable_pi_iff.1 measurable_snd _
  · simp [hi, updateFinset]
    exact measurable_pi_iff.1 measurable_fst _

@[simp] theorem lmarginal_empty (f : (∀ i, π i) → ℝ≥0∞) : ∫⋯∫⁻_∅, f ∂μ = f := by
  ext1 x
  simp_rw [lmarginal, Measure.pi_of_empty fun i : (∅ : Finset δ) => μ i]
  apply lintegral_dirac'
  exact Subsingleton.measurable

/-- The marginal distribution is independent of the variables in `s`. -/
theorem lmarginal_congr {x y : ∀ i, π i} (f : (∀ i, π i) → ℝ≥0∞)
    (h : ∀ i ∉ s, x i = y i) :
    (∫⋯∫⁻_s, f ∂μ) x = (∫⋯∫⁻_s, f ∂μ) y := by
  dsimp [lmarginal, updateFinset_def]; rcongr; exact h _ ‹_›

theorem lmarginal_update_of_mem {i : δ} (hi : i ∈ s)
    (f : (∀ i, π i) → ℝ≥0∞) (x : ∀ i, π i) (y : π i) :
    (∫⋯∫⁻_s, f ∂μ) (Function.update x i y) = (∫⋯∫⁻_s, f ∂μ) x := by
  apply lmarginal_congr
  intro j hj
  have : j ≠ i := by rintro rfl; exact hj hi
  apply update_noteq this

theorem lmarginal_union (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f)
    (hst : Disjoint s t) : ∫⋯∫⁻_s ∪ t, f ∂μ = ∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ := by
  ext1 x
  let e := MeasurableEquiv.piFinsetUnion π hst
  calc (∫⋯∫⁻_s ∪ t, f ∂μ) x
      = ∫⁻ (y : (i : ↥(s ∪ t)) → π i), f (updateFinset x (s ∪ t) y)
          ∂.pi fun i' : ↥(s ∪ t) ↦ μ i' := rfl
    _ = ∫⁻ (y : ((i : s) → π i) × ((j : t) → π j)), f (updateFinset x (s ∪ t) _)
          ∂(Measure.pi fun i : s ↦ μ i).prod (.pi fun j : t ↦ μ j) := by
        rw [measurePreserving_piFinsetUnion hst μ |>.lintegral_map_equiv]
    _ = ∫⁻ (y : (i : s) → π i), ∫⁻ (z : (j : t) → π j), f (updateFinset x (s ∪ t) (e (y, z)))
          ∂.pi fun j : t ↦ μ j ∂.pi fun i : s ↦ μ i := by
        apply lintegral_prod
        apply Measurable.aemeasurable
        exact hf.comp <| measurable_updateFinset.comp e.measurable
    _ = (∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ) x := by
        simp_rw [lmarginal, updateFinset_updateFinset hst]
        rfl

theorem lmarginal_union' (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {s t : Finset δ}
    (hst : Disjoint s t) : ∫⋯∫⁻_s ∪ t, f ∂μ = ∫⋯∫⁻_t, ∫⋯∫⁻_s, f ∂μ ∂μ := by
  rw [Finset.union_comm, lmarginal_union μ f hf hst.symm]

variable {μ}

set_option backward.synthInstance.canonInstances false in -- See https://github.com/leanprover-community/mathlib4/issues/12532
theorem lmarginal_singleton (f : (∀ i, π i) → ℝ≥0∞) (i : δ) :
    ∫⋯∫⁻_{i}, f ∂μ = fun x => ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i := by
  let α : Type _ := ({i} : Finset δ)
  let e := (MeasurableEquiv.piUnique fun j : α ↦ π j).symm
  ext1 x
  calc (∫⋯∫⁻_{i}, f ∂μ) x
      = ∫⁻ (y : π (default : α)), f (updateFinset x {i} (e y)) ∂μ (default : α) := by
        simp_rw [lmarginal, measurePreserving_piUnique (fun j : ({i} : Finset δ) ↦ μ j) |>.symm _
          |>.lintegral_map_equiv]
    _ = ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i := by simp [update_eq_updateFinset]; rfl

/-- Peel off a single integral from a `lmarginal` integral at the beginning (compare with
`lmarginal_insert'`, which peels off an integral at the end). -/
theorem lmarginal_insert (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∉ s) (x : ∀ i, π i) :
    (∫⋯∫⁻_insert i s, f ∂μ) x = ∫⁻ xᵢ, (∫⋯∫⁻_s, f ∂μ) (Function.update x i xᵢ) ∂μ i := by
  rw [Finset.insert_eq, lmarginal_union μ f hf (Finset.disjoint_singleton_left.mpr hi),
    lmarginal_singleton]

/-- Peel off a single integral from a `lmarginal` integral at the beginning (compare with
`lmarginal_erase'`, which peels off an integral at the end). -/
theorem lmarginal_erase (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∈ s) (x : ∀ i, π i) :
    (∫⋯∫⁻_s, f ∂μ) x = ∫⁻ xᵢ, (∫⋯∫⁻_(erase s i), f ∂μ) (Function.update x i xᵢ) ∂μ i := by
  simpa [insert_erase hi] using lmarginal_insert _ hf (not_mem_erase i s) x

/-- Peel off a single integral from a `lmarginal` integral at the end (compare with
`lmarginal_insert`, which peels off an integral at the beginning). -/
theorem lmarginal_insert' (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∉ s) :
    ∫⋯∫⁻_insert i s, f ∂μ = ∫⋯∫⁻_s, (fun x ↦ ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ∂μ := by
  rw [Finset.insert_eq, Finset.union_comm,
    lmarginal_union (s := s) μ f hf (Finset.disjoint_singleton_right.mpr hi), lmarginal_singleton]

/-- Peel off a single integral from a `lmarginal` integral at the end (compare with
`lmarginal_erase`, which peels off an integral at the beginning). -/
theorem lmarginal_erase' (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∈ s) :
    ∫⋯∫⁻_s, f ∂μ = ∫⋯∫⁻_(erase s i), (fun x ↦ ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ∂μ := by
  simpa [insert_erase hi] using lmarginal_insert' _ hf (not_mem_erase i s)

open Filter

@[gcongr]
theorem lmarginal_mono {f g : (∀ i, π i) → ℝ≥0∞} (hfg : f ≤ g) : ∫⋯∫⁻_s, f ∂μ ≤ ∫⋯∫⁻_s, g ∂μ :=
  fun _ => lintegral_mono fun _ => hfg _

@[simp] theorem lmarginal_univ [Fintype δ] {f : (∀ i, π i) → ℝ≥0∞} :
    ∫⋯∫⁻_univ, f ∂μ = fun _ => ∫⁻ x, f x ∂Measure.pi μ := by
  let e : { j // j ∈ Finset.univ } ≃ δ := Equiv.subtypeUnivEquiv mem_univ
  ext1 x
  simp_rw [lmarginal, measurePreserving_piCongrLeft μ e |>.lintegral_map_equiv, updateFinset_def]
  simp
  rfl

theorem lintegral_eq_lmarginal_univ [Fintype δ] {f : (∀ i, π i) → ℝ≥0∞} (x : ∀ i, π i) :
    ∫⁻ x, f x ∂Measure.pi μ = (∫⋯∫⁻_univ, f ∂μ) x := by simp

theorem lmarginal_image [DecidableEq δ'] {e : δ' → δ} (he : Injective e) (s : Finset δ')
    {f : (∀ i, π (e i)) → ℝ≥0∞} (hf : Measurable f) (x : ∀ i, π i) :
      (∫⋯∫⁻_s.image e, f ∘ (· ∘' e) ∂μ) x = (∫⋯∫⁻_s, f ∂μ ∘' e) (x ∘' e) := by
  have h : Measurable ((· ∘' e) : (∀ i, π i) → _) :=
    measurable_pi_iff.mpr <| fun i ↦ measurable_pi_apply (e i)
  induction s using Finset.induction generalizing x with
  | empty => simp
  | insert hi ih =>
    rw [image_insert, lmarginal_insert _ (hf.comp h) (he.mem_finset_image.not.mpr hi),
      lmarginal_insert _ hf hi]
    simp_rw [ih, ← update_comp_eq_of_injective' x he]

theorem lmarginal_update_of_not_mem {i : δ}
    {f : (∀ i, π i) → ℝ≥0∞} (hf : Measurable f) (hi : i ∉ s) (x : ∀ i, π i) (y : π i) :
    (∫⋯∫⁻_s, f ∂μ) (Function.update x i y) = (∫⋯∫⁻_s, f ∘ (Function.update · i y) ∂μ) x := by
  induction s using Finset.induction generalizing x with
  | empty => simp
  | @insert i' s hi' ih =>
    rw [lmarginal_insert _ hf hi', lmarginal_insert _ (hf.comp measurable_update_left) hi']
    have hii' : i ≠ i' := mt (by rintro rfl; exact mem_insert_self i s) hi
    simp_rw [update_comm hii', ih (mt Finset.mem_insert_of_mem hi)]

theorem lmarginal_eq_of_subset {f g : (∀ i, π i) → ℝ≥0∞} (hst : s ⊆ t)
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ = ∫⋯∫⁻_s, g ∂μ) :
    ∫⋯∫⁻_t, f ∂μ = ∫⋯∫⁻_t, g ∂μ := by
  rw [← union_sdiff_of_subset hst, lmarginal_union' μ f hf disjoint_sdiff,
    lmarginal_union' μ g hg disjoint_sdiff, hfg]

theorem lmarginal_le_of_subset {f g : (∀ i, π i) → ℝ≥0∞} (hst : s ⊆ t)
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ ≤ ∫⋯∫⁻_s, g ∂μ) :
    ∫⋯∫⁻_t, f ∂μ ≤ ∫⋯∫⁻_t, g ∂μ := by
  rw [← union_sdiff_of_subset hst, lmarginal_union' μ f hf disjoint_sdiff,
    lmarginal_union' μ g hg disjoint_sdiff]
  exact lmarginal_mono hfg

theorem lintegral_eq_of_lmarginal_eq [Fintype δ] (s : Finset δ) {f g : (∀ i, π i) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ = ∫⋯∫⁻_s, g ∂μ) :
    ∫⁻ x, f x ∂Measure.pi μ = ∫⁻ x, g x ∂Measure.pi μ := by
  rcases isEmpty_or_nonempty (∀ i, π i) with h|⟨⟨x⟩⟩
  · simp_rw [lintegral_of_isEmpty]
  simp_rw [lintegral_eq_lmarginal_univ x, lmarginal_eq_of_subset (Finset.subset_univ s) hf hg hfg]

theorem lintegral_le_of_lmarginal_le [Fintype δ] (s : Finset δ) {f g : (∀ i, π i) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ ≤ ∫⋯∫⁻_s, g ∂μ) :
    ∫⁻ x, f x ∂Measure.pi μ ≤ ∫⁻ x, g x ∂Measure.pi μ := by
  rcases isEmpty_or_nonempty (∀ i, π i) with h|⟨⟨x⟩⟩
  · simp_rw [lintegral_of_isEmpty, le_rfl]
  simp_rw [lintegral_eq_lmarginal_univ x, lmarginal_le_of_subset (Finset.subset_univ s) hf hg hfg x]

end LMarginal

-- not yet PR'd results below this!!

section

/-! Compute some measures using marginal. -/

variable {n : ℕ} {α : Fin (n+1) → Type*} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
variable [∀ i, SigmaFinite (μ i)]

open Fin

@[simp]
theorem insertNth_dcomp_succAbove (i : Fin (n + 1)) (x : α i) (p : ∀ j, α (i.succAbove j)) :
    insertNth i x p ∘' i.succAbove = p :=
  funext (insertNth_apply_succAbove i x p)

@[simp]
theorem insertNth_apply_dcomp_succAbove (i : Fin (n + 1)) (x : α i) (z : ∀ i, α i) :
    insertNth i x (z ∘' i.succAbove) = update z i x := by
  ext j
  rcases eq_or_ne i j with rfl|hij
  · simp
  obtain ⟨j', rfl⟩ := exists_succAbove_eq_iff.mpr hij.symm
  simp [dcomp, hij.symm]

theorem insertNth_comp_dcomp_succAbove (i : Fin (n + 1)) (x : α i) :
    insertNth i x ∘ (· ∘' i.succAbove) = (update · i x) := by
  simp [comp]

theorem insertNth_eq_of_ne {i j : Fin (n + 1)} (h : i ≠ j) (x x' : α i)
    (p : ∀ j, α (i.succAbove j)) : insertNth i x p j = insertNth i x' p j := by
  obtain ⟨j', rfl⟩ := exists_succAbove_eq_iff.mpr h.symm
  simp

@[simp]
theorem update_insertNth {i : Fin (n + 1)} (x x' : α i) (p : ∀ j, α (i.succAbove j)) :
    update (insertNth i x p) i x' = insertNth i x' p := by
  ext j
  rcases eq_or_ne i j with rfl|hij
  · simp
  simp [hij.symm, insertNth_eq_of_ne hij x x']

theorem measurable_insertNth {i : Fin (n+1)} (x : α i) :
    Measurable (insertNth i x) := by
  refine measurable_pi_iff.mpr fun j ↦ ?_
  rcases eq_or_ne i j with rfl|hij
  · simp
  obtain ⟨j', rfl⟩ := exists_succAbove_eq_iff.mpr hij.symm
  simp [measurable_pi_apply]

/-- An example of a computation we can do with `lmarginal`. Working with `lmarginal` directly is
  probably easier than using this lemma, though. This is roughly `FUBINI_SIMPLE` from HOL Light,
  though this has weaker assumptions (HOL Light assumes that `s` is bounded in `ℝⁿ`).
  Note: we could generalize `i.succAbove : Fin n → Fin (n+1)` to an arbitrary injective map `ι → ι'`
  whose range misses one point. -/
theorem lintegral_measure_insertNth {s : Set (∀ i, α i)} (hs : MeasurableSet s) (i : Fin (n+1)) :
    ∫⁻ x, Measure.pi (μ ∘' i.succAbove) (insertNth i x ⁻¹' s) ∂μ i =
    Measure.pi μ s := by
  rcases isEmpty_or_nonempty (α i) with h|⟨⟨x⟩⟩
  · have : IsEmpty (∀ i, α i) := ⟨λ x ↦ h.elim <| x i⟩
    simp [lintegral_of_isEmpty, Measure.eq_zero_of_isEmpty]
  rcases isEmpty_or_nonempty (∀ j, α (i.succAbove j)) with h|⟨⟨y⟩⟩
  · have : IsEmpty (∀ i, α i) := ⟨λ x ↦ h.elim <| λ j ↦ x _⟩
    simp [Measure.eq_zero_of_isEmpty]
  have hi : i ∉ ({i}ᶜ : Finset _) := not_mem_compl.mpr <| mem_singleton_self i
  let z := insertNth i x y
  calc ∫⁻ x : α i, Measure.pi (μ ∘' succAbove i) (insertNth i x ⁻¹' s) ∂μ i
      = ∫⁻ x : α i, (∫⋯∫⁻_.univ, indicator (insertNth i x ⁻¹' s) 1 ∂μ ∘' succAbove i) y ∂μ i := by
        simp_rw [← lintegral_indicator_one (measurable_insertNth _ hs),
          lintegral_eq_lmarginal_univ y]
    _ = ∫⁻ x : α i, (∫⋯∫⁻_.univ, indicator (insertNth i x ⁻¹' s) 1 ∂μ ∘' succAbove i)
          (z ∘' i.succAbove) ∂μ i := by
        rw [← insertNth_dcomp_succAbove i x y]
    _ = ∫⁻ x : α i, (∫⋯∫⁻_{i}ᶜ,
          indicator (insertNth i x ⁻¹' s) 1 ∘ (· ∘' succAbove i) ∂μ) z ∂μ i := by
        simp_rw [← λ x ↦ lmarginal_image succAbove_right_injective (μ := μ) .univ
          (f := indicator (insertNth i x ⁻¹' s) (1 : ((j : Fin n) → α (succAbove i j)) → ℝ≥0∞))
          (measurable_one.indicator (measurable_insertNth _ hs)) z, Fin.image_succAbove_univ]
    _ = ∫⁻ x : α i, (∫⋯∫⁻_{i}ᶜ,
          indicator (insertNth i x ∘ (· ∘' succAbove i) ⁻¹' s) 1 ∂μ) z ∂μ i := by
        rfl
    _ = ∫⁻ x : α i, (∫⋯∫⁻_{i}ᶜ,
          indicator ((Function.update · i x) ⁻¹' s) 1 ∂μ) z ∂μ i := by
        simp [comp]
    _ = (∫⋯∫⁻_insert i {i}ᶜ, indicator s 1 ∂μ) z := by
        simp_rw [lmarginal_insert _ (measurable_one.indicator hs) hi,
          lmarginal_update_of_not_mem (measurable_one.indicator hs) hi]
        rfl
    _ = (∫⋯∫⁻_.univ, indicator s 1 ∂μ) z := by simp
    _ = Measure.pi μ s := by rw [← lintegral_indicator_one hs, lintegral_eq_lmarginal_univ z]

end

section MeasureSpace

/-! Compute some measures using marginal. -/

variable {n : ℕ} {α : Fin (n+1) → Type*}
variable [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume (α := α i))]

open Fin

theorem lintegral_volume_insertNth {s : Set (∀ i, α i)} (hs : MeasurableSet s) (i : Fin (n+1)) :
    ∫⁻ x, volume (insertNth i x ⁻¹' s) = volume s :=
  lintegral_measure_insertNth (fun _ ↦ volume) hs i

end MeasureSpace

end MeasureTheory
