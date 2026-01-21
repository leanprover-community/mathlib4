/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.SuccPred.IntervalSucc

/-!
# Annulus

In this file we define annuli in (pseudo)(e)metric spaces.

For a point `x` and radii `r R`, the set `Metric.annulusIoo x r R` consists of all `y` such that
`dist y x ∈ Set.Ioo r R`. We provide analogous definitions for `Ioc`, `Ico`, `Icc`, and also for the
half-infinite intervals `Ioi`, `Ici` (these are complements of `closedBall`/`ball`).

We also define `EMetric.annulusIxx` using `edist` (hence radii in `ℝ≥0∞`), and relate these to
`Metric.annulusIxx` via `ENNReal.ofReal` when `edist = ENNReal.ofReal ∘ dist`.

## Tags

annulus
-/

@[expose] public section

open Set

open scoped ENNReal

namespace Metric

variable {X : Type*} [PseudoMetricSpace X]

/-! ### Annulus defined using `dist` -/

/-- The annulus `{y | dist y x ∈ Set.Ioo r R}` in a pseudo metric space. -/
def annulusIoo (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ioo r R
/-- The annulus `{y | dist y x ∈ Set.Ioc r R}` in a pseudo metric space. -/
def annulusIoc (x : X) (r R : ℝ) : Set X := (fun y : X => dist y x) ⁻¹' Ioc r R
/-- The annulus `{y | dist y x ∈ Set.Ico r R}` in a pseudo metric space. -/
def annulusIco (x : X) (r R : ℝ) : Set X := (fun y : X => dist y x) ⁻¹' Ico r R
/-- The annulus `{y | dist y x ∈ Set.Icc r R}` in a pseudo metric space. -/
def annulusIcc (x : X) (r R : ℝ) : Set X := (fun y : X => dist y x) ⁻¹' Icc r R
/-- The exterior `{y | dist y x ∈ Set.Ioi r}` (complement of `closedBall x r`). -/
def annulusIoi (x : X) (r : ℝ) : Set X := (fun y : X => dist y x) ⁻¹' Ioi r
/-- The exterior `{y | dist y x ∈ Set.Ici r}` (complement of `ball x r`). -/
def annulusIci (x : X) (r : ℝ) : Set X := (fun y : X => dist y x) ⁻¹' Ici r

lemma annulusIoo_eq {x : X} {r R : ℝ} :
    annulusIoo x r R = ball x R ∩ (closedBall x r)ᶜ := by
  ext y
  simp [annulusIoo, Metric.ball, Metric.closedBall, and_comm]

lemma annulusIoc_eq {x : X} {r R : ℝ} :
    annulusIoc x r R = closedBall x R ∩ (closedBall x r)ᶜ := by
  ext y
  simp [annulusIoc, Metric.closedBall, and_comm]

lemma annulusIco_eq {x : X} {r R : ℝ} :
    annulusIco x r R = ball x R ∩ (ball x r)ᶜ := by
  ext y
  simp [annulusIco, Metric.ball, and_comm]

lemma annulusIcc_eq {x : X} {r R : ℝ} :
    annulusIcc x r R = closedBall x R ∩ (ball x r)ᶜ := by
  ext y
  simp [annulusIcc, Metric.ball, Metric.closedBall, and_comm]

lemma annulusIoi_eq {x : X} {r : ℝ} : annulusIoi x r = (closedBall x r)ᶜ := by
  ext y
  simp [annulusIoi, Metric.closedBall]

lemma annulusIci_eq {x : X} {r : ℝ} : annulusIci x r = (ball x r)ᶜ := by
  ext y
  simp [annulusIci, Metric.ball]

@[simp] lemma annulusIoo_eq_empty {x : X} {r R : ℝ} (h : R ≤ r) : annulusIoo x r R = ∅ := by
  simp [annulusIoo, Ioo_eq_empty_of_le h]

@[simp] lemma annulusIoc_eq_empty {x : X} {r R : ℝ} (h : R ≤ r) : annulusIoc x r R = ∅ := by
  simp [annulusIoc, Ioc_eq_empty_of_le h]

@[simp] lemma annulusIco_eq_empty {x : X} {r R : ℝ} (h : R ≤ r) : annulusIco x r R = ∅ := by
  simp [annulusIco, Ico_eq_empty_of_le h]

@[simp] lemma annulusIcc_eq_empty {x : X} {r R : ℝ} (h : R < r) : annulusIcc x r R = ∅ := by
  simp [annulusIcc, Icc_eq_empty_of_lt h]

@[gcongr]
lemma annulusIoo_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIoo x r₁ R₁ ⊆ annulusIoo x r₂ R₂ := by
  intro y hy
  exact ⟨lt_of_le_of_lt hr hy.1, lt_of_lt_of_le hy.2 hR⟩

@[gcongr]
lemma annulusIoc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIoc x r₁ R₁ ⊆ annulusIoc x r₂ R₂ := by
  intro y hy
  exact ⟨lt_of_le_of_lt hr hy.1, hy.2.trans hR⟩

@[gcongr]
lemma annulusIco_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIco x r₁ R₁ ⊆ annulusIco x r₂ R₂ := by
  intro y hy
  exact ⟨hr.trans hy.1, lt_of_lt_of_le hy.2 hR⟩

@[gcongr]
lemma annulusIcc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIcc x r₁ R₁ ⊆ annulusIcc x r₂ R₂ := by
  intro y hy
  exact ⟨hr.trans hy.1, hy.2.trans hR⟩

lemma annulusIoo_subset_ball {x : X} {r R : ℝ} : annulusIoo x r R ⊆ ball x R := by
  intro y hy
  exact Metric.mem_ball.2 hy.2

lemma annulusIoc_subset_closedBall {x : X} {r R : ℝ} : annulusIoc x r R ⊆ closedBall x R := by
  intro y hy
  exact Metric.mem_closedBall.2 hy.2

lemma annulusIco_subset_ball {x : X} {r R : ℝ} : annulusIco x r R ⊆ ball x R := by
  intro y hy
  exact Metric.mem_ball.2 hy.2

lemma annulusIcc_subset_closedBall {x : X} {r R : ℝ} : annulusIcc x r R ⊆ closedBall x R := by
  intro y hy
  exact Metric.mem_closedBall.2 hy.2

@[simp]
lemma annulusIoc_union_annulusIoo {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' < R) :
    annulusIoc x r r' ∪ annulusIoo x r' R = annulusIoo x r R := by
  simpa [annulusIoc, annulusIoo, preimage_union] using
    congrArg (fun s : Set ℝ => (fun y : X => dist y x) ⁻¹' s) (Ioc_union_Ioo_eq_Ioo h₁ h₂)

@[simp]
lemma annulusIoc_union_annulusIoc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIoc x r r' ∪ annulusIoc x r' R = annulusIoc x r R := by
  simpa [annulusIoc, preimage_union] using
    congrArg (fun s : Set ℝ => (fun y : X => dist y x) ⁻¹' s) (Ioc_union_Ioc_eq_Ioc h₁ h₂)

@[simp]
lemma annulusIoo_union_annulusIco {x : X} {r r' R : ℝ} (h₁ : r < r') (h₂ : r' ≤ R) :
    annulusIoo x r r' ∪ annulusIco x r' R = annulusIoo x r R := by
  simpa [annulusIoo, annulusIco, preimage_union] using
    congrArg (fun s : Set ℝ => (fun y : X => dist y x) ⁻¹' s) (Ioo_union_Ico_eq_Ioo h₁ h₂)

@[simp]
lemma annulusIoo_union_annulusIcc {x : X} {r r' R : ℝ} (h₁ : r < r') (h₂ : r' ≤ R) :
    annulusIoo x r r' ∪ annulusIcc x r' R = annulusIoc x r R := by
  simpa [annulusIoo, annulusIcc, annulusIoc, preimage_union] using
    congrArg (fun s : Set ℝ => (fun y : X => dist y x) ⁻¹' s) (Ioo_union_Icc_eq_Ioc h₁ h₂)

@[simp]
lemma annulusIcc_union_annulusIoo {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' < R) :
    annulusIcc x r r' ∪ annulusIoo x r' R = annulusIco x r R := by
  simpa [annulusIcc, annulusIoo, annulusIco, preimage_union] using
    congrArg (fun s : Set ℝ => (fun y : X => dist y x) ⁻¹' s) (Icc_union_Ioo_eq_Ico h₁ h₂)

@[simp]
lemma annulusIcc_union_annulusIoc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIcc x r r' ∪ annulusIoc x r' R = annulusIcc x r R := by
  simpa [annulusIcc, annulusIoc, preimage_union] using
    congrArg (fun s : Set ℝ => (fun y : X => dist y x) ⁻¹' s) (Icc_union_Ioc_eq_Icc h₁ h₂)

@[simp]
lemma annulusIco_union_annulusIco {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIco x r r' ∪ annulusIco x r' R = annulusIco x r R := by
  simpa [annulusIco, preimage_union] using
    congrArg (fun s : Set ℝ => (fun y : X => dist y x) ⁻¹' s) (Ico_union_Ico_eq_Ico h₁ h₂)

@[simp]
lemma annulusIco_union_annulusIcc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIco x r r' ∪ annulusIcc x r' R = annulusIcc x r R := by
  simpa [annulusIco, annulusIcc, preimage_union] using
    congrArg (fun s : Set ℝ => (fun y : X => dist y x) ⁻¹' s) (Ico_union_Icc_eq_Icc h₁ h₂)

@[simp]
lemma annulusIoc_union_annulusIoi {x : X} {r R : ℝ} (h : r ≤ R) :
    annulusIoc x r R ∪ annulusIoi x R = annulusIoi x r := by
  simpa [annulusIoc, annulusIoi, preimage_union] using
    congrArg (fun s : Set ℝ => (fun y : X => dist y x) ⁻¹' s) (Ioc_union_Ioi_eq_Ioi h)

@[simp]
lemma annulusIoo_union_annulusIci {x : X} {r R : ℝ} (h : r < R) :
    annulusIoo x r R ∪ annulusIci x R = annulusIoi x r := by
  simpa [annulusIoo, annulusIci, annulusIoi, preimage_union] using
    congrArg (fun s : Set ℝ => (fun y : X => dist y x) ⁻¹' s) (Ioo_union_Ici_eq_Ioi h)

@[simp]
lemma annulusIcc_union_annulusIoi {x : X} {r R : ℝ} (h : r ≤ R) :
    annulusIcc x r R ∪ annulusIoi x R = annulusIci x r := by
  simpa [annulusIcc, annulusIoi, annulusIci, preimage_union] using
    congrArg (fun s : Set ℝ => (fun y : X => dist y x) ⁻¹' s) (Icc_union_Ioi_eq_Ici h)

@[simp]
lemma annulusIco_union_annulusIci {x : X} {r R : ℝ} (h : r ≤ R) :
    annulusIco x r R ∪ annulusIci x R = annulusIci x r := by
  simpa [annulusIco, annulusIci, preimage_union] using
    congrArg (fun s : Set ℝ => (fun y : X => dist y x) ⁻¹' s) (Ico_union_Ici_eq_Ici h)

theorem iUnion_annulusIco_eq_annulusIci {x : X} {f : ℕ → ℝ} (hf : ∀ n, f 0 ≤ f n)
    (h2f : ¬BddAbove (range f)) :
    (⋃ n : ℕ, annulusIco x (f n) (f (Nat.succ n))) = annulusIci x (f 0) := by
  simpa [annulusIco, annulusIci] using
    congrArg (fun s : Set ℝ => (fun y : X => dist y x) ⁻¹' s)
      (_root_.iUnion_Ico_map_succ_eq_Ici (β := ℝ) hf h2f)

theorem iUnion_annulusIoc_eq_annulusIoi {x : X} {f : ℕ → ℝ} (hf : ∀ n, f 0 ≤ f n)
    (h2f : ¬BddAbove (range f)) :
    (⋃ n : ℕ, annulusIoc x (f n) (f (Nat.succ n))) = annulusIoi x (f 0) := by
  simpa [annulusIoc, annulusIoi] using
    congrArg (fun s : Set ℝ => (fun y : X => dist y x) ⁻¹' s)
      (_root_.iUnion_Ioc_map_succ_eq_Ioi (β := ℝ) hf h2f)

end Metric

namespace EMetric

variable {X : Type*} [PseudoEMetricSpace X]

/-! ### Annulus defined using `edist` -/

/-- The annulus `{y | edist y x ∈ Set.Ioo r R}` in a pseudo emetric space. -/
def annulusIoo (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X => edist y x) ⁻¹' Ioo r R
/-- The annulus `{y | edist y x ∈ Set.Ioc r R}` in a pseudo emetric space. -/
def annulusIoc (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X => edist y x) ⁻¹' Ioc r R
/-- The annulus `{y | edist y x ∈ Set.Ico r R}` in a pseudo emetric space. -/
def annulusIco (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X => edist y x) ⁻¹' Ico r R
/-- The annulus `{y | edist y x ∈ Set.Icc r R}` in a pseudo emetric space. -/
def annulusIcc (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X => edist y x) ⁻¹' Icc r R
/-- The exterior `{y | edist y x ∈ Set.Ioi r}`. -/
def annulusIoi (x : X) (r : ℝ≥0∞) : Set X := (fun y : X => edist y x) ⁻¹' Ioi r
/-- The exterior `{y | edist y x ∈ Set.Ici r}`. -/
def annulusIci (x : X) (r : ℝ≥0∞) : Set X := (fun y : X => edist y x) ⁻¹' Ici r

@[simp] lemma annulusIoo_eq_preimage (x : X) (r R : ℝ≥0∞) :
    annulusIoo x r R = (fun y : X => edist y x) ⁻¹' Ioo r R := rfl
@[simp] lemma annulusIoc_eq_preimage (x : X) (r R : ℝ≥0∞) :
    annulusIoc x r R = (fun y : X => edist y x) ⁻¹' Ioc r R := rfl
@[simp] lemma annulusIco_eq_preimage (x : X) (r R : ℝ≥0∞) :
    annulusIco x r R = (fun y : X => edist y x) ⁻¹' Ico r R := rfl
@[simp] lemma annulusIcc_eq_preimage (x : X) (r R : ℝ≥0∞) :
    annulusIcc x r R = (fun y : X => edist y x) ⁻¹' Icc r R := rfl
@[simp] lemma annulusIoi_eq_preimage (x : X) (r : ℝ≥0∞) :
    annulusIoi x r = (fun y : X => edist y x) ⁻¹' Ioi r := rfl
@[simp] lemma annulusIci_eq_preimage (x : X) (r : ℝ≥0∞) :
    annulusIci x r = (fun y : X => edist y x) ⁻¹' Ici r := rfl

lemma annulusIoo_eq_empty {x : X} {r R : ℝ≥0∞} (h : R ≤ r) : annulusIoo x r R = ∅ := by
  simp [annulusIoo, Ioo_eq_empty_of_le h]

lemma annulusIoc_eq_empty {x : X} {r R : ℝ≥0∞} (h : R ≤ r) : annulusIoc x r R = ∅ := by
  simp [annulusIoc, Ioc_eq_empty_of_le h]

lemma annulusIco_eq_empty {x : X} {r R : ℝ≥0∞} (h : R ≤ r) : annulusIco x r R = ∅ := by
  simp [annulusIco, Ico_eq_empty_of_le h]

lemma annulusIcc_eq_empty {x : X} {r R : ℝ≥0∞} (h : R < r) : annulusIcc x r R = ∅ := by
  simp [annulusIcc, Icc_eq_empty_of_lt h]

@[gcongr]
lemma annulusIoo_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIoo x r₁ R₁ ⊆ annulusIoo x r₂ R₂ := by
  intro y hy
  exact ⟨lt_of_le_of_lt hr hy.1, lt_of_lt_of_le hy.2 hR⟩

@[gcongr]
lemma annulusIoc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIoc x r₁ R₁ ⊆ annulusIoc x r₂ R₂ := by
  intro y hy
  exact ⟨lt_of_le_of_lt hr hy.1, hy.2.trans hR⟩

@[gcongr]
lemma annulusIco_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIco x r₁ R₁ ⊆ annulusIco x r₂ R₂ := by
  intro y hy
  exact ⟨hr.trans hy.1, lt_of_lt_of_le hy.2 hR⟩

@[gcongr]
lemma annulusIcc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIcc x r₁ R₁ ⊆ annulusIcc x r₂ R₂ := by
  intro y hy
  exact ⟨hr.trans hy.1, hy.2.trans hR⟩

end EMetric
