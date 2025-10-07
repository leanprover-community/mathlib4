/-
Copyright (c) 2025 Janette Setälä, Yaël Dillies, Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janette Setälä, Yaël Dillies, Kalle Kytölä
-/
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Embedding a countably separated space inside a space of sequences

This file proves that a topological `X` separated by countably many continuous functions `X → Y n`
where the `Y n` are metric spaces, then `X` can be embedded inside the product `∀ n, Y n`.
-/

-- TODO: Tag in mathlib
attribute [simp] abs_mul abs_inv ENNReal.ofReal_mul ENNReal.ofReal_inv_of_pos ENNReal.ofReal_pow

namespace ENNReal

lemma ofReal_mono : Monotone ENNReal.ofReal := fun _ _ ↦ ENNReal.ofReal_le_ofReal

@[simp] lemma ofReal_min (x y : ℝ) : ENNReal.ofReal (min x y) = min (.ofReal x) (.ofReal y) :=
  ofReal_mono.map_min

@[simp] lemma ofReal_dist {X : Type*} [PseudoMetricSpace X] (x y : X) :
    .ofReal (dist x y) = edist x y := by simp [edist_dist]

@[simp] lemma min_eq_zero {x y : ℝ≥0∞} : min x y = 0 ↔ x = 0 ∨ y = 0 := min_eq_bot

end ENNReal

namespace PseudoMetricSpace
variable {X : Type*}

/-- Build a new pseudometric space from an old one where the distance uniform structure is provably
(but typically non-definitionaly) equal to some given distance structure. -/
-- See note [forgetful inheritance]
-- See note [reducible non-instances]
abbrev replaceDist (m : PseudoMetricSpace X) (d : X → X → ℝ) (hd : d = dist) :
    PseudoMetricSpace X where
  dist := d
  dist_self := by simp [hd]
  dist_comm := by simp [hd, dist_comm]
  dist_triangle := by simp [hd, dist_triangle]
  edist_dist := by simp [hd, edist_dist]
  uniformity_dist := by simp [hd, uniformity_dist]
  cobounded_sets := by simp [hd, cobounded_sets]
  __ := m

lemma replaceDist_eq (m : PseudoMetricSpace X) (d : X → X → ℝ) (hd : d = dist) :
    m.replaceDist d hd = m := by ext : 2; exact hd

end PseudoMetricSpace

namespace PseudoEMetricSpace

/-- One gets a pseudometric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the pseudometric space and the pseudoemetric space. In this definition, the
distance is given separately, to be able to prescribe some expression which is not defeq to the
push-forward of the edistance to reals. See note [reducible non-instances]. -/
abbrev toPseudoMetricSpaceOfDist' {X : Type*} [e : PseudoEMetricSpace X] (dist : X → X → ℝ)
    (dist_nonneg : ∀ x y, 0 ≤ dist x y)
    (h : ∀ x y, edist x y = .ofReal (dist x y)) : PseudoMetricSpace X where
  dist := dist
  dist_self x := by simpa [h, (dist_nonneg _ _).ge_iff_eq', -edist_self] using edist_self x
  dist_comm x y := by simpa [h, dist_nonneg] using edist_comm x y
  dist_triangle x y z := by
    simpa [h, dist_nonneg, add_nonneg, ← ENNReal.ofReal_add] using edist_triangle x y z
  edist := edist
  edist_dist _ _ := by simp only [h]
  toUniformSpace := toUniformSpace
  uniformity_dist := e.uniformity_edist.trans <| by
    simpa [h, dist_nonneg, ENNReal.coe_toNNReal_eq_toReal]
      using (Metric.uniformity_edist_aux fun x y : X => (edist x y).toNNReal).symm

end PseudoEMetricSpace

open Function Topology

variable {X : Type*} {Y : ℕ → Type*} {f : ∀ n, X → Y n}

namespace Metric

include f in
variable (X Y f) in
/-- Given a type `X` and a sequence `Y` of metric spaces and a sequence `f : : ∀ n, X → Y n` of
separating functions, `PiNatEmbed X Y f` is a type synonym for `X` seen as a subset of `∀ n, Y n`.
-/
structure PiNatEmbed (X : Type*) (Y : ℕ → Type*) (f : ∀ n, X → Y n) where
  /-- The map from `X` to the subset of `∀ n, Y n`. -/
  toPiNat ::
  /-- The map from the subset of `∀ n, Y n` to `X`. -/
  ofPiNat : X

namespace PiNatEmbed

@[ext] lemma ext {x y : PiNatEmbed X Y f} (hxy : x.ofPiNat = y.ofPiNat) : x = y := by
  cases x; congr!

variable (X Y f) in
/-- Equivalence between `X` and its embedding into `∀ n, Y n`. -/
@[simps]
def toPiNatEquiv : X ≃ PiNatEmbed X Y f where
  toFun := toPiNat
  invFun := ofPiNat
  left_inv _ := rfl
  right_inv _ := rfl

section PseudoEMetricSpace
variable [∀ n, PseudoEMetricSpace (Y n)]

private noncomputable abbrev truncEDist (x y : PiNatEmbed X Y f) (n : ℕ) :=
  (1 / 2) ^ n * min (edist (f n x.ofPiNat) (f n y.ofPiNat)) 1

private lemma truncEDist_le_geometric {x y : PiNatEmbed X Y f} (n : ℕ) :
    truncEDist x y n ≤ (1 / 2) ^ n := by
  transitivity (1 / 2) ^ n * 1
  · unfold truncEDist
    gcongr
    exact min_le_right ..
  · simp

noncomputable instance : PseudoEMetricSpace (PiNatEmbed X Y f) where
  edist x y := ∑' n, truncEDist x y n
  edist_self x := by simp
  edist_comm x y := by simp [truncEDist, edist_comm]
  edist_triangle x y z := calc
        ∑' n, truncEDist x z n
    _ ≤ ∑' n, (truncEDist x y n + truncEDist y z n) := by
      gcongr with n
      simp_rw [← mul_add, truncEDist]
      gcongr
      calc
            min (edist (f n x.ofPiNat) (f n z.ofPiNat)) 1
        _ ≤ min (edist (f n x.ofPiNat) (f n y.ofPiNat) +
              edist (f n y.ofPiNat) (f n z.ofPiNat)) 1 := by
          gcongr; exact edist_triangle (f n x.ofPiNat) (f n y.ofPiNat) (f n z.ofPiNat)
        _ ≤ min (edist (f n x.ofPiNat) (f n y.ofPiNat)) 1 +
              min (edist (f n y.ofPiNat) (f n z.ofPiNat)) 1 := by
          obtain hxy | hxy := le_total (edist (f n x.ofPiNat) (f n y.ofPiNat)) 1 <;>
            obtain hyz | hyz := le_total (edist (f n y.ofPiNat) (f n z.ofPiNat)) 1 <;>
              simp [*]
    _ = _ := ENNReal.tsum_add ..

lemma edist_def (x y : PiNatEmbed X Y f) :
    edist x y = ∑' n, (1/2) ^ n * min (edist (f n x.ofPiNat) (f n y.ofPiNat)) 1 := rfl

end PseudoEMetricSpace

section PseudoMetricSpace
variable [∀ n, PseudoMetricSpace (Y n)]

private lemma min_le_geometric {x y : X} (n : ℕ) :
    ‖(1 / 2) ^ n * min (dist (f n x) (f n y)) 1‖ ≤ (1 / 2) ^ n := by
  simp [abs_of_nonneg]

private lemma summable_min {x y : X} :
    Summable fun n ↦ (1 / 2) ^ n * min (dist (f n x) (f n y)) 1 :=
  summable_geometric_two.of_norm_bounded min_le_geometric

noncomputable instance : PseudoMetricSpace (PiNatEmbed X Y f) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist'
    (fun x y ↦ ∑' n, (1/2) ^ n * min (dist (f n x.ofPiNat) (f n y.ofPiNat)) 1)
    (fun x y ↦ by dsimp; positivity) fun x y ↦ by
      rw [edist_def, ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) summable_min]
      simp [edist, ENNReal.inv_pow]

lemma dist_def (x y : PiNatEmbed X Y f) :
    dist x y = ∑' n, (1/2) ^ n * min (dist (f n x.ofPiNat) (f n y.ofPiNat)) 1 := rfl

variable [TopologicalSpace X]

lemma continuous_toPiNat (continuous_f : ∀ n, Continuous (f n)) :
    Continuous (toPiNat : X → PiNatEmbed X Y f) := by
  rw [continuous_iff_continuous_dist]
  exact continuous_tsum (by fun_prop) summable_geometric_two fun n (a, b) ↦ min_le_geometric _

end PseudoMetricSpace

section EMetricSpace
variable [∀ n, EMetricSpace (Y n)]

/-- If the functions `f n : X → Y n` separate points of `X`, then `X` can be embedded into
`∀ n, Y n`. -/
noncomputable abbrev emetricSpace (separating_f : Pairwise fun x y ↦ ∃ n, f n x ≠ f n y) :
    EMetricSpace (PiNatEmbed X Y f) where
  eq_of_edist_eq_zero hxy := by ext; exact separating_f.eq <| by simpa [edist_def] using hxy

end EMetricSpace

section MetricSpace
variable [∀ n, MetricSpace (Y n)]

/-- If the functions `f n : X → Y n` separate points of `X`, then `X` can be embedded into
`∀ n, Y n`. -/
noncomputable abbrev metricSpace (separating_f : Pairwise fun x y ↦ ∃ n, f n x ≠ f n y) :
    MetricSpace (PiNatEmbed X Y f) :=
  (emetricSpace separating_f).toMetricSpace fun x y ↦ by simp [← ENNReal.ofReal_dist]

variable [TopologicalSpace X] [CompactSpace X]

lemma isHomeomorph_toPiNat (continuous_f : ∀ n, Continuous (f n))
    (separating_f : Pairwise fun x y ↦ ∃ n, f n x ≠ f n y) :
    IsHomeomorph (toPiNat : X → PiNatEmbed X Y f) := by
  letI := emetricSpace separating_f
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨continuous_toPiNat continuous_f, (toPiNatEquiv X Y f).bijective⟩

variable (X Y f) in
/-- Homeomorphism between `X` and its embedding into `∀ n, Y n` induced by a separating family of
continuous functions `f n : X → Y n`. -/
@[simps!]
noncomputable def toPiNatHomeo (continuous_f : ∀ n, Continuous (f n))
    (separating_f : Pairwise fun x y ↦ ∃ n, f n x ≠ f n y) :
    X ≃ₜ PiNatEmbed X Y f :=
  (toPiNatEquiv X Y f).toHomeomorphOfIsInducing
    (isHomeomorph_toPiNat continuous_f separating_f).isInducing

end MetricSpace
end Metric.PiNatEmbed

variable [TopologicalSpace X] [CompactSpace X] [∀ n, MetricSpace (Y n)]

/-- If `X` is compact, and there exists a sequence of continuous functions `f n : X → Y n` to
metric spaces `Y n` that separate points on `X`, then `X` is metrizable. -/
lemma TopologicalSpace.MetrizableSpace.of_countable_separating (f : ∀ n, X → Y n)
    (continuous_f : ∀ n, Continuous (f n)) (separating_f : Pairwise fun x y ↦ ∃ n, f n x ≠ f n y) :
    MetrizableSpace X :=
  letI := Metric.PiNatEmbed.metricSpace separating_f
  (Metric.PiNatEmbed.toPiNatHomeo X Y f continuous_f separating_f).isEmbedding.metrizableSpace
