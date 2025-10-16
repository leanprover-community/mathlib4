/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.SetIntegral

/-!
# Ionescu-Tulcea theorem

This file proves the *Ionescu-Tulcea theorem*. The idea of the statement is as follows:
consider a family of kernels `κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))`.
One can interpret `κ n` as a kernel which takes as an input the trajectory of a point started in
`X 0` and moving `X 0 → X 1 → X 2 → ... → X n` and which outputs the distribution of the next
position of the point in `X (n + 1)`. If `a b : ℕ` and `a < b`, we can compose the kernels,
and `κ a ⊗ₖ κ (a + 1) ⊗ₖ ... ⊗ₖ κ b` will take the trajectory up to time `a` as input and outputs
the distribution of the trajectory on `X (a + 1) × ... × X (b + 1)`.

The Ionescu-Tulcea theorem tells us that these compositions can be extended into a
`Kernel (Π i : Iic a, X i) (Π n > a, X n)` which given the trajectory up to time `a` outputs
the distribution of the infinite trajectory started in `X (a + 1)`. In other words this theorem
makes sense of composing infinitely many kernels together.

In this file we construct this "limit" kernel given the family `κ`. More precisely, for any `a : ℕ`,
we construct the kernel `traj κ a : Kernel (Π i : Iic a, X i) (Π n, X n)`, which takes as input
the trajectory in `X 0 × ... × X a` and outputs the distribution of the whole trajectory. The name
`traj` thus stands for "trajectory". We build a kernel with output in `Π n, X n` instead of
`Π i > a, X i` to make manipulations easier. The first coordinates are deterministic.

We also provide tools to compute integrals against `traj κ a` and an expression for the conditional
expectation.

## Main definition

* `traj κ a`: a kernel from `Π i : Iic a, X i` to `Π n, X n` which takes as input a trajectory
  up to time `a` and outputs the distribution of the trajectory obtained by iterating the kernels
  `κ`. Its existence is given by the Ionescu-Tulcea theorem.

## Main statements

* `eq_traj`: Uniqueness of `traj`: to check that `η = traj κ a` it is enough to show that
  the restriction of `η` to variables `≤ b` is `partialTraj κ a b`.
* `traj_comp_partialTraj`: Given the distribution up to time `a`, `partialTraj κ a b`
  gives the distribution of the trajectory up to time `b`, and composing this with
  `traj κ b` gives the distribution of the whole trajectory.
* `condExp_traj`: If `a ≤ b`, the conditional expectation of `f` with respect to `traj κ a`
  given the information up to time `b` is obtained by integrating `f` against `traj κ b`.

## Implementation notes

The kernel `traj κ a` is built using the Carathéodory extension theorem. First we build a projective
family of measures using `inducedFamily` and `partialTraj κ a`. Then we build a
`MeasureTheory.AddContent` on `MeasureTheory.measurableCylinders` called `trajContent` using
`projectiveFamilyContent`. Finally we prove `trajContent_tendsto_zero` which implies the
`σ`-additivity of the content, allowing to turn it into a measure.

## References

We follow the proof of Theorem 8.24 in
[O. Kallenberg, *Foundations of Modern Probability*][kallenberg2021]. For a more detailed proof
in the case of constant kernels (i.e. measures),
see Proposition 10.6.1 in [D. L. Cohn, *Measure Theory*][cohn2013measure].

## Tags

Ionescu-Tulcea theorem
-/

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory

open scoped ENNReal Topology

variable {X : ℕ → Type*}

section castLemmas

private lemma Iic_pi_eq {a b : ℕ} (h : a = b) :
    (Π i : Iic a, X i) = (Π i : Iic b, X i) := by cases h; rfl

private lemma cast_pi {s t : Set ℕ} (h : s = t) (x : (i : s) → X i) (i : t) :
    cast (congrArg (fun u : Set ℕ ↦ (Π i : u, X i)) h) x i = x ⟨i.1, h.symm ▸ i.2⟩ := by
  cases h; rfl

variable [∀ n, MeasurableSpace (X n)]

private lemma measure_cast {a b : ℕ} (h : a = b) (μ : (n : ℕ) → Measure (Π i : Iic n, X i)) :
    (μ a).map (cast (Iic_pi_eq h)) = μ b := by
  cases h
  exact Measure.map_id

private lemma heq_measurableSpace_Iic_pi {a b : ℕ} (h : a = b) :
    (inferInstance : MeasurableSpace (Π i : Iic a, X i)) ≍
      (inferInstance : MeasurableSpace (Π i : Iic b, X i)) := by cases h; rfl

end castLemmas

section iterateInduction

/-- This function takes as input a tuple `(x_₀, ..., x_ₐ)` and `ind` a function which
given `(y_₀, ...,y_ₙ)` outputs `x_{n+1} : X (n + 1)`, and it builds an element of `Π n, X n`
by starting with `(x_₀, ..., x_ₐ)` and then iterating `ind`. -/
def iterateInduction {a : ℕ} (x : Π i : Iic a, X i)
    (ind : (n : ℕ) → (Π i : Iic n, X i) → X (n + 1)) : Π n, X n
  | 0 => x ⟨0, mem_Iic.2 <| zero_le a⟩
  | k + 1 => if h : k + 1 ≤ a
      then x ⟨k + 1, mem_Iic.2 h⟩
      else ind k (fun i ↦ iterateInduction x ind i)
  decreasing_by exact Nat.lt_succ.2 (mem_Iic.1 i.2)

lemma frestrictLe_iterateInduction {a : ℕ} (x : Π i : Iic a, X i)
    (ind : (n : ℕ) → (Π i : Iic n, X i) → X (n + 1)) :
    frestrictLe a (iterateInduction x ind) = x := by
  ext i
  simp only [frestrictLe_apply]
  obtain ⟨(zero | j), hj⟩ := i <;> rw [iterateInduction]
  rw [dif_pos (mem_Iic.1 hj)]

end iterateInduction

variable [∀ n, MeasurableSpace (X n)]

section ProjectiveFamily

namespace MeasureTheory

/-! ### Projective families indexed by `Finset ℕ` -/

variable {μ : (n : ℕ) → Measure (Π i : Iic n, X i)}

/-- To check that a measure `ν` is the projective limit of a projective family of measures indexed
by `Finset ℕ`, it is enough to check on intervals of the form `Iic n`, where `n` is larger than
a given integer. -/
theorem isProjectiveLimit_nat_iff' {μ : (I : Finset ℕ) → Measure (Π i : I, X i)}
    (hμ : IsProjectiveMeasureFamily μ) (ν : Measure (Π n, X n)) (a : ℕ) :
    IsProjectiveLimit ν μ ↔ ∀ ⦃n⦄, a ≤ n → ν.map (frestrictLe n) = μ (Iic n) := by
  refine ⟨fun h n _ ↦ h (Iic n), fun h I ↦ ?_⟩
  have := (I.subset_Iic_sup_id.trans (Iic_subset_Iic.2 (le_max_left (I.sup id) a)))
  rw [← restrict₂_comp_restrict this, ← Measure.map_map, ← frestrictLe, h (le_max_right _ _), ← hμ]
  all_goals fun_prop

/-- To check that a measure `ν` is the projective limit of a projective family of measures indexed
by `Finset ℕ`, it is enough to check on intervals of the form `Iic n`. -/
theorem isProjectiveLimit_nat_iff {μ : (I : Finset ℕ) → Measure (Π i : I, X i)}
    (hμ : IsProjectiveMeasureFamily μ) (ν : Measure (Π n, X n)) :
    IsProjectiveLimit ν μ ↔ ∀ n, ν.map (frestrictLe n) = μ (Iic n) := by
  rw [isProjectiveLimit_nat_iff' hμ _ 0]
  simp

variable (μ : (n : ℕ) → Measure (Π i : Iic n, X i))

/-- Given a family of measures `μ : (n : ℕ) → Measure (Π i : Iic n, X i)`, we can define a family
of measures indexed by `Finset ℕ` by projecting the measures. -/
noncomputable def inducedFamily (S : Finset ℕ) : Measure ((k : S) → X k) :=
    (μ (S.sup id)).map (restrict₂ S.subset_Iic_sup_id)

instance [∀ n, SFinite (μ n)] (I : Finset ℕ) :
    SFinite (inducedFamily μ I) := by rw [inducedFamily]; infer_instance

instance [∀ n, IsFiniteMeasure (μ n)] (I : Finset ℕ) :
    IsFiniteMeasure (inducedFamily μ I) := by rw [inducedFamily]; infer_instance

instance [∀ n, IsZeroOrProbabilityMeasure (μ n)] (I : Finset ℕ) :
    IsZeroOrProbabilityMeasure (inducedFamily μ I) := by rw [inducedFamily]; infer_instance

instance [∀ n, IsProbabilityMeasure (μ n)] (I : Finset ℕ) :
    IsProbabilityMeasure (inducedFamily μ I) := by
  rw [inducedFamily]
  exact Measure.isProbabilityMeasure_map (measurable_restrict₂ _).aemeasurable

/-- Given a family of measures `μ : (n : ℕ) → Measure (Π i : Iic n, X i)`, the induced family
equals `μ` over the intervals `Iic n`. -/
theorem inducedFamily_Iic (n : ℕ) : inducedFamily μ (Iic n) = μ n := by
  rw [inducedFamily, ← measure_cast (sup_Iic n) μ]
  congr with x i
  rw [restrict₂, cast_pi (by rw [sup_Iic n])]

/-- Given a family of measures `μ : (n : ℕ) → Measure (Π i : Iic n, X i)`, the induced family
will be projective only if `μ` is projective, in the sense that if `a ≤ b`, then projecting
`μ b` gives `μ a`. -/
theorem isProjectiveMeasureFamily_inducedFamily
    (h : ∀ a b : ℕ, ∀ hab : a ≤ b, (μ b).map (frestrictLe₂ hab) = μ a) :
    IsProjectiveMeasureFamily (inducedFamily μ) := by
  intro I J hJI
  have sls : J.sup id ≤ I.sup id := sup_mono hJI
  simp only [inducedFamily]
  rw [Measure.map_map, restrict₂_comp_restrict₂,
    ← restrict₂_comp_restrict₂ J.subset_Iic_sup_id (Iic_subset_Iic.2 sls), ← Measure.map_map,
    ← frestrictLe₂.eq_def sls, h (J.sup id) (I.sup id) sls]
  all_goals fun_prop

end MeasureTheory

end ProjectiveFamily

variable {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))} [∀ n, IsMarkovKernel (κ n)]

namespace ProbabilityTheory.Kernel

section definition

/-! ### Definition and basic properties of `traj` -/

variable (κ)

lemma isProjectiveMeasureFamily_partialTraj {a : ℕ} (x₀ : Π i : Iic a, X i) :
    IsProjectiveMeasureFamily (inducedFamily (fun b ↦ partialTraj κ a b x₀)) :=
  isProjectiveMeasureFamily_inducedFamily _
    (fun _ _ ↦ partialTraj_map_frestrictLe₂_apply (κ := κ) x₀)

/-- Given a family of kernels `κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))`, and the
trajectory up to time `a` we can construct an additive content over cylinders. It corresponds
to composing the kernels, starting at time `a + 1`. -/
noncomputable def trajContent {a : ℕ} (x₀ : Π i : Iic a, X i) :
    AddContent (measurableCylinders X) :=
  projectiveFamilyContent (isProjectiveMeasureFamily_partialTraj κ x₀)

variable {κ}

/-- The `trajContent κ x₀` of a cylinder indexed by first coordinates is given by `partialTraj`. -/
theorem trajContent_cylinder {a b : ℕ} {S : Set (Π i : Iic b, X i)} (mS : MeasurableSet S)
    (x₀ : Π i : Iic a, X i) :
    trajContent κ x₀ (cylinder (Iic b) S) = partialTraj κ a b x₀ S := by
  rw [trajContent, projectiveFamilyContent_cylinder _ mS, inducedFamily_Iic]

/-- The `trajContent` of a cylinder is equal to the integral of its indicator function against
`partialTraj`. -/
theorem trajContent_eq_lmarginalPartialTraj {b : ℕ} {S : Set (Π i : Iic b, X i)}
    (mS : MeasurableSet S) (x₀ : Π n, X n) (a : ℕ) :
    trajContent κ (frestrictLe a x₀) (cylinder (Iic b) S) =
      lmarginalPartialTraj κ a b ((cylinder (Iic b) S).indicator 1) x₀ := by
  rw [trajContent_cylinder mS, ← lintegral_indicator_one mS, lmarginalPartialTraj]
  congr with x
  apply Set.indicator_const_eq_indicator_const
  rw [mem_cylinder]
  congrm (fun i ↦ ?_) ∈ S
  simp [updateFinset, i.2]

lemma trajContent_ne_top {a : ℕ} {x : Π i : Iic a, X i} {s : Set (Π n, X n)} :
    trajContent κ x s ≠ ∞ :=
  projectiveFamilyContent_ne_top (isProjectiveMeasureFamily_partialTraj κ x)

/-- This is an auxiliary result for `trajContent_tendsto_zero`. Consider `f` a sequence of bounded
measurable functions such that `f n` depends only on the first coordinates up to `a n`.
Assume that when integrating `f n` against `partialTraj (k + 1) (a n)`, one gets a non-increasing
sequence of functions which converges to `l`.
Assume then that there exists `ε` and `y : Π i : Iic k, X i` such that
when integrating `f n` against `partialTraj k (a n) y`, you get something at least
`ε` for all `n`. Then there exists `z` such that this remains true when integrating
`f` against `partialTraj (k + 1) (a n) (update y (k + 1) z)`. -/
theorem le_lmarginalPartialTraj_succ {f : ℕ → (Π n, X n) → ℝ≥0∞} {a : ℕ → ℕ}
    (hcte : ∀ n, DependsOn (f n) (Iic (a n))) (mf : ∀ n, Measurable (f n))
    {bound : ℝ≥0∞} (fin_bound : bound ≠ ∞) (le_bound : ∀ n x, f n x ≤ bound) {k : ℕ}
    (anti : ∀ x, Antitone (fun n ↦ lmarginalPartialTraj κ (k + 1) (a n) (f n) x))
    {l : (Π n, X n) → ℝ≥0∞}
    (htendsto : ∀ x, Tendsto (fun n ↦ lmarginalPartialTraj κ (k + 1) (a n) (f n) x) atTop (𝓝 (l x)))
    (ε : ℝ≥0∞) (y : Π i : Iic k, X i)
    (hpos : ∀ x n, ε ≤ lmarginalPartialTraj κ k (a n) (f n) (updateFinset x (Iic k) y)) :
    ∃ z, ∀ x n,
    ε ≤ lmarginalPartialTraj κ (k + 1) (a n) (f n)
      (update (updateFinset x (Iic k) y) (k + 1) z) := by
  have _ n : Nonempty (X n) := by
    induction n using Nat.case_strong_induction_on with
    | hz => exact ⟨y ⟨0, mem_Iic.2 (zero_le _)⟩⟩
    | hi m hm =>
      have : Nonempty (Π i : Iic m, X i) :=
        ⟨fun i ↦ @Classical.ofNonempty _ (hm i.1 (mem_Iic.1 i.2))⟩
      exact ProbabilityMeasure.nonempty ⟨κ m Classical.ofNonempty, inferInstance⟩
  -- `Fₙ` is the integral of `fₙ` from time `k + 1` to `aₙ`.
  let F n : (Π n, X n) → ℝ≥0∞ := lmarginalPartialTraj κ (k + 1) (a n) (f n)
  -- `Fₙ` converges to `l` by hypothesis.
  have tendstoF x : Tendsto (F · x) atTop (𝓝 (l x)) := htendsto x
  -- Integrating `fₙ` between time `k` and `aₙ` is the same as integrating
  -- `Fₙ` between time `k` and time `k + 1`.
  have f_eq x n : lmarginalPartialTraj κ k (a n) (f n) x =
      lmarginalPartialTraj κ k (k + 1) (F n) x := by
    simp_rw [F]
    obtain h | h | h := lt_trichotomy (k + 1) (a n)
    · rw [← lmarginalPartialTraj_self k.le_succ h.le (mf n)]
    · rw [← h, lmarginalPartialTraj_le _ le_rfl (mf n)]
    · rw [lmarginalPartialTraj_le _ _ (mf n), (hcte n).lmarginalPartialTraj_of_le _ (mf n),
        (hcte n).lmarginalPartialTraj_of_le _ (mf n)]
      all_goals cutsat
  -- `F` is also a bounded sequence.
  have F_le n x : F n x ≤ bound := by
    simpa [F, lmarginalPartialTraj] using lintegral_le_const (ae_of_all _ fun z ↦ le_bound _ _)
  -- By dominated convergence, the integral of `fₙ` between time `k` and time `a n` converges
  -- to the integral of `l` between time `k` and time `k + 1`.
  have tendsto_int x : Tendsto (fun n ↦ lmarginalPartialTraj κ k (a n) (f n) x) atTop
      (𝓝 (lmarginalPartialTraj κ k (k + 1) l x)) := by
    simp_rw [f_eq, lmarginalPartialTraj]
    exact tendsto_lintegral_of_dominated_convergence (fun _ ↦ bound)
      (fun n ↦ (measurable_lmarginalPartialTraj _ _ (mf n)).comp measurable_updateFinset)
      (fun n ↦ Eventually.of_forall <| fun y ↦ F_le n _)
      (by simp [fin_bound]) (Eventually.of_forall (fun _ ↦ tendstoF _))
  -- By hypothesis, we have `ε ≤ lmarginalPartialTraj κ k (k + 1) (F n) (updateFinset x _ y)`,
  -- so this is also true for `l`.
  have ε_le_lint x : ε ≤ lmarginalPartialTraj κ k (k + 1) l (updateFinset x _ y) :=
    ge_of_tendsto (tendsto_int _) (by simp [hpos])
  let x_ : Π n, X n := Classical.ofNonempty
  -- We now have that the integral of `l` with respect to a probability measure is greater than `ε`,
  -- therefore there exists `x` such that `ε ≤ l(y, x)`.
  obtain ⟨x, hx⟩ : ∃ x, ε ≤ l (update (updateFinset x_ _ y) (k + 1) x) := by
    have : ∫⁻ x, l (update (updateFinset x_ _ y) (k + 1) x) ∂(κ k y) ≠ ∞ :=
      ne_top_of_le_ne_top fin_bound <| lintegral_le_const <| ae_of_all _
        fun y ↦ le_of_tendsto' (tendstoF _) <| fun _ ↦ F_le _ _
    obtain ⟨x, hx⟩ := exists_lintegral_le this
    refine ⟨x, (ε_le_lint x_).trans ?_⟩
    rwa [lmarginalPartialTraj_succ, frestrictLe_updateFinset]
    exact ENNReal.measurable_of_tendsto (by fun_prop) (tendsto_pi_nhds.2 htendsto)
  refine ⟨x, fun x' n ↦ ?_⟩
  -- As `F` is a non-increasing sequence, we have `ε ≤ Fₙ(y, x)` for any `n`.
  have := le_trans hx ((anti _).le_of_tendsto (tendstoF _) n)
  -- This part below is just to say that this is true for any `x : (i : ι) → X i`,
  -- as `Fₙ` technically depends on all the variables, but really depends only on the first `k + 1`.
  convert this using 1
  refine (hcte n).dependsOn_lmarginalPartialTraj _ (mf n) fun i hi ↦ ?_
  simp only [update, updateFinset, mem_Iic]
  split_ifs with h1 h2 <;> try rfl
  rw [mem_coe, mem_Iic] at hi
  cutsat

/-- This is the key theorem to prove the existence of the `traj`:
the `trajContent` of a decreasing sequence of cylinders with empty intersection
converges to `0`.

This implies the `σ`-additivity of `trajContent`
(see `addContent_iUnion_eq_sum_of_tendsto_zero`),
which allows to extend it to the `σ`-algebra by Carathéodory's theorem. -/
theorem trajContent_tendsto_zero {A : ℕ → Set (Π n, X n)}
    (A_mem : ∀ n, A n ∈ measurableCylinders X) (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅)
    {p : ℕ} (x₀ : Π i : Iic p, X i) :
    Tendsto (fun n ↦ trajContent κ x₀ (A n)) atTop (𝓝 0) := by
  have _ n : Nonempty (X n) := by
    induction n using Nat.case_strong_induction_on with
    | hz => exact ⟨x₀ ⟨0, mem_Iic.2 (zero_le _)⟩⟩
    | hi m hm =>
      have : Nonempty (Π i : Iic m, X i) :=
        ⟨fun i ↦ @Classical.ofNonempty _ (hm i.1 (mem_Iic.1 i.2))⟩
      exact ProbabilityMeasure.nonempty ⟨κ m Classical.ofNonempty, inferInstance⟩
  -- `Aₙ` is a cylinder, it can be written as `cylinder (Iic (a n)) Sₙ`.
  have A_cyl n : ∃ a S, MeasurableSet S ∧ A n = cylinder (Iic a) S := by
    simpa [measurableCylinders_nat] using A_mem n
  choose a S mS A_eq using A_cyl
  -- We write `χₙ` for the indicator function of `Aₙ`.
  let χ n := (A n).indicator (1 : (Π n, X n) → ℝ≥0∞)
  -- `χₙ` is measurable.
  have mχ n : Measurable (χ n) := by
    simp_rw [χ, A_eq]
    exact (measurable_indicator_const_iff 1).2 <| (mS n).cylinder
  -- `χₙ` only depends on the first coordinates.
  have χ_dep n : DependsOn (χ n) (Iic (a n)) := by
    simp_rw [χ, A_eq]
    exact dependsOn_cylinder_indicator_const ..
  -- Therefore its integral against `partialTraj κ k (a n)` is constant.
  have lma_const x y n :
      lmarginalPartialTraj κ p (a n) (χ n) (updateFinset x _ x₀) =
      lmarginalPartialTraj κ p (a n) (χ n) (updateFinset y _ x₀) := by
    refine (χ_dep n).dependsOn_lmarginalPartialTraj p (mχ n) fun i hi ↦ ?_
    rw [mem_coe, mem_Iic] at hi
    simp [updateFinset, hi]
  -- As `(Aₙ)` is non-increasing, so is `(χₙ)`.
  have χ_anti : Antitone χ := fun m n hmn y ↦ by
    apply Set.indicator_le fun a ha ↦ ?_
    simp [χ, A_anti hmn ha]
  -- Integrating `χₙ` further than the last coordinate it depends on does nothing.
  -- This is used to then show that the integral of `χₙ` from time `k` is non-increasing.
  have lma_inv k M n (h : a n ≤ M) :
      lmarginalPartialTraj κ k M (χ n) = lmarginalPartialTraj κ k (a n) (χ n) :=
    (χ_dep n).lmarginalPartialTraj_const_right (mχ n) h le_rfl
  -- the integral of `χₙ` from time `k` is non-increasing.
  have anti_lma k x : Antitone fun n ↦ lmarginalPartialTraj κ k (a n) (χ n) x := by
    intro m n hmn
    simp only
    rw [← lma_inv k ((a n).max (a m)) n (le_max_left _ _),
      ← lma_inv k ((a n).max (a m)) m (le_max_right _ _)]
    exact lmarginalPartialTraj_mono _ _ (χ_anti hmn) _
  -- Therefore it converges to some function `lₖ`.
  have this k x : ∃ l, Tendsto (fun n ↦ lmarginalPartialTraj κ k (a n) (χ n) x) atTop (𝓝 l) := by
    obtain h | h := tendsto_of_antitone (anti_lma k x)
    · rw [OrderBot.atBot_eq] at h
      exact ⟨0, h.mono_right <| pure_le_nhds 0⟩
    · exact h
  choose l hl using this
  -- `lₚ` is constant because it is the limit of constant functions: we call it `ε`.
  have l_const x y : l p (updateFinset x _ x₀) = l p (updateFinset y _ x₀) := by
    have := hl p (updateFinset x _ x₀)
    simp_rw [lma_const x y] at this
    exact tendsto_nhds_unique this (hl p _)
  obtain ⟨ε, hε⟩ : ∃ ε, ∀ x, l p (updateFinset x _ x₀) = ε :=
      ⟨l p (updateFinset Classical.ofNonempty _ x₀), fun x ↦ l_const _ _⟩
  -- As the sequence is decreasing, `ε ≤ ∫ χₙ`.
  have hpos x n : ε ≤ lmarginalPartialTraj κ p (a n) (χ n) (updateFinset x _ x₀) :=
    hε x ▸ ((anti_lma p _).le_of_tendsto (hl p _)) n
  -- Also, the indicators are bounded by `1`.
  have χ_le n x : χ n x ≤ 1 := by
    apply Set.indicator_le
    simp
  -- We have all the conditions to apply `le_lmarginalPartialTraj_succ`.
  -- This allows us to recursively build a sequence `z` with the following property:
  -- for any `k ≥ p` and `n`, integrating `χ n` from time `k` to time `a n`
  -- with the trajectory up to `k` being equal to `z` gives something greater than `ε`.
  choose! ind hind using
    fun k y h ↦ le_lmarginalPartialTraj_succ χ_dep mχ (by simp : (1 : ℝ≥0∞) ≠ ∞)
      χ_le (anti_lma (k + 1)) (hl (k + 1)) ε y h
  let z := iterateInduction x₀ ind
  have main k (hk : p ≤ k) : ∀ x n,
      ε ≤ lmarginalPartialTraj κ k (a n) (χ n) (updateFinset x _ (frestrictLe k z)) := by
    induction k, hk using Nat.le_induction with
    | base => exact fun x n ↦ by simpa [z, frestrictLe_iterateInduction] using hpos x n
    | succ k hn h =>
      intro x n
      convert hind k (fun i ↦ z i.1) h x n
      ext i
      simp only [updateFinset, mem_Iic, frestrictLe_apply, dite_eq_ite, update, z]
      split_ifs with h1 h2 h3 h4 h5
      any_goals cutsat
      cases h2
      rw [iterateInduction, dif_neg (by cutsat)]
  -- We now want to prove that the integral of `χₙ`, which is equal to the `trajContent`
  -- of `Aₙ`, converges to `0`.
  have aux x n :
      trajContent κ x₀ (A n) = lmarginalPartialTraj κ p (a n) (χ n) (updateFinset x _ x₀) := by
    simp_rw [χ, A_eq]
    nth_rw 1 [← frestrictLe_updateFinset x x₀]
    exact trajContent_eq_lmarginalPartialTraj (mS n) ..
  simp_rw [aux z]
  convert hl p _
  rw [hε]
  -- Which means that we want to prove that `ε = 0`. But if `ε > 0`, then for any `n`,
  -- choosing `k > aₙ` we get `ε ≤ χₙ(z₀, ..., z_{aₙ})` and therefore `z ∈ Aₙ`.
  -- This contradicts the fact that `(Aₙ)` has an empty intersection.
  by_contra!
  have mem n : z ∈ A n := by
    have : 0 < χ n z := by
      rw [← lmarginalPartialTraj_le κ (le_max_right p (a n)) (mχ n),
        ← updateFinset_frestrictLe (a := a n) z]
      simpa using lt_of_lt_of_le this.symm.bot_lt (main _ (le_max_left _ _) z n)
    exact Set.mem_of_indicator_ne_zero (ne_of_lt this).symm
  exact (A_inter ▸ Set.mem_iInter.2 mem).elim

variable (κ)

/-- The `trajContent` is sigma-subadditive. -/
theorem isSigmaSubadditive_trajContent {a : ℕ} (x₀ : Π i : Iic a, X i) :
    (trajContent κ x₀).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' ↦ ?_)
  refine addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (trajContent κ x₀) (fun _ _ ↦ trajContent_ne_top) ?_ hf hf_Union hf'
  exact fun s hs anti_s inter_s ↦ trajContent_tendsto_zero hs anti_s inter_s x₀

/-- This function is the kernel given by the Ionescu-Tulcea theorem. It is shown below that it
is measurable and turned into a true kernel in `Kernel.traj`. -/
noncomputable def trajFun (a : ℕ) (x₀ : Π i : Iic a, X i) : Measure (Π n, X n) :=
  (trajContent κ x₀).measure isSetSemiring_measurableCylinders generateFrom_measurableCylinders.ge
    (isSigmaSubadditive_trajContent κ x₀)

theorem isProbabilityMeasure_trajFun (a : ℕ) (x₀ : Π i : Iic a, X i) :
    IsProbabilityMeasure (trajFun κ a x₀) where
  measure_univ := by
    rw [← cylinder_univ (Iic 0), trajFun, AddContent.measure_eq, trajContent_cylinder .univ,
      measure_univ]
    · exact generateFrom_measurableCylinders.symm
    · exact cylinder_mem_measurableCylinders _ _ .univ

theorem isProjectiveLimit_trajFun (a : ℕ) (x₀ : Π i : Iic a, X i) :
    IsProjectiveLimit (trajFun κ a x₀) (inducedFamily (fun n ↦ partialTraj κ a n x₀)) := by
  refine isProjectiveLimit_nat_iff (isProjectiveMeasureFamily_partialTraj κ x₀) _ |>.2 fun n ↦ ?_
  ext s ms
  rw [Measure.map_apply (measurable_frestrictLe n) ms, trajFun, AddContent.measure_eq, trajContent,
    projectiveFamilyContent_congr _ (frestrictLe n ⁻¹' s) rfl ms]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ ms

variable {κ} in
theorem measurable_trajFun (a : ℕ) : Measurable (trajFun κ a) := by
  apply Measure.measurable_of_measurable_coe
  refine MeasurableSpace.induction_on_inter
    (C := fun t ht ↦ Measurable (fun x₀ ↦ trajFun κ a x₀ t))
    (s := measurableCylinders X) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (by simp) (fun t ht ↦ ?cylinder) (fun t mt ht ↦ ?compl)
    (fun f disf mf hf ↦ ?union)
  · obtain ⟨N, S, mS, t_eq⟩ : ∃ N S, MeasurableSet S ∧ t = cylinder (Iic N) S := by
      simpa [measurableCylinders_nat] using ht
    simp_rw [trajFun, AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm _ ht,
      trajContent, projectiveFamilyContent_congr _ t t_eq mS, inducedFamily]
    refine Measure.measurable_measure.1 ?_ _ mS
    exact (Measure.measurable_map _ (measurable_restrict₂ _)).comp (measurable _)
  · have := isProbabilityMeasure_trajFun κ a
    simpa [measure_compl mt (measure_ne_top _ _)] using Measurable.const_sub ht _
  · simpa [measure_iUnion disf mf] using Measurable.ennreal_tsum hf

/-- *Ionescu-Tulcea Theorem* : Given a family of kernels `κ n` taking variables in `Iic n` with
value in `X (n + 1)`, the kernel `traj κ a` takes a variable `x` depending on the
variables `i ≤ a` and associates to it a kernel on trajectories depending on all variables,
where the entries with index `≤ a` are those of `x`, and then one follows iteratively the
kernels `κ a`, then `κ (a + 1)`, and so on.

The fact that such a kernel exists on infinite trajectories is not obvious, and is the content of
the Ionescu-Tulcea theorem. -/
noncomputable def traj (a : ℕ) : Kernel (Π i : Iic a, X i) (Π n, X n) where
  toFun := trajFun κ a
  measurable' := measurable_trajFun a

end definition

section basic

lemma traj_apply (a : ℕ) (x : Π i : Iic a, X i) : traj κ a x = trajFun κ a x := rfl

instance (a : ℕ) : IsMarkovKernel (traj κ a) := ⟨fun _ ↦ isProbabilityMeasure_trajFun ..⟩

lemma traj_map_frestrictLe (a b : ℕ) : (traj κ a).map (frestrictLe b) = partialTraj κ a b := by
  ext x
  rw [map_apply, traj_apply, frestrictLe, isProjectiveLimit_trajFun, inducedFamily_Iic]
  fun_prop

lemma traj_map_frestrictLe_apply (a b : ℕ) (x : Π i : Iic a, X i) :
    (traj κ a x).map (frestrictLe b) = partialTraj κ a b x := by
  rw [← map_apply _ (measurable_frestrictLe b), traj_map_frestrictLe]

lemma traj_map_frestrictLe_of_le {a b : ℕ} (hab : a ≤ b) :
    (traj κ b).map (frestrictLe a) =
      deterministic (frestrictLe₂ hab) (measurable_frestrictLe₂ _) := by
  rw [traj_map_frestrictLe, partialTraj_le]

variable (κ)

/-- To check that `η = traj κ a` it is enough to show that the restriction of `η` to variables `≤ b`
is `partialTraj κ a b` for any `b ≥ n`. -/
theorem eq_traj' {a : ℕ} (n : ℕ) (η : Kernel (Π i : Iic a, X i) (Π n, X n))
    (hη : ∀ b ≥ n, η.map (frestrictLe b) = partialTraj κ a b) : η = traj κ a := by
  ext x : 1
  refine ((isProjectiveLimit_trajFun _ _ _).unique ?_).symm
  rw [isProjectiveLimit_nat_iff' _ _ n]
  · intro k hk
    rw [inducedFamily_Iic, ← map_apply _ (measurable_frestrictLe k), hη k hk]
  · exact isProjectiveMeasureFamily_partialTraj κ x

/-- To check that `η = traj κ a` it is enough to show that the restriction of `η` to variables `≤ b`
is `partialTraj κ a b`. -/
theorem eq_traj {a : ℕ} (η : Kernel (Π i : Iic a, X i) (Π n, X n))
    (hη : ∀ b, η.map (frestrictLe b) = partialTraj κ a b) : η = traj κ a :=
  eq_traj' κ 0 η fun b _ ↦ hη b

variable {κ}

/-- Given the distribution up to tome `a`, `partialTraj κ a b` gives the distribution
of the trajectory up to time `b`, and composing this with `traj κ b` gives the distribution
of the whole trajectory. -/
theorem traj_comp_partialTraj {a b : ℕ} (hab : a ≤ b) :
    (traj κ b) ∘ₖ (partialTraj κ a b) = traj κ a := by
  refine eq_traj _ _ fun n ↦ ?_
  rw [map_comp, traj_map_frestrictLe, partialTraj_comp_partialTraj' _ hab]

/-- This theorem shows that `traj κ n` is, up to an equivalence, the product of
a deterministic kernel with another kernel. This is an intermediate result to compute integrals
with respect to this kernel. -/
theorem traj_eq_prod (a : ℕ) :
    traj κ a = (Kernel.id ×ₖ (traj κ a).map (Set.Ioi a).restrict).map (IicProdIoi a) := by
  refine (eq_traj' _ (a + 1) _ fun b hb ↦ ?_).symm
  rw [← map_comp_right]
  conv_lhs => enter [2]; change (IicProdIoc a b) ∘
    (Prod.map id (fun x i ↦ x ⟨i.1, Set.mem_Ioi.2 (mem_Ioc.1 i.2).1⟩))
  · rw [map_comp_right, ← map_prod_map, ← map_comp_right]
    · conv_lhs => enter [1, 2, 2]; change (Ioc a b).restrict
      rw [← restrict₂_comp_restrict Ioc_subset_Iic_self, ← frestrictLe, map_comp_right,
        traj_map_frestrictLe, map_id, ← partialTraj_eq_prod]
      all_goals fun_prop
    all_goals fun_prop
  all_goals fun_prop

theorem traj_map_updateFinset {n : ℕ} (x : Π i : Iic n, X i) :
    (traj κ n x).map (updateFinset · (Iic n) x) = traj κ n x := by
  nth_rw 2 [traj_eq_prod]
  have : (updateFinset · _ x) = IicProdIoi n ∘ (Prod.mk x) ∘ (Set.Ioi n).restrict := by
    ext; simp [IicProdIoi, updateFinset]
  rw [this, ← Function.comp_assoc, ← Measure.map_map, ← Measure.map_map, map_apply, prod_apply,
    map_apply, id_apply, Measure.dirac_prod]
  all_goals fun_prop

end basic

section integral

/-! ### Integrals and `traj` -/

theorem lintegral_traj₀ {a : ℕ} (x₀ : Π i : Iic a, X i) {f : (Π n, X n) → ℝ≥0∞}
    (mf : AEMeasurable f (traj κ a x₀)) :
    ∫⁻ x, f x ∂traj κ a x₀ = ∫⁻ x, f (updateFinset x (Iic a) x₀) ∂traj κ a x₀ := by
  nth_rw 1 [← traj_map_updateFinset, MeasureTheory.lintegral_map']
  · convert mf
    exact traj_map_updateFinset x₀
  · exact measurable_updateFinset_left.aemeasurable

theorem lintegral_traj {a : ℕ} (x₀ : Π i : Iic a, X i) {f : (Π n, X n) → ℝ≥0∞}
    (mf : Measurable f) :
    ∫⁻ x, f x ∂traj κ a x₀ = ∫⁻ x, f (updateFinset x (Iic a) x₀) ∂traj κ a x₀ :=
  lintegral_traj₀ x₀ mf.aemeasurable

variable {E : Type*} [NormedAddCommGroup E]

theorem integrable_traj {a b : ℕ} (hab : a ≤ b) {f : (Π n, X n) → E}
    (x₀ : Π i : Iic a, X i) (i_f : Integrable f (traj κ a x₀)) :
    ∀ᵐ x ∂traj κ a x₀, Integrable f (traj κ b (frestrictLe b x)) := by
  rw [← traj_comp_partialTraj hab, integrable_comp_iff] at i_f
  · apply ae_of_ae_map (p := fun x ↦ Integrable f (traj κ b x))
    · fun_prop
    · convert i_f.1
      rw [← traj_map_frestrictLe, Kernel.map_apply _ (measurable_frestrictLe _)]
  · exact i_f.aestronglyMeasurable

theorem aestronglyMeasurable_traj {a b : ℕ} (hab : a ≤ b) {f : (Π n, X n) → E}
    {x₀ : Π i : Iic a, X i} (hf : AEStronglyMeasurable f (traj κ a x₀)) :
    ∀ᵐ x ∂partialTraj κ a b x₀, AEStronglyMeasurable f (traj κ b x) := by
  rw [← traj_comp_partialTraj hab] at hf
  exact hf.comp

variable [NormedSpace ℝ E]

/-- When computing `∫ x, f x ∂traj κ n x₀`, because the trajectory up to time `n` is
determined by `x₀` we can replace `x` by `updateFinset x (Iic a) x₀`. -/
theorem integral_traj {a : ℕ} (x₀ : Π i : Iic a, X i) {f : (Π n, X n) → E}
    (mf : AEStronglyMeasurable f (traj κ a x₀)) :
    ∫ x, f x ∂traj κ a x₀ = ∫ x, f (updateFinset x (Iic a) x₀) ∂traj κ a x₀ := by
  nth_rw 1 [← traj_map_updateFinset, integral_map]
  · exact measurable_updateFinset_left.aemeasurable
  · convert mf
    rw [traj_map_updateFinset]

lemma partialTraj_compProd_traj {a b : ℕ} (hab : a ≤ b) (u : Π i : Iic a, X i) :
    (partialTraj κ a b u) ⊗ₘ (traj κ b) = (traj κ a u).map (fun x ↦ (frestrictLe b x, x)) := by
  ext s ms
  rw [Measure.map_apply, Measure.compProd_apply, ← traj_comp_partialTraj hab, comp_apply']
  · congr 1 with x
    rw [← traj_map_updateFinset, Measure.map_apply, Measure.map_apply]
    · congr 1 with y
      simp only [Set.mem_preimage]
      congrm (fun i ↦ ?_, fun i ↦ ?_) ∈ s <;> simp [updateFinset]
    any_goals fun_prop
    all_goals exact ms.preimage (by fun_prop)
  any_goals exact ms.preimage (by fun_prop)
  fun_prop

theorem integral_traj_partialTraj' {a b : ℕ} (hab : a ≤ b) {x₀ : Π i : Iic a, X i}
    {f : (Π i : Iic b, X i) → (Π n : ℕ, X n) → E}
    (hf : Integrable f.uncurry ((partialTraj κ a b x₀) ⊗ₘ (traj κ b))) :
    ∫ x, ∫ y, f x y ∂traj κ b x ∂partialTraj κ a b x₀ =
    ∫ x, f (frestrictLe b x) x ∂traj κ a x₀ := by
  have hf' := hf
  rw [partialTraj_compProd_traj hab] at hf'
  simp_rw [← uncurry_apply_pair f, ← Measure.integral_compProd hf,
    partialTraj_compProd_traj hab, integral_map (by fun_prop) hf'.1]

theorem integral_traj_partialTraj {a b : ℕ} (hab : a ≤ b) {x₀ : Π i : Iic a, X i}
    {f : (Π n : ℕ, X n) → E} (hf : Integrable f (traj κ a x₀)) :
    ∫ x, ∫ y, f y ∂traj κ b x ∂partialTraj κ a b x₀ = ∫ x, f x ∂traj κ a x₀ := by
  apply integral_traj_partialTraj' hab
  rw [← traj_comp_partialTraj hab, comp_apply, ← Measure.snd_compProd] at hf
  exact hf.comp_measurable measurable_snd

theorem setIntegral_traj_partialTraj' {a b : ℕ} (hab : a ≤ b) {u : (Π i : Iic a, X i)}
    {f : (Π i : Iic b, X i) → (Π n : ℕ, X n) → E}
    (hf : Integrable f.uncurry ((partialTraj κ a b u) ⊗ₘ (traj κ b)))
    {A : Set (Π i : Iic b, X i)} (hA : MeasurableSet A) :
    ∫ x in A, ∫ y, f x y ∂traj κ b x ∂partialTraj κ a b u =
      ∫ y in frestrictLe b ⁻¹' A, f (frestrictLe b y) y ∂traj κ a u := by
  rw [← integral_integral_indicator _ _ _ hA, integral_traj_partialTraj' hab]
  · simp_rw [← Set.indicator_comp_right, ← integral_indicator (measurable_frestrictLe b hA)]
    rfl
  convert hf.indicator (hA.prod .univ)
  ext ⟨x, y⟩
  by_cases hx : x ∈ A <;> simp [uncurry_def, hx]

theorem setIntegral_traj_partialTraj {a b : ℕ} (hab : a ≤ b) {x₀ : (Π i : Iic a, X i)}
    {f : (Π n : ℕ, X n) → E} (hf : Integrable f (traj κ a x₀))
    {A : Set (Π i : Iic b, X i)} (hA : MeasurableSet A) :
    ∫ x in A, ∫ y, f y ∂traj κ b x ∂partialTraj κ a b x₀ =
      ∫ y in frestrictLe b ⁻¹' A, f y ∂traj κ a x₀ := by
  refine setIntegral_traj_partialTraj' hab ?_ hA
  rw [← traj_comp_partialTraj hab, comp_apply, ← Measure.snd_compProd] at hf
  exact hf.comp_measurable measurable_snd

variable [CompleteSpace E]

open Filtration

theorem condExp_traj {a b : ℕ} (hab : a ≤ b) {x₀ : Π i : Iic a, X i}
    {f : (Π n, X n) → E} (i_f : Integrable f (traj κ a x₀)) :
    (traj κ a x₀)[f|piLE b] =ᵐ[traj κ a x₀]
      fun x ↦ ∫ y, f y ∂traj κ b (frestrictLe b x) := by
  have i_f' : Integrable (fun x ↦ ∫ y, f y ∂(traj κ b) x)
      (((traj κ a) x₀).map (frestrictLe b)) := by
    rw [← map_apply _ (measurable_frestrictLe _), traj_map_frestrictLe _ _]
    rw [← traj_comp_partialTraj hab] at i_f
    exact i_f.integral_comp
  refine ae_eq_condExp_of_forall_setIntegral_eq (piLE.le _) i_f
    (fun s _ _ ↦ i_f'.comp_aemeasurable (measurable_frestrictLe b).aemeasurable |>.integrableOn)
    ?_ ?_ |>.symm <;> rw [piLE_eq_comap_frestrictLe]
  · rintro - ⟨t, mt, rfl⟩ -
    simp_rw [Function.comp_apply]
    rw [← setIntegral_map mt i_f'.1, ← map_apply, traj_map_frestrictLe,
      setIntegral_traj_partialTraj hab i_f mt]
    all_goals fun_prop
  · exact (i_f'.1.comp_ae_measurable' (measurable_frestrictLe b).aemeasurable)

theorem condExp_traj' {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (x₀ : Π i : Iic a, X i) (f : (Π n, X n) → E) :
    (traj κ a x₀)[f|piLE b] =ᵐ[traj κ a x₀]
      fun x ↦ ∫ y, ((traj κ a x₀)[f|piLE c]) (updateFinset x (Iic c) y)
        ∂partialTraj κ b c (frestrictLe b x) := by
  have i_cf : Integrable ((traj κ a x₀)[f|piLE c]) (traj κ a x₀) :=
    integrable_condExp
  have mcf : StronglyMeasurable ((traj κ a x₀)[f|piLE c]) :=
    stronglyMeasurable_condExp.mono (piLE.le c)
  filter_upwards [piLE.condExp_condExp f hbc, condExp_traj hab i_cf] with x h1 h2
  rw [← h1, h2, ← traj_map_frestrictLe, Kernel.map_apply, integral_map]
  · congr with y
    apply stronglyMeasurable_condExp.dependsOn_of_piLE
    simp only [Set.mem_Iic, updateFinset, mem_Iic, frestrictLe_apply, dite_eq_ite]
    exact fun i hi ↦ (if_pos hi).symm
  any_goals fun_prop
  exact (mcf.comp_measurable measurable_updateFinset).aestronglyMeasurable

end integral

end ProbabilityTheory.Kernel
