/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Jireh Loreaux
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fintype.Order
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Analysis.Normed.Lp.WithLp

/-!
# `L^p` distance on finite products of metric spaces
Given finitely many metric spaces, one can put the max distance on their product, but there is also
a whole family of natural distances, indexed by a parameter `p : ℝ≥0∞`, that also induce
the product topology. We define them in this file. For `0 < p < ∞`, the distance on `Π i, α i`
is given by
$$
d(x, y) = \left(\sum d(x_i, y_i)^p\right)^{1/p}.
$$,
whereas for `p = 0` it is the cardinality of the set ${i | d (x_i, y_i) ≠ 0}$. For `p = ∞` the
distance is the supremum of the distances.

We give instances of this construction for emetric spaces, metric spaces, normed groups and normed
spaces.

To avoid conflicting instances, all these are defined on a copy of the original Π-type, named
`PiLp p α`. The assumption `[Fact (p ∉ Set.Ioo 0 1)]` is required for the metric and normed space
instances.

We ensure that the topology, bornology and uniform structure on `PiLp p α` are (defeq to) the
product topology, product bornology and product uniformity, to be able to use freely continuity
statements for the coordinate functions, for instance.

## Implementation notes

We only deal with the `L^p` distance on a product of finitely many metric spaces, which may be
distinct. A closely related construction is `lp`, the `L^p` norm on a product of (possibly
infinitely many) normed spaces, where the norm is
$$
\left(\sum ‖f (x)‖^p \right)^{1/p}.
$$
However, the topology induced by this construction is not the product topology, and some functions
have infinite `L^p` norm. These subtleties are not present in the case of finitely many metric
spaces, hence it is worth devoting a file to this specific case which is particularly well behaved.

Another related construction is `MeasureTheory.Lp`, the `L^p` norm on the space of functions from
a measure space to a normed space, where the norm is
$$
\left(\int ‖f (x)‖^p dμ\right)^{1/p}.
$$
This has all the same subtleties as `lp`, and the further subtlety that this only
defines a seminorm (as almost everywhere zero functions have zero `L^p` norm).
The construction `PiLp` corresponds to the special case of `MeasureTheory.Lp` in which the basis
is a finite space equipped with the counting measure.

To prove that the topology (and the uniform structure) on a finite product with the `L^p` distance
are the same as those coming from the `L^∞` distance, we could argue that the `L^p` and `L^∞` norms
are equivalent on `ℝ^n` for abstract (norm equivalence) reasons. Instead, we give a more explicit
(easy) proof which provides a comparison between these two norms with explicit constants.

We also set up the theory for `PseudoEMetricSpace` and `PseudoMetricSpace`.
-/

open Real Set Filter RCLike Bornology Uniformity Topology NNReal ENNReal

instance : Fact (∞ ∉ Set.Ioo 0 1) := ⟨by simp⟩
instance : Fact ((0 : ℝ≥0∞) ∉ Set.Ioo 0 1) := ⟨by simp⟩
instance : Fact (2 ∉ Set.Ioo 0 1) := ⟨by simp⟩
instance {p : ℝ≥0∞} [Fact (1 ≤ p)]: Fact (p ∉ Set.Ioo 0 1) := ⟨sorry⟩

noncomputable section

/-- A copy of a Pi type, on which we will put the `L^p` distance. Since the Pi type itself is
already endowed with the `L^∞` distance, we need the type synonym to avoid confusing typeclass
resolution. Also, we let it depend on `p`, to get a whole family of type on which we can put
different distances. -/
abbrev PiLp (p : ℝ≥0∞) {ι : Type*} (α : ι → Type*) : Type _ :=
  WithLp p (∀ i : ι, α i)

/-The following should not be a `FunLike` instance because then the coercion `⇑` would get
unfolded to `FunLike.coe` instead of `WithLp.equiv`. -/
instance (p : ℝ≥0∞) {ι : Type*} (α : ι → Type*) : CoeFun (PiLp p α) (fun _ ↦ (i : ι) → α i) where
  coe := WithLp.equiv p _

instance (p : ℝ≥0∞) {ι : Type*} (α : ι → Type*) [∀ i, Inhabited (α i)] : Inhabited (PiLp p α) :=
  ⟨fun _ => default⟩

@[ext]
protected theorem PiLp.ext {p : ℝ≥0∞} {ι : Type*} {α : ι → Type*} {x y : PiLp p α}
    (h : ∀ i, x i = y i) : x = y := funext h

namespace PiLp

variable (p : ℝ≥0∞) (𝕜 : Type*) {ι : Type*} (α : ι → Type*) (β : ι → Type*)
section
/- Register simplification lemmas for the applications of `PiLp` elements, as the usual lemmas
for Pi types will not trigger. -/
variable {𝕜 p α}
variable [Semiring 𝕜] [∀ i, SeminormedAddCommGroup (β i)]
variable [∀ i, Module 𝕜 (β i)] (c : 𝕜)
variable (x y : PiLp p β) (i : ι)

#adaptation_note /-- https://github.com/leanprover/lean4/pull/4481
the `simpNF` linter incorrectly claims this lemma can't be applied by `simp`.

(It appears to also be unused in Mathlib.) -/
@[simp, nolint simpNF]
theorem zero_apply : (0 : PiLp p β) i = 0 :=
  rfl

@[simp]
theorem add_apply : (x + y) i = x i + y i :=
  rfl

@[simp]
theorem sub_apply : (x - y) i = x i - y i :=
  rfl

@[simp]
theorem smul_apply : (c • x) i = c • x i :=
  rfl

@[simp]
theorem neg_apply : (-x) i = -x i :=
  rfl

variable (p) in
/-- The projection on the `i`-th coordinate of `WithLp p (∀ i, α i)`, as a linear map. -/
@[simps!]
def projₗ (i : ι) : PiLp p β →ₗ[𝕜] β i :=
  (LinearMap.proj i : (∀ i, β i) →ₗ[𝕜] β i) ∘ₗ (WithLp.linearEquiv p 𝕜 (∀ i, β i)).toLinearMap

end

/-! Note that the unapplied versions of these lemmas are deliberately omitted, as they break
the use of the type synonym. -/

@[simp]
theorem _root_.WithLp.equiv_pi_apply (x : PiLp p α) (i : ι) : WithLp.equiv p _ x i = x i :=
  rfl

@[simp]
theorem  _root_.WithLp.equiv_symm_pi_apply (x : ∀ i, α i) (i : ι) :
    (WithLp.equiv p _).symm x i = x i :=
  rfl

section DistNorm

variable [Fintype ι]

/-!
### Definition of `edist`, `dist` and `norm` on `PiLp`

In this section we define the `edist`, `dist` and `norm` functions on `PiLp p α` without assuming
`[Fact (p ∉ Set.Ioo 0 1)]` or metric properties of the spaces `α i`. This allows us to provide the
rewrite lemmas for each of three cases `p = 0`, `p = ∞` and `0 < p.to_real`.
-/


section Edist

variable [∀ i, EDist (β i)]

/-- Endowing the space `PiLp p β` with the `L^p` edistance. We register this instance
separate from `PiLp.pseudo_emetric` since the latter requires the type class hypothesis
`[Fact (p ∉ Set.Ioo 0 1)]` in order to prove the triangle inequality.

Registering this separately allows for a future emetric-like structure on `PiLp p β` for `p < 1`
satisfying a relaxed triangle inequality. The terminology for this varies throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*. -/
instance : EDist (PiLp p β) where
  edist f g :=
    if p = 0 then {i | edist (f i) (g i) ≠ 0}.toFinite.toFinset.card
    else
      if p = ∞ then ⨆ i, edist (f i) (g i) else (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)

variable {β}

theorem edist_eq_card (f g : PiLp 0 β) :
    edist f g = {i | edist (f i) (g i) ≠ 0}.toFinite.toFinset.card :=
  if_pos rfl

theorem edist_eq_sum {p : ℝ≥0∞} (hp : 0 < p.toReal) (f g : PiLp p β) :
    edist f g = (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

theorem edist_eq_iSup (f g : PiLp ∞ β) : edist f g = ⨆ i, edist (f i) (g i) := rfl

end Edist

section EdistProp

variable {β}
variable [∀ i, PseudoEMetricSpace (β i)]

/-- This holds independent of `p` and does not require `[Fact (p ∉ Set.Ioo 0 1)]`.

We keep it separate from `PiLp.pseudo_emetric_space` so it can be used also for `p < 1`. -/
protected theorem edist_self (f : PiLp p β) : edist f f = 0 := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp [edist_eq_card]
  · simp [edist_eq_iSup]
  · simp [edist_eq_sum h, ENNReal.zero_rpow_of_pos h, ENNReal.zero_rpow_of_pos (inv_pos.2 <| h)]

/-- This holds independent of `p` and does not require `[Fact (p ∉ Set.Ioo 0 1)]`

We keep it separate from `PiLp.pseudo_emetric_space` so it can be used also for `p < 1`. -/
protected theorem edist_comm (f g : PiLp p β) : edist f g = edist g f := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp only [edist_eq_card, edist_comm]
  · simp only [edist_eq_iSup, edist_comm]
  · simp only [edist_eq_sum h, edist_comm]

end EdistProp

section Dist

variable [∀ i, Dist (α i)]

/-- Endowing the space `PiLp p β` with the `L^p` distance. We register this instance
separate from `PiLp.pseudo_metric` since the latter requires the type class hypothesis
`[Fact (p ∉ Set.Ioo 0 1)]` in order to prove the triangle inequality.

Registering this separately allows for a future metric-like structure on `PiLp p β` for `p < 1`
satisfying a relaxed triangle inequality. The terminology for this varies throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*. -/
instance : Dist (PiLp p α) where
  dist f g :=
    if p = 0 then {i | dist (f i) (g i) ≠ 0}.toFinite.toFinset.card
    else
      if p = ∞ then ⨆ i, dist (f i) (g i) else (∑ i, dist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)

variable {α}

theorem dist_eq_card (f g : PiLp 0 α) :
    dist f g = {i | dist (f i) (g i) ≠ 0}.toFinite.toFinset.card :=
  if_pos rfl

theorem dist_eq_sum {p : ℝ≥0∞} (hp : 0 < p.toReal) (f g : PiLp p α) :
    dist f g = (∑ i, dist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

theorem dist_eq_iSup (f g : PiLp ∞ α) : dist f g = ⨆ i, dist (f i) (g i) := rfl

end Dist

section Norm

variable [∀ i, Norm (β i)]

/-- Endowing the space `PiLp p β` with the `L^p` norm. We register this instance
separate from `PiLp.seminormedAddCommGroup` since the latter requires the type class hypothesis
`[Fact (p ∉ Set.Ioo 0 1)]` in order to prove the triangle inequality.

Registering this separately allows for a future norm-like structure on `PiLp p β` for `p < 1`
satisfying a relaxed triangle inequality. These are called *quasi-norms*. -/
instance instNorm : Norm (PiLp p β) where
  norm f :=
    if p = 0 then {i | ‖f i‖ ≠ 0}.toFinset.card
    else if p = ∞ then ⨆ i, ‖f i‖ else (∑ i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)

variable {p β}

theorem norm_eq_card (f : PiLp 0 β) : ‖f‖ = {i | ‖f i‖ ≠ 0}.toFinset.card :=
  if_pos rfl

theorem norm_eq_ciSup (f : PiLp ∞ β) : ‖f‖ = ⨆ i, ‖f i‖ := rfl

theorem norm_eq_sum (hp : 0 < p.toReal) (f : PiLp p β) :
    ‖f‖ = (∑ i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

end Norm

end DistNorm

section Aux

/-!
### The uniformity on finite `L^p` products is the product uniformity

In this section, we put the `L^p` edistance on `PiLp p α`, and we check that the uniformity
coming from this edistance coincides with the product uniformity, by showing that the canonical
map to the Pi type (with the `L^∞` distance) is a uniform embedding, as it is both Lipschitz and
antiLipschitz.

We only register this emetric space structure as a temporary instance, as the true instance (to be
registered later) will have as uniformity exactly the product uniformity, instead of the one coming
from the edistance (which is equal to it, but not defeq). See Note [forgetful inheritance]
explaining why having definitionally the right uniformity is often important.
-/


variable [Fact (p ∉ Set.Ioo 0 1)] [∀ i, PseudoMetricSpace (α i)] [∀ i, PseudoEMetricSpace (β i)]
variable [Fintype ι]

/-- A version of `ENNReal.trichotomy` assuming `Fact (p ∉ Set.Ioo 0 1)`. -/
protected theorem _root_.ENNReal.trichotomy' (p : ℝ≥0∞) [Fact (p ∉ Set.Ioo 0 1)] :
    p = 0 ∨ p = ∞ ∨ 1 ≤ p.toReal := by
  obtain rfl | hp := eq_zero_or_pos p
  · left; rfl
  · right
    refine @ENNReal.dichotomy p ⟨?_⟩
    have : p ∉ Set.Ioo 0 1 := Fact.out
    simpa [hp] using this

/-- Endowing the space `PiLp p β` with the `L^p` pseudoemetric structure. This definition is not
satisfactory, as it does not register the fact that the topology and the uniform structure coincide
with the product one. Therefore, we do not register it as an instance. Using this as a temporary
pseudoemetric space instance, we will show that the uniform structure is equal (but not defeq) to
the product one, and then register an instance in which we replace the uniform structure by the
product one using this pseudoemetric space and `PseudoEMetricSpace.replaceUniformity`. -/
def pseudoEmetricAux : PseudoEMetricSpace (PiLp p β) where
  edist_self := PiLp.edist_self p
  edist_comm := PiLp.edist_comm p
  edist_triangle f g h := by
    rcases p.trichotomy' with (rfl | rfl | hp)
    · classical
      simp only [edist_eq_card, Finite.toFinset_setOf, ←Nat.cast_add, Nat.cast_le]
      refine le_trans (Finset.card_mono ?_) (Finset.card_union_le _ _)
      rw [← Finset.filter_or]
      refine Finset.monotone_filter_right _ fun i hi ↦ ?_
      have := hi.ne_or_ne
      rw [←not_and_or]
      rintro ⟨hf, hg⟩
      apply hi
      have hfg := congr($hf + $hg)
      rw [add_zero] at hfg
      have := edist_triangle (f i) (g i) (h i)
      rw [hfg] at this
      exact eq_bot_iff.mpr this
    · simp only [edist_eq_iSup]
      cases isEmpty_or_nonempty ι
      · simp only [ciSup_of_empty, ENNReal.bot_eq_zero, add_zero, nonpos_iff_eq_zero]
      -- Porting note: `le_iSup` needed some help
      refine
        iSup_le fun i => (edist_triangle _ (g i) _).trans <| add_le_add
            (le_iSup (fun k => edist (f k) (g k)) i) (le_iSup (fun k => edist (g k) (h k)) i)
    · simp only [edist_eq_sum (zero_lt_one.trans_le hp)]
      calc
        (∑ i, edist (f i) (h i) ^ p.toReal) ^ (1 / p.toReal) ≤
            (∑ i, (edist (f i) (g i) + edist (g i) (h i)) ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr
          apply edist_triangle
        _ ≤
            (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal) +
              (∑ i, edist (g i) (h i) ^ p.toReal) ^ (1 / p.toReal) :=
          ENNReal.Lp_add_le _ _ _ hp

attribute [local instance] PiLp.pseudoEmetricAux

/-- An auxiliary lemma used twice in the proof of `PiLp.pseudoMetricAux` below. Not intended for
use outside this file. -/
theorem iSup_edist_ne_top_aux {ι : Type*} [Finite ι] {α : ι → Type*}
    [∀ i, PseudoMetricSpace (α i)] (f g : PiLp ∞ α) : (⨆ i, edist (f i) (g i)) ≠ ⊤ := by
  cases nonempty_fintype ι
  obtain ⟨M, hM⟩ := Finite.exists_le fun i => (⟨dist (f i) (g i), dist_nonneg⟩ : ℝ≥0)
  refine ne_of_lt ((iSup_le fun i => ?_).trans_lt (@ENNReal.coe_lt_top M))
  simp only [edist, PseudoMetricSpace.edist_dist, ENNReal.ofReal_eq_coe_nnreal dist_nonneg]
  exact mod_cast hM i

/-- Endowing the space `PiLp p α` with the `L^p` pseudometric structure. This definition is not
satisfactory, as it does not register the fact that the topology, the uniform structure, and the
bornology coincide with the product ones. Therefore, we do not register it as an instance. Using
this as a temporary pseudoemetric space instance, we will show that the uniform structure is equal
(but not defeq) to the product one, and then register an instance in which we replace the uniform
structure and the bornology by the product ones using this pseudometric space,
`PseudoMetricSpace.replaceUniformity`, and `PseudoMetricSpace.replaceBornology`.

See note [reducible non-instances] -/
abbrev pseudoMetricAux : PseudoMetricSpace (PiLp p α) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
    (fun f g => by
      rcases p.trichotomy' with (rfl | rfl | h)
      · simp only [edist_eq_card, Finite.toFinset_setOf]
        exact natCast_ne_top _
      · exact iSup_edist_ne_top_aux f g
      · rw [edist_eq_sum (zero_lt_one.trans_le h)]
        exact ENNReal.rpow_ne_top_of_nonneg (by positivity) <| ENNReal.sum_ne_top.2 fun _ _ ↦
          ENNReal.rpow_ne_top_of_nonneg (by positivity) (edist_ne_top _ _))
    fun f g => by
    rcases p.trichotomy' with (rfl | rfl | h)
    · simp_rw [edist_eq_card, dist_eq_card, Finite.toFinset_setOf, toReal_nat, edist_nndist,
        ←coe_nndist, ENNReal.coe_ne_zero, NNReal.coe_ne_zero]
    · rw [edist_eq_iSup, dist_eq_iSup]
      cases isEmpty_or_nonempty ι
      · simp only [Real.iSup_of_isEmpty, ciSup_of_empty, ENNReal.bot_eq_zero, ENNReal.zero_toReal]
      · refine le_antisymm (ciSup_le fun i => ?_) ?_
        · rw [← ENNReal.ofReal_le_iff_le_toReal (iSup_edist_ne_top_aux f g), ←
            PseudoMetricSpace.edist_dist]
          -- Porting note: `le_iSup` needed some help
          exact le_iSup (fun k => edist (f k) (g k)) i
        · refine ENNReal.toReal_le_of_le_ofReal (Real.sSup_nonneg ?_) (iSup_le fun i => ?_)
          · rintro - ⟨i, rfl⟩
            exact dist_nonneg
          · change PseudoMetricSpace.edist _ _ ≤ _
            rw [PseudoMetricSpace.edist_dist]
            -- Porting note: `le_ciSup` needed some help
            exact ENNReal.ofReal_le_ofReal
              (le_ciSup (Finite.bddAbove_range (fun k => dist (f k) (g k))) i)
    · have A : ∀ i, edist (f i) (g i) ^ p.toReal ≠ ⊤ := fun i =>
        ENNReal.rpow_ne_top_of_nonneg (zero_le_one.trans h) (edist_ne_top _ _)
      simp only [edist_eq_sum (zero_lt_one.trans_le h), dist_edist, ENNReal.toReal_rpow,
        dist_eq_sum (zero_lt_one.trans_le h), ← ENNReal.toReal_sum fun i _ => A i]

attribute [local instance] PiLp.pseudoMetricAux

theorem lipschitzWith_equiv_aux (hp : p ≠ 0) : LipschitzWith 1 (WithLp.equiv p (∀ i, β i)) := by
  intro x y
  simp_rw [ENNReal.coe_one, one_mul, edist_pi_def, Finset.sup_le_iff, Finset.mem_univ,
    forall_true_left, WithLp.equiv_pi_apply]
  rcases p.trichotomy' with (rfl | rfl | h)
  · exact (hp rfl).elim
  · simpa only [edist_eq_iSup] using le_iSup fun i => edist (x i) (y i)
  · have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (zero_lt_one.trans_le h).ne'
    rw [edist_eq_sum (zero_lt_one.trans_le h)]
    intro i
    calc
      edist (x i) (y i) = (edist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) := by
        simp [← ENNReal.rpow_mul, cancel, -one_div]
      _ ≤ (∑ i, edist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) := by
        gcongr
        exact Finset.single_le_sum (fun i _ => (bot_le : (0 : ℝ≥0∞) ≤ _)) (Finset.mem_univ i)

theorem antilipschitzWith_equiv_aux (hp : p ≠ 0) :
    AntilipschitzWith ((Fintype.card ι : ℝ≥0) ^ (1 / p).toReal) (WithLp.equiv p (∀ i, β i)) := by
  intro x y
  rcases p.trichotomy' with (rfl | rfl | h)
  · exact (hp rfl).elim
  · simp only [edist_eq_iSup, ENNReal.div_top, ENNReal.zero_toReal, NNReal.rpow_zero,
      ENNReal.coe_one, one_mul, iSup_le_iff]
    -- Porting note: `Finset.le_sup` needed some help
    exact fun i => Finset.le_sup (f := fun i => edist (x i) (y i)) (Finset.mem_univ i)
  · have pos : 0 < p.toReal := zero_lt_one.trans_le h
    have nonneg : 0 ≤ 1 / p.toReal := one_div_nonneg.2 (le_of_lt pos)
    have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (ne_of_gt pos)
    rw [edist_eq_sum pos, ENNReal.toReal_div 1 p]
    simp only [edist, ← one_div, ENNReal.one_toReal]
    calc
      (∑ i, edist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) ≤
          (∑ _i, edist (WithLp.equiv p _ x) (WithLp.equiv p _ y) ^ p.toReal) ^ (1 / p.toReal) := by
        gcongr with i
        exact Finset.le_sup (f := fun i => edist (x i) (y i)) (Finset.mem_univ i)
      _ =
          ((Fintype.card ι : ℝ≥0) ^ (1 / p.toReal) : ℝ≥0) *
            edist (WithLp.equiv p _ x) (WithLp.equiv p _ y) := by
        simp only [nsmul_eq_mul, Finset.card_univ, ENNReal.rpow_one, Finset.sum_const,
          ENNReal.mul_rpow_of_nonneg _ _ nonneg, ← ENNReal.rpow_mul, cancel]
        have : (Fintype.card ι : ℝ≥0∞) = (Fintype.card ι : ℝ≥0) :=
          (ENNReal.coe_natCast (Fintype.card ι)).symm
        rw [this, ENNReal.coe_rpow_of_nonneg _ nonneg]

theorem aux_uniformity_eq : 𝓤 (PiLp p β) = 𝓤[Pi.uniformSpace _] := by
  have A : IsUniformInducing (WithLp.equiv p (∀ i, β i)) := by
    obtain rfl | hp := eq_or_ne p 0
    · sorry
    · exact (antilipschitzWith_equiv_aux p β hp).isUniformInducing
        (lipschitzWith_equiv_aux p β hp).uniformContinuous
  have : (fun x : PiLp p β × PiLp p β => (WithLp.equiv p _ x.fst, WithLp.equiv p _ x.snd)) = id :=
    by ext i <;> rfl
  rw [← A.comap_uniformity, this, comap_id]

theorem aux_cobounded_eq : cobounded (PiLp p α) = @cobounded _ Pi.instBornology := by
  obtain rfl | hp := eq_or_ne p 0
  · sorry
  · calc
      cobounded (PiLp p α) = comap (WithLp.equiv p (∀ i, α i)) (cobounded _) :=
        le_antisymm (antilipschitzWith_equiv_aux p α hp).tendsto_cobounded.le_comap
          (lipschitzWith_equiv_aux p α hp).comap_cobounded_le
      _ = _ := comap_id

end Aux

/-! ### Instances on finite `L^p` products -/


instance uniformSpace [∀ i, UniformSpace (β i)] : UniformSpace (PiLp p β) :=
  Pi.uniformSpace _

theorem uniformContinuous_equiv [∀ i, UniformSpace (β i)] :
    UniformContinuous (WithLp.equiv p (∀ i, β i)) :=
  uniformContinuous_id

theorem uniformContinuous_equiv_symm [∀ i, UniformSpace (β i)] :
    UniformContinuous (WithLp.equiv p (∀ i, β i)).symm :=
  uniformContinuous_id

@[continuity]
theorem continuous_equiv [∀ i, UniformSpace (β i)] : Continuous (WithLp.equiv p (∀ i, β i)) :=
  continuous_id

@[continuity]
theorem continuous_equiv_symm [∀ i, UniformSpace (β i)] :
    Continuous (WithLp.equiv p (∀ i, β i)).symm :=
  continuous_id

instance bornology [∀ i, Bornology (β i)] : Bornology (PiLp p β) :=
  Pi.instBornology

-- throughout the rest of the file, we assume `1 ≤ p`
variable [Fact (p ∉ Set.Ioo 0 1)]
section Fintype
variable [Fintype ι]

/-- pseudoemetric space instance on the product of finitely many pseudoemetric spaces, using the
`L^p` pseudoedistance, and having as uniformity the product uniformity. -/
instance [∀ i, PseudoEMetricSpace (β i)] : PseudoEMetricSpace (PiLp p β) :=
  (pseudoEmetricAux p β).replaceUniformity (aux_uniformity_eq p β).symm

/-- emetric space instance on the product of finitely many emetric spaces, using the `L^p`
edistance, and having as uniformity the product uniformity. -/
instance [∀ i, EMetricSpace (α i)] : EMetricSpace (PiLp p α) :=
  @EMetricSpace.ofT0PseudoEMetricSpace (PiLp p α) _ Pi.instT0Space

/-- pseudometric space instance on the product of finitely many pseudometric spaces, using the
`L^p` distance, and having as uniformity the product uniformity. -/
instance [∀ i, PseudoMetricSpace (β i)] : PseudoMetricSpace (PiLp p β) :=
  ((pseudoMetricAux p β).replaceUniformity (aux_uniformity_eq p β).symm).replaceBornology fun s =>
    Filter.ext_iff.1 (aux_cobounded_eq p β).symm sᶜ

/-- metric space instance on the product of finitely many metric spaces, using the `L^p` distance,
and having as uniformity the product uniformity. -/
instance [∀ i, MetricSpace (α i)] : MetricSpace (PiLp p α) :=
  MetricSpace.ofT0PseudoMetricSpace _

variable {p} in
theorem toReal_pos_of_ne_top_of_fact (h : p ≠ ⊤) :
    0 < p.toReal :=
  sorry
theorem nndist_eq_sum {β : ι → Type*} [∀ i, PseudoMetricSpace (β i)]
    (hp : p ≠ ∞) (x y : PiLp p β) :
    nndist x y = (∑ i : ι, nndist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) :=
  -- Porting note: was `Subtype.ext`
  NNReal.eq <| by
    push_cast
    exact dist_eq_sum (toReal_pos_of_ne_top_of_fact hp) _ _


theorem nndist_eq_iSup {β : ι → Type*} [∀ i, PseudoMetricSpace (β i)] (x y : PiLp ∞ β) :
    nndist x y = ⨆ i, nndist (x i) (y i) :=
  -- Porting note: was `Subtype.ext`
  NNReal.eq <| by
    push_cast
    exact dist_eq_iSup _ _

theorem lipschitzWith_equiv [∀ i, PseudoEMetricSpace (β i)] (hp : p ≠ 0) :
    LipschitzWith 1 (WithLp.equiv p (∀ i, β i)) :=
  lipschitzWith_equiv_aux p β hp

theorem antilipschitzWith_equiv [∀ i, PseudoEMetricSpace (β i)] (hp : p ≠ 0) :
    AntilipschitzWith ((Fintype.card ι : ℝ≥0) ^ (1 / p).toReal) (WithLp.equiv p (∀ i, β i)) :=
  antilipschitzWith_equiv_aux p β hp

theorem infty_equiv_isometry [∀ i, PseudoEMetricSpace (β i)] :
    Isometry (WithLp.equiv ∞ (∀ i, β i)) :=
  fun x y =>
  le_antisymm (by simpa only [ENNReal.coe_one, one_mul] using lipschitzWith_equiv ∞ β (by simp) x y)
    (by
      simpa only [ENNReal.div_top, ENNReal.zero_toReal, NNReal.rpow_zero, ENNReal.coe_one,
        one_mul] using antilipschitzWith_equiv ∞ β (by simp) x y)

/-- seminormed group instance on the product of finitely many normed groups, using the `L^p`
norm. -/
instance seminormedAddCommGroup [∀ i, SeminormedAddCommGroup (β i)] :
    SeminormedAddCommGroup (PiLp p β) :=
  { Pi.addCommGroup with
    dist_eq := fun x y => by
      rcases p.trichotomy with (rfl | rfl | h)
      · simp [dist_eq_card, norm_eq_card, dist_eq_norm]
      · simp only [dist_eq_iSup, norm_eq_ciSup, dist_eq_norm, sub_apply]
      · have : p ≠ ∞ := by
          intro hp
          rw [hp, ENNReal.top_toReal] at h
          linarith
        simp only [dist_eq_sum h, norm_eq_sum h, dist_eq_norm, sub_apply] }

/-- normed group instance on the product of finitely many normed groups, using the `L^p` norm. -/
instance normedAddCommGroup [∀ i, NormedAddCommGroup (α i)] : NormedAddCommGroup (PiLp p α) :=
  { PiLp.seminormedAddCommGroup p α with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }


theorem nnnorm_eq_card [∀ i, SeminormedAddCommGroup (β i)] (f : PiLp 0 β) :
    ‖f‖₊ = {i | ‖f i‖₊ ≠ 0}.toFinset.card := by
  ext
  simp [norm_eq_card, ← NNReal.coe_inj]

theorem nnnorm_eq_sum {p : ℝ≥0∞} [Fact (p ∉ Set.Ioo 0 1)] {β : ι → Type*} (hp : p ≠ ∞)
    [∀ i, SeminormedAddCommGroup (β i)] (f : PiLp p β) :
    ‖f‖₊ = (∑ i, ‖f i‖₊ ^ p.toReal) ^ (1 / p.toReal) := by
  ext
  simp [NNReal.coe_sum, norm_eq_sum (p.toReal_pos_iff_ne_top.mpr hp)]

section Linfty
variable {β}
variable [∀ i, SeminormedAddCommGroup (β i)]

theorem nnnorm_eq_ciSup (f : PiLp ∞ β) : ‖f‖₊ = ⨆ i, ‖f i‖₊ := by
  ext
  simp [NNReal.coe_iSup, norm_eq_ciSup]

@[simp] theorem nnnorm_equiv (f : PiLp ∞ β) : ‖WithLp.equiv ⊤ _ f‖₊ = ‖f‖₊ := by
  rw [nnnorm_eq_ciSup, Pi.nnnorm_def, Finset.sup_univ_eq_ciSup]
  dsimp only [WithLp.equiv_pi_apply]

@[simp] theorem nnnorm_equiv_symm (f : ∀ i, β i) : ‖(WithLp.equiv ⊤ _).symm f‖₊ = ‖f‖₊ :=
  (nnnorm_equiv _).symm

@[simp] theorem norm_equiv (f : PiLp ∞ β) : ‖WithLp.equiv ⊤ _ f‖ = ‖f‖ :=
  congr_arg NNReal.toReal <| nnnorm_equiv f

@[simp] theorem norm_equiv_symm (f : ∀ i, β i) : ‖(WithLp.equiv ⊤ _).symm f‖ = ‖f‖ :=
  (norm_equiv _).symm

end Linfty

theorem norm_eq_of_nat {p : ℝ≥0∞} [Fact (p ∉ Set.Ioo 0 1)] {β : ι → Type*}
    [∀ i, SeminormedAddCommGroup (β i)] (n : ℕ) (h : p = n) (f : PiLp p β) :
    ‖f‖ = (∑ i, ‖f i‖ ^ n) ^ (1 / (n : ℝ)) := by
  have := p.toReal_pos_iff_ne_top.mpr (ne_of_eq_of_ne h <| ENNReal.natCast_ne_top n)
  simp only [one_div, h, Real.rpow_natCast, ENNReal.toReal_natCast, eq_self_iff_true,
    Finset.sum_congr, norm_eq_sum this]

section L1
variable {β} [∀ i, SeminormedAddCommGroup (β i)]

theorem norm_eq_of_L1 (x : PiLp 1 β) : ‖x‖ = ∑ i : ι, ‖x i‖ := by
  simp [norm_eq_sum]

theorem nnnorm_eq_of_L1 (x : PiLp 1 β) : ‖x‖₊ = ∑ i : ι, ‖x i‖₊ :=
  NNReal.eq <| by push_cast; exact norm_eq_of_L1 x

theorem dist_eq_of_L1 (x y : PiLp 1 β) : dist x y = ∑ i, dist (x i) (y i) := by
  simp_rw [dist_eq_norm, norm_eq_of_L1, sub_apply]

theorem nndist_eq_of_L1 (x y : PiLp 1 β) : nndist x y = ∑ i, nndist (x i) (y i) :=
  NNReal.eq <| by push_cast; exact dist_eq_of_L1 _ _

theorem edist_eq_of_L1 (x y : PiLp 1 β) : edist x y = ∑ i, edist (x i) (y i) := by
  simp [PiLp.edist_eq_sum]

end L1

section L2
variable {β} [∀ i, SeminormedAddCommGroup (β i)]

theorem norm_eq_of_L2 (x : PiLp 2 β) :
    ‖x‖ = √(∑ i : ι, ‖x i‖ ^ 2) := by
  rw [norm_eq_of_nat 2 (by norm_cast) _]
  rw [Real.sqrt_eq_rpow]
  norm_cast

theorem nnnorm_eq_of_L2 (x : PiLp 2 β) :
    ‖x‖₊ = NNReal.sqrt (∑ i : ι, ‖x i‖₊ ^ 2) :=
  NNReal.eq <| by
    push_cast
    exact norm_eq_of_L2 x

theorem norm_sq_eq_of_L2 (β : ι → Type*) [∀ i, SeminormedAddCommGroup (β i)] (x : PiLp 2 β) :
    ‖x‖ ^ 2 = ∑ i : ι, ‖x i‖ ^ 2 := by
  suffices ‖x‖₊ ^ 2 = ∑ i : ι, ‖x i‖₊ ^ 2 by
    simpa only [NNReal.coe_sum] using congr_arg ((↑) : ℝ≥0 → ℝ) this
  rw [nnnorm_eq_of_L2, NNReal.sq_sqrt]

theorem dist_eq_of_L2 (x y : PiLp 2 β) :
    dist x y = √(∑ i, dist (x i) (y i) ^ 2) := by
  simp_rw [dist_eq_norm, norm_eq_of_L2, sub_apply]

theorem nndist_eq_of_L2 (x y : PiLp 2 β) :
    nndist x y = NNReal.sqrt (∑ i, nndist (x i) (y i) ^ 2) :=
  NNReal.eq <| by
    push_cast
    exact dist_eq_of_L2 _ _

theorem edist_eq_of_L2 (x y : PiLp 2 β) :
    edist x y = (∑ i, edist (x i) (y i) ^ 2) ^ (1 / 2 : ℝ) := by simp [PiLp.edist_eq_sum]

end L2

instance instBoundedSMul [SeminormedRing 𝕜] [∀ i, SeminormedAddCommGroup (β i)]
    [∀ i, Module 𝕜 (β i)] [∀ i, BoundedSMul 𝕜 (β i)] :
    BoundedSMul 𝕜 (PiLp p β) :=
  .of_nnnorm_smul_le fun c f => by
    rcases p.trichotomy with (rfl | rfl | hp)
    · sorry
    · rw [← nnnorm_equiv, ← nnnorm_equiv, WithLp.equiv_smul]
      exact nnnorm_smul_le c (WithLp.equiv ∞ (∀ i, β i) f)
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p ≠ ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [nnnorm_eq_sum hpt, nnnorm_eq_sum hpt, one_div, NNReal.rpow_inv_le_iff hp0,
        NNReal.mul_rpow, ← NNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', NNReal.rpow_one,
        Finset.mul_sum]
      simp_rw [← NNReal.mul_rpow, smul_apply]
      exact Finset.sum_le_sum fun i _ => NNReal.rpow_le_rpow (nnnorm_smul_le _ _) hp0.le

/-- The product of finitely many normed spaces is a normed space, with the `L^p` norm. -/
instance normedSpace [NormedField 𝕜] [∀ i, SeminormedAddCommGroup (β i)]
    [∀ i, NormedSpace 𝕜 (β i)] : NormedSpace 𝕜 (PiLp p β) where
  norm_smul_le := norm_smul_le

variable {𝕜 p α}
variable [Semiring 𝕜] [∀ i, SeminormedAddCommGroup (α i)] [∀ i, SeminormedAddCommGroup (β i)]
variable [∀ i, Module 𝕜 (α i)] [∀ i, Module 𝕜 (β i)] (c : 𝕜)

/-- The canonical map `WithLp.equiv` between `PiLp ∞ β` and `Π i, β i` as a linear isometric
equivalence. -/
def equivₗᵢ : PiLp ∞ β ≃ₗᵢ[𝕜] ∀ i, β i :=
  { WithLp.equiv ∞ (∀ i, β i) with
    map_add' := fun _f _g => rfl
    map_smul' := fun _c _f => rfl
    norm_map' := norm_equiv }

section piLpCongrLeft
variable {ι' : Type*}
variable [Fintype ι']
variable (p 𝕜)
variable (E : Type*) [SeminormedAddCommGroup E] [Module 𝕜 E]

/-- An equivalence of finite domains induces a linearly isometric equivalence of finitely supported
functions -/
def _root_.LinearIsometryEquiv.piLpCongrLeft (e : ι ≃ ι') :
    (PiLp p fun _ : ι => E) ≃ₗᵢ[𝕜] PiLp p fun _ : ι' => E where
  toLinearEquiv :=
    WithLp.linearEquiv p _ _ ≪≫ₗ
    LinearEquiv.piCongrLeft' 𝕜 (fun _ : ι => E) e ≪≫ₗ
    (WithLp.linearEquiv p _ _).symm
  norm_map' x' := by
    rcases p.trichotomy' with (rfl | rfl | h)
    · simp_rw [norm_eq_card, toFinset_setOf]
      dsimp
      rw [← Finset.univ_map_equiv_to_embedding e, Finset.filter_map]
      simp_rw [Function.comp_def, Equiv.toEmbedding_apply, Finset.card_map]
      congr!
      rw [e.symm_apply_apply]
    · simp_rw [norm_eq_ciSup]
      exact e.symm.iSup_congr fun _ => rfl
    · simp only [norm_eq_sum (zero_lt_one.trans_le h)]
      congr 1
      exact Fintype.sum_equiv e.symm _ _ fun _ => rfl

variable {p 𝕜 E}

@[simp]
theorem _root_.LinearIsometryEquiv.piLpCongrLeft_apply (e : ι ≃ ι') (v : PiLp p fun _ : ι => E) :
    LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e v = Equiv.piCongrLeft' (fun _ : ι => E) e v :=
  rfl

@[simp]
theorem _root_.LinearIsometryEquiv.piLpCongrLeft_symm (e : ι ≃ ι') :
    (LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e).symm =
      LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e.symm :=
  LinearIsometryEquiv.ext fun z ↦ -- Porting note: was `rfl`
    congr_arg (Equiv.toFun · z) (Equiv.piCongrLeft'_symm _ _)

@[simp high]
theorem _root_.LinearIsometryEquiv.piLpCongrLeft_single [DecidableEq ι] [DecidableEq ι']
    (e : ι ≃ ι') (i : ι) (v : E) :
    LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e ((WithLp.equiv p (_ → E)).symm <| Pi.single i v) =
      (WithLp.equiv p (_ → E)).symm (Pi.single (e i) v) := by
  funext x
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, LinearEquiv.piCongrLeft', Equiv.piCongrLeft',
    Pi.single, Function.update, Equiv.symm_apply_eq]

end piLpCongrLeft

section piLpCongrRight
variable {β}

variable (p) in
/-- A family of linearly isometric equivalences in the codomain induces an isometric equivalence
between Pi types with the Lp norm.

This is the isometry version of `LinearEquiv.piCongrRight`. -/
protected def _root_.LinearIsometryEquiv.piLpCongrRight (e : ∀ i, α i ≃ₗᵢ[𝕜] β i) :
    PiLp p α ≃ₗᵢ[𝕜] PiLp p β where
  toLinearEquiv :=
    WithLp.linearEquiv _ _ _
      ≪≫ₗ (LinearEquiv.piCongrRight fun i => (e i).toLinearEquiv)
      ≪≫ₗ (WithLp.linearEquiv _ _ _).symm
  norm_map' := (WithLp.linearEquiv p 𝕜 _).symm.surjective.forall.2 fun x => by
    simp only [LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply,
      Equiv.apply_symm_apply, WithLp.linearEquiv_symm_apply, WithLp.linearEquiv_apply]
    obtain rfl | rfl | hp := p.trichotomy'
    · simp [norm_eq_card]
    · simp_rw [PiLp.norm_equiv_symm, Pi.norm_def, LinearEquiv.piCongrRight_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.nnnorm_map]
    · have : 0 < p.toReal := zero_lt_one.trans_le <| by norm_cast
      simp only [PiLp.norm_eq_sum this, WithLp.equiv_symm_pi_apply, LinearEquiv.piCongrRight_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.norm_map]

@[simp]
theorem _root_.LinearIsometryEquiv.piLpCongrRight_apply (e : ∀ i, α i ≃ₗᵢ[𝕜] β i) (x : PiLp p α) :
    LinearIsometryEquiv.piLpCongrRight p e x =
      (WithLp.equiv p _).symm (fun i => e i (x i)) :=
  rfl

@[simp]
theorem _root_.LinearIsometryEquiv.piLpCongrRight_refl :
    LinearIsometryEquiv.piLpCongrRight p (fun i => .refl 𝕜 (α i)) = .refl _ _ :=
  rfl

@[simp]
theorem _root_.LinearIsometryEquiv.piLpCongrRight_symm (e : ∀ i, α i ≃ₗᵢ[𝕜] β i) :
    (LinearIsometryEquiv.piLpCongrRight p e).symm =
      LinearIsometryEquiv.piLpCongrRight p (fun i => (e i).symm) :=
  rfl

@[simp high]
theorem _root_.LinearIsometryEquiv.piLpCongrRight_single (e : ∀ i, α i ≃ₗᵢ[𝕜] β i) [DecidableEq ι]
    (i : ι) (v : α i) :
    LinearIsometryEquiv.piLpCongrRight p e ((WithLp.equiv p (∀ i, α i)).symm <| Pi.single i v) =
      (WithLp.equiv p (∀ i, β i)).symm (Pi.single i (e _ v)) :=
  funext <| Pi.apply_single (e ·) (fun _ => map_zero _) _ _

end piLpCongrRight

section piLpCurry

variable {ι : Type*} {κ : ι → Type*} (p : ℝ≥0∞) [Fact (1 ≤ p)]
  [Fintype ι] [∀ i, Fintype (κ i)]
  (α : ∀ i, κ i → Type*) [∀ i k, SeminormedAddCommGroup (α i k)] [∀ i k, Module 𝕜 (α i k)]

variable (𝕜) in
/-- `LinearEquiv.piCurry` for `PiLp`, as an isometry. -/
def _root_.LinearIsometryEquiv.piLpCurry :
    PiLp p (fun i : Sigma _ => α i.1 i.2) ≃ₗᵢ[𝕜] PiLp p (fun i => PiLp p (α i)) where
  toLinearEquiv :=
    WithLp.linearEquiv _ _ _
      ≪≫ₗ LinearEquiv.piCurry 𝕜 α
      ≪≫ₗ (LinearEquiv.piCongrRight fun _ => (WithLp.linearEquiv _ _ _).symm)
      ≪≫ₗ (WithLp.linearEquiv _ _ _).symm
  norm_map' := (WithLp.equiv p _).symm.surjective.forall.2 fun x => by
    simp_rw [← coe_nnnorm, NNReal.coe_inj]
    obtain rfl | hp := eq_or_ne p ⊤
    · simp_rw [← PiLp.nnnorm_equiv, Pi.nnnorm_def, ← PiLp.nnnorm_equiv, Pi.nnnorm_def]
      dsimp [Sigma.curry]
      rw [← Finset.univ_sigma_univ, Finset.sup_sigma]
    · have : 0 < p.toReal := (toReal_pos_iff_ne_top _).mpr hp
      simp_rw [PiLp.nnnorm_eq_sum hp, WithLp.equiv_symm_pi_apply]
      dsimp [Sigma.curry]
      simp_rw [one_div, NNReal.rpow_inv_rpow this.ne', ← Finset.univ_sigma_univ, Finset.sum_sigma]

@[simp] theorem _root_.LinearIsometryEquiv.piLpCurry_apply
    (f : PiLp p (fun i : Sigma κ => α i.1 i.2)) :
    _root_.LinearIsometryEquiv.piLpCurry 𝕜 p α f =
      (WithLp.equiv p _).symm (fun i => (WithLp.equiv p _).symm <|
        Sigma.curry (WithLp.equiv _ _ f) i) :=
  rfl

@[simp] theorem _root_.LinearIsometryEquiv.piLpCurry_symm_apply
    (f : PiLp p (fun i => PiLp p (α i))) :
    (_root_.LinearIsometryEquiv.piLpCurry 𝕜 p α).symm f =
      (WithLp.equiv p _).symm (Sigma.uncurry fun i j => f i j) :=
  rfl

end piLpCurry

section Single

variable (p)
variable [DecidableEq ι]

-- Porting note: added `hp`
@[simp]
theorem nnnorm_equiv_symm_single (i : ι) (b : β i) :
    ‖(WithLp.equiv p (∀ i, β i)).symm (Pi.single i b)‖₊ = ‖b‖₊ := by
  haveI : Nonempty ι := ⟨i⟩
  induction p generalizing hp with
  | top =>
    simp_rw [nnnorm_eq_ciSup, WithLp.equiv_symm_pi_apply]
    refine
      ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun j => ?_) fun n hn => ⟨i, hn.trans_eq ?_⟩
    · obtain rfl | hij := Decidable.eq_or_ne i j
      · rw [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne' hij, nnnorm_zero]
        exact zero_le _
    · rw [Pi.single_eq_same]
  | coe p =>
    have hp0 : (p : ℝ) ≠ 0 :=
      mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 ≤ (p : ℝ≥0∞))).ne'
    rw [nnnorm_eq_sum ENNReal.coe_ne_top, ENNReal.coe_toReal, Fintype.sum_eq_single i,
      WithLp.equiv_symm_pi_apply, Pi.single_eq_same, ← NNReal.rpow_mul, one_div,
      mul_inv_cancel₀ hp0, NNReal.rpow_one]
    intro j hij
    rw [WithLp.equiv_symm_pi_apply, Pi.single_eq_of_ne hij, nnnorm_zero, NNReal.zero_rpow hp0]

@[simp]
theorem norm_equiv_symm_single (i : ι) (b : β i) :
    ‖(WithLp.equiv p (∀ i, β i)).symm (Pi.single i b)‖ = ‖b‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_equiv_symm_single p β i b

@[simp]
theorem nndist_equiv_symm_single_same (i : ι) (b₁ b₂ : β i) :
    nndist
        ((WithLp.equiv p (∀ i, β i)).symm (Pi.single i b₁))
        ((WithLp.equiv p (∀ i, β i)).symm (Pi.single i b₂)) =
      nndist b₁ b₂ := by
  rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← WithLp.equiv_symm_sub, ← Pi.single_sub,
    nnnorm_equiv_symm_single]

@[simp]
theorem dist_equiv_symm_single_same (i : ι) (b₁ b₂ : β i) :
    dist
        ((WithLp.equiv p (∀ i, β i)).symm (Pi.single i b₁))
        ((WithLp.equiv p (∀ i, β i)).symm (Pi.single i b₂)) =
      dist b₁ b₂ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nndist_equiv_symm_single_same p β i b₁ b₂

@[simp]
theorem edist_equiv_symm_single_same (i : ι) (b₁ b₂ : β i) :
    edist
        ((WithLp.equiv p (∀ i, β i)).symm (Pi.single i b₁))
        ((WithLp.equiv p (∀ i, β i)).symm (Pi.single i b₂)) =
      edist b₁ b₂ := by
  simp only [edist_nndist, nndist_equiv_symm_single_same p β i b₁ b₂]

end Single

/-- When `p = ∞`, this lemma does not hold without the additional assumption `Nonempty ι` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `‖b‖₊`. See
`PiLp.nnnorm_equiv_symm_const'` for a version which exchanges the hypothesis `p ≠ ∞` for
`Nonempty ι`. -/
theorem nnnorm_equiv_symm_const {β} [SeminormedAddCommGroup β] (hp : p ≠ ∞) (b : β) :
    ‖(WithLp.equiv p (ι → β)).symm (Function.const _ b)‖₊ =
      (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖b‖₊ := by
  rcases p.dichotomy with (h | h)
  · exact False.elim (hp h)
  · have ne_zero : p.toReal ≠ 0 := (zero_lt_one.trans_le h).ne'
    simp_rw [nnnorm_eq_sum hp, WithLp.equiv_symm_pi_apply, Function.const_apply, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, NNReal.mul_rpow, ← NNReal.rpow_mul,
      mul_one_div_cancel ne_zero, NNReal.rpow_one, ENNReal.toReal_div, ENNReal.one_toReal]

/-- When `IsEmpty ι`, this lemma does not hold without the additional assumption `p ≠ ∞` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `‖b‖₊`. See
`PiLp.nnnorm_equiv_symm_const` for a version which exchanges the hypothesis `Nonempty ι`.
for `p ≠ ∞`. -/
theorem nnnorm_equiv_symm_const' {β} [SeminormedAddCommGroup β] [Nonempty ι] (b : β) :
    ‖(WithLp.equiv p (ι → β)).symm (Function.const _ b)‖₊ =
      (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖b‖₊ := by
  rcases em <| p = ∞ with (rfl | hp)
  · simp only [WithLp.equiv_symm_pi_apply, ENNReal.div_top, ENNReal.zero_toReal, NNReal.rpow_zero,
      one_mul, nnnorm_eq_ciSup, Function.const_apply, ciSup_const]
  · exact nnnorm_equiv_symm_const hp b

/-- When `p = ∞`, this lemma does not hold without the additional assumption `Nonempty ι` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `‖b‖₊`. See
`PiLp.norm_equiv_symm_const'` for a version which exchanges the hypothesis `p ≠ ∞` for
`Nonempty ι`. -/
theorem norm_equiv_symm_const {β} [SeminormedAddCommGroup β] (hp : p ≠ ∞) (b : β) :
    ‖(WithLp.equiv p (ι → β)).symm (Function.const _ b)‖ =
      (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖b‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_equiv_symm_const hp b).trans <| by simp

/-- When `IsEmpty ι`, this lemma does not hold without the additional assumption `p ≠ ∞` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `‖b‖₊`. See
`PiLp.norm_equiv_symm_const` for a version which exchanges the hypothesis `Nonempty ι`.
for `p ≠ ∞`. -/
theorem norm_equiv_symm_const' {β} [SeminormedAddCommGroup β] [Nonempty ι] (b : β) :
    ‖(WithLp.equiv p (ι → β)).symm (Function.const _ b)‖ =
      (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖b‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_equiv_symm_const' b).trans <| by simp

theorem nnnorm_equiv_symm_one {β} [SeminormedAddCommGroup β] (hp : p ≠ ∞) [One β] :
    ‖(WithLp.equiv p (ι → β)).symm 1‖₊ =
      (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖(1 : β)‖₊ :=
  (nnnorm_equiv_symm_const hp (1 : β)).trans rfl

theorem norm_equiv_symm_one {β} [SeminormedAddCommGroup β] (hp : p ≠ ∞) [One β] :
    ‖(WithLp.equiv p (ι → β)).symm 1‖ = (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖(1 : β)‖ :=
  (norm_equiv_symm_const hp (1 : β)).trans rfl

variable (𝕜 p)

/-- `WithLp.equiv` as a continuous linear equivalence. -/
@[simps! (config := .asFn) apply symm_apply]
protected def continuousLinearEquiv : PiLp p β ≃L[𝕜] ∀ i, β i where
  toLinearEquiv := WithLp.linearEquiv _ _ _
  continuous_toFun := continuous_equiv _ _
  continuous_invFun := continuous_equiv_symm _ _

variable {𝕜} in
/-- The projection on the `i`-th coordinate of `PiLp p β`, as a continuous linear map. -/
@[simps!]
def proj (i : ι) : PiLp p β →L[𝕜] β i where
  __ := projₗ p β i
  cont := continuous_apply i

end Fintype

section Basis

variable [Finite ι] [Ring 𝕜]
variable (ι)

/-- A version of `Pi.basisFun` for `PiLp`. -/
def basisFun : Basis ι 𝕜 (PiLp p fun _ : ι => 𝕜) :=
  Basis.ofEquivFun (WithLp.linearEquiv p 𝕜 (ι → 𝕜))

@[simp]
theorem basisFun_apply [DecidableEq ι] (i) :
    basisFun p 𝕜 ι i = (WithLp.equiv p _).symm (Pi.single i 1) := by
  simp_rw [basisFun, Basis.coe_ofEquivFun, WithLp.linearEquiv_symm_apply]

@[simp]
theorem basisFun_repr (x : PiLp p fun _ : ι => 𝕜) (i : ι) : (basisFun p 𝕜 ι).repr x i = x i :=
  rfl

@[simp]
theorem basisFun_equivFun : (basisFun p 𝕜 ι).equivFun = WithLp.linearEquiv p 𝕜 (ι → 𝕜) :=
  Basis.equivFun_ofEquivFun _

theorem basisFun_eq_pi_basisFun :
    basisFun p 𝕜 ι = (Pi.basisFun 𝕜 ι).map (WithLp.linearEquiv p 𝕜 (ι → 𝕜)).symm :=
  rfl

@[simp]
theorem basisFun_map :
    (basisFun p 𝕜 ι).map (WithLp.linearEquiv p 𝕜 (ι → 𝕜)) = Pi.basisFun 𝕜 ι :=
  rfl

end Basis

open Matrix

nonrec theorem basis_toMatrix_basisFun_mul [Fintype ι]
    {𝕜} [SeminormedCommRing 𝕜] (b : Basis ι 𝕜 (PiLp p fun _ : ι => 𝕜))
    (A : Matrix ι ι 𝕜) :
    b.toMatrix (PiLp.basisFun _ _ _) * A =
      Matrix.of fun i j => b.repr ((WithLp.equiv _ _).symm (Aᵀ j)) i := by
  have := basis_toMatrix_basisFun_mul (b.map (WithLp.linearEquiv _ 𝕜 _)) A
  simp_rw [← PiLp.basisFun_map p, Basis.map_repr, LinearEquiv.trans_apply,
    WithLp.linearEquiv_symm_apply, Basis.toMatrix_map, Function.comp_def, Basis.map_apply,
    LinearEquiv.symm_apply_apply] at this
  exact this

end PiLp
