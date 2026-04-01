/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Jireh Loreaux
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Data.Fintype.Order
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.Analysis.Normed.Lp.ProdLp

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
`PiLp p α`. The assumption `[Fact (1 ≤ p)]` is required for the metric and normed space instances.

We ensure that the topology, bornology and uniform structure on `PiLp p α` are (defeq to) the
product topology, product bornology and product uniformity, to be able to use freely continuity
statements for the coordinate functions, for instance.

If you wish to endow a type synonym of `Π i, α i` with the `L^p` distance, you can use
`pseudoMetricSpaceToPi` and the declarations below that one.

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

## TODO

TODO: the results about uniformity and bornology in the `Aux` section should be using the tools in
`Mathlib.Topology.MetricSpace.Bilipschitz`, so that they can be inlined in the next section and
the only remaining results are about `Lipschitz` and `Antilipschitz`.
-/

@[expose] public section

open Module Real Set Filter RCLike Bornology Uniformity Topology NNReal ENNReal WithLp

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
  coe := ofLp

instance (p : ℝ≥0∞) {ι : Type*} (α : ι → Type*) [∀ i, Inhabited (α i)] : Inhabited (PiLp p α) :=
  ⟨toLp p fun _ => default⟩

@[ext]
protected theorem PiLp.ext {p : ℝ≥0∞} {ι : Type*} {α : ι → Type*} {x y : PiLp p α}
    (h : ∀ i, x i = y i) : x = y := ofLp_injective p <| funext h

namespace PiLp

variable (p : ℝ≥0∞) (𝕜 : Type*) {ι : Type*} (α : ι → Type*) (β : ι → Type*)
section
/- Register simplification lemmas for the applications of `PiLp` elements, as the usual lemmas
for Pi types will not trigger. -/
variable {𝕜 p α}
variable [Semiring 𝕜] [∀ i, SeminormedAddCommGroup (β i)]
variable [∀ i, Module 𝕜 (β i)] (c : 𝕜)
variable (x y : PiLp p β) (i : ι)

@[simp]
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

lemma toLp_apply (x : ∀ i, α i) (i : ι) : toLp p x i = x i := rfl

section Single
variable [DecidableEq ι]
variable {β}

section Zero
variable [∀ i, Zero (β i)]

/-- The vector given in `PiLp` by being `a : β i` at coordinate `i : ι` and `0 : β j` at
all other coordinates `j`. -/
def single (i : ι) (a : β i) : PiLp p β := toLp p (Pi.single i a)

@[simp]
lemma ofLp_single (i : ι) (a : β i) : ofLp (single p i a) = Pi.single i a := rfl

@[simp]
lemma toLp_single (i : ι) (a : β i) : toLp p (Pi.single i a) = single p i a := rfl

@[simp]
lemma single_eq_same (i : ι) (a : β i) : single p i a i = a := by
  rw [ofLp_single, Pi.single_eq_same]

@[simp]
lemma single_eq_of_ne {i i' : ι} (h : i' ≠ i) (a : β i) : single p i a i' = 0 := by
  rw [ofLp_single, Pi.single_eq_of_ne h]

/-- Changing the hypothesis direction in `PiLp.single_eq_of_ne` for for ease of use by simp. -/
@[simp]
lemma single_eq_of_ne' {i i' : ι} (h : i ≠ i') (a : β i) : single p i a i' = 0 := by
  rw [ofLp_single, Pi.single_eq_of_ne' h]

end Zero

@[simp]
lemma single_apply [Zero 𝕜] (i : ι) (a : 𝕜) (j : ι) :
    (single p i a : PiLp p (fun _ ↦ 𝕜)) j = ite (j = i) a 0 := by
  rw [← toLp_single, PiLp.toLp_apply, ← Pi.single_apply i a j]

section AddCommGroup
variable [∀ i, AddCommGroup (β i)]

@[simp]
theorem single_eq_zero_iff (p : ℝ≥0∞) (i : ι) {a : β i} :
    single p i a = 0 ↔ a = 0 :=
  (toLp_eq_zero p).trans Pi.single_eq_zero_iff

lemma single_add (p : ℝ≥0∞) (i : ι) {a b : β i} :
    single p i (a + b) = single p i a + single p i b := by
  simp_rw [← toLp_single, Pi.single_add, toLp_add]

lemma single_sub (p : ℝ≥0∞) (i : ι) {a b : β i} :
    single p i (a - b) = single p i a - single p i b := by
  simp_rw [← toLp_single, Pi.single_sub, toLp_sub]

lemma single_neg (p : ℝ≥0∞) (i : ι) {a : β i} :
    single p i (-a) = -single p i a := by
  simp_rw [← toLp_single, Pi.single_neg, toLp_neg]

end AddCommGroup

section LinearIndependent

theorem linearIndependent_single [Semiring 𝕜] {η : Type*} {ιs : η → Type*}
    {Ms : η → Type*} [∀ i, AddCommGroup (Ms i)] [∀ i, Module 𝕜 (Ms i)] [DecidableEq η]
    (v : ∀ j, ιs j → Ms j) (hs : ∀ i, LinearIndependent 𝕜 (v i)) :
    LinearIndependent 𝕜 fun ji : Σ j, ιs j ↦ single p ji.1 (v ji.1 ji.2) := by
  suffices LinearIndependent 𝕜 ((WithLp.linearEquiv p 𝕜 _).symm.toLinearMap ∘
      fun ji : Σ j, ιs j ↦ Pi.single ji.1 (v ji.1 ji.2)) by
    simpa
  rw [LinearMap.linearIndependent_iff_of_injOn _ (by simp)]
  exact Pi.linearIndependent_single v hs

theorem linearIndependent_single_one [Ring 𝕜] :
    LinearIndependent 𝕜 (fun i : ι ↦ single p i (1 : 𝕜)) := by
  suffices LinearIndependent 𝕜 ((WithLp.linearEquiv p 𝕜 _).symm.toLinearMap ∘
      fun i : ι ↦ Pi.single i (1 : 𝕜)) by
    simpa
  rw [LinearMap.linearIndependent_iff_of_injOn _ (by simp)]
  exact Pi.linearIndependent_single_one ι 𝕜

theorem linearIndependent_single_of_ne_zero [Ring 𝕜] [IsDomain 𝕜] {M : Type*}
    [AddCommGroup M] [Module 𝕜 M] [IsTorsionFree 𝕜 M] {v : ι → M} (hv : ∀ i, v i ≠ 0) :
    LinearIndependent 𝕜 fun i : ι ↦ single p i (v i) := by
  suffices LinearIndependent 𝕜 ((WithLp.linearEquiv p 𝕜 _).symm.toLinearMap ∘
      fun i : ι ↦ Pi.single i (v i)) by
    simpa
  rw [LinearMap.linearIndependent_iff_of_injOn _ (by simp)]
  exact Pi.linearIndependent_single_of_ne_zero hv

end LinearIndependent

end Single

section DistNorm

variable [Fintype ι]

/-!
### Definition of `edist`, `dist` and `norm` on `PiLp`

In this section we define the `edist`, `dist` and `norm` functions on `PiLp p α` without assuming
`[Fact (1 ≤ p)]` or metric properties of the spaces `α i`. This allows us to provide the rewrite
lemmas for each of three cases `p = 0`, `p = ∞` and `0 < p.to_real`.
-/


section EDist

variable [∀ i, EDist (β i)]

/-- Endowing the space `PiLp p β` with the `L^p` edistance. We register this instance
separate from `pi_Lp.pseudo_emetric` since the latter requires the type class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

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

end EDist

section EDistProp

variable {β}
variable [∀ i, PseudoEMetricSpace (β i)]

/-- This holds independent of `p` and does not require `[Fact (1 ≤ p)]`. We keep it separate
from `pi_Lp.pseudo_emetric_space` so it can be used also for `p < 1`. -/
protected theorem edist_self (f : PiLp p β) : edist f f = 0 := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp [edist_eq_card]
  · simp [edist_eq_iSup]
  · simp [edist_eq_sum h, ENNReal.zero_rpow_of_pos h, ENNReal.zero_rpow_of_pos (inv_pos.2 <| h)]

/-- This holds independent of `p` and does not require `[Fact (1 ≤ p)]`. We keep it separate
from `pi_Lp.pseudo_emetric_space` so it can be used also for `p < 1`. -/
protected theorem edist_comm (f g : PiLp p β) : edist f g = edist g f := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp only [edist_eq_card, edist_comm]
  · simp only [edist_eq_iSup, edist_comm]
  · simp only [edist_eq_sum h, edist_comm]

end EDistProp

section Dist

variable [∀ i, Dist (α i)]

/-- Endowing the space `PiLp p β` with the `L^p` distance. We register this instance
separate from `pi_Lp.pseudo_metric` since the latter requires the type class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

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
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future norm-like structure on `PiLp p β` for `p < 1`
satisfying a relaxed triangle inequality. These are called *quasi-norms*. -/
instance instNorm : Norm (PiLp p β) where
  norm f :=
    if p = 0 then {i | ‖f i‖ ≠ 0}.toFinite.toFinset.card
    else if p = ∞ then ⨆ i, ‖f i‖ else (∑ i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)

variable {p β}

theorem norm_eq_card (f : PiLp 0 β) : ‖f‖ = {i | ‖f i‖ ≠ 0}.toFinite.toFinset.card :=
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

TODO: the results about uniformity and bornology should be using the tools in
`Mathlib.Topology.MetricSpace.Bilipschitz`, so that they can be inlined in the next section and
the only remaining results are about `Lipschitz` and `Antilipschitz`.
-/


variable [Fact (1 ≤ p)] [∀ i, PseudoMetricSpace (α i)] [∀ i, PseudoEMetricSpace (β i)]
variable [Fintype ι]

/-- Endowing the space `PiLp p β` with the `L^p` pseudoemetric structure. This definition is not
satisfactory, as it does not register the fact that the topology and the uniform structure coincide
with the product one. Therefore, we do not register it as an instance. Using this as a temporary
pseudoemetric space instance, we will show that the uniform structure is equal (but not defeq) to
the product one, and then register an instance in which we replace the uniform structure by the
product one using this pseudoemetric space and `PseudoEMetricSpace.replaceUniformity`. -/
@[instance_reducible]
def pseudoEmetricAux : PseudoEMetricSpace (PiLp p β) where
  edist_self := PiLp.edist_self p
  edist_comm := PiLp.edist_comm p
  edist_triangle f g h := by
    rcases p.dichotomy with (rfl | hp)
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
      rcases p.dichotomy with (rfl | h)
      · simp only [dist, top_ne_zero, ↓reduceIte]
        exact Real.iSup_nonneg fun i ↦ dist_nonneg
      · simp only [dist]
        split_ifs with hp
        · linarith
        · exact Real.iSup_nonneg fun i ↦ dist_nonneg
        · exact rpow_nonneg (Fintype.sum_nonneg fun i ↦ by positivity) (1 / p.toReal))
    fun f g => by
    rcases p.dichotomy with (rfl | h)
    · rw [edist_eq_iSup, dist_eq_iSup]
      cases isEmpty_or_nonempty ι
      · simp
      · refine ENNReal.eq_of_forall_le_nnreal_iff fun r ↦ ?_
        have : BddAbove <| .range fun i ↦ dist (f i) (g i) := Finite.bddAbove_range _
        simp [ciSup_le_iff this]
    · have : 0 < p.toReal := by rw [ENNReal.toReal_pos_iff_ne_top]; rintro rfl; norm_num at h
      simp only [edist_eq_sum, edist_dist, dist_eq_sum, this]
      rw [← ENNReal.ofReal_rpow_of_nonneg (by simp [Finset.sum_nonneg, Real.rpow_nonneg]) (by simp)]
      simp [Real.rpow_nonneg, ENNReal.ofReal_sum_of_nonneg, ← ENNReal.ofReal_rpow_of_nonneg]

attribute [local instance] PiLp.pseudoMetricAux

variable {p β} in
private theorem edist_apply_le_edist_aux (x y : PiLp p β) (i : ι) :
    edist (x i) (y i) ≤ edist x y := by
  rcases p.dichotomy with (rfl | h)
  · simpa only [edist_eq_iSup] using le_iSup (fun i => edist (x i) (y i)) i
  · have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (zero_lt_one.trans_le h).ne'
    rw [edist_eq_sum (zero_lt_one.trans_le h)]
    calc
      edist (x i) (y i) = (edist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) := by
        simp [← ENNReal.rpow_mul, cancel, -one_div]
      _ ≤ (∑ i, edist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) := by
        gcongr
        exact Finset.single_le_sum (fun i _ => (bot_le : (0 : ℝ≥0∞) ≤ _)) (Finset.mem_univ i)

private lemma lipschitzWith_ofLp_aux : LipschitzWith 1 (@ofLp p (∀ i, β i)) :=
  .of_edist_le fun x y => by
    simp_rw [edist_pi_def, Finset.sup_le_iff, Finset.mem_univ, forall_true_left]
    exact edist_apply_le_edist_aux _ _

private lemma antilipschitzWith_ofLp_aux :
    AntilipschitzWith ((Fintype.card ι : ℝ≥0) ^ (1 / p).toReal) (@ofLp p (∀ i, β i)) := by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simp only [edist_eq_iSup, ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero,
      ENNReal.coe_one, one_mul, iSup_le_iff]
    -- Porting note: `Finset.le_sup` needed some help
    exact fun i => Finset.le_sup (f := fun i => edist (x i) (y i)) (Finset.mem_univ i)
  · have pos : 0 < p.toReal := zero_lt_one.trans_le h
    have nonneg : 0 ≤ 1 / p.toReal := one_div_nonneg.2 (le_of_lt pos)
    have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (ne_of_gt pos)
    rw [edist_eq_sum pos, ENNReal.toReal_div 1 p]
    simp only [edist, ENNReal.toReal_one]
    calc
      (∑ i, edist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) ≤
          (∑ _i, edist (ofLp x) (ofLp y) ^ p.toReal) ^ (1 / p.toReal) := by
        gcongr with i
        exact Finset.le_sup (f := fun i => edist (x i) (y i)) (Finset.mem_univ i)
      _ =
          ((Fintype.card ι : ℝ≥0) ^ (1 / p.toReal) : ℝ≥0) *
            edist (ofLp x) (ofLp y) := by
        simp only [nsmul_eq_mul, Finset.card_univ, ENNReal.rpow_one, Finset.sum_const,
          ENNReal.mul_rpow_of_nonneg _ _ nonneg, ← ENNReal.rpow_mul, cancel]
        have : (Fintype.card ι : ℝ≥0∞) = (Fintype.card ι : ℝ≥0) :=
          (ENNReal.coe_natCast (Fintype.card ι)).symm
        rw [this, ENNReal.coe_rpow_of_nonneg _ nonneg]

private lemma isUniformInducing_ofLp_aux : IsUniformInducing (@ofLp p (∀ i, β i)) :=
    (antilipschitzWith_ofLp_aux p β).isUniformInducing
      (lipschitzWith_ofLp_aux p β).uniformContinuous

set_option backward.privateInPublic true in
private lemma uniformity_aux : 𝓤 (PiLp p β) = 𝓤[UniformSpace.comap ofLp inferInstance] := by
  rw [← (isUniformInducing_ofLp_aux p β).comap_uniformity]
  rfl

instance bornology (p : ℝ≥0∞) (β : ι → Type*) [∀ i, Bornology (β i)] :
    Bornology (PiLp p β) := Bornology.induced ofLp

set_option backward.privateInPublic true in
private lemma cobounded_aux : @cobounded _ PseudoMetricSpace.toBornology = cobounded (PiLp p α) :=
  le_antisymm (antilipschitzWith_ofLp_aux p α).tendsto_cobounded.le_comap
    (lipschitzWith_ofLp_aux p α).comap_cobounded_le

end Aux

/-! ### Instances on finite `L^p` products -/

instance topologicalSpace [∀ i, TopologicalSpace (β i)] : TopologicalSpace (PiLp p β) :=
  Pi.topologicalSpace.induced ofLp

@[fun_prop, continuity]
theorem continuous_ofLp [∀ i, TopologicalSpace (β i)] : Continuous (@ofLp p (∀ i, β i)) :=
  continuous_induced_dom

@[fun_prop, continuity]
protected lemma continuous_apply [∀ i, TopologicalSpace (β i)] (i : ι) :
    Continuous (fun f : PiLp p β ↦ f i) := (continuous_apply i).comp (continuous_ofLp p β)

@[fun_prop, continuity]
theorem continuous_toLp [∀ i, TopologicalSpace (β i)] : Continuous (@toLp p (∀ i, β i)) :=
  continuous_induced_rng.2 continuous_id

/-- `WithLp.equiv` as a homeomorphism. -/
def homeomorph [∀ i, TopologicalSpace (β i)] : PiLp p β ≃ₜ (Π i, β i) where
  toEquiv := WithLp.equiv p (Π i, β i)
  continuous_toFun := continuous_ofLp p β
  continuous_invFun := continuous_toLp p β

@[simp]
lemma toEquiv_homeomorph [∀ i, TopologicalSpace (β i)] :
    (homeomorph p β).toEquiv = WithLp.equiv p (Π i, β i) := rfl

lemma isOpenMap_apply [∀ i, TopologicalSpace (β i)] (i : ι) :
    IsOpenMap (fun f : PiLp p β ↦ f i) := (isOpenMap_eval i).comp (homeomorph p β).isOpenMap

instance instProdT0Space [∀ i, TopologicalSpace (β i)] [∀ i, T0Space (β i)] :
    T0Space (PiLp p β) :=
  (homeomorph p β).symm.t0Space

instance secondCountableTopology [Countable ι] [∀ i, TopologicalSpace (β i)]
    [∀ i, SecondCountableTopology (β i)] : SecondCountableTopology (PiLp p β) :=
  (homeomorph p β).secondCountableTopology

instance uniformSpace [∀ i, UniformSpace (β i)] : UniformSpace (PiLp p β) :=
  (Pi.uniformSpace β).comap ofLp

lemma uniformContinuous_ofLp [∀ i, UniformSpace (β i)] :
    UniformContinuous (@ofLp p (∀ i, β i)) :=
  uniformContinuous_comap

lemma uniformContinuous_toLp [∀ i, UniformSpace (β i)] :
    UniformContinuous (@toLp p (∀ i, β i)) :=
  uniformContinuous_comap' uniformContinuous_id

/-- `WithLp.equiv` as a uniform isomorphism. -/
def uniformEquiv [∀ i, UniformSpace (β i)] : PiLp p β ≃ᵤ (Π i, β i) where
  toEquiv := WithLp.equiv p (Π i, β i)
  uniformContinuous_toFun := uniformContinuous_ofLp p β
  uniformContinuous_invFun := uniformContinuous_toLp p β

@[simp]
lemma toHomeomorph_uniformEquiv [∀ i, UniformSpace (β i)] :
    (uniformEquiv p β).toHomeomorph = homeomorph p β := rfl

@[simp]
lemma toEquiv_uniformEquiv [∀ i, UniformSpace (β i)] :
    (uniformEquiv p β).toEquiv = WithLp.equiv p (Π i, β i) := rfl

instance completeSpace [∀ i, UniformSpace (β i)] [∀ i, CompleteSpace (β i)] :
    CompleteSpace (PiLp p β) :=
  (uniformEquiv p β).completeSpace_iff.2 inferInstance

section Fintype
variable [hp : Fact (1 ≤ p)]
variable [Fintype ι]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- pseudoemetric space instance on the product of finitely many pseudoemetric spaces, using the
`L^p` pseudoedistance, and having as uniformity the product uniformity. -/
instance [∀ i, PseudoEMetricSpace (β i)] : PseudoEMetricSpace (PiLp p β) :=
  (pseudoEmetricAux p β).replaceUniformity (uniformity_aux p β).symm

/-- emetric space instance on the product of finitely many emetric spaces, using the `L^p`
edistance, and having as uniformity the product uniformity. -/
instance [∀ i, EMetricSpace (α i)] : EMetricSpace (PiLp p α) :=
  EMetricSpace.ofT0PseudoEMetricSpace (PiLp p α)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- pseudometric space instance on the product of finitely many pseudometric spaces, using the
`L^p` distance, and having as uniformity the product uniformity. -/
instance [∀ i, PseudoMetricSpace (β i)] : PseudoMetricSpace (PiLp p β) :=
  ((pseudoMetricAux p β).replaceUniformity (uniformity_aux p β).symm).replaceBornology fun s =>
    Filter.ext_iff.1 (cobounded_aux p β).symm sᶜ

/-- metric space instance on the product of finitely many metric spaces, using the `L^p` distance,
and having as uniformity the product uniformity. -/
instance [∀ i, MetricSpace (α i)] : MetricSpace (PiLp p α) :=
  MetricSpace.ofT0PseudoMetricSpace _

theorem nndist_eq_sum {p : ℝ≥0∞} [Fact (1 ≤ p)] {β : ι → Type*} [∀ i, PseudoMetricSpace (β i)]
    (hp : p ≠ ∞) (x y : PiLp p β) :
    nndist x y = (∑ i : ι, nndist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) :=
  NNReal.eq <| by
    push_cast
    exact dist_eq_sum (p.toReal_pos_iff_ne_top.mpr hp) _ _

theorem nndist_eq_iSup {β : ι → Type*} [∀ i, PseudoMetricSpace (β i)] (x y : PiLp ∞ β) :
    nndist x y = ⨆ i, nndist (x i) (y i) :=
  NNReal.eq <| by
    push_cast
    exact dist_eq_iSup _ _

section
variable {β p}

theorem edist_apply_le [∀ i, PseudoEMetricSpace (β i)] (x y : PiLp p β) (i : ι) :
    edist (x i) (y i) ≤ edist x y :=
  edist_apply_le_edist_aux x y i

theorem nndist_apply_le [∀ i, PseudoMetricSpace (β i)] (x y : PiLp p β) (i : ι) :
    nndist (x i) (y i) ≤ nndist x y := by
  simpa [← coe_nnreal_ennreal_nndist] using edist_apply_le x y i

theorem dist_apply_le [∀ i, PseudoMetricSpace (β i)] (x y : PiLp p β) (i : ι) :
    dist (x i) (y i) ≤ dist x y :=
  nndist_apply_le x y i

end

lemma lipschitzWith_ofLp [∀ i, PseudoEMetricSpace (β i)] :
    LipschitzWith 1 (@ofLp p (∀ i, β i)) :=
  lipschitzWith_ofLp_aux p β

lemma antilipschitzWith_toLp [∀ i, PseudoEMetricSpace (β i)] :
    AntilipschitzWith 1 (@toLp p (∀ i, β i)) :=
  (lipschitzWith_ofLp p β).to_rightInverse (ofLp_toLp p)

theorem antilipschitzWith_ofLp [∀ i, PseudoEMetricSpace (β i)] :
    AntilipschitzWith ((Fintype.card ι : ℝ≥0) ^ (1 / p).toReal) (@ofLp p (∀ i, β i)) :=
  antilipschitzWith_ofLp_aux p β

lemma lipschitzWith_toLp [∀ i, PseudoEMetricSpace (β i)] :
    LipschitzWith ((Fintype.card ι : ℝ≥0) ^ (1 / p).toReal) (@toLp p (∀ i, β i)) :=
  (antilipschitzWith_ofLp p β).to_rightInverse (ofLp_toLp p)

lemma isometry_ofLp_infty [∀ i, PseudoEMetricSpace (β i)] :
    Isometry (@ofLp ∞ (∀ i, β i)) :=
  fun x y =>
  le_antisymm (by simpa only [ENNReal.coe_one, one_mul] using lipschitzWith_ofLp ∞ β x y)
    (by simpa only [ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero, ENNReal.coe_one,
      one_mul] using antilipschitzWith_ofLp ∞ β x y)

/-- seminormed group instance on the product of finitely many normed groups, using the `L^p`
norm. -/
instance seminormedAddCommGroup [∀ i, SeminormedAddCommGroup (β i)] :
    SeminormedAddCommGroup (PiLp p β) where
  dist_eq := fun x y => by
    rcases p.dichotomy with (rfl | h)
    · simp only [dist_eq_iSup, norm_eq_ciSup, dist_eq_norm, add_apply, neg_apply, norm_neg_add]
    · have : p ≠ ∞ := by
        intro hp
        rw [hp, ENNReal.toReal_top] at h
        linarith
      simp only [dist_eq_sum (zero_lt_one.trans_le h), norm_eq_sum (zero_lt_one.trans_le h),
        dist_eq_norm, add_apply, neg_apply, norm_neg_add]

omit [Fintype ι] in
lemma isUniformInducing_toLp [Finite ι] [∀ i, PseudoEMetricSpace (β i)] :
    IsUniformInducing (@toLp p (Π i, β i)) :=
  have := Fintype.ofFinite ι
  (antilipschitzWith_toLp p β).isUniformInducing
    (lipschitzWith_toLp p β).uniformContinuous

section
variable {β p}

theorem enorm_apply_le [∀ i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i : ι) :
    ‖x i‖ₑ ≤ ‖x‖ₑ := by
  simpa using edist_apply_le x 0 i

theorem nnnorm_apply_le [∀ i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i : ι) :
    ‖x i‖₊ ≤ ‖x‖₊ := by
  simpa using nndist_apply_le x 0 i

theorem norm_apply_le [∀ i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i : ι) :
    ‖x i‖ ≤ ‖x‖ := by
  simpa using dist_apply_le x 0 i

end

/-- normed group instance on the product of finitely many normed groups, using the `L^p` norm. -/
instance normedAddCommGroup [∀ i, NormedAddCommGroup (α i)] : NormedAddCommGroup (PiLp p α) :=
  { PiLp.seminormedAddCommGroup p α with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

theorem nnnorm_eq_sum {p : ℝ≥0∞} [Fact (1 ≤ p)] {β : ι → Type*} (hp : p ≠ ∞)
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

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma nnnorm_ofLp (f : PiLp ∞ β) : ‖ofLp f‖₊ = ‖f‖₊ := by
  rw [nnnorm_eq_ciSup, Pi.nnnorm_def, Finset.sup_univ_eq_ciSup]

@[simp] lemma nnnorm_toLp (f : ∀ i, β i) : ‖toLp ∞ f‖₊ = ‖f‖₊ := (nnnorm_ofLp _).symm

@[simp] lemma norm_ofLp (f : PiLp ∞ β) : ‖ofLp f‖ = ‖f‖ := congr_arg NNReal.toReal <| nnnorm_ofLp f
@[simp] lemma norm_toLp (f : ∀ i, β i) : ‖toLp ∞ f‖ = ‖f‖ := (norm_ofLp _).symm

end Linfty

theorem norm_eq_of_nat {p : ℝ≥0∞} [Fact (1 ≤ p)] {β : ι → Type*}
    [∀ i, SeminormedAddCommGroup (β i)] (n : ℕ) (h : p = n) (f : PiLp p β) :
    ‖f‖ = (∑ i, ‖f i‖ ^ n) ^ (1 / (n : ℝ)) := by
  have := p.toReal_pos_iff_ne_top.mpr (ne_of_eq_of_ne h <| ENNReal.natCast_ne_top n)
  simp only [one_div, h, Real.rpow_natCast, ENNReal.toReal_natCast,
    norm_eq_sum this]

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

theorem dist_sq_eq_of_L2 (x y : PiLp 2 β) :
    dist x y ^ 2 = ∑ i, dist (x i) (y i) ^ 2 := by
  simp_rw [dist_eq_norm, norm_sq_eq_of_L2, sub_apply]

theorem nndist_eq_of_L2 (x y : PiLp 2 β) :
    nndist x y = NNReal.sqrt (∑ i, nndist (x i) (y i) ^ 2) :=
  NNReal.eq <| by
    push_cast
    exact dist_eq_of_L2 _ _

theorem edist_eq_of_L2 (x y : PiLp 2 β) :
    edist x y = (∑ i, edist (x i) (y i) ^ 2) ^ (1 / 2 : ℝ) := by simp [PiLp.edist_eq_sum]

end L2

instance instIsBoundedSMul [SeminormedRing 𝕜] [∀ i, SeminormedAddCommGroup (β i)]
    [∀ i, Module 𝕜 (β i)] [∀ i, IsBoundedSMul 𝕜 (β i)] :
    IsBoundedSMul 𝕜 (PiLp p β) :=
  .of_nnnorm_smul_le fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · rw [← nnnorm_ofLp, ← nnnorm_ofLp, ofLp_smul]
      exact nnnorm_smul_le c (ofLp f)
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p ≠ ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [nnnorm_eq_sum hpt, nnnorm_eq_sum hpt, one_div, NNReal.rpow_inv_le_iff hp0,
        NNReal.mul_rpow, ← NNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', NNReal.rpow_one,
        Finset.mul_sum]
      simp_rw [← NNReal.mul_rpow, smul_apply]
      gcongr
      apply nnnorm_smul_le

instance instNormSMulClass [SeminormedRing 𝕜] [∀ i, SeminormedAddCommGroup (β i)]
    [∀ i, Module 𝕜 (β i)] [∀ i, NormSMulClass 𝕜 (β i)] :
    NormSMulClass 𝕜 (PiLp p β) :=
  .of_nnnorm_smul fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · rw [← nnnorm_ofLp, ← nnnorm_ofLp, WithLp.ofLp_smul, nnnorm_smul]
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p ≠ ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [nnnorm_eq_sum hpt, nnnorm_eq_sum hpt, one_div, NNReal.rpow_inv_eq_iff hp0.ne',
        NNReal.mul_rpow, ← NNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', NNReal.rpow_one,
        Finset.mul_sum]
      simp_rw [← NNReal.mul_rpow, smul_apply, nnnorm_smul]

/-- The product of finitely many normed spaces is a normed space, with the `L^p` norm. -/
instance normedSpace [NormedField 𝕜] [∀ i, SeminormedAddCommGroup (β i)]
    [∀ i, NormedSpace 𝕜 (β i)] : NormedSpace 𝕜 (PiLp p β) where
  norm_smul_le := norm_smul_le

variable {𝕜 p α}
variable [Semiring 𝕜] [∀ i, SeminormedAddCommGroup (α i)] [∀ i, SeminormedAddCommGroup (β i)]
variable [∀ i, Module 𝕜 (α i)] [∀ i, Module 𝕜 (β i)] (c : 𝕜)

/-- The canonical map `WithLp.equiv` between `PiLp ∞ β` and `Π i, β i` as a linear isometric
equivalence. -/
def equivₗᵢ : PiLp ∞ β ≃ₗᵢ[𝕜] (∀ i, β i) where
  __ := WithLp.linearEquiv ∞ 𝕜 _
  norm_map' := norm_ofLp

section piLpCongrLeft
variable {ι' : Type*}
variable [Fintype ι']
variable (p 𝕜)
variable (E : Type*) [SeminormedAddCommGroup E] [Module 𝕜 E]

/-- An equivalence of finite domains induces a linearly isometric equivalence of finitely supported
functions. -/
def _root_.LinearIsometryEquiv.piLpCongrLeft (e : ι ≃ ι') :
    (PiLp p fun _ : ι => E) ≃ₗᵢ[𝕜] PiLp p fun _ : ι' => E where
  toLinearEquiv := (WithLp.linearEquiv p 𝕜 (ι → E)).trans
    ((LinearEquiv.piCongrLeft' 𝕜 (fun _ : ι => E) e).trans (WithLp.linearEquiv p 𝕜 (ι' → E)).symm)
  norm_map' x' := by
    rcases p.dichotomy with (rfl | h)
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
      LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e.symm := by
  ext
  simp [LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.symm]

@[simp high]
theorem _root_.LinearIsometryEquiv.piLpCongrLeft_single [DecidableEq ι] [DecidableEq ι']
    (e : ι ≃ ι') (i : ι) (v : E) :
    LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e (single p i v) = single p (e i) v := by
  ext x
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft',
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
    simp only [coe_symm_linearEquiv, LinearEquiv.trans_apply, coe_linearEquiv]
    obtain rfl | hp := p.dichotomy
    · simp_rw [PiLp.norm_toLp, Pi.norm_def, LinearEquiv.piCongrRight_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.nnnorm_map]
    · have : 0 < p.toReal := zero_lt_one.trans_le <| by norm_cast
      simp only [PiLp.norm_eq_sum this, LinearEquiv.piCongrRight_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.norm_map, one_div]

@[simp]
theorem _root_.LinearIsometryEquiv.piLpCongrRight_apply (e : ∀ i, α i ≃ₗᵢ[𝕜] β i) (x : PiLp p α) :
    LinearIsometryEquiv.piLpCongrRight p e x = toLp p fun i => e i (x i) := rfl

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
    LinearIsometryEquiv.piLpCongrRight p e (single p i v) = single p i (e _ v) :=
  PiLp.ext <| Pi.apply_single (e ·) (fun _ => map_zero _) _ _

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
  norm_map' := (WithLp.linearEquiv p 𝕜 _).symm.surjective.forall.2 fun x => by
    simp_rw [← coe_nnnorm, NNReal.coe_inj]
    dsimp only [WithLp.linearEquiv_symm_apply]
    obtain rfl | hp := eq_or_ne p ⊤
    · simp_rw [← PiLp.nnnorm_ofLp, Pi.nnnorm_def, ← PiLp.nnnorm_ofLp, Pi.nnnorm_def]
      dsimp [Sigma.curry]
      rw [← Finset.univ_sigma_univ, Finset.sup_sigma]
    · have : 0 < p.toReal := (toReal_pos_iff_ne_top _).mpr hp
      simp_rw [PiLp.nnnorm_eq_sum hp]
      dsimp [Sigma.curry]
      simp_rw [one_div, NNReal.rpow_inv_rpow this.ne', ← Finset.univ_sigma_univ, Finset.sum_sigma]

@[simp] theorem _root_.LinearIsometryEquiv.piLpCurry_apply
    (f : PiLp p (fun i : Sigma κ => α i.1 i.2)) :
    _root_.LinearIsometryEquiv.piLpCurry 𝕜 p α f =
      toLp p (fun i => (toLp p) <| Sigma.curry (ofLp f) i) :=
  rfl

@[simp] theorem _root_.LinearIsometryEquiv.piLpCurry_symm_apply
    (f : PiLp p (fun i => PiLp p (α i))) :
    (_root_.LinearIsometryEquiv.piLpCurry 𝕜 p α).symm f =
      toLp p (Sigma.uncurry fun i j => f i j) :=
  rfl

end piLpCurry

section sumPiLpEquivProdLpPiLp

variable {ι κ : Type*} (p : ℝ≥0∞) (α : ι ⊕ κ → Type*) [Fintype ι] [Fintype κ] [Fact (1 ≤ p)]
variable [∀ i, SeminormedAddCommGroup (α i)] [∀ i, Module 𝕜 (α i)]

/-- `LinearEquiv.sumPiEquivProdPi` for `PiLp`, as an isometry. -/
@[simps! +simpRhs]
def sumPiLpEquivProdLpPiLp :
    WithLp p (Π i, α i) ≃ₗᵢ[𝕜]
      WithLp p (WithLp p (Π i, α (.inl i)) × WithLp p (Π i, α (.inr i))) where
  toLinearEquiv :=
    WithLp.linearEquiv p _ _
      ≪≫ₗ LinearEquiv.sumPiEquivProdPi _ _ _ α
      ≪≫ₗ LinearEquiv.prodCongr (WithLp.linearEquiv p _ _).symm
        (WithLp.linearEquiv _ _ _).symm
      ≪≫ₗ (WithLp.linearEquiv p _ _).symm
  norm_map' := (WithLp.linearEquiv p 𝕜 _).symm.surjective.forall.2 fun x => by
    obtain rfl | hp := p.dichotomy
    · simp [← Finset.univ_disjSum_univ, Finset.sup_disjSum, Pi.norm_def]
    · have : 0 < p.toReal := by positivity
      have hpt : p ≠ ⊤ := (toReal_pos_iff_ne_top p).mp this
      simp_rw [← coe_nnnorm]; congr 1 -- convert to nnnorm to avoid needing positivity arguments
      simp [nnnorm_eq_sum hpt, WithLp.prod_nnnorm_eq_add hpt, NNReal.rpow_inv_rpow this.ne']

end sumPiLpEquivProdLpPiLp

section Single

variable (p)
variable [DecidableEq ι]

@[simp]
theorem nnnorm_single (i : ι) (b : β i) : ‖single p i b‖₊ = ‖b‖₊ := by
  haveI : Nonempty ι := ⟨i⟩
  induction p generalizing hp with
  | top =>
    simp_rw [nnnorm_eq_ciSup]
    refine
      ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun j => ?_) fun n hn => ⟨i, hn.trans_eq ?_⟩
    · obtain rfl | hij := Decidable.eq_or_ne i j
      · rw [single_eq_same]
      · rw [single_eq_of_ne' _ hij, nnnorm_zero]
        exact zero_le _
    · rw [single_eq_same]
  | coe p =>
    have hp0 : (p : ℝ) ≠ 0 :=
      mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 ≤ (p : ℝ≥0∞))).ne'
    rw [nnnorm_eq_sum ENNReal.coe_ne_top, ENNReal.coe_toReal, Fintype.sum_eq_single i,
      toLp_apply, single_eq_same, ← NNReal.rpow_mul, one_div,
      mul_inv_cancel₀ hp0, NNReal.rpow_one]
    intro j hij
    rw [toLp_apply, single_eq_of_ne _ hij, nnnorm_zero, NNReal.zero_rpow hp0]

@[deprecated nnnorm_single (since := "2026-03-15")]
theorem nnnorm_toLp_single (i : ι) (b : β i) : ‖toLp p (Pi.single i b)‖₊ = ‖b‖₊ :=
  nnnorm_single p β i b

@[simp]
lemma norm_single (i : ι) (b : β i) : ‖single p i b‖ = ‖b‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_single p β i b

@[deprecated norm_single (since := "2026-03-15")]
lemma norm_toLp_single (i : ι) (b : β i) : ‖toLp p (Pi.single i b)‖ = ‖b‖ :=
  norm_single p β i b

@[simp]
lemma nndist_single_same (i : ι) (b₁ b₂ : β i) :
    nndist (single p i b₁) (single p i b₂) = nndist b₁ b₂ := by
  rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← single_sub, nnnorm_single]

@[deprecated nndist_single_same (since := "2026-03-15")]
lemma nndist_toLp_single_same (i : ι) (b₁ b₂ : β i) :
    nndist (toLp p (Pi.single i b₁)) (toLp p (Pi.single i b₂)) = nndist b₁ b₂ :=
  nndist_single_same p β i b₁ b₂

@[simp]
lemma dist_single_same (i : ι) (b₁ b₂ : β i) :
    dist (single p i b₁) (single p i b₂) = dist b₁ b₂ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nndist_single_same p β i b₁ b₂

@[deprecated dist_single_same (since := "2026-03-15")]
lemma dist_toLp_single_same (i : ι) (b₁ b₂ : β i) :
    dist (toLp p (Pi.single i b₁)) (toLp p (Pi.single i b₂)) = dist b₁ b₂ :=
  dist_single_same p β i b₁ b₂

@[simp]
lemma edist_single_same (i : ι) (b₁ b₂ : β i) :
    edist (single p i b₁) (single p i b₂) = edist b₁ b₂ := by
  simp only [edist_nndist, nndist_single_same p β i b₁ b₂]

@[deprecated edist_single_same (since := "2026-03-15")]
lemma edist_toLp_single_same (i : ι) (b₁ b₂ : β i) :
    edist (toLp p (Pi.single i b₁)) (toLp p (Pi.single i b₂)) = edist b₁ b₂ :=
  edist_single_same p β i b₁ b₂

end Single

/-- When `p = ∞`, this lemma does not hold without the additional assumption `Nonempty ι` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `‖b‖₊`. See
`PiLp.nnnorm_equiv_symm_const'` for a version which exchanges the hypothesis `p ≠ ∞` for
`Nonempty ι`. -/
lemma nnnorm_toLp_const {β} [SeminormedAddCommGroup β] (hp : p ≠ ∞) (b : β) :
    ‖toLp p (Function.const ι b)‖₊ =
      (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖b‖₊ := by
  rcases p.dichotomy with (h | h)
  · exact False.elim (hp h)
  · have ne_zero : p.toReal ≠ 0 := (zero_lt_one.trans_le h).ne'
    simp_rw [nnnorm_eq_sum hp, Function.const_apply, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, NNReal.mul_rpow, ← NNReal.rpow_mul,
      mul_one_div_cancel ne_zero, NNReal.rpow_one, ENNReal.toReal_div, ENNReal.toReal_one]

/-- When `IsEmpty ι`, this lemma does not hold without the additional assumption `p ≠ ∞` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `‖b‖₊`. See
`PiLp.nnnorm_toLp_const` for a version which exchanges the hypothesis `Nonempty ι`.
for `p ≠ ∞`. -/
lemma nnnorm_toLp_const' {β} [SeminormedAddCommGroup β] [Nonempty ι] (b : β) :
    ‖toLp p (Function.const ι b)‖₊ =
      (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖b‖₊ := by
  rcases em <| p = ∞ with (rfl | hp)
  · simp only [ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero,
      one_mul, nnnorm_eq_ciSup, Function.const_apply, ciSup_const]
  · exact nnnorm_toLp_const hp b

/-- When `p = ∞`, this lemma does not hold without the additional assumption `Nonempty ι` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `‖b‖₊`. See
`PiLp.norm_toLp_const'` for a version which exchanges the hypothesis `p ≠ ∞` for
`Nonempty ι`. -/
lemma norm_toLp_const {β} [SeminormedAddCommGroup β] (hp : p ≠ ∞) (b : β) :
    ‖toLp p (Function.const ι b)‖ =
      (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖b‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_toLp_const hp b).trans <| by simp

/-- When `IsEmpty ι`, this lemma does not hold without the additional assumption `p ≠ ∞` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `‖b‖₊`. See
`PiLp.norm_equiv_symm_const` for a version which exchanges the hypothesis `Nonempty ι`.
for `p ≠ ∞`. -/
lemma norm_toLp_const' {β} [SeminormedAddCommGroup β] [Nonempty ι] (b : β) :
    ‖toLp p (Function.const ι b)‖ =
      (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖b‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_toLp_const' b).trans <| by simp

lemma nnnorm_toLp_one {β} [SeminormedAddCommGroup β] (hp : p ≠ ∞) [One β] :
    ‖toLp p (1 : ι → β)‖₊ = (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖(1 : β)‖₊ :=
  (nnnorm_toLp_const hp (1 : β)).trans rfl

lemma norm_toLp_one {β} [SeminormedAddCommGroup β] (hp : p ≠ ∞) [One β] :
    ‖toLp p (1 : ι → β)‖ = (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖(1 : β)‖ :=
  (norm_toLp_const hp (1 : β)).trans rfl

end Fintype

section

variable [Semiring 𝕜] [∀ i, SeminormedAddCommGroup (β i)] [∀ i, Module 𝕜 (β i)]

/-- `WithLp.linearEquiv` as a continuous linear equivalence. -/
@[simps! apply symm_apply]
def continuousLinearEquiv : PiLp p β ≃L[𝕜] ∀ i, β i where
  toLinearEquiv := WithLp.linearEquiv _ _ _
  continuous_toFun := continuous_ofLp _ _
  continuous_invFun := continuous_toLp p _

lemma coe_continuousLinearEquiv :
    ⇑(PiLp.continuousLinearEquiv p 𝕜 β) = ofLp := rfl

lemma coe_symm_continuousLinearEquiv :
    ⇑(PiLp.continuousLinearEquiv p 𝕜 β).symm = toLp p := rfl

variable {𝕜} in
/-- The projection on the `i`-th coordinate of `PiLp p β`, as a continuous linear map. -/
@[simps!]
def proj (i : ι) : PiLp p β →L[𝕜] β i where
  __ := projₗ p β i
  cont := PiLp.continuous_apply ..

end

section Basis

variable [Finite ι] [Ring 𝕜]
variable (ι)

/-- A version of `Pi.basisFun` for `PiLp`. -/
def basisFun : Basis ι 𝕜 (PiLp p fun _ : ι => 𝕜) :=
  Basis.ofEquivFun (WithLp.linearEquiv p 𝕜 (ι → 𝕜))

@[simp]
theorem basisFun_apply [DecidableEq ι] (i) :
    basisFun p 𝕜 ι i = single p i 1 := by
  simp_rw [basisFun, Basis.coe_ofEquivFun, WithLp.coe_symm_linearEquiv, toLp_single]

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
    (basisFun p 𝕜 ι).map (WithLp.linearEquiv p 𝕜 (ι → 𝕜)) = Pi.basisFun 𝕜 ι := rfl

end Basis

open Matrix

nonrec theorem basis_toMatrix_basisFun_mul [Fintype ι]
    {𝕜} [SeminormedCommRing 𝕜] (b : Basis ι 𝕜 (PiLp p fun _ : ι => 𝕜))
    (A : Matrix ι ι 𝕜) :
    b.toMatrix (PiLp.basisFun _ _ _) * A =
      Matrix.of fun i j => b.repr (toLp p (Aᵀ j)) i := by
  have := basis_toMatrix_basisFun_mul (b.map (WithLp.linearEquiv _ 𝕜 _)) A
  simp_rw [← PiLp.basisFun_map p, Basis.map_repr, LinearEquiv.trans_apply,
    WithLp.linearEquiv_symm_apply, Basis.toMatrix_map, Function.comp_def, Basis.map_apply,
    LinearEquiv.symm_apply_apply] at this
  exact this

section toPi

/-!
### `L^p` distance on a product space

In this section we define a pseudometric space structure on `Π i, α i`, as well as a seminormed
group structure. These are meant to be used to put the desired instances on type synonyms
of `Π i, α i`. See for instance `Matrix.frobeniusSeminormedAddCommGroup`.
-/

-- This prevents Lean from elaborating terms of `Π i, α i` with an unintended norm.
attribute [-instance] Pi.seminormedAddGroup

variable [Fact (1 ≤ p)] [Fintype ι]

/-- This definition allows to endow `Π i, α i` with the Lp distance with the uniformity and
bornology being defeq to the product ones. It is useful to endow a type synonym of `Π i, α i` with
the Lp distance. -/
abbrev pseudoMetricSpaceToPi [∀ i, PseudoMetricSpace (α i)] :
    PseudoMetricSpace (Π i, α i) :=
  (isUniformInducing_toLp p α).comapPseudoMetricSpace.replaceBornology
    fun s => Filter.ext_iff.1
      (le_antisymm (antilipschitzWith_toLp p α).tendsto_cobounded.le_comap
        (lipschitzWith_toLp p α).comap_cobounded_le) sᶜ

lemma dist_pseudoMetricSpaceToPi [∀ i, PseudoMetricSpace (α i)] (x y : Π i, α i) :
    @dist _ (pseudoMetricSpaceToPi p α).toDist x y = dist (toLp p x) (toLp p y) := rfl

/-- This definition allows to endow `Π i, α i` with the Lp norm with the uniformity and bornology
being defeq to the product ones. It is useful to endow a type synonym of `Π i, α i` with the
Lp norm. -/
abbrev seminormedAddCommGroupToPi [∀ i, SeminormedAddCommGroup (α i)] :
    SeminormedAddCommGroup (Π i, α i) where
  norm x := ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToPi p α
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToPi, SeminormedAddCommGroup.dist_eq, toLp_add, toLp_neg]

lemma norm_seminormedAddCommGroupToPi [∀ i, SeminormedAddCommGroup (α i)] (x : Π i, α i) :
    @Norm.norm _ (seminormedAddCommGroupToPi p α).toNorm x = ‖toLp p x‖ := rfl

lemma nnnorm_seminormedAddCommGroupToPi [∀ i, SeminormedAddCommGroup (α i)] (x : Π i, α i) :
    @NNNorm.nnnorm _ (seminormedAddCommGroupToPi p α).toSeminormedAddGroup.toNNNorm x =
    ‖toLp p x‖₊ := rfl

lemma isBoundedSMulSeminormedAddCommGroupToPi
    [∀ i, SeminormedAddCommGroup (α i)] {R : Type*} [SeminormedRing R]
    [∀ i, Module R (α i)] [∀ i, IsBoundedSMul R (α i)] :
    letI := pseudoMetricSpaceToPi p α
    IsBoundedSMul R (Π i, α i) := by
  letI := pseudoMetricSpaceToPi p α
  refine ⟨fun x y z ↦ ?_, fun x y z ↦ ?_⟩
  · simpa [dist_pseudoMetricSpaceToPi] using dist_smul_pair x (toLp p y) (toLp p z)
  · simpa [dist_pseudoMetricSpaceToPi] using dist_pair_smul x y (toLp p z)

lemma normSMulClassSeminormedAddCommGroupToPi
    [∀ i, SeminormedAddCommGroup (α i)] {R : Type*} [SeminormedRing R]
    [∀ i, Module R (α i)] [∀ i, NormSMulClass R (α i)] :
    letI := seminormedAddCommGroupToPi p α
    NormSMulClass R (Π i, α i) := by
  letI := seminormedAddCommGroupToPi p α
  refine ⟨fun x y ↦ ?_⟩
  simp [norm_seminormedAddCommGroupToPi, norm_smul]

/-- This definition allows to endow `Π i, α i` with a normed space structure corresponding to
the Lp norm. It is useful for type synonyms of `Π i, α i`. -/
abbrev normedSpaceSeminormedAddCommGroupToPi
    [∀ i, SeminormedAddCommGroup (α i)] {R : Type*} [NormedField R]
    [∀ i, NormedSpace R (α i)] :
    letI := seminormedAddCommGroupToPi p α
    NormedSpace R (Π i, α i) := by
  letI := seminormedAddCommGroupToPi p α
  refine ⟨fun x y ↦ ?_⟩
  simp [norm_seminormedAddCommGroupToPi, norm_smul]

/-- This definition allows to endow `Π i, α i` with the Lp norm with the uniformity and bornology
being defeq to the product ones. It is useful to endow a type synonym of `Π i, α i` with the
Lp norm. -/
abbrev normedAddCommGroupToPi [∀ i, NormedAddCommGroup (α i)] :
    NormedAddCommGroup (Π i, α i) where
  norm x := ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToPi p α
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToPi, SeminormedAddCommGroup.dist_eq, toLp_add, toLp_neg]
  eq_of_dist_eq_zero {x y} h := by
    rw [dist_pseudoMetricSpaceToPi] at h
    apply eq_of_dist_eq_zero at h
    exact WithLp.toLp_injective p h

end toPi

end PiLp
