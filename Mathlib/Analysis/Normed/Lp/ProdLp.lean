/-
Copyright (c) 2023 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Sébastien Gouëzel, Jireh Loreaux
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Normed.Lp.WithLp

/-!
# `L^p` distance on products of two metric spaces
Given two metric spaces, one can put the max distance on their product, but there is also
a whole family of natural distances, indexed by a parameter `p : ℝ≥0∞`, that also induce
the product topology. We define them in this file. For `0 < p < ∞`, the distance on `α × β`
is given by
$$
d(x, y) = \left(d(x_1, y_1)^p + d(x_2, y_2)^p\right)^{1/p}.
$$
For `p = ∞` the distance is the supremum of the distances and `p = 0` the distance is the
cardinality of the elements that are not equal.

We give instances of this construction for emetric spaces, metric spaces, normed groups and normed
spaces.

To avoid conflicting instances, all these are defined on a copy of the original Prod-type, named
`WithLp p (α × β)`. The assumption `[Fact (1 ≤ p)]` is required for the metric and normed space
instances.

We ensure that the topology, bornology and uniform structure on `WithLp p (α × β)` are (defeq to)
the product topology, product bornology and product uniformity, to be able to use freely continuity
statements for the coordinate functions, for instance.

If you wish to endow a type synonym of `α × β` with the `L^p` distance, you can use
`pseudoMetricSpaceToProd` and the declarations below that one.


## Implementation notes

This file is a straight-forward adaptation of `Mathlib/Analysis/Normed/Lp/PiLp.lean`.

## TODO

TODO: the results about uniformity and bornology in the `Aux` section should be using the tools in
`Mathlib.Topology.MetricSpace.Bilipschitz`, so that they can be inlined in the next section and
the only remaining results are about `Lipschitz` and `Antilipschitz`.

-/

@[expose] public section

open Real Set Filter RCLike Bornology Uniformity Topology NNReal ENNReal

noncomputable section

variable (p : ℝ≥0∞) (𝕜 α β : Type*)

namespace WithLp

section algebra

/- Register simplification lemmas for the applications of `WithLp p (α × β)` elements, as the usual
lemmas for `Prod` will not trigger. -/

variable {p 𝕜 α β}
variable [Semiring 𝕜] [AddCommGroup α] [AddCommGroup β]
variable (x y : WithLp p (α × β)) (c : 𝕜)

/-- The projection on the first coordinate in `WithLp`. -/
protected def fst (x : WithLp p (α × β)) : α := (ofLp x).fst

/-- The projection on the second coordinate in `WithLp`. -/
protected def snd (x : WithLp p (α × β)) : β := (ofLp x).snd

@[simp]
theorem zero_fst : (0 : WithLp p (α × β)).fst = 0 :=
  rfl

@[simp]
theorem zero_snd : (0 : WithLp p (α × β)).snd = 0 :=
  rfl

@[simp]
theorem add_fst : (x + y).fst = x.fst + y.fst :=
  rfl

@[simp]
theorem add_snd : (x + y).snd = x.snd + y.snd :=
  rfl

@[simp]
theorem sub_fst : (x - y).fst = x.fst - y.fst :=
  rfl

@[simp]
theorem sub_snd : (x - y).snd = x.snd - y.snd :=
  rfl

@[simp]
theorem neg_fst : (-x).fst = -x.fst :=
  rfl

@[simp]
theorem neg_snd : (-x).snd = -x.snd :=
  rfl

variable [Module 𝕜 α] [Module 𝕜 β]

@[simp]
theorem smul_fst : (c • x).fst = c • x.fst :=
  rfl

@[simp]
theorem smul_snd : (c • x).snd = c • x.snd :=
  rfl

variable (p 𝕜 α β)

/-- `WithLp.fst` as a linear map. -/
@[simps]
def fstₗ : WithLp p (α × β) →ₗ[𝕜] α where
  toFun := WithLp.fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `WithLp.snd` as a linear map. -/
@[simps]
def sndₗ : WithLp p (α × β) →ₗ[𝕜] β where
  toFun := WithLp.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end algebra

/-! Note that the unapplied versions of these lemmas are deliberately omitted, as they break
the use of the type synonym. -/

section equiv

variable {p α β}

@[simp] lemma toLp_fst (x : α × β) : (toLp p x).fst = x.fst := rfl
@[simp] lemma toLp_snd (x : α × β) : (toLp p x).snd = x.snd := rfl
@[simp] lemma ofLp_fst (x : WithLp p (α × β)) : (ofLp x).fst = x.fst := rfl
@[simp] lemma ofLp_snd (x : WithLp p (α × β)) : (ofLp x).snd = x.snd := rfl

end equiv

section DistNorm

/-!
### Definition of `edist`, `dist` and `norm` on `WithLp p (α × β)`

In this section we define the `edist`, `dist` and `norm` functions on `WithLp p (α × β)` without
assuming `[Fact (1 ≤ p)]` or metric properties of the spaces `α` and `β`. This allows us to provide
the rewrite lemmas for each of three cases `p = 0`, `p = ∞` and `0 < p.toReal`.
-/


section EDist

variable [EDist α] [EDist β]

open scoped Classical in
/-- Endowing the space `WithLp p (α × β)` with the `L^p` edistance. We register this instance
separate from `WithLp.instProdPseudoEMetric` since the latter requires the type class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future emetric-like structure on `WithLp p (α × β)` for
`p < 1` satisfying a relaxed triangle inequality. The terminology for this varies throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*. -/
instance instProdEDist : EDist (WithLp p (α × β)) where
  edist f g :=
    if _hp : p = 0 then
      (if edist f.fst g.fst = 0 then 0 else 1) + (if edist f.snd g.snd = 0 then 0 else 1)
    else if p = ∞ then
      edist f.fst g.fst ⊔ edist f.snd g.snd
    else
      (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)

variable {p α β}

@[simp]
theorem prod_edist_eq_card (f g : WithLp 0 (α × β)) :
    edist f g =
      (if edist f.fst g.fst = 0 then 0 else 1) + (if edist f.snd g.snd = 0 then 0 else 1) := by
  convert if_pos rfl

theorem prod_edist_eq_add (hp : 0 < p.toReal) (f g : WithLp p (α × β)) :
    edist f g = (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

theorem prod_edist_eq_sup (f g : WithLp ∞ (α × β)) :
    edist f g = edist f.fst g.fst ⊔ edist f.snd g.snd := rfl

end EDist

section EDistProp

variable {α β}
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β]

/-- The distance from one point to itself is always zero.

This holds independent of `p` and does not require `[Fact (1 ≤ p)]`. We keep it separate
from `WithLp.instProdPseudoEMetricSpace` so it can be used also for `p < 1`. -/
theorem prod_edist_self (f : WithLp p (α × β)) : edist f f = 0 := by
  rcases p.trichotomy with (rfl | rfl | h)
  · classical
    simp
  · simp [prod_edist_eq_sup]
  · simp [prod_edist_eq_add h, ENNReal.zero_rpow_of_pos h,
      ENNReal.zero_rpow_of_pos (inv_pos.2 <| h)]

/-- The distance is symmetric.

This holds independent of `p` and does not require `[Fact (1 ≤ p)]`. We keep it separate
from `WithLp.instProdPseudoEMetricSpace` so it can be used also for `p < 1`. -/
theorem prod_edist_comm (f g : WithLp p (α × β)) : edist f g = edist g f := by
  classical
  rcases p.trichotomy with (rfl | rfl | h)
  · simp only [prod_edist_eq_card, edist_comm]
  · simp only [prod_edist_eq_sup, edist_comm]
  · simp only [prod_edist_eq_add h, edist_comm]

end EDistProp

section Dist

variable [Dist α] [Dist β]

open scoped Classical in
/-- Endowing the space `WithLp p (α × β)` with the `L^p` distance. We register this instance
separate from `WithLp.instProdPseudoMetricSpace` since the latter requires the type class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future metric-like structure on `WithLp p (α × β)` for
`p < 1` satisfying a relaxed triangle inequality. The terminology for this varies throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*. -/
instance instProdDist : Dist (WithLp p (α × β)) where
  dist f g :=
    if _hp : p = 0 then
      (if dist f.fst g.fst = 0 then 0 else 1) + (if dist f.snd g.snd = 0 then 0 else 1)
    else if p = ∞ then
      dist f.fst g.fst ⊔ dist f.snd g.snd
    else
      (dist f.fst g.fst ^ p.toReal + dist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)

variable {p α β}

theorem prod_dist_eq_card (f g : WithLp 0 (α × β)) : dist f g =
    (if dist f.fst g.fst = 0 then 0 else 1) + (if dist f.snd g.snd = 0 then 0 else 1) := by
  convert if_pos rfl

theorem prod_dist_eq_add (hp : 0 < p.toReal) (f g : WithLp p (α × β)) :
    dist f g = (dist f.fst g.fst ^ p.toReal + dist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

theorem prod_dist_eq_sup (f g : WithLp ∞ (α × β)) :
    dist f g = dist f.fst g.fst ⊔ dist f.snd g.snd := rfl

end Dist

section Norm

variable [Norm α] [Norm β]

open scoped Classical in
/-- Endowing the space `WithLp p (α × β)` with the `L^p` norm. We register this instance
separate from `WithLp.instProdSeminormedAddCommGroup` since the latter requires the type class
hypothesis `[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future norm-like structure on `WithLp p (α × β)` for
`p < 1` satisfying a relaxed triangle inequality. These are called *quasi-norms*. -/
instance instProdNorm : Norm (WithLp p (α × β)) where
  norm f :=
    if _hp : p = 0 then
      (if ‖f.fst‖ = 0 then 0 else 1) + (if ‖f.snd‖ = 0 then 0 else 1)
    else if p = ∞ then
      ‖f.fst‖ ⊔ ‖f.snd‖
    else
      (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal)

variable {p α β}

@[simp]
theorem prod_norm_eq_card (f : WithLp 0 (α × β)) :
    ‖f‖ = (if ‖f.fst‖ = 0 then 0 else 1) + (if ‖f.snd‖ = 0 then 0 else 1) := by
  convert if_pos rfl

theorem prod_norm_eq_sup (f : WithLp ∞ (α × β)) : ‖f‖ = ‖f.fst‖ ⊔ ‖f.snd‖ := rfl

theorem prod_norm_eq_add (hp : 0 < p.toReal) (f : WithLp p (α × β)) :
    ‖f‖ = (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

end Norm

end DistNorm

section Aux

/-!
### The uniformity on finite `L^p` products is the product uniformity

In this section, we put the `L^p` edistance on `WithLp p (α × β)`, and we check that the uniformity
coming from this edistance coincides with the product uniformity, by showing that the canonical
map to the Prod type (with the `L^∞` distance) is a uniform embedding, as it is both Lipschitz and
antiLipschitz.

We only register this emetric space structure as a temporary instance, as the true instance (to be
registered later) will have as uniformity exactly the product uniformity, instead of the one coming
from the edistance (which is equal to it, but not defeq). See Note [forgetful inheritance]
explaining why having definitionally the right uniformity is often important.

TODO: the results about uniformity and bornology should be using the tools in
`Mathlib.Topology.MetricSpace.Bilipschitz`, so that they can be inlined in the next section and
the only remaining results are about `Lipschitz` and `Antilipschitz`.
-/


variable [hp : Fact (1 ≤ p)]

/-- Endowing the space `WithLp p (α × β)` with the `L^p` pseudoemetric structure. This definition is
not satisfactory, as it does not register the fact that the topology and the uniform structure
coincide with the product one. Therefore, we do not register it as an instance. Using this as a
temporary pseudoemetric space instance, we will show that the uniform structure is equal (but not
defeq) to the product one, and then register an instance in which we replace the uniform structure
by the product one using this pseudoemetric space and `PseudoEMetricSpace.replaceUniformity`. -/
@[instance_reducible]
def prodPseudoEMetricAux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    PseudoEMetricSpace (WithLp p (α × β)) where
  edist_self := prod_edist_self p
  edist_comm := prod_edist_comm p
  edist_triangle f g h := by
    rcases p.dichotomy with (rfl | hp)
    · simp only [prod_edist_eq_sup]
      exact sup_le ((edist_triangle _ g.fst _).trans <| add_le_add le_sup_left le_sup_left)
        ((edist_triangle _ g.snd _).trans <| add_le_add le_sup_right le_sup_right)
    · simp only [prod_edist_eq_add (zero_lt_one.trans_le hp)]
      calc
        (edist f.fst h.fst ^ p.toReal + edist f.snd h.snd ^ p.toReal) ^ (1 / p.toReal) ≤
            ((edist f.fst g.fst + edist g.fst h.fst) ^ p.toReal +
              (edist f.snd g.snd + edist g.snd h.snd) ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr <;> apply edist_triangle
        _ ≤
            (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) +
              (edist g.fst h.fst ^ p.toReal + edist g.snd h.snd ^ p.toReal) ^ (1 / p.toReal) := by
          have := ENNReal.Lp_add_le {0, 1}
            (if · = 0 then edist f.fst g.fst else edist f.snd g.snd)
            (if · = 0 then edist g.fst h.fst else edist g.snd h.snd) hp
          simp only [Finset.mem_singleton, not_false_eq_true, Finset.sum_insert,
            Finset.sum_singleton, reduceCtorEq] at this
          exact this

attribute [local instance] WithLp.prodPseudoEMetricAux

variable {α β}

/-- An auxiliary lemma used twice in the proof of `WithLp.prodPseudoMetricAux` below. Not intended
for use outside this file. -/
theorem prod_sup_edist_ne_top_aux [PseudoMetricSpace α] [PseudoMetricSpace β]
    (f g : WithLp ∞ (α × β)) :
    edist f.fst g.fst ⊔ edist f.snd g.snd ≠ ⊤ :=
  ne_of_lt <| by simp [edist, PseudoMetricSpace.edist_dist]

variable (α β)

/-- Endowing the space `WithLp p (α × β)` with the `L^p` pseudometric structure. This definition is
not satisfactory, as it does not register the fact that the topology, the uniform structure, and the
bornology coincide with the product ones. Therefore, we do not register it as an instance. Using
this as a temporary pseudoemetric space instance, we will show that the uniform structure is equal
(but not defeq) to the product one, and then register an instance in which we replace the uniform
structure and the bornology by the product ones using this pseudometric space,
`PseudoMetricSpace.replaceUniformity`, and `PseudoMetricSpace.replaceBornology`.

See note [reducible non-instances] -/
abbrev prodPseudoMetricAux [PseudoMetricSpace α] [PseudoMetricSpace β] :
    PseudoMetricSpace (WithLp p (α × β)) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
    (fun f g => by
      rcases p.dichotomy with (rfl | h)
      · simp [prod_dist_eq_sup]
      · simp only [dist, one_div, dite_eq_ite]
        split_ifs with hp' <;> positivity)
    fun f g => by
    rcases p.dichotomy with (rfl | h)
    · refine ENNReal.eq_of_forall_le_nnreal_iff fun r ↦ ?_
      simp [prod_edist_eq_sup, prod_dist_eq_sup]
    · have : 0 < p.toReal := by rw [ENNReal.toReal_pos_iff_ne_top]; rintro rfl; norm_num at h
      simp only [prod_edist_eq_add, edist_dist, one_div, prod_dist_eq_add, this]
      rw [← ENNReal.ofReal_rpow_of_nonneg, ENNReal.ofReal_add, ← ENNReal.ofReal_rpow_of_nonneg,
        ← ENNReal.ofReal_rpow_of_nonneg] <;> simp [Real.rpow_nonneg, add_nonneg]

attribute [local instance] WithLp.prodPseudoMetricAux

variable {α β} in
private theorem edist_proj_le_edist_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    (x y : WithLp p (α × β)) :
    edist x.fst y.fst ≤ edist x y ∧ edist x.snd y.snd ≤ edist x y := by
  rcases p.dichotomy with (rfl | h)
  · simp [prod_edist_eq_sup]
  · have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (zero_lt_one.trans_le h).ne'
    rw [prod_edist_eq_add (zero_lt_one.trans_le h)]
    constructor
    · calc
        edist x.fst y.fst ≤ (edist x.fst y.fst ^ p.toReal) ^ (1 / p.toReal) := by
          simp only [← ENNReal.rpow_mul, cancel, ENNReal.rpow_one, le_refl]
        _ ≤ (edist x.fst y.fst ^ p.toReal + edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr
          simp only [self_le_add_right]
    · calc
        edist x.snd y.snd ≤ (edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) := by
          simp only [← ENNReal.rpow_mul, cancel, ENNReal.rpow_one, le_refl]
        _ ≤ (edist x.fst y.fst ^ p.toReal + edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr
          simp only [self_le_add_left]

private lemma prod_lipschitzWith_ofLp_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    LipschitzWith 1 (@ofLp p (α × β)) := by
  intro x y
  change max _ _ ≤ _
  rw [ENNReal.coe_one, one_mul, sup_le_iff]
  exact edist_proj_le_edist_aux p x y

private lemma prod_antilipschitzWith_ofLp_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    AntilipschitzWith ((2 : ℝ≥0) ^ (1 / p).toReal) (@ofLp p (α × β)) := by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simp [edist]
  · have pos : 0 < p.toReal := by positivity
    have nonneg : 0 ≤ 1 / p.toReal := by positivity
    have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (ne_of_gt pos)
    rw [prod_edist_eq_add pos, ENNReal.toReal_div 1 p]
    simp only [edist, ENNReal.toReal_one]
    calc
      (edist x.fst y.fst ^ p.toReal + edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) ≤
          (edist (ofLp x) (ofLp y) ^ p.toReal +
          edist (ofLp x) (ofLp y) ^ p.toReal) ^ (1 / p.toReal) := by
        gcongr <;> simp [edist]
      _ = (2 ^ (1 / p.toReal) : ℝ≥0) * edist (ofLp x) (ofLp y) := by
        simp only [← two_mul, ENNReal.mul_rpow_of_nonneg _ _ nonneg, ← ENNReal.rpow_mul, cancel,
          ENNReal.rpow_one, ENNReal.coe_rpow_of_nonneg _ nonneg, coe_ofNat]

private lemma isUniformInducing_ofLp_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    IsUniformInducing (@ofLp p (α × β)) :=
  (prod_antilipschitzWith_ofLp_aux p α β).isUniformInducing
    (prod_lipschitzWith_ofLp_aux p α β).uniformContinuous

set_option backward.privateInPublic true in
private lemma prod_uniformity_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    𝓤 (WithLp p (α × β)) = 𝓤[UniformSpace.comap ofLp inferInstance] := by
  rw [← (isUniformInducing_ofLp_aux p α β).comap_uniformity]
  rfl

instance instProdBornology (p : ℝ≥0∞) (α β : Type*) [Bornology α] [Bornology β] :
    Bornology (WithLp p (α × β)) := Bornology.induced ofLp

set_option backward.privateInPublic true in
private lemma prod_cobounded_aux [PseudoMetricSpace α] [PseudoMetricSpace β] :
    @cobounded _ PseudoMetricSpace.toBornology = cobounded (WithLp p (α × β)) :=
  le_antisymm (prod_antilipschitzWith_ofLp_aux p α β).tendsto_cobounded.le_comap
      (prod_lipschitzWith_ofLp_aux p α β).comap_cobounded_le

end Aux

/-! ### Instances on `L^p` products -/

section TopologicalSpace

variable [TopologicalSpace α] [TopologicalSpace β]

instance instProdTopologicalSpace : TopologicalSpace (WithLp p (α × β)) :=
  instTopologicalSpaceProd.induced ofLp

@[continuity, fun_prop]
lemma prod_continuous_toLp : Continuous (@toLp p (α × β)) :=
  continuous_induced_rng.2 continuous_id

@[continuity, fun_prop]
lemma prod_continuous_ofLp : Continuous (@ofLp p (α × β)) := continuous_induced_dom

/-- `WithLp.equiv` as a homeomorphism. -/
def homeomorphProd : WithLp p (α × β) ≃ₜ α × β where
  toEquiv := WithLp.equiv p (α × β)
  continuous_toFun := prod_continuous_ofLp p α β
  continuous_invFun := prod_continuous_toLp p α β

@[simp]
lemma toEquiv_homeomorphProd : (homeomorphProd p α β).toEquiv = WithLp.equiv p (α × β) := rfl

@[fun_prop]
protected lemma continuous_fst : Continuous (@WithLp.fst p α β) :=
  continuous_fst.comp <| prod_continuous_ofLp ..

@[fun_prop]
protected lemma continuous_snd : Continuous (@WithLp.snd p α β) :=
  continuous_snd.comp <| prod_continuous_ofLp ..

variable [T0Space α] [T0Space β]

instance instProdT0Space : T0Space (WithLp p (α × β)) :=
  (homeomorphProd p α β).symm.t0Space

variable [SecondCountableTopology α] [SecondCountableTopology β]

instance secondCountableTopology : SecondCountableTopology (WithLp p (α × β)) :=
  (homeomorphProd p α β).secondCountableTopology

end TopologicalSpace

section UniformSpace

variable [UniformSpace α] [UniformSpace β]

instance instProdUniformSpace : UniformSpace (WithLp p (α × β)) :=
  instUniformSpaceProd.comap ofLp

lemma prod_uniformContinuous_toLp : UniformContinuous (@toLp p (α × β)) :=
  uniformContinuous_comap' uniformContinuous_id

lemma prod_uniformContinuous_ofLp : UniformContinuous (@ofLp p (α × β)) :=
  uniformContinuous_comap

/-- `WithLp.equiv` as a uniform isomorphism. -/
def uniformEquivProd : WithLp p (α × β) ≃ᵤ α × β where
  toEquiv := WithLp.equiv p (α × β)
  uniformContinuous_toFun := prod_uniformContinuous_ofLp p α β
  uniformContinuous_invFun := prod_uniformContinuous_toLp p α β

@[simp]
lemma toHomeomorph_uniformEquivProd :
    (uniformEquivProd p α β).toHomeomorph = homeomorphProd p α β := rfl

@[simp]
lemma toEquiv_uniformEquivProd : (uniformEquivProd p α β).toEquiv = WithLp.equiv p (α × β) := rfl

variable [CompleteSpace α] [CompleteSpace β]

instance instProdCompleteSpace : CompleteSpace (WithLp p (α × β)) :=
  (uniformEquivProd p α β).completeSpace_iff.2 inferInstance

end UniformSpace

section ContinuousLinearEquiv

variable [TopologicalSpace α] [TopologicalSpace β]
variable [Semiring 𝕜] [AddCommGroup α] [AddCommGroup β]
variable [Module 𝕜 α] [Module 𝕜 β]

/-- `WithLp.equiv` as a continuous linear equivalence. -/
-- This is not specific to products and should be generalised!
@[simps!]
def prodContinuousLinearEquiv : WithLp p (α × β) ≃L[𝕜] α × β where
  toLinearEquiv := WithLp.linearEquiv _ _ _
  continuous_toFun := prod_continuous_ofLp p α β
  continuous_invFun := prod_continuous_toLp p α β

@[simp]
lemma prodContinuousLinearEquiv_symm_apply (x : α × β) :
    (prodContinuousLinearEquiv p 𝕜 α β).symm x = toLp p x := rfl

/-- `WithLp.fst` as a continuous linear map. -/
@[simps! coe apply]
def fstL : WithLp p (α × β) →L[𝕜] α where
  __ := fstₗ ..
  cont := WithLp.continuous_fst ..

/-- `WithLp.snd` as a continuous linear map. -/
@[simps! coe apply]
def sndL : WithLp p (α × β) →L[𝕜] β where
  __ := sndₗ ..
  cont := WithLp.continuous_snd ..

end ContinuousLinearEquiv

/-! Throughout the rest of the file, we assume `1 ≤ p`. -/
variable [hp : Fact (1 ≤ p)]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `PseudoEMetricSpace` instance on the product of two pseudoemetric spaces, using the
`L^p` pseudoedistance, and having as uniformity the product uniformity. -/
instance instProdPseudoEMetricSpace [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    PseudoEMetricSpace (WithLp p (α × β)) :=
  (prodPseudoEMetricAux p α β).replaceUniformity (prod_uniformity_aux p α β).symm

/-- `EMetricSpace` instance on the product of two emetric spaces, using the `L^p`
edistance, and having as uniformity the product uniformity. -/
instance instProdEMetricSpace [EMetricSpace α] [EMetricSpace β] : EMetricSpace (WithLp p (α × β)) :=
  EMetricSpace.ofT0PseudoEMetricSpace (WithLp p (α × β))

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `PseudoMetricSpace` instance on the product of two pseudometric spaces, using the
`L^p` distance, and having as uniformity the product uniformity. -/
instance instProdPseudoMetricSpace [PseudoMetricSpace α] [PseudoMetricSpace β] :
    PseudoMetricSpace (WithLp p (α × β)) :=
  ((prodPseudoMetricAux p α β).replaceUniformity
    (prod_uniformity_aux p α β).symm).replaceBornology
    fun s => Filter.ext_iff.1 (prod_cobounded_aux p α β).symm sᶜ

/-- `MetricSpace` instance on the product of two metric spaces, using the `L^p` distance,
and having as uniformity the product uniformity. -/
instance instProdMetricSpace [MetricSpace α] [MetricSpace β] : MetricSpace (WithLp p (α × β)) :=
  MetricSpace.ofT0PseudoMetricSpace _

variable {p α β}

theorem prod_nndist_eq_add [PseudoMetricSpace α] [PseudoMetricSpace β]
    (hp : p ≠ ∞) (x y : WithLp p (α × β)) :
    nndist x y = (nndist x.fst y.fst ^ p.toReal + nndist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) :=
  NNReal.eq <| by
    push_cast
    exact prod_dist_eq_add (p.toReal_pos_iff_ne_top.mpr hp) _ _

theorem prod_nndist_eq_sup [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp ∞ (α × β)) :
    nndist x y = nndist x.fst y.fst ⊔ nndist x.snd y.snd :=
  NNReal.eq <| by
    push_cast
    exact prod_dist_eq_sup _ _

theorem edist_fst_le [PseudoEMetricSpace α] [PseudoEMetricSpace β] (x y : WithLp p (α × β)) :
    edist x.fst y.fst ≤ edist x y :=
  (edist_proj_le_edist_aux p x y).1

theorem edist_snd_le [PseudoEMetricSpace α] [PseudoEMetricSpace β] (x y : WithLp p (α × β)) :
    edist x.snd y.snd ≤ edist x y :=
  (edist_proj_le_edist_aux p x y).2

theorem nndist_fst_le [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β)) :
    nndist x.fst y.fst ≤ nndist x y := by
  simpa [← coe_nnreal_ennreal_nndist] using edist_fst_le x y

theorem nndist_snd_le [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β)) :
    nndist x.snd y.snd ≤ nndist x y := by
  simpa [← coe_nnreal_ennreal_nndist] using edist_snd_le x y

theorem dist_fst_le [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β)) :
    dist x.fst y.fst ≤ dist x y :=
  nndist_fst_le x y

theorem dist_snd_le [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : WithLp p (α × β)) :
    dist x.snd y.snd ≤ dist x y :=
  nndist_snd_le x y

variable (p α β)

lemma prod_lipschitzWith_ofLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    LipschitzWith 1 (@ofLp p (α × β)) :=
  prod_lipschitzWith_ofLp_aux p α β

lemma prod_antilipschitzWith_toLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    AntilipschitzWith 1 (@toLp p (α × β)) :=
  (prod_lipschitzWith_ofLp p α β).to_rightInverse (ofLp_toLp p)

lemma prod_antilipschitzWith_ofLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    AntilipschitzWith ((2 : ℝ≥0) ^ (1 / p).toReal) (@ofLp p (α × β)) :=
  prod_antilipschitzWith_ofLp_aux p α β

lemma prod_lipschitzWith_toLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    LipschitzWith ((2 : ℝ≥0) ^ (1 / p).toReal) (@toLp p (α × β)) :=
  (prod_antilipschitzWith_ofLp p α β).to_rightInverse (ofLp_toLp p)

lemma prod_isometry_ofLp_infty [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    Isometry (@ofLp ∞ (α × β)) :=
  fun x y =>
  le_antisymm (by simpa only [ENNReal.coe_one, one_mul] using prod_lipschitzWith_ofLp ∞ α β x y)
    (by
      simpa only [ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero, ENNReal.coe_one,
        one_mul] using prod_antilipschitzWith_ofLp ∞ α β x y)

/-- Seminormed group instance on the product of two normed groups, using the `L^p`
norm. -/
instance instProdSeminormedAddCommGroup [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] :
    SeminormedAddCommGroup (WithLp p (α × β)) where
  dist_eq x y := by
    rcases p.dichotomy with (rfl | h)
    · simp only [prod_dist_eq_sup, prod_norm_eq_sup, dist_eq_norm, ← norm_neg_add]
      rfl
    · simp only [prod_dist_eq_add (zero_lt_one.trans_le h),
        prod_norm_eq_add (zero_lt_one.trans_le h), dist_eq_norm, ← norm_neg_add]
      rfl

lemma isUniformInducing_toLp [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    IsUniformInducing (@toLp p (α × β)) :=
  (prod_antilipschitzWith_toLp p α β).isUniformInducing
    (prod_lipschitzWith_toLp p α β).uniformContinuous

section
variable {β p}

theorem enorm_fst_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.fst‖ₑ ≤ ‖x‖ₑ := by
  simpa using edist_fst_le x 0

theorem enorm_snd_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.snd‖ₑ ≤ ‖x‖ₑ := by
  simpa using edist_snd_le x 0

theorem nnnorm_fst_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.fst‖₊ ≤ ‖x‖₊ := by
  simpa using nndist_fst_le x 0

theorem nnnorm_snd_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.snd‖₊ ≤ ‖x‖₊ := by
  simpa using nndist_snd_le x 0

theorem norm_fst_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.fst‖ ≤ ‖x‖ := by
  simpa using dist_fst_le x 0

theorem norm_snd_le [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : WithLp p (α × β)) :
    ‖x.snd‖ ≤ ‖x‖ := by
  simpa using dist_snd_le x 0

end

/-- normed group instance on the product of two normed groups, using the `L^p` norm. -/
instance instProdNormedAddCommGroup [NormedAddCommGroup α] [NormedAddCommGroup β] :
    NormedAddCommGroup (WithLp p (α × β)) :=
  { instProdSeminormedAddCommGroup p α β with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

example [NormedAddCommGroup α] [NormedAddCommGroup β] :
    (instProdNormedAddCommGroup p α β).toMetricSpace.toUniformSpace.toTopologicalSpace =
    instProdTopologicalSpace p α β :=
  rfl

example [NormedAddCommGroup α] [NormedAddCommGroup β] :
    (instProdNormedAddCommGroup p α β).toMetricSpace.toUniformSpace = instProdUniformSpace p α β :=
  rfl

example [NormedAddCommGroup α] [NormedAddCommGroup β] :
    (instProdNormedAddCommGroup p α β).toMetricSpace.toBornology = instProdBornology p α β :=
  rfl

section norm_of

variable {p α β}

theorem prod_norm_eq_of_nat [Norm α] [Norm β] (n : ℕ) (h : p = n) (f : WithLp p (α × β)) :
    ‖f‖ = (‖f.fst‖ ^ n + ‖f.snd‖ ^ n) ^ (1 / (n : ℝ)) := by
  have := p.toReal_pos_iff_ne_top.mpr (ne_of_eq_of_ne h <| ENNReal.natCast_ne_top n)
  simp only [one_div, h, Real.rpow_natCast, ENNReal.toReal_natCast,
    prod_norm_eq_add this]

variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

theorem prod_nnnorm_eq_add (hp : p ≠ ∞) (f : WithLp p (α × β)) :
    ‖f‖₊ = (‖f.fst‖₊ ^ p.toReal + ‖f.snd‖₊ ^ p.toReal) ^ (1 / p.toReal) := by
  ext
  simp [prod_norm_eq_add (p.toReal_pos_iff_ne_top.mpr hp)]

theorem prod_nnnorm_eq_sup (f : WithLp ∞ (α × β)) : ‖f‖₊ = ‖f.fst‖₊ ⊔ ‖f.snd‖₊ := by
  ext
  norm_cast

@[simp] lemma prod_nnnorm_ofLp (f : WithLp ∞ (α × β)) : ‖ofLp f‖₊ = ‖f‖₊ := by
  rw [prod_nnnorm_eq_sup, Prod.nnnorm_def, ofLp_fst, ofLp_snd]

@[simp] lemma prod_nnnorm_toLp (f : α × β) : ‖toLp ⊤ f‖₊ = ‖f‖₊ :=
  (prod_nnnorm_ofLp _).symm

@[simp] lemma prod_norm_ofLp (f : WithLp ∞ (α × β)) : ‖ofLp f‖ = ‖f‖ :=
  congr_arg NNReal.toReal <| prod_nnnorm_ofLp f

@[simp] lemma prod_norm_toLp (f : α × β) : ‖toLp ⊤ f‖ = ‖f‖ :=
  (prod_norm_ofLp _).symm

section L1

theorem prod_norm_eq_of_L1 (x : WithLp 1 (α × β)) :
    ‖x‖ = ‖x.fst‖ + ‖x.snd‖ := by
  simp [prod_norm_eq_add]

theorem prod_nnnorm_eq_of_L1 (x : WithLp 1 (α × β)) :
    ‖x‖₊ = ‖x.fst‖₊ + ‖x.snd‖₊ :=
  NNReal.eq <| by
    push_cast
    exact prod_norm_eq_of_L1 x

theorem prod_dist_eq_of_L1 (x y : WithLp 1 (α × β)) :
    dist x y = dist x.fst y.fst + dist x.snd y.snd := by
  simp_rw [dist_eq_norm, prod_norm_eq_of_L1, sub_fst, sub_snd]

theorem prod_nndist_eq_of_L1 (x y : WithLp 1 (α × β)) :
    nndist x y = nndist x.fst y.fst + nndist x.snd y.snd :=
  NNReal.eq <| by
    push_cast
    exact prod_dist_eq_of_L1 _ _

theorem prod_edist_eq_of_L1 (x y : WithLp 1 (α × β)) :
    edist x y = edist x.fst y.fst + edist x.snd y.snd := by
  simp [prod_edist_eq_add]

end L1

section L2

theorem prod_norm_eq_of_L2 (x : WithLp 2 (α × β)) :
    ‖x‖ = √(‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2) := by
  rw [prod_norm_eq_of_nat 2 (by norm_cast) _, Real.sqrt_eq_rpow]
  norm_cast

theorem prod_nnnorm_eq_of_L2 (x : WithLp 2 (α × β)) :
    ‖x‖₊ = NNReal.sqrt (‖x.fst‖₊ ^ 2 + ‖x.snd‖₊ ^ 2) :=
  NNReal.eq <| by
    push_cast
    exact prod_norm_eq_of_L2 x

theorem prod_norm_sq_eq_of_L2 (x : WithLp 2 (α × β)) : ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 := by
  suffices ‖x‖₊ ^ 2 = ‖x.fst‖₊ ^ 2 + ‖x.snd‖₊ ^ 2 by
    simpa only [NNReal.coe_sum] using congr_arg ((↑) : ℝ≥0 → ℝ) this
  rw [prod_nnnorm_eq_of_L2, NNReal.sq_sqrt]

theorem prod_dist_eq_of_L2 (x y : WithLp 2 (α × β)) :
    dist x y = √(dist x.fst y.fst ^ 2 + dist x.snd y.snd ^ 2) := by
  simp_rw [dist_eq_norm, prod_norm_eq_of_L2, sub_fst, sub_snd]

theorem prod_nndist_eq_of_L2 (x y : WithLp 2 (α × β)) :
    nndist x y = NNReal.sqrt (nndist x.fst y.fst ^ 2 + nndist x.snd y.snd ^ 2) :=
  NNReal.eq <| by
    push_cast
    exact prod_dist_eq_of_L2 _ _

theorem prod_edist_eq_of_L2 (x y : WithLp 2 (α × β)) :
    edist x y = (edist x.fst y.fst ^ 2 + edist x.snd y.snd ^ 2) ^ (1 / 2 : ℝ) := by
  simp [prod_edist_eq_add]

end L2

end norm_of

variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

section Single

@[simp] lemma nnnorm_toLp_inl (x : α) : ‖toLp p (x, (0 : β))‖₊ = ‖x‖₊ := by
  induction p generalizing hp with
  | top =>
    simp [prod_nnnorm_eq_sup]
  | coe p =>
    have hp0 : (p : ℝ) ≠ 0 := mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 ≤ (p : ℝ≥0∞))).ne'
    simp [prod_nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel₀ hp0]

@[simp] lemma nnnorm_toLp_inr (y : β) : ‖toLp p ((0 : α), y)‖₊ = ‖y‖₊ := by
  induction p generalizing hp with
  | top =>
    simp [prod_nnnorm_eq_sup]
  | coe p =>
    have hp0 : (p : ℝ) ≠ 0 := mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 ≤ (p : ℝ≥0∞))).ne'
    simp [prod_nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel₀ hp0]

@[simp]
lemma norm_toLp_fst (x : α) : ‖toLp p (x, (0 : β))‖ = ‖x‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_toLp_inl p α β x

@[simp]
lemma norm_toLp_snd (y : β) : ‖toLp p ((0 : α), y)‖ = ‖y‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_toLp_inr p α β y

@[simp]
lemma nndist_toLp_fst (x₁ x₂ : α) :
    nndist (toLp p (x₁, (0 : β))) (toLp p (x₂, 0)) = nndist x₁ x₂ := by
  rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← toLp_sub, Prod.mk_sub_mk, sub_zero,
    nnnorm_toLp_inl]

@[simp]
lemma nndist_toLp_snd (y₁ y₂ : β) :
    nndist (toLp p ((0 : α), y₁)) (toLp p (0, y₂)) = nndist y₁ y₂ := by
  rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← toLp_sub, Prod.mk_sub_mk, sub_zero,
    nnnorm_toLp_inr]

@[simp]
lemma dist_toLp_fst (x₁ x₂ : α) : dist (toLp p (x₁, (0 : β))) (toLp p (x₂, 0)) = dist x₁ x₂ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nndist_toLp_fst p α β x₁ x₂

@[simp]
lemma dist_toLp_snd (y₁ y₂ : β) :
    dist (toLp p ((0 : α), y₁)) (toLp p (0, y₂)) = dist y₁ y₂ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nndist_toLp_snd p α β y₁ y₂

@[simp]
lemma edist_toLp_fst (x₁ x₂ : α) : edist (toLp p (x₁, (0 : β))) (toLp p (x₂, 0)) = edist x₁ x₂ := by
  simp only [edist_nndist, nndist_toLp_fst p α β x₁ x₂]

@[simp]
lemma edist_toLp_snd (y₁ y₂ : β) :
    edist (toLp p ((0 : α), y₁)) (toLp p (0, y₂)) = edist y₁ y₂ := by
  simp only [edist_nndist, nndist_toLp_snd p α β y₁ y₂]

end Single

section IsBoundedSMul
variable [SeminormedRing 𝕜] [Module 𝕜 α] [Module 𝕜 β] [IsBoundedSMul 𝕜 α] [IsBoundedSMul 𝕜 β]

instance instProdIsBoundedSMul : IsBoundedSMul 𝕜 (WithLp p (α × β)) :=
  .of_nnnorm_smul_le fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · simp only [← prod_nnnorm_ofLp, ofLp_smul]
      exact norm_smul_le _ _
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p ≠ ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [prod_nnnorm_eq_add hpt, prod_nnnorm_eq_add hpt, one_div, NNReal.rpow_inv_le_iff hp0,
        NNReal.mul_rpow, ← NNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', NNReal.rpow_one, mul_add,
        ← NNReal.mul_rpow, ← NNReal.mul_rpow]
      exact add_le_add
        (NNReal.rpow_le_rpow (nnnorm_smul_le _ _) hp0.le)
        (NNReal.rpow_le_rpow (nnnorm_smul_le _ _) hp0.le)

variable {𝕜 p α β}

/-- The canonical map `WithLp.equiv` between `WithLp ∞ (α × β)` and `α × β` as a linear isometric
equivalence. -/
def prodEquivₗᵢ : WithLp ∞ (α × β) ≃ₗᵢ[𝕜] α × β where
  __ := WithLp.equiv ∞ _
  map_add' _f _g := rfl
  map_smul' _c _f := rfl
  norm_map' x := prod_norm_toLp (ofLp x)


end IsBoundedSMul

instance instProdNormSMulClass [SeminormedRing 𝕜] [Module 𝕜 α] [Module 𝕜 β]
    [NormSMulClass 𝕜 α] [NormSMulClass 𝕜 β] : NormSMulClass 𝕜 (WithLp p (α × β)) :=
  .of_nnnorm_smul fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · simp only [← prod_nnnorm_ofLp, WithLp.ofLp_smul, nnnorm_smul]
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p ≠ ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [prod_nnnorm_eq_add hpt, prod_nnnorm_eq_add hpt, one_div, NNReal.rpow_inv_eq_iff hp0.ne',
        NNReal.mul_rpow, ← NNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', NNReal.rpow_one, mul_add,
        ← NNReal.mul_rpow, ← NNReal.mul_rpow, smul_fst, smul_snd, nnnorm_smul, nnnorm_smul]

section SeminormedAddCommGroup

open ENNReal

variable {p : ℝ≥0∞} {α β}

/-- Projection on `WithLp p (α × β)` with range `α` and kernel `β` -/
def idemFst : AddMonoid.End (WithLp p (α × β)) where
  toFun x := toLp p (x.fst, 0)
  map_zero' := by simp
  map_add' := by simp [← toLp_add]

/-- Projection on `WithLp p (α × β)` with range `β` and kernel `α` -/
def idemSnd : AddMonoid.End (WithLp p (α × β)) where
  toFun x := toLp p (0, x.snd)
  map_zero' := by simp
  map_add' := by simp [← toLp_add]

lemma idemFst_apply (x : WithLp p (α × β)) : idemFst x = toLp p (x.fst, 0) := rfl

lemma idemSnd_apply (x : WithLp p (α × β)) : idemSnd x = toLp p (0, x.snd) := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma idemFst_add_idemSnd :
    idemFst + idemSnd = (1 : AddMonoid.End (WithLp p (α × β))) := AddMonoidHom.ext
  fun x => by
    rw [AddMonoidHom.add_apply, idemFst_apply, idemSnd_apply, AddMonoid.End.coe_one, id_eq,
      ← toLp_add, Prod.mk_add_mk, zero_add, add_zero]
    rfl

lemma idemFst_compl : (1 : AddMonoid.End (WithLp p (α × β))) - idemFst = idemSnd := by
  rw [← idemFst_add_idemSnd, add_sub_cancel_left]

lemma idemSnd_compl : (1 : AddMonoid.End (WithLp p (α × β))) - idemSnd = idemFst := by
  rw [← idemFst_add_idemSnd, add_sub_cancel_right]

theorem prod_norm_eq_idemFst_sup_idemSnd (x : WithLp ∞ (α × β)) :
    ‖x‖ = max ‖idemFst x‖ ‖idemSnd x‖ := by
  rw [WithLp.prod_norm_eq_sup, ← WithLp.norm_toLp_fst ∞ α β x.fst,
    ← WithLp.norm_toLp_snd ∞ α β x.snd]
  rfl

lemma prod_norm_eq_add_idemFst [Fact (1 ≤ p)] (hp : 0 < p.toReal) (x : WithLp p (α × β)) :
    ‖x‖ = (‖idemFst x‖ ^ p.toReal + ‖idemSnd x‖ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [WithLp.prod_norm_eq_add hp, ← WithLp.norm_toLp_fst p α β x.fst,
    ← WithLp.norm_toLp_snd p α β x.snd]
  rfl

lemma prod_norm_eq_idemFst_of_L1 (x : WithLp 1 (α × β)) : ‖x‖ = ‖idemFst x‖ + ‖idemSnd x‖ := by
  rw [prod_norm_eq_add_idemFst (lt_of_lt_of_eq zero_lt_one toReal_one.symm)]
  simp only [toReal_one, Real.rpow_one, ne_eq, one_ne_zero, not_false_eq_true, div_self]

end SeminormedAddCommGroup

section NormedSpace

/-- The product of two normed spaces is a normed space, with the `L^p` norm. -/
instance instProdNormedSpace [NormedField 𝕜] [NormedSpace 𝕜 α] [NormedSpace 𝕜 β] :
    NormedSpace 𝕜 (WithLp p (α × β)) where
  norm_smul_le := norm_smul_le

end NormedSpace

section toProd

/-!
### `L^p` distance on a product space

In this section we define a pseudometric space structure on `α × β`, as well as a seminormed
group structure. These are meant to be used to put the desired instances on type synonyms
of `α × β`. See for instance `TrivSqZeroExt.instL1SeminormedAddCommGroup`.
-/

variable (α β : Type*)

-- This prevents Lean from elaborating terms of `α × β` with an unintended norm.
attribute [-instance] Prod.toNorm

/-- This definition allows to endow `α × β` with the Lp distance with the uniformity and bornology
being defeq to the product ones. It is useful to endow a type synonym of `a × β` with the
Lp distance. -/
abbrev pseudoMetricSpaceToProd [PseudoMetricSpace α] [PseudoMetricSpace β] :
    PseudoMetricSpace (α × β) :=
  (isUniformInducing_toLp p α β).comapPseudoMetricSpace.replaceBornology
    fun s => Filter.ext_iff.1
      (le_antisymm (prod_antilipschitzWith_toLp p α β).tendsto_cobounded.le_comap
        (prod_lipschitzWith_toLp p α β).comap_cobounded_le) sᶜ

lemma dist_pseudoMetricSpaceToProd [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : α × β) :
    @dist _ (pseudoMetricSpaceToProd p α β).toDist x y = dist (toLp p x) (toLp p y) := rfl

/-- This definition allows to endow `α × β` with the Lp norm with the uniformity and bornology
being defeq to the product ones. It is useful to endow a type synonym of `a × β` with the
Lp norm. -/
abbrev seminormedAddCommGroupToProd [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] :
    SeminormedAddCommGroup (α × β) where
  norm x := ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToProd p α β
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToProd, SeminormedAddCommGroup.dist_eq, toLp_add, toLp_neg]

lemma norm_seminormedAddCommGroupToProd [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
    (x : α × β) :
    @Norm.norm _ (seminormedAddCommGroupToProd p α β).toNorm x = ‖toLp p x‖ := rfl

lemma nnnorm_seminormedAddCommGroupToProd [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
    (x : α × β) :
    @NNNorm.nnnorm _ (seminormedAddCommGroupToProd p α β).toSeminormedAddGroup.toNNNorm x =
    ‖toLp p x‖₊ := rfl

lemma isBoundedSMulSeminormedAddCommGroupToProd
    [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] {R : Type*} [SeminormedRing R]
    [Module R α] [Module R β] [IsBoundedSMul R α] [IsBoundedSMul R β] :
    letI := pseudoMetricSpaceToProd p α β
    IsBoundedSMul R (α × β) := by
  letI := pseudoMetricSpaceToProd p α β
  refine ⟨fun x y z ↦ ?_, fun x y z ↦ ?_⟩
  · simpa [dist_pseudoMetricSpaceToProd] using dist_smul_pair x (toLp p y) (toLp p z)
  · simpa [dist_pseudoMetricSpaceToProd] using dist_pair_smul x y (toLp p z)

lemma normSMulClassSeminormedAddCommGroupToProd
    [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] {R : Type*} [SeminormedRing R]
    [Module R α] [Module R β] [NormSMulClass R α] [NormSMulClass R β] :
    letI := seminormedAddCommGroupToProd p α β
    NormSMulClass R (α × β) := by
  letI := seminormedAddCommGroupToProd p α β
  exact ⟨fun x y ↦ norm_smul x (toLp p y)⟩

/-- This definition allows to endow `α × β` with a normed space structure corresponding to
the Lp norm. It is useful for type synonyms of `α × β`. -/
abbrev normedSpaceSeminormedAddCommGroupToProd
    [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] {R : Type*} [NormedField R]
    [NormedSpace R α] [NormedSpace R β] :
    letI := seminormedAddCommGroupToProd p α β
    NormedSpace R (α × β) := by
  letI := seminormedAddCommGroupToProd p α β
  exact ⟨fun x y ↦ norm_smul_le x (toLp p y)⟩

/-- This definition allows to endow `α × β` with the Lp norm with the uniformity and bornology
being defeq to the product ones. It is useful to endow a type synonym of `α × β` with the
Lp norm. -/
abbrev normedAddCommGroupToProd [NormedAddCommGroup α] [NormedAddCommGroup β] :
    NormedAddCommGroup (α × β) where
  norm x := ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToProd p α β
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToProd, SeminormedAddCommGroup.dist_eq, toLp_add, toLp_neg]
  eq_of_dist_eq_zero {x y} h := by
    rw [dist_pseudoMetricSpaceToProd] at h
    exact toLp_injective p (eq_of_dist_eq_zero h)

end toProd

end WithLp

variable (γ : Type*) {α' β' : Type*}

section Isometry

variable [hp : Fact (1 ≤ p)] [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
  [PseudoEMetricSpace α'] [PseudoEMetricSpace β']

variable {α β} in
/-- The `L^p` product of two isometries is an isometry. -/
theorem Isometry.withLpProdMap {f : α → α'} (hf : Isometry f) {g : β → β'} (hg : Isometry g) :
    Isometry (WithLp.map p (Prod.map f g)) := by
  intro _ _
  rcases p.trichotomy with rfl | rfl | hp
  · absurd hp.elim; simp
  · simp [WithLp.prod_edist_eq_sup, hf.edist_eq, hg.edist_eq]
  · simp [WithLp.prod_edist_eq_add hp, hf.edist_eq, hg.edist_eq]

namespace IsometryEquiv

variable {α β} in
/-- The `L^p` product of two isometric equivalences. -/
@[simps! apply symm_apply]
def withLpProdCongr (f : α ≃ᵢ α') (g : β ≃ᵢ β') : WithLp p (α × β) ≃ᵢ WithLp p (α' × β') where
  __ := WithLp.congr p (f.toEquiv.prodCongr g.toEquiv)
  isometry_toFun := f.isometry.withLpProdMap p g.isometry

/-- Commutativity of the `L^p` product as an isometric equivalence. -/
def withLpProdComm : WithLp p (α × β) ≃ᵢ WithLp p (β × α) where
  __ := WithLp.congr p (Equiv.prodComm α β)
  isometry_toFun _ _ := by
    rcases p.trichotomy with rfl | rfl | hp
    · absurd hp.elim; simp
    · simp [WithLp.prod_edist_eq_sup, max_comm]
    · simp [WithLp.prod_edist_eq_add hp, add_comm]

@[simp]
theorem withLpProdComm_apply (x : WithLp p (α × β)) :
    withLpProdComm p α β x = .toLp p (x.snd, x.fst) :=
  rfl

@[simp]
theorem withLpProdComm_symm : (withLpProdComm p α β).symm = withLpProdComm p β α :=
  rfl

/-- Associativity of the `L^p` product as an isometric equivalence. -/
@[simps apply symm_apply]
def withLpProdAssoc : WithLp p (WithLp p (α × β) × γ) ≃ᵢ WithLp p (α × WithLp p (β × γ)) where
  toFun x := .toLp p (x.fst.fst, .toLp p (x.fst.snd, x.snd))
  invFun x := .toLp p (.toLp p (x.fst, x.snd.fst), x.snd.snd)
  isometry_toFun _ _ := by
    rcases p.trichotomy with rfl | rfl | hp
    · absurd hp.elim; simp
    · simp [WithLp.prod_edist_eq_sup, max_assoc]
    · simp [WithLp.prod_edist_eq_add hp, ENNReal.rpow_inv_rpow hp.ne', add_assoc]

/-- Right identity of the `L^p` product as an isometric equivalence. -/
@[simps! apply symm_apply]
def withLpProdUnique [Unique β] : WithLp p (α × β) ≃ᵢ α where
  __ := (WithLp.equiv _ _).trans (Equiv.prodUnique _ _)
  isometry_toFun x y : edist x.fst y.fst = edist x y := by
    rcases p.trichotomy with rfl | rfl | hp
    · absurd hp.elim; simp
    · simp_rw [WithLp.prod_edist_eq_sup, Unique.eq_default, edist_self, max_zero_right]
    · simp_rw [WithLp.prod_edist_eq_add hp, Unique.eq_default, edist_self,
        ENNReal.zero_rpow_of_pos hp, add_zero, one_div, ENNReal.rpow_rpow_inv hp.ne']

theorem coe_withLpProdUnique [Unique β] : ⇑(withLpProdUnique p α β) = WithLp.fst :=
  rfl

/-- Left identity of the `L^p` product as an isometric equivalence. -/
@[simps! apply symm_apply]
def withLpUniqueProd [Unique α] : WithLp p (α × β) ≃ᵢ β :=
  (withLpProdComm p α β).trans (withLpProdUnique p β α)

theorem coe_withLpUniqueProd [Unique α] : ⇑(withLpUniqueProd p α β) = WithLp.snd :=
  rfl

end IsometryEquiv

end Isometry

section Linear

variable [hp : Fact (1 ≤ p)] [Semiring 𝕜]
  [SeminormedAddCommGroup α] [Module 𝕜 α]
  [SeminormedAddCommGroup β] [Module 𝕜 β]
  [SeminormedAddCommGroup γ] [Module 𝕜 γ]
  [SeminormedAddCommGroup α'] [Module 𝕜 α']
  [SeminormedAddCommGroup β'] [Module 𝕜 β']

variable {𝕜 α β} in
/-- The `L^p` product of two linear isometries. -/
@[simps! apply]
def LinearIsometry.withLpProdMap (f : α →ₗᵢ[𝕜] α') (g : β →ₗᵢ[𝕜] β') :
    WithLp p (α × β) →ₗᵢ[𝕜] WithLp p (α' × β') where
  __ := (f.toLinearMap.prodMap g.toLinearMap).withLpMap p
  norm_map' := (f.isometry.withLpProdMap p g.isometry).norm_map_of_map_zero
    ((f.toLinearMap.prodMap g.toLinearMap).withLpMap p).map_zero

namespace LinearIsometryEquiv

variable {𝕜 α β} in
/-- The `L^p` product of two linear isometric equivalences. -/
@[simps! apply symm_apply]
def withLpProdCongr (f : α ≃ₗᵢ[𝕜] α') (g : β ≃ₗᵢ[𝕜] β') :
    WithLp p (α × β) ≃ₗᵢ[𝕜] WithLp p (α' × β') where
  __ := (f.toLinearEquiv.prodCongr g.toLinearEquiv).withLpCongr p
  norm_map' := (f.toLinearIsometry.withLpProdMap p g.toLinearIsometry).norm_map

@[deprecated (since := "2025-12-22")] alias _root_.LinearIsometry.withLpProdCongr := withLpProdCongr

/-- Commutativity of the `L^p` product as a linear isometric equivalence. -/
def withLpProdComm : WithLp p (α × β) ≃ₗᵢ[𝕜] WithLp p (β × α) where
  __ := (LinearEquiv.prodComm 𝕜 α β).withLpCongr p
  norm_map' := (IsometryEquiv.withLpProdComm p α β).isometry.norm_map_of_map_zero rfl

@[simp]
theorem withLpProdComm_apply (x : WithLp p (α × β)) :
    withLpProdComm p 𝕜 α β x = WithLp.toLp p (x.snd, x.fst) :=
  rfl

@[simp]
theorem withLpProdComm_symm : (withLpProdComm p 𝕜 α β).symm = withLpProdComm p 𝕜 β α :=
  rfl

/-- Associativity of the `L^p` product as a linear isometric equivalence. -/
@[simps! apply symm_apply]
def withLpProdAssoc : WithLp p (WithLp p (α × β) × γ) ≃ₗᵢ[𝕜] WithLp p (α × WithLp p (β × γ)) where
  __ := (IsometryEquiv.withLpProdAssoc p α β γ).toEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := (IsometryEquiv.withLpProdAssoc p α β γ).isometry.norm_map_of_map_zero rfl

/-- Right identity of the `L^p` product as a linear isometric equivalence. -/
@[simps! apply symm_apply]
def withLpProdUnique [Unique β] : WithLp p (α × β) ≃ₗᵢ[𝕜] α where
  __ := (WithLp.linearEquiv _ _ _).trans LinearEquiv.prodUnique
  norm_map' := (IsometryEquiv.withLpProdUnique _ _ _).isometry.norm_map_of_map_zero rfl

theorem coe_withLpProdUnique [Unique β] : ⇑(withLpProdUnique p 𝕜 α β) = WithLp.fst :=
  rfl

/-- Left identity of the `L^p` product as a linear isometric equivalence. -/
@[simps! apply symm_apply]
def withLpUniqueProd [Unique α] : WithLp p (α × β) ≃ₗᵢ[𝕜] β :=
  (withLpProdComm p 𝕜 α β).trans (withLpProdUnique p 𝕜 β α)

theorem coe_withLpUniqueProd [Unique α] : ⇑(withLpUniqueProd p 𝕜 α β) = WithLp.snd :=
  rfl

end LinearIsometryEquiv

end Linear
