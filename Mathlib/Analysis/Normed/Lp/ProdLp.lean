/-
Copyright (c) 2023 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Sébastien Gouëzel, Jireh Loreaux
-/

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Lp.WithLp

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

# Implementation notes

This file is a straight-forward adaptation of `Mathlib.Analysis.Normed.Lp.PiLp`.

-/

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

end algebra

/-! Note that the unapplied versions of these lemmas are deliberately omitted, as they break
the use of the type synonym. -/

section equiv

variable {p α β}

@[simp]
theorem equiv_fst (x : WithLp p (α × β)) : (WithLp.equiv p (α × β) x).fst = x.fst :=
  rfl

@[simp]
theorem equiv_snd (x : WithLp p (α × β)) : (WithLp.equiv p (α × β) x).snd = x.snd :=
  rfl

@[simp]
theorem equiv_symm_fst (x : α × β) : ((WithLp.equiv p (α × β)).symm x).fst = x.fst :=
  rfl

@[simp]
theorem equiv_symm_snd (x : α × β) : ((WithLp.equiv p (α × β)).symm x).snd = x.snd :=
  rfl

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
-/


variable [hp : Fact (1 ≤ p)]

/-- Endowing the space `WithLp p (α × β)` with the `L^p` pseudoemetric structure. This definition is
not satisfactory, as it does not register the fact that the topology and the uniform structure
coincide with the product one. Therefore, we do not register it as an instance. Using this as a
temporary pseudoemetric space instance, we will show that the uniform structure is equal (but not
defeq) to the product one, and then register an instance in which we replace the uniform structure
by the product one using this pseudoemetric space and `PseudoEMetricSpace.replaceUniformity`. -/
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
      · exact prod_sup_edist_ne_top_aux f g
      · rw [prod_edist_eq_add (zero_lt_one.trans_le h)]
        refine ENNReal.rpow_ne_top_of_nonneg (by positivity) (ne_of_lt ?_)
        simp [ENNReal.add_lt_top, ENNReal.rpow_lt_top_of_nonneg, edist_ne_top] )
    fun f g => by
    rcases p.dichotomy with (rfl | h)
    · rw [prod_edist_eq_sup, prod_dist_eq_sup]
      refine le_antisymm (sup_le ?_ ?_) ?_
      · rw [← ENNReal.ofReal_le_iff_le_toReal (prod_sup_edist_ne_top_aux f g),
          ← PseudoMetricSpace.edist_dist]
        exact le_sup_left
      · rw [← ENNReal.ofReal_le_iff_le_toReal (prod_sup_edist_ne_top_aux f g),
          ← PseudoMetricSpace.edist_dist]
        exact le_sup_right
      · refine ENNReal.toReal_le_of_le_ofReal ?_ ?_
        · simp only [le_sup_iff, dist_nonneg, or_self]
        · simp [edist, PseudoMetricSpace.edist_dist, ENNReal.ofReal_le_ofReal]
    · have h1 : edist f.fst g.fst ^ p.toReal ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (zero_le_one.trans h) (edist_ne_top _ _)
      have h2 : edist f.snd g.snd ^ p.toReal ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (zero_le_one.trans h) (edist_ne_top _ _)
      simp only [prod_edist_eq_add (zero_lt_one.trans_le h), dist_edist, ENNReal.toReal_rpow,
        prod_dist_eq_add (zero_lt_one.trans_le h), ← ENNReal.toReal_add h1 h2]

attribute [local instance] WithLp.prodPseudoMetricAux

theorem prod_lipschitzWith_equiv_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    LipschitzWith 1 (WithLp.equiv p (α × β)) := by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simp [edist]
  · have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (zero_lt_one.trans_le h).ne'
    rw [prod_edist_eq_add (zero_lt_one.trans_le h)]
    simp only [edist, forall_prop_of_true, one_mul, ENNReal.coe_one, sup_le_iff]
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

theorem prod_antilipschitzWith_equiv_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    AntilipschitzWith ((2 : ℝ≥0) ^ (1 / p).toReal) (WithLp.equiv p (α × β)) := by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simp [edist]
  · have pos : 0 < p.toReal := by positivity
    have nonneg : 0 ≤ 1 / p.toReal := by positivity
    have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (ne_of_gt pos)
    rw [prod_edist_eq_add pos, ENNReal.toReal_div 1 p]
    simp only [edist, ← one_div, ENNReal.one_toReal]
    calc
      (edist x.fst y.fst ^ p.toReal + edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) ≤
          (edist (WithLp.equiv p _ x) (WithLp.equiv p _ y) ^ p.toReal +
          edist (WithLp.equiv p _ x) (WithLp.equiv p _ y) ^ p.toReal) ^ (1 / p.toReal) := by
        gcongr <;> simp [edist]
      _ = (2 ^ (1 / p.toReal) : ℝ≥0) * edist (WithLp.equiv p _ x) (WithLp.equiv p _ y) := by
        simp only [← two_mul, ENNReal.mul_rpow_of_nonneg _ _ nonneg, ← ENNReal.rpow_mul, cancel,
          ENNReal.rpow_one, ENNReal.coe_rpow_of_nonneg _ nonneg, coe_ofNat]

theorem prod_aux_uniformity_eq [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    𝓤 (WithLp p (α × β)) = 𝓤[instUniformSpaceProd] := by
  have A : IsUniformInducing (WithLp.equiv p (α × β)) :=
    (prod_antilipschitzWith_equiv_aux p α β).isUniformInducing
      (prod_lipschitzWith_equiv_aux p α β).uniformContinuous
  have : (fun x : WithLp p (α × β) × WithLp p (α × β) =>
    ((WithLp.equiv p (α × β)) x.fst, (WithLp.equiv p (α × β)) x.snd)) = id := by
    ext i <;> rfl
  rw [← A.comap_uniformity, this, comap_id]

theorem prod_aux_cobounded_eq [PseudoMetricSpace α] [PseudoMetricSpace β] :
    cobounded (WithLp p (α × β)) = @cobounded _ Prod.instBornology :=
  calc
    cobounded (WithLp p (α × β)) = comap (WithLp.equiv p (α × β)) (cobounded _) :=
      le_antisymm (prod_antilipschitzWith_equiv_aux p α β).tendsto_cobounded.le_comap
        (prod_lipschitzWith_equiv_aux p α β).comap_cobounded_le
    _ = _ := comap_id

end Aux

/-! ### Instances on `L^p` products -/

section TopologicalSpace

variable [TopologicalSpace α] [TopologicalSpace β]

instance instProdTopologicalSpace : TopologicalSpace (WithLp p (α × β)) :=
  instTopologicalSpaceProd

@[continuity]
theorem prod_continuous_equiv : Continuous (WithLp.equiv p (α × β)) :=
  continuous_id

@[continuity]
theorem prod_continuous_equiv_symm : Continuous (WithLp.equiv p (α × β)).symm :=
  continuous_id

variable [T0Space α] [T0Space β]

instance instProdT0Space : T0Space (WithLp p (α × β)) :=
  Prod.instT0Space

end TopologicalSpace

section UniformSpace

variable [UniformSpace α] [UniformSpace β]

instance instProdUniformSpace : UniformSpace (WithLp p (α × β)) :=
  instUniformSpaceProd

theorem prod_uniformContinuous_equiv : UniformContinuous (WithLp.equiv p (α × β)) :=
  uniformContinuous_id

theorem prod_uniformContinuous_equiv_symm : UniformContinuous (WithLp.equiv p (α × β)).symm :=
  uniformContinuous_id

variable [CompleteSpace α] [CompleteSpace β]

instance instProdCompleteSpace : CompleteSpace (WithLp p (α × β)) :=
  CompleteSpace.prod

end UniformSpace

instance instProdBornology [Bornology α] [Bornology β] : Bornology (WithLp p (α × β)) :=
  Prod.instBornology

section ContinuousLinearEquiv

variable [TopologicalSpace α] [TopologicalSpace β]
variable [Semiring 𝕜] [AddCommGroup α] [AddCommGroup β]
variable [Module 𝕜 α] [Module 𝕜 β]

/-- `WithLp.equiv` as a continuous linear equivalence. -/
@[simps! (config := .asFn) apply symm_apply]
protected def prodContinuousLinearEquiv : WithLp p (α × β) ≃L[𝕜] α × β where
  toLinearEquiv := WithLp.linearEquiv _ _ _
  continuous_toFun := prod_continuous_equiv _ _ _
  continuous_invFun := prod_continuous_equiv_symm _ _ _

end ContinuousLinearEquiv

/-! Throughout the rest of the file, we assume `1 ≤ p` -/
variable [hp : Fact (1 ≤ p)]

/-- `PseudoEMetricSpace` instance on the product of two pseudoemetric spaces, using the
`L^p` pseudoedistance, and having as uniformity the product uniformity. -/
instance instProdPseudoEMetricSpace [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    PseudoEMetricSpace (WithLp p (α × β)) :=
  (prodPseudoEMetricAux p α β).replaceUniformity (prod_aux_uniformity_eq p α β).symm

/-- `EMetricSpace` instance on the product of two emetric spaces, using the `L^p`
edistance, and having as uniformity the product uniformity. -/
instance instProdEMetricSpace [EMetricSpace α] [EMetricSpace β] : EMetricSpace (WithLp p (α × β)) :=
  EMetricSpace.ofT0PseudoEMetricSpace (WithLp p (α × β))

/-- `PseudoMetricSpace` instance on the product of two pseudometric spaces, using the
`L^p` distance, and having as uniformity the product uniformity. -/
instance instProdPseudoMetricSpace [PseudoMetricSpace α] [PseudoMetricSpace β] :
    PseudoMetricSpace (WithLp p (α × β)) :=
  ((prodPseudoMetricAux p α β).replaceUniformity
    (prod_aux_uniformity_eq p α β).symm).replaceBornology
    fun s => Filter.ext_iff.1 (prod_aux_cobounded_eq p α β).symm sᶜ

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

variable (p α β)

theorem prod_lipschitzWith_equiv [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    LipschitzWith 1 (WithLp.equiv p (α × β)) :=
  prod_lipschitzWith_equiv_aux p α β

theorem prod_antilipschitzWith_equiv [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    AntilipschitzWith ((2 : ℝ≥0) ^ (1 / p).toReal) (WithLp.equiv p (α × β)) :=
  prod_antilipschitzWith_equiv_aux p α β

theorem prod_infty_equiv_isometry [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    Isometry (WithLp.equiv ∞ (α × β)) :=
  fun x y =>
  le_antisymm (by simpa only [ENNReal.coe_one, one_mul] using prod_lipschitzWith_equiv ∞ α β x y)
    (by
      simpa only [ENNReal.div_top, ENNReal.zero_toReal, NNReal.rpow_zero, ENNReal.coe_one,
        one_mul] using prod_antilipschitzWith_equiv ∞ α β x y)

/-- Seminormed group instance on the product of two normed groups, using the `L^p`
norm. -/
instance instProdSeminormedAddCommGroup [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] :
    SeminormedAddCommGroup (WithLp p (α × β)) where
  dist_eq x y := by
    rcases p.dichotomy with (rfl | h)
    · simp only [prod_dist_eq_sup, prod_norm_eq_sup, dist_eq_norm]
      rfl
    · simp only [prod_dist_eq_add (zero_lt_one.trans_le h),
        prod_norm_eq_add (zero_lt_one.trans_le h), dist_eq_norm]
      rfl

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
  simp only [one_div, h, Real.rpow_natCast, ENNReal.toReal_nat, eq_self_iff_true, Finset.sum_congr,
    prod_norm_eq_add this]

variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

theorem prod_nnnorm_eq_add (hp : p ≠ ∞) (f : WithLp p (α × β)) :
    ‖f‖₊ = (‖f.fst‖₊ ^ p.toReal + ‖f.snd‖₊ ^ p.toReal) ^ (1 / p.toReal) := by
  ext
  simp [prod_norm_eq_add (p.toReal_pos_iff_ne_top.mpr hp)]

theorem prod_nnnorm_eq_sup (f : WithLp ∞ (α × β)) : ‖f‖₊ = ‖f.fst‖₊ ⊔  ‖f.snd‖₊ := by
  ext
  norm_cast

@[simp] theorem prod_nnnorm_equiv (f : WithLp ∞ (α × β)) : ‖WithLp.equiv ⊤ _ f‖₊ = ‖f‖₊ := by
  rw [prod_nnnorm_eq_sup, Prod.nnnorm_def, equiv_fst, equiv_snd]

@[simp] theorem prod_nnnorm_equiv_symm (f : α × β) : ‖(WithLp.equiv ⊤ _).symm f‖₊ = ‖f‖₊ :=
  (prod_nnnorm_equiv _).symm

@[simp] theorem prod_norm_equiv (f : WithLp ∞ (α × β)) : ‖WithLp.equiv ⊤ _ f‖ = ‖f‖ :=
  congr_arg NNReal.toReal <| prod_nnnorm_equiv f

@[simp] theorem prod_norm_equiv_symm (f : α × β) : ‖(WithLp.equiv ⊤ _).symm f‖ = ‖f‖ :=
  (prod_norm_equiv _).symm

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

@[simp]
theorem nnnorm_equiv_symm_fst (x : α) :
    ‖(WithLp.equiv p (α × β)).symm (x, 0)‖₊ = ‖x‖₊ := by
  induction p generalizing hp with
  | top =>
    simp [prod_nnnorm_eq_sup]
  | coe p =>
    have hp0 : (p : ℝ) ≠ 0 := mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 ≤ (p : ℝ≥0∞))).ne'
    simp [prod_nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel₀ hp0]

@[simp]
theorem nnnorm_equiv_symm_snd (y : β) :
    ‖(WithLp.equiv p (α × β)).symm (0, y)‖₊ = ‖y‖₊ := by
  induction p generalizing hp with
  | top =>
    simp [prod_nnnorm_eq_sup]
  | coe p =>
    have hp0 : (p : ℝ) ≠ 0 := mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 ≤ (p : ℝ≥0∞))).ne'
    simp [prod_nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel₀ hp0]

@[simp]
theorem norm_equiv_symm_fst (x : α) : ‖(WithLp.equiv p (α × β)).symm (x, 0)‖ = ‖x‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_equiv_symm_fst p α β x

@[simp]
theorem norm_equiv_symm_snd (y : β) : ‖(WithLp.equiv p (α × β)).symm (0, y)‖ = ‖y‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_equiv_symm_snd p α β y

@[simp]
theorem nndist_equiv_symm_fst (x₁ x₂ : α) :
    nndist ((WithLp.equiv p (α × β)).symm (x₁, 0)) ((WithLp.equiv p (α × β)).symm (x₂, 0)) =
      nndist x₁ x₂ := by
  rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← WithLp.equiv_symm_sub, Prod.mk_sub_mk, sub_zero,
    nnnorm_equiv_symm_fst]

@[simp]
theorem nndist_equiv_symm_snd (y₁ y₂ : β) :
    nndist ((WithLp.equiv p (α × β)).symm (0, y₁)) ((WithLp.equiv p (α × β)).symm (0, y₂)) =
      nndist y₁ y₂ := by
  rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← WithLp.equiv_symm_sub, Prod.mk_sub_mk, sub_zero,
    nnnorm_equiv_symm_snd]

@[simp]
theorem dist_equiv_symm_fst (x₁ x₂ : α) :
    dist ((WithLp.equiv p (α × β)).symm (x₁, 0)) ((WithLp.equiv p (α × β)).symm (x₂, 0)) =
      dist x₁ x₂ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nndist_equiv_symm_fst p α β x₁ x₂

@[simp]
theorem dist_equiv_symm_snd (y₁ y₂ : β) :
    dist ((WithLp.equiv p (α × β)).symm (0, y₁)) ((WithLp.equiv p (α × β)).symm (0, y₂)) =
      dist y₁ y₂ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nndist_equiv_symm_snd p α β y₁ y₂

@[simp]
theorem edist_equiv_symm_fst (x₁ x₂ : α) :
    edist ((WithLp.equiv p (α × β)).symm (x₁, 0)) ((WithLp.equiv p (α × β)).symm (x₂, 0)) =
      edist x₁ x₂ := by
  simp only [edist_nndist, nndist_equiv_symm_fst p α β x₁ x₂]

@[simp]
theorem edist_equiv_symm_snd (y₁ y₂ : β) :
    edist ((WithLp.equiv p (α × β)).symm (0, y₁)) ((WithLp.equiv p (α × β)).symm (0, y₂)) =
      edist y₁ y₂ := by
  simp only [edist_nndist, nndist_equiv_symm_snd p α β y₁ y₂]

end Single

section BoundedSMul
variable [SeminormedRing 𝕜] [Module 𝕜 α] [Module 𝕜 β] [BoundedSMul 𝕜 α] [BoundedSMul 𝕜 β]

instance instProdBoundedSMul : BoundedSMul 𝕜 (WithLp p (α × β)) :=
  .of_nnnorm_smul_le fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · simp only [← prod_nnnorm_equiv, WithLp.equiv_smul]
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
  __ := WithLp.equiv ∞ (α × β)
  map_add' _f _g := rfl
  map_smul' _c _f := rfl
  norm_map' := prod_norm_equiv

end BoundedSMul

section SeminormedAddCommGroup

open ENNReal

variable {p : ℝ≥0∞} {α β}

/-- Projection on `WithLp p (α × β)` with range `α` and kernel `β` -/
def idemFst : AddMonoid.End (WithLp p (α × β)) := (AddMonoidHom.inl α β).comp (AddMonoidHom.fst α β)

/-- Projection on `WithLp p (α × β)` with range `β` and kernel `α` -/
def idemSnd : AddMonoid.End (WithLp p (α × β)) := (AddMonoidHom.inr α β).comp (AddMonoidHom.snd α β)

lemma idemFst_apply (x : WithLp p (α × β)) :
    idemFst x = (WithLp.equiv _ _).symm (((WithLp.equiv _ _) x).1, 0) :=
  rfl

lemma idemSnd_apply (x : WithLp p (α × β)) :
    idemSnd x = (WithLp.equiv _ _).symm (0, ((WithLp.equiv _ _) x).2) :=
  rfl

@[simp]
lemma idemFst_add_idemSnd :
    idemFst + idemSnd = (1 : AddMonoid.End (WithLp p (α × β))) := AddMonoidHom.ext
  fun x => by
    rw [AddMonoidHom.add_apply, idemFst_apply, idemSnd_apply, AddMonoid.End.coe_one, id_eq,
      ← WithLp.equiv_symm_add, Prod.mk_add_mk, zero_add, add_zero, Prod.mk.eta,
      Equiv.symm_apply_apply]

lemma idemFst_compl : (1 : AddMonoid.End (WithLp p (α × β))) - idemFst = idemSnd := by
  rw [← idemFst_add_idemSnd, add_sub_cancel_left]

lemma idemSnd_compl : (1 : AddMonoid.End (WithLp p (α × β))) - idemSnd = idemFst := by
  rw [← idemFst_add_idemSnd, add_sub_cancel_right]

theorem prod_norm_eq_idemFst_sup_idemSnd (x : WithLp ∞ (α × β)) :
    ‖x‖ = max ‖idemFst x‖ ‖idemSnd x‖ := by
  rw [WithLp.prod_norm_eq_sup, ← WithLp.norm_equiv_symm_fst ∞ α β x.1,
    ← WithLp.norm_equiv_symm_snd ∞ α β x.2, idemFst_apply, idemSnd_apply]
  simp only [norm_equiv_symm_fst, norm_equiv_symm_snd, equiv_fst, equiv_snd]

lemma prod_norm_eq_add_idemFst [Fact (1 ≤ p)] (hp : 0 < p.toReal) (x : WithLp p (α × β)) :
    ‖x‖ = (‖idemFst x‖ ^ p.toReal + ‖idemSnd x‖ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [WithLp.prod_norm_eq_add hp, ← WithLp.norm_equiv_symm_fst p α β x.1,
    ← WithLp.norm_equiv_symm_snd p α β x.2]
  simp only [norm_equiv_symm_fst, norm_equiv_symm_snd, one_div, idemFst_apply, equiv_fst,
    idemSnd_apply, equiv_snd]

lemma prod_norm_eq_idemFst_of_L1 (x : WithLp 1 (α × β)) : ‖x‖ = ‖idemFst x‖ + ‖idemSnd x‖ := by
  rw [prod_norm_eq_add_idemFst (lt_of_lt_of_eq zero_lt_one one_toReal.symm)]
  simp only [one_toReal, Real.rpow_one, ne_eq, one_ne_zero, not_false_eq_true, div_self]

end SeminormedAddCommGroup

section NormedSpace

/-- The product of two normed spaces is a normed space, with the `L^p` norm. -/
instance instProdNormedSpace [NormedField 𝕜] [NormedSpace 𝕜 α] [NormedSpace 𝕜 β] :
    NormedSpace 𝕜 (WithLp p (α × β)) where
  norm_smul_le := norm_smul_le

end NormedSpace

end WithLp
