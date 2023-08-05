/-
Copyright (c) 2023 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Sébastien Gouëzel, Jireh Loreaux
-/

import Mathlib.Analysis.MeanInequalities

/-!
# `L^p` distance on products of two metric spaces
Given two metric spaces, one can put the max distance on their product, but there is also
a whole family of natural distances, indexed by a parameter `p : ℝ≥0∞`, that also induce
the product topology. We define them in this file. For `0 < p < ∞`, the distance on `α × β`
is given by
$$
d(x, y) = \left(d(x_1, y_1)^p + d(x_2, y_2)^p\right)^{1/p}.
$$
For `p = ∞` the distance is the supremum of the distances.

We give instances of this construction for emetric spaces, metric spaces, normed groups and normed
spaces.

To avoid conflicting instances, all these are defined on a copy of the original Prod-type, named
`ProdLp p α β`. The assumption `[Fact (1 ≤ p)]` is required for the metric and normed space
instances.

We ensure that the topology, bornology and uniform structure on `ProdLp p α β` are (defeq to) the
product topology, product bornology and product uniformity, to be able to use freely continuity
statements for the coordinate functions, for instance.

# Implementation notes

This files is a straight-forward adaption of `Mathlib.Analysis.NormedSpace.PiLp`. We deviate from
`PiLp` in that we use for `p = 0` the junk value `d(x, y) = 0`.

-/

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y) -- Porting note: See issue #2220

open Real Set Filter IsROrC Bornology BigOperators Uniformity Topology NNReal ENNReal

noncomputable section

/-- A copy of a Prod type, on which we will put the `L^p` distance. Since the Prod type itself is
already endowed with the `L^∞` distance, we need the type synonym to avoid confusing typeclass
resolution. Also, we let it depend on `p`, to get a whole family of type on which we can put
different distances. -/
@[nolint unusedArguments]
def ProdLp (_p : ℝ≥0∞) (α β : Type _) : Type _ :=
  α × β

instance ProdLp.instInhabited (p : ℝ≥0∞) (α β : Type _) [Inhabited α] [Inhabited β] :
    Inhabited (ProdLp p α β) :=
  ⟨default, default⟩

@[ext]
protected theorem ProdLp.ext {p : ℝ≥0∞} {α β : Type _} {x y : ProdLp p α β}
    (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y := Prod.ext h1 h2

namespace ProdLp

variable (p : ℝ≥0∞) (𝕜 𝕜' : Type _) (α β : Type _)

/-- Canonical bijection between `ProdLp p α β` and the original Prod type. We introduce it to be
able to compare the `L^p` and `L^∞` distances through it. -/
protected def equiv : ProdLp p α β ≃ α × β :=
  Equiv.refl _

/-! Note that the unapplied versions of these lemmas are deliberately omitted, as they break
the use of the type synonym. -/

@[simp]
theorem equiv_apply (x : ProdLp p α β) : ProdLp.equiv p α β x = x :=
  rfl

@[simp]
theorem equiv_symm_apply (x : α × β) : (ProdLp.equiv p α β).symm x = x :=
  rfl

section DistNorm

/-!
### Definition of `edist`, `dist` and `norm` on `ProdLp`

In this section we define the `edist`, `dist` and `norm` functions on `ProdLp p α β` without
assuming `[Fact (1 ≤ p)]` or metric properties of the spaces `α` and `β`. This allows us to provide
the rewrite lemmas for each of three cases `p = 0`, `p = ∞` and `0 < p.to_real`.
-/


section Edist

variable [EDist α] [EDist β]

/-- Endowing the space `ProdLp p α β` with the `L^p` edistance. We register this instance
separate from `ProdLp.instPseudoEMetric` since the latter requires the type class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future emetric-like structure on `ProdLp p α β` for `p < 1`
satisfying a relaxed triangle inequality. The terminology for this varies throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*. -/
instance instEDist : EDist (ProdLp p α β) where
  edist f g :=
    if _hp : p = 0 then 0
    else
      if p = ∞ then edist f.fst g.fst ⊔ edist f.snd g.snd
      else (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)

variable {α β}

variable (x y : ProdLp p α β) (x' : α × β)

@[simp]
protected theorem edist_eq_zero (f g : ProdLp 0 α β) : edist f g = 0 :=
  if_pos rfl

theorem edist_eq_add {p : ℝ≥0∞} (hp : 0 < p.toReal) (f g : ProdLp p α β) :
    edist f g = (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

theorem edist_eq_sup (f g : ProdLp ∞ α β) :
    edist f g = edist f.fst g.fst ⊔ edist f.snd g.snd := by
  dsimp [edist]
  exact if_neg ENNReal.top_ne_zero

end Edist

section EdistProp

variable {α β}
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β]

/-- This holds independent of `p` and does not require `[Fact (1 ≤ p)]`. We keep it separate
from `ProdLp.instPseudoEMetricSpace` so it can be used also for `p < 1`. -/
protected theorem edist_self (f : ProdLp p α β) : edist f f = 0 := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp
  · simp [edist_eq_sup]
  · simp [edist_eq_add h, ENNReal.zero_rpow_of_pos h, ENNReal.zero_rpow_of_pos (inv_pos.2 <| h)]

/-- This holds independent of `p` and does not require `[Fact (1 ≤ p)]`. We keep it separate
from `ProdLp.instPseudoEMetricSpace` so it can be used also for `p < 1`. -/
protected theorem edist_comm (f g : ProdLp p α β) : edist f g = edist g f := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp only [ProdLp.edist_eq_zero, eq_comm, Ne.def]
  · simp only [edist_eq_sup, edist_comm]
  · simp only [edist_eq_add h, edist_comm]

end EdistProp

section Dist

variable [Dist α] [Dist β]

/-- Endowing the space `ProdLp p α β` with the `L^p` distance. We register this instance
separate from `ProdLp.instPseudoMetricSpace` since the latter requires the type class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future metric-like structure on `ProdLp p α β` for `p < 1`
satisfying a relaxed triangle inequality. The terminology for this varies throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*. -/
instance instDist : Dist (ProdLp p α β) where
  dist f g :=
    if _hp : p = 0 then 0 --{ i | f i ≠ g i }.toFinite.toFinset.card
    else
      if p = ∞ then dist f.fst g.fst ⊔ dist f.snd g.snd
      else (dist f.fst g.fst ^ p.toReal + dist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)

variable {α β}

theorem dist_eq_card (f g : ProdLp 0 α β) : dist f g = 0 :=
  if_pos rfl

theorem dist_eq_add {p : ℝ≥0∞} (hp : 0 < p.toReal) (f g : ProdLp p α β) :
    dist f g = (dist f.fst g.fst ^ p.toReal + dist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

theorem dist_eq_sup (f g : ProdLp ∞ α β) :
    dist f g = dist f.fst g.fst ⊔ dist f.snd g.snd := by
  dsimp [dist]
  exact if_neg ENNReal.top_ne_zero

end Dist

section Norm

variable [Norm α] [Zero α] [Norm β] [Zero β]

/-- Endowing the space `ProdLp p α β` with the `L^p` norm. We register this instance
separate from `ProdLp.instSeminormedAddCommGroup` since the latter requires the type class
hypothesis `[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future norm-like structure on `ProdLp p α β` for `p < 1`
satisfying a relaxed triangle inequality. These are called *quasi-norms*. -/
instance instNorm : Norm (ProdLp p α β) where
  norm f :=
    if _hp : p = 0 then 0
    else if p = ∞ then ‖f.fst‖ ⊔ ‖f.snd‖
    else (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal)

variable {p α β}

@[simp]
protected theorem norm_eq_zero (f : ProdLp 0 α β) : ‖f‖ = 0 :=
  if_pos rfl

theorem norm_eq_sup (f : ProdLp ∞ α β) : ‖f‖ = ‖f.fst‖ ⊔ ‖f.snd‖ := by
  dsimp [Norm.norm]
  exact if_neg ENNReal.top_ne_zero

theorem norm_eq_add (hp : 0 < p.toReal) (f : ProdLp p α β) :
    ‖f‖ = (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

end Norm

end DistNorm

section Aux

/-!
### The uniformity on finite `L^p` products is the product uniformity

In this section, we put the `L^p` edistance on `ProdLp p α β`, and we check that the uniformity
coming from this edistance coincides with the product uniformity, by showing that the canonical
map to the Pi type (with the `L^∞` distance) is a uniform embedding, as it is both Lipschitz and
antiLipschitz.

We only register this emetric space structure as a temporary instance, as the true instance (to be
registered later) will have as uniformity exactly the product uniformity, instead of the one coming
from the edistance (which is equal to it, but not defeq). See Note [forgetful inheritance]
explaining why having definitionally the right uniformity is often important.
-/


variable [Fact (1 ≤ p)]

/-- Endowing the space `ProdLp p α β` with the `L^p` pseudoemetric structure. This definition is not
satisfactory, as it does not register the fact that the topology and the uniform structure coincide
with the product one. Therefore, we do not register it as an instance. Using this as a temporary
pseudoemetric space instance, we will show that the uniform structure is equal (but not defeq) to
the product one, and then register an instance in which we replace the uniform structure by the
product one using this pseudoemetric space and `PseudoEMetricSpace.replaceUniformity`. -/
def pseudoEmetricAux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    PseudoEMetricSpace (ProdLp p α β) where
  edist_self := ProdLp.edist_self p
  edist_comm := ProdLp.edist_comm p
  edist_triangle f g h := by
    rcases p.dichotomy with (rfl | hp)
    · simp only [edist_eq_sup]
      exact sup_le ((edist_triangle _ g.fst _).trans <| add_le_add le_sup_left le_sup_left)
        ((edist_triangle _ g.snd _).trans <| add_le_add le_sup_right le_sup_right)
    · simp only [edist_eq_add (zero_lt_one.trans_le hp)]
      calc
        (edist f.fst h.fst ^ p.toReal + edist f.snd h.snd ^ p.toReal) ^ (1 / p.toReal) ≤
            ((edist f.fst g.fst + edist g.fst h.fst) ^ p.toReal +
              (edist f.snd g.snd + edist g.snd h.snd) ^ p.toReal) ^ (1 / p.toReal) := by
          apply ENNReal.rpow_le_rpow _ (one_div_nonneg.2 <| zero_le_one.trans hp)
          exact add_le_add (ENNReal.rpow_le_rpow (edist_triangle _ _ _) (zero_le_one.trans hp))
            (ENNReal.rpow_le_rpow (edist_triangle _ _ _) (zero_le_one.trans hp))
        _ ≤
            (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) +
              (edist g.fst h.fst ^ p.toReal + edist g.snd h.snd ^ p.toReal) ^ (1 / p.toReal) := by
          have := ENNReal.Lp_add_le {0, 1}
            (if · = 0 then edist f.fst g.fst else edist f.snd g.snd)
            (if · = 0 then edist g.fst h.fst else edist g.snd h.snd) hp
          simp only [Finset.mem_singleton, not_false_eq_true, Finset.sum_insert,
            Finset.sum_singleton] at this
          exact this

attribute [local instance] ProdLp.pseudoEmetricAux

/-- An auxiliary lemma used twice in the proof of `ProdLp.pseudoMetricAux` below. Not intended for
use outside this file. -/
theorem sup_edist_ne_top_aux {α β : Type _}
    [PseudoMetricSpace α] [PseudoMetricSpace β] (f g : ProdLp ∞ α β) :
    edist f.fst g.fst ⊔ edist f.snd g.snd ≠ ⊤ := by
  refine ne_of_lt ?_
  simp [edist, PseudoMetricSpace.edist_dist]

/-- Endowing the space `ProdLp p α β` with the `L^p` pseudometric structure. This definition is not
satisfactory, as it does not register the fact that the topology, the uniform structure, and the
bornology coincide with the product ones. Therefore, we do not register it as an instance. Using
this as a temporary pseudoemetric space instance, we will show that the uniform structure is equal
(but not defeq) to the product one, and then register an instance in which we replace the uniform
structure and the bornology by the product ones using this pseudometric space,
`PseudoMetricSpace.replaceUniformity`, and `PseudoMetricSpace.replaceBornology`.

See note [reducible non-instances] -/
@[reducible]
def pseudoMetricAux [PseudoMetricSpace α] [PseudoMetricSpace β] :
    PseudoMetricSpace (ProdLp p α β) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
    (fun f g => by
      rcases p.dichotomy with (rfl | h)
      · exact sup_edist_ne_top_aux f g
      · rw [edist_eq_add (zero_lt_one.trans_le h)]
        refine
          ENNReal.rpow_ne_top_of_nonneg (by positivity) (ne_of_lt ?_)
        simp [ENNReal.add_lt_top, ENNReal.rpow_lt_top_of_nonneg, edist_ne_top] )
    fun f g => by
    rcases p.dichotomy with (rfl | h)
    · rw [edist_eq_sup, dist_eq_sup]
      refine' le_antisymm (sup_le _ _) _
      · rw [← ENNReal.ofReal_le_iff_le_toReal (sup_edist_ne_top_aux f g), ←
          PseudoMetricSpace.edist_dist]
        exact le_sup_left
      · rw [← ENNReal.ofReal_le_iff_le_toReal (sup_edist_ne_top_aux f g), ←
          PseudoMetricSpace.edist_dist]
        exact le_sup_right
      · refine ENNReal.toReal_le_of_le_ofReal ?_ ?_
        · simp only [ge_iff_le, le_sup_iff, dist_nonneg]
        · simp [edist, PseudoMetricSpace.edist_dist, ENNReal.ofReal_le_ofReal]
    · have h1 : edist f.fst g.fst ^ p.toReal ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (zero_le_one.trans h) (edist_ne_top _ _)
      have h2 : edist f.snd g.snd ^ p.toReal ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (zero_le_one.trans h) (edist_ne_top _ _)
      simp only [edist_eq_add (zero_lt_one.trans_le h), dist_edist, ENNReal.toReal_rpow,
        dist_eq_add (zero_lt_one.trans_le h), ← ENNReal.toReal_add h1 h2]

attribute [local instance] ProdLp.pseudoMetricAux

theorem lipschitzWith_equiv_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    LipschitzWith 1 (ProdLp.equiv p α β) := by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simp only [equiv_apply, coe_one, one_mul, le_refl]
  · have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel' 1 (zero_lt_one.trans_le h).ne'
    rw [edist_eq_add (zero_lt_one.trans_le h)]
    simp only [edist, forall_prop_of_true, one_mul, ENNReal.coe_one, equiv_apply, ge_iff_le,
      sup_le_iff]
    constructor
    · calc
        edist x.fst y.fst ≤ (edist x.fst y.fst ^ p.toReal) ^ (1 / p.toReal) := by
          simp only [← ENNReal.rpow_mul, cancel, ENNReal.rpow_one, le_refl]
        _ ≤ (edist x.fst y.fst ^ p.toReal + edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) := by
          apply ENNReal.rpow_le_rpow _ (by positivity)
          simp only [self_le_add_right]
    · calc
        edist x.snd y.snd ≤ (edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) := by
          simp only [← ENNReal.rpow_mul, cancel, ENNReal.rpow_one, le_refl]
        _ ≤ (edist x.fst y.fst ^ p.toReal + edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) := by
          apply ENNReal.rpow_le_rpow _ (by positivity)
          simp only [self_le_add_left]

example (a : ENNReal) : a + a = 2*a := by exact Eq.symm (two_mul a)

theorem antilipschitzWith_equiv_aux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    AntilipschitzWith ((2 : ℝ≥0) ^ (1 / p).toReal) (ProdLp.equiv p α β) := by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simp [edist]
  · have pos : 0 < p.toReal := by positivity
    have nonneg : 0 ≤ 1 / p.toReal := by positivity
    have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel' 1 (ne_of_gt pos)
    rw [edist_eq_add pos, ENNReal.toReal_div 1 p]
    simp only [edist, ← one_div, ENNReal.one_toReal]
    calc
      (edist x.fst y.fst ^ p.toReal + edist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) ≤
          (edist (ProdLp.equiv p α β x) (ProdLp.equiv p α β y) ^ p.toReal +
          edist (ProdLp.equiv p α β x) (ProdLp.equiv p α β y) ^ p.toReal) ^ (1 / p.toReal) := by
        refine ENNReal.rpow_le_rpow (add_le_add ?_ ?_) nonneg
        · refine ENNReal.rpow_le_rpow ?_ (le_of_lt pos)
          simp [edist]
        · refine ENNReal.rpow_le_rpow ?_ (le_of_lt pos)
          simp [edist]
      _ =
          ((2 : ℝ≥0) ^ (1 / p.toReal) : ℝ≥0) *
            edist (ProdLp.equiv p α β x) (ProdLp.equiv p α β y) := by
        simp only [equiv_apply, ← two_mul, ENNReal.mul_rpow_of_nonneg _ _ nonneg,
          ← ENNReal.rpow_mul, cancel, ENNReal.rpow_one, ← ENNReal.coe_rpow_of_nonneg _ nonneg,
          coe_ofNat]

theorem aux_uniformity_eq [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    𝓤 (ProdLp p α β) = 𝓤[instUniformSpaceProd] := by
  have A : UniformInducing (ProdLp.equiv p α β) :=
    (antilipschitzWith_equiv_aux p α β).uniformInducing
      (lipschitzWith_equiv_aux p α β).uniformContinuous
  have : (fun x : ProdLp p α β × ProdLp p α β =>
    ((ProdLp.equiv p α β) x.fst, (ProdLp.equiv p α β) x.snd)) = id :=
    by ext i <;> rfl
  rw [← A.comap_uniformity, this, comap_id]

theorem aux_cobounded_eq [PseudoMetricSpace α] [PseudoMetricSpace β] :
    cobounded (ProdLp p α β) = @cobounded _ Prod.instBornology :=
  calc
    cobounded (ProdLp p α β) = comap (ProdLp.equiv p α β) (cobounded _) :=
      le_antisymm (antilipschitzWith_equiv_aux p α β).tendsto_cobounded.le_comap
        (lipschitzWith_equiv_aux p α β).comap_cobounded_le
    _ = _ := comap_id

end Aux

/-! ### Instances on `L^p` products -/


instance instUniformSpace [UniformSpace α] [UniformSpace β] : UniformSpace (ProdLp p α β) :=
  instUniformSpaceProd

theorem uniformContinuous_equiv [UniformSpace α] [UniformSpace β] :
    UniformContinuous (ProdLp.equiv p α β) :=
  uniformContinuous_id

theorem uniformContinuous_equiv_symm [UniformSpace α] [UniformSpace β] :
    UniformContinuous (ProdLp.equiv p α β).symm :=
  uniformContinuous_id

@[continuity]
theorem continuous_equiv [UniformSpace α] [UniformSpace β] : Continuous (ProdLp.equiv p α β) :=
  continuous_id

@[continuity]
theorem continuous_equiv_symm [UniformSpace α] [UniformSpace β] :
    Continuous (ProdLp.equiv p α β).symm :=
  continuous_id

instance instBornology [Bornology α] [Bornology β] : Bornology (ProdLp p α β) :=
  Prod.instBornology

-- throughout the rest of the file, we assume `1 ≤ p`
variable [Fact (1 ≤ p)]

/-- `PseudoEMetricSpace` instance on the product of two pseudoemetric spaces, using the
`L^p` pseudoedistance, and having as uniformity the product uniformity. -/
instance instPseudoEMetricSpace [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    PseudoEMetricSpace (ProdLp p α β) :=
  (pseudoEmetricAux p α β).replaceUniformity (aux_uniformity_eq p α β).symm

/-- `EMetricSpace` instance on the product of two emetric spaces, using the `L^p`
edistance, and having as uniformity the product uniformity. -/
instance instEMetricSpace [EMetricSpace α] [EMetricSpace β] : EMetricSpace (ProdLp p α β) :=
  @EMetricSpace.ofT0PseudoEMetricSpace (ProdLp p α β) _ instT0SpaceProdInstTopologicalSpaceProd

/-- `PseudoMetricSpace` instance on the product of two pseudometric spaces, using the
`L^p` distance, and having as uniformity the product uniformity. -/
instance instPseudoMetricSpace [PseudoMetricSpace α] [PseudoMetricSpace β] :
    PseudoMetricSpace (ProdLp p α β) :=
  ((pseudoMetricAux p α β).replaceUniformity (aux_uniformity_eq p α β).symm).replaceBornology
    fun s => Filter.ext_iff.1 (aux_cobounded_eq p α β).symm sᶜ

/-- `MetricSpace` instance on the product of two metric spaces, using the `L^p` distance,
and having as uniformity the product uniformity. -/
instance instMetricSpace [MetricSpace α] [MetricSpace β] : MetricSpace (ProdLp p α β) :=
  MetricSpace.ofT0PseudoMetricSpace _

variable {p α β}

theorem nndist_eq_sum [PseudoMetricSpace α] [PseudoMetricSpace β]
    (hp : p ≠ ∞) (x y : ProdLp p α β) :
    nndist x y = (nndist x.fst y.fst ^ p.toReal + nndist x.snd y.snd ^ p.toReal) ^ (1 / p.toReal) :=
  -- Porting note: was `Subtype.ext`
  NNReal.eq <| by
    push_cast
    exact dist_eq_add (p.toReal_pos_iff_ne_top.mpr hp) _ _

theorem nndist_eq_iSup [PseudoMetricSpace α] [PseudoMetricSpace β] (x y : ProdLp ∞ α β) :
    nndist x y = nndist x.fst y.fst ⊔ nndist x.snd y.snd :=
  -- Porting note: was `Subtype.ext`
  NNReal.eq <| by
    push_cast
    exact dist_eq_sup _ _

variable (p α β)

theorem lipschitzWith_equiv [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    LipschitzWith 1 (ProdLp.equiv p α β) :=
  lipschitzWith_equiv_aux p α β

theorem antilipschitzWith_equiv [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    AntilipschitzWith ((2 : ℝ≥0) ^ (1 / p).toReal) (ProdLp.equiv p α β) :=
  antilipschitzWith_equiv_aux p α β

theorem infty_equiv_isometry [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    Isometry (ProdLp.equiv ∞ α β) :=
  fun x y =>
  le_antisymm (by simpa only [ENNReal.coe_one, one_mul] using lipschitzWith_equiv ∞ α β x y)
    (by
      simpa only [ENNReal.div_top, ENNReal.zero_toReal, NNReal.rpow_zero, ENNReal.coe_one,
        one_mul] using antilipschitzWith_equiv ∞ α β x y)

/-- Seminormed group instance on the product of two normed groups, using the `L^p`
norm. -/
instance instSeminormedAddCommGroup [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] :
    SeminormedAddCommGroup (ProdLp p α β) :=
  { Prod.instAddCommGroupSum with
    dist_eq := fun x y => by
      rcases p.dichotomy with (rfl | h)
      · simp only [dist_eq_sup, norm_eq_sup, dist_eq_norm]
        rfl
      · have : p ≠ ∞ := by
          intro hp
          rw [hp, ENNReal.top_toReal] at h
          linarith
        simp only [dist_eq_add (zero_lt_one.trans_le h), norm_eq_add (zero_lt_one.trans_le h),
          dist_eq_norm]
        rfl }

/-- normed group instance on the product of two normed groups, using the `L^p` norm. -/
instance normedAddCommGroup [NormedAddCommGroup α] [NormedAddCommGroup β] :
    NormedAddCommGroup (ProdLp p α β) :=
  { ProdLp.instSeminormedAddCommGroup p α β with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

section norm_of

variable {p α β}
variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

theorem nnnorm_eq_add (hp : p ≠ ∞) (f : ProdLp p α β) :
    ‖f‖₊ = (‖f.fst‖₊ ^ p.toReal + ‖f.snd‖₊ ^ p.toReal) ^ (1 / p.toReal) := by
  ext
  simp [norm_eq_add (p.toReal_pos_iff_ne_top.mpr hp)]

theorem nnnorm_eq_sup (f : ProdLp ∞ α β) : ‖f‖₊ = ‖f.fst‖₊ ⊔  ‖f.snd‖₊ := by
  ext
  norm_cast

theorem norm_eq_of_nat (n : ℕ) (h : p = n) (f : ProdLp p α β) :
    ‖f‖ = (‖f.fst‖ ^ n + ‖f.snd‖ ^ n) ^ (1 / (n : ℝ)) := by
  have := p.toReal_pos_iff_ne_top.mpr (ne_of_eq_of_ne h <| ENNReal.nat_ne_top n)
  simp only [one_div, h, Real.rpow_nat_cast, ENNReal.toReal_nat, eq_self_iff_true, Finset.sum_congr,
    norm_eq_add this]

theorem norm_eq_of_L2 (x : ProdLp 2 α β) : ‖x‖ = sqrt (‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2) := by
  rw [norm_eq_of_nat 2 (by norm_cast) _] -- Porting note: was `convert`
  rw [Real.sqrt_eq_rpow]
  norm_cast

theorem nnnorm_eq_of_L2 (x : ProdLp 2 α β) : ‖x‖₊ = NNReal.sqrt (‖x.fst‖₊ ^ 2 + ‖x.snd‖₊ ^ 2) :=
  -- Porting note: was `Subtype.ext`
  NNReal.eq <| by
    push_cast
    exact norm_eq_of_L2 x

variable (α β)

theorem norm_sq_eq_of_L2 (x : ProdLp 2 α β) : ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 := by
  suffices ‖x‖₊ ^ 2 = ‖x.fst‖₊ ^ 2 + ‖x.snd‖₊ ^ 2 by
    simpa only [NNReal.coe_sum] using congr_arg ((↑) : ℝ≥0 → ℝ) this
  rw [nnnorm_eq_of_L2, NNReal.sq_sqrt]

variable {α β}

theorem dist_eq_of_L2 (x y : ProdLp 2 α β) :
    dist x y = (dist x.fst y.fst ^ 2 + dist x.snd y.snd ^ 2).sqrt := by
  simp_rw [dist_eq_norm, norm_eq_of_L2, Pi.sub_apply]
  rfl

theorem nndist_eq_of_L2 (x y : ProdLp 2 α β) :
    nndist x y = NNReal.sqrt (nndist x.fst y.fst ^ 2 + nndist x.snd y.snd ^ 2) :=
  -- Porting note: was `Subtype.ext`
  NNReal.eq <| by
    push_cast
    exact dist_eq_of_L2 _ _

theorem edist_eq_of_L2 (x y : ProdLp 2 α β) :
    edist x y = (edist x.fst y.fst ^ 2 + edist x.snd y.snd ^ 2) ^ (1 / 2 : ℝ) := by
  simp [ProdLp.edist_eq_add]

end norm_of

variable [NormedField 𝕜] [NormedField 𝕜']

section normed_space_inst

variable [SeminormedAddCommGroup α] [NormedSpace 𝕜 α]
  [SeminormedAddCommGroup β] [NormedSpace 𝕜 β]

-- Porting note: added
instance instModule : Module 𝕜 (ProdLp p α β) :=
  { Prod.module with }

/-- The product of two normed spaces is a normed space, with the `L^p` norm. -/
instance instNormedSpace :
    NormedSpace 𝕜 (ProdLp p α β) :=
  { instModule p 𝕜 α β with
    norm_smul_le := fun c f => by
      rcases p.dichotomy with (rfl | hp)
      · letI : Module 𝕜 (ProdLp ∞ α β) := Prod.module
        suffices ‖c • f‖₊ = ‖c‖₊ * ‖f‖₊ by exact_mod_cast NNReal.coe_mono this.le
        simp only [nnnorm_eq_sup, NNReal.mul_sup, ← nnnorm_smul]
        rfl
      · have : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel' 1 (zero_lt_one.trans_le hp).ne'
        have smul_fst : (c • f).fst = c • f.fst := rfl
        have smul_snd : (c • f).snd = c • f.snd := rfl
        simp only [norm_eq_add (zero_lt_one.trans_le hp), norm_smul, Real.mul_rpow, norm_nonneg,
          smul_fst, smul_snd]
        rw [← mul_add, mul_rpow (rpow_nonneg_of_nonneg (norm_nonneg _) _),
          ← rpow_mul (norm_nonneg _), this, Real.rpow_one]
        positivity }

section towers

variable [NormedSpace 𝕜' α] [NormedSpace 𝕜' β]

instance instIsScalarTower [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' α] [IsScalarTower 𝕜 𝕜' β] :
    IsScalarTower 𝕜 𝕜' (ProdLp p α β) :=
  Prod.isScalarTower

instance instSMulCommClass [SMulCommClass 𝕜 𝕜' α] [SMulCommClass 𝕜 𝕜' β] :
    SMulCommClass 𝕜 𝕜' (ProdLp p α β) :=
  Prod.smulCommClass

end towers

instance instFiniteDimensional [FiniteDimensional 𝕜 α] [FiniteDimensional 𝕜 β] :
    FiniteDimensional 𝕜 (ProdLp p α β) :=
  Module.Finite.prod

end normed_space_inst

/- Register simplification lemmas for the applications of `ProdLp` elements, as the usual lemmas
for Prod types will not trigger. -/
variable {𝕜 𝕜' p α β}
variable [SeminormedAddCommGroup α] [NormedSpace 𝕜 α]
  [SeminormedAddCommGroup β] [NormedSpace 𝕜 β]

section algebra

variable (x y : ProdLp p α β) (c : 𝕜)

@[simp]
theorem zero_fst : (0 : ProdLp p α β).fst = 0 :=
  rfl

@[simp]
theorem zero_snd : (0 : ProdLp p α β).snd = 0 :=
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
theorem smul_fst : (c • x).fst = c • x.fst :=
  rfl

@[simp]
theorem smul_snd : (c • x).snd = c • x.snd :=
  rfl

@[simp]
theorem neg_fst : (-x).fst = -x.fst :=
  rfl

@[simp]
theorem neg_snd : (-x).snd = -x.snd :=
  rfl

end algebra

section Equiv

/-- The canonical map `ProdLp.equiv` between `ProdLp ∞ β` and `Π i, β i` as a linear isometric
equivalence. -/
def equivₗᵢ : ProdLp ∞ α β ≃ₗᵢ[𝕜] α × β :=
  { ProdLp.equiv ∞ α β with
    map_add' := fun f g => rfl
    map_smul' := fun c f => rfl
    norm_map' := fun f => by simp }

variable (x y : ProdLp p α β) (x' y' : α × β) (c : 𝕜)

@[simp]
theorem equiv_zero : ProdLp.equiv p α β 0 = 0 :=
  rfl

@[simp]
theorem equiv_symm_zero : (ProdLp.equiv p α β).symm 0 = 0 :=
  rfl

@[simp]
theorem equiv_add : ProdLp.equiv p α β (x + y) = ProdLp.equiv p α β x + ProdLp.equiv p α β y :=
  rfl

@[simp]
theorem equiv_symm_add : (ProdLp.equiv p α β).symm (x' + y') =
    (ProdLp.equiv p α β).symm x' + (ProdLp.equiv p α β).symm y' :=
  rfl

@[simp]
theorem equiv_sub : ProdLp.equiv p α β (x - y) = ProdLp.equiv p α β x - ProdLp.equiv p α β y :=
  rfl

@[simp]
theorem equiv_symm_sub : (ProdLp.equiv p α β).symm (x' - y') =
    (ProdLp.equiv p α β).symm x' - (ProdLp.equiv p α β).symm y' :=
  rfl

@[simp]
theorem equiv_neg : ProdLp.equiv p α β (-x) = -ProdLp.equiv p α β x :=
  rfl

@[simp]
theorem equiv_symm_neg : (ProdLp.equiv p α β).symm (-x') = -(ProdLp.equiv p α β).symm x' :=
  rfl

@[simp]
theorem equiv_smul : ProdLp.equiv p α β (c • x) = c • ProdLp.equiv p α β x :=
  rfl

@[simp]
theorem equiv_symm_smul : (ProdLp.equiv p α β).symm (c • x') = c • (ProdLp.equiv p α β).symm x' :=
  rfl

end Equiv

section Single

variable (p α β)

@[simp]
theorem nnnorm_equiv_symm_fst [hp : Fact (1 ≤ p)] (x : α) :
    ‖(ProdLp.equiv p α β).symm (x, 0)‖₊ = ‖x‖₊ := by
  induction p using ENNReal.recTopCoe generalizing hp with
  | top =>
    simp [nnnorm_eq_sup]
  | coe p =>
    have hp0 : (p : ℝ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 ≤ (p : ℝ≥0∞))).ne'
    simp [nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel hp0]

@[simp]
theorem nnnorm_equiv_symm_snd [hp : Fact (1 ≤ p)] (y : β) :
    ‖(ProdLp.equiv p α β).symm (0, y)‖₊ = ‖y‖₊ := by
  induction p using ENNReal.recTopCoe generalizing hp with
  | top =>
    simp [nnnorm_eq_sup]
  | coe p =>
    have hp0 : (p : ℝ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 ≤ (p : ℝ≥0∞))).ne'
    simp [nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel hp0]

@[simp]
theorem norm_equiv_symm_fst (x : α) : ‖(ProdLp.equiv p α β).symm (x, 0)‖ = ‖x‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_equiv_symm_fst p α β x

@[simp]
theorem norm_equiv_symm_snd (y : β) : ‖(ProdLp.equiv p α β).symm (0, y)‖ = ‖y‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_equiv_symm_snd p α β y

@[simp]
theorem nndist_equiv_symm_single_fst (x₁ x₂ : α) :
    nndist ((ProdLp.equiv p α β).symm (x₁, 0)) ((ProdLp.equiv p α β).symm (x₂, 0)) =
      nndist x₁ x₂ := by
  rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← equiv_symm_sub, Prod.mk_sub_mk, sub_zero,
    nnnorm_equiv_symm_fst]

@[simp]
theorem nndist_equiv_symm_single_snd (y₁ y₂ : β) :
    nndist ((ProdLp.equiv p α β).symm (0, y₁)) ((ProdLp.equiv p α β).symm (0, y₂)) =
      nndist y₁ y₂ := by
  rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← equiv_symm_sub, Prod.mk_sub_mk, sub_zero,
    nnnorm_equiv_symm_snd]

@[simp]
theorem dist_equiv_symm_single_fst (x₁ x₂ : α) :
    dist ((ProdLp.equiv p α β).symm (x₁, 0)) ((ProdLp.equiv p α β).symm (x₂, 0)) =
      dist x₁ x₂ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nndist_equiv_symm_single_fst p α β x₁ x₂

@[simp]
theorem dist_equiv_symm_single_snd (y₁ y₂ : β) :
    dist ((ProdLp.equiv p α β).symm (0, y₁)) ((ProdLp.equiv p α β).symm (0, y₂)) =
      dist y₁ y₂ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nndist_equiv_symm_single_snd p α β y₁ y₂

@[simp]
theorem edist_equiv_symm_single_fst (x₁ x₂ : α) :
    edist ((ProdLp.equiv p α β).symm (x₁, 0)) ((ProdLp.equiv p α β).symm (x₂, 0)) =
      edist x₁ x₂ := by
  simp only [edist_nndist, nndist_equiv_symm_single_fst p α β x₁ x₂]

@[simp]
theorem edist_equiv_symm_single_snd (y₁ y₂ : β) :
    edist ((ProdLp.equiv p α β).symm (0, y₁)) ((ProdLp.equiv p α β).symm (0, y₂)) =
      edist y₁ y₂ := by
  simp only [edist_nndist, nndist_equiv_symm_single_snd p α β y₁ y₂]

end Single

variable (𝕜 p α β)

/-- `ProdLp.equiv` as a linear equivalence. -/
@[simps (config := { fullyApplied := false })]
protected def linearEquiv : ProdLp p α β ≃ₗ[𝕜] α × β :=
  { LinearEquiv.refl _ _ with
    toFun := ProdLp.equiv _ _ _
    invFun := (ProdLp.equiv _ _ _).symm }

/-- `ProdLp.equiv` as a continuous linear equivalence. -/
@[simps! (config := { fullyApplied := false }) apply symm_apply]
protected def continuousLinearEquiv : ProdLp p α β ≃L[𝕜] α × β where
  toLinearEquiv := ProdLp.linearEquiv _ _ _ _
  continuous_toFun := continuous_equiv _ _ _
  continuous_invFun := continuous_equiv_symm _ _ _

end ProdLp
