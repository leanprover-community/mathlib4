/-
Copyright (c) 2023 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Sébastien Gouëzel, Jireh Loreaux
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fintype.Order
import Mathlib.LinearAlgebra.Matrix.Basis

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

instance (p : ℝ≥0∞) (α β : Type _) [Inhabited α] [Inhabited β] : Inhabited (ProdLp p α β) :=
  ⟨default, default⟩

@[ext]
protected theorem ProdLp.ext {p : ℝ≥0∞} {α β : Type _} {x y : ProdLp p α β}
    (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y := Prod.ext h1 h2

namespace ProdLp

variable (p : ℝ≥0∞) (𝕜 𝕜' : Type _) (α β : Type _)

/-- Canonical bijection between `PiLp p α` and the original Pi type. We introduce it to be able
to compare the `L^p` and `L^∞` distances through it. -/
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

variable [Fintype ι]

/-!
### Definition of `edist`, `dist` and `norm` on `PiLp`

In this section we define the `edist`, `dist` and `norm` functions on `PiLp p α` without assuming
`[Fact (1 ≤ p)]` or metric properties of the spaces `α i`. This allows us to provide the rewrite
lemmas for each of three cases `p = 0`, `p = ∞` and `0 < p.to_real`.
-/


section Edist

variable [EDist α] [EDist β]

/-- Endowing the space `ProdLp p α β` with the `L^p` edistance. We register this instance
separate from `ProdLp.instPseudoEMetric` since the latter requires the type class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future emetric-like structure on `ProdLp p α β` for `p < 1`
satisfying a relaxed triangle inequality. The terminology for this varies throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*. -/
instance : EDist (ProdLp p α β) where
  edist f g :=
    -- Porting note: can we drop the `_hp` entirely?
    if _hp : p = 0 then 0
    else
      if p = ∞ then edist f.fst g.fst ⊔ edist f.snd g.snd
      else (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)

variable {α β}

variable (x y : ProdLp p α β) (x' : α × β)

theorem edist_eq_card (f g : ProdLp 0 α β) : edist f g = 0 :=
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
from `pi_Lp.pseudo_emetric_space` so it can be used also for `p < 1`. -/
protected theorem edist_self (f : ProdLp p α β) : edist f f = 0 := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp [edist_eq_card]
  · simp [edist_eq_sup]
  · simp [edist_eq_add h, ENNReal.zero_rpow_of_pos h, ENNReal.zero_rpow_of_pos (inv_pos.2 <| h)]

/-- This holds independent of `p` and does not require `[Fact (1 ≤ p)]`. We keep it separate
from `pi_Lp.pseudo_emetric_space` so it can be used also for `p < 1`. -/
protected theorem edist_comm (f g : ProdLp p α β) : edist f g = edist g f := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp only [edist_eq_card, eq_comm, Ne.def]
  · simp only [edist_eq_sup, edist_comm]
  · simp only [edist_eq_add h, edist_comm]

end EdistProp

section Dist

variable [Dist α] [Dist β]

/-- Endowing the space `PiLp p β` with the `L^p` distance. We register this instance
separate from `pi_Lp.pseudo_metric` since the latter requires the type class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future metric-like structure on `PiLp p β` for `p < 1`
satisfying a relaxed triangle inequality. The terminology for this varies throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*. -/
instance : Dist (ProdLp p α β) where
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

/-- Endowing the space `PiLp p β` with the `L^p` norm. We register this instance
separate from `PiLp.seminormedAddCommGroup` since the latter requires the type class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future norm-like structure on `PiLp p β` for `p < 1`
satisfying a relaxed triangle inequality. These are called *quasi-norms*. -/
instance instNorm : Norm (ProdLp p α β) where
  norm f :=
    if _hp : p = 0 then 0 -- { i | f i ≠ 0 }.toFinite.toFinset.card
    else if p = ∞ then ‖f.fst‖ ⊔ ‖f.snd‖
    else (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal)

variable {p β}

theorem norm_eq_card (f : ProdLp 0 α β) : ‖f‖ = 0 :=
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

/-! ### Instances on finite `L^p` products -/


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

/-- pseudoemetric space instance on the product of finitely many pseudoemetric spaces, using the
`L^p` pseudoedistance, and having as uniformity the product uniformity. -/
instance [PseudoEMetricSpace α] [PseudoEMetricSpace β] : PseudoEMetricSpace (ProdLp p α β) :=
  (pseudoEmetricAux p α β).replaceUniformity (aux_uniformity_eq p β).symm

/-- emetric space instance on the product of finitely many emetric spaces, using the `L^p`
edistance, and having as uniformity the product uniformity. -/
instance [EMetricSpace α] [EMetricSpace β] : EMetricSpace (ProdLp p α β) :=
  @EMetricSpace.ofT0PseudoEMetricSpace (ProdLp p α β) _ Prod.instT0Space

/-- pseudometric space instance on the product of finitely many pseudometric spaces, using the
`L^p` distance, and having as uniformity the product uniformity. -/
instance [∀ i, PseudoMetricSpace (β i)] : PseudoMetricSpace (PiLp p β) :=
  ((pseudoMetricAux p β).replaceUniformity (aux_uniformity_eq p β).symm).replaceBornology fun s =>
    Filter.ext_iff.1 (aux_cobounded_eq p β).symm sᶜ

/-- metric space instance on the product of finitely many metric spaces, using the `L^p` distance,
and having as uniformity the product uniformity. -/
instance [∀ i, MetricSpace (α i)] : MetricSpace (PiLp p α) :=
  MetricSpace.ofT0PseudoMetricSpace _
