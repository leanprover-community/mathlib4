/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.ENNReal.Inv
public import Mathlib.Tactic.Basify.Core

/-!
# `basify` for `ℝ≥0∞` and `ℝ≥0`

`ℝ≥0∞` is two constructions away from `ℝ`: it is `WithTop ℝ≥0`, and `ℝ≥0` is the subtype of the
nonnegative reals. This file registers both layers with `basify`, so that a goal about `ℝ≥0∞`
becomes a goal about `ℝ` together with nonnegativity hypotheses.

It also registers real powers and the norms and distances that take values in these types.
-/

public section

open scoped NNReal ENNReal

namespace Mathlib.Tactic.Basify

/-! ### Taking `ℝ≥0∞` and `ℝ≥0` apart -/

attribute [basify_elim] ENNReal.recTopCoe

/-- A `Subtype.mk`-free eliminator for `ℝ≥0`, exposing the underlying real and its nonnegativity. -/
@[elab_as_elim, basify_elim]
def _root_.NNReal.recToNNReal {C : ℝ≥0 → Sort*} (mk : ∀ (x : ℝ) (_nonneg : 0 ≤ x), C x.toNNReal)
    (t : ℝ≥0) : C t :=
  Real.toNNReal_coe (r := t) ▸ mk t t.coe_nonneg

/-! ### Getting rid of `⊤` -/

attribute [basify_simp] top_add add_top ENNReal.top_mul ENNReal.mul_top ENNReal.sub_top
  ENNReal.top_sub_coe ENNReal.inv_top ENNReal.top_div ENNReal.div_top ENNReal.top_pow
  ENNReal.coe_ne_top ENNReal.top_ne_coe ENNReal.coe_lt_top ENNReal.not_lt_top
  ENNReal.toReal_top le_top top_le_iff lt_top_iff_ne_top ENNReal.coe_eq_zero
  ne_eq not_false_eq_true OfNat.ofNat_ne_zero one_ne_zero

/-! ### From `ℝ≥0∞` down to `ℝ≥0`

Coercions `ℝ≥0 → ℝ≥0∞` are pulled outwards until they meet a relation, which then cancels them.
-/

attribute [basify_op ←] ENNReal.coe_zero ENNReal.coe_one
  ENNReal.coe_natCast ENNReal.coe_add ENNReal.coe_mul ENNReal.coe_sub ENNReal.coe_pow
  ENNReal.coe_inv ENNReal.coe_div ENNReal.coe_min ENNReal.coe_max

attribute [basify_simp] ENNReal.coe_inj ENNReal.coe_le_coe ENNReal.coe_lt_coe
  ENNReal.coe_toReal

/-- `ENNReal.coe_ofNat` read from right to left. It is restated here because the `ofNat(n)` on the
right-hand side of `ENNReal.coe_ofNat` is `no_index`ed, which would make the reversed lemma match
against every term. -/
@[basify_op]
theorem ennreal_ofNat_eq_coe (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : ℝ≥0∞) = ((OfNat.ofNat n : ℝ≥0) : ℝ≥0∞) :=
  rfl

/-- The decimal-literal counterpart of `ennreal_ofNat_eq_coe`. Mathlib has no `coe_ofScientific`
for `ℝ≥0∞`, and without one a literal like `1.5` is an atom that nothing can rewrite. -/
@[basify_op]
theorem ennreal_ofScientific_eq_coe (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e : ℝ≥0∞)
      = ((OfScientific.ofScientific m s e : ℝ≥0) : ℝ≥0∞) :=
  rfl

/-! ### From `ℝ≥0` down to `ℝ`

Coercions `ℝ≥0 → ℝ` are pushed inwards until only atoms are left under them.
-/

attribute [basify_simp ←] NNReal.coe_inj NNReal.coe_le_coe NNReal.coe_lt_coe

attribute [basify_simp] Real.coe_toNNReal

attribute [basify_op] NNReal.coe_zero NNReal.coe_one NNReal.coe_ofNat
  NNReal.coe_natCast NNReal.coe_add NNReal.coe_mul NNReal.coe_inv NNReal.coe_div NNReal.coe_pow
  NNReal.coe_max NNReal.coe_min NNReal.coe_sub_def

/-- The decimal-literal counterpart of `NNReal.coe_ofNat`, which Mathlib does not have. -/
@[basify_op]
theorem nnreal_coe_ofScientific (m : ℕ) (s : Bool) (e : ℕ) :
    ((OfScientific.ofScientific m s e : ℝ≥0) : ℝ) = OfScientific.ofScientific m s e :=
  rfl

/-! ### Real powers -/

attribute [basify_op ←] ENNReal.coe_rpow_of_nonneg

attribute [basify_op] NNReal.coe_rpow

/-! ### Norms and distances -/

attribute [basify_op] enorm_eq_nnnorm coe_nnnorm coe_nnnorm' coe_nndist

end Mathlib.Tactic.Basify
