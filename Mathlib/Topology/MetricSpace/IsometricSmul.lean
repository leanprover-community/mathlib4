/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.metric_space.isometric_smul
! leanprover-community/mathlib commit 832a8ba8f10f11fea99367c469ff802e69a5b8ec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.MetricSpace.Isometry

/-!
# Group actions by isometries

In this file we define two typeclasses:

- `has_isometric_smul M X` says that `M` multiplicatively acts on a (pseudo extended) metric space
  `X` by isometries;
- `has_isometric_vadd` is an additive version of `has_isometric_smul`.

We also prove basic facts about isometric actions and define bundled isometries
`isometry_equiv.const_mul`, `isometry_equiv.mul_left`, `isometry_equiv.mul_right`,
`isometry_equiv.div_left`, `isometry_equiv.div_right`, and `isometry_equiv.inv`, as well as their
additive versions.

If `G` is a group, then `has_isometric_smul G G` means that `G` has a left-invariant metric while
`has_isometric_smul Gᵐᵒᵖ G` means that `G` has a right-invariant metric. For a commutative group,
these two notions are equivalent. A group with a right-invariant metric can be also represented as a
`normed_group`.
-/


open Set

open ENNReal Pointwise

universe u v w

variable (M : Type u) (G : Type v) (X : Type w)

/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`isometry_vadd] [] -/
/-- An additive action is isometric if each map `x ↦ c +ᵥ x` is an isometry. -/
class HasIsometricVadd [PseudoEMetricSpace X] [VAdd M X] : Prop where
  isometry_vadd : ∀ c : M, Isometry ((· +ᵥ ·) c : X → X)
#align has_isometric_vadd HasIsometricVadd

/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`isometry_smul] [] -/
/-- A multiplicative action is isometric if each map `x ↦ c • x` is an isometry. -/
@[to_additive]
class HasIsometricSmul [PseudoEMetricSpace X] [SMul M X] : Prop where
  isometry_smul : ∀ c : M, Isometry ((· • ·) c : X → X)
#align has_isometric_smul HasIsometricSmul
#align has_isometric_vadd HasIsometricVadd

export HasIsometricVadd (isometry_vadd)

export HasIsometricSmul (isometry_smul)

@[to_additive]
instance (priority := 100) HasIsometricSmul.to_continuousConstSMul [PseudoEMetricSpace X] [SMul M X]
    [HasIsometricSmul M X] : ContinuousConstSMul M X :=
  ⟨fun c => (isometry_smul X c).Continuous⟩
#align has_isometric_smul.to_has_continuous_const_smul HasIsometricSmul.to_continuousConstSMul
#align has_isometric_vadd.to_has_continuous_const_vadd HasIsometricVadd.to_has_continuous_const_vadd

@[to_additive]
instance (priority := 100) HasIsometricSmul.opposite_of_comm [PseudoEMetricSpace X] [SMul M X]
    [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] [HasIsometricSmul M X] : HasIsometricSmul Mᵐᵒᵖ X :=
  ⟨fun c x y => by simpa only [← op_smul_eq_smul] using isometry_smul X c.unop x y⟩
#align has_isometric_smul.opposite_of_comm HasIsometricSmul.opposite_of_comm
#align has_isometric_vadd.opposite_of_comm HasIsometricVadd.opposite_of_comm

variable {M G X}

section Emetric

variable [PseudoEMetricSpace X] [Group G] [MulAction G X] [HasIsometricSmul G X]

@[simp, to_additive]
theorem edist_smul_left [SMul M X] [HasIsometricSmul M X] (c : M) (x y : X) :
    edist (c • x) (c • y) = edist x y :=
  isometry_smul X c x y
#align edist_smul_left edist_smul_left
#align edist_vadd_left edist_vadd_left

@[to_additive]
theorem isometry_mul_left [Mul M] [PseudoEMetricSpace M] [HasIsometricSmul M M] (a : M) :
    Isometry ((· * ·) a) :=
  isometry_smul M a
#align isometry_mul_left isometry_mul_left
#align isometry_add_left isometry_add_left

@[simp, to_additive]
theorem edist_mul_left [Mul M] [PseudoEMetricSpace M] [HasIsometricSmul M M] (a b c : M) :
    edist (a * b) (a * c) = edist b c :=
  isometry_mul_left a b c
#align edist_mul_left edist_mul_left
#align edist_add_left edist_add_left

@[to_additive]
theorem isometry_mul_right [Mul M] [PseudoEMetricSpace M] [HasIsometricSmul Mᵐᵒᵖ M] (a : M) :
    Isometry fun x => x * a :=
  isometry_smul M (MulOpposite.op a)
#align isometry_mul_right isometry_mul_right
#align isometry_add_right isometry_add_right

@[simp, to_additive]
theorem edist_mul_right [Mul M] [PseudoEMetricSpace M] [HasIsometricSmul Mᵐᵒᵖ M] (a b c : M) :
    edist (a * c) (b * c) = edist a b :=
  isometry_mul_right c a b
#align edist_mul_right edist_mul_right
#align edist_add_right edist_add_right

@[simp, to_additive]
theorem edist_div_right [DivInvMonoid M] [PseudoEMetricSpace M] [HasIsometricSmul Mᵐᵒᵖ M]
    (a b c : M) : edist (a / c) (b / c) = edist a b := by
  simp only [div_eq_mul_inv, edist_mul_right]
#align edist_div_right edist_div_right
#align edist_sub_right edist_sub_right

@[simp, to_additive]
theorem edist_inv_inv [PseudoEMetricSpace G] [HasIsometricSmul G G] [HasIsometricSmul Gᵐᵒᵖ G]
    (a b : G) : edist a⁻¹ b⁻¹ = edist a b := by
  rw [← edist_mul_left a, ← edist_mul_right _ _ b, mul_right_inv, one_mul, inv_mul_cancel_right,
    edist_comm]
#align edist_inv_inv edist_inv_inv
#align edist_neg_neg edist_neg_neg

@[to_additive]
theorem isometry_inv [PseudoEMetricSpace G] [HasIsometricSmul G G] [HasIsometricSmul Gᵐᵒᵖ G] :
    Isometry (Inv.inv : G → G) :=
  edist_inv_inv
#align isometry_inv isometry_inv
#align isometry_neg isometry_neg

@[to_additive]
theorem edist_inv [PseudoEMetricSpace G] [HasIsometricSmul G G] [HasIsometricSmul Gᵐᵒᵖ G]
    (x y : G) : edist x⁻¹ y = edist x y⁻¹ := by rw [← edist_inv_inv, inv_inv]
#align edist_inv edist_inv
#align edist_neg edist_neg

@[simp, to_additive]
theorem edist_div_left [PseudoEMetricSpace G] [HasIsometricSmul G G] [HasIsometricSmul Gᵐᵒᵖ G]
    (a b c : G) : edist (a / b) (a / c) = edist b c := by
  rw [div_eq_mul_inv, div_eq_mul_inv, edist_mul_left, edist_inv_inv]
#align edist_div_left edist_div_left
#align edist_sub_left edist_sub_left

namespace IsometryEquiv

/-- If a group `G` acts on `X` by isometries, then `isometry_equiv.const_smul` is the isometry of
`X` given by multiplication of a constant element of the group. -/
@[to_additive
      "If an additive group `G` acts on `X` by isometries, then `isometry_equiv.const_vadd`\nis the isometry of `X` given by addition of a constant element of the group.",
  simps toEquiv apply]
def constSmul (c : G) : X ≃ᵢ X where
  toEquiv := MulAction.toPerm c
  isometry_toFun := isometry_smul X c
#align isometry_equiv.const_smul IsometryEquiv.constSmul
#align isometry_equiv.const_vadd IsometryEquiv.constVadd

@[simp, to_additive]
theorem constSmul_symm (c : G) : (constSmul c : X ≃ᵢ X).symm = constSmul c⁻¹ :=
  ext fun _ => rfl
#align isometry_equiv.const_smul_symm IsometryEquiv.constSmul_symm
#align isometry_equiv.const_vadd_symm IsometryEquiv.const_vadd_symm

variable [PseudoEMetricSpace G]

/-- Multiplication `y ↦ x * y` as an `isometry_equiv`. -/
@[to_additive "Addition `y ↦ x + y` as an `isometry_equiv`.", simps apply toEquiv]
def mulLeft [HasIsometricSmul G G] (c : G) : G ≃ᵢ G
    where
  toEquiv := Equiv.mulLeft c
  isometry_toFun := edist_mul_left c
#align isometry_equiv.mul_left IsometryEquiv.mulLeft
#align isometry_equiv.add_left IsometryEquiv.addLeft

@[simp, to_additive]
theorem mulLeft_symm [HasIsometricSmul G G] (x : G) :
    (mulLeft x).symm = IsometryEquiv.mulLeft x⁻¹ :=
  constSmul_symm x
#align isometry_equiv.mul_left_symm IsometryEquiv.mulLeft_symm
#align isometry_equiv.add_left_symm IsometryEquiv.add_left_symm

--ext $ λ y, rfl
/-- Multiplication `y ↦ y * x` as an `isometry_equiv`. -/
@[to_additive "Addition `y ↦ y + x` as an `isometry_equiv`.", simps apply toEquiv]
def mulRight [HasIsometricSmul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G
    where
  toEquiv := Equiv.mulRight c
  isometry_toFun a b := edist_mul_right a b c
#align isometry_equiv.mul_right IsometryEquiv.mulRight
#align isometry_equiv.add_right IsometryEquiv.addRight

@[simp, to_additive]
theorem mulRight_symm [HasIsometricSmul Gᵐᵒᵖ G] (x : G) : (mulRight x).symm = mulRight x⁻¹ :=
  ext fun y => rfl
#align isometry_equiv.mul_right_symm IsometryEquiv.mulRight_symm
#align isometry_equiv.add_right_symm IsometryEquiv.add_right_symm

/-- Division `y ↦ y / x` as an `isometry_equiv`. -/
@[to_additive "Subtraction `y ↦ y - x` as an `isometry_equiv`.", simps apply toEquiv]
def divRight [HasIsometricSmul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G
    where
  toEquiv := Equiv.divRight c
  isometry_toFun a b := edist_div_right a b c
#align isometry_equiv.div_right IsometryEquiv.divRight
#align isometry_equiv.sub_right IsometryEquiv.subRight

@[simp, to_additive]
theorem divRight_symm [HasIsometricSmul Gᵐᵒᵖ G] (c : G) : (divRight c).symm = mulRight c :=
  ext fun y => rfl
#align isometry_equiv.div_right_symm IsometryEquiv.divRight_symm
#align isometry_equiv.sub_right_symm IsometryEquiv.sub_right_symm

variable [HasIsometricSmul G G] [HasIsometricSmul Gᵐᵒᵖ G]

/-- Division `y ↦ x / y` as an `isometry_equiv`. -/
@[to_additive "Subtraction `y ↦ x - y` as an `isometry_equiv`.", simps apply symm_apply toEquiv]
def divLeft (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.divLeft c
  isometry_toFun := edist_div_left c
#align isometry_equiv.div_left IsometryEquiv.divLeft
#align isometry_equiv.sub_left IsometryEquiv.subLeft

variable (G)

/-- Inversion `x ↦ x⁻¹` as an `isometry_equiv`. -/
@[to_additive "Negation `x ↦ -x` as an `isometry_equiv`.", simps apply toEquiv]
def inv : G ≃ᵢ G where
  toEquiv := Equiv.inv G
  isometry_toFun := edist_inv_inv
#align isometry_equiv.inv IsometryEquiv.inv
#align isometry_equiv.neg IsometryEquiv.neg

@[simp, to_additive]
theorem inv_symm : (inv G).symm = inv G :=
  rfl
#align isometry_equiv.inv_symm IsometryEquiv.inv_symm
#align isometry_equiv.neg_symm IsometryEquiv.neg_symm

end IsometryEquiv

namespace Emetric

@[simp, to_additive]
theorem smul_ball (c : G) (x : X) (r : ℝ≥0∞) : c • ball x r = ball (c • x) r :=
  (IsometryEquiv.constSmul c).image_emetric_ball _ _
#align emetric.smul_ball Emetric.smul_ball
#align emetric.vadd_ball Emetric.vadd_ball

@[simp, to_additive]
theorem preimage_smul_ball (c : G) (x : X) (r : ℝ≥0∞) : (· • ·) c ⁻¹' ball x r = ball (c⁻¹ • x) r :=
  by rw [preimage_smul, smul_ball]
#align emetric.preimage_smul_ball Emetric.preimage_smul_ball
#align emetric.preimage_vadd_ball Emetric.preimage_vadd_ball

@[simp, to_additive]
theorem smul_closedBall (c : G) (x : X) (r : ℝ≥0∞) : c • closedBall x r = closedBall (c • x) r :=
  (IsometryEquiv.constSmul c).image_emetric_closedBall _ _
#align emetric.smul_closed_ball Emetric.smul_closedBall
#align emetric.vadd_closed_ball Emetric.vadd_closedBall

@[simp, to_additive]
theorem preimage_smul_closedBall (c : G) (x : X) (r : ℝ≥0∞) :
    (· • ·) c ⁻¹' closedBall x r = closedBall (c⁻¹ • x) r := by rw [preimage_smul, smul_closed_ball]
#align emetric.preimage_smul_closed_ball Emetric.preimage_smul_closedBall
#align emetric.preimage_vadd_closed_ball Emetric.preimage_vadd_closedBall

variable [PseudoEMetricSpace G]

@[simp, to_additive]
theorem preimage_mul_left_ball [HasIsometricSmul G G] (a b : G) (r : ℝ≥0∞) :
    (· * ·) a ⁻¹' ball b r = ball (a⁻¹ * b) r :=
  preimage_smul_ball a b r
#align emetric.preimage_mul_left_ball Emetric.preimage_mul_left_ball
#align emetric.preimage_add_left_ball Emetric.preimage_add_left_ball

@[simp, to_additive]
theorem preimage_mul_right_ball [HasIsometricSmul Gᵐᵒᵖ G] (a b : G) (r : ℝ≥0∞) :
    (fun x => x * a) ⁻¹' ball b r = ball (b / a) r :=
  by
  rw [div_eq_mul_inv]
  exact preimage_smul_ball (MulOpposite.op a) b r
#align emetric.preimage_mul_right_ball Emetric.preimage_mul_right_ball
#align emetric.preimage_add_right_ball Emetric.preimage_add_right_ball

@[simp, to_additive]
theorem preimage_mul_left_closedBall [HasIsometricSmul G G] (a b : G) (r : ℝ≥0∞) :
    (· * ·) a ⁻¹' closedBall b r = closedBall (a⁻¹ * b) r :=
  preimage_smul_closedBall a b r
#align emetric.preimage_mul_left_closed_ball Emetric.preimage_mul_left_closedBall
#align emetric.preimage_add_left_closed_ball Emetric.preimage_add_left_closedBall

@[simp, to_additive]
theorem preimage_mul_right_closedBall [HasIsometricSmul Gᵐᵒᵖ G] (a b : G) (r : ℝ≥0∞) :
    (fun x => x * a) ⁻¹' closedBall b r = closedBall (b / a) r :=
  by
  rw [div_eq_mul_inv]
  exact preimage_smul_closed_ball (MulOpposite.op a) b r
#align emetric.preimage_mul_right_closed_ball Emetric.preimage_mul_right_closedBall
#align emetric.preimage_add_right_closed_ball Emetric.preimage_add_right_closedBall

end Emetric

end Emetric

@[simp, to_additive]
theorem dist_smul [PseudoMetricSpace X] [SMul M X] [HasIsometricSmul M X] (c : M) (x y : X) :
    dist (c • x) (c • y) = dist x y :=
  (isometry_smul X c).dist_eq x y
#align dist_smul dist_smul
#align dist_vadd dist_vadd

@[simp, to_additive]
theorem nndist_smul [PseudoMetricSpace X] [SMul M X] [HasIsometricSmul M X] (c : M) (x y : X) :
    nndist (c • x) (c • y) = nndist x y :=
  (isometry_smul X c).nndist_eq x y
#align nndist_smul nndist_smul
#align nndist_vadd nndist_vadd

@[simp, to_additive]
theorem dist_mul_left [PseudoMetricSpace M] [Mul M] [HasIsometricSmul M M] (a b c : M) :
    dist (a * b) (a * c) = dist b c :=
  dist_smul a b c
#align dist_mul_left dist_mul_left
#align dist_add_left dist_add_left

@[simp, to_additive]
theorem nndist_mul_left [PseudoMetricSpace M] [Mul M] [HasIsometricSmul M M] (a b c : M) :
    nndist (a * b) (a * c) = nndist b c :=
  nndist_smul a b c
#align nndist_mul_left nndist_mul_left
#align nndist_add_left nndist_add_left

@[simp, to_additive]
theorem dist_mul_right [Mul M] [PseudoMetricSpace M] [HasIsometricSmul Mᵐᵒᵖ M] (a b c : M) :
    dist (a * c) (b * c) = dist a b :=
  dist_smul (MulOpposite.op c) a b
#align dist_mul_right dist_mul_right
#align dist_add_right dist_add_right

@[simp, to_additive]
theorem nndist_mul_right [PseudoMetricSpace M] [Mul M] [HasIsometricSmul Mᵐᵒᵖ M] (a b c : M) :
    nndist (a * c) (b * c) = nndist a b :=
  nndist_smul (MulOpposite.op c) a b
#align nndist_mul_right nndist_mul_right
#align nndist_add_right nndist_add_right

@[simp, to_additive]
theorem dist_div_right [DivInvMonoid M] [PseudoMetricSpace M] [HasIsometricSmul Mᵐᵒᵖ M]
    (a b c : M) : dist (a / c) (b / c) = dist a b := by simp only [div_eq_mul_inv, dist_mul_right]
#align dist_div_right dist_div_right
#align dist_sub_right dist_sub_right

@[simp, to_additive]
theorem nndist_div_right [DivInvMonoid M] [PseudoMetricSpace M] [HasIsometricSmul Mᵐᵒᵖ M]
    (a b c : M) : nndist (a / c) (b / c) = nndist a b := by
  simp only [div_eq_mul_inv, nndist_mul_right]
#align nndist_div_right nndist_div_right
#align nndist_sub_right nndist_sub_right

@[simp, to_additive]
theorem dist_inv_inv [Group G] [PseudoMetricSpace G] [HasIsometricSmul G G]
    [HasIsometricSmul Gᵐᵒᵖ G] (a b : G) : dist a⁻¹ b⁻¹ = dist a b :=
  (IsometryEquiv.inv G).dist_eq a b
#align dist_inv_inv dist_inv_inv
#align dist_neg_neg dist_neg_neg

@[simp, to_additive]
theorem nndist_inv_inv [Group G] [PseudoMetricSpace G] [HasIsometricSmul G G]
    [HasIsometricSmul Gᵐᵒᵖ G] (a b : G) : nndist a⁻¹ b⁻¹ = nndist a b :=
  (IsometryEquiv.inv G).nndist_eq a b
#align nndist_inv_inv nndist_inv_inv
#align nndist_neg_neg nndist_neg_neg

@[simp, to_additive]
theorem dist_div_left [Group G] [PseudoMetricSpace G] [HasIsometricSmul G G]
    [HasIsometricSmul Gᵐᵒᵖ G] (a b c : G) : dist (a / b) (a / c) = dist b c := by
  simp [div_eq_mul_inv]
#align dist_div_left dist_div_left
#align dist_sub_left dist_sub_left

@[simp, to_additive]
theorem nndist_div_left [Group G] [PseudoMetricSpace G] [HasIsometricSmul G G]
    [HasIsometricSmul Gᵐᵒᵖ G] (a b c : G) : nndist (a / b) (a / c) = nndist b c := by
  simp [div_eq_mul_inv]
#align nndist_div_left nndist_div_left
#align nndist_sub_left nndist_sub_left

namespace Metric

variable [PseudoMetricSpace X] [Group G] [MulAction G X] [HasIsometricSmul G X]

@[simp, to_additive]
theorem smul_ball (c : G) (x : X) (r : ℝ) : c • ball x r = ball (c • x) r :=
  (IsometryEquiv.constSmul c).image_ball _ _
#align metric.smul_ball Metric.smul_ball
#align metric.vadd_ball Metric.vadd_ball

@[simp, to_additive]
theorem preimage_smul_ball (c : G) (x : X) (r : ℝ) : (· • ·) c ⁻¹' ball x r = ball (c⁻¹ • x) r := by
  rw [preimage_smul, smul_ball]
#align metric.preimage_smul_ball Metric.preimage_smul_ball
#align metric.preimage_vadd_ball Metric.preimage_vadd_ball

@[simp, to_additive]
theorem smul_closedBall (c : G) (x : X) (r : ℝ) : c • closedBall x r = closedBall (c • x) r :=
  (IsometryEquiv.constSmul c).image_closedBall _ _
#align metric.smul_closed_ball Metric.smul_closedBall
#align metric.vadd_closed_ball Metric.vadd_closedBall

@[simp, to_additive]
theorem preimage_smul_closedBall (c : G) (x : X) (r : ℝ) :
    (· • ·) c ⁻¹' closedBall x r = closedBall (c⁻¹ • x) r := by rw [preimage_smul, smul_closed_ball]
#align metric.preimage_smul_closed_ball Metric.preimage_smul_closedBall
#align metric.preimage_vadd_closed_ball Metric.preimage_vadd_closedBall

@[simp, to_additive]
theorem smul_sphere (c : G) (x : X) (r : ℝ) : c • sphere x r = sphere (c • x) r :=
  (IsometryEquiv.constSmul c).image_sphere _ _
#align metric.smul_sphere Metric.smul_sphere
#align metric.vadd_sphere Metric.vadd_sphere

@[simp, to_additive]
theorem preimage_smul_sphere (c : G) (x : X) (r : ℝ) :
    (· • ·) c ⁻¹' sphere x r = sphere (c⁻¹ • x) r := by rw [preimage_smul, smul_sphere]
#align metric.preimage_smul_sphere Metric.preimage_smul_sphere
#align metric.preimage_vadd_sphere Metric.preimage_vadd_sphere

variable [PseudoMetricSpace G]

@[simp, to_additive]
theorem preimage_mul_left_ball [HasIsometricSmul G G] (a b : G) (r : ℝ) :
    (· * ·) a ⁻¹' ball b r = ball (a⁻¹ * b) r :=
  preimage_smul_ball a b r
#align metric.preimage_mul_left_ball Metric.preimage_mul_left_ball
#align metric.preimage_add_left_ball Metric.preimage_add_left_ball

@[simp, to_additive]
theorem preimage_mul_right_ball [HasIsometricSmul Gᵐᵒᵖ G] (a b : G) (r : ℝ) :
    (fun x => x * a) ⁻¹' ball b r = ball (b / a) r :=
  by
  rw [div_eq_mul_inv]
  exact preimage_smul_ball (MulOpposite.op a) b r
#align metric.preimage_mul_right_ball Metric.preimage_mul_right_ball
#align metric.preimage_add_right_ball Metric.preimage_add_right_ball

@[simp, to_additive]
theorem preimage_mul_left_closedBall [HasIsometricSmul G G] (a b : G) (r : ℝ) :
    (· * ·) a ⁻¹' closedBall b r = closedBall (a⁻¹ * b) r :=
  preimage_smul_closedBall a b r
#align metric.preimage_mul_left_closed_ball Metric.preimage_mul_left_closedBall
#align metric.preimage_add_left_closed_ball Metric.preimage_add_left_closedBall

@[simp, to_additive]
theorem preimage_mul_right_closedBall [HasIsometricSmul Gᵐᵒᵖ G] (a b : G) (r : ℝ) :
    (fun x => x * a) ⁻¹' closedBall b r = closedBall (b / a) r :=
  by
  rw [div_eq_mul_inv]
  exact preimage_smul_closed_ball (MulOpposite.op a) b r
#align metric.preimage_mul_right_closed_ball Metric.preimage_mul_right_closedBall
#align metric.preimage_add_right_closed_ball Metric.preimage_add_right_closedBall

end Metric

section Instances

variable {Y : Type _} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [SMul M X]
  [HasIsometricSmul M X]

@[to_additive]
instance [SMul M Y] [HasIsometricSmul M Y] : HasIsometricSmul M (X × Y) :=
  ⟨fun c => (isometry_smul X c).Prod_map (isometry_smul Y c)⟩

@[to_additive]
instance Prod.has_isometric_smul' {N} [Mul M] [PseudoEMetricSpace M] [HasIsometricSmul M M] [Mul N]
    [PseudoEMetricSpace N] [HasIsometricSmul N N] : HasIsometricSmul (M × N) (M × N) :=
  ⟨fun c => (isometry_smul M c.1).Prod_map (isometry_smul N c.2)⟩
#align prod.has_isometric_smul' Prod.has_isometric_smul'
#align prod.has_isometric_vadd' Prod.has_isometric_vadd'

@[to_additive]
instance Prod.has_isometric_smul'' {N} [Mul M] [PseudoEMetricSpace M] [HasIsometricSmul Mᵐᵒᵖ M]
    [Mul N] [PseudoEMetricSpace N] [HasIsometricSmul Nᵐᵒᵖ N] :
    HasIsometricSmul (M × N)ᵐᵒᵖ (M × N) :=
  ⟨fun c => (isometry_mul_right c.unop.1).Prod_map (isometry_mul_right c.unop.2)⟩
#align prod.has_isometric_smul'' Prod.has_isometric_smul''
#align prod.has_isometric_vadd'' Prod.has_isometric_vadd''

@[to_additive]
instance Units.hasIsometricSmul [Monoid M] : HasIsometricSmul Mˣ X :=
  ⟨fun c => by convert isometry_smul X (c : M)⟩
#align units.has_isometric_smul Units.hasIsometricSmul
#align add_units.has_isometric_vadd AddUnits.has_isometric_vadd

@[to_additive]
instance : HasIsometricSmul M Xᵐᵒᵖ :=
  ⟨fun c x y => by simpa only using edist_smul_left c x.unop y.unop⟩

@[to_additive]
instance ULift.hasIsometricSmul : HasIsometricSmul (ULift M) X :=
  ⟨fun c => by simpa only using isometry_smul X c.down⟩
#align ulift.has_isometric_smul ULift.hasIsometricSmul
#align ulift.has_isometric_vadd ULift.has_isometric_vadd

@[to_additive]
instance ULift.has_isometric_smul' : HasIsometricSmul M (ULift X) :=
  ⟨fun c x y => by simpa only using edist_smul_left c x.1 y.1⟩
#align ulift.has_isometric_smul' ULift.has_isometric_smul'
#align ulift.has_isometric_vadd' ULift.has_isometric_vadd'

@[to_additive]
instance {ι} {X : ι → Type _} [Fintype ι] [∀ i, SMul M (X i)] [∀ i, PseudoEMetricSpace (X i)]
    [∀ i, HasIsometricSmul M (X i)] : HasIsometricSmul M (∀ i, X i) :=
  ⟨fun c => isometry_dcomp (fun i => (· • ·) c) fun i => isometry_smul (X i) c⟩

@[to_additive]
instance Pi.has_isometric_smul' {ι} {M X : ι → Type _} [Fintype ι] [∀ i, SMul (M i) (X i)]
    [∀ i, PseudoEMetricSpace (X i)] [∀ i, HasIsometricSmul (M i) (X i)] :
    HasIsometricSmul (∀ i, M i) (∀ i, X i) :=
  ⟨fun c => isometry_dcomp (fun i => (· • ·) (c i)) fun i => isometry_smul _ _⟩
#align pi.has_isometric_smul' Pi.has_isometric_smul'
#align pi.has_isometric_vadd' Pi.has_isometric_vadd'

@[to_additive]
instance Pi.has_isometric_smul'' {ι} {M : ι → Type _} [Fintype ι] [∀ i, Mul (M i)]
    [∀ i, PseudoEMetricSpace (M i)] [∀ i, HasIsometricSmul (M i)ᵐᵒᵖ (M i)] :
    HasIsometricSmul (∀ i, M i)ᵐᵒᵖ (∀ i, M i) :=
  ⟨fun c => isometry_dcomp (fun i (x : M i) => x * c.unop i) fun i => isometry_mul_right _⟩
#align pi.has_isometric_smul'' Pi.has_isometric_smul''
#align pi.has_isometric_vadd'' Pi.has_isometric_vadd''

instance Additive.hasIsometricVadd : HasIsometricVadd (Additive M) X :=
  ⟨fun c => isometry_smul X c.toMul⟩
#align additive.has_isometric_vadd Additive.hasIsometricVadd

instance Additive.has_isometric_vadd' [Mul M] [PseudoEMetricSpace M] [HasIsometricSmul M M] :
    HasIsometricVadd (Additive M) (Additive M) :=
  ⟨fun c x y => edist_smul_left c.toMul x.toMul y.toMul⟩
#align additive.has_isometric_vadd' Additive.has_isometric_vadd'

instance Additive.has_isometric_vadd'' [Mul M] [PseudoEMetricSpace M] [HasIsometricSmul Mᵐᵒᵖ M] :
    HasIsometricVadd (Additive M)ᵃᵒᵖ (Additive M) :=
  ⟨fun c x y => edist_smul_left (MulOpposite.op c.unop.toMul) x.toMul y.toMul⟩
#align additive.has_isometric_vadd'' Additive.has_isometric_vadd''

instance Multiplicative.hasIsometricSmul {M X} [VAdd M X] [PseudoEMetricSpace X]
    [HasIsometricVadd M X] : HasIsometricSmul (Multiplicative M) X :=
  ⟨fun c => isometry_vadd X c.toAdd⟩
#align multiplicative.has_isometric_smul Multiplicative.hasIsometricSmul

instance Multiplicative.has_isometric_smul' [Add M] [PseudoEMetricSpace M] [HasIsometricVadd M M] :
    HasIsometricSmul (Multiplicative M) (Multiplicative M) :=
  ⟨fun c x y => edist_vadd_left c.toAdd x.toAdd y.toAdd⟩
#align multiplicative.has_isometric_smul' Multiplicative.has_isometric_smul'

instance Multiplicative.has_isometric_vadd'' [Add M] [PseudoEMetricSpace M]
    [HasIsometricVadd Mᵃᵒᵖ M] : HasIsometricSmul (Multiplicative M)ᵐᵒᵖ (Multiplicative M) :=
  ⟨fun c x y => edist_vadd_left (AddOpposite.op c.unop.toAdd) x.toAdd y.toAdd⟩
#align multiplicative.has_isometric_vadd'' Multiplicative.has_isometric_vadd''

end Instances

