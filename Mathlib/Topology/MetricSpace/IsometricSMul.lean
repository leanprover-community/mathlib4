/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz

#align_import topology.metric_space.isometric_smul from "leanprover-community/mathlib"@"bc91ed7093bf098d253401e69df601fc33dde156"

/-!
# Group actions by isometries

In this file we define two typeclasses:

- `IsometricSMul M X` says that `M` multiplicatively acts on a (pseudo extended) metric space
  `X` by isometries;
- `IsometricVAdd` is an additive version of `IsometricSMul`.

We also prove basic facts about isometric actions and define bundled isometries
`IsometryEquiv.constSMul`, `IsometryEquiv.mulLeft`, `IsometryEquiv.mulRight`,
`IsometryEquiv.divLeft`, `IsometryEquiv.divRight`, and `IsometryEquiv.inv`, as well as their
additive versions.

If `G` is a group, then `IsometricSMul G G` means that `G` has a left-invariant metric while
`IsometricSMul Gᵐᵒᵖ G` means that `G` has a right-invariant metric. For a commutative group,
these two notions are equivalent. A group with a right-invariant metric can be also represented as a
`NormedGroup`.
-/


open Set

open ENNReal Pointwise

universe u v w

variable (M : Type u) (G : Type v) (X : Type w)

/-- An additive action is isometric if each map `x ↦ c +ᵥ x` is an isometry. -/
class IsometricVAdd [PseudoEMetricSpace X] [VAdd M X] : Prop where
  protected isometry_vadd : ∀ c : M, Isometry ((c +ᵥ ·) : X → X)
#align has_isometric_vadd IsometricVAdd

/-- A multiplicative action is isometric if each map `x ↦ c • x` is an isometry. -/
@[to_additive]
class IsometricSMul [PseudoEMetricSpace X] [SMul M X] : Prop where
  protected isometry_smul : ∀ c : M, Isometry ((c • ·) : X → X)
#align has_isometric_smul IsometricSMul

-- Porting note: Lean 4 doesn't support `[]` in classes, so make a lemma instead of `export`ing
@[to_additive]
theorem isometry_smul {M : Type u} (X : Type w) [PseudoEMetricSpace X] [SMul M X]
    [IsometricSMul M X] (c : M) : Isometry (c • · : X → X) :=
  IsometricSMul.isometry_smul c

@[to_additive]
instance (priority := 100) IsometricSMul.to_continuousConstSMul [PseudoEMetricSpace X] [SMul M X]
    [IsometricSMul M X] : ContinuousConstSMul M X :=
  ⟨fun c => (isometry_smul X c).continuous⟩
#align has_isometric_smul.to_has_continuous_const_smul IsometricSMul.to_continuousConstSMul
#align has_isometric_vadd.to_has_continuous_const_vadd IsometricVAdd.to_continuousConstVAdd

@[to_additive]
instance (priority := 100) IsometricSMul.opposite_of_comm [PseudoEMetricSpace X] [SMul M X]
    [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] [IsometricSMul M X] : IsometricSMul Mᵐᵒᵖ X :=
  ⟨fun c x y => by simpa only [← op_smul_eq_smul] using isometry_smul X c.unop x y⟩
#align has_isometric_smul.opposite_of_comm IsometricSMul.opposite_of_comm
#align has_isometric_vadd.opposite_of_comm IsometricVAdd.opposite_of_comm

variable {M G X}

section EMetric

variable [PseudoEMetricSpace X] [Group G] [MulAction G X] [IsometricSMul G X]

@[to_additive (attr := simp)]
theorem edist_smul_left [SMul M X] [IsometricSMul M X] (c : M) (x y : X) :
    edist (c • x) (c • y) = edist x y :=
  isometry_smul X c x y
#align edist_smul_left edist_smul_left
#align edist_vadd_left edist_vadd_left

@[to_additive (attr := simp)]
theorem ediam_smul [SMul M X] [IsometricSMul M X] (c : M) (s : Set X) :
    EMetric.diam (c • s) = EMetric.diam s :=
  (isometry_smul _ _).ediam_image s
#align ediam_smul ediam_smul
#align ediam_vadd ediam_vadd

@[to_additive]
theorem isometry_mul_left [Mul M] [PseudoEMetricSpace M] [IsometricSMul M M] (a : M) :
    Isometry (a * ·) :=
  isometry_smul M a
#align isometry_mul_left isometry_mul_left
#align isometry_add_left isometry_add_left

@[to_additive (attr := simp)]
theorem edist_mul_left [Mul M] [PseudoEMetricSpace M] [IsometricSMul M M] (a b c : M) :
    edist (a * b) (a * c) = edist b c :=
  isometry_mul_left a b c
#align edist_mul_left edist_mul_left
#align edist_add_left edist_add_left

@[to_additive]
theorem isometry_mul_right [Mul M] [PseudoEMetricSpace M] [IsometricSMul Mᵐᵒᵖ M] (a : M) :
    Isometry fun x => x * a :=
  isometry_smul M (MulOpposite.op a)
#align isometry_mul_right isometry_mul_right
#align isometry_add_right isometry_add_right

@[to_additive (attr := simp)]
theorem edist_mul_right [Mul M] [PseudoEMetricSpace M] [IsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    edist (a * c) (b * c) = edist a b :=
  isometry_mul_right c a b
#align edist_mul_right edist_mul_right
#align edist_add_right edist_add_right

@[to_additive (attr := simp)]
theorem edist_div_right [DivInvMonoid M] [PseudoEMetricSpace M] [IsometricSMul Mᵐᵒᵖ M]
    (a b c : M) : edist (a / c) (b / c) = edist a b := by
  simp only [div_eq_mul_inv, edist_mul_right]
#align edist_div_right edist_div_right
#align edist_sub_right edist_sub_right

@[to_additive (attr := simp)]
theorem edist_inv_inv [PseudoEMetricSpace G] [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G]
    (a b : G) : edist a⁻¹ b⁻¹ = edist a b := by
  rw [← edist_mul_left a, ← edist_mul_right _ _ b, mul_right_inv, one_mul, inv_mul_cancel_right,
    edist_comm]
#align edist_inv_inv edist_inv_inv
#align edist_neg_neg edist_neg_neg

@[to_additive]
theorem isometry_inv [PseudoEMetricSpace G] [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G] :
    Isometry (Inv.inv : G → G) :=
  edist_inv_inv
#align isometry_inv isometry_inv
#align isometry_neg isometry_neg

@[to_additive]
theorem edist_inv [PseudoEMetricSpace G] [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G]
    (x y : G) : edist x⁻¹ y = edist x y⁻¹ := by rw [← edist_inv_inv, inv_inv]
#align edist_inv edist_inv
#align edist_neg edist_neg

@[to_additive (attr := simp)]
theorem edist_div_left [PseudoEMetricSpace G] [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G]
    (a b c : G) : edist (a / b) (a / c) = edist b c := by
  rw [div_eq_mul_inv, div_eq_mul_inv, edist_mul_left, edist_inv_inv]
#align edist_div_left edist_div_left
#align edist_sub_left edist_sub_left

namespace IsometryEquiv

/-- If a group `G` acts on `X` by isometries, then `IsometryEquiv.constSMul` is the isometry of
`X` given by multiplication of a constant element of the group. -/
@[to_additive (attr := simps! toEquiv apply) "If an additive group `G` acts on `X` by isometries,
then `IsometryEquiv.constVAdd` is the isometry of `X` given by addition of a constant element of the
group."]
def constSMul (c : G) : X ≃ᵢ X where
  toEquiv := MulAction.toPerm c
  isometry_toFun := isometry_smul X c
#align isometry_equiv.const_smul IsometryEquiv.constSMul
#align isometry_equiv.const_vadd IsometryEquiv.constVAdd
#align isometry_equiv.const_smul_to_equiv IsometryEquiv.constSMul_toEquiv
#align isometry_equiv.const_smul_apply IsometryEquiv.constSMul_apply
#align isometry_equiv.const_vadd_to_equiv IsometryEquiv.constVAdd_toEquiv
#align isometry_equiv.const_vadd_apply IsometryEquiv.constVAdd_apply

@[to_additive (attr := simp)]
theorem constSMul_symm (c : G) : (constSMul c : X ≃ᵢ X).symm = constSMul c⁻¹ :=
  ext fun _ => rfl
#align isometry_equiv.const_smul_symm IsometryEquiv.constSMul_symm
#align isometry_equiv.const_vadd_symm IsometryEquiv.constVAdd_symm

variable [PseudoEMetricSpace G]

/-- Multiplication `y ↦ x * y` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply toEquiv) "Addition `y ↦ x + y` as an `IsometryEquiv`."]
def mulLeft [IsometricSMul G G] (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.mulLeft c
  isometry_toFun := edist_mul_left c
#align isometry_equiv.mul_left IsometryEquiv.mulLeft
#align isometry_equiv.add_left IsometryEquiv.addLeft
#align isometry_equiv.mul_left_apply IsometryEquiv.mulLeft_apply
#align isometry_equiv.mul_left_to_equiv IsometryEquiv.mulLeft_toEquiv
#align isometry_equiv.add_left_apply IsometryEquiv.addLeft_apply
#align isometry_equiv.add_left_to_equiv IsometryEquiv.addLeft_toEquiv

@[to_additive (attr := simp)]
theorem mulLeft_symm [IsometricSMul G G] (x : G) :
    (mulLeft x).symm = IsometryEquiv.mulLeft x⁻¹ :=
  constSMul_symm x
#align isometry_equiv.mul_left_symm IsometryEquiv.mulLeft_symm
#align isometry_equiv.add_left_symm IsometryEquiv.addLeft_symm

/-- Multiplication `y ↦ y * x` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply toEquiv) "Addition `y ↦ y + x` as an `IsometryEquiv`."]
def mulRight [IsometricSMul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.mulRight c
  isometry_toFun a b := edist_mul_right a b c
#align isometry_equiv.mul_right IsometryEquiv.mulRight
#align isometry_equiv.add_right IsometryEquiv.addRight
#align isometry_equiv.mul_right_apply IsometryEquiv.mulRight_apply
#align isometry_equiv.mul_right_to_equiv IsometryEquiv.mulRight_toEquiv
#align isometry_equiv.add_right_apply IsometryEquiv.addRight_apply
#align isometry_equiv.add_right_to_equiv IsometryEquiv.addRight_toEquiv

@[to_additive (attr := simp)]
theorem mulRight_symm [IsometricSMul Gᵐᵒᵖ G] (x : G) : (mulRight x).symm = mulRight x⁻¹ :=
  ext fun _ => rfl
#align isometry_equiv.mul_right_symm IsometryEquiv.mulRight_symm
#align isometry_equiv.add_right_symm IsometryEquiv.addRight_symm

/-- Division `y ↦ y / x` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply toEquiv) "Subtraction `y ↦ y - x` as an `IsometryEquiv`."]
def divRight [IsometricSMul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.divRight c
  isometry_toFun a b := edist_div_right a b c
#align isometry_equiv.div_right IsometryEquiv.divRight
#align isometry_equiv.sub_right IsometryEquiv.subRight
#align isometry_equiv.div_right_apply IsometryEquiv.divRight_apply
#align isometry_equiv.div_right_to_equiv IsometryEquiv.divRight_toEquiv
#align isometry_equiv.sub_right_apply IsometryEquiv.subRight_apply
#align isometry_equiv.sub_right_to_equiv IsometryEquiv.subRight_toEquiv

@[to_additive (attr := simp)]
theorem divRight_symm [IsometricSMul Gᵐᵒᵖ G] (c : G) : (divRight c).symm = mulRight c :=
  ext fun _ => rfl
#align isometry_equiv.div_right_symm IsometryEquiv.divRight_symm
#align isometry_equiv.sub_right_symm IsometryEquiv.subRight_symm

variable [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G]

/-- Division `y ↦ x / y` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply symm_apply toEquiv)
  "Subtraction `y ↦ x - y` as an `IsometryEquiv`."]
def divLeft (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.divLeft c
  isometry_toFun := edist_div_left c
#align isometry_equiv.div_left IsometryEquiv.divLeft
#align isometry_equiv.sub_left IsometryEquiv.subLeft
#align isometry_equiv.div_left_apply IsometryEquiv.divLeft_apply
#align isometry_equiv.div_left_symm_apply IsometryEquiv.divLeft_symm_apply
#align isometry_equiv.div_left_to_equiv IsometryEquiv.divLeft_toEquiv
#align isometry_equiv.sub_left_apply IsometryEquiv.subLeft_apply
#align isometry_equiv.sub_left_symm_apply IsometryEquiv.subLeft_symm_apply
#align isometry_equiv.sub_left_to_equiv IsometryEquiv.subLeft_toEquiv

variable (G)

/-- Inversion `x ↦ x⁻¹` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply toEquiv) "Negation `x ↦ -x` as an `IsometryEquiv`."]
def inv : G ≃ᵢ G where
  toEquiv := Equiv.inv G
  isometry_toFun := edist_inv_inv
#align isometry_equiv.inv IsometryEquiv.inv
#align isometry_equiv.neg IsometryEquiv.neg
#align isometry_equiv.inv_apply IsometryEquiv.inv_apply
#align isometry_equiv.inv_to_equiv IsometryEquiv.inv_toEquiv
#align isometry_equiv.neg_apply IsometryEquiv.neg_apply
#align isometry_equiv.neg_to_equiv IsometryEquiv.neg_toEquiv

@[to_additive (attr := simp)] theorem inv_symm : (inv G).symm = inv G := rfl
#align isometry_equiv.inv_symm IsometryEquiv.inv_symm
#align isometry_equiv.neg_symm IsometryEquiv.neg_symm

end IsometryEquiv

namespace EMetric

@[to_additive (attr := simp)]
theorem smul_ball (c : G) (x : X) (r : ℝ≥0∞) : c • ball x r = ball (c • x) r :=
  (IsometryEquiv.constSMul c).image_emetric_ball _ _
#align emetric.smul_ball EMetric.smul_ball
#align emetric.vadd_ball EMetric.vadd_ball

@[to_additive (attr := simp)]
theorem preimage_smul_ball (c : G) (x : X) (r : ℝ≥0∞) :
    (c • ·) ⁻¹' ball x r = ball (c⁻¹ • x) r := by
  rw [preimage_smul, smul_ball]
#align emetric.preimage_smul_ball EMetric.preimage_smul_ball
#align emetric.preimage_vadd_ball EMetric.preimage_vadd_ball

@[to_additive (attr := simp)]
theorem smul_closedBall (c : G) (x : X) (r : ℝ≥0∞) : c • closedBall x r = closedBall (c • x) r :=
  (IsometryEquiv.constSMul c).image_emetric_closedBall _ _
#align emetric.smul_closed_ball EMetric.smul_closedBall
#align emetric.vadd_closed_ball EMetric.vadd_closedBall

@[to_additive (attr := simp)]
theorem preimage_smul_closedBall (c : G) (x : X) (r : ℝ≥0∞) :
    (c • ·) ⁻¹' closedBall x r = closedBall (c⁻¹ • x) r := by
  rw [preimage_smul, smul_closedBall]
#align emetric.preimage_smul_closed_ball EMetric.preimage_smul_closedBall
#align emetric.preimage_vadd_closed_ball EMetric.preimage_vadd_closedBall

variable [PseudoEMetricSpace G]

@[to_additive (attr := simp)]
theorem preimage_mul_left_ball [IsometricSMul G G] (a b : G) (r : ℝ≥0∞) :
    (a * ·) ⁻¹' ball b r = ball (a⁻¹ * b) r :=
  preimage_smul_ball a b r
#align emetric.preimage_mul_left_ball EMetric.preimage_mul_left_ball
#align emetric.preimage_add_left_ball EMetric.preimage_add_left_ball

@[to_additive (attr := simp)]
theorem preimage_mul_right_ball [IsometricSMul Gᵐᵒᵖ G] (a b : G) (r : ℝ≥0∞) :
    (fun x => x * a) ⁻¹' ball b r = ball (b / a) r := by
  rw [div_eq_mul_inv]
  exact preimage_smul_ball (MulOpposite.op a) b r
#align emetric.preimage_mul_right_ball EMetric.preimage_mul_right_ball
#align emetric.preimage_add_right_ball EMetric.preimage_add_right_ball

@[to_additive (attr := simp)]
theorem preimage_mul_left_closedBall [IsometricSMul G G] (a b : G) (r : ℝ≥0∞) :
    (a * ·) ⁻¹' closedBall b r = closedBall (a⁻¹ * b) r :=
  preimage_smul_closedBall a b r
#align emetric.preimage_mul_left_closed_ball EMetric.preimage_mul_left_closedBall
#align emetric.preimage_add_left_closed_ball EMetric.preimage_add_left_closedBall

@[to_additive (attr := simp)]
theorem preimage_mul_right_closedBall [IsometricSMul Gᵐᵒᵖ G] (a b : G) (r : ℝ≥0∞) :
    (fun x => x * a) ⁻¹' closedBall b r = closedBall (b / a) r := by
  rw [div_eq_mul_inv]
  exact preimage_smul_closedBall (MulOpposite.op a) b r
#align emetric.preimage_mul_right_closed_ball EMetric.preimage_mul_right_closedBall
#align emetric.preimage_add_right_closed_ball EMetric.preimage_add_right_closedBall

end EMetric

end EMetric

@[to_additive (attr := simp)]
theorem dist_smul [PseudoMetricSpace X] [SMul M X] [IsometricSMul M X] (c : M) (x y : X) :
    dist (c • x) (c • y) = dist x y :=
  (isometry_smul X c).dist_eq x y
#align dist_smul dist_smul
#align dist_vadd dist_vadd

@[to_additive (attr := simp)]
theorem nndist_smul [PseudoMetricSpace X] [SMul M X] [IsometricSMul M X] (c : M) (x y : X) :
    nndist (c • x) (c • y) = nndist x y :=
  (isometry_smul X c).nndist_eq x y
#align nndist_smul nndist_smul
#align nndist_vadd nndist_vadd

@[to_additive (attr := simp)]
theorem diam_smul [PseudoMetricSpace X] [SMul M X] [IsometricSMul M X] (c : M) (s : Set X) :
    Metric.diam (c • s) = Metric.diam s :=
  (isometry_smul _ _).diam_image s
#align diam_smul diam_smul
#align diam_vadd diam_vadd

@[to_additive (attr := simp)]
theorem dist_mul_left [PseudoMetricSpace M] [Mul M] [IsometricSMul M M] (a b c : M) :
    dist (a * b) (a * c) = dist b c :=
  dist_smul a b c
#align dist_mul_left dist_mul_left
#align dist_add_left dist_add_left

@[to_additive (attr := simp)]
theorem nndist_mul_left [PseudoMetricSpace M] [Mul M] [IsometricSMul M M] (a b c : M) :
    nndist (a * b) (a * c) = nndist b c :=
  nndist_smul a b c
#align nndist_mul_left nndist_mul_left
#align nndist_add_left nndist_add_left

@[to_additive (attr := simp)]
theorem dist_mul_right [Mul M] [PseudoMetricSpace M] [IsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    dist (a * c) (b * c) = dist a b :=
  dist_smul (MulOpposite.op c) a b
#align dist_mul_right dist_mul_right
#align dist_add_right dist_add_right

@[to_additive (attr := simp)]
theorem nndist_mul_right [PseudoMetricSpace M] [Mul M] [IsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    nndist (a * c) (b * c) = nndist a b :=
  nndist_smul (MulOpposite.op c) a b
#align nndist_mul_right nndist_mul_right
#align nndist_add_right nndist_add_right

@[to_additive (attr := simp)]
theorem dist_div_right [DivInvMonoid M] [PseudoMetricSpace M] [IsometricSMul Mᵐᵒᵖ M]
    (a b c : M) : dist (a / c) (b / c) = dist a b := by simp only [div_eq_mul_inv, dist_mul_right]
#align dist_div_right dist_div_right
#align dist_sub_right dist_sub_right

@[to_additive (attr := simp)]
theorem nndist_div_right [DivInvMonoid M] [PseudoMetricSpace M] [IsometricSMul Mᵐᵒᵖ M]
    (a b c : M) : nndist (a / c) (b / c) = nndist a b := by
  simp only [div_eq_mul_inv, nndist_mul_right]
#align nndist_div_right nndist_div_right
#align nndist_sub_right nndist_sub_right

@[to_additive (attr := simp)]
theorem dist_inv_inv [Group G] [PseudoMetricSpace G] [IsometricSMul G G]
    [IsometricSMul Gᵐᵒᵖ G] (a b : G) : dist a⁻¹ b⁻¹ = dist a b :=
  (IsometryEquiv.inv G).dist_eq a b
#align dist_inv_inv dist_inv_inv
#align dist_neg_neg dist_neg_neg

@[to_additive (attr := simp)]
theorem nndist_inv_inv [Group G] [PseudoMetricSpace G] [IsometricSMul G G]
    [IsometricSMul Gᵐᵒᵖ G] (a b : G) : nndist a⁻¹ b⁻¹ = nndist a b :=
  (IsometryEquiv.inv G).nndist_eq a b
#align nndist_inv_inv nndist_inv_inv
#align nndist_neg_neg nndist_neg_neg

@[to_additive (attr := simp)]
theorem dist_div_left [Group G] [PseudoMetricSpace G] [IsometricSMul G G]
    [IsometricSMul Gᵐᵒᵖ G] (a b c : G) : dist (a / b) (a / c) = dist b c := by
  simp [div_eq_mul_inv]
#align dist_div_left dist_div_left
#align dist_sub_left dist_sub_left

@[to_additive (attr := simp)]
theorem nndist_div_left [Group G] [PseudoMetricSpace G] [IsometricSMul G G]
    [IsometricSMul Gᵐᵒᵖ G] (a b c : G) : nndist (a / b) (a / c) = nndist b c := by
  simp [div_eq_mul_inv]
#align nndist_div_left nndist_div_left
#align nndist_sub_left nndist_sub_left

/-- If `G` acts isometrically on `X`, then the image of a bounded set in `X` under scalar
multiplication by `c : G` is bounded. See also `Bornology.IsBounded.smul₀` for a similar lemma about
normed spaces. -/
@[to_additive "Given an additive isometric action of `G` on `X`, the image of a bounded set in `X`
under translation by `c : G` is bounded"]
theorem Bornology.IsBounded.smul [PseudoMetricSpace X] [SMul G X] [IsometricSMul G X] {s : Set X}
    (hs : IsBounded s) (c : G) : IsBounded (c • s) :=
  (isometry_smul X c).lipschitz.isBounded_image hs

namespace Metric

variable [PseudoMetricSpace X] [Group G] [MulAction G X] [IsometricSMul G X]

@[to_additive (attr := simp)]
theorem smul_ball (c : G) (x : X) (r : ℝ) : c • ball x r = ball (c • x) r :=
  (IsometryEquiv.constSMul c).image_ball _ _
#align metric.smul_ball Metric.smul_ball
#align metric.vadd_ball Metric.vadd_ball

@[to_additive (attr := simp)]
theorem preimage_smul_ball (c : G) (x : X) (r : ℝ) : (c • ·) ⁻¹' ball x r = ball (c⁻¹ • x) r := by
  rw [preimage_smul, smul_ball]
#align metric.preimage_smul_ball Metric.preimage_smul_ball
#align metric.preimage_vadd_ball Metric.preimage_vadd_ball

@[to_additive (attr := simp)]
theorem smul_closedBall (c : G) (x : X) (r : ℝ) : c • closedBall x r = closedBall (c • x) r :=
  (IsometryEquiv.constSMul c).image_closedBall _ _
#align metric.smul_closed_ball Metric.smul_closedBall
#align metric.vadd_closed_ball Metric.vadd_closedBall

@[to_additive (attr := simp)]
theorem preimage_smul_closedBall (c : G) (x : X) (r : ℝ) :
    (c • ·) ⁻¹' closedBall x r = closedBall (c⁻¹ • x) r := by rw [preimage_smul, smul_closedBall]
#align metric.preimage_smul_closed_ball Metric.preimage_smul_closedBall
#align metric.preimage_vadd_closed_ball Metric.preimage_vadd_closedBall

@[to_additive (attr := simp)]
theorem smul_sphere (c : G) (x : X) (r : ℝ) : c • sphere x r = sphere (c • x) r :=
  (IsometryEquiv.constSMul c).image_sphere _ _
#align metric.smul_sphere Metric.smul_sphere
#align metric.vadd_sphere Metric.vadd_sphere

@[to_additive (attr := simp)]
theorem preimage_smul_sphere (c : G) (x : X) (r : ℝ) :
    (c • ·) ⁻¹' sphere x r = sphere (c⁻¹ • x) r := by rw [preimage_smul, smul_sphere]
#align metric.preimage_smul_sphere Metric.preimage_smul_sphere
#align metric.preimage_vadd_sphere Metric.preimage_vadd_sphere

variable [PseudoMetricSpace G]

@[to_additive (attr := simp)]
theorem preimage_mul_left_ball [IsometricSMul G G] (a b : G) (r : ℝ) :
    (a * ·) ⁻¹' ball b r = ball (a⁻¹ * b) r :=
  preimage_smul_ball a b r
#align metric.preimage_mul_left_ball Metric.preimage_mul_left_ball
#align metric.preimage_add_left_ball Metric.preimage_add_left_ball

@[to_additive (attr := simp)]
theorem preimage_mul_right_ball [IsometricSMul Gᵐᵒᵖ G] (a b : G) (r : ℝ) :
    (fun x => x * a) ⁻¹' ball b r = ball (b / a) r := by
  rw [div_eq_mul_inv]
  exact preimage_smul_ball (MulOpposite.op a) b r
#align metric.preimage_mul_right_ball Metric.preimage_mul_right_ball
#align metric.preimage_add_right_ball Metric.preimage_add_right_ball

@[to_additive (attr := simp)]
theorem preimage_mul_left_closedBall [IsometricSMul G G] (a b : G) (r : ℝ) :
    (a * ·) ⁻¹' closedBall b r = closedBall (a⁻¹ * b) r :=
  preimage_smul_closedBall a b r
#align metric.preimage_mul_left_closed_ball Metric.preimage_mul_left_closedBall
#align metric.preimage_add_left_closed_ball Metric.preimage_add_left_closedBall

@[to_additive (attr := simp)]
theorem preimage_mul_right_closedBall [IsometricSMul Gᵐᵒᵖ G] (a b : G) (r : ℝ) :
    (fun x => x * a) ⁻¹' closedBall b r = closedBall (b / a) r := by
  rw [div_eq_mul_inv]
  exact preimage_smul_closedBall (MulOpposite.op a) b r
#align metric.preimage_mul_right_closed_ball Metric.preimage_mul_right_closedBall
#align metric.preimage_add_right_closed_ball Metric.preimage_add_right_closedBall

end Metric

section Instances

variable {Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [SMul M X]
  [IsometricSMul M X]

@[to_additive]
instance [SMul M Y] [IsometricSMul M Y] : IsometricSMul M (X × Y) :=
  ⟨fun c => (isometry_smul X c).prod_map (isometry_smul Y c)⟩

@[to_additive]
instance Prod.isometricSMul' {N} [Mul M] [PseudoEMetricSpace M] [IsometricSMul M M] [Mul N]
    [PseudoEMetricSpace N] [IsometricSMul N N] : IsometricSMul (M × N) (M × N) :=
  ⟨fun c => (isometry_smul M c.1).prod_map (isometry_smul N c.2)⟩
#align prod.has_isometric_smul' Prod.isometricSMul'
#align prod.has_isometric_vadd' Prod.isometricVAdd'

@[to_additive]
instance Prod.isometricSMul'' {N} [Mul M] [PseudoEMetricSpace M] [IsometricSMul Mᵐᵒᵖ M]
    [Mul N] [PseudoEMetricSpace N] [IsometricSMul Nᵐᵒᵖ N] :
    IsometricSMul (M × N)ᵐᵒᵖ (M × N) :=
  ⟨fun c => (isometry_mul_right c.unop.1).prod_map (isometry_mul_right c.unop.2)⟩
#align prod.has_isometric_smul'' Prod.isometricSMul''
#align prod.has_isometric_vadd'' Prod.isometricVAdd''

@[to_additive]
instance Units.isometricSMul [Monoid M] : IsometricSMul Mˣ X :=
  ⟨fun c => isometry_smul X (c : M)⟩
#align units.has_isometric_smul Units.isometricSMul
#align add_units.has_isometric_vadd AddUnits.isometricVAdd

@[to_additive]
instance : IsometricSMul M Xᵐᵒᵖ :=
  ⟨fun c x y => by simpa only using edist_smul_left c x.unop y.unop⟩

@[to_additive]
instance ULift.isometricSMul : IsometricSMul (ULift M) X :=
  ⟨fun c => by simpa only using isometry_smul X c.down⟩
#align ulift.has_isometric_smul ULift.isometricSMul
#align ulift.has_isometric_vadd ULift.isometricVAdd

@[to_additive]
instance ULift.isometricSMul' : IsometricSMul M (ULift X) :=
  ⟨fun c x y => by simpa only using edist_smul_left c x.1 y.1⟩
#align ulift.has_isometric_smul' ULift.isometricSMul'
#align ulift.has_isometric_vadd' ULift.isometricVAdd'

@[to_additive]
instance {ι} {X : ι → Type*} [Fintype ι] [∀ i, SMul M (X i)] [∀ i, PseudoEMetricSpace (X i)]
    [∀ i, IsometricSMul M (X i)] : IsometricSMul M (∀ i, X i) :=
  ⟨fun c => isometry_dcomp (fun _ => (c • ·)) fun i => isometry_smul (X i) c⟩

@[to_additive]
instance Pi.isometricSMul' {ι} {M X : ι → Type*} [Fintype ι] [∀ i, SMul (M i) (X i)]
    [∀ i, PseudoEMetricSpace (X i)] [∀ i, IsometricSMul (M i) (X i)] :
    IsometricSMul (∀ i, M i) (∀ i, X i) :=
  ⟨fun c => isometry_dcomp (fun i => (c i • ·)) fun _ => isometry_smul _ _⟩
#align pi.has_isometric_smul' Pi.isometricSMul'
#align pi.has_isometric_vadd' Pi.isometricVAdd'

@[to_additive]
instance Pi.isometricSMul'' {ι} {M : ι → Type*} [Fintype ι] [∀ i, Mul (M i)]
    [∀ i, PseudoEMetricSpace (M i)] [∀ i, IsometricSMul (M i)ᵐᵒᵖ (M i)] :
    IsometricSMul (∀ i, M i)ᵐᵒᵖ (∀ i, M i) :=
  ⟨fun c => isometry_dcomp (fun i (x : M i) => x * c.unop i) fun _ => isometry_mul_right _⟩
#align pi.has_isometric_smul'' Pi.isometricSMul''
#align pi.has_isometric_vadd'' Pi.isometricVAdd''

instance Additive.isometricVAdd : IsometricVAdd (Additive M) X :=
  ⟨fun c => isometry_smul X (toMul c)⟩
#align additive.has_isometric_vadd Additive.isometricVAdd

instance Additive.isometricVAdd' [Mul M] [PseudoEMetricSpace M] [IsometricSMul M M] :
    IsometricVAdd (Additive M) (Additive M) :=
  ⟨fun c x y => edist_smul_left (toMul c) (toMul x) (toMul y)⟩
#align additive.has_isometric_vadd' Additive.isometricVAdd'

instance Additive.isometricVAdd'' [Mul M] [PseudoEMetricSpace M] [IsometricSMul Mᵐᵒᵖ M] :
    IsometricVAdd (Additive M)ᵃᵒᵖ (Additive M) :=
  ⟨fun c x y => edist_smul_left (MulOpposite.op (toMul c.unop)) (toMul x) (toMul y)⟩
#align additive.has_isometric_vadd'' Additive.isometricVAdd''

instance Multiplicative.isometricSMul {M X} [VAdd M X] [PseudoEMetricSpace X]
    [IsometricVAdd M X] : IsometricSMul (Multiplicative M) X :=
  ⟨fun c => isometry_vadd X (toAdd c)⟩
#align multiplicative.has_isometric_smul Multiplicative.isometricSMul

instance Multiplicative.isometricSMul' [Add M] [PseudoEMetricSpace M] [IsometricVAdd M M] :
    IsometricSMul (Multiplicative M) (Multiplicative M) :=
  ⟨fun c x y => edist_vadd_left (toAdd c) (toAdd x) (toAdd y)⟩
#align multiplicative.has_isometric_smul' Multiplicative.isometricSMul'

instance Multiplicative.isometricVAdd'' [Add M] [PseudoEMetricSpace M]
    [IsometricVAdd Mᵃᵒᵖ M] : IsometricSMul (Multiplicative M)ᵐᵒᵖ (Multiplicative M) :=
  ⟨fun c x y => edist_vadd_left (AddOpposite.op (toAdd c.unop)) (toAdd x) (toAdd y)⟩
#align multiplicative.has_isometric_vadd'' Multiplicative.isometricVAdd''

end Instances
