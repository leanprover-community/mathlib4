/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz

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

/-- A multiplicative action is isometric if each map `x ↦ c • x` is an isometry. -/
@[to_additive]
class IsometricSMul [PseudoEMetricSpace X] [SMul M X] : Prop where
  protected isometry_smul : ∀ c : M, Isometry ((c • ·) : X → X)

-- Porting note: Lean 4 doesn't support `[]` in classes, so make a lemma instead of `export`ing
@[to_additive]
theorem isometry_smul {M : Type u} (X : Type w) [PseudoEMetricSpace X] [SMul M X]
    [IsometricSMul M X] (c : M) : Isometry (c • · : X → X) :=
  IsometricSMul.isometry_smul c

@[to_additive]
instance (priority := 100) IsometricSMul.to_continuousConstSMul [PseudoEMetricSpace X] [SMul M X]
    [IsometricSMul M X] : ContinuousConstSMul M X :=
  ⟨fun c => (isometry_smul X c).continuous⟩

@[to_additive]
instance (priority := 100) IsometricSMul.opposite_of_comm [PseudoEMetricSpace X] [SMul M X]
    [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] [IsometricSMul M X] : IsometricSMul Mᵐᵒᵖ X :=
  ⟨fun c x y => by simpa only [← op_smul_eq_smul] using isometry_smul X c.unop x y⟩

variable {M G X}

section EMetric

variable [PseudoEMetricSpace X] [Group G] [MulAction G X] [IsometricSMul G X]

@[to_additive (attr := simp)]
theorem edist_smul_left [SMul M X] [IsometricSMul M X] (c : M) (x y : X) :
    edist (c • x) (c • y) = edist x y :=
  isometry_smul X c x y

@[to_additive (attr := simp)]
theorem ediam_smul [SMul M X] [IsometricSMul M X] (c : M) (s : Set X) :
    EMetric.diam (c • s) = EMetric.diam s :=
  (isometry_smul _ _).ediam_image s

@[to_additive]
theorem isometry_mul_left [Mul M] [PseudoEMetricSpace M] [IsometricSMul M M] (a : M) :
    Isometry (a * ·) :=
  isometry_smul M a

@[to_additive (attr := simp)]
theorem edist_mul_left [Mul M] [PseudoEMetricSpace M] [IsometricSMul M M] (a b c : M) :
    edist (a * b) (a * c) = edist b c :=
  isometry_mul_left a b c

@[to_additive]
theorem isometry_mul_right [Mul M] [PseudoEMetricSpace M] [IsometricSMul Mᵐᵒᵖ M] (a : M) :
    Isometry fun x => x * a :=
  isometry_smul M (MulOpposite.op a)

@[to_additive (attr := simp)]
theorem edist_mul_right [Mul M] [PseudoEMetricSpace M] [IsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    edist (a * c) (b * c) = edist a b :=
  isometry_mul_right c a b

@[to_additive (attr := simp)]
theorem edist_div_right [DivInvMonoid M] [PseudoEMetricSpace M] [IsometricSMul Mᵐᵒᵖ M]
    (a b c : M) : edist (a / c) (b / c) = edist a b := by
  simp only [div_eq_mul_inv, edist_mul_right]

@[to_additive (attr := simp)]
theorem edist_inv_inv [PseudoEMetricSpace G] [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G]
    (a b : G) : edist a⁻¹ b⁻¹ = edist a b := by
  rw [← edist_mul_left a, ← edist_mul_right _ _ b, mul_right_inv, one_mul, inv_mul_cancel_right,
    edist_comm]

@[to_additive]
theorem isometry_inv [PseudoEMetricSpace G] [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G] :
    Isometry (Inv.inv : G → G) :=
  edist_inv_inv

@[to_additive]
theorem edist_inv [PseudoEMetricSpace G] [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G]
    (x y : G) : edist x⁻¹ y = edist x y⁻¹ := by rw [← edist_inv_inv, inv_inv]

@[to_additive (attr := simp)]
theorem edist_div_left [PseudoEMetricSpace G] [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G]
    (a b c : G) : edist (a / b) (a / c) = edist b c := by
  rw [div_eq_mul_inv, div_eq_mul_inv, edist_mul_left, edist_inv_inv]

namespace IsometryEquiv

/-- If a group `G` acts on `X` by isometries, then `IsometryEquiv.constSMul` is the isometry of
`X` given by multiplication of a constant element of the group. -/
@[to_additive (attr := simps! toEquiv apply) "If an additive group `G` acts on `X` by isometries,
then `IsometryEquiv.constVAdd` is the isometry of `X` given by addition of a constant element of the
group."]
def constSMul (c : G) : X ≃ᵢ X where
  toEquiv := MulAction.toPerm c
  isometry_toFun := isometry_smul X c

@[to_additive (attr := simp)]
theorem constSMul_symm (c : G) : (constSMul c : X ≃ᵢ X).symm = constSMul c⁻¹ :=
  ext fun _ => rfl

variable [PseudoEMetricSpace G]

/-- Multiplication `y ↦ x * y` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply toEquiv) "Addition `y ↦ x + y` as an `IsometryEquiv`."]
def mulLeft [IsometricSMul G G] (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.mulLeft c
  isometry_toFun := edist_mul_left c

@[to_additive (attr := simp)]
theorem mulLeft_symm [IsometricSMul G G] (x : G) :
    (mulLeft x).symm = IsometryEquiv.mulLeft x⁻¹ :=
  constSMul_symm x

/-- Multiplication `y ↦ y * x` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply toEquiv) "Addition `y ↦ y + x` as an `IsometryEquiv`."]
def mulRight [IsometricSMul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.mulRight c
  isometry_toFun a b := edist_mul_right a b c

@[to_additive (attr := simp)]
theorem mulRight_symm [IsometricSMul Gᵐᵒᵖ G] (x : G) : (mulRight x).symm = mulRight x⁻¹ :=
  ext fun _ => rfl

/-- Division `y ↦ y / x` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply toEquiv) "Subtraction `y ↦ y - x` as an `IsometryEquiv`."]
def divRight [IsometricSMul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.divRight c
  isometry_toFun a b := edist_div_right a b c

@[to_additive (attr := simp)]
theorem divRight_symm [IsometricSMul Gᵐᵒᵖ G] (c : G) : (divRight c).symm = mulRight c :=
  ext fun _ => rfl

variable [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G]

/-- Division `y ↦ x / y` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply symm_apply toEquiv)
  "Subtraction `y ↦ x - y` as an `IsometryEquiv`."]
def divLeft (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.divLeft c
  isometry_toFun := edist_div_left c

variable (G)

/-- Inversion `x ↦ x⁻¹` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply toEquiv) "Negation `x ↦ -x` as an `IsometryEquiv`."]
def inv : G ≃ᵢ G where
  toEquiv := Equiv.inv G
  isometry_toFun := edist_inv_inv

@[to_additive (attr := simp)] theorem inv_symm : (inv G).symm = inv G := rfl

end IsometryEquiv

namespace EMetric

@[to_additive (attr := simp)]
theorem smul_ball (c : G) (x : X) (r : ℝ≥0∞) : c • ball x r = ball (c • x) r :=
  (IsometryEquiv.constSMul c).image_emetric_ball _ _

@[to_additive (attr := simp)]
theorem preimage_smul_ball (c : G) (x : X) (r : ℝ≥0∞) :
    (c • ·) ⁻¹' ball x r = ball (c⁻¹ • x) r := by
  rw [preimage_smul, smul_ball]

@[to_additive (attr := simp)]
theorem smul_closedBall (c : G) (x : X) (r : ℝ≥0∞) : c • closedBall x r = closedBall (c • x) r :=
  (IsometryEquiv.constSMul c).image_emetric_closedBall _ _

@[to_additive (attr := simp)]
theorem preimage_smul_closedBall (c : G) (x : X) (r : ℝ≥0∞) :
    (c • ·) ⁻¹' closedBall x r = closedBall (c⁻¹ • x) r := by
  rw [preimage_smul, smul_closedBall]

variable [PseudoEMetricSpace G]

@[to_additive (attr := simp)]
theorem preimage_mul_left_ball [IsometricSMul G G] (a b : G) (r : ℝ≥0∞) :
    (a * ·) ⁻¹' ball b r = ball (a⁻¹ * b) r :=
  preimage_smul_ball a b r

@[to_additive (attr := simp)]
theorem preimage_mul_right_ball [IsometricSMul Gᵐᵒᵖ G] (a b : G) (r : ℝ≥0∞) :
    (fun x => x * a) ⁻¹' ball b r = ball (b / a) r := by
  rw [div_eq_mul_inv]
  exact preimage_smul_ball (MulOpposite.op a) b r

@[to_additive (attr := simp)]
theorem preimage_mul_left_closedBall [IsometricSMul G G] (a b : G) (r : ℝ≥0∞) :
    (a * ·) ⁻¹' closedBall b r = closedBall (a⁻¹ * b) r :=
  preimage_smul_closedBall a b r

@[to_additive (attr := simp)]
theorem preimage_mul_right_closedBall [IsometricSMul Gᵐᵒᵖ G] (a b : G) (r : ℝ≥0∞) :
    (fun x => x * a) ⁻¹' closedBall b r = closedBall (b / a) r := by
  rw [div_eq_mul_inv]
  exact preimage_smul_closedBall (MulOpposite.op a) b r

end EMetric

end EMetric

@[to_additive (attr := simp)]
theorem dist_smul [PseudoMetricSpace X] [SMul M X] [IsometricSMul M X] (c : M) (x y : X) :
    dist (c • x) (c • y) = dist x y :=
  (isometry_smul X c).dist_eq x y

@[to_additive (attr := simp)]
theorem nndist_smul [PseudoMetricSpace X] [SMul M X] [IsometricSMul M X] (c : M) (x y : X) :
    nndist (c • x) (c • y) = nndist x y :=
  (isometry_smul X c).nndist_eq x y

@[to_additive (attr := simp)]
theorem diam_smul [PseudoMetricSpace X] [SMul M X] [IsometricSMul M X] (c : M) (s : Set X) :
    Metric.diam (c • s) = Metric.diam s :=
  (isometry_smul _ _).diam_image s

@[to_additive (attr := simp)]
theorem dist_mul_left [PseudoMetricSpace M] [Mul M] [IsometricSMul M M] (a b c : M) :
    dist (a * b) (a * c) = dist b c :=
  dist_smul a b c

@[to_additive (attr := simp)]
theorem nndist_mul_left [PseudoMetricSpace M] [Mul M] [IsometricSMul M M] (a b c : M) :
    nndist (a * b) (a * c) = nndist b c :=
  nndist_smul a b c

@[to_additive (attr := simp)]
theorem dist_mul_right [Mul M] [PseudoMetricSpace M] [IsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    dist (a * c) (b * c) = dist a b :=
  dist_smul (MulOpposite.op c) a b

@[to_additive (attr := simp)]
theorem nndist_mul_right [PseudoMetricSpace M] [Mul M] [IsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    nndist (a * c) (b * c) = nndist a b :=
  nndist_smul (MulOpposite.op c) a b

@[to_additive (attr := simp)]
theorem dist_div_right [DivInvMonoid M] [PseudoMetricSpace M] [IsometricSMul Mᵐᵒᵖ M]
    (a b c : M) : dist (a / c) (b / c) = dist a b := by simp only [div_eq_mul_inv, dist_mul_right]

@[to_additive (attr := simp)]
theorem nndist_div_right [DivInvMonoid M] [PseudoMetricSpace M] [IsometricSMul Mᵐᵒᵖ M]
    (a b c : M) : nndist (a / c) (b / c) = nndist a b := by
  simp only [div_eq_mul_inv, nndist_mul_right]

@[to_additive (attr := simp)]
theorem dist_inv_inv [Group G] [PseudoMetricSpace G] [IsometricSMul G G]
    [IsometricSMul Gᵐᵒᵖ G] (a b : G) : dist a⁻¹ b⁻¹ = dist a b :=
  (IsometryEquiv.inv G).dist_eq a b

@[to_additive (attr := simp)]
theorem nndist_inv_inv [Group G] [PseudoMetricSpace G] [IsometricSMul G G]
    [IsometricSMul Gᵐᵒᵖ G] (a b : G) : nndist a⁻¹ b⁻¹ = nndist a b :=
  (IsometryEquiv.inv G).nndist_eq a b

@[to_additive (attr := simp)]
theorem dist_div_left [Group G] [PseudoMetricSpace G] [IsometricSMul G G]
    [IsometricSMul Gᵐᵒᵖ G] (a b c : G) : dist (a / b) (a / c) = dist b c := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
theorem nndist_div_left [Group G] [PseudoMetricSpace G] [IsometricSMul G G]
    [IsometricSMul Gᵐᵒᵖ G] (a b c : G) : nndist (a / b) (a / c) = nndist b c := by
  simp [div_eq_mul_inv]

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

@[to_additive (attr := simp)]
theorem preimage_smul_ball (c : G) (x : X) (r : ℝ) : (c • ·) ⁻¹' ball x r = ball (c⁻¹ • x) r := by
  rw [preimage_smul, smul_ball]

@[to_additive (attr := simp)]
theorem smul_closedBall (c : G) (x : X) (r : ℝ) : c • closedBall x r = closedBall (c • x) r :=
  (IsometryEquiv.constSMul c).image_closedBall _ _

@[to_additive (attr := simp)]
theorem preimage_smul_closedBall (c : G) (x : X) (r : ℝ) :
    (c • ·) ⁻¹' closedBall x r = closedBall (c⁻¹ • x) r := by rw [preimage_smul, smul_closedBall]

@[to_additive (attr := simp)]
theorem smul_sphere (c : G) (x : X) (r : ℝ) : c • sphere x r = sphere (c • x) r :=
  (IsometryEquiv.constSMul c).image_sphere _ _

@[to_additive (attr := simp)]
theorem preimage_smul_sphere (c : G) (x : X) (r : ℝ) :
    (c • ·) ⁻¹' sphere x r = sphere (c⁻¹ • x) r := by rw [preimage_smul, smul_sphere]

variable [PseudoMetricSpace G]

@[to_additive (attr := simp)]
theorem preimage_mul_left_ball [IsometricSMul G G] (a b : G) (r : ℝ) :
    (a * ·) ⁻¹' ball b r = ball (a⁻¹ * b) r :=
  preimage_smul_ball a b r

@[to_additive (attr := simp)]
theorem preimage_mul_right_ball [IsometricSMul Gᵐᵒᵖ G] (a b : G) (r : ℝ) :
    (fun x => x * a) ⁻¹' ball b r = ball (b / a) r := by
  rw [div_eq_mul_inv]
  exact preimage_smul_ball (MulOpposite.op a) b r

@[to_additive (attr := simp)]
theorem preimage_mul_left_closedBall [IsometricSMul G G] (a b : G) (r : ℝ) :
    (a * ·) ⁻¹' closedBall b r = closedBall (a⁻¹ * b) r :=
  preimage_smul_closedBall a b r

@[to_additive (attr := simp)]
theorem preimage_mul_right_closedBall [IsometricSMul Gᵐᵒᵖ G] (a b : G) (r : ℝ) :
    (fun x => x * a) ⁻¹' closedBall b r = closedBall (b / a) r := by
  rw [div_eq_mul_inv]
  exact preimage_smul_closedBall (MulOpposite.op a) b r

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

@[to_additive]
instance Prod.isometricSMul'' {N} [Mul M] [PseudoEMetricSpace M] [IsometricSMul Mᵐᵒᵖ M]
    [Mul N] [PseudoEMetricSpace N] [IsometricSMul Nᵐᵒᵖ N] :
    IsometricSMul (M × N)ᵐᵒᵖ (M × N) :=
  ⟨fun c => (isometry_mul_right c.unop.1).prod_map (isometry_mul_right c.unop.2)⟩

@[to_additive]
instance Units.isometricSMul [Monoid M] : IsometricSMul Mˣ X :=
  ⟨fun c => isometry_smul X (c : M)⟩

@[to_additive]
instance : IsometricSMul M Xᵐᵒᵖ :=
  ⟨fun c x y => by simpa only using edist_smul_left c x.unop y.unop⟩

@[to_additive]
instance ULift.isometricSMul : IsometricSMul (ULift M) X :=
  ⟨fun c => by simpa only using isometry_smul X c.down⟩

@[to_additive]
instance ULift.isometricSMul' : IsometricSMul M (ULift X) :=
  ⟨fun c x y => by simpa only using edist_smul_left c x.1 y.1⟩

@[to_additive]
instance {ι} {X : ι → Type*} [Fintype ι] [∀ i, SMul M (X i)] [∀ i, PseudoEMetricSpace (X i)]
    [∀ i, IsometricSMul M (X i)] : IsometricSMul M (∀ i, X i) :=
  ⟨fun c => isometry_dcomp (fun _ => (c • ·)) fun i => isometry_smul (X i) c⟩

@[to_additive]
instance Pi.isometricSMul' {ι} {M X : ι → Type*} [Fintype ι] [∀ i, SMul (M i) (X i)]
    [∀ i, PseudoEMetricSpace (X i)] [∀ i, IsometricSMul (M i) (X i)] :
    IsometricSMul (∀ i, M i) (∀ i, X i) :=
  ⟨fun c => isometry_dcomp (fun i => (c i • ·)) fun _ => isometry_smul _ _⟩

@[to_additive]
instance Pi.isometricSMul'' {ι} {M : ι → Type*} [Fintype ι] [∀ i, Mul (M i)]
    [∀ i, PseudoEMetricSpace (M i)] [∀ i, IsometricSMul (M i)ᵐᵒᵖ (M i)] :
    IsometricSMul (∀ i, M i)ᵐᵒᵖ (∀ i, M i) :=
  ⟨fun c => isometry_dcomp (fun i (x : M i) => x * c.unop i) fun _ => isometry_mul_right _⟩

instance Additive.isometricVAdd : IsometricVAdd (Additive M) X :=
  ⟨fun c => isometry_smul X (toMul c)⟩

instance Additive.isometricVAdd' [Mul M] [PseudoEMetricSpace M] [IsometricSMul M M] :
    IsometricVAdd (Additive M) (Additive M) :=
  ⟨fun c x y => edist_smul_left (toMul c) (toMul x) (toMul y)⟩

instance Additive.isometricVAdd'' [Mul M] [PseudoEMetricSpace M] [IsometricSMul Mᵐᵒᵖ M] :
    IsometricVAdd (Additive M)ᵃᵒᵖ (Additive M) :=
  ⟨fun c x y => edist_smul_left (MulOpposite.op (toMul c.unop)) (toMul x) (toMul y)⟩

instance Multiplicative.isometricSMul {M X} [VAdd M X] [PseudoEMetricSpace X]
    [IsometricVAdd M X] : IsometricSMul (Multiplicative M) X :=
  ⟨fun c => isometry_vadd X (toAdd c)⟩

instance Multiplicative.isometricSMul' [Add M] [PseudoEMetricSpace M] [IsometricVAdd M M] :
    IsometricSMul (Multiplicative M) (Multiplicative M) :=
  ⟨fun c x y => edist_vadd_left (toAdd c) (toAdd x) (toAdd y)⟩

instance Multiplicative.isometricVAdd'' [Add M] [PseudoEMetricSpace M]
    [IsometricVAdd Mᵃᵒᵖ M] : IsometricSMul (Multiplicative M)ᵐᵒᵖ (Multiplicative M) :=
  ⟨fun c x y => edist_vadd_left (AddOpposite.op (toAdd c.unop)) (toAdd x) (toAdd y)⟩

end Instances
