/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis, Heather Macbeth
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# (Semi-)linear isometries

In this file we define `LinearIsometry σ₁₂ E E₂` (notation: `E →ₛₗᵢ[σ₁₂] E₂`) to be a semilinear
isometric embedding of `E` into `E₂` and `LinearIsometryEquiv` (notation: `E ≃ₛₗᵢ[σ₁₂] E₂`) to be
a semilinear isometric equivalence between `E` and `E₂`.  The notation for the associated purely
linear concepts is `E →ₗᵢ[R] E₂`, `E ≃ₗᵢ[R] E₂`, and `E →ₗᵢ⋆[R] E₂`, `E ≃ₗᵢ⋆[R] E₂` for
the star-linear versions.

We also prove some trivial lemmas and provide convenience constructors.

Since a lot of elementary properties don't require `‖x‖ = 0 → x = 0` we start setting up the
theory for `SeminormedAddCommGroup` and we specialize to `NormedAddCommGroup` when needed.
-/

open Function Set Topology

variable {R R₂ R₃ R₄ E E₂ E₃ E₄ F 𝓕 : Type*} [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring R₄]
  {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} {σ₁₃ : R →+* R₃} {σ₃₁ : R₃ →+* R} {σ₁₄ : R →+* R₄}
  {σ₄₁ : R₄ →+* R} {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} {σ₂₄ : R₂ →+* R₄} {σ₄₂ : R₄ →+* R₂}
  {σ₃₄ : R₃ →+* R₄} {σ₄₃ : R₄ →+* R₃} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃] [RingHomInvPair σ₂₃ σ₃₂]
  [RingHomInvPair σ₃₂ σ₂₃] [RingHomInvPair σ₁₄ σ₄₁] [RingHomInvPair σ₄₁ σ₁₄]
  [RingHomInvPair σ₂₄ σ₄₂] [RingHomInvPair σ₄₂ σ₂₄] [RingHomInvPair σ₃₄ σ₄₃]
  [RingHomInvPair σ₄₃ σ₃₄] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
  [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
  [RingHomCompTriple σ₄₂ σ₂₁ σ₄₁] [RingHomCompTriple σ₄₃ σ₃₂ σ₄₂] [RingHomCompTriple σ₄₃ σ₃₁ σ₄₁]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [SeminormedAddCommGroup E₃]
  [SeminormedAddCommGroup E₄] [Module R E] [Module R₂ E₂] [Module R₃ E₃] [Module R₄ E₄]
  [NormedAddCommGroup F] [Module R F]

/-- A `σ₁₂`-semilinear isometric embedding of a normed `R`-module into an `R₂`-module,
denoted as `f : E →ₛₗᵢ[σ₁₂] E₂`. -/
structure LinearIsometry (σ₁₂ : R →+* R₂) (E E₂ : Type*) [SeminormedAddCommGroup E]
  [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] extends E →ₛₗ[σ₁₂] E₂ where
  norm_map' : ∀ x, ‖toLinearMap x‖ = ‖x‖

@[inherit_doc]
notation:25 E " →ₛₗᵢ[" σ₁₂:25 "] " E₂:0 => LinearIsometry σ₁₂ E E₂

/-- A linear isometric embedding of a normed `R`-module into another one. -/
notation:25 E " →ₗᵢ[" R:25 "] " E₂:0 => LinearIsometry (RingHom.id R) E E₂

/-- An antilinear isometric embedding of a normed `R`-module into another one. -/
notation:25 E " →ₗᵢ⋆[" R:25 "] " E₂:0 => LinearIsometry (starRingEnd R) E E₂

/-- `SemilinearIsometryClass F σ E E₂` asserts `F` is a type of bundled `σ`-semilinear isometries
`E → E₂`.

See also `LinearIsometryClass F R E E₂` for the case where `σ` is the identity map on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. -/
class SemilinearIsometryClass (𝓕 : Type*) {R R₂ : outParam Type*} [Semiring R] [Semiring R₂]
    (σ₁₂ : outParam <| R →+* R₂) (E E₂ : outParam Type*) [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] [FunLike 𝓕 E E₂] : Prop
    extends SemilinearMapClass 𝓕 σ₁₂ E E₂ where
  norm_map : ∀ (f : 𝓕) (x : E), ‖f x‖ = ‖x‖

/-- `LinearIsometryClass F R E E₂` asserts `F` is a type of bundled `R`-linear isometries
`M → M₂`.

This is an abbreviation for `SemilinearIsometryClass F (RingHom.id R) E E₂`.
-/
abbrev LinearIsometryClass (𝓕 : Type*) (R E E₂ : outParam Type*) [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [Module R E] [Module R E₂]
    [FunLike 𝓕 E E₂] :=
  SemilinearIsometryClass 𝓕 (RingHom.id R) E E₂

namespace SemilinearIsometryClass

variable [FunLike 𝓕 E E₂]

protected theorem isometry [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) : Isometry f :=
  AddMonoidHomClass.isometry_of_norm _ (norm_map _)

@[continuity]
protected theorem continuous [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) : Continuous f :=
  (SemilinearIsometryClass.isometry f).continuous

-- Should be `@[simp]` but it doesn't fire due to https://github.com/leanprover/lean4/issues/3107.
theorem nnnorm_map [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (x : E) : ‖f x‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_map f x

protected theorem lipschitz [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) : LipschitzWith 1 f :=
  (SemilinearIsometryClass.isometry f).lipschitz

protected theorem antilipschitz [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) :
    AntilipschitzWith 1 f :=
  (SemilinearIsometryClass.isometry f).antilipschitz

theorem ediam_image [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (s : Set E) :
    EMetric.diam (f '' s) = EMetric.diam s :=
  (SemilinearIsometryClass.isometry f).ediam_image s

theorem ediam_range [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) :
    EMetric.diam (range f) = EMetric.diam (univ : Set E) :=
  (SemilinearIsometryClass.isometry f).ediam_range

theorem diam_image [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (s : Set E) :
    Metric.diam (f '' s) = Metric.diam s :=
  (SemilinearIsometryClass.isometry f).diam_image s

theorem diam_range [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) :
    Metric.diam (range f) = Metric.diam (univ : Set E) :=
  (SemilinearIsometryClass.isometry f).diam_range

instance (priority := 100) toContinuousSemilinearMapClass
    [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] : ContinuousSemilinearMapClass 𝓕 σ₁₂ E E₂ where
  map_continuous := SemilinearIsometryClass.continuous

end SemilinearIsometryClass

namespace LinearIsometry

variable (f : E →ₛₗᵢ[σ₁₂] E₂) (f₁ : F →ₛₗᵢ[σ₁₂] E₂)

theorem toLinearMap_injective : Injective (toLinearMap : (E →ₛₗᵢ[σ₁₂] E₂) → E →ₛₗ[σ₁₂] E₂)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[simp]
theorem toLinearMap_inj {f g : E →ₛₗᵢ[σ₁₂] E₂} : f.toLinearMap = g.toLinearMap ↔ f = g :=
  toLinearMap_injective.eq_iff

instance instFunLike : FunLike (E →ₛₗᵢ[σ₁₂] E₂) E E₂ where
  coe f := f.toFun
  coe_injective' _ _ h := toLinearMap_injective (DFunLike.coe_injective h)

instance instSemilinearIsometryClass : SemilinearIsometryClass (E →ₛₗᵢ[σ₁₂] E₂) σ₁₂ E E₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := map_smulₛₗ f.toLinearMap
  norm_map f := f.norm_map'

@[simp]
theorem coe_toLinearMap : ⇑f.toLinearMap = f :=
  rfl

@[simp]
theorem coe_mk (f : E →ₛₗ[σ₁₂] E₂) (hf) : ⇑(mk f hf) = f :=
  rfl

theorem coe_injective : @Injective (E →ₛₗᵢ[σ₁₂] E₂) (E → E₂) (fun f => f) := by
  rintro ⟨_⟩ ⟨_⟩
  simp

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (σ₁₂ : R →+* R₂) (E E₂ : Type*) [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] (h : E →ₛₗᵢ[σ₁₂] E₂) : E → E₂ :=
  h

initialize_simps_projections LinearIsometry (toFun → apply)

@[ext]
theorem ext {f g : E →ₛₗᵢ[σ₁₂] E₂} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h

variable [FunLike 𝓕 E E₂]

protected theorem map_zero : f 0 = 0 :=
  f.toLinearMap.map_zero

protected theorem map_add (x y : E) : f (x + y) = f x + f y :=
  f.toLinearMap.map_add x y

protected theorem map_neg (x : E) : f (-x) = -f x :=
  f.toLinearMap.map_neg x

protected theorem map_sub (x y : E) : f (x - y) = f x - f y :=
  f.toLinearMap.map_sub x y

protected theorem map_smulₛₗ (c : R) (x : E) : f (c • x) = σ₁₂ c • f x :=
  f.toLinearMap.map_smulₛₗ c x

protected theorem map_smul [Module R E₂] (f : E →ₗᵢ[R] E₂) (c : R) (x : E) : f (c • x) = c • f x :=
  f.toLinearMap.map_smul c x

@[simp]
theorem norm_map (x : E) : ‖f x‖ = ‖x‖ :=
  SemilinearIsometryClass.norm_map f x

@[simp] -- Should be replaced with `SemilinearIsometryClass.nnorm_map` when https://github.com/leanprover/lean4/issues/3107 is fixed.
theorem nnnorm_map (x : E) : ‖f x‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_map f x

@[simp] -- Should be replaced with `SemilinearIsometryClass.enorm_map` when https://github.com/leanprover/lean4/issues/3107 is fixed.
theorem enorm_map (x : E) : ‖f x‖ₑ = ‖x‖ₑ := by
  simp [enorm]

protected theorem isometry : Isometry f :=
  AddMonoidHomClass.isometry_of_norm f.toLinearMap (norm_map _)

lemma isEmbedding (f : F →ₛₗᵢ[σ₁₂] E₂) : IsEmbedding f := f.isometry.isEmbedding

-- Should be `@[simp]` but it doesn't fire due to https://github.com/leanprover/lean4/issues/3107.
theorem isComplete_image_iff [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) {s : Set E} :
    IsComplete (f '' s) ↔ IsComplete s :=
  _root_.isComplete_image_iff (SemilinearIsometryClass.isometry f).isUniformInducing

@[simp] -- Should be replaced with `LinearIsometry.isComplete_image_iff` when https://github.com/leanprover/lean4/issues/3107 is fixed.
theorem isComplete_image_iff' (f : LinearIsometry σ₁₂ E E₂) {s : Set E} :
    IsComplete (f '' s) ↔ IsComplete s :=
  LinearIsometry.isComplete_image_iff _

theorem isComplete_map_iff [RingHomSurjective σ₁₂] {p : Submodule R E} :
    IsComplete (p.map f.toLinearMap : Set E₂) ↔ IsComplete (p : Set E) :=
  isComplete_image_iff f

theorem isComplete_map_iff' [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) [RingHomSurjective σ₁₂]
    {p : Submodule R E} : IsComplete (p.map f : Set E₂) ↔ IsComplete (p : Set E) :=
  isComplete_image_iff f

instance completeSpace_map [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) [RingHomSurjective σ₁₂]
    (p : Submodule R E) [CompleteSpace p] : CompleteSpace (p.map f) :=
  ((isComplete_map_iff' f).2 <| completeSpace_coe_iff_isComplete.1 ‹_›).completeSpace_coe

instance completeSpace_map' [RingHomSurjective σ₁₂] (p : Submodule R E) [CompleteSpace p] :
    CompleteSpace (p.map f.toLinearMap) :=
  (f.isComplete_map_iff.2 <| completeSpace_coe_iff_isComplete.1 ‹_›).completeSpace_coe

@[simp]
theorem dist_map (x y : E) : dist (f x) (f y) = dist x y :=
  f.isometry.dist_eq x y

@[simp]
theorem edist_map (x y : E) : edist (f x) (f y) = edist x y :=
  f.isometry.edist_eq x y

protected theorem injective : Injective f₁ :=
  Isometry.injective (LinearIsometry.isometry f₁)

@[simp]
theorem map_eq_iff {x y : F} : f₁ x = f₁ y ↔ x = y :=
  f₁.injective.eq_iff

theorem map_ne {x y : F} (h : x ≠ y) : f₁ x ≠ f₁ y :=
  f₁.injective.ne h

protected theorem lipschitz : LipschitzWith 1 f :=
  f.isometry.lipschitz

protected theorem antilipschitz : AntilipschitzWith 1 f :=
  f.isometry.antilipschitz

@[continuity]
protected theorem continuous : Continuous f :=
  f.isometry.continuous

@[simp]
theorem preimage_ball (x : E) (r : ℝ) : f ⁻¹' Metric.ball (f x) r = Metric.ball x r :=
  f.isometry.preimage_ball x r

@[simp]
theorem preimage_sphere (x : E) (r : ℝ) : f ⁻¹' Metric.sphere (f x) r = Metric.sphere x r :=
  f.isometry.preimage_sphere x r

@[simp]
theorem preimage_closedBall (x : E) (r : ℝ) :
    f ⁻¹' Metric.closedBall (f x) r = Metric.closedBall x r :=
  f.isometry.preimage_closedBall x r

theorem ediam_image (s : Set E) : EMetric.diam (f '' s) = EMetric.diam s :=
  f.isometry.ediam_image s

theorem ediam_range : EMetric.diam (range f) = EMetric.diam (univ : Set E) :=
  f.isometry.ediam_range

theorem diam_image (s : Set E) : Metric.diam (f '' s) = Metric.diam s :=
  Isometry.diam_image (LinearIsometry.isometry f) s

theorem diam_range : Metric.diam (range f) = Metric.diam (univ : Set E) :=
  Isometry.diam_range (LinearIsometry.isometry f)

/-- Interpret a linear isometry as a continuous linear map. -/
def toContinuousLinearMap : E →SL[σ₁₂] E₂ :=
  ⟨f.toLinearMap, f.continuous⟩

theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap : _ → E →SL[σ₁₂] E₂) := fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toContinuousLinearMap = _)

@[simp]
theorem toContinuousLinearMap_inj {f g : E →ₛₗᵢ[σ₁₂] E₂} :
    f.toContinuousLinearMap = g.toContinuousLinearMap ↔ f = g :=
  toContinuousLinearMap_injective.eq_iff

@[simp]
theorem coe_toContinuousLinearMap : ⇑f.toContinuousLinearMap = f :=
  rfl

@[simp]
theorem comp_continuous_iff {α : Type*} [TopologicalSpace α] {g : α → E} :
    Continuous (f ∘ g) ↔ Continuous g :=
  f.isometry.comp_continuous_iff

/-- The identity linear isometry. -/
def id : E →ₗᵢ[R] E :=
  ⟨LinearMap.id, fun _ => rfl⟩

@[simp, norm_cast]
theorem coe_id : ((id : E →ₗᵢ[R] E) : E → E) = _root_.id :=
  rfl

@[simp]
theorem id_apply (x : E) : (id : E →ₗᵢ[R] E) x = x :=
  rfl

@[simp]
theorem id_toLinearMap : (id.toLinearMap : E →ₗ[R] E) = LinearMap.id :=
  rfl

@[simp]
theorem id_toContinuousLinearMap : id.toContinuousLinearMap = ContinuousLinearMap.id R E :=
  rfl

instance instInhabited : Inhabited (E →ₗᵢ[R] E) := ⟨id⟩

/-- Composition of linear isometries. -/
def comp (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (f : E →ₛₗᵢ[σ₁₂] E₂) : E →ₛₗᵢ[σ₁₃] E₃ :=
  ⟨g.toLinearMap.comp f.toLinearMap, fun _ => (norm_map g _).trans (norm_map f _)⟩

@[simp]
theorem coe_comp (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (f : E →ₛₗᵢ[σ₁₂] E₂) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp]
theorem id_comp : (id : E₂ →ₗᵢ[R₂] E₂).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id : f.comp id = f :=
  ext fun _ => rfl

theorem comp_assoc (f : E₃ →ₛₗᵢ[σ₃₄] E₄) (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (h : E →ₛₗᵢ[σ₁₂] E₂) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

instance instMonoid : Monoid (E →ₗᵢ[R] E) where
  one := id
  mul := comp
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

@[simp]
theorem coe_one : ((1 : E →ₗᵢ[R] E) : E → E) = _root_.id :=
  rfl

@[simp]
theorem coe_mul (f g : E →ₗᵢ[R] E) : ⇑(f * g) = f ∘ g :=
  rfl

theorem one_def : (1 : E →ₗᵢ[R] E) = id :=
  rfl

theorem mul_def (f g : E →ₗᵢ[R] E) : (f * g : E →ₗᵢ[R] E) = f.comp g :=
  rfl

theorem coe_pow (f : E →ₗᵢ[R] E) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

end LinearIsometry

/-- Construct a `LinearIsometry` from a `LinearMap` satisfying `Isometry`. -/
def LinearMap.toLinearIsometry (f : E →ₛₗ[σ₁₂] E₂) (hf : Isometry f) : E →ₛₗᵢ[σ₁₂] E₂ :=
  { f with
    norm_map' := by
      simp_rw [← dist_zero_right]
      simpa using (hf.dist_eq · 0) }

namespace Submodule

variable {R' : Type*} [Ring R'] [Module R' E] (p : Submodule R' E)

/-- `Submodule.subtype` as a `LinearIsometry`. -/
def subtypeₗᵢ : p →ₗᵢ[R'] E :=
  ⟨p.subtype, fun _ => rfl⟩

@[simp]
theorem coe_subtypeₗᵢ : ⇑p.subtypeₗᵢ = p.subtype :=
  rfl

@[simp]
theorem subtypeₗᵢ_toLinearMap : p.subtypeₗᵢ.toLinearMap = p.subtype :=
  rfl

@[simp]
theorem subtypeₗᵢ_toContinuousLinearMap : p.subtypeₗᵢ.toContinuousLinearMap = p.subtypeL :=
  rfl

end Submodule

/-- A semilinear isometric equivalence between two normed vector spaces,
denoted as `f : E ≃ₛₗᵢ[σ₁₂] E₂`. -/
structure LinearIsometryEquiv (σ₁₂ : R →+* R₂) {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] (E E₂ : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂]
  [Module R E] [Module R₂ E₂] extends E ≃ₛₗ[σ₁₂] E₂ where
  norm_map' : ∀ x, ‖toLinearEquiv x‖ = ‖x‖

@[inherit_doc]
notation:25 E " ≃ₛₗᵢ[" σ₁₂:25 "] " E₂:0 => LinearIsometryEquiv σ₁₂ E E₂

/-- A linear isometric equivalence between two normed vector spaces. -/
notation:25 E " ≃ₗᵢ[" R:25 "] " E₂:0 => LinearIsometryEquiv (RingHom.id R) E E₂

/-- An antilinear isometric equivalence between two normed vector spaces. -/
notation:25 E " ≃ₗᵢ⋆[" R:25 "] " E₂:0 => LinearIsometryEquiv (starRingEnd R) E E₂

/-- `SemilinearIsometryEquivClass F σ E E₂` asserts `F` is a type of bundled `σ`-semilinear
isometric equivs `E → E₂`.

See also `LinearIsometryEquivClass F R E E₂` for the case where `σ` is the identity map on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. -/
class SemilinearIsometryEquivClass (𝓕 : Type*) {R R₂ : outParam Type*} [Semiring R]
  [Semiring R₂] (σ₁₂ : outParam <| R →+* R₂) {σ₂₁ : outParam <| R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] (E E₂ : outParam Type*) [SeminormedAddCommGroup E]
  [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] [EquivLike 𝓕 E E₂] : Prop
  extends SemilinearEquivClass 𝓕 σ₁₂ E E₂ where
  norm_map : ∀ (f : 𝓕) (x : E), ‖f x‖ = ‖x‖

/-- `LinearIsometryEquivClass F R E E₂` asserts `F` is a type of bundled `R`-linear isometries
`M → M₂`.

This is an abbreviation for `SemilinearIsometryEquivClass F (RingHom.id R) E E₂`.
-/
abbrev LinearIsometryEquivClass (𝓕 : Type*) (R E E₂ : outParam Type*) [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [Module R E] [Module R E₂]
    [EquivLike 𝓕 E E₂] :=
  SemilinearIsometryEquivClass 𝓕 (RingHom.id R) E E₂

namespace SemilinearIsometryEquivClass

variable (𝓕)

-- `σ₂₁` becomes a metavariable, but it's OK since it's an outparam
instance (priority := 100) toSemilinearIsometryClass [EquivLike 𝓕 E E₂]
    [s : SemilinearIsometryEquivClass 𝓕 σ₁₂ E E₂] : SemilinearIsometryClass 𝓕 σ₁₂ E E₂ :=
  { s with }

end SemilinearIsometryEquivClass

namespace LinearIsometryEquiv

variable (e : E ≃ₛₗᵢ[σ₁₂] E₂)

theorem toLinearEquiv_injective : Injective (toLinearEquiv : (E ≃ₛₗᵢ[σ₁₂] E₂) → E ≃ₛₗ[σ₁₂] E₂)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[simp]
theorem toLinearEquiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} : f.toLinearEquiv = g.toLinearEquiv ↔ f = g :=
  toLinearEquiv_injective.eq_iff

instance instEquivLike : EquivLike (E ≃ₛₗᵢ[σ₁₂] E₂) E E₂ where
  coe e := e.toFun
  inv e := e.invFun
  coe_injective' f g h₁ h₂ := by
    obtain ⟨f', _⟩ := f
    obtain ⟨g', _⟩ := g
    cases f'
    cases g'
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, DFunLike.coe_fn_eq] at h₁
    congr
  left_inv e := e.left_inv
  right_inv e := e.right_inv

instance instSemilinearIsometryEquivClass :
    SemilinearIsometryEquivClass (E ≃ₛₗᵢ[σ₁₂] E₂) σ₁₂ E E₂ where
  map_add f := map_add f.toLinearEquiv
  map_smulₛₗ e := map_smulₛₗ e.toLinearEquiv
  norm_map e := e.norm_map'

/-- Shortcut instance, saving 8.5% of compilation time in
`Mathlib/Analysis/InnerProductSpace/Adjoint.lean`.

(This instance was pinpointed by benchmarks; we didn't do an in depth investigation why it is
specifically needed.)
-/
instance instCoeFun : CoeFun (E ≃ₛₗᵢ[σ₁₂] E₂) fun _ ↦ E → E₂ := ⟨DFunLike.coe⟩

theorem coe_injective : @Function.Injective (E ≃ₛₗᵢ[σ₁₂] E₂) (E → E₂) (↑) :=
  DFunLike.coe_injective

@[simp]
theorem coe_mk (e : E ≃ₛₗ[σ₁₂] E₂) (he : ∀ x, ‖e x‖ = ‖x‖) : ⇑(mk e he) = e :=
  rfl

@[simp]
theorem coe_toLinearEquiv (e : E ≃ₛₗᵢ[σ₁₂] E₂) : ⇑e.toLinearEquiv = e :=
  rfl

@[ext]
theorem ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : ∀ x, e x = e' x) : e = e' :=
  toLinearEquiv_injective <| LinearEquiv.ext h

protected theorem congr_arg {f : E ≃ₛₗᵢ[σ₁₂] E₂} : ∀ {x x' : E}, x = x' → f x = f x'
  | _, _, rfl => rfl

protected theorem congr_fun {f g : E ≃ₛₗᵢ[σ₁₂] E₂} (h : f = g) (x : E) : f x = g x :=
  h ▸ rfl

/-- Construct a `LinearIsometryEquiv` from a `LinearEquiv` and two inequalities:
`∀ x, ‖e x‖ ≤ ‖x‖` and `∀ y, ‖e.symm y‖ ≤ ‖y‖`. -/
def ofBounds (e : E ≃ₛₗ[σ₁₂] E₂) (h₁ : ∀ x, ‖e x‖ ≤ ‖x‖) (h₂ : ∀ y, ‖e.symm y‖ ≤ ‖y‖) :
    E ≃ₛₗᵢ[σ₁₂] E₂ :=
  ⟨e, fun x => le_antisymm (h₁ x) <| by simpa only [e.symm_apply_apply] using h₂ (e x)⟩

@[simp]
theorem norm_map (x : E) : ‖e x‖ = ‖x‖ :=
  e.norm_map' x

/-- Reinterpret a `LinearIsometryEquiv` as a `LinearIsometry`. -/
def toLinearIsometry : E →ₛₗᵢ[σ₁₂] E₂ :=
  ⟨e.1, e.2⟩

theorem toLinearIsometry_injective : Function.Injective (toLinearIsometry : _ → E →ₛₗᵢ[σ₁₂] E₂) :=
  fun x _ h => coe_injective (congr_arg _ h : ⇑x.toLinearIsometry = _)

@[simp]
theorem toLinearIsometry_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
    f.toLinearIsometry = g.toLinearIsometry ↔ f = g :=
  toLinearIsometry_injective.eq_iff

@[simp]
theorem coe_toLinearIsometry : ⇑e.toLinearIsometry = e :=
  rfl

protected theorem isometry : Isometry e :=
  e.toLinearIsometry.isometry

/-- Reinterpret a `LinearIsometryEquiv` as an `IsometryEquiv`. -/
def toIsometryEquiv : E ≃ᵢ E₂ :=
  ⟨e.toLinearEquiv.toEquiv, e.isometry⟩

theorem toIsometryEquiv_injective :
    Function.Injective (toIsometryEquiv : (E ≃ₛₗᵢ[σ₁₂] E₂) → E ≃ᵢ E₂) := fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toIsometryEquiv = _)

@[simp]
theorem toIsometryEquiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
    f.toIsometryEquiv = g.toIsometryEquiv ↔ f = g :=
  toIsometryEquiv_injective.eq_iff

@[simp]
theorem coe_toIsometryEquiv : ⇑e.toIsometryEquiv = e :=
  rfl

theorem range_eq_univ (e : E ≃ₛₗᵢ[σ₁₂] E₂) : Set.range e = Set.univ := by
  rw [← coe_toIsometryEquiv]
  exact IsometryEquiv.range_eq_univ _

/-- Reinterpret a `LinearIsometryEquiv` as a `Homeomorph`. -/
def toHomeomorph : E ≃ₜ E₂ :=
  e.toIsometryEquiv.toHomeomorph

theorem toHomeomorph_injective : Function.Injective (toHomeomorph : (E ≃ₛₗᵢ[σ₁₂] E₂) → E ≃ₜ E₂) :=
  fun x _ h => coe_injective (congr_arg _ h : ⇑x.toHomeomorph = _)

@[simp]
theorem toHomeomorph_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} : f.toHomeomorph = g.toHomeomorph ↔ f = g :=
  toHomeomorph_injective.eq_iff

@[simp]
theorem coe_toHomeomorph : ⇑e.toHomeomorph = e :=
  rfl

protected theorem continuous : Continuous e :=
  e.isometry.continuous

protected theorem continuousAt {x} : ContinuousAt e x :=
  e.continuous.continuousAt

protected theorem continuousOn {s} : ContinuousOn e s :=
  e.continuous.continuousOn

protected theorem continuousWithinAt {s x} : ContinuousWithinAt e s x :=
  e.continuous.continuousWithinAt

/-- Interpret a `LinearIsometryEquiv` as a `ContinuousLinearEquiv`. -/
def toContinuousLinearEquiv : E ≃SL[σ₁₂] E₂ :=
  { e.toLinearIsometry.toContinuousLinearMap, e.toHomeomorph with }

theorem toContinuousLinearEquiv_injective :
    Function.Injective (toContinuousLinearEquiv : _ → E ≃SL[σ₁₂] E₂) := fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toContinuousLinearEquiv = _)

@[simp]
theorem toContinuousLinearEquiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
    f.toContinuousLinearEquiv = g.toContinuousLinearEquiv ↔ f = g :=
  toContinuousLinearEquiv_injective.eq_iff

@[simp]
theorem coe_toContinuousLinearEquiv : ⇑e.toContinuousLinearEquiv = e :=
  rfl

variable (R E)

/-- Identity map as a `LinearIsometryEquiv`. -/
def refl : E ≃ₗᵢ[R] E :=
  ⟨LinearEquiv.refl R E, fun _ => rfl⟩

/-- Linear isometry equiv between a space and its lift to another universe. -/
def ulift : ULift E ≃ₗᵢ[R] E :=
  { ContinuousLinearEquiv.ulift with norm_map' := fun _ => rfl }

variable {R E}

instance instInhabited : Inhabited (E ≃ₗᵢ[R] E) := ⟨refl R E⟩

@[simp]
theorem coe_refl : ⇑(refl R E) = id :=
  rfl

/-- The inverse `LinearIsometryEquiv`. -/
def symm : E₂ ≃ₛₗᵢ[σ₂₁] E :=
  ⟨e.toLinearEquiv.symm, fun x =>
    (e.norm_map _).symm.trans <| congr_arg norm <| e.toLinearEquiv.apply_symm_apply x⟩

@[simp]
theorem apply_symm_apply (x : E₂) : e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply x

@[simp]
theorem symm_apply_apply (x : E) : e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply x

theorem map_eq_zero_iff {x : E} : e x = 0 ↔ x = 0 :=
  e.toLinearEquiv.map_eq_zero_iff

@[simp]
theorem symm_symm : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (symm : (E₂ ≃ₛₗᵢ[σ₂₁] E) → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem toLinearEquiv_symm : e.symm.toLinearEquiv = e.toLinearEquiv.symm :=
  rfl

@[simp]
theorem coe_symm_toLinearEquiv : ⇑e.toLinearEquiv.symm = e.symm := rfl

@[simp]
theorem toContinuousLinearEquiv_symm :
    e.symm.toContinuousLinearEquiv = e.toContinuousLinearEquiv.symm := rfl

@[simp]
theorem coe_symm_toContinuousLinearEquiv : ⇑e.toContinuousLinearEquiv.symm = e.symm :=
  rfl

@[simp]
theorem toIsometryEquiv_symm : e.symm.toIsometryEquiv = e.toIsometryEquiv.symm :=
  rfl

@[simp]
theorem coe_symm_toIsometryEquiv : ⇑e.toIsometryEquiv.symm = e.symm := rfl

@[simp]
theorem toHomeomorph_symm : e.symm.toHomeomorph = e.toHomeomorph.symm :=
  rfl

@[simp]
theorem coe_symm_toHomeomorph : ⇑e.toHomeomorph.symm = e.symm := rfl

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (σ₁₂ : R →+* R₂) {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (E E₂ : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [Module R E]
    [Module R₂ E₂] (h : E ≃ₛₗᵢ[σ₁₂] E₂) : E → E₂ :=
  h

/-- See Note [custom simps projection] -/
def Simps.symm_apply (σ₁₂ : R →+* R₂) {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁]
    [RingHomInvPair σ₂₁ σ₁₂] (E E₂ : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂]
    [Module R E] [Module R₂ E₂] (h : E ≃ₛₗᵢ[σ₁₂] E₂) : E₂ → E :=
  h.symm

initialize_simps_projections LinearIsometryEquiv (toFun → apply, invFun → symm_apply)

/-- Composition of `LinearIsometryEquiv`s as a `LinearIsometryEquiv`. -/
def trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : E ≃ₛₗᵢ[σ₁₃] E₃ :=
  ⟨e.toLinearEquiv.trans e'.toLinearEquiv, fun _ => (e'.norm_map _).trans (e.norm_map _)⟩

@[simp]
theorem coe_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
theorem trans_apply (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (c : E) :
    (e₁.trans e₂ : E ≃ₛₗᵢ[σ₁₃] E₃) c = e₂ (e₁ c) :=
  rfl

@[simp]
theorem toLinearEquiv_trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    (e.trans e').toLinearEquiv = e.toLinearEquiv.trans e'.toLinearEquiv :=
  rfl

@[simp]
theorem toIsometryEquiv_trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    (e.trans e').toIsometryEquiv = e.toIsometryEquiv.trans e'.toIsometryEquiv :=
  rfl

@[simp]
theorem toHomeomorph_trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    (e.trans e').toHomeomorph = e.toHomeomorph.trans e'.toHomeomorph :=
  rfl

@[simp]
theorem trans_refl : e.trans (refl R₂ E₂) = e :=
  ext fun _ => rfl

@[simp]
theorem refl_trans : (refl R E).trans e = e :=
  ext fun _ => rfl

@[simp]
theorem self_trans_symm : e.trans e.symm = refl R E :=
  ext e.symm_apply_apply

@[simp]
theorem symm_trans_self : e.symm.trans e = refl R₂ E₂ :=
  ext e.apply_symm_apply

@[simp]
theorem symm_comp_self : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[simp]
theorem self_comp_symm : e ∘ e.symm = id :=
  e.symm.symm_comp_self

@[simp]
theorem symm_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl

theorem coe_symm_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    ⇑(e₁.trans e₂).symm = e₁.symm ∘ e₂.symm :=
  rfl

theorem trans_assoc (eEE₂ : E ≃ₛₗᵢ[σ₁₂] E₂) (eE₂E₃ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (eE₃E₄ : E₃ ≃ₛₗᵢ[σ₃₄] E₄) :
    eEE₂.trans (eE₂E₃.trans eE₃E₄) = (eEE₂.trans eE₂E₃).trans eE₃E₄ :=
  rfl

instance instGroup : Group (E ≃ₗᵢ[R] E) where
  mul e₁ e₂ := e₂.trans e₁
  one := refl _ _
  inv := symm
  one_mul := trans_refl
  mul_one := refl_trans
  mul_assoc _ _ _ := trans_assoc _ _ _
  inv_mul_cancel := self_trans_symm

@[simp]
theorem coe_one : ⇑(1 : E ≃ₗᵢ[R] E) = id :=
  rfl

@[simp]
theorem coe_mul (e e' : E ≃ₗᵢ[R] E) : ⇑(e * e') = e ∘ e' :=
  rfl

@[simp]
theorem coe_inv (e : E ≃ₗᵢ[R] E) : ⇑e⁻¹ = e.symm :=
  rfl

theorem one_def : (1 : E ≃ₗᵢ[R] E) = refl _ _ :=
  rfl

theorem mul_def (e e' : E ≃ₗᵢ[R] E) : (e * e' : E ≃ₗᵢ[R] E) = e'.trans e :=
  rfl

theorem inv_def (e : E ≃ₗᵢ[R] E) : (e⁻¹ : E ≃ₗᵢ[R] E) = e.symm :=
  rfl

/-! Lemmas about mixing the group structure with definitions. Because we have multiple ways to
express `LinearIsometryEquiv.refl`, `LinearIsometryEquiv.symm`, and
`LinearIsometryEquiv.trans`, we want simp lemmas for every combination.
The assumption made here is that if you're using the group structure, you want to preserve it
after simp.

This copies the approach used by the lemmas near `Equiv.Perm.trans_one`. -/


@[simp]
theorem trans_one : e.trans (1 : E₂ ≃ₗᵢ[R₂] E₂) = e :=
  trans_refl _

@[simp]
theorem one_trans : (1 : E ≃ₗᵢ[R] E).trans e = e :=
  refl_trans _

@[simp]
theorem refl_mul (e : E ≃ₗᵢ[R] E) : refl _ _ * e = e :=
  trans_refl _

@[simp]
theorem mul_refl (e : E ≃ₗᵢ[R] E) : e * refl _ _ = e :=
  refl_trans _

/-- Reinterpret a `LinearIsometryEquiv` as a `ContinuousLinearEquiv`. -/
instance instCoeTCContinuousLinearEquiv : CoeTC (E ≃ₛₗᵢ[σ₁₂] E₂) (E ≃SL[σ₁₂] E₂) :=
  ⟨fun e => ⟨e.toLinearEquiv, e.continuous, e.toIsometryEquiv.symm.continuous⟩⟩

instance instCoeTCContinuousLinearMap : CoeTC (E ≃ₛₗᵢ[σ₁₂] E₂) (E →SL[σ₁₂] E₂) :=
  ⟨fun e => ↑(e : E ≃SL[σ₁₂] E₂)⟩

@[simp]
theorem coe_coe : ⇑(e : E ≃SL[σ₁₂] E₂) = e :=
  rfl

@[simp]
theorem coe_coe'' : ⇑(e : E →SL[σ₁₂] E₂) = e :=
  rfl

theorem map_zero : e 0 = 0 :=
  e.1.map_zero

theorem map_add (x y : E) : e (x + y) = e x + e y :=
  e.1.map_add x y

theorem map_sub (x y : E) : e (x - y) = e x - e y :=
  e.1.map_sub x y

theorem map_smulₛₗ (c : R) (x : E) : e (c • x) = σ₁₂ c • e x :=
  e.1.map_smulₛₗ c x

theorem map_smul [Module R E₂] {e : E ≃ₗᵢ[R] E₂} (c : R) (x : E) : e (c • x) = c • e x :=
  e.1.map_smul c x

@[simp] -- Should be replaced with `SemilinearIsometryClass.nnorm_map` when https://github.com/leanprover/lean4/issues/3107 is fixed.
theorem nnnorm_map (x : E) : ‖e x‖₊ = ‖x‖₊ :=
  SemilinearIsometryClass.nnnorm_map e x

@[simp]
theorem dist_map (x y : E) : dist (e x) (e y) = dist x y :=
  e.toLinearIsometry.dist_map x y

@[simp]
theorem edist_map (x y : E) : edist (e x) (e y) = edist x y :=
  e.toLinearIsometry.edist_map x y

protected theorem bijective : Bijective e :=
  e.1.bijective

protected theorem injective : Injective e :=
  e.1.injective

protected theorem surjective : Surjective e :=
  e.1.surjective

theorem map_eq_iff {x y : E} : e x = e y ↔ x = y :=
  e.injective.eq_iff

theorem map_ne {x y : E} (h : x ≠ y) : e x ≠ e y :=
  e.injective.ne h

protected theorem lipschitz : LipschitzWith 1 e :=
  e.isometry.lipschitz

protected theorem antilipschitz : AntilipschitzWith 1 e :=
  e.isometry.antilipschitz

theorem image_eq_preimage (s : Set E) : e '' s = e.symm ⁻¹' s :=
  e.toLinearEquiv.image_eq_preimage s

@[simp]
theorem ediam_image (s : Set E) : EMetric.diam (e '' s) = EMetric.diam s :=
  e.isometry.ediam_image s

@[simp]
theorem diam_image (s : Set E) : Metric.diam (e '' s) = Metric.diam s :=
  e.isometry.diam_image s

@[simp]
theorem preimage_ball (x : E₂) (r : ℝ) : e ⁻¹' Metric.ball x r = Metric.ball (e.symm x) r :=
  e.toIsometryEquiv.preimage_ball x r

@[simp]
theorem preimage_sphere (x : E₂) (r : ℝ) : e ⁻¹' Metric.sphere x r = Metric.sphere (e.symm x) r :=
  e.toIsometryEquiv.preimage_sphere x r

@[simp]
theorem preimage_closedBall (x : E₂) (r : ℝ) :
    e ⁻¹' Metric.closedBall x r = Metric.closedBall (e.symm x) r :=
  e.toIsometryEquiv.preimage_closedBall x r

@[simp]
theorem image_ball (x : E) (r : ℝ) : e '' Metric.ball x r = Metric.ball (e x) r :=
  e.toIsometryEquiv.image_ball x r

@[simp]
theorem image_sphere (x : E) (r : ℝ) : e '' Metric.sphere x r = Metric.sphere (e x) r :=
  e.toIsometryEquiv.image_sphere x r

@[simp]
theorem image_closedBall (x : E) (r : ℝ) : e '' Metric.closedBall x r = Metric.closedBall (e x) r :=
  e.toIsometryEquiv.image_closedBall x r

variable {α : Type*} [TopologicalSpace α]

@[simp]
theorem comp_continuousOn_iff {f : α → E} {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.isometry.comp_continuousOn_iff

@[simp]
theorem comp_continuous_iff {f : α → E} : Continuous (e ∘ f) ↔ Continuous f :=
  e.isometry.comp_continuous_iff

instance completeSpace_map (p : Submodule R E) [CompleteSpace p] :
    CompleteSpace (p.map (e.toLinearEquiv : E →ₛₗ[σ₁₂] E₂)) :=
  e.toLinearIsometry.completeSpace_map' p

/-- Construct a linear isometry equiv from a surjective linear isometry. -/
noncomputable def ofSurjective (f : F →ₛₗᵢ[σ₁₂] E₂) (hfr : Function.Surjective f) :
    F ≃ₛₗᵢ[σ₁₂] E₂ :=
  { LinearEquiv.ofBijective f.toLinearMap ⟨f.injective, hfr⟩ with norm_map' := f.norm_map }

@[simp]
theorem coe_ofSurjective (f : F →ₛₗᵢ[σ₁₂] E₂) (hfr : Function.Surjective f) :
    ⇑(LinearIsometryEquiv.ofSurjective f hfr) = f := by
  ext
  rfl

/-- If a linear isometry has an inverse, it is a linear isometric equivalence. -/
def ofLinearIsometry (f : E →ₛₗᵢ[σ₁₂] E₂) (g : E₂ →ₛₗ[σ₂₁] E)
    (h₁ : f.toLinearMap.comp g = LinearMap.id) (h₂ : g.comp f.toLinearMap = LinearMap.id) :
    E ≃ₛₗᵢ[σ₁₂] E₂ :=
  { toLinearEquiv := LinearEquiv.ofLinear f.toLinearMap g h₁ h₂
    norm_map' := fun x => f.norm_map x }

@[simp]
theorem coe_ofLinearIsometry (f : E →ₛₗᵢ[σ₁₂] E₂) (g : E₂ →ₛₗ[σ₂₁] E)
    (h₁ : f.toLinearMap.comp g = LinearMap.id) (h₂ : g.comp f.toLinearMap = LinearMap.id) :
    (ofLinearIsometry f g h₁ h₂ : E → E₂) = (f : E → E₂) :=
  rfl

@[simp]
theorem coe_ofLinearIsometry_symm (f : E →ₛₗᵢ[σ₁₂] E₂) (g : E₂ →ₛₗ[σ₂₁] E)
    (h₁ : f.toLinearMap.comp g = LinearMap.id) (h₂ : g.comp f.toLinearMap = LinearMap.id) :
    ((ofLinearIsometry f g h₁ h₂).symm : E₂ → E) = (g : E₂ → E) :=
  rfl

variable (R) in
/-- The negation operation on a normed space `E`, considered as a linear isometry equivalence. -/
def neg : E ≃ₗᵢ[R] E :=
  { LinearEquiv.neg R with norm_map' := norm_neg }

@[simp]
theorem coe_neg : (neg R : E → E) = fun x => -x :=
  rfl

@[simp]
theorem symm_neg : (neg R : E ≃ₗᵢ[R] E).symm = neg R :=
  rfl

variable (R E E₂ E₃)

/-- The natural equivalence `(E × E₂) × E₃ ≃ E × (E₂ × E₃)` is a linear isometry. -/
def prodAssoc [Module R E₂] [Module R E₃] : (E × E₂) × E₃ ≃ₗᵢ[R] E × E₂ × E₃ :=
  { LinearEquiv.prodAssoc R E E₂ E₃ with
    norm_map' := by
      rintro ⟨⟨e, f⟩, g⟩
      simp only [LinearEquiv.prodAssoc_apply, AddEquiv.toEquiv_eq_coe,
        Equiv.toFun_as_coe, EquivLike.coe_coe, AddEquiv.coe_prodAssoc,
        Equiv.prodAssoc_apply, Prod.norm_def, max_assoc] }

@[simp]
theorem coe_prodAssoc [Module R E₂] [Module R E₃] :
    (prodAssoc R E E₂ E₃ : (E × E₂) × E₃ → E × E₂ × E₃) = Equiv.prodAssoc E E₂ E₃ :=
  rfl

@[simp]
theorem coe_prodAssoc_symm [Module R E₂] [Module R E₃] :
    ((prodAssoc R E E₂ E₃).symm : E × E₂ × E₃ → (E × E₂) × E₃) = (Equiv.prodAssoc E E₂ E₃).symm :=
  rfl

/-- If `p` is a submodule that is equal to `⊤`, then `LinearIsometryEquiv.ofTop p hp` is the
"identity" equivalence between `p` and `E`. -/
@[simps! toLinearEquiv apply symm_apply_coe]
def ofTop {R : Type*} [Ring R] [Module R E] (p : Submodule R E) (hp : p = ⊤) : p ≃ₗᵢ[R] E :=
  { p.subtypeₗᵢ with toLinearEquiv := LinearEquiv.ofTop p hp }

variable {R E E₂ E₃} {R' : Type*} [Ring R']
variable [Module R' E] (p q : Submodule R' E)

/-- `LinearEquiv.ofEq` as a `LinearIsometryEquiv`. -/
def ofEq (hpq : p = q) : p ≃ₗᵢ[R'] q :=
  { LinearEquiv.ofEq p q hpq with norm_map' := fun _ => rfl }

variable {p q}

@[simp]
theorem coe_ofEq_apply (h : p = q) (x : p) : (ofEq p q h x : E) = x :=
  rfl

@[simp]
theorem ofEq_symm (h : p = q) : (ofEq p q h).symm = ofEq q p h.symm :=
  rfl

@[simp]
theorem ofEq_rfl : ofEq p p rfl = LinearIsometryEquiv.refl R' p := rfl

end LinearIsometryEquiv

/-- Two linear isometries are equal if they are equal on basis vectors. -/
theorem Module.Basis.ext_linearIsometry {ι : Type*} (b : Basis ι R E) {f₁ f₂ : E →ₛₗᵢ[σ₁₂] E₂}
    (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
  LinearIsometry.toLinearMap_injective <| b.ext h

/-- Two linear isometric equivalences are equal if they are equal on basis vectors. -/
theorem Module.Basis.ext_linearIsometryEquiv {ι : Type*} (b : Basis ι R E) {f₁ f₂ : E ≃ₛₗᵢ[σ₁₂] E₂}
    (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
  LinearIsometryEquiv.toLinearEquiv_injective <| b.ext' h

/-- Reinterpret a `LinearIsometry` as a `LinearIsometryEquiv` to the range. -/
@[simps! apply_coe]
noncomputable def LinearIsometry.equivRange {R S : Type*} [Semiring R] [Ring S] [Module S E]
    [Module R F] {σ₁₂ : R →+* S} {σ₂₁ : S →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (f : F →ₛₗᵢ[σ₁₂] E) : F ≃ₛₗᵢ[σ₁₂] (LinearMap.range f.toLinearMap) :=
  { f with toLinearEquiv := LinearEquiv.ofInjective f.toLinearMap f.injective }
