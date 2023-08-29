/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis, Heather Macbeth
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Basis

#align_import analysis.normed_space.linear_isometry from "leanprover-community/mathlib"@"4601791ea62fea875b488dafc4e6dede19e8363f"

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


open Function Set

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

/-- A `σ₁₂`-semilinear isometric embedding of a normed `R`-module into an `R₂`-module. -/
structure LinearIsometry (σ₁₂ : R →+* R₂) (E E₂ : Type*) [SeminormedAddCommGroup E]
  [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] extends E →ₛₗ[σ₁₂] E₂ where
  norm_map' : ∀ x, ‖toLinearMap x‖ = ‖x‖
#align linear_isometry LinearIsometry

notation:25 E " →ₛₗᵢ[" σ₁₂:25 "] " E₂:0 => LinearIsometry σ₁₂ E E₂

notation:25 E " →ₗᵢ[" R:25 "] " E₂:0 => LinearIsometry (RingHom.id R) E E₂

notation:25 E " →ₗᵢ⋆[" R:25 "] " E₂:0 => LinearIsometry (starRingEnd R) E E₂

/-- `SemilinearIsometryClass F σ E E₂` asserts `F` is a type of bundled `σ`-semilinear isometries
`E → E₂`.

See also `LinearIsometryClass F R E E₂` for the case where `σ` is the identity map on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. -/
class SemilinearIsometryClass (𝓕 : Type*) {R R₂ : outParam (Type*)} [Semiring R] [Semiring R₂]
  (σ₁₂ : outParam <| R →+* R₂) (E E₂ : outParam (Type*)) [SeminormedAddCommGroup E]
  [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] extends
  SemilinearMapClass 𝓕 σ₁₂ E E₂ where
  norm_map : ∀ (f : 𝓕) (x : E), ‖f x‖ = ‖x‖
#align semilinear_isometry_class SemilinearIsometryClass

/-- `LinearIsometryClass F R E E₂` asserts `F` is a type of bundled `R`-linear isometries
`M → M₂`.

This is an abbreviation for `SemilinearIsometryClass F (RingHom.id R) E E₂`.
-/
abbrev LinearIsometryClass (𝓕 : Type*) (R E E₂ : outParam (Type*)) [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [Module R E] [Module R E₂] :=
  SemilinearIsometryClass 𝓕 (RingHom.id R) E E₂
#align linear_isometry_class LinearIsometryClass

namespace SemilinearIsometryClass

protected theorem isometry [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) : Isometry f :=
  AddMonoidHomClass.isometry_of_norm _ (norm_map _)
#align semilinear_isometry_class.isometry SemilinearIsometryClass.isometry

@[continuity]
protected theorem continuous [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) : Continuous f :=
  (SemilinearIsometryClass.isometry f).continuous
#align semilinear_isometry_class.continuous SemilinearIsometryClass.continuous

@[simp]
theorem nnnorm_map [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (x : E) : ‖f x‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_map f x
#align semilinear_isometry_class.nnnorm_map SemilinearIsometryClass.nnnorm_map

protected theorem lipschitz [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) : LipschitzWith 1 f :=
  (SemilinearIsometryClass.isometry f).lipschitz
#align semilinear_isometry_class.lipschitz SemilinearIsometryClass.lipschitz

protected theorem antilipschitz [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) :
    AntilipschitzWith 1 f :=
  (SemilinearIsometryClass.isometry f).antilipschitz
#align semilinear_isometry_class.antilipschitz SemilinearIsometryClass.antilipschitz

theorem ediam_image [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (s : Set E) :
    EMetric.diam (f '' s) = EMetric.diam s :=
  (SemilinearIsometryClass.isometry f).ediam_image s
#align semilinear_isometry_class.ediam_image SemilinearIsometryClass.ediam_image

theorem ediam_range [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) :
    EMetric.diam (range f) = EMetric.diam (univ : Set E) :=
  (SemilinearIsometryClass.isometry f).ediam_range
#align semilinear_isometry_class.ediam_range SemilinearIsometryClass.ediam_range

theorem diam_image [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (s : Set E) :
    Metric.diam (f '' s) = Metric.diam s :=
  (SemilinearIsometryClass.isometry f).diam_image s
#align semilinear_isometry_class.diam_image SemilinearIsometryClass.diam_image

theorem diam_range [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) :
    Metric.diam (range f) = Metric.diam (univ : Set E) :=
  (SemilinearIsometryClass.isometry f).diam_range
#align semilinear_isometry_class.diam_range SemilinearIsometryClass.diam_range

instance (priority := 100) [s : SemilinearIsometryClass 𝓕 σ₁₂ E E₂] :
    ContinuousSemilinearMapClass 𝓕 σ₁₂ E E₂ :=
  { s with map_continuous := SemilinearIsometryClass.continuous }

end SemilinearIsometryClass

namespace LinearIsometry

variable (f : E →ₛₗᵢ[σ₁₂] E₂) (f₁ : F →ₛₗᵢ[σ₁₂] E₂)

theorem toLinearMap_injective : Injective (toLinearMap : (E →ₛₗᵢ[σ₁₂] E₂) → E →ₛₗ[σ₁₂] E₂)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
#align linear_isometry.to_linear_map_injective LinearIsometry.toLinearMap_injective

@[simp]
theorem toLinearMap_inj {f g : E →ₛₗᵢ[σ₁₂] E₂} : f.toLinearMap = g.toLinearMap ↔ f = g :=
  toLinearMap_injective.eq_iff
#align linear_isometry.to_linear_map_inj LinearIsometry.toLinearMap_inj

instance : SemilinearIsometryClass (E →ₛₗᵢ[σ₁₂] E₂) σ₁₂ E E₂ where
  coe f := f.toFun
  coe_injective' _ _ h := toLinearMap_injective (FunLike.coe_injective h)
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := map_smulₛₗ f.toLinearMap
  norm_map f := f.norm_map'

-- porting note: These helper instances are unhelpful in Lean 4, so omitting:
-- /-- Helper instance for when there's too many metavariables to apply `FunLike.has_coe_to_fun`
-- directly.
-- -/
-- instance : CoeFun (E →ₛₗᵢ[σ₁₂] E₂) fun _ => E → E₂ :=
--   ⟨fun f => f.toFun⟩

@[simp]
theorem coe_toLinearMap : ⇑f.toLinearMap = f :=
  rfl
#align linear_isometry.coe_to_linear_map LinearIsometry.coe_toLinearMap

@[simp]
theorem coe_mk (f : E →ₛₗ[σ₁₂] E₂) (hf) : ⇑(mk f hf) = f :=
  rfl
#align linear_isometry.coe_mk LinearIsometry.coe_mk

theorem coe_injective : @Injective (E →ₛₗᵢ[σ₁₂] E₂) (E → E₂) (fun f => f) := by
  rintro ⟨_⟩ ⟨_⟩
  -- ⊢ (fun f => ↑f) { toLinearMap := toLinearMap✝¹, norm_map' := norm_map'✝¹ } = ( …
  simp
  -- 🎉 no goals

#align linear_isometry.coe_injective LinearIsometry.coe_injective

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (σ₁₂ : R →+* R₂) (E E₂ : Type*) [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] (h : E →ₛₗᵢ[σ₁₂] E₂) : E → E₂ :=
  h
#align linear_isometry.simps.apply LinearIsometry.Simps.apply

initialize_simps_projections LinearIsometry (toLinearMap_toFun → apply)

@[ext]
theorem ext {f g : E →ₛₗᵢ[σ₁₂] E₂} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h
#align linear_isometry.ext LinearIsometry.ext

protected theorem congr_arg [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] {f : 𝓕} :
    ∀ {x x' : E}, x = x' → f x = f x'
  | _, _, rfl => rfl
#align linear_isometry.congr_arg LinearIsometry.congr_arg

protected theorem congr_fun [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] {f g : 𝓕} (h : f = g) (x : E) :
    f x = g x :=
  h ▸ rfl
#align linear_isometry.congr_fun LinearIsometry.congr_fun

-- @[simp] -- Porting note: simp can prove this
protected theorem map_zero : f 0 = 0 :=
  f.toLinearMap.map_zero
#align linear_isometry.map_zero LinearIsometry.map_zero

-- @[simp] -- Porting note: simp can prove this
protected theorem map_add (x y : E) : f (x + y) = f x + f y :=
  f.toLinearMap.map_add x y
#align linear_isometry.map_add LinearIsometry.map_add

-- @[simp] -- Porting note: simp can prove this
protected theorem map_neg (x : E) : f (-x) = -f x :=
  f.toLinearMap.map_neg x
#align linear_isometry.map_neg LinearIsometry.map_neg

-- @[simp] -- Porting note: simp can prove this
protected theorem map_sub (x y : E) : f (x - y) = f x - f y :=
  f.toLinearMap.map_sub x y
#align linear_isometry.map_sub LinearIsometry.map_sub

-- @[simp] -- Porting note: simp can prove this
protected theorem map_smulₛₗ (c : R) (x : E) : f (c • x) = σ₁₂ c • f x :=
  f.toLinearMap.map_smulₛₗ c x
#align linear_isometry.map_smulₛₗ LinearIsometry.map_smulₛₗ

-- @[simp] -- Porting note: simp can prove this
protected theorem map_smul [Module R E₂] (f : E →ₗᵢ[R] E₂) (c : R) (x : E) : f (c • x) = c • f x :=
  f.toLinearMap.map_smul c x
#align linear_isometry.map_smul LinearIsometry.map_smul

@[simp]
theorem norm_map (x : E) : ‖f x‖ = ‖x‖ :=
  SemilinearIsometryClass.norm_map f x
#align linear_isometry.norm_map LinearIsometry.norm_map

-- @[simp] -- Porting note: simp can prove this
theorem nnnorm_map (x : E) : ‖f x‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_map f x
#align linear_isometry.nnnorm_map LinearIsometry.nnnorm_map

protected theorem isometry : Isometry f :=
  AddMonoidHomClass.isometry_of_norm f.toLinearMap (norm_map _)
#align linear_isometry.isometry LinearIsometry.isometry

@[simp]
theorem isComplete_image_iff [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) {s : Set E} :
    IsComplete (f '' s) ↔ IsComplete s :=
  _root_.isComplete_image_iff (SemilinearIsometryClass.isometry f).uniformInducing
#align linear_isometry.is_complete_image_iff LinearIsometry.isComplete_image_iff

theorem isComplete_map_iff [RingHomSurjective σ₁₂] {p : Submodule R E} :
    IsComplete (p.map f.toLinearMap : Set E₂) ↔ IsComplete (p : Set E) :=
  isComplete_image_iff f
#align linear_isometry.is_complete_map_iff LinearIsometry.isComplete_map_iff

theorem isComplete_map_iff' [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) [RingHomSurjective σ₁₂]
    {p : Submodule R E} : IsComplete (p.map f : Set E₂) ↔ IsComplete (p : Set E) :=
  isComplete_image_iff f
#align linear_isometry.is_complete_map_iff' LinearIsometry.isComplete_map_iff'

instance completeSpace_map [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) [RingHomSurjective σ₁₂]
    (p : Submodule R E) [CompleteSpace p] : CompleteSpace (p.map f) :=
  ((isComplete_map_iff' f).2 <| completeSpace_coe_iff_isComplete.1 ‹_›).completeSpace_coe
#align linear_isometry.complete_space_map LinearIsometry.completeSpace_map

instance completeSpace_map' [RingHomSurjective σ₁₂] (p : Submodule R E) [CompleteSpace p] :
    CompleteSpace (p.map f.toLinearMap) :=
  (f.isComplete_map_iff.2 <| completeSpace_coe_iff_isComplete.1 ‹_›).completeSpace_coe
#align linear_isometry.complete_space_map' LinearIsometry.completeSpace_map'

@[simp]
theorem dist_map (x y : E) : dist (f x) (f y) = dist x y :=
  f.isometry.dist_eq x y
#align linear_isometry.dist_map LinearIsometry.dist_map

@[simp]
theorem edist_map (x y : E) : edist (f x) (f y) = edist x y :=
  f.isometry.edist_eq x y
#align linear_isometry.edist_map LinearIsometry.edist_map

protected theorem injective : Injective f₁ :=
  Isometry.injective (LinearIsometry.isometry f₁)
#align linear_isometry.injective LinearIsometry.injective

@[simp]
theorem map_eq_iff {x y : F} : f₁ x = f₁ y ↔ x = y :=
  f₁.injective.eq_iff
#align linear_isometry.map_eq_iff LinearIsometry.map_eq_iff

theorem map_ne {x y : F} (h : x ≠ y) : f₁ x ≠ f₁ y :=
  f₁.injective.ne h
#align linear_isometry.map_ne LinearIsometry.map_ne

protected theorem lipschitz : LipschitzWith 1 f :=
  f.isometry.lipschitz
#align linear_isometry.lipschitz LinearIsometry.lipschitz

protected theorem antilipschitz : AntilipschitzWith 1 f :=
  f.isometry.antilipschitz
#align linear_isometry.antilipschitz LinearIsometry.antilipschitz

@[continuity]
protected theorem continuous : Continuous f :=
  f.isometry.continuous
#align linear_isometry.continuous LinearIsometry.continuous

@[simp]
theorem preimage_ball (x : E) (r : ℝ) : f ⁻¹' Metric.ball (f x) r = Metric.ball x r :=
  f.isometry.preimage_ball x r
#align linear_isometry.preimage_ball LinearIsometry.preimage_ball

@[simp]
theorem preimage_sphere (x : E) (r : ℝ) : f ⁻¹' Metric.sphere (f x) r = Metric.sphere x r :=
  f.isometry.preimage_sphere x r
#align linear_isometry.preimage_sphere LinearIsometry.preimage_sphere

@[simp]
theorem preimage_closedBall (x : E) (r : ℝ) :
    f ⁻¹' Metric.closedBall (f x) r = Metric.closedBall x r :=
  f.isometry.preimage_closedBall x r
#align linear_isometry.preimage_closed_ball LinearIsometry.preimage_closedBall

theorem ediam_image (s : Set E) : EMetric.diam (f '' s) = EMetric.diam s :=
  f.isometry.ediam_image s
#align linear_isometry.ediam_image LinearIsometry.ediam_image

theorem ediam_range : EMetric.diam (range f) = EMetric.diam (univ : Set E) :=
  f.isometry.ediam_range
#align linear_isometry.ediam_range LinearIsometry.ediam_range

theorem diam_image (s : Set E) : Metric.diam (f '' s) = Metric.diam s :=
  Isometry.diam_image (LinearIsometry.isometry f) s
#align linear_isometry.diam_image LinearIsometry.diam_image

theorem diam_range : Metric.diam (range f) = Metric.diam (univ : Set E) :=
  Isometry.diam_range (LinearIsometry.isometry f)
#align linear_isometry.diam_range LinearIsometry.diam_range

/-- Interpret a linear isometry as a continuous linear map. -/
def toContinuousLinearMap : E →SL[σ₁₂] E₂ :=
  ⟨f.toLinearMap, f.continuous⟩
#align linear_isometry.to_continuous_linear_map LinearIsometry.toContinuousLinearMap

theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap : _ → E →SL[σ₁₂] E₂) := fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toContinuousLinearMap = _)
#align linear_isometry.to_continuous_linear_map_injective LinearIsometry.toContinuousLinearMap_injective

@[simp]
theorem toContinuousLinearMap_inj {f g : E →ₛₗᵢ[σ₁₂] E₂} :
    f.toContinuousLinearMap = g.toContinuousLinearMap ↔ f = g :=
  toContinuousLinearMap_injective.eq_iff
#align linear_isometry.to_continuous_linear_map_inj LinearIsometry.toContinuousLinearMap_inj

@[simp]
theorem coe_toContinuousLinearMap : ⇑f.toContinuousLinearMap = f :=
  rfl
#align linear_isometry.coe_to_continuous_linear_map LinearIsometry.coe_toContinuousLinearMap

@[simp]
theorem comp_continuous_iff {α : Type*} [TopologicalSpace α] {g : α → E} :
    Continuous (f ∘ g) ↔ Continuous g :=
  f.isometry.comp_continuous_iff
#align linear_isometry.comp_continuous_iff LinearIsometry.comp_continuous_iff

/-- The identity linear isometry. -/
def id : E →ₗᵢ[R] E :=
  ⟨LinearMap.id, fun _ => rfl⟩
#align linear_isometry.id LinearIsometry.id

@[simp]
theorem coe_id : ((id : E →ₗᵢ[R] E) : E → E) = _root_.id :=
  rfl
#align linear_isometry.coe_id LinearIsometry.coe_id

@[simp]
theorem id_apply (x : E) : (id : E →ₗᵢ[R] E) x = x :=
  rfl
#align linear_isometry.id_apply LinearIsometry.id_apply

@[simp]
theorem id_toLinearMap : (id.toLinearMap : E →ₗ[R] E) = LinearMap.id :=
  rfl
#align linear_isometry.id_to_linear_map LinearIsometry.id_toLinearMap

@[simp]
theorem id_toContinuousLinearMap : id.toContinuousLinearMap = ContinuousLinearMap.id R E :=
  rfl
#align linear_isometry.id_to_continuous_linear_map LinearIsometry.id_toContinuousLinearMap

instance : Inhabited (E →ₗᵢ[R] E) :=
  ⟨id⟩

/-- Composition of linear isometries. -/
def comp (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (f : E →ₛₗᵢ[σ₁₂] E₂) : E →ₛₗᵢ[σ₁₃] E₃ :=
  ⟨g.toLinearMap.comp f.toLinearMap, fun _ => (norm_map g _).trans (norm_map f _)⟩
#align linear_isometry.comp LinearIsometry.comp

@[simp]
theorem coe_comp (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (f : E →ₛₗᵢ[σ₁₂] E₂) : ⇑(g.comp f) = g ∘ f :=
  rfl
#align linear_isometry.coe_comp LinearIsometry.coe_comp

@[simp]
theorem id_comp : (id : E₂ →ₗᵢ[R₂] E₂).comp f = f :=
  ext fun _ => rfl
#align linear_isometry.id_comp LinearIsometry.id_comp

@[simp]
theorem comp_id : f.comp id = f :=
  ext fun _ => rfl
#align linear_isometry.comp_id LinearIsometry.comp_id

theorem comp_assoc (f : E₃ →ₛₗᵢ[σ₃₄] E₄) (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (h : E →ₛₗᵢ[σ₁₂] E₂) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align linear_isometry.comp_assoc LinearIsometry.comp_assoc

instance : Monoid (E →ₗᵢ[R] E) where
  one := id
  mul := comp
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

@[simp]
theorem coe_one : ((1 : E →ₗᵢ[R] E) : E → E) = _root_.id :=
  rfl
#align linear_isometry.coe_one LinearIsometry.coe_one

@[simp]
theorem coe_mul (f g : E →ₗᵢ[R] E) : ⇑(f * g) = f ∘ g :=
  rfl
#align linear_isometry.coe_mul LinearIsometry.coe_mul

theorem one_def : (1 : E →ₗᵢ[R] E) = id :=
  rfl
#align linear_isometry.one_def LinearIsometry.one_def

theorem mul_def (f g : E →ₗᵢ[R] E) : (f * g : E →ₗᵢ[R] E) = f.comp g :=
  rfl
#align linear_isometry.mul_def LinearIsometry.mul_def

theorem coe_pow (f : E →ₗᵢ[R] E) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

end LinearIsometry

/-- Construct a `LinearIsometry` from a `LinearMap` satisfying `Isometry`. -/
def LinearMap.toLinearIsometry (f : E →ₛₗ[σ₁₂] E₂) (hf : Isometry f) : E →ₛₗᵢ[σ₁₂] E₂ :=
  { f with
    norm_map' := by
      simp_rw [← dist_zero_right]
      -- ⊢ ∀ (x : E), dist (↑{ toAddHom := f.toAddHom, map_smul' := (_ : ∀ (r : R) (x : …
      simpa using (hf.dist_eq · 0) }
      -- 🎉 no goals
#align linear_map.to_linear_isometry LinearMap.toLinearIsometry

namespace Submodule

variable {R' : Type*} [Ring R'] [Module R' E] (p : Submodule R' E)

/-- `Submodule.subtype` as a `LinearIsometry`. -/
def subtypeₗᵢ : p →ₗᵢ[R'] E :=
  ⟨p.subtype, fun _ => rfl⟩
#align submodule.subtypeₗᵢ Submodule.subtypeₗᵢ

@[simp]
theorem coe_subtypeₗᵢ : ⇑p.subtypeₗᵢ = p.subtype :=
  rfl
#align submodule.coe_subtypeₗᵢ Submodule.coe_subtypeₗᵢ

@[simp]
theorem subtypeₗᵢ_toLinearMap : p.subtypeₗᵢ.toLinearMap = p.subtype :=
  rfl
#align submodule.subtypeₗᵢ_to_linear_map Submodule.subtypeₗᵢ_toLinearMap

@[simp]
theorem subtypeₗᵢ_toContinuousLinearMap : p.subtypeₗᵢ.toContinuousLinearMap = p.subtypeL :=
  rfl
#align submodule.subtypeₗᵢ_to_continuous_linear_map Submodule.subtypeₗᵢ_toContinuousLinearMap

end Submodule

/-- A semilinear isometric equivalence between two normed vector spaces. -/
structure LinearIsometryEquiv (σ₁₂ : R →+* R₂) {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] (E E₂ : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂]
  [Module R E] [Module R₂ E₂] extends E ≃ₛₗ[σ₁₂] E₂ where
  norm_map' : ∀ x, ‖toLinearEquiv x‖ = ‖x‖
#align linear_isometry_equiv LinearIsometryEquiv

notation:25 E " ≃ₛₗᵢ[" σ₁₂:25 "] " E₂:0 => LinearIsometryEquiv σ₁₂ E E₂

notation:25 E " ≃ₗᵢ[" R:25 "] " E₂:0 => LinearIsometryEquiv (RingHom.id R) E E₂

notation:25 E " ≃ₗᵢ⋆[" R:25 "] " E₂:0 => LinearIsometryEquiv (starRingEnd R) E E₂

/-- `SemilinearIsometryEquivClass F σ E E₂` asserts `F` is a type of bundled `σ`-semilinear
isometric equivs `E → E₂`.

See also `LinearIsometryEquivClass F R E E₂` for the case where `σ` is the identity map on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. -/
class SemilinearIsometryEquivClass (𝓕 : Type*) {R R₂ : outParam (Type*)} [Semiring R]
  [Semiring R₂] (σ₁₂ : outParam <| R →+* R₂) {σ₂₁ : outParam <| R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] (E E₂ : outParam (Type*)) [SeminormedAddCommGroup E]
  [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] extends
  SemilinearEquivClass 𝓕 σ₁₂ E E₂ where
  norm_map : ∀ (f : 𝓕) (x : E), ‖f x‖ = ‖x‖
#align semilinear_isometry_equiv_class SemilinearIsometryEquivClass

/-- `LinearIsometryEquivClass F R E E₂` asserts `F` is a type of bundled `R`-linear isometries
`M → M₂`.

This is an abbreviation for `SemilinearIsometryEquivClass F (RingHom.id R) E E₂`.
-/
abbrev LinearIsometryEquivClass (𝓕 : Type*) (R E E₂ : outParam (Type*)) [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [Module R E] [Module R E₂] :=
  SemilinearIsometryEquivClass 𝓕 (RingHom.id R) E E₂
#align linear_isometry_equiv_class LinearIsometryEquivClass

namespace SemilinearIsometryEquivClass

variable (𝓕)

-- `σ₂₁` becomes a metavariable, but it's OK since it's an outparam
instance (priority := 100) [s : SemilinearIsometryEquivClass 𝓕 σ₁₂ E E₂] :
    SemilinearIsometryClass 𝓕 σ₁₂ E E₂ :=
  { s with
    coe := ((↑) : 𝓕 → E → E₂)
    coe_injective' := @FunLike.coe_injective 𝓕 _ _ _ }

end SemilinearIsometryEquivClass

namespace LinearIsometryEquiv

variable (e : E ≃ₛₗᵢ[σ₁₂] E₂)

theorem toLinearEquiv_injective : Injective (toLinearEquiv : (E ≃ₛₗᵢ[σ₁₂] E₂) → E ≃ₛₗ[σ₁₂] E₂)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
#align linear_isometry_equiv.to_linear_equiv_injective LinearIsometryEquiv.toLinearEquiv_injective

@[simp]
theorem toLinearEquiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} : f.toLinearEquiv = g.toLinearEquiv ↔ f = g :=
  toLinearEquiv_injective.eq_iff
#align linear_isometry_equiv.to_linear_equiv_inj LinearIsometryEquiv.toLinearEquiv_inj

instance : SemilinearIsometryEquivClass (E ≃ₛₗᵢ[σ₁₂] E₂) σ₁₂ E E₂ where
  coe e := e.toFun
  inv e := e.invFun
  coe_injective' f g h₁ h₂ := by
    cases' f with f' _
    -- ⊢ { toLinearEquiv := f', norm_map' := norm_map'✝ } = g
    cases' g with g' _
    -- ⊢ { toLinearEquiv := f', norm_map' := norm_map'✝¹ } = { toLinearEquiv := g', n …
    cases f'
    -- ⊢ { toLinearEquiv := { toLinearMap := toLinearMap✝, invFun := invFun✝, left_in …
    cases g'
    -- ⊢ { toLinearEquiv := { toLinearMap := toLinearMap✝¹, invFun := invFun✝¹, left_ …
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, FunLike.coe_fn_eq] at h₁
    -- ⊢ { toLinearEquiv := { toLinearMap := toLinearMap✝¹, invFun := invFun✝¹, left_ …
    congr
    -- 🎉 no goals
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  map_add f := map_add f.toLinearEquiv
  map_smulₛₗ e := map_smulₛₗ e.toLinearEquiv
  norm_map e := e.norm_map'

/-- Helper instance for when there's too many metavariables to apply `FunLike.hasCoeToFun`
directly.
-/
instance : CoeFun (E ≃ₛₗᵢ[σ₁₂] E₂) fun _ => E → E₂ :=
  ⟨FunLike.coe⟩

theorem coe_injective : @Function.Injective (E ≃ₛₗᵢ[σ₁₂] E₂) (E → E₂) (↑) :=
  FunLike.coe_injective
#align linear_isometry_equiv.coe_injective LinearIsometryEquiv.coe_injective

@[simp]
theorem coe_mk (e : E ≃ₛₗ[σ₁₂] E₂) (he : ∀ x, ‖e x‖ = ‖x‖) : ⇑(mk e he) = e :=
  rfl
#align linear_isometry_equiv.coe_mk LinearIsometryEquiv.coe_mk

@[simp]
theorem coe_toLinearEquiv (e : E ≃ₛₗᵢ[σ₁₂] E₂) : ⇑e.toLinearEquiv = e :=
  rfl
#align linear_isometry_equiv.coe_to_linear_equiv LinearIsometryEquiv.coe_toLinearEquiv

@[ext]
theorem ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : ∀ x, e x = e' x) : e = e' :=
  toLinearEquiv_injective <| LinearEquiv.ext h
#align linear_isometry_equiv.ext LinearIsometryEquiv.ext

protected theorem congr_arg {f : E ≃ₛₗᵢ[σ₁₂] E₂} : ∀ {x x' : E}, x = x' → f x = f x'
  | _, _, rfl => rfl
#align linear_isometry_equiv.congr_arg LinearIsometryEquiv.congr_arg

protected theorem congr_fun {f g : E ≃ₛₗᵢ[σ₁₂] E₂} (h : f = g) (x : E) : f x = g x :=
  h ▸ rfl
#align linear_isometry_equiv.congr_fun LinearIsometryEquiv.congr_fun

/-- Construct a `LinearIsometryEquiv` from a `LinearEquiv` and two inequalities:
`∀ x, ‖e x‖ ≤ ‖x‖` and `∀ y, ‖e.symm y‖ ≤ ‖y‖`. -/
def ofBounds (e : E ≃ₛₗ[σ₁₂] E₂) (h₁ : ∀ x, ‖e x‖ ≤ ‖x‖) (h₂ : ∀ y, ‖e.symm y‖ ≤ ‖y‖) :
    E ≃ₛₗᵢ[σ₁₂] E₂ :=
  ⟨e, fun x => le_antisymm (h₁ x) <| by simpa only [e.symm_apply_apply] using h₂ (e x)⟩
                                        -- 🎉 no goals
#align linear_isometry_equiv.of_bounds LinearIsometryEquiv.ofBounds

@[simp]
theorem norm_map (x : E) : ‖e x‖ = ‖x‖ :=
  e.norm_map' x
#align linear_isometry_equiv.norm_map LinearIsometryEquiv.norm_map

/-- Reinterpret a `LinearIsometryEquiv` as a `LinearIsometry`. -/
def toLinearIsometry : E →ₛₗᵢ[σ₁₂] E₂ :=
  ⟨e.1, e.2⟩
#align linear_isometry_equiv.to_linear_isometry LinearIsometryEquiv.toLinearIsometry

theorem toLinearIsometry_injective : Function.Injective (toLinearIsometry : _ → E →ₛₗᵢ[σ₁₂] E₂) :=
  fun x _ h => coe_injective (congr_arg _ h : ⇑x.toLinearIsometry = _)
#align linear_isometry_equiv.to_linear_isometry_injective LinearIsometryEquiv.toLinearIsometry_injective

@[simp]
theorem toLinearIsometry_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
    f.toLinearIsometry = g.toLinearIsometry ↔ f = g :=
  toLinearIsometry_injective.eq_iff
#align linear_isometry_equiv.to_linear_isometry_inj LinearIsometryEquiv.toLinearIsometry_inj

@[simp]
theorem coe_toLinearIsometry : ⇑e.toLinearIsometry = e :=
  rfl
#align linear_isometry_equiv.coe_to_linear_isometry LinearIsometryEquiv.coe_toLinearIsometry

protected theorem isometry : Isometry e :=
  e.toLinearIsometry.isometry
#align linear_isometry_equiv.isometry LinearIsometryEquiv.isometry

/-- Reinterpret a `LinearIsometryEquiv` as an `IsometryEquiv`. -/
def toIsometryEquiv : E ≃ᵢ E₂ :=
  ⟨e.toLinearEquiv.toEquiv, e.isometry⟩
#align linear_isometry_equiv.to_isometry_equiv LinearIsometryEquiv.toIsometryEquiv

theorem toIsometryEquiv_injective :
    Function.Injective (toIsometryEquiv : (E ≃ₛₗᵢ[σ₁₂] E₂) → E ≃ᵢ E₂) := fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toIsometryEquiv = _)
#align linear_isometry_equiv.to_isometry_equiv_injective LinearIsometryEquiv.toIsometryEquiv_injective

@[simp]
theorem toIsometryEquiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
    f.toIsometryEquiv = g.toIsometryEquiv ↔ f = g :=
  toIsometryEquiv_injective.eq_iff
#align linear_isometry_equiv.to_isometry_equiv_inj LinearIsometryEquiv.toIsometryEquiv_inj

@[simp]
theorem coe_toIsometryEquiv : ⇑e.toIsometryEquiv = e :=
  rfl
#align linear_isometry_equiv.coe_to_isometry_equiv LinearIsometryEquiv.coe_toIsometryEquiv

theorem range_eq_univ (e : E ≃ₛₗᵢ[σ₁₂] E₂) : Set.range e = Set.univ := by
  rw [← coe_toIsometryEquiv]
  -- ⊢ range ↑(toIsometryEquiv e) = univ
  exact IsometryEquiv.range_eq_univ _
  -- 🎉 no goals
#align linear_isometry_equiv.range_eq_univ LinearIsometryEquiv.range_eq_univ

/-- Reinterpret a `LinearIsometryEquiv` as a `Homeomorph`. -/
def toHomeomorph : E ≃ₜ E₂ :=
  e.toIsometryEquiv.toHomeomorph
#align linear_isometry_equiv.to_homeomorph LinearIsometryEquiv.toHomeomorph

theorem toHomeomorph_injective : Function.Injective (toHomeomorph : (E ≃ₛₗᵢ[σ₁₂] E₂) → E ≃ₜ E₂) :=
  fun x _ h => coe_injective (congr_arg _ h : ⇑x.toHomeomorph = _)
#align linear_isometry_equiv.to_homeomorph_injective LinearIsometryEquiv.toHomeomorph_injective

@[simp]
theorem toHomeomorph_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} : f.toHomeomorph = g.toHomeomorph ↔ f = g :=
  toHomeomorph_injective.eq_iff
#align linear_isometry_equiv.to_homeomorph_inj LinearIsometryEquiv.toHomeomorph_inj

@[simp]
theorem coe_toHomeomorph : ⇑e.toHomeomorph = e :=
  rfl
#align linear_isometry_equiv.coe_to_homeomorph LinearIsometryEquiv.coe_toHomeomorph

protected theorem continuous : Continuous e :=
  e.isometry.continuous
#align linear_isometry_equiv.continuous LinearIsometryEquiv.continuous

protected theorem continuousAt {x} : ContinuousAt e x :=
  e.continuous.continuousAt
#align linear_isometry_equiv.continuous_at LinearIsometryEquiv.continuousAt

protected theorem continuousOn {s} : ContinuousOn e s :=
  e.continuous.continuousOn
#align linear_isometry_equiv.continuous_on LinearIsometryEquiv.continuousOn

protected theorem continuousWithinAt {s x} : ContinuousWithinAt e s x :=
  e.continuous.continuousWithinAt
#align linear_isometry_equiv.continuous_within_at LinearIsometryEquiv.continuousWithinAt

/-- Interpret a `LinearIsometryEquiv` as a `ContinuousLinearEquiv`. -/
def toContinuousLinearEquiv : E ≃SL[σ₁₂] E₂ :=
  { e.toLinearIsometry.toContinuousLinearMap, e.toHomeomorph with }
#align linear_isometry_equiv.to_continuous_linear_equiv LinearIsometryEquiv.toContinuousLinearEquiv

theorem toContinuousLinearEquiv_injective :
    Function.Injective (toContinuousLinearEquiv : _ → E ≃SL[σ₁₂] E₂) := fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toContinuousLinearEquiv = _)
#align linear_isometry_equiv.to_continuous_linear_equiv_injective LinearIsometryEquiv.toContinuousLinearEquiv_injective

@[simp]
theorem toContinuousLinearEquiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
    f.toContinuousLinearEquiv = g.toContinuousLinearEquiv ↔ f = g :=
  toContinuousLinearEquiv_injective.eq_iff
#align linear_isometry_equiv.to_continuous_linear_equiv_inj LinearIsometryEquiv.toContinuousLinearEquiv_inj

@[simp]
theorem coe_toContinuousLinearEquiv : ⇑e.toContinuousLinearEquiv = e :=
  rfl
#align linear_isometry_equiv.coe_to_continuous_linear_equiv LinearIsometryEquiv.coe_toContinuousLinearEquiv

variable (R E)

/-- Identity map as a `LinearIsometryEquiv`. -/
def refl : E ≃ₗᵢ[R] E :=
  ⟨LinearEquiv.refl R E, fun _ => rfl⟩
#align linear_isometry_equiv.refl LinearIsometryEquiv.refl

/-- Linear isometry equiv between a space and its lift to another universe. -/
def ulift : ULift E ≃ₗᵢ[R] E :=
  { ContinuousLinearEquiv.ulift with norm_map' := fun _ => rfl }
#align linear_isometry_equiv.ulift LinearIsometryEquiv.ulift

variable {R E}

instance : Inhabited (E ≃ₗᵢ[R] E) :=
  ⟨refl R E⟩

@[simp]
theorem coe_refl : ⇑(refl R E) = id :=
  rfl
#align linear_isometry_equiv.coe_refl LinearIsometryEquiv.coe_refl

/-- The inverse `LinearIsometryEquiv`. -/
def symm : E₂ ≃ₛₗᵢ[σ₂₁] E :=
  ⟨e.toLinearEquiv.symm, fun x =>
    (e.norm_map _).symm.trans <| congr_arg norm <| e.toLinearEquiv.apply_symm_apply x⟩
#align linear_isometry_equiv.symm LinearIsometryEquiv.symm

@[simp]
theorem apply_symm_apply (x : E₂) : e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply x
#align linear_isometry_equiv.apply_symm_apply LinearIsometryEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (x : E) : e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply x
#align linear_isometry_equiv.symm_apply_apply LinearIsometryEquiv.symm_apply_apply

-- @[simp] -- Porting note: simp can prove this
theorem map_eq_zero_iff {x : E} : e x = 0 ↔ x = 0 :=
  e.toLinearEquiv.map_eq_zero_iff
#align linear_isometry_equiv.map_eq_zero_iff LinearIsometryEquiv.map_eq_zero_iff

@[simp]
theorem symm_symm : e.symm.symm = e :=
  ext fun _ => rfl
#align linear_isometry_equiv.symm_symm LinearIsometryEquiv.symm_symm

@[simp]
theorem toLinearEquiv_symm : e.toLinearEquiv.symm = e.symm.toLinearEquiv :=
  rfl
#align linear_isometry_equiv.to_linear_equiv_symm LinearIsometryEquiv.toLinearEquiv_symm

@[simp]
theorem toIsometryEquiv_symm : e.toIsometryEquiv.symm = e.symm.toIsometryEquiv :=
  rfl
#align linear_isometry_equiv.to_isometry_equiv_symm LinearIsometryEquiv.toIsometryEquiv_symm

@[simp]
theorem toHomeomorph_symm : e.toHomeomorph.symm = e.symm.toHomeomorph :=
  rfl
#align linear_isometry_equiv.to_homeomorph_symm LinearIsometryEquiv.toHomeomorph_symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (σ₁₂ : R →+* R₂) {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (E E₂ : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [Module R E]
    [Module R₂ E₂] (h : E ≃ₛₗᵢ[σ₁₂] E₂) : E → E₂ :=
  h
#align linear_isometry_equiv.simps.apply LinearIsometryEquiv.Simps.apply

/-- See Note [custom simps projection] -/
def Simps.symm_apply (σ₁₂ : R →+* R₂) {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁]
    [RingHomInvPair σ₂₁ σ₁₂] (E E₂ : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂]
    [Module R E] [Module R₂ E₂] (h : E ≃ₛₗᵢ[σ₁₂] E₂) : E₂ → E :=
  h.symm
#align linear_isometry_equiv.simps.symm_apply LinearIsometryEquiv.Simps.symm_apply

initialize_simps_projections LinearIsometryEquiv (toLinearEquiv_toFun → apply,
  toLinearEquiv_invFun → symm_apply)

/-- Composition of `LinearIsometryEquiv`s as a `LinearIsometryEquiv`. -/
def trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : E ≃ₛₗᵢ[σ₁₃] E₃ :=
  ⟨e.toLinearEquiv.trans e'.toLinearEquiv, fun _ => (e'.norm_map _).trans (e.norm_map _)⟩
#align linear_isometry_equiv.trans LinearIsometryEquiv.trans

@[simp]
theorem coe_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl
#align linear_isometry_equiv.coe_trans LinearIsometryEquiv.coe_trans

@[simp]
theorem trans_apply (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (c : E) :
    (e₁.trans e₂ : E ≃ₛₗᵢ[σ₁₃] E₃) c = e₂ (e₁ c) :=
  rfl
#align linear_isometry_equiv.trans_apply LinearIsometryEquiv.trans_apply

@[simp]
theorem toLinearEquiv_trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    (e.trans e').toLinearEquiv = e.toLinearEquiv.trans e'.toLinearEquiv :=
  rfl
#align linear_isometry_equiv.to_linear_equiv_trans LinearIsometryEquiv.toLinearEquiv_trans

@[simp]
theorem trans_refl : e.trans (refl R₂ E₂) = e :=
  ext fun _ => rfl
#align linear_isometry_equiv.trans_refl LinearIsometryEquiv.trans_refl

@[simp]
theorem refl_trans : (refl R E).trans e = e :=
  ext fun _ => rfl
#align linear_isometry_equiv.refl_trans LinearIsometryEquiv.refl_trans

@[simp]
theorem self_trans_symm : e.trans e.symm = refl R E :=
  ext e.symm_apply_apply
#align linear_isometry_equiv.self_trans_symm LinearIsometryEquiv.self_trans_symm

@[simp]
theorem symm_trans_self : e.symm.trans e = refl R₂ E₂ :=
  ext e.apply_symm_apply
#align linear_isometry_equiv.symm_trans_self LinearIsometryEquiv.symm_trans_self

@[simp]
theorem symm_comp_self : e.symm ∘ e = id :=
  funext e.symm_apply_apply
#align linear_isometry_equiv.symm_comp_self LinearIsometryEquiv.symm_comp_self

@[simp]
theorem self_comp_symm : e ∘ e.symm = id :=
  e.symm.symm_comp_self
#align linear_isometry_equiv.self_comp_symm LinearIsometryEquiv.self_comp_symm

@[simp]
theorem symm_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl
#align linear_isometry_equiv.symm_trans LinearIsometryEquiv.symm_trans

theorem coe_symm_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    ⇑(e₁.trans e₂).symm = e₁.symm ∘ e₂.symm :=
  rfl
#align linear_isometry_equiv.coe_symm_trans LinearIsometryEquiv.coe_symm_trans

theorem trans_assoc (eEE₂ : E ≃ₛₗᵢ[σ₁₂] E₂) (eE₂E₃ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (eE₃E₄ : E₃ ≃ₛₗᵢ[σ₃₄] E₄) :
    eEE₂.trans (eE₂E₃.trans eE₃E₄) = (eEE₂.trans eE₂E₃).trans eE₃E₄ :=
  rfl
#align linear_isometry_equiv.trans_assoc LinearIsometryEquiv.trans_assoc

instance : Group (E ≃ₗᵢ[R] E) where
  mul e₁ e₂ := e₂.trans e₁
  one := refl _ _
  inv := symm
  one_mul := trans_refl
  mul_one := refl_trans
  mul_assoc _ _ _ := trans_assoc _ _ _
  mul_left_inv := self_trans_symm

@[simp]
theorem coe_one : ⇑(1 : E ≃ₗᵢ[R] E) = id :=
  rfl
#align linear_isometry_equiv.coe_one LinearIsometryEquiv.coe_one

@[simp]
theorem coe_mul (e e' : E ≃ₗᵢ[R] E) : ⇑(e * e') = e ∘ e' :=
  rfl
#align linear_isometry_equiv.coe_mul LinearIsometryEquiv.coe_mul

@[simp]
theorem coe_inv (e : E ≃ₗᵢ[R] E) : ⇑e⁻¹ = e.symm :=
  rfl
#align linear_isometry_equiv.coe_inv LinearIsometryEquiv.coe_inv

theorem one_def : (1 : E ≃ₗᵢ[R] E) = refl _ _ :=
  rfl
#align linear_isometry_equiv.one_def LinearIsometryEquiv.one_def

theorem mul_def (e e' : E ≃ₗᵢ[R] E) : (e * e' : E ≃ₗᵢ[R] E) = e'.trans e :=
  rfl
#align linear_isometry_equiv.mul_def LinearIsometryEquiv.mul_def

theorem inv_def (e : E ≃ₗᵢ[R] E) : (e⁻¹ : E ≃ₗᵢ[R] E) = e.symm :=
  rfl
#align linear_isometry_equiv.inv_def LinearIsometryEquiv.inv_def

/-! Lemmas about mixing the group structure with definitions. Because we have multiple ways to
express `LinearIsometryEquiv.refl`, `LinearIsometryEquiv.symm`, and
`LinearIsometryEquiv.trans`, we want simp lemmas for every combination.
The assumption made here is that if you're using the group structure, you want to preserve it
after simp.

This copies the approach used by the lemmas near `Equiv.Perm.trans_one`. -/


@[simp]
theorem trans_one : e.trans (1 : E₂ ≃ₗᵢ[R₂] E₂) = e :=
  trans_refl _
#align linear_isometry_equiv.trans_one LinearIsometryEquiv.trans_one

@[simp]
theorem one_trans : (1 : E ≃ₗᵢ[R] E).trans e = e :=
  refl_trans _
#align linear_isometry_equiv.one_trans LinearIsometryEquiv.one_trans

@[simp]
theorem refl_mul (e : E ≃ₗᵢ[R] E) : refl _ _ * e = e :=
  trans_refl _
#align linear_isometry_equiv.refl_mul LinearIsometryEquiv.refl_mul

@[simp]
theorem mul_refl (e : E ≃ₗᵢ[R] E) : e * refl _ _ = e :=
  refl_trans _
#align linear_isometry_equiv.mul_refl LinearIsometryEquiv.mul_refl

/-- Reinterpret a `LinearIsometryEquiv` as a `ContinuousLinearEquiv`. -/
instance : CoeTC (E ≃ₛₗᵢ[σ₁₂] E₂) (E ≃SL[σ₁₂] E₂) :=
  ⟨fun e => ⟨e.toLinearEquiv, e.continuous, e.toIsometryEquiv.symm.continuous⟩⟩

instance : CoeTC (E ≃ₛₗᵢ[σ₁₂] E₂) (E →SL[σ₁₂] E₂) :=
  ⟨fun e => ↑(e : E ≃SL[σ₁₂] E₂)⟩

@[simp]
theorem coe_coe : ⇑(e : E ≃SL[σ₁₂] E₂) = e :=
  rfl
#align linear_isometry_equiv.coe_coe LinearIsometryEquiv.coe_coe

-- @[simp] -- Porting note: now a syntactic tautology
-- theorem coe_coe' : ((e : E ≃SL[σ₁₂] E₂) : E →SL[σ₁₂] E₂) = e :=
--   rfl
#noalign linear_isometry_equiv.coe_coe'

@[simp]
theorem coe_coe'' : ⇑(e : E →SL[σ₁₂] E₂) = e :=
  rfl
#align linear_isometry_equiv.coe_coe'' LinearIsometryEquiv.coe_coe''

-- @[simp] -- Porting note: simp can prove this
theorem map_zero : e 0 = 0 :=
  e.1.map_zero
#align linear_isometry_equiv.map_zero LinearIsometryEquiv.map_zero

-- @[simp] -- Porting note: simp can prove this
theorem map_add (x y : E) : e (x + y) = e x + e y :=
  e.1.map_add x y
#align linear_isometry_equiv.map_add LinearIsometryEquiv.map_add

-- @[simp] -- Porting note: simp can prove this
theorem map_sub (x y : E) : e (x - y) = e x - e y :=
  e.1.map_sub x y
#align linear_isometry_equiv.map_sub LinearIsometryEquiv.map_sub

-- @[simp] -- Porting note: simp can prove this
theorem map_smulₛₗ (c : R) (x : E) : e (c • x) = σ₁₂ c • e x :=
  e.1.map_smulₛₗ c x
#align linear_isometry_equiv.map_smulₛₗ LinearIsometryEquiv.map_smulₛₗ

-- @[simp] -- Porting note: simp can prove this
theorem map_smul [Module R E₂] {e : E ≃ₗᵢ[R] E₂} (c : R) (x : E) : e (c • x) = c • e x :=
  e.1.map_smul c x
#align linear_isometry_equiv.map_smul LinearIsometryEquiv.map_smul

-- @[simp] -- Porting note: simp can prove this
theorem nnnorm_map (x : E) : ‖e x‖₊ = ‖x‖₊ :=
  SemilinearIsometryClass.nnnorm_map e x
#align linear_isometry_equiv.nnnorm_map LinearIsometryEquiv.nnnorm_map

@[simp]
theorem dist_map (x y : E) : dist (e x) (e y) = dist x y :=
  e.toLinearIsometry.dist_map x y
#align linear_isometry_equiv.dist_map LinearIsometryEquiv.dist_map

@[simp]
theorem edist_map (x y : E) : edist (e x) (e y) = edist x y :=
  e.toLinearIsometry.edist_map x y
#align linear_isometry_equiv.edist_map LinearIsometryEquiv.edist_map

protected theorem bijective : Bijective e :=
  e.1.bijective
#align linear_isometry_equiv.bijective LinearIsometryEquiv.bijective

protected theorem injective : Injective e :=
  e.1.injective
#align linear_isometry_equiv.injective LinearIsometryEquiv.injective

protected theorem surjective : Surjective e :=
  e.1.surjective
#align linear_isometry_equiv.surjective LinearIsometryEquiv.surjective

-- @[simp] -- Porting note: simp can prove this
theorem map_eq_iff {x y : E} : e x = e y ↔ x = y :=
  e.injective.eq_iff
#align linear_isometry_equiv.map_eq_iff LinearIsometryEquiv.map_eq_iff

theorem map_ne {x y : E} (h : x ≠ y) : e x ≠ e y :=
  e.injective.ne h
#align linear_isometry_equiv.map_ne LinearIsometryEquiv.map_ne

protected theorem lipschitz : LipschitzWith 1 e :=
  e.isometry.lipschitz
#align linear_isometry_equiv.lipschitz LinearIsometryEquiv.lipschitz

protected theorem antilipschitz : AntilipschitzWith 1 e :=
  e.isometry.antilipschitz
#align linear_isometry_equiv.antilipschitz LinearIsometryEquiv.antilipschitz

theorem image_eq_preimage (s : Set E) : e '' s = e.symm ⁻¹' s :=
  e.toLinearEquiv.image_eq_preimage s
#align linear_isometry_equiv.image_eq_preimage LinearIsometryEquiv.image_eq_preimage

@[simp]
theorem ediam_image (s : Set E) : EMetric.diam (e '' s) = EMetric.diam s :=
  e.isometry.ediam_image s
#align linear_isometry_equiv.ediam_image LinearIsometryEquiv.ediam_image

@[simp]
theorem diam_image (s : Set E) : Metric.diam (e '' s) = Metric.diam s :=
  e.isometry.diam_image s
#align linear_isometry_equiv.diam_image LinearIsometryEquiv.diam_image

@[simp]
theorem preimage_ball (x : E₂) (r : ℝ) : e ⁻¹' Metric.ball x r = Metric.ball (e.symm x) r :=
  e.toIsometryEquiv.preimage_ball x r
#align linear_isometry_equiv.preimage_ball LinearIsometryEquiv.preimage_ball

@[simp]
theorem preimage_sphere (x : E₂) (r : ℝ) : e ⁻¹' Metric.sphere x r = Metric.sphere (e.symm x) r :=
  e.toIsometryEquiv.preimage_sphere x r
#align linear_isometry_equiv.preimage_sphere LinearIsometryEquiv.preimage_sphere

@[simp]
theorem preimage_closedBall (x : E₂) (r : ℝ) :
    e ⁻¹' Metric.closedBall x r = Metric.closedBall (e.symm x) r :=
  e.toIsometryEquiv.preimage_closedBall x r
#align linear_isometry_equiv.preimage_closed_ball LinearIsometryEquiv.preimage_closedBall

@[simp]
theorem image_ball (x : E) (r : ℝ) : e '' Metric.ball x r = Metric.ball (e x) r :=
  e.toIsometryEquiv.image_ball x r
#align linear_isometry_equiv.image_ball LinearIsometryEquiv.image_ball

@[simp]
theorem image_sphere (x : E) (r : ℝ) : e '' Metric.sphere x r = Metric.sphere (e x) r :=
  e.toIsometryEquiv.image_sphere x r
#align linear_isometry_equiv.image_sphere LinearIsometryEquiv.image_sphere

@[simp]
theorem image_closedBall (x : E) (r : ℝ) : e '' Metric.closedBall x r = Metric.closedBall (e x) r :=
  e.toIsometryEquiv.image_closedBall x r
#align linear_isometry_equiv.image_closed_ball LinearIsometryEquiv.image_closedBall

variable {α : Type*} [TopologicalSpace α]

@[simp]
theorem comp_continuousOn_iff {f : α → E} {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.isometry.comp_continuousOn_iff
#align linear_isometry_equiv.comp_continuous_on_iff LinearIsometryEquiv.comp_continuousOn_iff

@[simp]
theorem comp_continuous_iff {f : α → E} : Continuous (e ∘ f) ↔ Continuous f :=
  e.isometry.comp_continuous_iff
#align linear_isometry_equiv.comp_continuous_iff LinearIsometryEquiv.comp_continuous_iff

instance completeSpace_map (p : Submodule R E) [CompleteSpace p] :
    CompleteSpace (p.map (e.toLinearEquiv : E →ₛₗ[σ₁₂] E₂)) :=
  e.toLinearIsometry.completeSpace_map' p
#align linear_isometry_equiv.complete_space_map LinearIsometryEquiv.completeSpace_map

/-- Construct a linear isometry equiv from a surjective linear isometry. -/
noncomputable def ofSurjective (f : F →ₛₗᵢ[σ₁₂] E₂) (hfr : Function.Surjective f) :
    F ≃ₛₗᵢ[σ₁₂] E₂ :=
  { LinearEquiv.ofBijective f.toLinearMap ⟨f.injective, hfr⟩ with norm_map' := f.norm_map }
#align linear_isometry_equiv.of_surjective LinearIsometryEquiv.ofSurjective

@[simp]
theorem coe_ofSurjective (f : F →ₛₗᵢ[σ₁₂] E₂) (hfr : Function.Surjective f) :
    ⇑(LinearIsometryEquiv.ofSurjective f hfr) = f := by
  ext
  -- ⊢ ↑(ofSurjective f hfr) x✝ = ↑f x✝
  rfl
  -- 🎉 no goals
#align linear_isometry_equiv.coe_of_surjective LinearIsometryEquiv.coe_ofSurjective

/-- If a linear isometry has an inverse, it is a linear isometric equivalence. -/
def ofLinearIsometry (f : E →ₛₗᵢ[σ₁₂] E₂) (g : E₂ →ₛₗ[σ₂₁] E)
    (h₁ : f.toLinearMap.comp g = LinearMap.id) (h₂ : g.comp f.toLinearMap = LinearMap.id) :
    E ≃ₛₗᵢ[σ₁₂] E₂ :=
  { LinearEquiv.ofLinear f.toLinearMap g h₁ h₂ with norm_map' := fun x => f.norm_map x }
#align linear_isometry_equiv.of_linear_isometry LinearIsometryEquiv.ofLinearIsometry

@[simp]
theorem coe_ofLinearIsometry (f : E →ₛₗᵢ[σ₁₂] E₂) (g : E₂ →ₛₗ[σ₂₁] E)
    (h₁ : f.toLinearMap.comp g = LinearMap.id) (h₂ : g.comp f.toLinearMap = LinearMap.id) :
    (ofLinearIsometry f g h₁ h₂ : E → E₂) = (f : E → E₂) :=
  rfl
#align linear_isometry_equiv.coe_of_linear_isometry LinearIsometryEquiv.coe_ofLinearIsometry

@[simp]
theorem coe_ofLinearIsometry_symm (f : E →ₛₗᵢ[σ₁₂] E₂) (g : E₂ →ₛₗ[σ₂₁] E)
    (h₁ : f.toLinearMap.comp g = LinearMap.id) (h₂ : g.comp f.toLinearMap = LinearMap.id) :
    ((ofLinearIsometry f g h₁ h₂).symm : E₂ → E) = (g : E₂ → E) :=
  rfl
#align linear_isometry_equiv.coe_of_linear_isometry_symm LinearIsometryEquiv.coe_ofLinearIsometry_symm

variable (R)

/-- The negation operation on a normed space `E`, considered as a linear isometry equivalence. -/
def neg : E ≃ₗᵢ[R] E :=
  { LinearEquiv.neg R with norm_map' := norm_neg }
#align linear_isometry_equiv.neg LinearIsometryEquiv.neg

variable {R}

@[simp]
theorem coe_neg : (neg R : E → E) = fun x => -x :=
  rfl
#align linear_isometry_equiv.coe_neg LinearIsometryEquiv.coe_neg

@[simp]
theorem symm_neg : (neg R : E ≃ₗᵢ[R] E).symm = neg R :=
  rfl
#align linear_isometry_equiv.symm_neg LinearIsometryEquiv.symm_neg

variable (R E E₂ E₃)

/-- The natural equivalence `(E × E₂) × E₃ ≃ E × (E₂ × E₃)` is a linear isometry. -/
def prodAssoc [Module R E₂] [Module R E₃] : (E × E₂) × E₃ ≃ₗᵢ[R] E × E₂ × E₃ :=
  { Equiv.prodAssoc E E₂ E₃ with
    toFun := Equiv.prodAssoc E E₂ E₃
    invFun := (Equiv.prodAssoc E E₂ E₃).symm
    map_add' := by simp
                   -- 🎉 no goals
    map_smul' := by simp
                    -- 🎉 no goals
    norm_map' := by
      rintro ⟨⟨e, f⟩, g⟩
      -- ⊢ ‖↑{ toLinearMap := { toAddHom := { toFun := ↑(Equiv.prodAssoc E E₂ E₃), map_ …
      simp only [LinearEquiv.coe_mk, Equiv.prodAssoc_apply, Prod.norm_def, max_assoc] }
      -- 🎉 no goals
#align linear_isometry_equiv.prod_assoc LinearIsometryEquiv.prodAssoc

@[simp]
theorem coe_prodAssoc [Module R E₂] [Module R E₃] :
    (prodAssoc R E E₂ E₃ : (E × E₂) × E₃ → E × E₂ × E₃) = Equiv.prodAssoc E E₂ E₃ :=
  rfl
#align linear_isometry_equiv.coe_prod_assoc LinearIsometryEquiv.coe_prodAssoc

@[simp]
theorem coe_prodAssoc_symm [Module R E₂] [Module R E₃] :
    ((prodAssoc R E E₂ E₃).symm : E × E₂ × E₃ → (E × E₂) × E₃) = (Equiv.prodAssoc E E₂ E₃).symm :=
  rfl
#align linear_isometry_equiv.coe_prod_assoc_symm LinearIsometryEquiv.coe_prodAssoc_symm

/-- If `p` is a submodule that is equal to `⊤`, then `LinearIsometryEquiv.ofTop p hp` is the
"identity" equivalence between `p` and `E`. -/
@[simps! toLinearEquiv apply symm_apply_coe]
def ofTop {R : Type*} [Ring R] [Module R E] (p : Submodule R E) (hp : p = ⊤) : p ≃ₗᵢ[R] E :=
  { p.subtypeₗᵢ with toLinearEquiv := LinearEquiv.ofTop p hp }
#align linear_isometry_equiv.of_top LinearIsometryEquiv.ofTop

variable {R E E₂ E₃} {R' : Type*} [Ring R']

variable [Module R' E] (p q : Submodule R' E)

/-- `LinearEquiv.ofEq` as a `LinearIsometryEquiv`. -/
def ofEq (hpq : p = q) : p ≃ₗᵢ[R'] q :=
  { LinearEquiv.ofEq p q hpq with norm_map' := fun _ => rfl }
#align linear_isometry_equiv.of_eq LinearIsometryEquiv.ofEq

variable {p q}

@[simp]
theorem coe_ofEq_apply (h : p = q) (x : p) : (ofEq p q h x : E) = x :=
  rfl
#align linear_isometry_equiv.coe_of_eq_apply LinearIsometryEquiv.coe_ofEq_apply

@[simp]
theorem ofEq_symm (h : p = q) : (ofEq p q h).symm = ofEq q p h.symm :=
  rfl
#align linear_isometry_equiv.of_eq_symm LinearIsometryEquiv.ofEq_symm

@[simp]
theorem ofEq_rfl : ofEq p p rfl = LinearIsometryEquiv.refl R' p := by funext; rfl
                                                                      -- ⊢ ofEq p p (_ : p = p) = refl R' { x // x ∈ p }
                                                                              -- 🎉 no goals
#align linear_isometry_equiv.of_eq_rfl LinearIsometryEquiv.ofEq_rfl

end LinearIsometryEquiv

/-- Two linear isometries are equal if they are equal on basis vectors. -/
theorem Basis.ext_linearIsometry {ι : Type*} (b : Basis ι R E) {f₁ f₂ : E →ₛₗᵢ[σ₁₂] E₂}
    (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
  LinearIsometry.toLinearMap_injective <| b.ext h
#align basis.ext_linear_isometry Basis.ext_linearIsometry

/-- Two linear isometric equivalences are equal if they are equal on basis vectors. -/
theorem Basis.ext_linearIsometryEquiv {ι : Type*} (b : Basis ι R E) {f₁ f₂ : E ≃ₛₗᵢ[σ₁₂] E₂}
    (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
  LinearIsometryEquiv.toLinearEquiv_injective <| b.ext' h
#align basis.ext_linear_isometry_equiv Basis.ext_linearIsometryEquiv

/-- Reinterpret a `LinearIsometry` as a `LinearIsometryEquiv` to the range. -/
@[simps! apply_coe] -- Porting note: `toLinearEquiv` projection does not simplify using itself
noncomputable def LinearIsometry.equivRange {R S : Type*} [Semiring R] [Ring S] [Module S E]
    [Module R F] {σ₁₂ : R →+* S} {σ₂₁ : S →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (f : F →ₛₗᵢ[σ₁₂] E) : F ≃ₛₗᵢ[σ₁₂] (LinearMap.range f.toLinearMap) :=
  { f with toLinearEquiv := LinearEquiv.ofInjective f.toLinearMap f.injective }
#align linear_isometry.equiv_range LinearIsometry.equivRange
