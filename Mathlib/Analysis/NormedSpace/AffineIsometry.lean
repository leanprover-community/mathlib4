/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module analysis.normed_space.affine_isometry
! leanprover-community/mathlib commit 78261225eb5cedc61c5c74ecb44e5b385d13b733
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.LinearIsometry
import Mathbin.Analysis.Normed.Group.AddTorsor
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.LinearAlgebra.AffineSpace.Restrict
import Mathbin.LinearAlgebra.AffineSpace.MidpointZero

/-!
# Affine isometries

In this file we define `affine_isometry 𝕜 P P₂` to be an affine isometric embedding of normed
add-torsors `P` into `P₂` over normed `𝕜`-spaces and `affine_isometry_equiv` to be an affine
isometric equivalence between `P` and `P₂`.

We also prove basic lemmas and provide convenience constructors.  The choice of these lemmas and
constructors is closely modelled on those for the `linear_isometry` and `affine_map` theories.

Since many elementary properties don't require `‖x‖ = 0 → x = 0` we initially set up the theory for
`seminormed_add_comm_group` and specialize to `normed_add_comm_group` only when needed.

## Notation

We introduce the notation `P →ᵃⁱ[𝕜] P₂` for `affine_isometry 𝕜 P P₂`, and `P ≃ᵃⁱ[𝕜] P₂` for
`affine_isometry_equiv 𝕜 P P₂`.  In contrast with the notation `→ₗᵢ` for linear isometries, `≃ᵢ`
for isometric equivalences, etc., the "i" here is a superscript.  This is for aesthetic reasons to
match the superscript "a" (note that in mathlib `→ᵃ` is an affine map, since `→ₐ` has been taken by
algebra-homomorphisms.)

-/


open Function Set

variable (𝕜 : Type _) {V V₁ V₂ V₃ V₄ : Type _} {P₁ : Type _} (P P₂ : Type _) {P₃ P₄ : Type _}
  [NormedField 𝕜] [SeminormedAddCommGroup V] [SeminormedAddCommGroup V₁] [SeminormedAddCommGroup V₂]
  [SeminormedAddCommGroup V₃] [SeminormedAddCommGroup V₄] [NormedSpace 𝕜 V] [NormedSpace 𝕜 V₁]
  [NormedSpace 𝕜 V₂] [NormedSpace 𝕜 V₃] [NormedSpace 𝕜 V₄] [PseudoMetricSpace P] [MetricSpace P₁]
  [PseudoMetricSpace P₂] [PseudoMetricSpace P₃] [PseudoMetricSpace P₄] [NormedAddTorsor V P]
  [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂] [NormedAddTorsor V₃ P₃] [NormedAddTorsor V₄ P₄]

include V V₂

/-- An `𝕜`-affine isometric embedding of one normed add-torsor over a normed `𝕜`-space into
another. -/
structure AffineIsometry extends P →ᵃ[𝕜] P₂ where
  norm_map : ∀ x : V, ‖linear x‖ = ‖x‖
#align affine_isometry AffineIsometry

omit V V₂

variable {𝕜 P P₂}

-- mathport name: «expr →ᵃⁱ[ ] »
notation:25 -- `→ᵃᵢ` would be more consistent with the linear isometry notation, but it is uglier
P " →ᵃⁱ[" 𝕜:25 "] " P₂:0 => AffineIsometry 𝕜 P P₂

namespace AffineIsometry

variable (f : P →ᵃⁱ[𝕜] P₂)

/-- The underlying linear map of an affine isometry is in fact a linear isometry. -/
protected def linearIsometry : V →ₗᵢ[𝕜] V₂ :=
  { f.linear with norm_map' := f.norm_map }
#align affine_isometry.linear_isometry AffineIsometry.linearIsometry

@[simp]
theorem linear_eq_linearIsometry : f.linear = f.LinearIsometry.toLinearMap :=
  by
  ext
  rfl
#align affine_isometry.linear_eq_linear_isometry AffineIsometry.linear_eq_linearIsometry

include V V₂

instance : CoeFun (P →ᵃⁱ[𝕜] P₂) fun _ => P → P₂ :=
  ⟨fun f => f.toFun⟩

omit V V₂

@[simp]
theorem coe_toAffineMap : ⇑f.toAffineMap = f :=
  rfl
#align affine_isometry.coe_to_affine_map AffineIsometry.coe_toAffineMap

include V V₂

theorem toAffineMap_injective : Injective (toAffineMap : (P →ᵃⁱ[𝕜] P₂) → P →ᵃ[𝕜] P₂)
  | ⟨f, _⟩, ⟨g, _⟩, rfl => rfl
#align affine_isometry.to_affine_map_injective AffineIsometry.toAffineMap_injective

theorem coeFn_injective : @Injective (P →ᵃⁱ[𝕜] P₂) (P → P₂) coeFn :=
  AffineMap.coeFn_injective.comp toAffineMap_injective
#align affine_isometry.coe_fn_injective AffineIsometry.coeFn_injective

@[ext]
theorem ext {f g : P →ᵃⁱ[𝕜] P₂} (h : ∀ x, f x = g x) : f = g :=
  coeFn_injective <| funext h
#align affine_isometry.ext AffineIsometry.ext

omit V V₂

end AffineIsometry

namespace LinearIsometry

variable (f : V →ₗᵢ[𝕜] V₂)

/-- Reinterpret a linear isometry as an affine isometry. -/
def toAffineIsometry : V →ᵃⁱ[𝕜] V₂ :=
  { f.toLinearMap.toAffineMap with norm_map := f.norm_map }
#align linear_isometry.to_affine_isometry LinearIsometry.toAffineIsometry

@[simp]
theorem coe_toAffineIsometry : ⇑(f.toAffineIsometry : V →ᵃⁱ[𝕜] V₂) = f :=
  rfl
#align linear_isometry.coe_to_affine_isometry LinearIsometry.coe_toAffineIsometry

@[simp]
theorem toAffineIsometry_linearIsometry : f.toAffineIsometry.LinearIsometry = f :=
  by
  ext
  rfl
#align linear_isometry.to_affine_isometry_linear_isometry LinearIsometry.toAffineIsometry_linearIsometry

-- somewhat arbitrary choice of simp direction
@[simp]
theorem toAffineIsometry_toAffineMap : f.toAffineIsometry.toAffineMap = f.toLinearMap.toAffineMap :=
  rfl
#align linear_isometry.to_affine_isometry_to_affine_map LinearIsometry.toAffineIsometry_toAffineMap

end LinearIsometry

namespace AffineIsometry

variable (f : P →ᵃⁱ[𝕜] P₂) (f₁ : P₁ →ᵃⁱ[𝕜] P₂)

@[simp]
theorem map_vadd (p : P) (v : V) : f (v +ᵥ p) = f.LinearIsometry v +ᵥ f p :=
  f.toAffineMap.map_vadd p v
#align affine_isometry.map_vadd AffineIsometry.map_vadd

@[simp]
theorem map_vsub (p1 p2 : P) : f.LinearIsometry (p1 -ᵥ p2) = f p1 -ᵥ f p2 :=
  f.toAffineMap.linearMap_vsub p1 p2
#align affine_isometry.map_vsub AffineIsometry.map_vsub

@[simp]
theorem dist_map (x y : P) : dist (f x) (f y) = dist x y := by
  rw [dist_eq_norm_vsub V₂, dist_eq_norm_vsub V, ← map_vsub, f.linear_isometry.norm_map]
#align affine_isometry.dist_map AffineIsometry.dist_map

@[simp]
theorem nndist_map (x y : P) : nndist (f x) (f y) = nndist x y := by simp [nndist_dist]
#align affine_isometry.nndist_map AffineIsometry.nndist_map

@[simp]
theorem edist_map (x y : P) : edist (f x) (f y) = edist x y := by simp [edist_dist]
#align affine_isometry.edist_map AffineIsometry.edist_map

protected theorem isometry : Isometry f :=
  f.edist_map
#align affine_isometry.isometry AffineIsometry.isometry

protected theorem injective : Injective f₁ :=
  f₁.Isometry.Injective
#align affine_isometry.injective AffineIsometry.injective

@[simp]
theorem map_eq_iff {x y : P₁} : f₁ x = f₁ y ↔ x = y :=
  f₁.Injective.eq_iff
#align affine_isometry.map_eq_iff AffineIsometry.map_eq_iff

theorem map_ne {x y : P₁} (h : x ≠ y) : f₁ x ≠ f₁ y :=
  f₁.Injective.Ne h
#align affine_isometry.map_ne AffineIsometry.map_ne

protected theorem lipschitz : LipschitzWith 1 f :=
  f.Isometry.lipschitz
#align affine_isometry.lipschitz AffineIsometry.lipschitz

protected theorem antilipschitz : AntilipschitzWith 1 f :=
  f.Isometry.antilipschitz
#align affine_isometry.antilipschitz AffineIsometry.antilipschitz

@[continuity]
protected theorem continuous : Continuous f :=
  f.Isometry.Continuous
#align affine_isometry.continuous AffineIsometry.continuous

theorem ediam_image (s : Set P) : EMetric.diam (f '' s) = EMetric.diam s :=
  f.Isometry.ediam_image s
#align affine_isometry.ediam_image AffineIsometry.ediam_image

theorem ediam_range : EMetric.diam (range f) = EMetric.diam (univ : Set P) :=
  f.Isometry.ediam_range
#align affine_isometry.ediam_range AffineIsometry.ediam_range

theorem diam_image (s : Set P) : Metric.diam (f '' s) = Metric.diam s :=
  f.Isometry.diam_image s
#align affine_isometry.diam_image AffineIsometry.diam_image

theorem diam_range : Metric.diam (range f) = Metric.diam (univ : Set P) :=
  f.Isometry.diam_range
#align affine_isometry.diam_range AffineIsometry.diam_range

@[simp]
theorem comp_continuous_iff {α : Type _} [TopologicalSpace α] {g : α → P} :
    Continuous (f ∘ g) ↔ Continuous g :=
  f.Isometry.comp_continuous_iff
#align affine_isometry.comp_continuous_iff AffineIsometry.comp_continuous_iff

include V

/-- The identity affine isometry. -/
def id : P →ᵃⁱ[𝕜] P :=
  ⟨AffineMap.id 𝕜 P, fun x => rfl⟩
#align affine_isometry.id AffineIsometry.id

@[simp]
theorem coe_id : ⇑(id : P →ᵃⁱ[𝕜] P) = id :=
  rfl
#align affine_isometry.coe_id AffineIsometry.coe_id

@[simp]
theorem id_apply (x : P) : (AffineIsometry.id : P →ᵃⁱ[𝕜] P) x = x :=
  rfl
#align affine_isometry.id_apply AffineIsometry.id_apply

@[simp]
theorem id_toAffineMap : (id.toAffineMap : P →ᵃ[𝕜] P) = AffineMap.id 𝕜 P :=
  rfl
#align affine_isometry.id_to_affine_map AffineIsometry.id_toAffineMap

instance : Inhabited (P →ᵃⁱ[𝕜] P) :=
  ⟨id⟩

include V₂ V₃

/-- Composition of affine isometries. -/
def comp (g : P₂ →ᵃⁱ[𝕜] P₃) (f : P →ᵃⁱ[𝕜] P₂) : P →ᵃⁱ[𝕜] P₃ :=
  ⟨g.toAffineMap.comp f.toAffineMap, fun x => (g.norm_map _).trans (f.norm_map _)⟩
#align affine_isometry.comp AffineIsometry.comp

@[simp]
theorem coe_comp (g : P₂ →ᵃⁱ[𝕜] P₃) (f : P →ᵃⁱ[𝕜] P₂) : ⇑(g.comp f) = g ∘ f :=
  rfl
#align affine_isometry.coe_comp AffineIsometry.coe_comp

omit V V₂ V₃

@[simp]
theorem id_comp : (id : P₂ →ᵃⁱ[𝕜] P₂).comp f = f :=
  ext fun x => rfl
#align affine_isometry.id_comp AffineIsometry.id_comp

@[simp]
theorem comp_id : f.comp id = f :=
  ext fun x => rfl
#align affine_isometry.comp_id AffineIsometry.comp_id

include V V₂ V₃ V₄

theorem comp_assoc (f : P₃ →ᵃⁱ[𝕜] P₄) (g : P₂ →ᵃⁱ[𝕜] P₃) (h : P →ᵃⁱ[𝕜] P₂) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align affine_isometry.comp_assoc AffineIsometry.comp_assoc

omit V₂ V₃ V₄

instance : Monoid (P →ᵃⁱ[𝕜] P) where
  one := id
  mul := comp
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

@[simp]
theorem coe_one : ⇑(1 : P →ᵃⁱ[𝕜] P) = id :=
  rfl
#align affine_isometry.coe_one AffineIsometry.coe_one

@[simp]
theorem coe_mul (f g : P →ᵃⁱ[𝕜] P) : ⇑(f * g) = f ∘ g :=
  rfl
#align affine_isometry.coe_mul AffineIsometry.coe_mul

end AffineIsometry

namespace AffineSubspace

include V

/-- `affine_subspace.subtype` as an `affine_isometry`. -/
def subtypeₐᵢ (s : AffineSubspace 𝕜 P) [Nonempty s] : s →ᵃⁱ[𝕜] P :=
  { s.Subtype with norm_map := s.direction.subtypeₗᵢ.norm_map }
#align affine_subspace.subtypeₐᵢ AffineSubspace.subtypeₐᵢ

theorem subtypeₐᵢ_linear (s : AffineSubspace 𝕜 P) [Nonempty s] :
    s.subtypeₐᵢ.linear = s.direction.Subtype :=
  rfl
#align affine_subspace.subtypeₐᵢ_linear AffineSubspace.subtypeₐᵢ_linear

@[simp]
theorem subtypeₐᵢ_linearIsometry (s : AffineSubspace 𝕜 P) [Nonempty s] :
    s.subtypeₐᵢ.LinearIsometry = s.direction.subtypeₗᵢ :=
  rfl
#align affine_subspace.subtypeₐᵢ_linear_isometry AffineSubspace.subtypeₐᵢ_linearIsometry

@[simp]
theorem coe_subtypeₐᵢ (s : AffineSubspace 𝕜 P) [Nonempty s] : ⇑s.subtypeₐᵢ = s.Subtype :=
  rfl
#align affine_subspace.coe_subtypeₐᵢ AffineSubspace.coe_subtypeₐᵢ

@[simp]
theorem subtypeₐᵢ_toAffineMap (s : AffineSubspace 𝕜 P) [Nonempty s] :
    s.subtypeₐᵢ.toAffineMap = s.Subtype :=
  rfl
#align affine_subspace.subtypeₐᵢ_to_affine_map AffineSubspace.subtypeₐᵢ_toAffineMap

end AffineSubspace

variable (𝕜 P P₂)

include V V₂

/-- A affine isometric equivalence between two normed vector spaces. -/
structure AffineIsometryEquiv extends P ≃ᵃ[𝕜] P₂ where
  norm_map : ∀ x, ‖linear x‖ = ‖x‖
#align affine_isometry_equiv AffineIsometryEquiv

variable {𝕜 P P₂}

omit V V₂

-- mathport name: «expr ≃ᵃⁱ[ ] »
notation:25
  -- `≃ᵃᵢ` would be more consistent with the linear isometry equiv notation, but it is uglier
P " ≃ᵃⁱ[" 𝕜:25 "] " P₂:0 => AffineIsometryEquiv 𝕜 P P₂

namespace AffineIsometryEquiv

variable (e : P ≃ᵃⁱ[𝕜] P₂)

/-- The underlying linear equiv of an affine isometry equiv is in fact a linear isometry equiv. -/
protected def linearIsometryEquiv : V ≃ₗᵢ[𝕜] V₂ :=
  { e.linear with norm_map' := e.norm_map }
#align affine_isometry_equiv.linear_isometry_equiv AffineIsometryEquiv.linearIsometryEquiv

@[simp]
theorem linear_eq_linear_isometry : e.linear = e.LinearIsometryEquiv.toLinearEquiv :=
  by
  ext
  rfl
#align affine_isometry_equiv.linear_eq_linear_isometry AffineIsometryEquiv.linear_eq_linear_isometry

include V V₂

instance : CoeFun (P ≃ᵃⁱ[𝕜] P₂) fun _ => P → P₂ :=
  ⟨fun f => f.toFun⟩

@[simp]
theorem coe_mk (e : P ≃ᵃ[𝕜] P₂) (he : ∀ x, ‖e.linear x‖ = ‖x‖) : ⇑(mk e he) = e :=
  rfl
#align affine_isometry_equiv.coe_mk AffineIsometryEquiv.coe_mk

@[simp]
theorem coe_toAffineEquiv (e : P ≃ᵃⁱ[𝕜] P₂) : ⇑e.toAffineEquiv = e :=
  rfl
#align affine_isometry_equiv.coe_to_affine_equiv AffineIsometryEquiv.coe_toAffineEquiv

theorem toAffineEquiv_injective : Injective (toAffineEquiv : (P ≃ᵃⁱ[𝕜] P₂) → P ≃ᵃ[𝕜] P₂)
  | ⟨e, _⟩, ⟨_, _⟩, rfl => rfl
#align affine_isometry_equiv.to_affine_equiv_injective AffineIsometryEquiv.toAffineEquiv_injective

@[ext]
theorem ext {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : ∀ x, e x = e' x) : e = e' :=
  toAffineEquiv_injective <| AffineEquiv.ext h
#align affine_isometry_equiv.ext AffineIsometryEquiv.ext

omit V V₂

/-- Reinterpret a `affine_isometry_equiv` as a `affine_isometry`. -/
def toAffineIsometry : P →ᵃⁱ[𝕜] P₂ :=
  ⟨e.1.toAffineMap, e.2⟩
#align affine_isometry_equiv.to_affine_isometry AffineIsometryEquiv.toAffineIsometry

@[simp]
theorem coe_toAffineIsometry : ⇑e.toAffineIsometry = e :=
  rfl
#align affine_isometry_equiv.coe_to_affine_isometry AffineIsometryEquiv.coe_toAffineIsometry

/-- Construct an affine isometry equivalence by verifying the relation between the map and its
linear part at one base point. Namely, this function takes a map `e : P₁ → P₂`, a linear isometry
equivalence `e' : V₁ ≃ᵢₗ[k] V₂`, and a point `p` such that for any other point `p'` we have
`e p' = e' (p' -ᵥ p) +ᵥ e p`. -/
def mk' (e : P₁ → P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p : P₁) (h : ∀ p' : P₁, e p' = e' (p' -ᵥ p) +ᵥ e p) :
    P₁ ≃ᵃⁱ[𝕜] P₂ :=
  { AffineEquiv.mk' e e'.toLinearEquiv p h with norm_map := e'.norm_map }
#align affine_isometry_equiv.mk' AffineIsometryEquiv.mk'

@[simp]
theorem coe_mk' (e : P₁ → P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p h) : ⇑(mk' e e' p h) = e :=
  rfl
#align affine_isometry_equiv.coe_mk' AffineIsometryEquiv.coe_mk'

@[simp]
theorem linearIsometryEquiv_mk' (e : P₁ → P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p h) :
    (mk' e e' p h).LinearIsometryEquiv = e' := by
  ext
  rfl
#align affine_isometry_equiv.linear_isometry_equiv_mk' AffineIsometryEquiv.linearIsometryEquiv_mk'

end AffineIsometryEquiv

namespace LinearIsometryEquiv

variable (e : V ≃ₗᵢ[𝕜] V₂)

/-- Reinterpret a linear isometry equiv as an affine isometry equiv. -/
def toAffineIsometryEquiv : V ≃ᵃⁱ[𝕜] V₂ :=
  { e.toLinearEquiv.toAffineEquiv with norm_map := e.norm_map }
#align linear_isometry_equiv.to_affine_isometry_equiv LinearIsometryEquiv.toAffineIsometryEquiv

@[simp]
theorem coe_toAffineIsometryEquiv : ⇑(e.toAffineIsometryEquiv : V ≃ᵃⁱ[𝕜] V₂) = e :=
  rfl
#align linear_isometry_equiv.coe_to_affine_isometry_equiv LinearIsometryEquiv.coe_toAffineIsometryEquiv

@[simp]
theorem toAffineIsometryEquiv_linearIsometryEquiv :
    e.toAffineIsometryEquiv.LinearIsometryEquiv = e :=
  by
  ext
  rfl
#align linear_isometry_equiv.to_affine_isometry_equiv_linear_isometry_equiv LinearIsometryEquiv.toAffineIsometryEquiv_linearIsometryEquiv

-- somewhat arbitrary choice of simp direction
@[simp]
theorem toAffineIsometryEquiv_toAffineEquiv :
    e.toAffineIsometryEquiv.toAffineEquiv = e.toLinearEquiv.toAffineEquiv :=
  rfl
#align linear_isometry_equiv.to_affine_isometry_equiv_to_affine_equiv LinearIsometryEquiv.toAffineIsometryEquiv_toAffineEquiv

-- somewhat arbitrary choice of simp direction
@[simp]
theorem toAffineIsometryEquiv_toAffineIsometry :
    e.toAffineIsometryEquiv.toAffineIsometry = e.toLinearIsometry.toAffineIsometry :=
  rfl
#align linear_isometry_equiv.to_affine_isometry_equiv_to_affine_isometry LinearIsometryEquiv.toAffineIsometryEquiv_toAffineIsometry

end LinearIsometryEquiv

namespace AffineIsometryEquiv

variable (e : P ≃ᵃⁱ[𝕜] P₂)

protected theorem isometry : Isometry e :=
  e.toAffineIsometry.Isometry
#align affine_isometry_equiv.isometry AffineIsometryEquiv.isometry

/-- Reinterpret a `affine_isometry_equiv` as an `isometry_equiv`. -/
def toIsometryEquiv : P ≃ᵢ P₂ :=
  ⟨e.toAffineEquiv.toEquiv, e.Isometry⟩
#align affine_isometry_equiv.to_isometry_equiv AffineIsometryEquiv.toIsometryEquiv

@[simp]
theorem coe_toIsometryEquiv : ⇑e.toIsometryEquiv = e :=
  rfl
#align affine_isometry_equiv.coe_to_isometry_equiv AffineIsometryEquiv.coe_toIsometryEquiv

include V V₂

theorem range_eq_univ (e : P ≃ᵃⁱ[𝕜] P₂) : Set.range e = Set.univ :=
  by
  rw [← coe_to_isometry_equiv]
  exact IsometryEquiv.range_eq_univ _
#align affine_isometry_equiv.range_eq_univ AffineIsometryEquiv.range_eq_univ

omit V V₂

/-- Reinterpret a `affine_isometry_equiv` as an `homeomorph`. -/
def toHomeomorph : P ≃ₜ P₂ :=
  e.toIsometryEquiv.toHomeomorph
#align affine_isometry_equiv.to_homeomorph AffineIsometryEquiv.toHomeomorph

@[simp]
theorem coe_toHomeomorph : ⇑e.toHomeomorph = e :=
  rfl
#align affine_isometry_equiv.coe_to_homeomorph AffineIsometryEquiv.coe_toHomeomorph

protected theorem continuous : Continuous e :=
  e.Isometry.Continuous
#align affine_isometry_equiv.continuous AffineIsometryEquiv.continuous

protected theorem continuousAt {x} : ContinuousAt e x :=
  e.Continuous.ContinuousAt
#align affine_isometry_equiv.continuous_at AffineIsometryEquiv.continuousAt

protected theorem continuousOn {s} : ContinuousOn e s :=
  e.Continuous.ContinuousOn
#align affine_isometry_equiv.continuous_on AffineIsometryEquiv.continuousOn

protected theorem continuousWithinAt {s x} : ContinuousWithinAt e s x :=
  e.Continuous.ContinuousWithinAt
#align affine_isometry_equiv.continuous_within_at AffineIsometryEquiv.continuousWithinAt

variable (𝕜 P)

include V

/-- Identity map as a `affine_isometry_equiv`. -/
def refl : P ≃ᵃⁱ[𝕜] P :=
  ⟨AffineEquiv.refl 𝕜 P, fun x => rfl⟩
#align affine_isometry_equiv.refl AffineIsometryEquiv.refl

variable {𝕜 P}

instance : Inhabited (P ≃ᵃⁱ[𝕜] P) :=
  ⟨refl 𝕜 P⟩

@[simp]
theorem coe_refl : ⇑(refl 𝕜 P) = id :=
  rfl
#align affine_isometry_equiv.coe_refl AffineIsometryEquiv.coe_refl

@[simp]
theorem toAffineEquiv_refl : (refl 𝕜 P).toAffineEquiv = AffineEquiv.refl 𝕜 P :=
  rfl
#align affine_isometry_equiv.to_affine_equiv_refl AffineIsometryEquiv.toAffineEquiv_refl

@[simp]
theorem toIsometryEquiv_refl : (refl 𝕜 P).toIsometryEquiv = IsometryEquiv.refl P :=
  rfl
#align affine_isometry_equiv.to_isometry_equiv_refl AffineIsometryEquiv.toIsometryEquiv_refl

@[simp]
theorem toHomeomorph_refl : (refl 𝕜 P).toHomeomorph = Homeomorph.refl P :=
  rfl
#align affine_isometry_equiv.to_homeomorph_refl AffineIsometryEquiv.toHomeomorph_refl

omit V

/-- The inverse `affine_isometry_equiv`. -/
def symm : P₂ ≃ᵃⁱ[𝕜] P :=
  { e.toAffineEquiv.symm with norm_map := e.LinearIsometryEquiv.symm.norm_map }
#align affine_isometry_equiv.symm AffineIsometryEquiv.symm

@[simp]
theorem apply_symm_apply (x : P₂) : e (e.symm x) = x :=
  e.toAffineEquiv.apply_symm_apply x
#align affine_isometry_equiv.apply_symm_apply AffineIsometryEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (x : P) : e.symm (e x) = x :=
  e.toAffineEquiv.symm_apply_apply x
#align affine_isometry_equiv.symm_apply_apply AffineIsometryEquiv.symm_apply_apply

@[simp]
theorem symm_symm : e.symm.symm = e :=
  ext fun x => rfl
#align affine_isometry_equiv.symm_symm AffineIsometryEquiv.symm_symm

@[simp]
theorem toAffineEquiv_symm : e.toAffineEquiv.symm = e.symm.toAffineEquiv :=
  rfl
#align affine_isometry_equiv.to_affine_equiv_symm AffineIsometryEquiv.toAffineEquiv_symm

@[simp]
theorem toIsometryEquiv_symm : e.toIsometryEquiv.symm = e.symm.toIsometryEquiv :=
  rfl
#align affine_isometry_equiv.to_isometry_equiv_symm AffineIsometryEquiv.toIsometryEquiv_symm

@[simp]
theorem toHomeomorph_symm : e.toHomeomorph.symm = e.symm.toHomeomorph :=
  rfl
#align affine_isometry_equiv.to_homeomorph_symm AffineIsometryEquiv.toHomeomorph_symm

include V₃

/-- Composition of `affine_isometry_equiv`s as a `affine_isometry_equiv`. -/
def trans (e' : P₂ ≃ᵃⁱ[𝕜] P₃) : P ≃ᵃⁱ[𝕜] P₃ :=
  ⟨e.toAffineEquiv.trans e'.toAffineEquiv, fun x => (e'.norm_map _).trans (e.norm_map _)⟩
#align affine_isometry_equiv.trans AffineIsometryEquiv.trans

include V V₂

@[simp]
theorem coe_trans (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl
#align affine_isometry_equiv.coe_trans AffineIsometryEquiv.coe_trans

omit V V₂ V₃

@[simp]
theorem trans_refl : e.trans (refl 𝕜 P₂) = e :=
  ext fun x => rfl
#align affine_isometry_equiv.trans_refl AffineIsometryEquiv.trans_refl

@[simp]
theorem refl_trans : (refl 𝕜 P).trans e = e :=
  ext fun x => rfl
#align affine_isometry_equiv.refl_trans AffineIsometryEquiv.refl_trans

@[simp]
theorem self_trans_symm : e.trans e.symm = refl 𝕜 P :=
  ext e.symm_apply_apply
#align affine_isometry_equiv.self_trans_symm AffineIsometryEquiv.self_trans_symm

@[simp]
theorem symm_trans_self : e.symm.trans e = refl 𝕜 P₂ :=
  ext e.apply_symm_apply
#align affine_isometry_equiv.symm_trans_self AffineIsometryEquiv.symm_trans_self

include V V₂ V₃

@[simp]
theorem coe_symm_trans (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃) :
    ⇑(e₁.trans e₂).symm = e₁.symm ∘ e₂.symm :=
  rfl
#align affine_isometry_equiv.coe_symm_trans AffineIsometryEquiv.coe_symm_trans

include V₄

theorem trans_assoc (ePP₂ : P ≃ᵃⁱ[𝕜] P₂) (eP₂G : P₂ ≃ᵃⁱ[𝕜] P₃) (eGG' : P₃ ≃ᵃⁱ[𝕜] P₄) :
    ePP₂.trans (eP₂G.trans eGG') = (ePP₂.trans eP₂G).trans eGG' :=
  rfl
#align affine_isometry_equiv.trans_assoc AffineIsometryEquiv.trans_assoc

omit V₂ V₃ V₄

/-- The group of affine isometries of a `normed_add_torsor`, `P`. -/
instance : Group (P ≃ᵃⁱ[𝕜] P) where
  mul e₁ e₂ := e₂.trans e₁
  one := refl _ _
  inv := symm
  one_mul := trans_refl
  mul_one := refl_trans
  mul_assoc _ _ _ := trans_assoc _ _ _
  mul_left_inv := self_trans_symm

@[simp]
theorem coe_one : ⇑(1 : P ≃ᵃⁱ[𝕜] P) = id :=
  rfl
#align affine_isometry_equiv.coe_one AffineIsometryEquiv.coe_one

@[simp]
theorem coe_mul (e e' : P ≃ᵃⁱ[𝕜] P) : ⇑(e * e') = e ∘ e' :=
  rfl
#align affine_isometry_equiv.coe_mul AffineIsometryEquiv.coe_mul

@[simp]
theorem coe_inv (e : P ≃ᵃⁱ[𝕜] P) : ⇑e⁻¹ = e.symm :=
  rfl
#align affine_isometry_equiv.coe_inv AffineIsometryEquiv.coe_inv

omit V

@[simp]
theorem map_vadd (p : P) (v : V) : e (v +ᵥ p) = e.LinearIsometryEquiv v +ᵥ e p :=
  e.toAffineIsometry.map_vadd p v
#align affine_isometry_equiv.map_vadd AffineIsometryEquiv.map_vadd

@[simp]
theorem map_vsub (p1 p2 : P) : e.LinearIsometryEquiv (p1 -ᵥ p2) = e p1 -ᵥ e p2 :=
  e.toAffineIsometry.map_vsub p1 p2
#align affine_isometry_equiv.map_vsub AffineIsometryEquiv.map_vsub

@[simp]
theorem dist_map (x y : P) : dist (e x) (e y) = dist x y :=
  e.toAffineIsometry.dist_map x y
#align affine_isometry_equiv.dist_map AffineIsometryEquiv.dist_map

@[simp]
theorem edist_map (x y : P) : edist (e x) (e y) = edist x y :=
  e.toAffineIsometry.edist_map x y
#align affine_isometry_equiv.edist_map AffineIsometryEquiv.edist_map

protected theorem bijective : Bijective e :=
  e.1.Bijective
#align affine_isometry_equiv.bijective AffineIsometryEquiv.bijective

protected theorem injective : Injective e :=
  e.1.Injective
#align affine_isometry_equiv.injective AffineIsometryEquiv.injective

protected theorem surjective : Surjective e :=
  e.1.Surjective
#align affine_isometry_equiv.surjective AffineIsometryEquiv.surjective

@[simp]
theorem map_eq_iff {x y : P} : e x = e y ↔ x = y :=
  e.Injective.eq_iff
#align affine_isometry_equiv.map_eq_iff AffineIsometryEquiv.map_eq_iff

theorem map_ne {x y : P} (h : x ≠ y) : e x ≠ e y :=
  e.Injective.Ne h
#align affine_isometry_equiv.map_ne AffineIsometryEquiv.map_ne

protected theorem lipschitz : LipschitzWith 1 e :=
  e.Isometry.lipschitz
#align affine_isometry_equiv.lipschitz AffineIsometryEquiv.lipschitz

protected theorem antilipschitz : AntilipschitzWith 1 e :=
  e.Isometry.antilipschitz
#align affine_isometry_equiv.antilipschitz AffineIsometryEquiv.antilipschitz

@[simp]
theorem ediam_image (s : Set P) : EMetric.diam (e '' s) = EMetric.diam s :=
  e.Isometry.ediam_image s
#align affine_isometry_equiv.ediam_image AffineIsometryEquiv.ediam_image

@[simp]
theorem diam_image (s : Set P) : Metric.diam (e '' s) = Metric.diam s :=
  e.Isometry.diam_image s
#align affine_isometry_equiv.diam_image AffineIsometryEquiv.diam_image

variable {α : Type _} [TopologicalSpace α]

@[simp]
theorem comp_continuousOn_iff {f : α → P} {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.Isometry.comp_continuousOn_iff
#align affine_isometry_equiv.comp_continuous_on_iff AffineIsometryEquiv.comp_continuousOn_iff

@[simp]
theorem comp_continuous_iff {f : α → P} : Continuous (e ∘ f) ↔ Continuous f :=
  e.Isometry.comp_continuous_iff
#align affine_isometry_equiv.comp_continuous_iff AffineIsometryEquiv.comp_continuous_iff

section Constructions

variable (𝕜)

/-- The map `v ↦ v +ᵥ p` as an affine isometric equivalence between `V` and `P`. -/
def vaddConst (p : P) : V ≃ᵃⁱ[𝕜] P :=
  { AffineEquiv.vaddConst 𝕜 p with norm_map := fun x => rfl }
#align affine_isometry_equiv.vadd_const AffineIsometryEquiv.vaddConst

variable {𝕜}

include V

@[simp]
theorem coe_vaddConst (p : P) : ⇑(vaddConst 𝕜 p) = fun v => v +ᵥ p :=
  rfl
#align affine_isometry_equiv.coe_vadd_const AffineIsometryEquiv.coe_vaddConst

@[simp]
theorem coe_vaddConst_symm (p : P) : ⇑(vaddConst 𝕜 p).symm = fun p' => p' -ᵥ p :=
  rfl
#align affine_isometry_equiv.coe_vadd_const_symm AffineIsometryEquiv.coe_vaddConst_symm

@[simp]
theorem vaddConst_toAffineEquiv (p : P) :
    (vaddConst 𝕜 p).toAffineEquiv = AffineEquiv.vaddConst 𝕜 p :=
  rfl
#align affine_isometry_equiv.vadd_const_to_affine_equiv AffineIsometryEquiv.vaddConst_toAffineEquiv

omit V

variable (𝕜)

/-- `p' ↦ p -ᵥ p'` as an affine isometric equivalence. -/
def constVsub (p : P) : P ≃ᵃⁱ[𝕜] V :=
  { AffineEquiv.constVSub 𝕜 p with norm_map := norm_neg }
#align affine_isometry_equiv.const_vsub AffineIsometryEquiv.constVsub

variable {𝕜}

include V

@[simp]
theorem coe_constVsub (p : P) : ⇑(constVsub 𝕜 p) = (· -ᵥ ·) p :=
  rfl
#align affine_isometry_equiv.coe_const_vsub AffineIsometryEquiv.coe_constVsub

@[simp]
theorem symm_constVsub (p : P) :
    (constVsub 𝕜 p).symm =
      (LinearIsometryEquiv.neg 𝕜).toAffineIsometryEquiv.trans (vaddConst 𝕜 p) :=
  by
  ext
  rfl
#align affine_isometry_equiv.symm_const_vsub AffineIsometryEquiv.symm_constVsub

omit V

variable (𝕜 P)

/-- Translation by `v` (that is, the map `p ↦ v +ᵥ p`) as an affine isometric automorphism of `P`.
-/
def constVadd (v : V) : P ≃ᵃⁱ[𝕜] P :=
  { AffineEquiv.constVAdd 𝕜 P v with norm_map := fun x => rfl }
#align affine_isometry_equiv.const_vadd AffineIsometryEquiv.constVadd

variable {𝕜 P}

@[simp]
theorem coe_constVadd (v : V) : ⇑(constVadd 𝕜 P v : P ≃ᵃⁱ[𝕜] P) = (· +ᵥ ·) v :=
  rfl
#align affine_isometry_equiv.coe_const_vadd AffineIsometryEquiv.coe_constVadd

@[simp]
theorem constVadd_zero : constVadd 𝕜 P (0 : V) = refl 𝕜 P :=
  ext <| zero_vadd V
#align affine_isometry_equiv.const_vadd_zero AffineIsometryEquiv.constVadd_zero

include 𝕜 V

/-- The map `g` from `V` to `V₂` corresponding to a map `f` from `P` to `P₂`, at a base point `p`,
is an isometry if `f` is one. -/
theorem vadd_vsub {f : P → P₂} (hf : Isometry f) {p : P} {g : V → V₂}
    (hg : ∀ v, g v = f (v +ᵥ p) -ᵥ f p) : Isometry g :=
  by
  convert(vadd_const 𝕜 (f p)).symm.Isometry.comp (hf.comp (vadd_const 𝕜 p).Isometry)
  exact funext hg
#align affine_isometry_equiv.vadd_vsub AffineIsometryEquiv.vadd_vsub

omit 𝕜

variable (𝕜)

/-- Point reflection in `x` as an affine isometric automorphism. -/
def pointReflection (x : P) : P ≃ᵃⁱ[𝕜] P :=
  (constVsub 𝕜 x).trans (vaddConst 𝕜 x)
#align affine_isometry_equiv.point_reflection AffineIsometryEquiv.pointReflection

variable {𝕜}

theorem pointReflection_apply (x y : P) : (pointReflection 𝕜 x) y = x -ᵥ y +ᵥ x :=
  rfl
#align affine_isometry_equiv.point_reflection_apply AffineIsometryEquiv.pointReflection_apply

@[simp]
theorem pointReflection_toAffineEquiv (x : P) :
    (pointReflection 𝕜 x).toAffineEquiv = AffineEquiv.pointReflection 𝕜 x :=
  rfl
#align affine_isometry_equiv.point_reflection_to_affine_equiv AffineIsometryEquiv.pointReflection_toAffineEquiv

@[simp]
theorem pointReflection_self (x : P) : pointReflection 𝕜 x x = x :=
  AffineEquiv.pointReflection_self 𝕜 x
#align affine_isometry_equiv.point_reflection_self AffineIsometryEquiv.pointReflection_self

theorem pointReflection_involutive (x : P) : Function.Involutive (pointReflection 𝕜 x) :=
  Equiv.pointReflection_involutive x
#align affine_isometry_equiv.point_reflection_involutive AffineIsometryEquiv.pointReflection_involutive

@[simp]
theorem pointReflection_symm (x : P) : (pointReflection 𝕜 x).symm = pointReflection 𝕜 x :=
  toAffineEquiv_injective <| AffineEquiv.pointReflection_symm 𝕜 x
#align affine_isometry_equiv.point_reflection_symm AffineIsometryEquiv.pointReflection_symm

@[simp]
theorem dist_pointReflection_fixed (x y : P) : dist (pointReflection 𝕜 x y) x = dist y x := by
  rw [← (point_reflection 𝕜 x).dist_map y x, point_reflection_self]
#align affine_isometry_equiv.dist_point_reflection_fixed AffineIsometryEquiv.dist_pointReflection_fixed

theorem dist_pointReflection_self' (x y : P) : dist (pointReflection 𝕜 x y) y = ‖bit0 (x -ᵥ y)‖ :=
  by rw [point_reflection_apply, dist_eq_norm_vsub V, vadd_vsub_assoc, bit0]
#align affine_isometry_equiv.dist_point_reflection_self' AffineIsometryEquiv.dist_pointReflection_self'

theorem dist_pointReflection_self (x y : P) :
    dist (pointReflection 𝕜 x y) y = ‖(2 : 𝕜)‖ * dist x y := by
  rw [dist_point_reflection_self', ← two_smul' 𝕜 (x -ᵥ y), norm_smul, ← dist_eq_norm_vsub V]
#align affine_isometry_equiv.dist_point_reflection_self AffineIsometryEquiv.dist_pointReflection_self

theorem pointReflection_fixed_iff [Invertible (2 : 𝕜)] {x y : P} :
    pointReflection 𝕜 x y = y ↔ y = x :=
  AffineEquiv.pointReflection_fixed_iff_of_module 𝕜
#align affine_isometry_equiv.point_reflection_fixed_iff AffineIsometryEquiv.pointReflection_fixed_iff

variable [NormedSpace ℝ V]

theorem dist_pointReflection_self_real (x y : P) : dist (pointReflection ℝ x y) y = 2 * dist x y :=
  by rw [dist_point_reflection_self, Real.norm_two]
#align affine_isometry_equiv.dist_point_reflection_self_real AffineIsometryEquiv.dist_pointReflection_self_real

@[simp]
theorem pointReflection_midpoint_left (x y : P) : pointReflection ℝ (midpoint ℝ x y) x = y :=
  AffineEquiv.pointReflection_midpoint_left x y
#align affine_isometry_equiv.point_reflection_midpoint_left AffineIsometryEquiv.pointReflection_midpoint_left

@[simp]
theorem pointReflection_midpoint_right (x y : P) : pointReflection ℝ (midpoint ℝ x y) y = x :=
  AffineEquiv.pointReflection_midpoint_right x y
#align affine_isometry_equiv.point_reflection_midpoint_right AffineIsometryEquiv.pointReflection_midpoint_right

end Constructions

end AffineIsometryEquiv

include V V₂

/-- If `f` is an affine map, then its linear part is continuous iff `f` is continuous. -/
theorem AffineMap.continuous_linear_iff {f : P →ᵃ[𝕜] P₂} : Continuous f.linear ↔ Continuous f :=
  by
  inhabit P
  have :
    (f.linear : V → V₂) =
      (AffineIsometryEquiv.vaddConst 𝕜 <| f default).toHomeomorph.symm ∘
        f ∘ (AffineIsometryEquiv.vaddConst 𝕜 default).toHomeomorph :=
    by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_continuous_iff, Homeomorph.comp_continuous_iff']
#align affine_map.continuous_linear_iff AffineMap.continuous_linear_iff

/-- If `f` is an affine map, then its linear part is an open map iff `f` is an open map. -/
theorem AffineMap.isOpenMap_linear_iff {f : P →ᵃ[𝕜] P₂} : IsOpenMap f.linear ↔ IsOpenMap f :=
  by
  inhabit P
  have :
    (f.linear : V → V₂) =
      (AffineIsometryEquiv.vaddConst 𝕜 <| f default).toHomeomorph.symm ∘
        f ∘ (AffineIsometryEquiv.vaddConst 𝕜 default).toHomeomorph :=
    by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_isOpenMap_iff, Homeomorph.comp_isOpenMap_iff']
#align affine_map.is_open_map_linear_iff AffineMap.isOpenMap_linear_iff

attribute [local instance, local nolint fails_quickly] AffineSubspace.nonempty_map

include V₁

omit V

namespace AffineSubspace

/-- An affine subspace is isomorphic to its image under an injective affine map.
This is the affine version of `submodule.equiv_map_of_injective`.
-/
@[simps]
noncomputable def equivMapOfInjective (E : AffineSubspace 𝕜 P₁) [Nonempty E] (φ : P₁ →ᵃ[𝕜] P₂)
    (hφ : Function.Injective φ) : E ≃ᵃ[𝕜] E.map φ :=
  {
    Equiv.Set.image _ (E : Set P₁)
      hφ with
    linear :=
      (E.direction.equivMapOfInjective φ.linear (φ.linear_injective_iff.mpr hφ)).trans
        (LinearEquiv.ofEq _ _ (AffineSubspace.map_direction _ _).symm)
    map_vadd' := fun p v => Subtype.ext <| φ.map_vadd p v }
#align affine_subspace.equiv_map_of_injective AffineSubspace.equivMapOfInjective

/-- Restricts an affine isometry to an affine isometry equivalence between a nonempty affine
subspace `E` and its image.

This is an isometry version of `affine_subspace.equiv_map`, having a stronger premise and a stronger
conclusion.
-/
noncomputable def isometryEquivMap (φ : P₁ →ᵃⁱ[𝕜] P₂) (E : AffineSubspace 𝕜 P₁) [Nonempty E] :
    E ≃ᵃⁱ[𝕜] E.map φ.toAffineMap :=
  ⟨E.equivMapOfInjective φ.toAffineMap φ.Injective, fun _ => φ.norm_map _⟩
#align affine_subspace.isometry_equiv_map AffineSubspace.isometryEquivMap

@[simp]
theorem isometryEquivMap.apply_symm_apply {E : AffineSubspace 𝕜 P₁} [Nonempty E] {φ : P₁ →ᵃⁱ[𝕜] P₂}
    (x : E.map φ.toAffineMap) : φ ((E.isometryEquivMap φ).symm x) = x :=
  congr_arg coe <| (E.isometryEquivMap φ).apply_symm_apply _
#align affine_subspace.isometry_equiv_map.apply_symm_apply AffineSubspace.isometryEquivMap.apply_symm_apply

@[simp]
theorem isometryEquivMap.coe_apply (φ : P₁ →ᵃⁱ[𝕜] P₂) (E : AffineSubspace 𝕜 P₁) [Nonempty E]
    (g : E) : ↑(E.isometryEquivMap φ g) = φ g :=
  rfl
#align affine_subspace.isometry_equiv_map.coe_apply AffineSubspace.isometryEquivMap.coe_apply

@[simp]
theorem isometryEquivMap.toAffineMap_eq (φ : P₁ →ᵃⁱ[𝕜] P₂) (E : AffineSubspace 𝕜 P₁) [Nonempty E] :
    (E.isometryEquivMap φ).toAffineMap = E.equivMapOfInjective φ.toAffineMap φ.Injective :=
  rfl
#align affine_subspace.isometry_equiv_map.to_affine_map_eq AffineSubspace.isometryEquivMap.toAffineMap_eq

end AffineSubspace

