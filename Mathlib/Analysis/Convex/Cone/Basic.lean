/-
Copyright (c) 2022 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade, Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Cone.Closure
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.Algebra.Order.Module
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Proper cones

We define a *proper cone* as a closed, pointed cone. Proper cones are used in defining conic
programs which generalize linear programs. A linear program is a conic program for the positive
cone. We then prove Farkas' lemma for conic programs following the proof in the reference below.
Farkas' lemma is equivalent to strong duality. So, once we have the definitions of conic and
linear programs, the results from this file can be used to prove duality theorems.

One can turn `C : PointedCone R E` + `hC : IsClosed C` into `C : ProperCone R E` in a tactic block
by doing `lift C to ProperCone R E using hC`.

One can also turn `C : ConvexCone 𝕜 E` + `hC : Set.Nonempty C ∧ IsClosed C` into
`C : ProperCone 𝕜 E` in a tactic block by doing `lift C to ProperCone 𝕜 E using hC`,
assuming `𝕜` is a dense topological field.

## TODO

The next steps are:
- Add `ConvexConeClass` that extends `SetLike` and replace the below instance
- Define primal and dual cone programs and prove weak duality.
- Prove regular and strong duality for cone programs using Farkas' lemma (see reference).
- Define linear programs and prove LP duality as a special case of cone duality.
- Find a better reference (textbook instead of lecture notes).

## References

- [B. Gartner and J. Matousek, Cone Programming][gartnerMatousek]

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open ContinuousLinearMap Filter Function Set

variable {𝕜 R E F G : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [TopologicalSpace E] [Module R E]
variable [AddCommMonoid F] [TopologicalSpace F] [Module R F]
variable [AddCommMonoid G] [TopologicalSpace G] [Module R G]

local notation "R≥0" => {r : R // 0 ≤ r}

variable (R E) in
/-- A proper cone is a pointed cone `C` that is closed. Proper cones have the nice property that
they are equal to their double dual, see `ProperCone.dual_dual`.
This makes them useful for defining cone programs and proving duality theorems. -/
abbrev ProperCone := ClosedSubmodule R≥0 E

namespace ProperCone
section Module
variable {C C₁ C₂ : ProperCone R E} {r : R} {x : E}

/-- Any proper cone can be seen as a pointed cone.

This is an alias of `ClosedSubmodule.toSubmodule` for convenience and discoverability. -/
@[coe] abbrev toPointedCone (C : ProperCone R E) : PointedCone R E := C.toSubmodule

instance : Coe (ProperCone R E) (PointedCone R E) := ⟨toPointedCone⟩

lemma toPointedCone_injective : Injective ((↑) : ProperCone R E → PointedCone R E) :=
  ClosedSubmodule.toSubmodule_injective

-- TODO: add `ConvexConeClass` that extends `SetLike` and replace the below instance
instance : SetLike (ProperCone R E) E where
  coe C := C.carrier
  coe_injective' _ _ h := ProperCone.toPointedCone_injective <| SetLike.coe_injective h

instance : PartialOrder (ProperCone R E) := .ofSetLike (ProperCone R E) E

@[ext] lemma ext (h : ∀ x, x ∈ C₁ ↔ x ∈ C₂) : C₁ = C₂ := SetLike.ext h

lemma mem_toPointedCone : x ∈ C.toPointedCone ↔ x ∈ C := .rfl

lemma pointed_toConvexCone (C : ProperCone R E) : (C : ConvexCone R E).Pointed :=
  C.toPointedCone.pointed_toConvexCone

protected lemma nonempty (C : ProperCone R E) : (C : Set E).Nonempty := C.toSubmodule.nonempty
protected lemma isClosed (C : ProperCone R E) : IsClosed (C : Set E) := C.isClosed'
protected lemma convex (C : ProperCone R E) : Convex R (C : Set E) := C.toPointedCone.convex

protected nonrec lemma smul_mem (C : ProperCone R E) (hx : x ∈ C) (hr : 0 ≤ r) : r • x ∈ C :=
  C.smul_mem ⟨r, hr⟩ hx

section T1Space
variable [T1Space E]

lemma mem_bot : x ∈ (⊥ : ProperCone R E) ↔ x = 0 := .rfl

@[simp, norm_cast] lemma coe_bot : (⊥ : ProperCone R E) = ({0} : Set E) := rfl
@[simp, norm_cast] lemma toPointedCone_bot : (⊥ : ProperCone R E).toPointedCone = ⊥ := rfl

end T1Space

set_option backward.isDefEq.respectTransparency false in
/-- The closure of image of a proper cone under an `R`-linear map is a proper cone. We
use continuous maps here so that the comap of f is also a map between proper cones. -/
abbrev comap (f : E →L[R] F) (C : ProperCone R F) : ProperCone R E :=
  ClosedSubmodule.comap (f.restrictScalars R≥0) C

@[simp] lemma comap_id (C : ProperCone R F) : C.comap (.id _ _) = C := rfl

@[simp] lemma coe_comap (f : E →L[R] F) (C : ProperCone R F) : (C.comap f : Set E) = f ⁻¹' C := rfl

lemma comap_comap (g : F →L[R] G) (f : E →L[R] F) (C : ProperCone R G) :
    (C.comap g).comap f = C.comap (g.comp f) := rfl

lemma mem_comap {C : ProperCone R F} {f : E →L[R] F} : x ∈ C.comap f ↔ f x ∈ C := .rfl

variable [ContinuousAdd F] [ContinuousConstSMul R F]

set_option backward.isDefEq.respectTransparency false in
/-- The closure of image of a proper cone under a linear map is a proper cone.

We use continuous maps here to match `ProperCone.comap`. -/
abbrev map (f : E →L[R] F) (C : ProperCone R E) : ProperCone R F :=
  ClosedSubmodule.map (f.restrictScalars R≥0) C

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma map_id (C : ProperCone R F) : C.map (.id _ _) = C := ClosedSubmodule.map_id _

@[simp, norm_cast]
lemma coe_map (f : E →L[R] F) (C : ProperCone R E) :
    C.map f = (C.toPointedCone.map (f : E →ₗ[R] F)).closure := rfl

@[simp]
lemma mem_map {f : E →L[R] F} {C : ProperCone R E} {y : F} :
    y ∈ C.map f ↔ y ∈ (C.toPointedCone.map (f : E →ₗ[R] F)).closure := .rfl

end Module

section PositiveCone
variable [PartialOrder E] [IsOrderedAddMonoid E] [PosSMulMono R E] [OrderClosedTopology E] {x : E}

variable (R E) in
/-- The positive cone is the proper cone formed by the set of nonnegative elements in an ordered
module. -/
@[simps!]
def positive : ProperCone R E where
  toSubmodule := PointedCone.positive R E
  isClosed' := isClosed_Ici

@[simp] lemma mem_positive : x ∈ positive R E ↔ 0 ≤ x := .rfl
@[simp] lemma toPointedCone_positive : (positive R E).toPointedCone = .positive R E := rfl

end PositiveCone
end ProperCone

/-!
### Topological properties of convex cones

This section proves topological results about convex cones.

#### TODO

This result generalises to G-submodules.
-/

namespace ConvexCone
variable [Semifield 𝕜] [LinearOrder 𝕜] [Module 𝕜 E] {s : Set E}

-- FIXME: This is necessary for the proof below but triggers the `unusedSectionVars` linter.
-- variable [IsStrictOrderedRing 𝕜] [IsTopologicalAddGroup M] in
/-- This is true essentially by `Submodule.span_eq_iUnion_nat`, except that `Submodule` currently
doesn't support that use case. See
https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/G-submodules/with/514426583 -/
proof_wanted isOpen_hull (hs : IsOpen s) : IsOpen (hull 𝕜 s : Set E)

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
  [ContinuousSMul 𝕜 E] {C : ConvexCone 𝕜 E}

lemma Pointed.of_nonempty_of_isClosed (hC : (C : Set E).Nonempty) (hSclos : IsClosed (C : Set E)) :
    C.Pointed := by
  obtain ⟨x, hx⟩ := hC
  let f : 𝕜 → E := (· • x)
  -- The closure of `f (0, ∞)` is a subset of `C`
  have hfS : closure (f '' Set.Ioi 0) ⊆ C :=
    hSclos.closure_subset_iff.2 <| by rintro _ ⟨_, h, rfl⟩; exact C.smul_mem h hx
  -- `f` is continuous at `0` from the right
  have fc : ContinuousWithinAt f (Set.Ioi (0 : 𝕜)) 0 := by fun_prop
  -- `0 ∈ closure f (0, ∞) ⊆ C, 0 ∈ C`
  simpa [f, Pointed, ← SetLike.mem_coe] using hfS <| fc.mem_closure_image <| by simp

variable [IsOrderedRing 𝕜]

instance canLift : CanLift (ConvexCone 𝕜 E) (ProperCone 𝕜 E) (↑)
    fun C ↦ (C : Set E).Nonempty ∧ IsClosed (C : Set E) where
  prf C hC := ⟨⟨C.toPointedCone <| .of_nonempty_of_isClosed hC.1 hC.2, hC.2⟩, rfl⟩

end ConvexCone
