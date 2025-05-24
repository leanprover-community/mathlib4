/-
Copyright (c) 2022 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade, Yaël Dillies
-/
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Order.Module
import Mathlib.Topology.Order.DenselyOrdered

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

open Filter Function Set

/-!
### Topological properties of convex cones

This section proves topological results about convex cones.

#### TODO

Both results generalise to G-submodules.
-/

namespace ConvexCone
variable {𝕜 M : Type*}

section Module
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup M] [Module 𝕜 M]
  [TopologicalSpace M] {C : ConvexCone 𝕜 M} {s : Set M} {x : M}

-- This is necessary for the proof below but triggers the `unusedSectionVars` linter.
-- variable [IsTopologicalAddGroup M]

/-- This is true essentially by `Submodule.span_eq_iUnion_nat`, except that `Submodule` currently
doesn't support that use case. See
https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/G-submodules/with/514426583 -/
proof_wanted isOpen_hull (hs : IsOpen s) : IsOpen (hull 𝕜 s : Set M)

end Module

section ContinuousSMul
variable [TopologicalSpace 𝕜] [Field 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] [OrderTopology 𝕜]
  [DenselyOrdered 𝕜] [AddCommGroup M] [TopologicalSpace M] [Module 𝕜 M] [ContinuousSMul 𝕜 M]
  {S : ConvexCone 𝕜 M}

lemma Pointed.of_nonempty_of_isClosed (hS : (S : Set M).Nonempty) (hSclos : IsClosed (S : Set M)) :
    S.Pointed := by
  obtain ⟨x, hx⟩ := hS
  let f : 𝕜 → M := (· • x)
  -- The closure of `f (0, ∞)` is a subset of `K`
  have hfS : closure (f '' Set.Ioi 0) ⊆ S :=
    hSclos.closure_subset_iff.2 <| by rintro _ ⟨_, h, rfl⟩; exact S.smul_mem h hx
  -- `f` is continuous at `0` from the right
  have fc : ContinuousWithinAt f (Set.Ioi (0 : 𝕜)) 0 :=
    (continuous_id.smul continuous_const).continuousWithinAt
  -- `0 ∈ closure f (0, ∞) ⊆ K, 0 ∈ K`
  simpa [f, Pointed, ← SetLike.mem_coe] using hfS <| fc.mem_closure_image <| by simp

@[deprecated (since := "2025-04-18")]
alias pointed_of_nonempty_of_isClosed := Pointed.of_nonempty_of_isClosed

end ContinuousSMul
end ConvexCone

/-! ### Proper cones -/

variable {R E F : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [TopologicalSpace E] [Module R E]
variable [AddCommMonoid F] [TopologicalSpace F] [Module R F]

variable (R E) in
/-- A proper cone is a pointed cone `C` that is closed. Proper cones have the nice property that
they are equal to their double dual, see `ProperCone.dual_dual`.
This makes them useful for defining cone programs and proving duality theorems. -/
abbrev ProperCone := ClosedSubmodule {r : R // 0 ≤ r} E

namespace ProperCone
section Module
variable {C C₁ C₂ : ProperCone R E} {r : R} {x : E}

/-- Alias of `ClosedSubmodule.toSubmodule` for convenience and discoverability. -/
@[coe] abbrev toPointedCone (C : ProperCone R E) : PointedCone R E := C.toSubmodule

instance : Coe (ProperCone R E) (PointedCone R E) := ⟨toPointedCone⟩

lemma toPointedCone_injective : Injective ((↑) : ProperCone R E → PointedCone R E) :=
  ClosedSubmodule.toSubmodule_injective

-- TODO: add `ConvexConeClass` that extends `SetLike` and replace the below instance
instance : SetLike (ProperCone R E) E where
  coe C := C.carrier
  coe_injective' _ _ h := ProperCone.toPointedCone_injective <| SetLike.coe_injective h

@[ext] lemma ext (h : ∀ x, x ∈ C₁ ↔ x ∈ C₂) : C₁ = C₂ := SetLike.ext h

@[simp] lemma mem_toPointedCone : x ∈ C.toPointedCone ↔ x ∈ C := .rfl

protected lemma pointed_toConvexCone (C : ProperCone R E) : (C : ConvexCone R E).Pointed :=
  C.toPointedCone.pointed_toConvexCone

protected lemma nonempty (C : ProperCone R E) : (C : Set E).Nonempty := C.toSubmodule.nonempty
protected lemma isClosed (C : ProperCone R E) : IsClosed (C : Set E) := C.isClosed'
protected lemma convex (C : ProperCone R E) : Convex R (C : Set E) := C.toPointedCone.convex

protected nonrec lemma smul_mem (C : ProperCone R E) (hx : x ∈ C) (hr : 0 ≤ r) : r • x ∈ C :=
  C.smul_mem ⟨r, hr⟩ hx

/-- The closure of image of a proper cone under a `ℝ`-linear map is a proper cone. We
use continuous maps here so that the comap of f is also a map between proper cones. -/
abbrev comap (f : E →L[R] F) (C : ProperCone R F) : ProperCone R E :=
  ClosedSubmodule.comap (f.restrictScalars {r : R // 0 ≤ r}) C

@[simp] lemma comap_id (C : ProperCone R F) : C.comap (.id _ _) = C := rfl

variable [T1Space E]

lemma mem_bot : x ∈ (⊥ : ProperCone R E) ↔ x = 0 := .rfl

@[simp, norm_cast] lemma toPointedCone_bot : (⊥ : ProperCone R E).toPointedCone = ⊥ := rfl

variable [ContinuousAdd F] [ContinuousConstSMul R F]

/-- The closure of image of a proper cone under a linear map is a proper cone.

We use continuous maps here to match `ProperCone.comap`. -/
abbrev map (f : E →L[R] F) (C : ProperCone R E) : ProperCone R F :=
  ClosedSubmodule.map (f.restrictScalars {r : R // 0 ≤ r}) C

@[simp] lemma map_id (C : ProperCone R F) : C.map (.id _ _) = C := ClosedSubmodule.map_id _

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

end PositiveCone

instance canLift {𝕜 E : Type*} [TopologicalSpace 𝕜] [Field 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜]
    [OrderTopology 𝕜] [DenselyOrdered 𝕜] [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
    [ContinuousSMul 𝕜 E] :
    CanLift (ConvexCone 𝕜 E) (ProperCone 𝕜 E) (↑)
     fun C ↦ (C : Set E).Nonempty ∧ IsClosed (C : Set E) where
  prf C hC := ⟨⟨C.toPointedCone <| .of_nonempty_of_isClosed hC.1 hC.2, hC.2⟩, rfl⟩

end ProperCone
