/-
Copyright (c) 2025 S. Gangloff. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: S. Gangloff
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.Defs
/-!
# Symbolic dynamics on groups

This file develops a minimal API for symbolic dynamics over an arbitrary group `G`.
Given a finite alphabet `A`, the ambient configuration space is the set of functions
`G → A`, endowed with the product topology. We define the right-translation action,
cylinders, finite patterns, their occurrences, forbidden sets, and subshifts
(closed, shift-invariant subsets). Basic topological facts (e.g. cylinders are clopen,
occurrence sets are clopen, forbidden sets are closed) are proved under discreteness
assumptions on the alphabet.

The development is group-generic. Geometry specific to `ℤ^d` (boxes/cubes and the
box-based entropy) is deferred to a separate specialization.

## Main definitions

* `mulShift g x` — right translation: in multiplicative notation `(mulShift g x) h = x (h * g)`;
  additive notation `(addShift v x) u = x (u + v)`.
* `cylinder U x` — configurations agreeing with `x` on a finite set `U ⊆ G`.
* `Pattern A G` — finite support together with values on that support.
* `Pattern.occursIn p x g` — occurrence of `p` in `x` at translate `g`.
* `forbids F` — configurations avoiding every pattern in `F`.
* `Subshift A G` — closed, shift-invariant subsets of the full shift.
* `X_F F` — the subshift defined by forbidding a family of patterns.
* `SFT F` — a subshift of finite type defined by a finite set of forbidden patterns.
* `languageOn X U` — the set of patterns of shape `U` obtained by restricting some `x ∈ X`.

## Conventions

We use a **right** action of `G` on configurations:
`(mulShift g x) h = x (h * g)`.
In additive notation (e.g. for `ℤ^d`):
`(addShift v x) u = x (u + v)`.

## Design choice: ambient vs. inner (subshift-relative) viewpoint

All core notions (shift, cylinder, occurrence, language, …) are defined **in the
ambient full shift** `(G → A)`. A subshift is then a closed, invariant subset,
bundled as `Subshift A G`. Working inside a subshift is done by restriction.

**Motivation.**
If cylinders and shifts were defined only *inside* a subshift, local ergonomics
would improve but global operations would become awkward. For instance, to prove
that for finite shape `U`:

`languageOn (X ∪ Y) U = languageOn X U ∪ languageOn Y U,`

one must eventually move both sides to the ambient pattern type. Similar issues
arise for intersections, factors, and products. By contrast, with ambient
definitions these set-theoretic identities are tautological.
Thus the file develops the theory ambiently, and subshifts reuse it by restriction.

**Working inside a subshift.**
For `Y : Subshift A G`, cylinders and occurrence sets *inside `Y`* are simply
preimages of the ambient ones under the inclusion `Y → (G → A)`. For example:

`{ y : Y | ∀ i ∈ U, (y : G → A) i = (x : G → A) i } = (Subtype.val) ⁻¹’ (cylinder U (x : G → A)).`

Shift invariance guarantees that the ambient shift restricts to `Y`.

**Ergonomics.**
Thin wrappers (e.g. `Subshift.shift`, `Subshift.cylinder`, `Subshift.languageOn`)
may be added for convenience. They introduce no new theory and unfold to the
ambient definitions.

## Namespacing policy

All ambient definitions live under the namespace `SymbolicDynamics.Ambiant`.
If inner, subshift-relative wrappers are provided, they will be placed in the
subnamespace `SymbolicDynamics.Inner`. This separation avoids name clashes
between the two viewpoints, since both may naturally want to reuse names like
`cylinder`, `shift`, `occursAt`, or `languageOn`.

## Implementation notes

* Openness/closedness results for cylinders and occurrence sets use
  `[DiscreteTopology A]`. Closedness proofs that enumerate values additionally
  require `[Fintype A]`, `[DecidableEq A]`, and `[DecidableEq G]` (for `Finset`
  manipulations and `Function.update`).
-/


noncomputable section
open Set Topology

namespace SymbolicDynamics

namespace Ambiant

/-! ## Full shift and shift action -/

section ShiftDefinition

variable {A : Type*}
variable {G : Type*}
variable [Group G]

/-- Right-translation shift:
* In multiplicative notation: `(mulShift g x) h = x (h * g)`.
* In additive notation (e.g. for `ℤ^d`): `(addShift v x) u = x (u + v)` -/
@[to_additive]
def mulShift (g : G) (x : G → A) : G → A :=
  fun h => x (h * g)

attribute [inherit_doc SymbolicDynamics.Ambiant.mulShift] SymbolicDynamics.Ambiant.addShift

end ShiftDefinition

section ShiftAlgebra

variable {A G : Type*} [Group G]

@[to_additive] lemma mulShift_apply (g h : G) (x : G → A) :
  mulShift g x h = x (h * g) := rfl

@[to_additive] lemma mulShift_one (x : G → A) : mulShift (1 : G) x = x := by
  ext h; simp [mulShift]

@[to_additive] lemma mulShift_mul (g₁ g₂ : G) (x : G → A) :
  mulShift (g₁ * g₂) x = mulShift g₁ (mulShift g₂ x) := by
  ext h; simp [mulShift, mul_assoc]

end ShiftAlgebra

section ShiftTopology  -- add only topology on A

variable {A G : Type*} [Group G] [TopologicalSpace A]

@[to_additive] lemma continuous_mulShift (g : G) : Continuous (mulShift (A := A) (G := G) g) := by
  -- coordinate projections are continuous; composition preserves continuity
  continuity

end ShiftTopology



/-! ## Cylinders -/

section CylindersDefs

variable {A G : Type*}

/-- Cylinder fixing `x` on the finite set `U`. -/
def cylinder (U : Finset G) (x : G → A) : Set (G → A) :=
  { y | ∀ i ∈ U, y i = x i }

lemma cylinder_eq_set_pi (U : Finset G) (x : G → A) :
    cylinder U x = Set.pi (↑U : Set G) (fun i => ({x i} : Set A)) := by
  ext y; simp [cylinder, Set.pi, Finset.mem_coe]

lemma mem_cylinder {U : Finset G} {x y : G → A} :
    y ∈ cylinder U x ↔ ∀ i ∈ U, y i = x i := Iff.rfl

end CylindersDefs

section CylindersOpen

variable {A G : Type*} [TopologicalSpace A] [DiscreteTopology A]

/-- Cylinders are open (and, dually, closed) when `A` is discrete. -/
lemma cylinder_is_open (U : Finset G) (x : G → A) :
    IsOpen (cylinder (A := A) (G := G) U x) := by
  classical
  have hopen : ∀ i ∈ (↑U : Set G), IsOpen ({x i} : Set A) := by
    intro i _; simp
  have hpi :
      IsOpen (Set.pi (s := (↑U : Set G))
                     (t := fun i => ({x i} : Set A))) :=
    isOpen_set_pi (U.finite_toSet) hopen
  simpa [cylinder_eq_set_pi (A := A) (G := G) U x] using hpi

end CylindersOpen

section CylindersClosed

variable {A G : Type*} [TopologicalSpace A] [DiscreteTopology A]

lemma cylinder_is_closed (U : Finset G) (x : G → A) :
    IsClosed (cylinder (A := A) (G := G) U x) := by
  classical
  have hclosed : ∀ i ∈ (↑U : Set G), IsClosed ({x i} : Set A) := by
    intro i _; simp
  have hpi :
      IsClosed (Set.pi (s := (↑U : Set G))
                       (t := fun i => ({x i} : Set A))) :=
    isClosed_set_pi hclosed
  simpa [cylinder_eq_set_pi (A := A) (G := G) U x] using hpi

end CylindersClosed

/-! ## Patterns and occurrences -/

section SubshiftDef
variable (A : Type*) [TopologicalSpace A]
variable (G : Type*) [Group G]

/-- A subshift is a closed, shift-invariant subset. -/
structure Subshift : Type _ where
  /-- The underlying set of configurations. -/
  carrier : Set (G → A)
  /-- Closedness of `carrier`. -/
  isClosed : IsClosed carrier
  /-- Shift invariance of `carrier`. -/
  shiftInvariant : ∀ g : G, ∀ x ∈ carrier, mulShift g x ∈ carrier

end SubshiftDef


section AddSubshiftDef
variable (A : Type*) [TopologicalSpace A]
variable (G : Type*) [AddGroup G]

/-- Additive version of the definition of subshift. -/
structure AddSubshift : Type _ where
  /-- The underlying set of configurations (additive group version). -/
  carrier : Set (G → A)
  /-- Closedness of `carrier`. -/
  isClosed : IsClosed carrier
  /-- Shift invariance of `carrier` for the additive shift `addShift`. -/
  shiftInvariant : ∀ g : G, ∀ x ∈ carrier, addShift g x ∈ carrier

end AddSubshiftDef

attribute [to_additive existing SymbolicDynamics.Ambiant.AddSubshift]
  SymbolicDynamics.Ambiant.Subshift

/-- Example: the full shift on alphabet A. -/
@[to_additive SymbolicDynamics.Ambiant.addFullShift]
def fullShift (A G) [TopologicalSpace A] [Group G] : Subshift A G :=
{ carrier := Set.univ,
  isClosed := isClosed_univ,
  shiftInvariant := by intro _ _ _; simp }

attribute [inherit_doc SymbolicDynamics.Ambiant.fullShift] SymbolicDynamics.Ambiant.addFullShift

/-- A finite pattern: finite support in `G` and values on it. -/
structure Pattern (A : Type*) (G : Type*) [Group G] where
  /-- Finite support of the pattern. -/
  support : Finset G
  /-- The value (symbol) at each point of the support. -/
  data : support → A

/-- Additive version of `Pattern`. -/
structure AddPattern (A : Type*) (G : Type*) [AddGroup G] : Type _ where
  /-- Finite support of the pattern (subset of `G`). -/
  support : Finset G
  /-- The symbol at each point of the support. -/
  data    : support → A

attribute [to_additive existing SymbolicDynamics.Ambiant.AddPattern]
  SymbolicDynamics.Ambiant.Pattern

section Dominos

variable (G : Type*) [Group G] [DecidableEq G]

/-- The domino supported on `{i,j}` with values `ai`,`aj`. -/
@[to_additive addDomino]
def domino {A : Type*}
    (i j : G) (ai aj : A) : Pattern A G := by
  refine
  { support := ({i, j} : Finset G)
  , data := fun ⟨z, hz⟩ => if z = i then ai else aj }

attribute [inherit_doc SymbolicDynamics.Ambiant.domino] SymbolicDynamics.Ambiant.addDomino

end Dominos

section Forbids

variable {A : Type*}
variable {G : Type*}
variable [Group G]

/-- Occurrence of a pattern `p` in `x` at position `g`. -/
@[to_additive Pattern.addOccursIn]
def Pattern.occursIn (p : Pattern A G) (x : G → A) (g : G) : Prop :=
  ∀ (h) (hh : h ∈ p.support), x (h * g) = p.data ⟨h, hh⟩

attribute [inherit_doc SymbolicDynamics.Ambiant.Pattern.occursIn]
  SymbolicDynamics.Ambiant.Pattern.addOccursIn

/-- Configurations avoiding every pattern in `F`. -/
@[to_additive addForbids]
def forbids (F : Set (Pattern A G)) : Set (G → A) :=
  { x | ∀ p ∈ F, ∀ g : G, ¬ p.occursIn x g }

attribute [inherit_doc SymbolicDynamics.Ambiant.forbids] SymbolicDynamics.Ambiant.addForbids

end Forbids

section ShiftInvariance

variable {A G : Type*} [Group G]

/-- Shifts move occurrences as expected. -/
@[to_additive addOccurs_addShift]
lemma occurs_shift (p : Pattern A G) (x : G → A) (g h : G) :
    p.occursIn (mulShift h x) g ↔ p.occursIn x (g * h) := by
  constructor <;> intro H u hu <;> simpa [mulShift, mul_assoc] using H u hu

@[to_additive addForbids_addShift_invariant]
lemma forbids_shift_invariant (F : Set (Pattern A G)) :
    ∀ h : G, ∀ x ∈ forbids (A := A) (G := G) F, mulShift h x ∈ forbids F := by
  intro h x hx p hp g
  specialize hx p hp (g * h)
  -- contraposition
  contrapose! hx
  simpa [occurs_shift] using hx

end ShiftInvariance

section PatternFromToConfig

variable {A : Type*} [Inhabited A]
variable {G : Type*}
variable [Group G] [DecidableEq G]

/-- Extend a pattern by `default` away from its support (anchored at the origin). -/
@[to_additive addPatternToOriginConfig]
def patternToOriginConfig (p : Pattern A G) : G → A :=
  fun i ↦ if h : i ∈ p.support then p.data ⟨i, h⟩ else default

attribute [inherit_doc SymbolicDynamics.Ambiant.patternToOriginConfig]
  SymbolicDynamics.Ambiant.addPatternToOriginConfig

/-- Translate a pattern to occur at `v`. -/
@[to_additive addPatternToConfig]
def patternToConfig (p : Pattern A G) (v : G) : G → A :=
  mulShift (v⁻¹) (patternToOriginConfig p)

attribute [inherit_doc SymbolicDynamics.Ambiant.patternToConfig]
  SymbolicDynamics.Ambiant.addPatternToConfig

/-- Restrict a configuration to a finite support, seen as a pattern. -/
@[to_additive addPatternFromConfig]
def patternFromConfig (x : G → A) (U : Finset G) : Pattern A G :=
  { support := U,
    data := fun i => x i.1 }

attribute [inherit_doc SymbolicDynamics.Ambiant.patternFromConfig]
  SymbolicDynamics.Ambiant.addPatternFromConfig

end PatternFromToConfig

section OccursAtEqCylinder

variable {A G : Type*} [Group G] [Inhabited A] [DecidableEq G]

/-- “Occurrence = cylinder translated by `g`”. -/
@[to_additive addOccursAt_eq_cylinder]
lemma occursAt_eq_cylinder (p : Pattern A G) (g : G) :
    { x | p.occursIn x g } = cylinder (p.support.image (· * g)) (patternToConfig p g) := by
  ext x
  constructor
  · intro H u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    dsimp [patternToConfig, patternToOriginConfig, mulShift]
    simp [dif_pos hw, H w hw]
  · intro H u hu
    have := H (u * g) (Finset.mem_image_of_mem _ hu)
    dsimp [patternToConfig, patternToOriginConfig, mulShift] at this
    simpa [mul_inv_cancel_right, mul_assoc, dif_pos hu] using this

end OccursAtEqCylinder

/-! ## Forbidden sets and subshifts -/

section OccSetsOpen

variable {A G : Type*} [Group G] [TopologicalSpace A] [DiscreteTopology A]
           [Inhabited A] [DecidableEq G]

/-- Occurrence sets are open. -/
@[to_additive addOccursAt_open]
lemma occursAt_open (p : Pattern A G) (g : G) :
    IsOpen { x | p.occursIn x g } := by
  rw [occursAt_eq_cylinder]; exact cylinder_is_open _ _

/-- Avoiding a fixed set of patterns is a closed condition. -/
@[to_additive addForbids_closed]
lemma forbids_closed (F : Set (Pattern A G)) :
    IsClosed (forbids F) := by
  rw [forbids]
  have : {x | ∀ p ∈ F, ∀ v : G, ¬ p.occursIn x v}
       = ⋂ (p : Pattern A G) (h : p ∈ F), ⋂ (v : G), {x | ¬ p.occursIn x v} := by
    ext x; simp
  rw [this]
  refine isClosed_iInter ?_;
  intro p; refine isClosed_iInter ?_;
  intro _; refine isClosed_iInter ?_;
  intro v; have : {x | ¬p.occursIn x v} = {x | p.occursIn x v}ᶜ := by ext x; simp
  simpa [this, isClosed_compl_iff] using occursAt_open p v

end OccSetsOpen

section OccSetsClosed

variable {A G : Type*} [Group G] [TopologicalSpace A] [DiscreteTopology A]
           [Inhabited A] [DecidableEq G]

/-- Occurrence sets are closed. -/
@[to_additive addOccursAt_closed]
lemma occursAt_closed (p : Pattern A G) (g : G) :
    IsClosed { x | p.occursIn x g } := by
  rw [occursAt_eq_cylinder]; exact cylinder_is_closed _ _

end OccSetsClosed

section DefSubshiftByForbidden

variable {A : Type*} [Inhabited A]
variable {G : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
variable [Group G] [DecidableEq G]

/-- Subshift defined by forbidden patterns. -/
@[to_additive addX_F]
def X_F (F : Set (Pattern A G)) : Subshift A G :=
{ carrier := forbids F,
  isClosed := forbids_closed F,
  shiftInvariant := forbids_shift_invariant F }

attribute [inherit_doc SymbolicDynamics.Ambiant.X_F] SymbolicDynamics.Ambiant.addX_F

/-- Subshift of finite type defined by a finite family of forbidden patterns. -/
@[to_additive addSFT]
def SFT (F : Finset (Pattern A G)) : Subshift A G :=
  X_F (F : Set (Pattern A G))

attribute [inherit_doc SymbolicDynamics.Ambiant.SFT] SymbolicDynamics.Ambiant.addSFT

end DefSubshiftByForbidden

section Language

variable {A : Type*} [Fintype A]
variable {G : Type*}
variable [TopologicalSpace A]
variable [Group G]

/-- Patterns with fixed support `U`. -/
@[to_additive AddFixedSupport]
def FixedSupport (A : Type*) (G : Type*) [Group G] (U : Finset G) :=
  { p : Pattern A G // p.support = U }

attribute [inherit_doc SymbolicDynamics.Ambiant.FixedSupport]
  SymbolicDynamics.Ambiant.AddFixedSupport

/-- `FixedSupport A G U ≃ (U → A)`; gives finiteness immediately. -/
@[to_additive addEquivFun]
def equivFun {U : Finset G} :
  FixedSupport A G U ≃ (U → A) where
  toFun   := fun p i => p.1.data ⟨i.1, by simp [p.2]⟩
  invFun  := fun f => ⟨{ support := U, data := f }, rfl⟩
  left_inv := by rintro ⟨p,hU⟩; apply Subtype.ext; cases hU; rfl
  right_inv := by intro f; rfl

attribute [inherit_doc SymbolicDynamics.Ambiant.equivFun] SymbolicDynamics.Ambiant.addEquivFun

@[to_additive SymbolicDynamics.Ambiant.addFintypeFixedSupport] noncomputable
instance fintypeFixedSupport {U : Finset G} :
    Fintype (FixedSupport A G U) := by
  classical exact Fintype.ofEquiv (U → A) (equivFun (A := A) (G := G) (U := U)).symm

/-- Language on a finite set `U ⊆ G`: patterns obtained by restricting some `x ∈ X`. -/
@[to_additive addLanguageOn]
def languageOn (X : Set (G → A)) (U : Finset G) : Set (Pattern A G) :=
  { p | ∃ x ∈ X, patternFromConfig x U = p }

attribute [inherit_doc SymbolicDynamics.Ambiant.languageOn] SymbolicDynamics.Ambiant.addLanguageOn


/-- Cardinality of the finite-support language. -/
@[to_additive addLanguageCardOn]
noncomputable def languageCardOn (X : Set (G → A)) (U : Finset G) : ℕ := by
  classical
  -- Image of a map into the finite type `FixedSupport A G U`
  let f : {x : G → A // x ∈ X} → FixedSupport A G U :=
    fun x => ⟨patternFromConfig x.1 U, rfl⟩
  have hfin : (Set.range f).Finite := (Set.finite_univ :
    (Set.univ : Set (FixedSupport A G U)).Finite)
    |>.subset (by intro y hy; simp)
  exact hfin.toFinset.card

attribute [inherit_doc SymbolicDynamics.Ambiant.languageCardOn]
  SymbolicDynamics.Ambiant.addLanguageCardOn

/-- Number of patterns of a subshift on a finite shape `U`. -/
@[to_additive addPatternCountOn]
noncomputable def patternCountOn (Y : Subshift A G) (U : Finset G) : ℕ :=
  languageCardOn (A := A) (G := G) Y.carrier U

attribute [inherit_doc SymbolicDynamics.Ambiant.patternCountOn]
  SymbolicDynamics.Ambiant.addPatternCountOn

end Language

end Ambiant

end SymbolicDynamics
