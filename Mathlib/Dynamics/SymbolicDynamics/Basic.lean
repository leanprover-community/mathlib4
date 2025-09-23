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
Provided a finite set `A`, the ambient space is the space of functions from `G` to `A`,
hence it inherits the product topology from the Π-type. We define the right-translation action,
cylinders, finite patterns, their occurrences, forbidden sets, and subshifts (closed,
shift-invariant subsets). Basic topological statements (e.g. cylinders are clopen,
occurrence sets are clopen, forbidden sets are closed) are proved under discreteness
assumptions on the alphabet.

The file is group-generic. Geometry specific to `ℤ^d` (boxes/cubes and the
box-based entropy) is kept in a separate specialization.

## Main definitions

* `shift g x` — right translation: `(shift g x) h = x (h * g)`.
* `cylinder U x` — configurations agreeing with `x` on a finite set `U ⊆ G`.
* `Pattern A G` — finite support together with values on that support.
* `Pattern.occursIn p x g` — occurrence of `p` in `x` at translate `g`.
* `forbids F` — configurations avoiding every pattern in `F`.
* `Subshift A G` — closed, shift-invariant subsets of the full shift.

## Conventions

We use a **right** action of `G` on configurations:
`(shift g x) h = x (h * g)`. In additive notation (e.g. for `ℤ^d`) this is
`(shift v x) u = x (u + v)`.

## Implementation notes

* Openness/closedness results for cylinders and occurrence sets use
  `[DiscreteTopology A]`. The closedness proofs that enumerate values additionally
  require `[Fintype A]`, `[DecidableEq A]`, and `[DecidableEq G]` (for `Finset` manipulations
  and `Function.update`).
-/

noncomputable section
open Set Topology

namespace SymbolicDynamics

variable {A : Type*} [Fintype A] [Inhabited A]
variable {G : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
variable [Group G] [DecidableEq G]

/-! ## Full shift and shift action -/


/-- Right-translation shift: `(shift g x) (h) = x (h * g)`. -/
def shift (g : G) (x : G → A) : G → A :=
  fun h => x (h * g)

section ShiftAlgebra

variable {A G : Type*} [Group G]

@[simp] lemma shift_apply (g h : G) (x : G → A) :
  shift g x h = x (h * g) := rfl

@[simp] lemma shift_one (x : G → A) : shift (1 : G) x = x := by
  ext h; simp [shift]

lemma shift_mul (g₁ g₂ : G) (x : G → A) :
  shift (g₁ * g₂) x = shift g₁ (shift g₂ x) := by
  ext h; simp [shift, mul_assoc]

end ShiftAlgebra

section ShiftTopology  -- add only topology on A

variable {A G : Type*} [Group G] [TopologicalSpace A]
lemma continuous_shift (g : G) : Continuous (shift (A := A) (G := G) g) := by
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

@[simp] lemma mem_cylinder {U : Finset G} {x y : G → A} :
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

/-- A subshift is a closed, shift-invariant subset. -/
structure Subshift (A : Type*) [TopologicalSpace A] [Inhabited A] (G : Type*) [Group G] where
  /-- The underlying set of configurations. -/
  carrier : Set (G → A)
  /-- Closedness of `carrier`. -/
  isClosed : IsClosed carrier
  /-- Shift invariance of `carrier`. -/
  shiftInvariant : ∀ g : G, ∀ x ∈ carrier, shift (A := A) (G := G) g x ∈ carrier

/-- Example: the full shift on alphabet A. -/
def fullShift (A G) [TopologicalSpace A] [Inhabited A] [Group G] : Subshift A G :=
{ carrier := Set.univ,
  isClosed := isClosed_univ,
  shiftInvariant := by intro _ _ _; simp }


/-- A finite pattern: finite support in `G` and values on it. -/
structure Pattern (A : Type*) (G : Type*) [Group G] where
  /-- Finite support of the pattern. -/
  support : Finset G
  /-- The value (symbol) at each point of the support. -/
  data : support → A

/-- The domino supported on `{i,j}` with values `ai`,`aj`. -/
def domino {A : Type*}
    (i j : G) (ai aj : A) : Pattern A G := by
  refine
  { support := ({i, j} : Finset G)
  , data := fun ⟨z, hz⟩ => if z = i then ai else aj }

/-- Occurrence of a pattern `p` in `x` at position `g`. -/
def Pattern.occursIn (p : Pattern A G) (x : G → A) (g : G) : Prop :=
  ∀ (h) (hh : h ∈ p.support), x (h * g) = p.data ⟨h, hh⟩

/-- Configurations avoiding every pattern in `F`. -/
def forbids (F : Set (Pattern A G)) : Set (G → A) :=
  { x | ∀ p ∈ F, ∀ g : G, ¬ p.occursIn x g }


section ShiftInvariance

variable {A G : Type*} [Group G]

/-- Shifts move occurrences as expected. -/
lemma occurs_shift (p : Pattern A G) (x : G → A) (g h : G) :
    p.occursIn (shift h x) g ↔ p.occursIn x (g * h) := by
  constructor <;> intro H u hu <;> simpa [shift, mul_assoc] using H u hu

lemma forbids_shift_invariant (F : Set (Pattern A G)) :
    ∀ h : G, ∀ x ∈ forbids (A := A) (G := G) F, shift h x ∈ forbids F := by
  intro h x hx p hp g
  specialize hx p hp (g * h)
  -- contraposition
  contrapose! hx
  simpa [occurs_shift] using hx

end ShiftInvariance

/-- Extend a pattern by `default` away from its support (anchored at the origin). -/
def patternToOriginConfig (p : Pattern A G) : G → A :=
  fun i ↦ if h : i ∈ p.support then p.data ⟨i, h⟩ else default

/-- Translate a pattern to occur at `v`. -/
def patternToConfig (p : Pattern A G) (v : G) : G → A :=
  shift (v⁻¹) (patternToOriginConfig p)

/-- Restrict a configuration to a finite support, seen as a pattern. -/
def patternFromConfig (x : G → A) (U : Finset G) : Pattern A G :=
  { support := U,
    data := fun i => x i.1 }

section OccursAtEqCylinder

variable {A G : Type*} [Group G] [Inhabited A] [DecidableEq G]

/-- “Occurrence = cylinder translated by `g`”. -/
lemma occursAt_eq_cylinder (p : Pattern A G) (g : G) :
    { x | p.occursIn x g } = cylinder (p.support.image (· * g)) (patternToConfig p g) := by
  ext x
  constructor
  · intro H u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    dsimp [patternToConfig, patternToOriginConfig, shift]
    simp [dif_pos hw, H w hw]
  · intro H u hu
    have := H (u * g) (Finset.mem_image_of_mem _ hu)
    dsimp [patternToConfig, patternToOriginConfig, shift] at this
    simpa [add_neg_cancel_right, dif_pos hu] using this

end OccursAtEqCylinder

/-! ## Forbidden sets and subshifts -/

section OccSetsOpen

variable {A G : Type*} [Group G] [TopologicalSpace A] [DiscreteTopology A]
           [Inhabited A] [DecidableEq G]

/-- Occurrence sets are open. -/
lemma occursAt_open (p : Pattern A G) (g : G) :
    IsOpen { x | p.occursIn x g } := by
  rw [occursAt_eq_cylinder]; exact cylinder_is_open _ _

/-- Avoiding a fixed set of patterns is a closed condition. -/
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
lemma occursAt_closed (p : Pattern A G) (g : G) :
    IsClosed { x | p.occursIn x g } := by
  rw [occursAt_eq_cylinder]; exact cylinder_is_closed _ _

end OccSetsClosed

/-- Subshift defined by forbidden patterns. -/
def X_F (F : Set (Pattern A G)) : Subshift A G :=
{ carrier := forbids F,
  isClosed := forbids_closed F,
  shiftInvariant := forbids_shift_invariant F }

/-- Subshift of finite type defined by a finite family of forbidden patterns. -/
def SFT (F : Finset (Pattern A G)) : Subshift A G :=
  X_F (F : Set (Pattern A G))

/-- Patterns with fixed support `U`. -/
def FixedSupport (A : Type*) (G : Type*) [Group G] (U : Finset G) :=
  { p : Pattern A G // p.support = U }

/-- `FixedSupport A G U ≃ (U → A)`; gives finiteness immediately. -/
def equivFun {U : Finset G} :
  FixedSupport A G U ≃ (U → A) where
  toFun   := fun p i => p.1.data ⟨i.1, by simp [p.2]⟩
  invFun  := fun f => ⟨{ support := U, data := f }, rfl⟩
  left_inv := by rintro ⟨p,hU⟩; apply Subtype.ext; cases hU; rfl
  right_inv := by intro f; rfl

instance fintypeFixedSupport {U : Finset G} :
    Fintype (FixedSupport A G U) := by
  classical exact Fintype.ofEquiv (U → A) (equivFun (A := A) (G := G) (U := U)).symm

/-- Language on a finite set `U ⊆ G`: patterns obtained by restricting some `x ∈ X`. -/
def languageOn (X : Set (G → A)) (U : Finset G) : Set (Pattern A G) :=
  { p | ∃ x ∈ X, patternFromConfig x U = p }

/-- Cardinality of the finite-support language. -/
noncomputable def languageCardOn (X : Set (G → A)) (U : Finset G) : ℕ := by
  classical
  -- Image of a map into the finite type `FixedSupport A G U`
  let f : {x : G → A // x ∈ X} → FixedSupport A G U :=
    fun x => ⟨patternFromConfig x.1 U, rfl⟩
  have hfin : (Set.range f).Finite := (Set.finite_univ :
    (Set.univ : Set (FixedSupport A G U)).Finite)
    |>.subset (by intro y hy; simp)
  exact hfin.toFinset.card

/-- Number of patterns of a subshift on a finite shape `U`. -/
noncomputable def patternCountOn (Y : Subshift A G) (U : Finset G) : ℕ :=
  languageCardOn (A := A) (G := G) Y.carrier U

end SymbolicDynamics
