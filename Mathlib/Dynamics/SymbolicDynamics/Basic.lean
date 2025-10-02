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
# Symbolic dynamics on cancellative monoids

This file develops a minimal API for symbolic dynamics over an arbitrary
**right-cancellative monoid** `G` (`[Monoid G] [IsRightCancelMul G]`).

Given a finite alphabet `A`, the ambient configuration space is the set of
functions `G → A`, endowed with the product topology. We define the
right-translation action, cylinders, finite patterns, their occurrences,
forbidden sets, and subshifts (closed, shift-invariant subsets). Basic
topological facts (e.g. cylinders are clopen, occurrence sets are clopen,
forbidden sets are closed) are proved under discreteness assumptions on
the alphabet.

The development is generic for right-cancellative monoids. This covers both
groups (the standard setting of symbolic dynamics) and more general monoids
where cancellation holds but inverses may not exist. Geometry specific to
`ℤ^d` (boxes/cubes and the box-based entropy) is deferred to a separate
specialization.

## Why cancellativity?

Some constructions, such as translating a finite pattern to occur at a point `v`,
require solving equations of the form `w * v = h`. For this to have a unique
solution `w` given `h` and `v`, we assume **right-cancellation**:
if `a * v = b * v` then `a = b`. This allows us to define
`patternToConfig` without using inverses, so that the theory works not only
for groups but also for cancellative monoids.

## Main definitions

* `mulShift g x` — right translation: in multiplicative notation
  `(mulShift g x) h = x (h * g)`; additive notation `(addShift v x) u = x (u + v)`.
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

`{ y : Y | ∀ i ∈ U, (y : G → A) i = (x : G → A) i } = (Subtype.val) ⁻¹' (cylinder U (x : G → A)).`

Shift invariance guarantees that the ambient shift restricts to `Y`.

**Ergonomics.**
Thin wrappers (e.g. `Subshift.shift`, `Subshift.cylinder`, `Subshift.languageOn`)
may be added for convenience. They introduce no new theory and unfold to the
ambient definitions.

## Namespacing policy

All ambient definitions live under the namespace `SymbolicDynamics.FullShift`.
If inner, subshift-relative wrappers are provided, they will be placed in the
subnamespace `SymbolicDynamics.Subshift`. This separation avoids name clashes
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

namespace FullShift

/-! ## Full shift and shift action -/

section ShiftDefinition

variable {A G : Type*} [Monoid G]

/-- Right-translation shift:
* In multiplicative notation: `(mulShift g x) h = x (h * g)`.
* In additive notation (e.g. for `ℤ^d`): `(addShift v x) u = x (u + v)` -/
@[to_additive]
def mulShift (g : G) (x : G → A) : G → A :=
  fun h => x (h * g)

attribute [inherit_doc SymbolicDynamics.FullShift.mulShift] SymbolicDynamics.FullShift.addShift


@[to_additive] lemma mulShift_apply (g h : G) (x : G → A) :
  mulShift g x h = x (h * g) := rfl

@[to_additive] lemma mulShift_one (x : G → A) : mulShift (1 : G) x = x := by
  ext h; simp [mulShift]

@[to_additive addShift_mul] lemma mulShift_mul (g₁ g₂ : G) (x : G → A) :
  mulShift (g₁ * g₂) x = mulShift g₁ (mulShift g₂ x) := by
  ext h; simp [mulShift, mul_assoc]


variable [TopologicalSpace A]

@[to_additive] lemma continuous_mulShift (g : G) :
    Continuous (mulShift (A := A) (G := G) g) := by
  -- coordinate projections are continuous; composition preserves continuity
  continuity

end ShiftDefinition

/-! ## Cylinders -/

section Cylinders

variable {A G : Type*}

/-- Cylinder fixing `x` on the finite set `U`. -/
def cylinder (U : Finset G) (x : G → A) : Set (G → A) :=
  { y | ∀ i ∈ U, y i = x i }

lemma cylinder_eq_set_pi (U : Finset G) (x : G → A) :
    cylinder U x = Set.pi (↑U : Set G) (fun i => ({x i} : Set A)) := by
  ext y; simp [cylinder, Set.pi, Finset.mem_coe]

lemma mem_cylinder {U : Finset G} {x y : G → A} :
    y ∈ cylinder U x ↔ ∀ i ∈ U, y i = x i := Iff.rfl

variable [TopologicalSpace A] [DiscreteTopology A]

/-- Cylinders are open (and, dually, closed) when `A` is discrete. -/
lemma isOpen_cylinder (U : Finset G) (x : G → A) :
    IsOpen (cylinder (A := A) (G := G) U x) := by
  classical
  have hopen : ∀ i ∈ (↑U : Set G), IsOpen ({x i} : Set A) := by
    intro i _; simp
  have hpi :
      IsOpen (Set.pi (s := (↑U : Set G))
                     (t := fun i => ({x i} : Set A))) :=
    isOpen_set_pi (U.finite_toSet) hopen
  simpa [cylinder_eq_set_pi (A := A) (G := G) U x] using hpi

lemma isClosed_cylinder (U : Finset G) (x : G → A) :
    IsClosed (cylinder (A := A) (G := G) U x) := by
  classical
  have hclosed : ∀ i ∈ (↑U : Set G), IsClosed ({x i} : Set A) := by
    intro i _; simp
  have hpi :
      IsClosed (Set.pi (s := (↑U : Set G))
                       (t := fun i => ({x i} : Set A))) :=
    isClosed_set_pi hclosed
  simpa [cylinder_eq_set_pi (A := A) (G := G) U x] using hpi

end Cylinders

/-! ## Patterns and occurrences -/

section SubshiftDef
variable (A : Type*) [TopologicalSpace A]
variable (G : Type*) [Monoid G]

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
variable (G : Type*) [AddMonoid G]

/-- Additive version of the definition of subshift. -/
structure AddSubshift : Type _ where
  /-- The underlying set of configurations (additive group version). -/
  carrier : Set (G → A)
  /-- Closedness of `carrier`. -/
  isClosed : IsClosed carrier
  /-- Shift invariance of `carrier` for the additive shift `addShift`. -/
  shiftInvariant : ∀ g : G, ∀ x ∈ carrier, addShift g x ∈ carrier


attribute [to_additive existing SymbolicDynamics.FullShift.AddSubshift]
  SymbolicDynamics.FullShift.Subshift

end AddSubshiftDef


/-- Example: the full shift on alphabet A. -/
@[to_additive SymbolicDynamics.FullShift.addFullShift]
def fullShift (A G) [TopologicalSpace A] [Monoid G] : Subshift A G :=
  { carrier := Set.univ,
    isClosed := isClosed_univ,
    shiftInvariant := by intro _ _ _; simp }

attribute [inherit_doc SymbolicDynamics.FullShift.fullShift] SymbolicDynamics.FullShift.addFullShift

/-- A finite pattern: finite support in `G` and values on it. -/
structure Pattern (A : Type*) (G : Type*) [Monoid G] where
  /-- Finite support of the pattern. -/
  support : Finset G
  /-- The value (symbol) at each point of the support. -/
  data : support → A

/-- Additive version of `Pattern`. -/
structure AddPattern (A : Type*) (G : Type*) [AddMonoid G] : Type _ where
  /-- Finite support of the pattern (subset of `G`). -/
  support : Finset G
  /-- The symbol at each point of the support. -/
  data : support → A

attribute [to_additive existing SymbolicDynamics.FullShift.AddPattern]
  SymbolicDynamics.FullShift.Pattern

section Dominos

variable (G : Type*) [Monoid G] [DecidableEq G]

/-- The domino supported on `{i,j}` with values `ai`,`aj`. -/
@[to_additive addDomino]
def domino {A : Type*}
    (i j : G) (ai aj : A) : Pattern A G := by
  refine
  { support := ({i, j} : Finset G)
  , data := fun ⟨z, hz⟩ => if z = i then ai else aj }

attribute [inherit_doc SymbolicDynamics.FullShift.domino] SymbolicDynamics.FullShift.addDomino

end Dominos

section Forbids

variable {A : Type*}
variable {G : Type*}
variable [Monoid G]

/-- Occurrence of a pattern `p` in `x` at position `g`. -/
@[to_additive Pattern.addOccursIn]
def Pattern.occursIn (p : Pattern A G) (x : G → A) (g : G) : Prop :=
  ∀ (h) (hh : h ∈ p.support), x (h * g) = p.data ⟨h, hh⟩

attribute [inherit_doc SymbolicDynamics.FullShift.Pattern.occursIn]
  SymbolicDynamics.FullShift.Pattern.addOccursIn

/-- Configurations avoiding every pattern in `F`. -/
@[to_additive addForbids]
def forbids (F : Set (Pattern A G)) : Set (G → A) :=
  { x | ∀ p ∈ F, ∀ g : G, ¬ p.occursIn x g }

attribute [inherit_doc SymbolicDynamics.FullShift.forbids] SymbolicDynamics.FullShift.addForbids

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

end Forbids

section OccursAt

variable {A : Type*} [Inhabited A]
variable {G : Type*}
variable [Monoid G] [IsRightCancelMul G] [DecidableEq G]

/-- Extend a pattern by `default` away from its support (anchored at the origin). -/
@[to_additive addPatternToOriginConfig]
def patternToOriginConfig (p : Pattern A G) : G → A :=
  fun i ↦ if h : i ∈ p.support then p.data ⟨i, h⟩ else default

attribute [inherit_doc SymbolicDynamics.FullShift.patternToOriginConfig]
  SymbolicDynamics.FullShift.addPatternToOriginConfig

/-- Translate a finite pattern `p` so that it occurs at the translate `v`.

On input `h : G`, we proceed as follows:
* if `h` lies in the right-translate of the support, i.e. `h ∈ p.support.image (· * v)`,
  choose (noncomputably) `w ∈ p.support` with `w * v = h` and return `p.data ⟨w, _⟩`;
* otherwise return `default`.

This definition does **not** assume cancellation; it only *chooses* a preimage.
Uniqueness (and the usual equations such as `patternToConfig p v (w * v) = p.data ⟨w, _⟩`)
require a right-cancellation hypothesis and are proved in separate lemmas.
-/
@[to_additive addPatternToConfig]
noncomputable def patternToConfig (p : Pattern A G) (v : G) : G → A :=
  fun h =>
    if hmem : h ∈ p.support.image (· * v) then
      -- package existence of a preimage under (_ * v)
      let ex : ∃ w, w ∈ p.support ∧ w * v = h := by
        simpa [Finset.mem_image] using hmem
      let w := Classical.choose ex
      have hw  : w ∈ p.support := (Classical.choose_spec ex).1
      have hwv : w * v = h     := (Classical.choose_spec ex).2
      p.data ⟨w, hw⟩
    else
      default

attribute [inherit_doc SymbolicDynamics.FullShift.patternToConfig]
  SymbolicDynamics.FullShift.addPatternToConfig

/-- Restrict a configuration to a finite support, seen as a pattern. -/
@[to_additive addPatternFromConfig]
def patternFromConfig (x : G → A) (U : Finset G) : Pattern A G :=
  { support := U,
    data := fun i => x i.1 }

attribute [inherit_doc SymbolicDynamics.FullShift.patternFromConfig]
  SymbolicDynamics.FullShift.addPatternFromConfig


/-- On the translated support, `patternToConfig` agrees with `p` at the preimage. -/
@[to_additive addPatternToConfig_apply_of_mem]
lemma patternToConfig_apply_of_mem
    (p : Pattern A G) (v w : G) (hw : w ∈ p.support) :
    patternToConfig (A := A) (G := G) p v (w * v) = p.data ⟨w, hw⟩ := by
  classical
  -- (w*v) is in the translated support
  have hmem : (w * v) ∈ p.support.image (· * v) :=
    Finset.mem_image.mpr ⟨w, hw, rfl⟩
  -- existential used in the branch
  have ex : ∃ w', w' ∈ p.support ∧ w' * v = w * v := by
    simpa [Finset.mem_image] using hmem
  -- open the `if` branch as returned by the definition
  have h1 :
      patternToConfig (A := A) (G := G) p v (w * v)
        = p.data ⟨Classical.choose ex, (Classical.choose_spec ex).1⟩ := by
    simp [patternToConfig, hmem]
  -- name the chosen witness and relate it to `w` by right-cancellation
  let w' := Classical.choose ex
  have hw'  : w' ∈ p.support := (Classical.choose_spec ex).1
  have hwv' : w' * v = w * v := (Classical.choose_spec ex).2
  have h_eq : w' = w := by simpa using (mul_right_cancel hwv')
  -- transport membership along h_eq
  have hw_w : w ∈ p.support := by simpa [h_eq] using hw'
  -- identify the subtype inside `p.data` (first replace the value w' by w)
  have h2 :
      (⟨Classical.choose ex, (Classical.choose_spec ex).1⟩ : p.support)
        = (⟨w, hw_w⟩ : p.support) := by
    apply Subtype.ext
    -- goal: Classical.choose ex = w
    -- we have h_eq : w' = w and w' := Classical.choose ex
    simpa [w'] using h_eq     -- <-- use `using h_eq`, only unfold `[w']`

  -- then replace the proof component (same carrier w)
  have h3 :
      (⟨w, hw_w⟩ : p.support) = (⟨w, hw⟩ : p.support) := by
    apply Subtype.ext
    rfl

  -- put the rewrites together
  calc
    patternToConfig (A := A) (G := G) p v (w * v)
        = p.data ⟨Classical.choose ex, (Classical.choose_spec ex).1⟩ := h1
    _   = p.data ⟨w, hw_w⟩ := by
            -- push h2 through `p.data`
            simpa using
              (congrArg (fun z : {x // x ∈ p.support} => p.data z) h2)
    _   = p.data ⟨w, hw⟩ := by
            -- push h3 through `p.data`
            simp [h3]

/-- “Occurrence = cylinder translated by `g`”. -/
@[to_additive addOccursAt_eq_cylinder]
lemma occursAt_eq_cylinder
    (p : Pattern A G) (g : G) :
    { x | p.occursIn x g } = cylinder (p.support.image (· * g)) (patternToConfig p g) := by
  classical
  ext x; constructor
  · -- ⇒: from an occurrence, get membership in the cylinder
    intro H u hu
    rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
    -- want: x (w*g) = patternToConfig p g (w*g)
    have hx : x (w * g) = p.data ⟨w, hw⟩ := H w hw
    simpa [patternToConfig_apply_of_mem (p:=p) (v:=g) (w:=w) hw] using hx
  · -- ⇐: from the cylinder, recover an occurrence
    intro H u hu
    -- H gives equality with the translated pattern on the image
    have hx : x (u * g) = patternToConfig p g (u * g) :=
      H (u * g) (Finset.mem_image_of_mem (· * g) hu)
    -- rewrite the RHS by the “apply_of_mem” lemma
    simpa [patternToConfig_apply_of_mem (p:=p) (v:=g) (w:=u) hu] using hx

end OccursAt

/-! ## Forbidden sets and subshifts -/

section DefSubshiftByForbidden

variable {A G : Type*} [Monoid G] [IsRightCancelMul G] [TopologicalSpace A] [DiscreteTopology A]
           [Inhabited A] [DecidableEq G]

/-- Occurrence sets are open. -/
@[to_additive addOccursAt_open]
lemma occursAt_open (p : Pattern A G) (g : G) :
    IsOpen { x | p.occursIn x g } := by
  rw [occursAt_eq_cylinder]; exact isOpen_cylinder _ _

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

/-- Occurrence sets are closed. -/
@[to_additive addOccursAt_closed]
lemma occursAt_closed (p : Pattern A G) (g : G) :
    IsClosed { x | p.occursIn x g } := by
  rw [occursAt_eq_cylinder]; exact isClosed_cylinder _ _

/-- Subshift defined by forbidden patterns. -/
@[to_additive addX_F]
def X_F (F : Set (Pattern A G)) : Subshift A G :=
{ carrier := forbids F,
  isClosed := forbids_closed F,
  shiftInvariant := forbids_shift_invariant F }

attribute [inherit_doc SymbolicDynamics.FullShift.X_F] SymbolicDynamics.FullShift.addX_F

/-- Subshift of finite type defined by a finite family of forbidden patterns. -/
@[to_additive addSFT]
def SFT (F : Finset (Pattern A G)) : Subshift A G :=
  X_F (F : Set (Pattern A G))

attribute [inherit_doc SymbolicDynamics.FullShift.SFT] SymbolicDynamics.FullShift.addSFT

end DefSubshiftByForbidden

section Language

variable {A : Type*} [Fintype A]
variable {G : Type*}
variable [TopologicalSpace A]
variable [Monoid G]

/-- Patterns with fixed support `U`. -/
@[to_additive AddFixedSupport]
def FixedSupport (A : Type*) (G : Type*) [Monoid G] (U : Finset G) :=
  { p : Pattern A G // p.support = U }

attribute [inherit_doc SymbolicDynamics.FullShift.FixedSupport]
  SymbolicDynamics.FullShift.AddFixedSupport

/-- `FixedSupport A G U ≃ (U → A)`; gives finiteness immediately. -/
@[to_additive addEquivFun]
def equivFun {U : Finset G} :
  FixedSupport A G U ≃ (U → A) where
  toFun   := fun p i => p.1.data ⟨i.1, by simp [p.2]⟩
  invFun  := fun f => ⟨{ support := U, data := f }, rfl⟩
  left_inv := by rintro ⟨p,hU⟩; apply Subtype.ext; cases hU; rfl
  right_inv := by intro f; rfl

attribute [inherit_doc SymbolicDynamics.FullShift.equivFun] SymbolicDynamics.FullShift.addEquivFun

@[to_additive SymbolicDynamics.FullShift.addFintypeFixedSupport] noncomputable
instance fintypeFixedSupport {U : Finset G} :
    Fintype (FixedSupport A G U) := by
  classical exact Fintype.ofEquiv (U → A) (equivFun (A := A) (G := G) (U := U)).symm

/-- Language on a finite set `U ⊆ G`: patterns obtained by restricting some `x ∈ X`. -/
@[to_additive addLanguageOn]
def languageOn (X : Set (G → A)) (U : Finset G) : Set (Pattern A G) :=
  { p | ∃ x ∈ X, patternFromConfig x U = p }

attribute [inherit_doc SymbolicDynamics.FullShift.languageOn]
  SymbolicDynamics.FullShift.addLanguageOn


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

attribute [inherit_doc SymbolicDynamics.FullShift.languageCardOn]
  SymbolicDynamics.FullShift.addLanguageCardOn

/-- Number of patterns of a subshift on a finite shape `U`. -/
@[to_additive addPatternCountOn]
noncomputable def patternCountOn (Y : Subshift A G) (U : Finset G) : ℕ :=
  languageCardOn (A := A) (G := G) Y.carrier U

attribute [inherit_doc SymbolicDynamics.FullShift.patternCountOn]
  SymbolicDynamics.FullShift.addPatternCountOn

end Language

end FullShift

end SymbolicDynamics
