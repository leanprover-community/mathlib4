/-
Copyright (c) 2025 Silvère Gangloff. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Silvère Gangloff
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Basic

/-!
# Symbolic dynamics on cancellative monoids

This file develops a minimal API for symbolic dynamics over a
**right-cancellative monoid** `G`—formally, a structure carrying `[Monoid G]`
and `[IsRightCancelMul G]` (which becomes `[AddMonoid G]` and
`[IsRightCancelAdd G]` in the additive form). Throughout the documentation we use the
**additive** notations, which are the most common in symbolic dynamics, although
all the notions introduced are defined in the multiplicative notations and adapted
to the additive notation.

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
require solving equations of the form `w + v = h`. For this to have a unique
solution `w` given `h` and `v`, we assume **right-cancellation**:
if `a + v = b + v` then `a = b`. This allows us to define
`Pattern.extend` (which extends a pattern into a configuration
using the default value of `A`) without using inverses,
so that the theory works not only for groups but also for cancellative monoids.

## Main definitions

* `shift g x` — right translation: in additive notation `(shift v x) u = x (u + v)` (using the
**right** action of `G` on configurations).
* `cylinder U x` — configurations agreeing with `x` on a finite set `U ⊆ G`.
* `Pattern A G` — finite support together with values on that support.
* `Pattern.occursInAt p x g` — occurrence of `p` in `x` at translate `g`.
* `forbidden F` — configurations avoiding every pattern in `F`.
* `Subshift A G` — closed, shift-invariant subsets of the full shift.
* `MulSubshift.ofForbidde F` — the subshift defined by forbidding a family of patterns.
* `subshift_of_finite_type F` — a subshift of finite type defined by a finite set of
forbidden patterns.
* `languageOn X U` — the set of patterns of shape `U` obtained by restricting some `x ∈ X`.

## Design choice: ambient vs. inner (subshift-relative) viewpoint

All core notions (shift, cylinder, occurrence, language, …) are defined **in the
ambient full shift** `G → A`. A subshift is then a closed, invariant subset,
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
  require `[Fintype A]` and `[DecidableEq A]`.
-/

set_option linter.style.openClassical false

@[expose] public section

noncomputable section
open Set Topology

namespace SymbolicDynamics

namespace FullShift

/-! ## Full shift and shift action -/

section ShiftDefinition

variable {A G : Type*} [Monoid G]

/-- The **right-translation shift** on configurations.

We call *configuration* an element of `G → A`.

Given a configuration `x : G → A` and an element `g : G` of the monoid, the shifted configuration
`mulShift g x` is defined by `(mulShift g x) h = x (h * g)`.

Intuitively, this moves the whole configuration "in the direction of `g`": the value
at position `h` in the shifted configuration is the value that was at position
`h * g` in the original one.

For example, if `G = ℤ` (with addition) and `A = {0, 1}`, then
`mulShift 1 x` is the sequence obtained from `x` by shifting every symbol one
step to the left. -/
@[to_additive /-- The **right-translation shift** on configurations, in additive notation.

We call *configuration* an element of `G → A`.

Given a configuration `x : G → A` and an element `g : G` of the additive monoid,
the shifted configuration `shift g x` is defined by `(shift g x) h = x (h + g)`.

Intuitively, this moves the whole configuration "in the direction of `g`": the value
at position `h` in the shifted configuration is the value that was at position
`h + g` in the original one.

For example, if `G = ℤ` and `A = {0, 1}`, then
`shift 1 x` is the sequence obtained from `x` by shifting every symbol one
step to the left. -/]
def mulShift (g : G) (x : G → A) : G → A :=
  fun h => x (h * g)

@[to_additive (attr := simp)] lemma mulShift_apply (g : G) (x : G → A) (h : G) :
  mulShift g x h = x (h * g) := rfl

@[to_additive (attr := simp)] lemma mulShift_one (x : G → A) : mulShift (1 : G) x = x := by
  ext h; simp [mulShift]

/-- Composition of right-translation shifts corresponds to multiplication in the monoid `G`. -/
@[to_additive] lemma mulShift_mul (g₁ g₂ : G) (x : G → A) :
    mulShift (g₁ * g₂) x = mulShift g₁ (mulShift g₂ x) := by
  ext h; simp [mulShift, mul_assoc]

variable [TopologicalSpace A]

/-- The right-translation shift is continuous. -/
@[to_additive (attr := fun_prop)] lemma continuous_mulShift (g : G) :
    Continuous (mulShift (A := A) g) := by
  -- coordinate projections are continuous; composition preserves continuity
  unfold mulShift
  fun_prop

end ShiftDefinition

/-! ## Cylinders -/

section Cylinders

variable {A G : Type*}

/-- A *cylinder set* is the set of all configurations that agree with a given
reference configuration `x` on a fixed finite subset `U` of the index set `G`.

The set `U` is called the *support* of the cylinder.

Intuitively, cylinders specify the "letters" on finitely many coordinates, while
leaving all other coordinates free. For example, in the full shift `{0, 1}^ℤ`,
the cylinder determined by `U = {0, 1}` and `x 0 = 1, x 1 = 0` consists of all
bi-infinite sequences of `0`s and `1`s whose entries on positions `0` and `1`
respectively are `1` and `0`.

When `A` has the discrete topology, cylinder sets form a basis of clopen sets
for the product topology on `G → A`. -/
def cylinder (U : Finset G) (x : G → A) : Set (G → A) :=
  { y | ∀ i ∈ U, y i = x i }

/-- A cylinder set on `U` is the `Set.pi` over `U` of the singletons `{x i}`,
viewed as a subset of `G → A`. Equivalently, it is the preimage of that product
of singletons in `U → A` under the restriction map `(G → A) → (U → A)`. -/
lemma cylinder_eq_set_pi (U : Finset G) (x : G → A) :
    cylinder U x = Set.pi (↑U : Set G) (fun i => ({x i} : Set A)) := by
  ext y; simp [cylinder, Set.pi]

lemma mem_cylinder {U : Finset G} {x y : G → A} :
    y ∈ cylinder U x ↔ ∀ i ∈ U, y i = x i := Iff.rfl

variable [TopologicalSpace A]

/-- Cylinders are open when `A` is discrete. -/
lemma isOpen_cylinder [DiscreteTopology A] (U : Finset G) (x : G → A) :
    IsOpen (cylinder U x) := by
  simpa [cylinder_eq_set_pi U x] using isOpen_set_pi (U.finite_toSet) (by simp)

/-- Cylinders are closed when `A` is a T1 Space. -/
lemma isClosed_cylinder [T1Space A] (U : Finset G) (x : G → A) :
    IsClosed (cylinder U x) := by
  simpa [cylinder_eq_set_pi U x] using isClosed_set_pi (by simp)

end Cylinders

/-! ## Patterns and occurrences -/


section SubshiftDef
variable (A : Type*) [TopologicalSpace A]
variable (G : Type*) [AddMonoid G]

/-- A *subshift* on an alphabet `A` is a closed, shift-invariant subset of `G → A`. Formally, it is
composed of:
* `carrier`: the underlying set of allowed configurations.
* `isClosed`: the set is topologically closed in `A^G`.
* `mapsTo`: the set is invariant under all right-translation shifts
  `(shift g)`. -/
structure Subshift where
  /-- The underlying set of configurations (additive monoid version). -/
  carrier : Set (G → A)
  /-- Closedness of `carrier`. -/
  isClosed : IsClosed carrier
  /-- Shift invariance of `carrier` for the additive shift `shift`. -/
  mapsTo : ∀ g : G, MapsTo (shift g) carrier carrier

end SubshiftDef

section MulSubshiftDef
variable (A : Type*) [TopologicalSpace A]
variable (G : Type*) [Monoid G]

/-- A *subshift* on an alphabet `A` over a multiplicative monoid `G` is a closed,
shift-invariant subset of `G → A`, where the shift is given by right-multiplication.
Formally, it is composed of:
* `carrier`: the underlying set of allowed configurations.
* `isClosed`: the set is topologically closed in `A^G`.
* `mapsTo`: the set is invariant under all right-translation shifts
  `(mulShift g)`. -/
@[to_additive existing Subshift]
structure MulSubshift where
  /-- The underlying set of configurations. -/
  carrier : Set (G → A)
  /-- Closedness of `carrier`. -/
  isClosed : IsClosed carrier
  /-- Shift invariance of `carrier`. -/
  mapsTo : ∀ g : G, MapsTo (mulShift g) carrier carrier

end MulSubshiftDef


/-- Example: the **full shift** on alphabet `A` over the multiplicative monoid `G`.

It is the subshift whose underlying set is the set of all configurations
`G → A`.
-/
@[to_additive fullShift
/-- Example: the **full shift** on alphabet `A` over the additive monoid `G`.

It is the subshift whose underlying set is the set of all configurations
`G → A`.
-/]
def mulFullShift (A G) [TopologicalSpace A] [Monoid G] : MulSubshift A G where
  carrier := Set.univ
  isClosed := isClosed_univ
  mapsTo := by
    intro _ _ _
    simp

/-- A *pattern* is a finite configuration in the full shift `A^G`.

It consists of:
* a finite subset `support : Finset G` of coordinates, called the support of `p`;
* an assignment `data : support → A` of symbols to each point in the support.

Intuitively, a pattern is a "partial configuration" (like a finite word),
specifying finitely many values of a configuration in `G → A`. Patterns are
the basic building blocks used to define subshifts via forbidden configurations.
Note that each pattern corresponds to a cylinder, which is the set of configurations
which agree with this pattern on its support. -/
structure Pattern (A : Type*) (G : Type*) where
  /-- Finite support of the pattern. -/
  support : Finset G
  /-- The value (symbol) at each point of the support. -/
  data : support → A

namespace Pattern
section Dominos

variable (G : Type*)

/-- A *domino* is a pattern supported on exactly two positions (sometimes
also called cells) `{i, j}`, specifying the value `ai` at `i` and the value `aj` at `j`.

In symbolic dynamics, dominos (two-cell patterns) are the simplest nontrivial
building blocks: they describe local adjacency conditions between two sites
of a configuration. -/
def domino {A : Type*} (i j : G) (ai aj : A) : Pattern A G := by
  classical
  exact
    { support := ({i, j} : Finset G)
      data := fun ⟨z, _hz⟩ => if z = i then ai else aj }

end Dominos
end Pattern

section Forbidden

variable {A G : Type*} [Monoid G]

/-- `p.mulOccursInAt x g` means that the finite pattern
`p` appears in the configuration `x`
at position `g`.

Formally: for every position `h` in the support of `p`, the value of the configuration
at `h * g` coincides with the value specified by `p` at `h`.

Intuitively, if you shift the configuration `x` by `g` (using `mulShift g`),
then on the support of `p` you exactly recover the pattern `p`. This is the basic
notion of "pattern occurrence" used to define subshifts via forbidden patterns. -/
@[to_additive Pattern.occursInAt
/-- `p.occursInAt x g` means that the finite pattern `p` appears in the configuration `x`
at position `g`.

Formally: for every position `h` in the support of `p`, the value of the configuration
at `h + g` coincides with the value specified by `p` at `h`.

Intuitively, if you shift the configuration `x` by `g` (using `shift g`),
then on the support of `p` you exactly recover the pattern `p`. This is the basic
notion of "pattern occurrence" used to define subshifts via forbidden patterns. -/]
def Pattern.mulOccursInAt (p : Pattern A G) (x : G → A) (g : G) : Prop :=
  ∀ (h) (hh : h ∈ p.support), x (h * g) = p.data ⟨h, hh⟩

/-- `mulForbidden F` is the set of configurations that avoid every pattern in `F`.

Formally: `x ∈ mulForbidden F` if and only if for every pattern `p ∈ F` and every
monoid element `g : G`, the pattern `p` does not occur in `x` at position `g`.

Intuitively, `mulForbidden F` is the shift space defined by declaring the finite set
(or family) of patterns `F` to be *forbidden*. A configuration belongs to the subshift if and only
it avoids all the forbidden patterns. -/
@[to_additive forbidden
/-- `forbidden F` is the set of configurations that avoid every pattern in `F`.

Formally: `x ∈ forbidden F` if and only if for every pattern `p ∈ F` and every
monoid element `g : G`, the pattern `p` does not occur in `x` at position `g`.

Intuitively, `forbidden F` is the shift space defined by declaring the finite set
(or family) of patterns `F` to be *forbidden*. A configuration belongs to the subshift if and only
it avoids all the forbidden patterns. -/]
def mulForbidden (F : Set (Pattern A G)) : Set (G → A) :=
  { x | ∀ p ∈ F, ∀ g : G, ¬ p.mulOccursInAt x g }

end Forbidden

section OccursInAt


variable {A : Type*} [Inhabited A]
variable {G : Type*} [Monoid G] [IsRightCancelMul G]

section PatternExtension
open scoped Classical
-- We assume right-cancellation throughout this section for uniqueness of preimages under (_ * v)
-- or (_ + v).

/-- Turn a finite pattern into a configuration, by extending it with
the default symbol outside its support.

Formally: given a pattern `p` with finite support in `G`, we define a configuration
`Pattern.extendAtOrigin p : G → A` by setting
* `Pattern.extendAtOrigin p i = p.data ⟨i, h⟩` if `i ∈ p.support`,
* `Pattern.extendAtOrigin p i = default` otherwise.

This produces a canonical "completion" of the pattern to a configuration,
filling all unspecified positions with `default`. -/
def Pattern.extendAtOrigin (p : Pattern A G) : G → A :=
  fun i ↦ if h : i ∈ p.support then p.data ⟨i, h⟩ else default

/-- Translate a finite pattern `p` so that it occurs at the translate `v`, before completing into
a configuration.

On input `h : G`, we proceed as follows:
* if `h` lies in the right-translate of the support, i.e. `h ∈ p.support.image (· * v)`,
  choose (noncomputably) `w ∈ p.support` with `w * v = h` and return `p.data ⟨w, _⟩`;
* otherwise return `default`.

This definition does not assume right-cancellation; it only *chooses* a preimage.
Uniqueness (and the usual equations such as `Pattern.mulExtend p v (w * v) = p.data ⟨w, _⟩`)
require a right-cancellation hypothesis and are proved in separate lemmas.
-/
@[to_additive Pattern.extend
/-- Translate a finite pattern `p` so that it occurs at the translate `v`, before completing into
a configuration.

On input `h : G`, we proceed as follows:
* if `h` lies in the right-translate of the support, i.e. `h ∈ p.support.image (· + v)`,
  choose (noncomputably) `w ∈ p.support` with `w + v = h` and return `p.data ⟨w, _⟩`;
* otherwise return `default`.

This definition does not assume right-cancellation; it only *chooses* a preimage.
Uniqueness (and the usual equations such as `Pattern.extend p v (w + v) = p.data ⟨w, _⟩`)
require a right-cancellation hypothesis and are proved in separate lemmas.
-/]
noncomputable def Pattern.mulExtend (p : Pattern A G) (v : G) : G → A :=
  fun h =>
    if hmem : h ∈ p.support.image (· * v) then
      -- package existence of a preimage under (_ * v)
      let ex : ∃ w, w ∈ p.support ∧ w * v = h := by
        simpa [Finset.mem_image] using hmem
      let w := Classical.choose ex
      have hw  : w ∈ p.support := (Classical.choose_spec ex).1
      have hwv : w * v = h := (Classical.choose_spec ex).2
      p.data ⟨w, hw⟩
    else
      default
end PatternExtension

namespace Pattern
/-- Extract the finite pattern given by restricting a configuration `x : G → A`
to a finite subset `U : Finset G`.

Formally: the support is `U`, and for each `i ∈ U` the pattern records the value
`x i`. In other words, `Pattern.fromConfig x U` is the partial configuration of
`x` visible on the coordinates in `U`.

This is the inverse construction to `Pattern.extendAtOrigin` (which extends a
finite pattern to a configuration by filling with `default`). -/
def fromConfig (x : G → A) (U : Finset G) : Pattern A G where
  support := U
  data := fun i => x i.1

/-- On the translated support, `p.mulExtend v` agrees with `p` at the preimage.

More precisely, if `w ∈ p.support`, then at the translated site `w * v`,
the configuration `p.mulExtend v` takes the value prescribed by `p` at `w`.

This uses `[IsRightCancelMul G]` to identify the unique preimage of `w * v`
under right-multiplication by `v`. -/
@[to_additive extend_apply_add_right_of_mem
  /-- On the translated support, `p.extend v` agrees with `p` at the preimage.

  More precisely, if `w ∈ p.support`, then at the translated site `w + v`,
  the configuration `p.extend v` takes the value prescribed by `p` at `w`.

  This uses `[IsRightCancelAdd G]` to identify the unique preimage of `w + v`
  under right-translation by `v`. -/]
lemma mulExtend_apply_mul_right_of_mem
    (p : Pattern A G) (v w : G) (hw : w ∈ p.support) :
    p.mulExtend v (w * v) = p.data ⟨w, hw⟩ := by
  classical
  -- (w*v) is in the translated support
  have hmem : (w * v) ∈ p.support.image (· * v) :=
    Finset.mem_image.mpr ⟨w, hw, rfl⟩
  -- existential used in the branch
  have ex : ∃ w', w' ∈ p.support ∧ w' * v = w * v := by
    simpa [Finset.mem_image] using hmem
  -- open the `if` branch as returned by the definition
  have h1 :
      p.mulExtend v (w * v)
        = p.data ⟨Classical.choose ex, (Classical.choose_spec ex).1⟩ := by
    simp [Pattern.mulExtend, hmem]
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
  have h3 : (⟨w, hw_w⟩ : p.support) = (⟨w, hw⟩ : p.support) := by
    apply Subtype.ext; rfl
  -- put the rewrites together
  calc
    p.mulExtend v (w * v)
        = p.data ⟨Classical.choose ex, (Classical.choose_spec ex).1⟩ := h1
    _   = p.data ⟨w, hw_w⟩ := by
            -- push h2 through `p.data`
            simpa using
              (congrArg (fun z : {x // x ∈ p.support} => p.data z) h2)
    _   = p.data ⟨w, hw⟩ := by
            -- push h3 through `p.data`
            simp [h3]


/-- Shifting a configuration commutes with occurrences of a pattern.

Formally: a pattern `p` occurs in the shifted configuration `mulShift h x` at
position `g` if and only if it occurs in the original configuration `x` at
position `g * h`. -/
@[to_additive occursInAt_shift
/-- Shifting a configuration commutes with occurrences of a pattern.

Formally: a pattern `p` occurs in the shifted configuration `shift h x` at
position `g` if and only if it occurs in the original configuration `x` at
position `g + h`. -/]
lemma mulOccursInAt_mulShift {A G : Type*} [Monoid G] (p : Pattern A G) (x : G → A) (g h : G) :
    p.mulOccursInAt (mulShift h x) g ↔ p.mulOccursInAt x (g * h) := by
  constructor <;> intro H u hu <;> simpa [mulShift, mul_assoc] using H u hu

/-- Configurations that avoid a family `F` of patterns are stable under the shift.

Formally: if `x` avoids every `p ∈ F` at every position, then for any `h : G`,
the shifted configuration `mulShift h x` also avoids every `p ∈ F` at every position. -/
@[to_additive mapsTo_shift_forbidden
  /-- Configurations that avoid a family `F` of patterns are stable under the shift.

Formally: if `x` avoids every `p ∈ F` at every position, then for any `h : G`,
the shifted configuration `shift h x` also avoids every `p ∈ F` at every position. -/]
lemma mapsTo_mulShift_mulForbidden {A G : Type*} [Monoid G]
    (F : Set (Pattern A G)) (h : G) :
    Set.MapsTo (fun x => mulShift h x)
    (mulForbidden (A := A) (G := G) F) (mulForbidden F) := by
  -- unfold `MapsTo`
  intro x hx p hp g
  specialize hx p hp (g * h)
  contrapose! hx
  simpa [mulOccursInAt_mulShift] using hx

end Pattern

section OccursInAtEqCylinder
open scoped Classical

/-- We call *occurrence set* for pattern `p` and position `g` the set of configurations
in which a pattern `p` occurs at position `g`.

This proves that it is exactly the cylinder corresponding to the
pattern obtained by translating `p` by `g`.

Equivalently, `p.mulOccursInAt x g` iff on every translated site
`w * g` (with `w ∈ p.support`)
the configuration `x` agrees with the translated pattern `Pattern.mulExtend p g`.

(This uses `[IsRightCancelMul G]` to identify the preimage along right-multiplication by `g`.) -/
@[to_additive occursInAt_eq_cylinder
  /-- We call *occurrence set* for pattern `p` and position `g` the set of configurations
in which a pattern `p` occurs at position `g`.

This proves that it is exactly the cylinder corresponding to the
pattern obtained by translating `p` by `g`.

Equivalently, `p.occursInAt x g` iff on every translated site `w + g` (with `w ∈ p.support`)
the configuration `x` agrees with the translated pattern `Pattern.extend p g`.

(This uses `[IsRightCancelMul G]` to identify the preimage along right-multiplication by `g`.) -/]
lemma mulOccursInAt_eq_cylinder
    (p : Pattern A G) (g : G) :
    { x | p.mulOccursInAt x g } = cylinder (p.support.image (· * g)) (p.mulExtend g) := by
  ext x; constructor
  · -- ⇒: from an occurrence, get membership in the cylinder
    intro H u hu
    rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
    -- want: x (w*g) = Pattern.mulExtend p g (w*g)
    have hx : x (w * g) = p.data ⟨w, hw⟩ := H w hw
    simpa [Pattern.mulExtend_apply_mul_right_of_mem (p := p) (v := g) (w := w) hw] using hx
  · -- ⇐: from the cylinder, recover an occurrence
    intro H u hu
    -- H gives equality with the translated pattern on the image
    have hx : x (u * g) = p.mulExtend g (u * g) :=
      H (u * g) (Finset.mem_image_of_mem (· * g) hu)
    -- rewrite the RHS by the “apply_of_mem” lemma
    simpa [Pattern.mulExtend_apply_mul_right_of_mem (p := p) (v := g) (w := u) hu] using hx
end OccursInAtEqCylinder
end OccursInAt

/-! ## Forbidden sets and subshifts -/

section DefSubshiftByForbidden

variable {A : Type*} [TopologicalSpace A] [Inhabited A]
variable {G : Type*} [Monoid G] [IsRightCancelMul G]

/-- Occurrence sets are open. -/
@[to_additive isOpen_occursInAt]
lemma isOpen_mulOccursInAt [DiscreteTopology A] (p : Pattern A G) (g : G) :
    IsOpen { x | p.mulOccursInAt x g } := by
  simpa [mulOccursInAt_eq_cylinder] using isOpen_cylinder _ _

/-- Avoiding a fixed family of patterns is a closed condition (in the product topology on `G → A`).

Since each occurrence set `{ x | p.mulOccursInAt x v }` is open (when `A` is discrete),
its complement `{ x | ¬ p.mulOccursInAt x v }` is closed; `forbidden F` is the intersection
of these closed sets over `p ∈ F` and `v ∈ G`. -/
@[to_additive isClosed_forbidden /-- Avoiding a fixed family of patterns is a closed
condition (in the product topology on `G → A`).

Since each occurrence set `{ x | p.occursInAt x v }` is open (when `A` is discrete),
its complement `{ x | ¬ p.occursInAt x v }` is closed; `forbidden F` is the intersection
of these closed sets over `p ∈ F` and `v ∈ G`. -/]
lemma isClosed_mulForbidden [DiscreteTopology A] (F : Set (Pattern A G)) :
    IsClosed (mulForbidden F) := by
  rw [mulForbidden]
  -- Rewrite as an intersection indexed by `p ∈ F` and `v : G`.
  have h_eq :
      {x | ∀ p ∈ F, ∀ v : G, ¬ p.mulOccursInAt x v}
        = ⋂ (p : Pattern A G) (hp : p ∈ F) (v : G), {x | ¬ p.mulOccursInAt x v} := by
    ext x; simp
  rw [h_eq]
  -- Now prove that this big intersection is closed.
  have h_closed :
      IsClosed (⋂ (p : Pattern A G) (hp : p ∈ F) (v : G), {x | ¬ p.mulOccursInAt x v}) := by
    refine isClosed_iInter (fun p => ?_)
    refine isClosed_iInter (fun hp => ?_)
    refine isClosed_iInter (fun v => ?_)
    -- For each `p, hp, v`, the section is the complement of an open occurrence set.
    have : {x | ¬ p.mulOccursInAt x v} = {x | p.mulOccursInAt x v}ᶜ := by
      ext x; simp
    simpa [this, isClosed_compl_iff] using
      isOpen_mulOccursInAt (A := A) (G := G) p v
  simpa using h_closed

/-- Occurrence sets are closed. -/
@[to_additive isClosed_occursInAt]
lemma isClosed_mulOccursInAt [T1Space A] (p : Pattern A G) (g : G) :
    IsClosed { x | p.mulOccursInAt x g } := by
  simpa [mulOccursInAt_eq_cylinder] using isClosed_cylinder _ _

/-- The subshift defined by a family of forbidden patterns `F`.

This is a standard way to construct subshifts:
`MulSubshift.ofForbidden F` consists of all configurations `x : G → A` in which no pattern
`p ∈ F` occurs at any position.

Formally:
* the carrier is `forbidden F` (configurations avoiding `F`),
* it is closed because each occurrence set is open, and
* it is shift-invariant since avoidance is preserved by shifts. -/
@[to_additive /-- The subshift defined by a family of forbidden patterns `F`.

This is a standard way to construct subshifts:
`Subshift.ofForbidden F` consists of all configurations `x : G → A` in which no pattern
`p ∈ F` occurs at any position.

Formally:
* the carrier is `forbidden F` (configurations avoiding `F`),
* it is closed because each occurrence set is open, and
* it is shift-invariant since avoidance is preserved by shifts. -/]
def MulSubshift.ofForbidden [DiscreteTopology A] (F : Set (Pattern A G)) : MulSubshift A G where
  carrier := mulForbidden F
  isClosed := isClosed_mulForbidden F
  mapsTo := Pattern.mapsTo_mulShift_mulForbidden F

/-- A subshift of finite type (SFT) is a subshift defined by forbidding
a *finite* family of patterns.

Formally, `mulSubshift_of_finite_type F` is `MulSubshift.ofForbidden F` where `F` is a
`Finset (Pattern A G)`. -/
@[to_additive /-- A subshift of finite type (SFT) is a subshift defined by forbidding
a *finite* family of patterns.

Formally, `subshift_of_finite_type F` is `Subshift.ofForbidden F` where `F` is a
`Finset (Pattern A G)`. -/]
def mulSubshift_of_finite_type [DiscreteTopology A] (F : Finset (Pattern A G)) : MulSubshift A G :=
  MulSubshift.ofForbidden (F : Set (Pattern A G))

end DefSubshiftByForbidden

section Language

variable {A : Type*} [Fintype A]
variable {G : Type*}

/-- Patterns with support exactly `U` form a finite set. -/
lemma finite_patterns_with_support
    {A G : Type*} [Fintype A]
    (U : Finset G) :
    ({ p : Pattern A G | p.support = U } : Set (Pattern A G)).Finite := by
  classical
  -- Local equivalence between the subtype and functions on U
  have e : { p : Pattern A G // p.support = U } ≃ (U → A) :=
  { toFun   := fun p i => p.1.data ⟨i.1, by simp [p.2]⟩
    invFun  := fun f => ⟨{ support := U, data := f }, rfl⟩
    left_inv := by
      rintro ⟨p, hU⟩
      apply Subtype.ext
      cases hU
      rfl
    right_inv := by intro f; rfl }
  -- Give a Fintype structure to the subtype via this equivalence
  haveI : Fintype { p : Pattern A G // p.support = U } :=
    Fintype.ofEquiv (U → A) e.symm
  -- Now prove finiteness of `{ p : Pattern A G | p.support = U }` by
  -- viewing it as the image of `univ` in that finite subtype
  let T := { p : Pattern A G // p.support = U }
  have h_univ : (Set.univ : Set T).Finite :=
    Set.finite_univ
  let coeT : T → Pattern A G := fun p => (p : Pattern A G)
  have h_image : (Set.image coeT (Set.univ : Set T)).Finite :=
    h_univ.image _
  have himage_eq :
      Set.image coeT (Set.univ : Set T)
        = ({ p : Pattern A G | p.support = U } : Set (Pattern A G)) := by
    ext p; constructor
    · intro hp
      rcases hp with ⟨p', -, rfl⟩
      exact p'.property
    · intro hp
      refine ⟨⟨p, hp⟩, ?_, rfl⟩
      simp
  simpa [himage_eq] using h_image

/-- The language of a set of configurations `X` on a finite shape `U`.

This is the set of all finite patterns obtained by restricting some configuration
`x ∈ X` to `U`. -/
@[to_additive languageOn]
def mulLanguageOn (X : Set (G → A)) (U : Finset G) : Set (Pattern A G) :=
  { p | ∃ x ∈ X, Pattern.fromConfig x U = p }

attribute [inherit_doc SymbolicDynamics.FullShift.mulLanguageOn]
  SymbolicDynamics.FullShift.languageOn

/-- The language of a subshift `Y` on a finite shape `U`. -/
@[to_additive /-- The language of a subshift `Y` on a finite shape `U`. -/]
def MulSubshift.languageOn {A G} [TopologicalSpace A] [Monoid G]
    (Y : MulSubshift A G) (U : Finset G) : Set (Pattern A G) :=
  SymbolicDynamics.FullShift.mulLanguageOn (A:=A) (G:=G) Y.carrier U

end Language

end FullShift

end SymbolicDynamics
