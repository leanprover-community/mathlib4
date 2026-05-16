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
**left-cancellative monoid** `G`—formally, a structure carrying `[Monoid G]`
and `[IsLeftCancelMul G]` (which becomes `[AddMonoid G]` and
`[IsLeftCancelAdd G]` in the additive form). Throughout the documentation we use the
**additive** notations, which are the most common in symbolic dynamics, although
all the notions introduced are defined in the multiplicative notations and adapted
to the additive notation.

Given a finite alphabet `A`, the ambient configuration space is the set of
functions `G → A`, endowed with the product topology. We define the
left-translation action, cylinders, finite patterns, their occurrences,
forbidden sets, and subshifts (closed, shift-invariant subsets). Basic
topological facts (e.g. cylinders are clopen, occurrence sets are clopen,
forbidden sets are closed) are proved under discreteness assumptions on
the alphabet.

The development is generic for left-cancellative monoids. This covers both
groups (the standard setting of symbolic dynamics) and more general monoids
where cancellation holds but inverses may not exist. Geometry specific to
`ℤ^d` (boxes/cubes and the box-based entropy) is deferred to a separate
specialization.

## Why cancellativity?

Some constructions, such as translating a finite pattern to occur at a point `v`,
require solving equations of the form `w + v = h`. For this to have a unique
solution `w` given `h` and `v`, we assume **left-cancellation**:
if `v + a = v + b` then `a = b`. This allows us to define
`Pattern.shift` (which shifts a pattern) without using inverses,
so that the theory works not only for groups but also for cancellative monoids.

## Main definitions

* `shift g x` — left translation: in additive notation `(shift v x) u = x (v + u)` (using the
**left** action of `G` on configurations).
* `cylinder U x` — configurations agreeing with `x` on a finite set `U ⊆ G`.
* `Pattern A G` — a configuration which takes
default value outside of a finite support, together with this support.
* `Pattern.occursInAt p x g` — occurrence of `p` in `x` at translate `g`.
* `forbidden F` — configurations avoiding every pattern in `F`.
* `Subshift A G` — closed, shift-invariant subsets of the full shift.
* `MulSubshift.ofForbidden F` — the subshift defined by forbidding a family of patterns.
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

* Openness results for cylinders and occurrence sets use
  `[DiscreteTopology A]`. Closeness results use `[T1Space A]`.
-/

@[expose] public section

noncomputable section
open Set Topology

namespace SymbolicDynamics

namespace FullShift

/-! ## Full shift and shift action -/

section ShiftDefinition

variable {A G : Type*} [Monoid G]

/-- The **left-translation shift** on configurations.

We call *configuration* an element of `G → A`.

Given a configuration `x : G → A` and an element `g : G` of the monoid, the shifted configuration
`mulShift g x` is defined by `(mulShift g x) h = x (g * h)`.

Intuitively, this moves the whole configuration "in the direction of `g`": the value
at position `h` in the shifted configuration is the value that was at position
`g * h` in the original one.

For example, if `G = ℤ` (with addition) and `A = {0, 1}`, then
`mulShift 1 x` is the sequence obtained from `x` by shifting every symbol one
step to the left. -/
@[to_additive /-- The **left-translation shift** on configurations, in additive notation.

We call *configuration* an element of `G → A`.

Given a configuration `x : G → A` and an element `g : G` of the additive monoid,
the shifted configuration `shift g x` is defined by `(shift g x) h = x (g + h)`.

Intuitively, this moves the whole configuration "in the direction of `g`": the value
at position `h` in the shifted configuration is the value that was at position
`g + h` in the original one.

For example, if `G = ℤ` and `A = {0, 1}`, then
`shift 1 x` is the sequence obtained from `x` by shifting every symbol one
step to the left. -/]
def mulShift (g : G) (x : G → A) : G → A :=
  fun h => x (g * h)

@[to_additive (attr := simp)] lemma mulShift_apply (g : G) (x : G → A) (h : G) :
    mulShift g x h = x (g * h) := rfl

@[to_additive (attr := simp)] lemma mulShift_one (x : G → A) : mulShift (1 : G) x = x := by
  ext h; simp [mulShift]

/-- Composition of left-translation shifts corresponds to multiplication in the monoid `G`. -/
@[to_additive] lemma mulShift_mul (g₁ g₂ : G) (x : G → A) :
    mulShift (g₁ * g₂) x = mulShift g₂ (mulShift g₁ x) := by
  ext h; simp [mulShift, mul_assoc]

variable [TopologicalSpace A]

/-- The left-translation shift is continuous. -/
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

/-- A *subshift* on an alphabet `A` is a closed, shift-invariant subset of `G → A`. Formally, it is
composed of:
* `carrier`: the underlying set of allowed configurations.
* `isClosed`: the set is topologically closed in `A^G`.
* `mapsTo`: the set is invariant under all left-translation shifts
  `(shift g)`. -/
structure Subshift (A : Type*) [TopologicalSpace A] (G : Type*) [AddMonoid G] where
  /-- The underlying set of configurations (additive monoid version). -/
  carrier : Set (G → A)
  /-- Closedness of `carrier`. -/
  isClosed : IsClosed carrier
  /-- Shift invariance of `carrier` for the additive shift `shift`. -/
  mapsTo : ∀ g : G, MapsTo (shift g) carrier carrier

section MulSubshiftDef
variable (A : Type*) [TopologicalSpace A]
variable (G : Type*) [Monoid G]

/-- A *subshift* on an alphabet `A` over a multiplicative monoid `G` is a closed,
shift-invariant subset of `G → A`, where the shift is given by left-multiplication.
Formally, it is composed of:
* `carrier`: the underlying set of allowed configurations.
* `isClosed`: the set is topologically closed in `A^G`.
* `mapsTo`: the set is invariant under all left-translation shifts
  `(mulShift g)`. -/
@[to_additive existing]
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
`G → A`. -/
@[to_additive fullShift
/-- Example: the **full shift** on alphabet `A` over the additive monoid `G`.

It is the subshift whose underlying set is the set of all configurations
`G → A`.
-/]
def mulFullShift (A G) [TopologicalSpace A] [Monoid G] : MulSubshift A G where
  carrier := Set.univ
  isClosed := isClosed_univ
  mapsTo := fun _ _ _ => trivial

/-- A *pattern* is a finite configuration in the full shift `A^G`.

It consists of:
* a full configuration `config : G → A` in the full shift;
* a finite subset `support : Finset G` of coordinates, called the support of `p`;
* a proof `condition` that outside `support`, `config` takes the default value of `A`.

Intuitively, a pattern is a "partial configuration" specifying finitely many values of
a configuration in `G → A` (the rest being `default`).
Patterns are the basic building blocks used to define subshifts via forbidden configurations.
Note that each pattern corresponds to a cylinder, which is the set of configurations
which agree with this pattern on its support. -/
structure Pattern (A : Type*) (G : Type*) [Inhabited A] where
  /-- The full configuration in the full shift `A^G`. -/
  config : G → A
  /-- Finite support of the pattern. -/
  support : Finset G
  /-- Outside the support, `config` takes the default value of `A`. -/
  condition : ∀ g ∉ support, config g = default

section Forbidden

variable {A G : Type*} [Inhabited A] [Monoid G]

/-- `p.mulOccursInAt x g` means that the finite pattern
`p` appears in the configuration `x`
at position `g`.

Formally: for every position `h` in the support of `p`, the value of the configuration
at `g * h` coincides with the value of `p.config` at `h`.

Intuitively, if you shift the configuration `x` by `g` (using `mulShift g`),
then on the support of `p` you exactly recover the pattern `p`. This is the basic
notion of "pattern occurrence" used to define subshifts via forbidden patterns. -/
@[to_additive Pattern.occursInAt
/-- `p.occursInAt x g` means that the finite pattern `p` appears in the configuration `x`
at position `g`.

Formally: for every position `h` in the support of `p`, the value of the configuration
at `g + h` coincides with the value of `p.config` at `h`.

Intuitively, if you shift the configuration `x` by `g` (using `shift g`),
then on the support of `p` you exactly recover the pattern `p`. This is the basic
notion of "pattern occurrence" used to define subshifts via forbidden patterns. -/]
def Pattern.mulOccursInAt (p : Pattern A G) (x : G → A) (g : G) : Prop :=
  ∀ (h) (_ : h ∈ p.support), x (g * h) = p.config h

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
variable {G : Type*} [Monoid G]

/-- The **shift of a finite pattern** `p` by `v`, as a bundled `Pattern`.

The resulting pattern has:
* support `v • p.support = p.support.image (v * ·)`,
* configuration sending `v * w` to `p.config w` for `w ∈ p.support` (chosen
  noncomputably), and `default` outside the shifted support.

This definition does not assume left-cancellation; it only *chooses* a preimage.
Uniqueness (and the equation `(p.mulShift v).config (v * w) = p.config w`)
requires `[IsLeftCancelMul G]` and is proved in
`Pattern.mulShift_config_apply_mul_left_of_mem`. -/
@[to_additive
/-- The **shift of a finite pattern** `p` by `v` (additive form), as a bundled `Pattern`.

The resulting pattern has:
* support `v +ᵥ p.support = p.support.image (v + ·)`,
* configuration sending `v + w` to `p.config w` for `w ∈ p.support`, `default`
  outside.

This definition does not assume left-cancellation; uniqueness of the chosen
preimage requires `[IsLeftCancelAdd G]`. -/]
protected noncomputable def Pattern.mulShift (p : Pattern A G) (v : G) : Pattern A G := by
  classical
  refine
    ⟨fun h =>
        if hmem : h ∈ p.support.image (v * ·) then
          let ex : ∃ w, w ∈ p.support ∧ v * w = h := by
            simpa [Finset.mem_image] using hmem
          p.config (Classical.choose ex)
        else default,
      p.support.image (v * ·),
      fun _ hg => dif_neg hg⟩

namespace Pattern
/-- Extract the finite pattern given by restricting a configuration `x : G → A`
to a finite subset `U : Finset G`.

The pattern has `config g = x g` for `g ∈ U` and `config g = default` outside `U`,
with support `U`. In other words, `Pattern.fromConfig x U` is the partial configuration of
`x` visible on the coordinates in `U`, padded with `default` elsewhere. -/
noncomputable def fromConfig (x : G → A) (U : Finset G) : Pattern A G := by
  classical
  exact { config := fun g => if g ∈ U then x g else default,
          support := U,
          condition := fun g hg => if_neg hg }

open scoped Classical in
@[to_additive (attr := simp)]
lemma mulShift_support (p : Pattern A G) (v : G) :
    (p.mulShift v).support = p.support.image (v * ·) := rfl

/-- On the translated support, `(p.mulShift v).config` agrees with `p.config`
at the preimage.

More precisely, if `w ∈ p.support`, then at the translated site `v * w`,
the bundled shifted pattern `p.mulShift v` takes the value `p.config w`.

This uses `[IsLeftCancelMul G]` to identify the unique preimage of `v * w`
under left-multiplication by `v`. -/
@[to_additive
  /-- On the translated support, `(p.shift v).config` agrees with `p.config`
  at the preimage. -/]
lemma mulShift_config_apply_mul_left_of_mem [IsLeftCancelMul G]
    (p : Pattern A G) (v w : G) (hw : w ∈ p.support) :
    (p.mulShift v).config (v * w) = p.config w := by
  classical
  -- (v * w) is in the translated support
  have hmem : (v * w) ∈ p.support.image (v * ·) :=
    Finset.mem_image.mpr ⟨w, hw, rfl⟩
  -- existential used in the branch
  have ex : ∃ w', w' ∈ p.support ∧ v * w' = v * w := by
    simpa [Finset.mem_image] using hmem
  -- open the `if` branch as returned by the definition
  have h1 : (p.mulShift v).config (v * w) = p.config (Classical.choose ex) := by
    simp only [Pattern.mulShift, dif_pos hmem]
  -- the chosen witness equals w by left-cancellation
  have hwv' : v * Classical.choose ex = v * w := (Classical.choose_spec ex).2
  have h_eq : Classical.choose ex = w := mul_left_cancel hwv'
  rw [h1, h_eq]

/-- Shifting a configuration commutes with occurrences of a pattern.

Formally: a pattern `p` occurs in the shifted configuration `mulShift h x` at
position `g` if and only if it occurs in the original configuration `x` at
position `g * h`. -/
@[to_additive occursInAt_shift
/-- Shifting a configuration commutes with occurrences of a pattern.

Formally: a pattern `p` occurs in the shifted configuration `shift h x` at
position `g` if and only if it occurs in the original configuration `x` at
position `g + h`. -/]
lemma mulOccursInAt_mulShift {A G : Type*} [Inhabited A] [Monoid G]
    (p : Pattern A G) (x : G → A) (g h : G) :
    p.mulOccursInAt (mulShift g x) h ↔ p.mulOccursInAt x (g * h) := by
  simp only [Pattern.mulOccursInAt, mulShift_apply, mul_assoc]

/-- Configurations that avoid a family `F` of patterns are stable under the shift.

Formally: if `x` avoids every `p ∈ F` at every position, then for any `h : G`,
the shifted configuration `mulShift h x` also avoids every `p ∈ F` at every position. -/
@[to_additive mapsTo_shift_forbidden
  /-- Configurations that avoid a family `F` of patterns are stable under the shift.

Formally: if `x` avoids every `p ∈ F` at every position, then for any `h : G`,
the shifted configuration `shift h x` also avoids every `p ∈ F` at every position. -/]
lemma mapsTo_mulShift_mulForbidden {A G : Type*} [Inhabited A] [Monoid G]
    (F : Set (Pattern A G)) (h : G) :
    Set.MapsTo (mulShift h) (mulForbidden (A := A) (G := G) F) (mulForbidden F) := by
  -- unfold `MapsTo`
  intro x hx p hp g
  specialize hx p hp (h * g)
  contrapose! hx
  simpa [mulOccursInAt_mulShift] using hx

end Pattern

open scoped Classical in
/-- We call *occurrence set* for pattern `p` and position `g` the set of configurations
in which a pattern `p` occurs at position `g`.

This proves that it is exactly the cylinder corresponding to the
pattern obtained by translating `p` by `g`.

Equivalently, `p.mulOccursInAt x g` iff on every translated site
`g * w` (with `w ∈ p.support`)
the configuration `x` agrees with the translated pattern `Pattern.mulShift p g`.

(This uses `[IsLeftCancelMul G]` to identify the preimage along left-multiplication by `g`.) -/
@[to_additive occursInAt_eq_cylinder
  /-- We call *occurrence set* for pattern `p` and position `g` the set of configurations
in which a pattern `p` occurs at position `g`.

This proves that it is exactly the cylinder corresponding to the
pattern obtained by translating `p` by `g`.

Equivalently, `p.occursInAt x g` iff on every translated site `g + w` (with `w ∈ p.support`)
the configuration `x` agrees with the translated pattern `Pattern.shift p g`.

(This uses `[IsLeftCancelMul G]` to identify the preimage along left-multiplication by `g`.) -/]
lemma mulOccursInAt_eq_cylinder [IsLeftCancelMul G]
    (p : Pattern A G) (g : G) :
    { x | p.mulOccursInAt x g } = cylinder (p.mulShift g).support (p.mulShift g).config := by
  ext x; constructor
  · -- ⇒: from an occurrence, get membership in the cylinder
    intro H u hu
    change u ∈ p.support.image (g * ·) at hu
    rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
    -- want: x (g * w) = (p.mulShift g).config (g * w)
    have hx : x (g * w) = p.config w := H w hw
    simpa [Pattern.mulShift_config_apply_mul_left_of_mem (p := p) (v := g) (w := w) hw] using hx
  · -- ⇐: from the cylinder, recover an occurrence
    intro H u hu
    -- H gives equality with the translated pattern on the image
    have hx : x (g * u) = (p.mulShift g).config (g * u) :=
      H (g * u) (Finset.mem_image_of_mem (g * ·) hu)
    -- rewrite the RHS by the “apply_of_mem” lemma
    simpa [Pattern.mulShift_config_apply_mul_left_of_mem (p := p) (v := g) (w := u) hu] using hx
end OccursInAt

/-! ## Forbidden sets and subshifts -/

section DefSubshiftByForbidden

variable {A : Type*} [TopologicalSpace A] [Inhabited A]
variable {G : Type*} [Monoid G] [IsLeftCancelMul G]

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
  have h_eq : {x | ∀ p ∈ F, ∀ v : G, ¬ p.mulOccursInAt x v}
    = ⋂ (p : Pattern A G) (hp : p ∈ F) (v : G), {x | ¬ p.mulOccursInAt x v} := by ext; simp
  rw [h_eq]
  -- Now prove that this big intersection is closed.
  refine isClosed_iInter (fun p => ?_)
  refine isClosed_iInter (fun hp => ?_)
  refine isClosed_iInter (fun v => ?_)
  -- For each `p, hp, v`, the section is the complement of an open occurrence set.
  have : {x | ¬ p.mulOccursInAt x v} = {x | p.mulOccursInAt x v}ᶜ := by ext; simp
  simpa [this, isClosed_compl_iff] using isOpen_mulOccursInAt (A := A) (G := G) p v

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

end DefSubshiftByForbidden

section Language

variable {A : Type*} [Fintype A] [Inhabited A]
variable {G : Type*}

/-- Patterns with support exactly `U` form a finite set. -/
lemma finite_setOf_pattern_support_eq
    {A G : Type*} [Finite A] [Inhabited A]
    (U : Finset G) :
    ({p : Pattern A G | p.support = U}).Finite := by
  -- 1. Upgrade Finite A to Fintype A locally
  cases nonempty_fintype A
  classical
  -- Patterns with support U biject with (U → A) via restriction/extension
  let e : { p : Pattern A G // p.support = U } ≃ (U → A) :=
  { toFun := fun p i => p.1.config i.1
    invFun := fun f => ⟨{ config := fun g => if h : g ∈ U then f ⟨g, h⟩ else default,
                           support := U,
                           condition := fun g hg => by simp [hg] }, rfl⟩
    left_inv := by
      rintro ⟨⟨cfg, dom, cond⟩, hU⟩
      simp only at hU; subst hU
      apply Subtype.ext
      simp only [Pattern.mk.injEq, and_true]
      funext g
      by_cases hg : g ∈ dom
      · simp [hg]
      · simp [hg, cond g hg]
    right_inv := fun f => by ext i; simp [i.2] }
  let : Fintype { p : Pattern A G | p.support = U } := Fintype.ofEquiv (U → A) e.symm
  apply toFinite

/-- The language of a set of configurations `X` on a finite shape `U`.

This is the set of all finite patterns obtained by restricting some configuration
`x ∈ X` to `U`. -/
def LanguageOn (X : Set (G → A)) (U : Finset G) : Set (Pattern A G) :=
  { p | ∃ x ∈ X, Pattern.fromConfig x U = p }

/-- The language of a subshift `Y` on a finite shape `U`. -/
def MulSubshift.languageOn {A G} [TopologicalSpace A] [Inhabited A] [Monoid G]
    (Y : MulSubshift A G) (U : Finset G) : Set (Pattern A G) :=
  SymbolicDynamics.FullShift.LanguageOn (A := A) (G := G) Y.carrier U

end Language

/-! ## Shift-invariance of the language of a subshift -/

section PatternMulShifted

variable {A : Type*} [Inhabited A]
variable {G : Type*}

namespace Pattern

/-- Pattern extensionality: two patterns are equal iff their supports agree and
their configurations agree on the support. (Values outside the support are
forced to `default` by `Pattern.condition`.) -/
@[ext]
theorem ext {p q : Pattern A G}
    (hsup : p.support = q.support)
    (hcfg : ∀ g ∈ p.support, p.config g = q.config g) : p = q := by
  obtain ⟨pc, ps, pcond⟩ := p
  obtain ⟨qc, qs, qcond⟩ := q
  cases hsup
  have hc : pc = qc := by
    funext g
    by_cases hg : g ∈ ps
    · exact hcfg g hg
    · rw [pcond g hg, qcond g hg]
  cases hc
  rfl

@[simp] lemma fromConfig_support (x : G → A) (U : Finset G) :
    (Pattern.fromConfig x U).support = U := rfl

/-- The value of `Pattern.fromConfig x U` on a point g of the support is `x g`. -/
@[simp] lemma fromConfig_config_of_mem
    (x : G → A) {U : Finset G} {g : G} (hg : g ∈ U) : (Pattern.fromConfig x U).config g = x g := by
  classical
  change (if g ∈ U then x g else default) = x g
  rw [if_pos hg]

end Pattern

end PatternMulShifted

section LanguageMulShift

variable {A : Type*} [Inhabited A]
variable {G : Type*} [Monoid G] [IsLeftCancelMul G]

namespace Pattern

open scoped Classical in
/-- Naturality of `Pattern.fromConfig` with respect to the shift action.

Restricting `x` to a finite shape `U` and then shifting the resulting pattern by `g` agrees
with restricting the shifted configuration `mulShift g' x` to the translated shape
`U.image (g * ·)`, where `g'` is a left inverse of `g`. -/
lemma fromConfig_mulShift
    (x : G → A) (U : Finset G) (g g' : G) (hg'g : g' * g = 1) :
    (Pattern.fromConfig x U).mulShift g = Pattern.fromConfig (mulShift g' x) (U.image (g * ·)) := by
  refine Pattern.ext rfl ?_
  intro h hh
  change h ∈ U.image (g * ·) at hh
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hh
  rw [Pattern.mulShift_config_apply_mul_left_of_mem _ g u hu,
      Pattern.fromConfig_config_of_mem _ hu,
      Pattern.fromConfig_config_of_mem _ (Finset.mem_image_of_mem (g * ·) hu),
      mulShift_apply, ← mul_assoc, hg'g, one_mul]

end Pattern

open scoped Classical in
/-- **Shift-invariance of the language of a subshift on a shape.**

For a subshift `Y` over a monoid `G`, and elements `g, g' : G` with `g * g' = 1`
and `g' * g = 1`, the language on a translated shape `U.image (g * ·)` is exactly
the image of `Y.languageOn U` under the pattern-shift map `p ↦ p.mulShift g`. In
particular `Y.languageOn U` and `Y.languageOn (U.image (g * ·))` are in natural
bijection (with inverse given by `p ↦ p.mulShift g'`). -/
theorem MulSubshift.languageOn_image_mulShift [TopologicalSpace A]
    (Y : MulSubshift A G) (U : Finset G) (g g' : G)
    (hgg' : g * g' = 1) (hg'g : g' * g = 1) :
    (fun p : Pattern A G => p.mulShift g) '' Y.languageOn U = Y.languageOn (U.image (g * ·)) := by
  ext q
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨mulShift g' x, Y.mapsTo g' hx,
           (Pattern.fromConfig_mulShift x U g g' hg'g).symm⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨Pattern.fromConfig (mulShift g y) U,
            ⟨mulShift g y, Y.mapsTo g hy, rfl⟩, ?_⟩
    change (Pattern.fromConfig (mulShift g y) U).mulShift g
         = Pattern.fromConfig y (U.image (g * ·))
    rw [Pattern.fromConfig_mulShift (g' := g') (hg'g := hg'g), ← mulShift_mul,
        hgg', mulShift_one]

end LanguageMulShift

end FullShift

end SymbolicDynamics
