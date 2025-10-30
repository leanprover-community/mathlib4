/-
Copyright (c) 2025 Silvère Gangloff. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Silvère Gangloff
-/
import Mathlib.Topology.Constructions

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
`patternToConfig` (which extends a pattern into a configuration
using the default value of `A`) without using inverses,
so that the theory works not only for groups but also for cancellative monoids.

## Main definitions

* `mulShift g x` — right translation: in additive notation `(shift v x) u = x (u + v)`;
          multiplicative notation `(mulShift g x) h = x (h * g)`.
* `cylinder U x` — configurations agreeing with `x` on a finite set `U ⊆ G`.
* `pattern A G` — finite support together with values on that support.
* `pattern.occursIn p x g` — occurrence of `p` in `x` at translate `g`.
* `forbids F` — configurations avoiding every pattern in `F`.
* `subshift A G` — closed, shift-invariant subsets of the full shift.
* `subshft_from_forbidden F` — the subshift defined by forbidding a family of patterns.
* `subshift_of_finite_type F` — a subshift of finite type defined by a finite set of
forbidden patterns.
* `languageOn X U` — the set of patterns of shape `U` obtained by restricting some `x ∈ X`.

## Conventions

We use a **right** action of `G` on configurations:
`(shift v x) u = x (u + v)`.
In multiplicative notation:
`(mulShift g x) h = x (h * g)`.

## Design choice: ambient vs. inner (subshift-relative) viewpoint

All core notions (shift, cylinder, occurrence, language, …) are defined **in the
ambient full shift** `G → A`. A subshift is then a closed, invariant subset,
bundled as `subshift A G`. Working inside a subshift is done by restriction.

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
For `Y : subshift A G`, cylinders and occurrence sets *inside `Y`* are simply
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

/-- The **right-translation shift** on configurations.

We call *configuration* an element of `G → A`.

Given a configuration `x : G → A` and an element `g : G` of the group, the shifted configuration
`mulShift g x` is defined by `(mulShift g x) h = x (h * g)`.

Intuitively, this moves the whole configuration "in the direction of `g`": the value
at position `h` in the shifted configuration is the value that was at position
`h * g` in the original one.

For example, if `G = ℤ` (with addition) and `A = {0, 1}`, then
`shift 1 x` is the sequence obtained from `x` by shifting every symbol one
step to the left. -/
@[to_additive /-- The **right-translation shift** on configurations, in additive notation.

We call *configuration* an element of `G → A`.

Given a configuration `x : G → A` and an element `g : G` of the multiplicative group,
the shifted configuration `shift g x` is defined by `(shift g x) h = x (h + g)`.

Intuitively, this moves the whole configuration "in the direction of `g`": the value
at position `h` in the shifted configuration is the value that was at position
`h + g` in the original one.

For example, if `G = ℤ` and `A = {0,1}`, then
`shift 1 x` is the sequence obtained from `x` by shifting every symbol one
step to the left. -/]
def mulShift (g : G) (x : G → A) : G → A :=
  fun h => x (h * g)

@[to_additive] lemma mulShift_apply (g h : G) (x : G → A) :
  mulShift g x h = x (h * g) := rfl

@[to_additive] lemma mulShift_one (x : G → A) : mulShift (1 : G) x = x := by
  ext h; simp [mulShift]

/-- Composition of right-translation shifts corresponds to multiplication in the group. -/
lemma mulShift_mul (g₁ g₂ : G) (x : G → A) :
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
leaving all other coordinates free. For example, in the full shift `{0,1}^ℤ`,
the cylinder determined by `U = {0,1}` and `x 0 = 1, x 1 = 0` consists of all
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
  ext y; simp [cylinder, Set.pi, Finset.mem_coe]

lemma mem_cylinder {U : Finset G} {x y : G → A} :
    y ∈ cylinder U x ↔ ∀ i ∈ U, y i = x i := Iff.rfl

variable [TopologicalSpace A] [DiscreteTopology A]

/-- Cylinders are open when `A` is discrete. -/
lemma isOpen_cylinder (U : Finset G) (x : G → A) :
    IsOpen (cylinder U x) := by
  simpa [cylinder_eq_set_pi U x] using isOpen_set_pi (U.finite_toSet) (by simp)

/-- Cylinders are closed when `A` is discrete. -/
lemma isClosed_cylinder (U : Finset G) (x : G → A) :
    IsClosed (cylinder U x) := by
  simpa [cylinder_eq_set_pi U x] using isClosed_set_pi (by simp)

end Cylinders

/-! ## Patterns and occurrences -/


section SubshiftDef
variable (A : Type*) [TopologicalSpace A]
variable (G : Type*) [AddMonoid G]

/-- A *subshift* on alphabet A is a closed, shift-invariant subset of `G → A`. Formally, it is
composed of:
* `carrier`: the underlying set of allowed configurations.
* `isClosed`: the set is topologically closed in `A^G`.
* `shiftInvariant`: the set is invariant under all right-translation shifts
  `(shift g)`. -/
structure subshift : Type _ where
  /-- The underlying set of configurations (additive group version). -/
  carrier : Set (G → A)
  /-- Closedness of `carrier`. -/
  isClosed : IsClosed carrier
  /-- Shift invariance of `carrier` for the additive shift `shift`. -/
  shiftInvariant : ∀ g : G, ∀ x ∈ carrier, shift g x ∈ carrier

end SubshiftDef

section MulSubshiftDef
variable (A : Type*) [TopologicalSpace A]
variable (G : Type*) [Monoid G]

/-- Multiplicative version of the definition of subshift. -/
structure mulSubshift : Type _ where
  /-- The underlying set of configurations. -/
  carrier : Set (G → A)
  /-- Closedness of `carrier`. -/
  isClosed : IsClosed carrier
  /-- Shift invariance of `carrier`. -/
  shiftInvariant : ∀ g : G, ∀ x ∈ carrier, mulShift g x ∈ carrier

end MulSubshiftDef


attribute [to_additive existing]
  SymbolicDynamics.FullShift.mulSubshift


/-- Example: the **full shift** on alphabet `A` over the multiplicative monoid `G`.

It is the subshift whose underlying set is the set of all configurations
`G → A`.
-/
@[to_additive SymbolicDynamics.FullShift.fullShift
/-- Example: the **full shift** on alphabet `A` over the additive monoid `G`.

It is the subshift whose underlying set is the set of all configurations
`G → A`.
-/]
def mulFullShift (A G) [TopologicalSpace A] [Monoid G] : mulSubshift A G where
  carrier := Set.univ
  isClosed := isClosed_univ
  shiftInvariant := by
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
structure mulPattern (A : Type*) (G : Type*) [Monoid G] where
  /-- Finite support of the pattern. -/
  support : Finset G
  /-- The value (symbol) at each point of the support. -/
  data : support → A

/-- Additive version of `Pattern`. -/
structure pattern (A : Type*) (G : Type*) [AddMonoid G] : Type _ where
  /-- Finite support of the pattern (subset of `G`). -/
  support : Finset G
  /-- The symbol at each point of the support. -/
  data : support → A

attribute [to_additive existing SymbolicDynamics.FullShift.pattern]
  SymbolicDynamics.FullShift.mulPattern

section Dominos

variable (G : Type*) [Monoid G] [DecidableEq G]

/-- A *domino* is a pattern supported on exactly two positions (sometimes
also called cells) `{i, j}`, specifying the value `ai` at `i` and the value `aj` at `j`.

In symbolic dynamics, dominos (two-cell patterns) are the simplest nontrivial
building blocks: they describe local adjacency conditions between two sites
of a configuration. -/
@[to_additive domino]
def mulDomino {A : Type*} (i j : G) (ai aj : A) : mulPattern A G where
  support := ({i, j} : Finset G)
  data := fun ⟨z, _hz⟩ => if z = i then ai else aj

attribute [inherit_doc SymbolicDynamics.FullShift.mulDomino] SymbolicDynamics.FullShift.domino

end Dominos

section Forbids

variable {A : Type*}
variable {G : Type*}
variable [Monoid G]

/-- `p.occursIn x g` means that the finite pattern `p` appears in the configuration `x`
at position `g`.

Formally: for every position `h` in the support of `p`, the value of the configuration
at `h * g` coincides with the value specified by `p` at `h`.

Intuitively, if you shift the configuration `x` by `g` (using `mulShift g`),
then on the support of `p` you exactly recover the pattern `p`. This is the basic
notion of "pattern occurrence" used to define subshifts via forbidden patterns. -/
@[to_additive
/-- `p.occursIn x g` means that the finite pattern `p` appears in the configuration `x`
at position `g`.

Formally: for every position `h` in the support of `p`, the value of the configuration
at `h + g` coincides with the value specified by `p` at `h`.

Intuitively, if you shift the configuration `x` by `g` (using `shift g`),
then on the support of `p` you exactly recover the pattern `p`. This is the basic
notion of "pattern occurrence" used to define subshifts via forbidden patterns. -/]
def mulPattern.occursIn (p : mulPattern A G) (x : G → A) (g : G) : Prop :=
  ∀ (h) (hh : h ∈ p.support), x (h * g) = p.data ⟨h, hh⟩

/-- `forbids F` is the set of configurations that avoid every pattern in `F`.

Formally: `x ∈ forbids F` if and only if for every pattern `p ∈ F` and every
group element `g : G`, the pattern `p` does not occur in `x` at position `g`.

Intuitively, `forbids F` is the shift space defined by declaring the finite set
(or family) of patterns `F` to be *forbidden*. A configuration belongs to the subshift if and only
it avoids all the forbidden patterns. -/
@[to_additive forbids]
def mulForbids (F : Set (mulPattern A G)) : Set (G → A) :=
  { x | ∀ p ∈ F, ∀ g : G, ¬ p.occursIn x g }

attribute [inherit_doc SymbolicDynamics.FullShift.mulForbids] SymbolicDynamics.FullShift.forbids

/-- Shifting a configuration commutes with occurrences of a pattern.

Formally: a pattern `p` occurs in the shifted configuration `mulShift h x` at
position `g` if and only if it occurs in the original configuration `x` at
position `g + h`. -/
@[to_additive occurs_shift
/-- Shifting a configuration commutes with occurrences of a pattern.

Formally: a pattern `p` occurs in the shifted configuration `shift h x` at
position `g` if and only if it occurs in the original configuration `x` at
position `g + h`. -/]
lemma mulOccurs_mulShift (p : mulPattern A G) (x : G → A) (g h : G) :
    p.occursIn (mulShift h x) g ↔ p.occursIn x (g * h) := by
  constructor <;> intro H u hu <;> simpa [mulShift, mul_assoc] using H u hu

/-- Configurations that avoid a family `F` of patterns are stable under the shift.

Formally: if `x` avoids every `p ∈ F` at every position, then for any `h : G`,
the shifted configuration `mulShift h x` also avoids every `p ∈ F` at every position. -/
@[to_additive forbids_shift_invariant
  /-- Configurations that avoid a family `F` of patterns are stable under the shift.

Formally: if `x` avoids every `p ∈ F` at every position, then for any `h : G`,
the shifted configuration `shift h x` also avoids every `p ∈ F` at every position. -/]
lemma mulForbids_shift_invariant (F : Set (mulPattern A G)) :
    ∀ h : G, ∀ x ∈ mulForbids (A := A) (G := G) F, mulShift h x ∈ mulForbids F := by
  intro h x hx p hp g
  specialize hx p hp (g * h)
  -- contraposition
  contrapose! hx
  simpa [mulOccurs_mulShift] using hx

end Forbids

section OccursAt

variable {A : Type*} [Inhabited A]
variable {G : Type*}
-- We assume right-cancellation throughout this section for uniqueness of preimages under (_ + v).
variable [Monoid G] [IsRightCancelMul G] [DecidableEq G]

/-- Turn a finite pattern into a configuration, by extending it with
the default symbol outside its support.

Formally: given a pattern `p` with finite support in `G`, we define a configuration
`patternToOriginConfig p : G → A` by setting
* `patternToOriginConfig p i = p.data ⟨i, h⟩` if `i ∈ p.support`,
* `patternToOriginConfig p i = default` otherwise.

This produces a canonical "completion" of the pattern to a configuration,
filling all unspecified positions with `default`. -/
@[to_additive patternToOriginConfig]
def mulPatternToOriginConfig (p : mulPattern A G) : G → A :=
  fun i ↦ if h : i ∈ p.support then p.data ⟨i, h⟩ else default

attribute [inherit_doc SymbolicDynamics.FullShift.mulPatternToOriginConfig]
  SymbolicDynamics.FullShift.patternToOriginConfig

/-- Translate a finite pattern `p` so that it occurs at the translate `v`, before completing into
a configuration.

On input `h : G`, we proceed as follows:
* if `h` lies in the right-translate of the support, i.e. `h ∈ p.support.image (· * v)`,
  choose (noncomputably) `w ∈ p.support` with `w * v = h` and return `p.data ⟨w, _⟩`;
* otherwise return `default`.

This definition does not assume right-cancellation; it only *chooses* a preimage.
Uniqueness (and the usual equations such as `mulPatternToConfig p v (w * v) = p.data ⟨w, _⟩`)
require a right-cancellation hypothesis and are proved in separate lemmas.
-/
@[to_additive patternToConfig
/-- Translate a finite pattern `p` so that it occurs at the translate `v`, before completing into
a configuration.

On input `h : G`, we proceed as follows:
* if `h` lies in the right-translate of the support, i.e. `h ∈ p.support.image (· + v)`,
  choose (noncomputably) `w ∈ p.support` with `w + v = h` and return `p.data ⟨w, _⟩`;
* otherwise return `default`.

This definition does not assume right-cancellation; it only *chooses* a preimage.
Uniqueness (and the usual equations such as `patternToConfig p v (w + v) = p.data ⟨w, _⟩`)
require a right-cancellation hypothesis and are proved in separate lemmas.
-/]
noncomputable def mulPatternToConfig (p : mulPattern A G) (v : G) : G → A :=
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

/-- Extract the finite pattern given by restricting a configuration `x : G → A`
to a finite subset `U : Finset G`.

Formally: the support is `U`, and for each `i ∈ U` the pattern records the value
`x i`. In other words, `mulPatternFromConfig x U` is the partial configuration of
`x` visible on the coordinates in `U`.

This is the inverse construction to `mulPatternToOriginConfig` (which extends a
finite pattern to a configuration by filling with `default`). -/
@[to_additive patternFromConfig
/-- Extract the finite pattern given by restricting a configuration `x : G → A`
to a finite subset `U : Finset G`.

Formally: the support is `U`, and for each `i ∈ U` the pattern records the value
`x i`. In other words, `patternFromConfig x U` is the partial configuration of
`x` visible on the coordinates in `U`.

This is the inverse construction to `patternToOriginConfig` (which extends a
finite pattern to a configuration by filling with `default`). -/]
def mulPatternFromConfig (x : G → A) (U : Finset G) : mulPattern A G where
  support := U
  data := fun i => x i.1

/-- On the translated support, `mulPatternToConfig p v` agrees with `p` at the preimage.

More precisely, if `w ∈ p.support`, then at the translated site `w * v`,
the configuration `mulPatternToConfig p v` takes the value prescribed by `p` at `w`.

This statement uses `[IsRightCancelMul G]` to identify the preimage of `w * v`
under right-multiplication by `v`. -/
@[to_additive patternToConfig_apply_of_mem
  /-- On the translated support, `patternToConfig p v` agrees with `p` at the preimage.

More precisely, if `w ∈ p.support`, then at the translated site `w + v`,
the configuration `patternToConfig p v` takes the value prescribed by `p` at `w`.

This statement uses `[IsRightCancelMul G]` to identify the preimage of `w + v`
under right-multiplication by `v`. -/]
lemma mulPatternToConfig_apply_of_mem
    (p : mulPattern A G) (v w : G) (hw : w ∈ p.support) :
    mulPatternToConfig (A := A) (G := G) p v (w * v) = p.data ⟨w, hw⟩ := by
  -- (w*v) is in the translated support
  have hmem : (w * v) ∈ p.support.image (· * v) :=
    Finset.mem_image.mpr ⟨w, hw, rfl⟩
  -- existential used in the branch
  have ex : ∃ w', w' ∈ p.support ∧ w' * v = w * v := by
    simpa [Finset.mem_image] using hmem
  -- open the `if` branch as returned by the definition
  have h1 :
      mulPatternToConfig (A := A) (G := G) p v (w * v)
        = p.data ⟨Classical.choose ex, (Classical.choose_spec ex).1⟩ := by
    simp [mulPatternToConfig, hmem]
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
    mulPatternToConfig (A := A) (G := G) p v (w * v)
        = p.data ⟨Classical.choose ex, (Classical.choose_spec ex).1⟩ := h1
    _   = p.data ⟨w, hw_w⟩ := by
            -- push h2 through `p.data`
            simpa using
              (congrArg (fun z : {x // x ∈ p.support} => p.data z) h2)
    _   = p.data ⟨w, hw⟩ := by
            -- push h3 through `p.data`
            simp [h3]

/-- We call *occurrence set* for pattern `p` and position `g` the set of configurations
in which a pattern `p` occurs at position `g`.

This proves that it is exactly the cylinder corresponding to the
pattern obtained by translating `p` by `g`.

Equivalently, `p.OccursIn x g` iff on every translated site `w * g` (with `w ∈ p.support`)
the configuration `x` agrees with the translated pattern `mulpatternToConfig p g`.

(This uses `[IsRightCancelMul G]` to identify the preimage along right-multiplication by `g`.) -/
@[to_additive occursAt_eq_cylinder
  /-- We call *occurrence set* for pattern `p` and position `g` the set of configurations
in which a pattern `p` occurs at position `g`.

This proves that it is exactly the cylinder corresponding to the
pattern obtained by translating `p` by `g`.

Equivalently, `p.occursIn x g` iff on every translated site `w + g` (with `w ∈ p.support`)
the configuration `x` agrees with the translated pattern `patternToConfig p g`.

(This uses `[IsRightCancelMul G]` to identify the preimage along right-multiplication by `g`.) -/]
lemma mulOccursAt_eq_cylinder
    (p : mulPattern A G) (g : G) :
    { x | p.occursIn x g } = cylinder (p.support.image (· * g)) (mulPatternToConfig p g) := by
  ext x; constructor
  · -- ⇒: from an occurrence, get membership in the cylinder
    intro H u hu
    rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
    -- want: x (w*g) = patternToConfig p g (w*g)
    have hx : x (w * g) = p.data ⟨w, hw⟩ := H w hw
    simpa [mulPatternToConfig_apply_of_mem (p := p) (v := g) (w := w) hw] using hx
  · -- ⇐: from the cylinder, recover an occurrence
    intro H u hu
    -- H gives equality with the translated pattern on the image
    have hx : x (u * g) = mulPatternToConfig p g (u * g) :=
      H (u * g) (Finset.mem_image_of_mem (· * g) hu)
    -- rewrite the RHS by the “apply_of_mem” lemma
    simpa [mulPatternToConfig_apply_of_mem (p := p) (v := g) (w := u) hu] using hx

end OccursAt

/-! ## Forbidden sets and subshifts -/

section DefSubshiftByForbidden

variable {A G : Type*} [Monoid G] [IsRightCancelMul G] [TopologicalSpace A] [DiscreteTopology A]
           [Inhabited A] [DecidableEq G]

/-- Occurrence sets are open. -/
@[to_additive occursAt_open]
lemma mulOccursAt_open (p : mulPattern A G) (g : G) :
    IsOpen { x | p.occursIn x g } := by
  simpa [mulOccursAt_eq_cylinder] using isOpen_cylinder _ _

/-- Avoiding a fixed family of patterns is a closed condition (in the product topology on `G → A`).

Since each occurrence set `{ x | p.occursIn x v }` is open (when `A` is discrete),
its complement `{ x | ¬ p.occursIn x v }` is closed; `forbids F` is the intersection
of these closed sets over `p ∈ F` and `v ∈ G`. -/
@[to_additive forbids_closed]
lemma mulForbids_closed (F : Set (mulPattern A G)) :
    IsClosed (mulForbids F) := by
  rw [mulForbids]
  have : {x | ∀ p ∈ F, ∀ v : G, ¬ p.occursIn x v}
       = ⋂ (p : mulPattern A G) (h : p ∈ F), ⋂ (v : G), {x | ¬ p.occursIn x v} := by
    ext x; simp
  rw [this]
  refine isClosed_iInter ?_;
  intro p; refine isClosed_iInter ?_;
  intro _; refine isClosed_iInter ?_;
  intro v; have : {x | ¬p.occursIn x v} = {x | p.occursIn x v}ᶜ := by ext x; simp
  simpa [this, isClosed_compl_iff] using mulOccursAt_open p v

/-- Occurrence sets are closed. -/
@[to_additive occursAt_closed]
lemma mulOccursAt_closed (p : mulPattern A G) (g : G) :
    IsClosed { x | p.occursIn x g } := by
  simpa [mulOccursAt_eq_cylinder] using isClosed_cylinder _ _

/-- The subshift defined by a family of forbidden patterns `F`.

This is a standard way to construct subshifts:
`subshift_from_forbidden F` consists of all configurations `x : G → A` in which no pattern
`p ∈ F` occurs at any position.

Formally:
* the carrier is `forbids F` (configurations avoiding `F`),
* it is closed because each occurrence set is open, and
* it is shift-invariant since avoidance is preserved by shifts. -/
@[to_additive]
def mulSubshift_from_forbidden (F : Set (mulPattern A G)) : mulSubshift A G where
  carrier := mulForbids F
  isClosed := mulForbids_closed F
  shiftInvariant := mulForbids_shift_invariant F

attribute [inherit_doc SymbolicDynamics.FullShift.mulSubshift_from_forbidden]
  SymbolicDynamics.FullShift.subshift_from_forbidden

/-- A subshift of finite type (SFT) is a subshift defined by forbidding
a *finite* family of patterns.

Formally, `subshift_of_finite_type F` is `subshift_from_forbidden F` where `F` is a
`Finset (pattern A G)`. -/
@[to_additive]
def mulSubshift_of_finite_type (F : Finset (mulPattern A G)) : mulSubshift A G :=
  mulSubshift_from_forbidden (F : Set (mulPattern A G))

attribute [inherit_doc SymbolicDynamics.FullShift.mulSubshift_of_finite_type]
  SymbolicDynamics.FullShift.subshift_of_finite_type

end DefSubshiftByForbidden

section Language

variable {A : Type*} [Fintype A]
variable {G : Type*}
variable [TopologicalSpace A]
variable [Monoid G]

/-- The set of patterns with fixed support `U`. -/
@[to_additive fixedSupport]
def mulFixedSupport (A : Type*) (G : Type*) [Monoid G] (U : Finset G) :=
  { p : mulPattern A G // p.support = U }

attribute [inherit_doc SymbolicDynamics.FullShift.mulFixedSupport]
  SymbolicDynamics.FullShift.fixedSupport

/-- An equivalence between patterns with fixed support and functions on that support.

Concretely, `fixedSupport A G U` is the subtype of patterns whose support is
exactly `U`. Such a pattern is determined uniquely by its values on `U`,
i.e. by a function `U → A`. This equivalence makes that identification precise:

* `toFun` sends a fixed-support pattern to the function recording its values,
* `invFun` rebuilds the pattern from a function on `U`.

This shows immediately that `fixedSupport A G U` is finite whenever `U` is. -/
@[to_additive equivFun
  /-- Additive version: equivalence between fixed-support additive patterns and functions. -/]
def mulEquivFun {U : Finset G} :
  mulFixedSupport A G U ≃ (U → A) where
  toFun   := fun p i => p.1.data ⟨i.1, by simp [p.2]⟩
  invFun  := fun f => ⟨{ support := U, data := f }, rfl⟩
  left_inv := by rintro ⟨p,hU⟩; apply Subtype.ext; cases hU; rfl
  right_inv := by intro f; rfl

/-- `fixedSupport A G U` is a finite type: there are only finitely many patterns
with support exactly `U`. This follows from the equivalence with functions `U → A`. -/
@[to_additive SymbolicDynamics.FullShift.fintypeFixedSupport] noncomputable
instance mulFintypeFixedSupport {U : Finset G} :
    Fintype (mulFixedSupport A G U) := by
  classical exact Fintype.ofEquiv (U → A) (mulEquivFun (A := A) (G := G) (U := U)).symm

/-- The language of a set of configurations `X` on a finite shape `U`.

This is the set of all finite patterns obtained by restricting some configuration
`x ∈ X` to `U`. -/
@[to_additive languageOn]
def mulLanguageOn (X : Set (G → A)) (U : Finset G) : Set (mulPattern A G) :=
  { p | ∃ x ∈ X, mulPatternFromConfig x U = p }

attribute [inherit_doc SymbolicDynamics.FullShift.mulLanguageOn]
  SymbolicDynamics.FullShift.languageOn


/-- The cardinality of the language of `X` on a finite set `U`.

That is, the number of distinct patterns supported on `U` which appear
in some configuration of `X`. Since `U` is finite, this is a finite number. -/
@[to_additive languageCardOn]
noncomputable def mulLanguageCardOn (X : Set (G → A)) (U : Finset G) : ℕ := by
  -- Image of a map into the finite type `FixedSupport A G U`
  let f : {x : G → A // x ∈ X} → mulFixedSupport A G U :=
    fun x => ⟨mulPatternFromConfig x.1 U, rfl⟩
  have hfin : (Set.range f).Finite := (Set.finite_univ :
    (Set.univ : Set (mulFixedSupport A G U)).Finite)
    |>.subset (by intro y hy; simp)
  exact hfin.toFinset.card

attribute [inherit_doc SymbolicDynamics.FullShift.mulLanguageCardOn]
  SymbolicDynamics.FullShift.languageCardOn

/-- The number of patterns which appear in the configurations of the carrier
of a subshift `Y` on a finite set `U`. -/
@[to_additive patternCountOn]
noncomputable def mulPatternCountOn (Y : mulSubshift A G) (U : Finset G) : ℕ :=
  mulLanguageCardOn (A := A) (G := G) Y.carrier U

attribute [inherit_doc SymbolicDynamics.FullShift.mulPatternCountOn]
  SymbolicDynamics.FullShift.patternCountOn

end Language

end FullShift

end SymbolicDynamics
