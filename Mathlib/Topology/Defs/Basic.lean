/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.MkIffOfInductiveProp
import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.IrreducibleDef

/-!
# Basic definitions about topological spaces

This file contains definitions about topology that do not require imports
other than `Mathlib.Data.Set.Lattice`.

## Main definitions

* `TopologicalSpace X`: a typeclass endowing `X` with a topology.
  By definition, a topology is a collection of sets called *open sets* such that

  - `isOpen_univ`: the whole space is open;
  - `IsOpen.inter`: the intersection of two open sets is an open set;
  - `isOpen_sUnion`: the union of a family of open sets is an open set.

* `IsOpen s`: predicate saying that `s` is an open set, same as `TopologicalSpace.IsOpen`.

* `IsClosed s`: a set is called *closed*, if its complement is an open set.
  For technical reasons, this is a typeclass.

* `IsClopen s`: a set is *clopen* if it is both closed and open.

* `interior s`: the *interior* of a set `s` is the maximal open set that is included in `s`.

* `closure s`: the *closure* of a set `s` is the minimal closed set that includes `s`.

* `frontier s`: the *frontier* of a set is the set difference `closure s \ interior s`.
  A point `x` belongs to `frontier s`, if any neighborhood of `x`
  contains points both from `s` and `sᶜ`.

* `Dense s`: a set is *dense* if its closure is the whole space.
  We define it as `∀ x, x ∈ closure s` so that one can write `(h : Dense s) x`.

* `DenseRange f`: a function has *dense range*, if `Set.range f` is a dense set.

* `Continuous f`: a map is *continuous*, if the preimage of any open set is an open set.

* `IsOpenMap f`: a map is an *open map*, if the image of any open set is an open set.

* `IsClosedMap f`: a map is a *closed map*, if the image of any closed set is a closed set.

** Notation

We introduce notation `IsOpen[t]`, `IsClosed[t]`, `closure[t]`, `Continuous[t₁, t₂]`
that allow passing custom topologies to these predicates and functions without using `@`.
-/

assert_not_exists Monoid

universe u v
open Set

/-- An auxiliary class towards a topological space structure on `X`. *Do not use.*
For forgetful inheritance reasons, we will endow each topological space with an atlas to itself
made only of the identity. To build up this `TopologicalSpace` class, we need the current class
as an auxiliary device. -/
@[to_additive existing TopologicalSpaceWithoutAtlas]
class TopologicalSpaceWithoutAtlas (X : Type u) where
  /-- A predicate saying that a set is an open set. Use `IsOpen` in the root namespace instead. -/
  protected IsOpen : Set X → Prop
  /-- The set representing the whole space is an open set.
  Use `isOpen_univ` in the root namespace instead. -/
  protected isOpen_univ : IsOpen univ
  /-- The intersection of two open sets is an open set. Use `IsOpen.inter` instead. -/
  protected isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  /-- The union of a family of open sets is an open set.
  Use `isOpen_sUnion` in the root namespace instead. -/
  protected isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)

variable {X : Type u} {Y : Type v}

/-! ### Setting up an atlas definition as quickly as possible -/

section Atlas

variable [TopologicalSpaceWithoutAtlas X] [TopologicalSpaceWithoutAtlas Y] {s t : Set X}

open Filter

/-- Temporary neighborhood definition, before setting up topological spaces. *Do not use*.
Use instead `nhds`. -/
irreducible_def nhdsWithoutAtlas (x : X) : Filter X :=
  ⨅ s ∈ { s : Set X | x ∈ s ∧ TopologicalSpaceWithoutAtlas.IsOpen s }, 𝓟 s

variable (X Y) in
/-- Partial homeomorphisms, defined on open subsets of the space -/
structure PartialHomeomorph extends PartialEquiv X Y where
  open_source' : TopologicalSpaceWithoutAtlas.IsOpen source
  open_target' : TopologicalSpaceWithoutAtlas.IsOpen target
  /-- `toFun` is continuous on `source`, written by hand as the definitions have not been given. -/
  continuousOn_toFun : ∀ x ∈ source, Tendsto toFun (nhdsWithoutAtlas x ⊓ 𝓟 source)
    (nhdsWithoutAtlas (toFun x))
  /-- `invFun` is continuous on `target`, written by hand as the definitions have not been given. -/
  continuousOn_invFun : ∀ x ∈ target, Tendsto invFun (nhdsWithoutAtlas x ⊓ 𝓟 target)
    (nhdsWithoutAtlas (invFun x))

open Filter in
variable (X) in
/-- The identity on the whole space as a partial homeomorphism. -/
protected def PartialHomeomorph.refl : PartialHomeomorph X X :=
  { PartialEquiv.refl X with
    open_source' := TopologicalSpaceWithoutAtlas.isOpen_univ
    open_target' := TopologicalSpaceWithoutAtlas.isOpen_univ
    continuousOn_toFun := by
      intro x hx
      simp only [Tendsto, map, PartialEquiv.refl_coe, preimage_id_eq,
        PartialEquiv.refl_source, id_eq, le_def, Filter.mem_mk, Filter.mem_sets]
      intro s hs
      exact ⟨s, hs, univ, by simp, by simp⟩
    continuousOn_invFun := by
      intro x hx
      simp only [Tendsto, map, PartialEquiv.refl_coe, preimage_id_eq,
        PartialEquiv.refl_source, id_eq, le_def, Filter.mem_mk, Filter.mem_sets]
      intro s hs
      exact ⟨s, hs, univ, by simp, by simp⟩ }

/-- A charted space is a topological space endowed with an atlas, i.e., a set of local
homeomorphisms taking value in a model space `H`, called charts, such that the domains of the charts
cover the whole space. We express the covering property by choosing for each `x` a member
`chartAt x` of the atlas containing `x` in its source: in the smooth case, this is convenient to
construct the tangent bundle in an efficient way.
The model space is written as an explicit parameter as there can be several model spaces for a
given topological space. For instance, a complex manifold (modelled over `ℂ^n`) will also be seen
sometimes as a real manifold over `ℝ^(2n)`.
-/
@[ext]
class ChartedSpace (H : Type*) [TopologicalSpaceWithoutAtlas H]
    (M : Type*) [TopologicalSpaceWithoutAtlas M] where
  /-- The atlas of charts in the `ChartedSpace`. -/
  protected atlas : Set (PartialHomeomorph M H)
  /-- The preferred chart at each point in the charted space. -/
  protected chartAt : M → PartialHomeomorph M H
  protected mem_chart_source : ∀ x, x ∈ (chartAt x).source
  protected chart_mem_atlas : ∀ x, chartAt x ∈ atlas

/-- Any space is a `ChartedSpace` modelled over itself, by just using the identity chart. We do
*not* register this as an instance, as for product spaces we rather want to use the product charted
space as the default. We will instead embed in the definition of a topological space
a charted space structure which is propositionally equal to this one. -/
def chartedSpaceSelfId (H : Type*) [TopologicalSpaceWithoutAtlas H] : ChartedSpace H H where
  atlas := {PartialHomeomorph.refl H}
  chartAt _ := PartialHomeomorph.refl H
  mem_chart_source x := Set.mem_univ x
  chart_mem_atlas _ := Set.mem_singleton _

/-- A topology on `X`.

We include the data of an atlas on `X` made only of the identity map, to avoid diamond problems
when defining the product of two manifolds.
-/
@[to_additive existing TopologicalSpace]
class TopologicalSpace (X : Type u) extends TopologicalSpaceWithoutAtlas X where
  chartedSpaceSelf : ChartedSpace X X := chartedSpaceSelfId X
  chartedSpaceSelf_eq_id : chartedSpaceSelf = chartedSpaceSelfId X := by rfl

end Atlas

/-! ### Predicates on sets -/

section Defs

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

/-- `IsOpen s` means that `s` is open in the ambient topological space on `X` -/
def IsOpen : Set X → Prop := TopologicalSpaceWithoutAtlas.IsOpen

@[simp] theorem isOpen_univ : IsOpen (univ : Set X) := TopologicalSpaceWithoutAtlas.isOpen_univ

theorem IsOpen.inter (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) :=
  TopologicalSpaceWithoutAtlas.isOpen_inter s t hs ht

theorem isOpen_sUnion {s : Set (Set X)} (h : ∀ t ∈ s, IsOpen t) : IsOpen (⋃₀ s) :=
  TopologicalSpaceWithoutAtlas.isOpen_sUnion s h

@[simp] theorem TopologicalSpaceWithoutAtlas.isOpen_iff :
    TopologicalSpaceWithoutAtlas.IsOpen s ↔ IsOpen s := Iff.rfl

/-- A set is closed if its complement is open -/
class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ

/-- A set is clopen if it is both closed and open. -/
def IsClopen (s : Set X) : Prop :=
  IsClosed s ∧ IsOpen s

/--
A set is locally closed if it is the intersection of some open set and some closed set.
Also see `isLocallyClosed_tfae` and other lemmas in `Mathlib/Topology/LocallyClosed.lean`.
-/
def IsLocallyClosed (s : Set X) : Prop := ∃ (U Z : Set X), IsOpen U ∧ IsClosed Z ∧ s = U ∩ Z

/-- The interior of a set `s` is the largest open subset of `s`. -/
def interior (s : Set X) : Set X :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }

/-- The closure of `s` is the smallest closed set containing `s`. -/
def closure (s : Set X) : Set X :=
  ⋂₀ { t | IsClosed t ∧ s ⊆ t }

/-- The frontier of a set is the set of points between the closure and interior. -/
def frontier (s : Set X) : Set X :=
  closure s \ interior s

/--
The coborder is defined as the complement of `closure s \ s`,
or the union of `s` and the complement of `∂(s)`.
This is the largest set in which `s` is closed, and `s` is locally closed if and only if
`coborder s` is open.

This is unnamed in the literature, and this name is due to the fact that `coborder s = (border sᶜ)ᶜ`
where `border s = s \ interior s` is the border in the sense of Hausdorff.
-/
def coborder (s : Set X) : Set X :=
  (closure s \ s)ᶜ

/-- A set is dense in a topological space if every point belongs to its closure. -/
def Dense (s : Set X) : Prop :=
  ∀ x, x ∈ closure s

/-- `f : α → X` has dense range if its range (image) is a dense subset of `X`. -/
def DenseRange {α : Type*} (f : α → X) := Dense (range f)

/-- A function between topological spaces is continuous if the preimage
  of every open set is open. Registered as a structure to make sure it is not unfolded by Lean. -/
@[fun_prop]
structure Continuous (f : X → Y) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)

/-- A map `f : X → Y` is said to be an *open map*,
if the image of any open `U : Set X` is open in `Y`. -/
def IsOpenMap (f : X → Y) : Prop := ∀ U : Set X, IsOpen U → IsOpen (f '' U)

/-- A map `f : X → Y` is said to be a *closed map*,
if the image of any closed `U : Set X` is closed in `Y`. -/
def IsClosedMap (f : X → Y) : Prop := ∀ U : Set X, IsClosed U → IsClosed (f '' U)

/-- An open quotient map is an open map `f : X → Y` which is both an open map and a quotient map.
Equivalently, it is a surjective continuous open map.
We use the latter characterization as a definition.

Many important quotient maps are open quotient maps, including

- the quotient map from a topological space to its quotient by the action of a group;
- the quotient map from a topological group to its quotient by a normal subgroup;
- the quotient map from a topological spaace to its separation quotient.

Contrary to general quotient maps,
the category of open quotient maps is closed under `Prod.map`.
-/
@[mk_iff]
structure IsOpenQuotientMap (f : X → Y) : Prop where
  /-- An open quotient map is surjective. -/
  surjective : Function.Surjective f
  /-- An open quotient map is continuous. -/
  continuous : Continuous f
  /-- An open quotient map is an open map. -/
  isOpenMap : IsOpenMap f

end Defs

/-! ### Notation for non-standard topologies -/

/-- Notation for `IsOpen` with respect to a non-standard topology. -/
scoped[Topology] notation (name := IsOpen_of) "IsOpen[" t "]" => @IsOpen _ t

/-- Notation for `IsClosed` with respect to a non-standard topology. -/
scoped[Topology] notation (name := IsClosed_of) "IsClosed[" t "]" => @IsClosed _ t

/-- Notation for `closure` with respect to a non-standard topology. -/
scoped[Topology] notation (name := closure_of) "closure[" t "]" => @closure _ t

/-- Notation for `Continuous` with respect to a non-standard topologies. -/
scoped[Topology] notation (name := Continuous_of) "Continuous[" t₁ ", " t₂ "]" =>
  @Continuous _ _ t₁ t₂

/-- The property `BaireSpace α` means that the topological space `α` has the Baire property:
any countable intersection of open dense subsets is dense.
Formulated here when the source space is ℕ.
Use `dense_iInter_of_isOpen` which works for any countable index type instead. -/
class BaireSpace (X : Type*) [TopologicalSpace X] : Prop where
  baire_property : ∀ f : ℕ → Set X, (∀ n, IsOpen (f n)) → (∀ n, Dense (f n)) → Dense (⋂ n, f n)
