/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FunProp

#align_import topology.basic from "leanprover-community/mathlib"@"e354e865255654389cc46e6032160238df2e0f40"
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

universe u v
open Set

/-- A topology on `X`. -/
@[to_additive existing TopologicalSpace]
class TopologicalSpace (X : Type u) where
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
#align topological_space TopologicalSpace

variable {X : Type u} {Y : Type v}

/-! ### Predicates on sets -/

section Defs

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

/-- `IsOpen s` means that `s` is open in the ambient topological space on `X` -/
def IsOpen : Set X → Prop := TopologicalSpace.IsOpen
#align is_open IsOpen

@[simp] theorem isOpen_univ : IsOpen (univ : Set X) := TopologicalSpace.isOpen_univ
#align is_open_univ isOpen_univ

theorem IsOpen.inter (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) :=
  TopologicalSpace.isOpen_inter s t hs ht
#align is_open.inter IsOpen.inter

theorem isOpen_sUnion {s : Set (Set X)} (h : ∀ t ∈ s, IsOpen t) : IsOpen (⋃₀ s) :=
  TopologicalSpace.isOpen_sUnion s h
#align is_open_sUnion isOpen_sUnion

/-- A set is closed if its complement is open -/
class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ
#align is_closed IsClosed

/-- A set is clopen if it is both closed and open. -/
def IsClopen (s : Set X) : Prop :=
  IsClosed s ∧ IsOpen s
#align is_clopen IsClopen

/-- The interior of a set `s` is the largest open subset of `s`. -/
def interior (s : Set X) : Set X :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }
#align interior interior

/-- The closure of `s` is the smallest closed set containing `s`. -/
def closure (s : Set X) : Set X :=
  ⋂₀ { t | IsClosed t ∧ s ⊆ t }
#align closure closure

/-- The frontier of a set is the set of points between the closure and interior. -/
def frontier (s : Set X) : Set X :=
  closure s \ interior s
#align frontier frontier

/-- A set is dense in a topological space if every point belongs to its closure. -/
def Dense (s : Set X) : Prop :=
  ∀ x, x ∈ closure s
#align dense Dense

/-- `f : α → X` has dense range if its range (image) is a dense subset of `X`. -/
def DenseRange {α : Type*} (f : α → X) := Dense (range f)
#align dense_range DenseRange

/-- A function between topological spaces is continuous if the preimage
  of every open set is open. Registered as a structure to make sure it is not unfolded by Lean. -/
@[fun_prop]
structure Continuous (f : X → Y) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
#align continuous Continuous

/-- A map `f : X → Y` is said to be an *open map*,
if the image of any open `U : Set X` is open in `Y`. -/
def IsOpenMap (f : X → Y) : Prop := ∀ U : Set X, IsOpen U → IsOpen (f '' U)
#align is_open_map IsOpenMap

/-- A map `f : X → Y` is said to be a *closed map*,
if the image of any closed `U : Set X` is closed in `Y`. -/
def IsClosedMap (f : X → Y) : Prop := ∀ U : Set X, IsClosed U → IsClosed (f '' U)
#align is_closed_map IsClosedMap

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
#align baire_space BaireSpace
