import Mathlib.Order.Filter.Lift
import Mathlib.Topology.Defs.Filter

open scoped Topology

universe u
variable {X : Type u} [TopologicalSpace X]

/--
`SeparatedNhds` is a predicate on pairs of sub`Set`s of a topological space.  It holds if the two
sub`Set`s are contained in disjoint open sets.
-/
def SeparatedNhds (s t : Set X) : Prop :=
  ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ s ⊆ U ∧ t ⊆ V ∧ Disjoint U V

/-- A T₀ space, also known as a Kolmogorov space, is a topological space such that for every pair
`x ≠ y`, there is an open set containing one but not the other. We formulate the definition in terms
of the `Inseparable` relation. -/
class T0Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Two inseparable points in a T₀ space are equal. -/
  t0 : ∀ ⦃x y : X⦄, Inseparable x y → x = y

theorem Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x y) : x = y :=
  T0Space.t0 h

/-- A topological space is called an R₀ space, if `Specializes` relation is symmetric.

In other words, given two points `x y : X`,
if every neighborhood of `y` contains `x`, then every neighborhood of `x` contains `y`. -/
@[mk_iff]
class R0Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- In an R₀ space, the `Specializes` relation is symmetric. -/
  specializes_symmetric : Symmetric (Specializes : X → X → Prop)

export R0Space (specializes_symmetric)

/-- A T₁ space, also known as a Fréchet space, is a topological space
  where every singleton set is closed. Equivalently, for every pair
  `x ≠ y`, there is an open set containing `x` and not `y`. -/
class T1Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- A singleton in a T₁ space is a closed set. -/
  t1 : ∀ x, IsClosed ({x} : Set X)

theorem isClosed_singleton [T1Space X] {x : X} : IsClosed ({x} : Set X) :=
  T1Space.t1 x

/-- A topological space is called a *preregular* (a.k.a. R₁) space,
if any two topologically distinguishable points have disjoint neighbourhoods. -/
@[mk_iff r1Space_iff_specializes_or_disjoint_nhds]
class R1Space (X : Type*) [TopologicalSpace X] : Prop where
  specializes_or_disjoint_nhds (x y : X) : Specializes x y ∨ Disjoint (𝓝 x) (𝓝 y)

export R1Space (specializes_or_disjoint_nhds)

/-- A T₂ space, also known as a Hausdorff space, is one in which for every
  `x ≠ y` there exists disjoint open sets around `x` and `y`. This is
  the most widely used of the separation axioms. -/
@[mk_iff]
class T2Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Every two points in a Hausdorff space admit disjoint open neighbourhoods. -/
  t2 : Pairwise fun x y => ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v

/-- Two different points can be separated by open sets. -/
theorem t2_separation [T2Space X] {x y : X} (h : x ≠ y) :
    ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v :=
  T2Space.t2 h

/-- A topological space is called a *regular space* if for any closed set `s` and `a ∉ s`, there
exist disjoint open sets `U ⊇ s` and `V ∋ a`. We formulate this condition in terms of `Disjoint`ness
of filters `𝓝ˢ s` and `𝓝 a`. -/
@[mk_iff]
class RegularSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- If `a` is a point that does not belong to a closed set `s`, then `a` and `s` admit disjoint
  neighborhoods. -/
  regular : ∀ {s : Set X} {a}, IsClosed s → a ∉ s → Disjoint (𝓝ˢ s) (𝓝 a)

/-- A T₂.₅ space, also known as a Urysohn space, is a topological space
  where for every pair `x ≠ y`, there are two open sets, with the intersection of closures
  empty, one containing `x` and the other `y` . -/
class T25Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Given two distinct points in a T₂.₅ space, their filters of closed neighborhoods are
  disjoint. -/
  t2_5 : ∀ ⦃x y : X⦄, x ≠ y → Disjoint ((𝓝 x).lift' closure) ((𝓝 y).lift' closure)

/-- A T₃ space is a T₀ space which is a regular space. Any T₃ space is a T₁ space, a T₂ space, and
a T₂.₅ space. -/
class T3Space (X : Type u) [TopologicalSpace X] extends T0Space X, RegularSpace X : Prop

instance (priority := 90) instT3Space [T0Space X] [RegularSpace X] : T3Space X := ⟨⟩

/-- A topological space is said to be a *normal space* if any two disjoint closed sets
have disjoint open neighborhoods. -/
class NormalSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- Two disjoint sets in a normal space admit disjoint neighbourhoods. -/
  normal : ∀ s t : Set X, IsClosed s → IsClosed t → Disjoint s t → SeparatedNhds s t

/-- A T₄ space is a normal T₁ space. -/
class T4Space (X : Type u) [TopologicalSpace X] extends T1Space X, NormalSpace X : Prop

instance (priority := 100) [T1Space X] [NormalSpace X] : T4Space X := ⟨⟩

/-- A topological space `X` is a *completely normal space* provided that for any two sets `s`, `t`
such that if both `closure s` is disjoint with `t`, and `s` is disjoint with `closure t`,
then there exist disjoint neighbourhoods of `s` and `t`. -/
class CompletelyNormalSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- If `closure s` is disjoint with `t`, and `s` is disjoint with `closure t`, then `s` and `t`
  admit disjoint neighbourhoods. -/
  completely_normal :
    ∀ ⦃s t : Set X⦄, Disjoint (closure s) t → Disjoint s (closure t) → Disjoint (𝓝ˢ s) (𝓝ˢ t)

export CompletelyNormalSpace (completely_normal)

/-- A T₅ space is a completely normal T₁ space. -/
class T5Space (X : Type u) [TopologicalSpace X] extends T1Space X, CompletelyNormalSpace X : Prop
