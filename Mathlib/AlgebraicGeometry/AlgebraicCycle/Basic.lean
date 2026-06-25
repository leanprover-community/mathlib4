/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.LocallyFinsupp.Pushforward
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Algebraic Cycles

In this file we define algebraic cycles on a scheme `X` with coefficients in a type `R` and provide
some basic API for working with them. We define an algebraic cycle on a scheme `X` with
coefficients in a type `R` to be functions `c : X → R` whose support is locally finite.

## Implementation notes

Here we're making use of the equivalence between irreducible closed subsets of a scheme and their
generic points in order to reuse the API in `Function.locallyFinsupp`, hence the slightly
nonstandard definition.
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory Set Function

universe u v
variable {X Y : Scheme.{u}} {R : Type*}

/--
Algebraic cycle on a scheme `X` with coefficients in a type `Z` is just a function from `X` to `Z`
with locally finite support.
(see the module docstring for more details).
-/
@[stacks 02QR]
abbrev AlgebraicCycle (X : Scheme.{u}) (R : Type*) [Zero R] :=
    Function.locallyFinsupp X R

variable (f : X ⟶ Y)

namespace AlgebraicCycle
section restrict

variable [Zero R] (D : AlgebraicCycle X R) (t : Set X)
/--
Restriction of an algebraic cycle to some set. This is distinct from `Function.locallyFinsuppWithin`
because here we get something which is still just a locally finsupp function on the whole space.
-/
noncomputable
def restrict : AlgebraicCycle X R where
  toFun z := by
    classical
    exact if z ∈ t then D z else 0
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' := by
    intro z hz
    obtain ⟨U, hU⟩ := D.supportLocallyFiniteWithinDomain z hz
    use U, hU.1
    apply Finite.subset hU.2
    apply inter_subset_inter (Subset.refl U)
    simp

open Classical in
lemma restrict_apply (z : X) : D.restrict t z = if z ∈ t then D z else 0 := rfl

@[simp]
lemma restrict_eq_of_mem (z : X) (hz : z ∈ t) :
    D.restrict t z = D z := dif_pos hz

@[simp]
lemma restrict_eq_zero_of_not_mem (z : X) (hz : z ∉ t) :
    D.restrict t z = 0 := dif_neg hz

lemma restrict_eqOn : Set.EqOn (D.restrict t) D t := by
  intro _ _
  simp_all

lemma restrict_eqOn_compl : Set.EqOn (D.restrict t) 0 tᶜ := by
  intro _ hx
  simp_all

@[simp]
lemma restrict_eq_zero_of_eq_zero {z : X} (hD : D z = 0) : (D.restrict t) z = 0 := by
  by_cases o : z ∈ t <;> simp_all

@[simp]
lemma restrict_support : (D.restrict t).support = D.support ∩ t := by
  ext z
  simp [restrict, And.comm]

@[simp]
lemma restrict_univ {X : Scheme.{u}} {R : Type*} [Zero R] {D : AlgebraicCycle X R} :
    D.restrict univ = D := by
  ext z
  simp

end restrict

variable [Semiring R] (c : AlgebraicCycle X R)
/--
Implementation detail for `AlgebraicCycle.map`: function used to define the coefficient of the
pushforward of a cycle `c` at a point `z = f x`, as in stacks `02R3`.
-/
noncomputable
def mapAux {N : Type*} [DecidableEq N] {Y : Scheme} (f : X ⟶ Y) (wx : X → N) (wy : Y → N) (x : X) :
    ℕ := if wx x = wy (f.base x) then f.residueDegree x else 0

/--
The pushforward of algebraic cycles with respect to a quasicompact morphism of schemes. The
arguments `wx` and `wy` are gradings of the algebraic cycle, which is necessary information for the
function determining how to adjust the coefficients of the cycle. Typically in
applications these will be some notions of dimension or codimension. The most common notion of
dimension is `Order.height`, and the most common notion of codimension is `Order.coheight`, though
more sophisticated notions exist in the literature which are useful when sufficient
equidimensionality hypotheses cannot be assumed.
-/
@[stacks 02R3]
noncomputable
def map [QuasiCompact f] {N : Type*} [DecidableEq N]
    (wx : X → N) (wy : Y → N) (c : AlgebraicCycle X R) : AlgebraicCycle Y R :=
  Function.locallyFinsupp.map f (Nat.cast (R := R) <| mapAux f wx wy ·) f.isSpectralMap c

lemma map_apply [QuasiCompact f] {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N)
    (c : AlgebraicCycle X R) (y : Y) :
  map f wx wy c y = ∑ᶠ x ∈ f ⁻¹' {y}, c x * (Nat.cast (R := R) <| mapAux f wx wy x) := rfl

@[simp]
lemma map_id {N : Type*} [DecidableEq N] (wx : X → N) (c : AlgebraicCycle X R) :
    map (𝟙 _) wx wx c = c := by
  apply Function.locallyFinsupp.map_id
  simp [mapAux]

@[ext]
lemma ext {R : Type*} [Zero R] {D₁ D₂ : AlgebraicCycle X R}
    (h : ∀ a ∈ D₁.support ∪ D₂.support, D₁ a = D₂ a) : D₁ = D₂ :=
  have h' : ∀ a, D₁ a = D₂ a := by
    intro a
    by_cases o : a ∈ D₁.support ∪ D₂.support
    · exact h a o
    simp_all
  DFunLike.ext _ _ h'

lemma le_iff_of_support_subset {R : Type*} [Zero R] [Preorder R] {D₁ D₂ : AlgebraicCycle X R}
    {t : Set X} (hD₁ : D₁.support ⊆ t) (hD₂ : ∀ z ∈ tᶜ, D₂ z ≥ 0) :
    D₁ ≤ D₂ ↔ ∀ z ∈ t, D₁ z ≤ D₂ z := by
  peel with z
  refine ⟨by tauto, fun m ↦ ?_⟩
  by_cases o : z ∈ t
  · exact m o
  simp only [support_subset_iff, ne_eq] at hD₁
  specialize hD₁ z
  by_cases p : D₁ z = 0
  · simp_all
  specialize hD₁ p
  contradiction

end AlgebraicGeometry.AlgebraicCycle
