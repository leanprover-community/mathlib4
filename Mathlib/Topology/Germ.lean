/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Order.Filter.Germ
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Topology.NhdsSet
import Mathlib.Topology.LocallyConstant.Basic

/-! # Germs of functions between topological spaces

In this file, we prove basic properties of germs of functions between topological spaces,
with respect to the neighbourhood filter `𝓝 x`.

## Main definitions and results
* `Filter.Germ.value φ f`: value associated to the germ `φ` at a point `x`, w.r.t. the neighbourhood
filter at `x`. This is the common value of all representatives of `φ` at `x`.
* `Filter.Germ.valueOrderRingHom` and friends: the map `Germ (𝓝 x) E → E` is a
monoid homomorphism, 𝕜-module homomorphism, ring homomorphism, monotone ring homeomorphism

* `RestrictGermPredicate`: given a predicate on germs `P : Π x : X, germ (𝓝 x) Y → Prop` and
`A : set X`, build a new predicate on germs `restrict_germ_predicate P A` such that
`(∀ x, restrict_germ_predicate P A x f) ↔ ∀ᶠ x near A, P x f`;
`forall_restrict_germ_predicate_iff` is this equivalence.

* `Filter.Germ.sliceLeft,sliceRight`: map the germ of functions `X × Y → Z` at `p=(x,y) ∈ X × Y` to
the corresponding germ of functions `X → Z` at `x ∈ X` resp. `Y → Z` at `y ∈ Y`..
* `eq_of_germ_isConstant`: if each germ of `f : X → Y` is constant and `X` is pre-connected,
`f` is constant.
-/

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

open scoped Topology

open Filter Set

variable {X Y Z : Type*} [TopologicalSpace X] {f g : X → Y} {A : Set X} {x : X}

namespace Filter.Germ

/-- The value associated to a germ at a point. This is the common value
shared by all representatives at the given point. -/
def value {X α : Type*} [TopologicalSpace X] {x : X} (φ : Germ (𝓝 x) α) : α :=
  Quotient.liftOn' φ (fun f ↦ f x) fun f g h ↦ by dsimp only; rw [Eventually.self_of_nhds h]

theorem value_smul {α β : Type*} [SMul α β] (φ : Germ (𝓝 x) α)
    (ψ : Germ (𝓝 x) β) : (φ • ψ).value = φ.value • ψ.value :=
  Germ.inductionOn φ fun _ ↦ Germ.inductionOn ψ fun _ ↦ rfl

/-- The map `Germ (𝓝 x) E → E` as a monoid homeomorphism -/
@[to_additive "The map `Germ (𝓝 x) E → E` as an additive monoid homeomorphism"]
def valueMulHom {X E : Type*} [Monoid E] [TopologicalSpace X] {x : X} : Germ (𝓝 x) E →* E where
  toFun := Filter.Germ.value
  map_one' := rfl
  map_mul' φ ψ := Germ.inductionOn φ fun _ ↦ Germ.inductionOn ψ fun _ ↦ rfl

/-- The map `Germ (𝓝 x) E → E` into a `𝕜`-module `E` as a `𝕜`-linear map -/
def valueₗ {X 𝕜 E : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace X]
    {x : X} : Germ (𝓝 x) E →ₗ[𝕜] E :=
  { Filter.Germ.valueAddHom with map_smul' := fun _ φ ↦ Germ.inductionOn φ fun _ ↦ rfl }

/-- The map `Germ (𝓝 x) E → E` as a ring homeomorphism -/
def valueRingHom {X E : Type*} [Semiring E] [TopologicalSpace X] {x : X} : Germ (𝓝 x) E →+* E :=
  { Filter.Germ.valueMulHom, Filter.Germ.valueAddHom with }

/-- The map `Germ (𝓝 x) E → E` as a monotone ring homeomorphism -/
def valueOrderRingHom {X E : Type*} [OrderedSemiring E] [TopologicalSpace X] {x : X} :
    Germ (𝓝 x) E →+*o E where
  __ := Filter.Germ.valueRingHom
  monotone' := fun φ ψ ↦
  Germ.inductionOn φ fun _ ↦ Germ.inductionOn ψ fun _ h ↦ h.self_of_nhds

end Filter.Germ

/-- The inclusion `S → R` of a subring, as an ordered ring homomorphism. -/
-- xxx: OrderedRing has no morphisms, OrderedRingHom no subtypes -> which file is a good place?
def _root_.Subring.orderedSubtype {R} [OrderedRing R] (s : Subring R) : s →+*o R :=
  { s.subtype with monotone' := fun _ _ h ↦ h }

section RestrictGermPredicate
/-- Given a predicate on germs `P : Π x : X, germ (𝓝 x) Y → Prop` and `A : set X`,
build a new predicate on germs `restrict_germ_predicate P A` such that
`(∀ x, restrict_germ_predicate P A x f) ↔ ∀ᶠ x near A, P x f`, see
`forall_restrict_germ_predicate_iff` for this equivalence. -/
def RestrictGermPredicate (P : ∀ x : X, Germ (𝓝 x) Y → Prop)
    (A : Set X) : ∀ x : X, Germ (𝓝 x) Y → Prop := fun x φ ↦
  Germ.liftOn φ (fun f ↦ x ∈ A → ∀ᶠ y in 𝓝 x, P y f)
    haveI : ∀ f f' : X → Y, f =ᶠ[𝓝 x] f' → (∀ᶠ y in 𝓝 x, P y f) → ∀ᶠ y in 𝓝 x, P y f' := by
      intro f f' hff' hf
      apply (hf.and <| Eventually.eventually_nhds hff').mono
      rintro y ⟨hy, hy'⟩
      rwa [Germ.coe_eq.mpr (EventuallyEq.symm hy')]
    fun f f' hff' ↦ propext <| forall_congr' fun _ ↦ ⟨this f f' hff', this f' f hff'.symm⟩

theorem Filter.Eventually.germ_congr_set
    {P : ∀ x : X, Germ (𝓝 x) Y → Prop} (hf : ∀ᶠ x in 𝓝ˢ A, P x f)
    (h : ∀ᶠ z in 𝓝ˢ A, g z = f z) : ∀ᶠ x in 𝓝ˢ A, P x g := by
  rw [eventually_nhdsSet_iff_forall] at *
  intro x hx
  apply ((hf x hx).and (h x hx).eventually_nhds).mono
  intro y hy
  convert hy.1 using 1
  exact Germ.coe_eq.mpr hy.2

theorem restrictGermPredicate_congr {P : ∀ x : X, Germ (𝓝 x) Y → Prop}
    (hf : RestrictGermPredicate P A x f) (h : ∀ᶠ z in 𝓝ˢ A, g z = f z) :
    RestrictGermPredicate P A x g := by
  intro hx
  apply ((hf hx).and <| (eventually_nhdsSet_iff_forall.mp h x hx).eventually_nhds).mono
  rintro y ⟨hy, h'y⟩
  rwa [Germ.coe_eq.mpr h'y]

theorem forall_restrictGermPredicate_iff {P : ∀ x : X, Germ (𝓝 x) Y → Prop} :
    (∀ x, RestrictGermPredicate P A x f) ↔ ∀ᶠ x in 𝓝ˢ A, P x f := by
  rw [eventually_nhdsSet_iff_forall]
  rfl

theorem forall_restrictGermPredicate_of_forall
    {P : ∀ x : X, Germ (𝓝 x) Y → Prop} (h : ∀ x, P x f) :
    ∀ x, RestrictGermPredicate P A x f :=
  forall_restrictGermPredicate_iff.mpr (eventually_of_forall h)
end RestrictGermPredicate

namespace Filter.Germ
/-- Map the germ at of functions `X × Y → Z` at `p=(x,y) ∈ X × Y` to the corresponding germ
  of functions `X → Z` at `x ∈ X` -/
def sliceLeft [TopologicalSpace Y] {p : X × Y} (P : Germ (𝓝 p) Z) : Germ (𝓝 p.1) Z :=
  P.compTendsto (Prod.mk · p.2) (Continuous.Prod.mk_left p.2).continuousAt

@[simp]
theorem sliceLeft_coe [TopologicalSpace Y] {y : Y} (f : X × Y → Z) :
    (↑f : Germ (𝓝 (x, y)) Z).sliceLeft = fun x' ↦ f (x', y) :=
  rfl

/-- Map the germ at of functions `X × Y → Z` at `p=(x,y) ∈ X × Y` to the corresponding germ
  of functions `Y → Z` at `y ∈ Y` -/
def sliceRight [TopologicalSpace Y] {p : X × Y} (P : Germ (𝓝 p) Z) : Germ (𝓝 p.2) Z :=
  P.compTendsto (Prod.mk p.1) (Continuous.Prod.mk p.1).continuousAt

@[simp]
theorem sliceRight_coe [TopologicalSpace Y] {y : Y} (f : X × Y → Z) :
    (↑f : Germ (𝓝 (x, y)) Z).sliceRight = fun y' ↦ f (x, y') :=
  rfl

end Filter.Germ

/-- If the germ of `f` w.r.t. each `𝓝 x` is constant, `f` is locally constant. -/
private lemma IsLocallyConstant.of_germ_isConstant (h : ∀ x : X, (f : Germ (𝓝 x) Y).IsConstant) :
    IsLocallyConstant f := by
  intro s
  rw [isOpen_iff_mem_nhds]
  intro a ha
  obtain ⟨b, hb⟩ := h a
  apply mem_of_superset hb
  intro x hx
  have : f x = f a := (mem_of_mem_nhds hb) ▸ hx
  rw [mem_preimage, this]
  exact ha

-- should follow from `isConstant_compTendsto` specialised to the neigbourhood filter
proof_wanted isConstant_comp_subtype {s : Set X} {f : X → Y} {x : s}
  (_hf : (f : Germ (𝓝 (x : X)) Y).IsConstant) :
    ((f ∘ Subtype.val : s → Y) : Germ (𝓝 x) Y).IsConstant

-- move to `LocallyConstant/Basic.lean` once proven
proof_wanted IsLocallyConstant.of_comp_of_inducing
  {f : X → Y} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {i : Z → X} (_hi : Inducing i) (_hF : IsLocallyConstant (f ∘ i)) : IsLocallyConstant f

-- use previous lemma: `Subtype.val` is inducing
proof_wanted IsLocallyConstant.of_germ_isConstantOn_of_preconnected {s : Set X} [TopologicalSpace Y]
    (_hs : IsPreconnected s) (_h : ∀ x ∈ s, (f : Germ (𝓝 x) Y).IsConstant) : IsLocallyConstant f

theorem eq_of_germ_isConstant [i: PreconnectedSpace X]
    (h : ∀ x : X, (f : Germ (𝓝 x) Y).IsConstant) (x x' : X) : f x = f x' :=
  (IsLocallyConstant.of_germ_isConstant h).apply_eq_of_isPreconnected
    (preconnectedSpace_iff_univ.mp i) (by trivial) (by trivial)

-- use `IsLocallyConstant.of_germ_isConstantOn_of_preconnected`
proof_wanted eq_of_germ_isConstant_on {s : Set X} (_h : ∀ x ∈ s, (f : Germ (𝓝 x) Y).IsConstant)
    (_hs : IsPreconnected s) {x' : X} (_x_in : x ∈ s) (_x'_in : x' ∈ s) : f x = f x'

open scoped BigOperators in
@[to_additive (attr := simp)]
theorem Germ.coe_prod {α : Type*} (l : Filter α) (R : Type*) [CommMonoid R] {ι} (f : ι → α → R)
    (s : Finset ι) : ((∏ i in s, f i : α → R) : Germ l R) = ∏ i in s, (f i : Germ l R) :=
  map_prod (Germ.coeMulHom l : (α → R) →* Germ l R) f s
