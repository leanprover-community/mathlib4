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

/-! ## Additional lemmas about germs of functions

TODO: add a module docstring, eventually
-/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

open scoped Topology

open Filter Set

namespace Filter.Germ

/-- The value associated to a germ at a point. This is the common value
shared by all representatives at the given point. -/
def value {X α : Type*} [TopologicalSpace X] {x : X} (φ : Germ (𝓝 x) α) : α :=
  Quotient.liftOn' φ (fun f => f x) fun f g h => by dsimp only; rw [Eventually.self_of_nhds h]

theorem value_smul {X α β : Type*} [TopologicalSpace X] {x : X} [SMul α β] (φ : Germ (𝓝 x) α)
    (ψ : Germ (𝓝 x) β) : (φ • ψ).value = φ.value • ψ.value :=
  Germ.inductionOn φ fun _ => Germ.inductionOn ψ fun _ => rfl

@[to_additive]
def valueMulHom {X E : Type*} [Monoid E] [TopologicalSpace X] {x : X} : Germ (𝓝 x) E →* E
    where
  toFun := Filter.Germ.value
  map_one' := rfl
  map_mul' φ ψ := Germ.inductionOn φ fun _ => Germ.inductionOn ψ fun _ => rfl

def valueₗ {X 𝕜 E : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace X]
    {x : X} : Germ (𝓝 x) E →ₗ[𝕜] E :=
  { Filter.Germ.valueAddHom with map_smul' := fun _ φ => Germ.inductionOn φ fun _ => rfl }

def valueRingHom {X E : Type*} [Semiring E] [TopologicalSpace X] {x : X} : Germ (𝓝 x) E →+* E :=
  { Filter.Germ.valueMulHom, Filter.Germ.valueAddHom with }

def valueOrderRingHom {X E : Type*} [OrderedSemiring E] [TopologicalSpace X] {x : X} :
    Germ (𝓝 x) E →+*o E :=
  { Filter.Germ.valueRingHom with
    monotone' := fun φ ψ =>
      Germ.inductionOn φ fun _ => Germ.inductionOn ψ fun _ h => h.self_of_nhds }

def _root_.Subring.orderedSubtype {R} [OrderedRing R] (s : Subring R) : s →+*o R :=
  { s.subtype with monotone' := fun _ _ h => h }

end Filter.Germ

/-- Given a predicate on germs `P : Π x : X, germ (𝓝 x) Y → Prop` and `A : set X`,
build a new predicate on germs `restrict_germ_predicate P A` such that
`(∀ x, restrict_germ_predicate P A x f) ↔ ∀ᶠ x near A, P x f`, see
`forall_restrict_germ_predicate_iff` for this equivalence. -/
def RestrictGermPredicate {X Y : Type*} [TopologicalSpace X] (P : ∀ x : X, Germ (𝓝 x) Y → Prop)
    (A : Set X) : ∀ x : X, Germ (𝓝 x) Y → Prop := fun x φ =>
  Quotient.liftOn' φ (fun f => x ∈ A → ∀ᶠ y in 𝓝 x, P y f)
    haveI : ∀ f f' : X → Y, f =ᶠ[𝓝 x] f' → (∀ᶠ y in 𝓝 x, P y f) → ∀ᶠ y in 𝓝 x, P y f' := by
      intro f f' hff' hf
      apply (hf.and <| Eventually.eventually_nhds hff').mono
      rintro y ⟨hy, hy'⟩
      rwa [Germ.coe_eq.mpr (EventuallyEq.symm hy')]
    fun f f' hff' => propext <| forall_congr' fun _ => ⟨this f f' hff', this f' f hff'.symm⟩

theorem Filter.Eventually.germ_congr {X Y : Type*} [TopologicalSpace X] {x : X}
    {P : Germ (𝓝 x) Y → Prop} {f g : X → Y} (hf : P f) (h : ∀ᶠ z in 𝓝 x, g z = f z) : P g := by
  convert hf using 1
  apply Quotient.sound
  exact h

theorem Filter.Eventually.germ_congr_set {X Y : Type*} [TopologicalSpace X]
    {P : ∀ x : X, Germ (𝓝 x) Y → Prop} {A : Set X} {f g : X → Y} (hf : ∀ᶠ x in 𝓝ˢ A, P x f)
    (h : ∀ᶠ z in 𝓝ˢ A, g z = f z) : ∀ᶠ x in 𝓝ˢ A, P x g := by
  rw [eventually_nhdsSet_iff] at *
  intro x hx
  apply ((hf x hx).and (h x hx).eventually_nhds).mono
  exact fun y hy => hy.2.germ_congr hy.1

theorem restrictGermPredicate_congr {X Y : Type*} [TopologicalSpace X]
    {P : ∀ x : X, Germ (𝓝 x) Y → Prop} {A : Set X} {f g : X → Y} {x : X}
    (hf : RestrictGermPredicate P A x f) (h : ∀ᶠ z in 𝓝ˢ A, g z = f z) :
    RestrictGermPredicate P A x g := by
  intro hx
  apply ((hf hx).and <| (eventually_nhdsSet_iff.mp h x hx).eventually_nhds).mono
  rintro y ⟨hy, h'y⟩
  rwa [Germ.coe_eq.mpr h'y]

theorem forall_restrictGermPredicate_iff {X Y : Type*} [TopologicalSpace X]
    {P : ∀ x : X, Germ (𝓝 x) Y → Prop} {A : Set X} {f : X → Y} :
    (∀ x, RestrictGermPredicate P A x f) ↔ ∀ᶠ x in 𝓝ˢ A, P x f := by
  rw [eventually_nhdsSet_iff]
  rfl

theorem forall_restrictGermPredicate_of_forall {X Y : Type*} [TopologicalSpace X]
    {P : ∀ x : X, Germ (𝓝 x) Y → Prop} {A : Set X} {f : X → Y} (h : ∀ x, P x f) :
    ∀ x, RestrictGermPredicate P A x f :=
  forall_restrictGermPredicate_iff.mpr (eventually_of_forall h)

theorem Filter.EventuallyEq.comp_fun {α β γ : Type*} {f g : β → γ} {l : Filter α} {l' : Filter β}
    (h : f =ᶠ[l'] g) {φ : α → β} (hφ : Tendsto φ l l') : f ∘ φ =ᶠ[l] g ∘ φ :=
  hφ h

theorem Filter.Tendsto.congr_germ {α β γ : Type*} {f g : β → γ} {l : Filter α} {l' : Filter β}
    (h : f =ᶠ[l'] g) {φ : α → β} (hφ : Tendsto φ l l') : (f ∘ φ : Germ l γ) = g ∘ φ :=
  @Quotient.sound _ (l.germSetoid γ) _ _ (hφ h)

def Filter.Germ.sliceLeft {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] {p : X × Y}
    (P : Germ (𝓝 p) Z) : Germ (𝓝 p.1) Z :=
  P.compTendsto (Prod.mk · p.2) (Continuous.Prod.mk_left p.2).continuousAt

@[simp]
theorem Filter.Germ.sliceLeft_coe {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X}
    {y : Y} (f : X × Y → Z) : (↑f : Germ (𝓝 (x, y)) Z).sliceLeft = fun x' => f (x', y) :=
  rfl

def Filter.Germ.sliceRight {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] {p : X × Y}
    (P : Germ (𝓝 p) Z) : Germ (𝓝 p.2) Z :=
  P.compTendsto (Prod.mk p.1) (Continuous.Prod.mk p.1).continuousAt

@[simp]
theorem Filter.Germ.sliceRight_coe {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : X × Y → Z) : (↑f : Germ (𝓝 (x, y)) Z).sliceRight = fun y' => f (x, y') :=
  rfl

def Filter.Germ.IsConstant {X Y : Type*} [TopologicalSpace X] {x : X} (P : Germ (𝓝 x) Y) : Prop :=
  P.liftOn (fun f => ∀ᶠ x' in 𝓝 x, f x' = f x) <| by
    suffices : ∀ f g : X → Y, f =ᶠ[𝓝 x] g → (∀ᶠ x' in 𝓝 x, f x' = f x) → ∀ᶠ x' in 𝓝 x, g x' = g x
    exact fun f g hfg => propext ⟨fun h => this f g hfg h, fun h => this g f hfg.symm h⟩
    rintro f g hfg hf
    refine (hf.and hfg).mono fun x' hx' => ?_
    rw [← hx'.2, hx'.1, hfg.eq_of_nhds]

theorem Filter.Germ.isConstant_coe {X Y : Type*} [TopologicalSpace X] {x : X} {y} {f : X → Y}
    (h : ∀ x', f x' = y) : (↑f : Germ (𝓝 x) Y).IsConstant :=
  eventually_of_forall fun x' => by rw [h, h]

@[simp]
theorem Filter.Germ.isConstant_coe_const {X Y : Type*} [TopologicalSpace X] {x : X} {y : Y} :
    (fun _ : X => y : Germ (𝓝 x) Y).IsConstant :=
  eventually_of_forall fun _ => rfl

theorem eq_of_germ_isConstant {X Y : Type*} [TopologicalSpace X] [PreconnectedSpace X] {f : X → Y}
    (h : ∀ x : X, (f : Germ (𝓝 x) Y).IsConstant) (x x' : X) : f x = f x' := by
  revert x
  erw [← eq_univ_iff_forall]
  apply IsClopen.eq_univ _ (⟨x', rfl⟩ : {x | f x = f x'}.Nonempty)
  refine' ⟨isOpen_iff_eventually.mpr fun x hx => hx ▸ h x, _⟩
  rw [isClosed_iff_frequently]
  rintro x hx
  rcases ((h x).and_frequently hx).exists with ⟨x'', H⟩
  exact H.1.symm.trans H.2

theorem eq_of_germ_isConstant_on {X Y : Type*} [TopologicalSpace X] {f : X → Y} {s : Set X}
    (h : ∀ x ∈ s, (f : Germ (𝓝 x) Y).IsConstant) (hs : IsPreconnected s) {x x' : X} (x_in : x ∈ s)
    (x'_in : x' ∈ s) : f x = f x' := by
  haveI := isPreconnected_iff_preconnectedSpace.mp hs
  let F : s → Y := f ∘ (↑)
  change F ⟨x, x_in⟩ = F ⟨x', x'_in⟩
  apply eq_of_germ_isConstant
  rintro ⟨x, hx⟩
  have : ContinuousAt ((↑) : s → X) ⟨x, hx⟩ := continuousAt_subtype_val
  exact this (h x hx)
