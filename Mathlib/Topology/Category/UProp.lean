/-
Copyright (c) 2025 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Mathlib.Topology.Category.TopCat.Basic

public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.ContinuousMap.Constructions
public import Mathlib.Topology.Order.UpperLowerSetTopology
public import Mathlib.Order.Hom.Basic


/-!
# UProp

Here we define `UProp` as an abbreviation for `of ULift Prop` with the Sierpinski topology.
For `X : TopCat`, `Opens X ≃ (X ⟶ UProp) ≃ Closeds X`. We provide a convenient API for working
with open and closed sets in terms of continuous maps to `UProp`.

## Main definitions

* `UProp`
* `homEquivOpen` : the type of continuous maps `X ⟶ UProp` is equivalent to the type of open subsets
  of `X`.
* `homEquivClosed` : the type of continuous maps `X ⟶ UProp` is equivalent to the type of closed
  subsets of `X`.

## Main statements

* `fooBar_unique`

## Notation



## Implementation notes

Due to unification issues in contexts where reducible definitions are not unfolded, we define
those homs likely to be applied as abbreviations-with-type-hints for `ContinuousMap`s using `where`
clauses; for example, `UProp.desc` is a `UProp ⟶ X` where `X : TopCat`, but
immediately unfolds into `UProp.desc.map` which is a `C(UProp, X)`, `X` now being an
unbundled type with a `TopologicalSpace` instance. In general, the underlying definition can
always be found under the `.map` projection.

## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

@[expose] public section

--TODO goes into `Mathlib.Topology.Order.UpperLowerSetTopology`
-- open Topology in
/-- An order iso which is also a homeomorphism transports `Topology.IsUpperSet`. -/
lemma _root_.OrderIso.isUpperSet_of_isHomeomorph {X Y}
    [Preorder X] [TopologicalSpace X] [Topology.IsUpperSet X] [Preorder Y] [TopologicalSpace Y]
    (η : X ≃o Y) (hη : IsHomeomorph η) : Topology.IsUpperSet Y := by
  constructor
  ext s
  nth_rw 2 [@Topology.IsUpperSet.isOpen_iff_isUpperSet]
  rw [← hη.isQuotientMap.isOpen_preimage, Topology.IsUpperSet.isOpen_iff_isUpperSet]
  unfold IsUpperSet
  simp [η.toEquiv.forall_congr_left]
  -- simp
  -- constructor
  -- · intro hs
  --   rw

-- /-- A homeomorphism which is also an order iso transports `Topology.IsUpperSet`.-/
-- lemma _root_.Homeomorph.isUpperSet_of_monotone {X Y}
--     [Preorder X] [TopologicalSpace X] [Topology.IsUpperSet X] [Preorder Y] [TopologicalSpace Y]
--     (η : X ≃ₜ Y) (hη : Monotone η) (hη' : Monotone η.symm) : Topology.IsUpperSet Y := by
--   constructor
--   ext s
--   nth_rw 2 [@Topology.IsUpperSet.isOpen_iff_isUpperSet]
--   rw [← η.isOpen_preimage, Topology.IsUpperSet.isOpen_iff_isUpperSet]
--   unfold IsUpperSet
--   simp [η.toEquiv.forall_congr_left, hη]
--   peel with x y
  -- simp
  -- constructor
  -- · intro hs
  --   rw

instance {X} [Preorder X] [TopologicalSpace X] [Topology.IsUpperSet X] :
    Topology.IsUpperSet (ULift X) :=
  ULift.orderIso.symm.isUpperSet_of_isHomeomorph Homeomorph.ulift.symm.isHomeomorph


-- TODO probably goes into `Mathlib.Topology.ContinuousMap.Basic`
/-- The characteristic function of an open set, as a bundled continuous map. -/
@[simps]
def ContinuousMap.ofIsOpen {X} [TopologicalSpace X] {s : Set X} (h : IsOpen s) :
    C(X, Prop) where
  toFun := (· ∈ s)
  continuous_toFun := by rwa [continuous_Prop]

-- TODO goes into ` Mathlib.Topology.Order`
lemma isClosed_singleton_false : IsClosed {False} := by
  simp [← isOpen_compl_iff, isOpen_singleton_true]

-- TODO goes into `TopCat.Basic`
lemma TopCat.Hom.continuous {X Y : TopCat} (f : X ⟶ Y) : Continuous f := f.hom.continuous

universe u v
open CategoryTheory TopCat Topology TopologicalSpace Set ContinuousMap
namespace TopCat

/-- The Sierpinski space on `ULift Prop`. -/
def UProp := ULift.{u} Prop
  deriving PartialOrder, OrderTop, OrderBot, TopologicalSpace, Inhabited, AlexandrovDiscrete
-- def UProp : TopCat.{u} := of (ULift Prop)

namespace UProp

instance : Topology.IsUpperSet UProp := inferInstanceAs (Topology.IsUpperSet <| ULift Prop)

-- instance : AlexandrovDiscrete UProp := inferInstanceAs (AlexandrovDiscrete <| ULift Prop)

instance : Coe UProp Prop := ⟨ULift.down⟩

-- attribute [simps! -isSimp] instOrderTopUProp instOrderBotUProp

lemma top_def : (⊤ : UProp) = ⟨True⟩ := rfl
lemma bot_def : (⊥ : UProp) = ⟨False⟩ := rfl
--
@[simp] lemma top : (⊤ : UProp).down := by trivial
@[simp] lemma not_bot : ¬ (⊥ : UProp).down := by simp [bot_def]

@[simp] lemma top_ne_bot : (⊤ : UProp) ≠ (⊥ : UProp) := by
  intro h; simp [↓top_def, ↓bot_def, UProp] at h

@[simp] lemma bot_ne_top : (⊥ : UProp) ≠ (⊤ : UProp) := top_ne_bot.symm

@[simp]
lemma «forall» {p : UProp → Prop} : (∀ z, p z) ↔ p ⊤ ∧ p ⊥ := by
  constructor
  · intro h; exact ⟨h _, h _⟩
  · rintro ⟨hT, hF⟩ ⟨p⟩; rcases em p with h | h <;> simp [h, hT, hF, ← top_def, ← bot_def]

@[simp]
lemma «exists» {p : UProp → Prop} : (∃ z, p z) ↔ p ⊤ ∨ p ⊥ := by
  constructor
  · rintro ⟨⟨q⟩, hq⟩; rcases em q with h | h <;> simp_all [← top_def, ← bot_def]
  · rintro (hT | hF) <;> [use ⊤; use ⊥]

@[ext]
lemma funext {α} {f g : UProp → α} (h_top : f ⊤ = g ⊤) (h_bot : f ⊥ = g ⊥) : f = g := by
  ext ⟨p⟩; rcases em p with h | h <;> simp [h, h_top, h_bot, ← top_def, ← bot_def]

@[ext]
lemma propext {α} {f g : α → UProp} (h_top : ∀ x, f x = ⊤ ↔ g x = ⊤) : f = g := by
  ext x
  rcases hf : f x with ⟨pf⟩; rcases hg : g x with ⟨pg⟩
  rcases em pf with hpf | hpf <;> rcases em pg with hpg | hpg <;>
    simp only [hpf, hpg, ← top_def, ← bot_def] at *
  · simp [h_top, hg] at hf
  · simp [← h_top, hf] at hg

@[ext]
lemma set_ext {s t : Set UProp} (h_top : ⊤ ∈ s ↔ ⊤ ∈ t) (h_bot : ⊥ ∈ s ↔ ⊥ ∈ t) : s = t := by
  ext ⟨p⟩; rcases em p with h | h <;> simp [h, h_top, h_bot, ← top_def, ← bot_def]

@[ext]
lemma hom_ext {X} {f g : of UProp ⟶ X} (h_top : f ⊤ = g ⊤) (h_bot : f ⊥ = g ⊥) : f = g := by
  apply TopCat.hom_ext; apply ContinuousMap.coe_injective; ext <;> simp [h_top, h_bot]

@[ext]
lemma hom_ext' {X : TopCat} {f g : X ⟶ of UProp} : (∀ x, f x = ⊤ ↔ g x = ⊤) → f = g := by
  intro hx; apply TopCat.hom_ext; apply ContinuousMap.coe_injective;
  ext x; simp [hx]

lemma univ_eq : (Set.univ : Set UProp) = {⊤, ⊥} := by ext <;> simp

@[simp]
lemma not_eq_top_iff {x : UProp} : x ≠ ⊤ ↔ x = ⊥ := by
  rcases x with ⟨p⟩; rcases em p with h' | h' <;> simp_all [ULift.ext_iff, UProp]

@[simp]
lemma not_eq_bot_iff {x : UProp} : x ≠ ⊥ ↔ x = ⊤ := by
  rcases x with ⟨p⟩; rcases em p with h' | h' <;> simp_all [ULift.ext_iff, UProp]

@[simp]
lemma isOpen_top : IsOpen {(⊤ : UProp)} := by
  simpa [↓top_def, UProp, ULift.isOpen_iff, ← Set.setOf_eq_eq_singleton]
    using isOpen_singleton_true

@[simp]
lemma isClosed_bot : IsClosed {(⊥ : UProp)} := by
  rw [← isOpen_compl_iff]; convert isOpen_top; ext <;> simp

lemma specializes : (⊤ : UProp) ⤳ (⊥ : UProp) := by
  have : True ⤳ False := by unfold Specializes; simp
  exact this.map Homeomorph.ulift.continuous_symm

@[simp]
lemma specializes_iff : ∀ {x y : UProp.{u}}, x ⤳ y ↔ x = ⊤ ∨ y = ⊥ := by
  simpa [UProp.forall, specializes_refl, specializes] using
    isOpen_top.not_specializes (by simp) rfl
  -- rcases x with ⟨px⟩; rcases y with ⟨py⟩
  -- rcases em px with hpx | hpx <;> rcases em py with hpy | hpy <;> simp_all [UProp, ULift.ext_iff]

@[simp]
lemma not_isOpen_bot : ¬ IsOpen {(⊥ : UProp)} := by
  intro h
  have := specializes.mem_open h (Set.mem_singleton _)
  simp at this

lemma isOpen_iff_empty_or_top_mem {u : Set UProp} : IsOpen u ↔ u = ∅ ∨ ⊤ ∈ u := by
  constructor
  · intro hu
    simp_rw [or_iff_not_imp_left, ← Set.nonempty_iff_ne_empty]
    rintro ⟨x, hx⟩; rcases x with ⟨p⟩; rcases em p with h | h
    · simpa [h] using hx
    · exact specializes.mem_open hu <| by simpa [h] using hx
  · rintro (rfl | hT)
    · simp
    · rcases em (⊥ ∈ u) with hF | hF
      · convert isOpen_univ; ext <;> simp [hT, hF]
      · convert isOpen_top; ext <;> simp [hT, hF]

lemma isOpen_iff {u : Set UProp} : IsOpen u ↔ u = ∅ ∨ u = {⊤} ∨ u = univ := by
  simp [isOpen_iff_empty_or_top_mem, univ_eq, Set.ext_iff]; grind

lemma basis : IsTopologicalBasis (α := UProp) {{⊤}, univ} := by
  apply isTopologicalBasis_of_isOpen_of_nhds (by simp)
  rw [UProp.forall]; split_ands
  · intro u hu uO; use {⊤}, by simp, mem_singleton _, by simp [hu]
  · intro u hu uO; use univ, by simp, mem_univ _
    rw [univ_subset_iff, univ_eq]
    ext <;> simp [specializes.mem_open uO hu, hu]

section opens

attribute [local simp] UProp in
/-- The set of open sets on a topological space `X` is in bijection with the set of continuous maps
`X ⟶ UProp`. -/
@[simps]
def homEquivOpen (X : Type u) [TopologicalSpace X] : Opens X ≃ C(X, UProp.{v}) where
  toFun s := .comp .uliftUp <| .ofIsOpen s.2
  invFun f := ⟨f ⁻¹' (uliftUp '' {True}), IsOpen.preimage f.continuous <|
    IsOpenEmbedding.uliftUp.isOpen_iff_image_isOpen.mp isOpen_singleton_true⟩
  left_inv s := by ext; simp [uliftUp, Homeomorph.ulift]
  right_inv f := by ext; simp [ULift.ext_iff]


end opens

section closeds

attribute [local simp] UProp in
/-- The set of closed sets on a topological space `X` is in bijection with the set of continuous
maps `X ⟶ UProp`. -/
@[simps]
def homEquivClosed (X : Type u) [TopologicalSpace X] : Closeds X ≃ C(X, UProp.{v}) where
  toFun s := .comp .uliftUp <| .ofIsOpen s.2.isOpen_compl
  invFun f := ⟨f ⁻¹' (uliftUp '' {False}), IsClosed.preimage f.continuous <|
    IsClosedEmbedding.uliftUp.isClosed_iff_image_isClosed.mp isClosed_singleton_false⟩
  left_inv s := by ext; simp [uliftUp, Homeomorph.ulift]
  right_inv f := by ext; simp [ULift.ext_iff]

end closeds

open scoped Classical in
noncomputable abbrev desc {X : TopCat.{u}} {x y : X} (hxy : x ⤳ y) : of UProp ⟶ X :=
  ofHom (map hxy)
where
  map {X : Type u} [TopologicalSpace X] {x y : X} (hxy : x ⤳ y) : C(UProp, X) :=
    .comp ⟨(if · then x else y), ⟨by
      intro s hs
      by_cases hy : y ∈ s
      · replace hxy := hxy.mem_open hs hy
        convert isOpen_univ
        simp only [Set.preimage_eq_univ_iff]
        rintro x ⟨p, rfl⟩
        simp only
        split_ifs <;> assumption
      · by_cases hx : x ∈ s
        · convert isOpen_singleton_true
          ext p
          rcases em p with h | h <;> simp [h, hx, hy]
        · convert isOpen_empty
          ext p
          rcases em p with h | h <;> simp [h, hx, hy] ⟩⟩ .uliftDown

-- @[simp]
-- lemma desc_apply_top' {X : TopCat} {x y : X} (hxy : x ⤳ y) :
--     (desc.map hxy) ⊤ = x := by simp [desc.map, UProp]

@[simp]
lemma desc_apply_top {X} [TopologicalSpace X] {x y : X} (hxy : x ⤳ y) :
    (desc.map hxy) ⊤ = x := by simp [desc.map, UProp]

-- @[simp]
-- lemma desc_apply_bot' {X : TopCat} {x y : X} (hxy : x ⤳ y) :
--     (desc.map hxy) ⊥ = y := by simp [desc.map, UProp]

@[simp]
lemma desc_apply_bot {X} [TopologicalSpace X] {x y : X} (hxy : x ⤳ y) :
    (desc.map hxy) ⊥ = y := by simp [desc.map, UProp]

lemma specializesOfHom {X : TopCat} (f : of UProp ⟶ X) : f ⊤ ⤳ f ⊥ := specializes.map f.continuous

end TopCat.UProp

namespace IsOpen
open TopCat UProp

/-- Build a continuous map to `UProp` from an open set. -/
-- @[simp]
abbrev toHom {X : TopCat.{u}} {s : Set X} (hs : IsOpen s) : X ⟶ of UProp :=
  ofHom (map (X := of X) hs)
where
  map {X : Type u} [TopologicalSpace X] {s : Set X} hs : C(X, UProp) := homEquivOpen (of X) ⟨s, hs⟩

@[inherit_doc toHom]
abbrev toHom' {X} [TopologicalSpace X] {s : Set X} (hs : IsOpen s) : of X ⟶ of UProp := toHom hs

@[simp]
lemma toHom_apply_iff_mem {X} [TopologicalSpace X] {s : Set X} (hs : IsOpen s) {x : X} :
    toHom.map hs x = ⊤ ↔ x ∈ s := by
  simp [UProp, ULift.ext_iff, -ULift.down_inj]; rfl

alias ⟨_, toHom_apply_of_mem⟩ := toHom_apply_iff_mem

--For some reason, even though the proof is just `by simp`, this lemma fails to
--`simp` 'in the wild' without explicit `@[simp]`
@[simp] lemma toHom_univ_apply {X} [TopologicalSpace X] {x : X} :
    toHom.map isOpen_univ x = ⊤ := by simp

@[simp] lemma toHom_singleton_apply {X} [TopologicalSpace X] {x y : X} {h : IsOpen {x}} :
    toHom.map h y = ⊤ ↔ x = y := by simpa using eq_comm

@[simp]
lemma toHom_apply_iff_notMem {X} [TopologicalSpace X] {s : Set X} (hs : IsOpen s) {x : X} :
   toHom.map hs x = ⊥ ↔ x ∉ s := by
  simp [UProp, ULift.ext_iff, -ULift.down_inj]; rfl

alias ⟨_, toHom_apply_of_notMem⟩ := toHom_apply_iff_notMem

@[simp] lemma toHom_empty_apply {X} [TopologicalSpace X] {x : X} :
    toHom.map isOpen_empty x = ⊥ := by simp

@[simp]
lemma ofHom {X : TopCat} (f : X ⟶ of UProp) : IsOpen (f ⁻¹' {⊤}) :=
  isOpen_top.preimage f.continuous

@[simp]
lemma toHom_ofHom {X : TopCat} (s : X ⟶ of UProp) :
    (ofHom s).toHom = s := by
  ext x; simp [toHom, toHom.map, UProp, homEquivOpen, ULift.ext_iff, -ULift.down_inj]

@[simp]
lemma preimage_toHom_top {X : TopCat} {s : Set X} (hs : IsOpen s) :
    toHom.map hs ⁻¹' {⊤} = s := by
  ext x; simp [toHom_apply_iff_mem hs]

@[simp]
lemma preimage_toHom_bot {X : TopCat} {s : Set X} (hs : IsOpen s) :
    toHom.map hs ⁻¹' {⊥} = sᶜ := by
  ext x; simp [toHom_apply_iff_notMem hs]

@[reassoc (attr := simp)]
lemma comp_toHom {X Y : TopCat.{u}} (f : X ⟶ Y) {s : Set Y} (hs : IsOpen s) :
    f ≫ hs.toHom = (hs.preimage f.hom.continuous).toHom := by
  ext x; simp

@[simp]
lemma toHom_inj {X : TopCat} {s t : Set X} (hs : IsOpen s) (ht : IsOpen t) :
    (hs.toHom = ht.toHom) ↔ s = t := by
  simp only [toHom.map, ConcreteCategory.ext_iff, Equiv.apply_eq_iff_eq, hom_ofHom]
  simp

end IsOpen

namespace IsClosed
open TopCat UProp

/-- Build a continuous map to `UProp` from an closed set. -/
-- @[simp]
abbrev toHom {X : TopCat} {s : Set X} (hs : IsClosed s) : X ⟶ of UProp :=
  ofHom (map hs)
where
  map {X : Type u} [TopologicalSpace X] {s : Set X} hs : C(X, UProp) :=
    homEquivClosed (of X) ⟨s, hs⟩

@[inherit_doc toHom]
abbrev toHom' {X} [TopologicalSpace X] {s : Set X} (hs : IsClosed s) : of X ⟶ of UProp := toHom hs

@[simp]
lemma toHom_apply_iff_notMem {X} [TopologicalSpace X] {s : Set X} (hs : IsClosed s) {x : X} :
    toHom.map hs x = ⊤ ↔ x ∉ s := by
  simp [UProp, ULift.ext_iff, -ULift.down_inj]; rfl

@[simp] alias ⟨_, toHom_apply_of_notMem⟩ := toHom_apply_iff_notMem

@[simp] lemma toHom_empty_apply {X} [TopologicalSpace X] {x : X} :
    toHom.map isClosed_empty x = ⊤ := by simp

@[simp]
lemma toHom_apply_iff_mem {X} [TopologicalSpace X] {s : Set X} (hs : IsClosed s) {x : X} :
   toHom.map hs x = ⊥ ↔ x ∈ s := by
  conv_rhs => rw [← not_not (a := x ∈ s)]
  simp [UProp, ULift.ext_iff, -ULift.down_inj, -not_not]; rfl

alias ⟨_, toHom_apply_of_mem⟩ := toHom_apply_iff_mem

@[simp] lemma toHom_univ_apply {X} [TopologicalSpace X] {x : X} :
    toHom.map isClosed_univ x = ⊥ := by simp

@[simp] lemma toHom_singleton_apply {X} [TopologicalSpace X] {x y : X} {h : IsClosed {x}} :
    toHom.map h y = ⊥ ↔ x = y := by simpa using eq_comm

@[simp]
lemma ofHom {X : TopCat} (f : X ⟶ of UProp) : IsClosed (f ⁻¹' {⊥}) :=
  isClosed_bot.preimage f.continuous

@[simp]
lemma toHom_ofHom {X : TopCat} (s : X ⟶ of UProp) :
    (ofHom s).toHom = s := by ext x; simp

-- @[simp]
-- lemma preimage_toHom_bot {X} [TopologicalSpace X] {s : Set X} (hs : IsClosed s) :
--     toHom.map hs ⁻¹' {⊥} = (TopCat.coe_of X).mp ⁻¹' s := by ext; simp
@[simp]
lemma preimage_toHom_bot {X} [TopologicalSpace X] {s : Set X} (hs : IsClosed s) :
    toHom.map hs ⁻¹' {⊥} = s := by ext; simp

-- @[simp]
-- lemma preimage_toHom_top {X} [TopologicalSpace X] {s : Set X} (hs : IsClosed s) :
--     toHom.map hs ⁻¹' {⊤} = (TopCat.coe_of X).mp ⁻¹' sᶜ := by ext x; simp

@[simp]
lemma preimage_toHom_top {X} [TopologicalSpace X] {s : Set X} (hs : IsClosed s) :
    toHom.map hs ⁻¹' {⊤} = sᶜ := by ext x; simp

@[reassoc (attr := simp)]
lemma comp_toHom {X Y : TopCat} (f : X ⟶ Y) {s : Set Y} (hs : IsClosed s) :
    f ≫ hs.toHom = (hs.preimage f.continuous).toHom := by
  ext x; simp

@[simp↓]
lemma toHom_inj {X : TopCat} {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) :
    (hs.toHom = ht.toHom) ↔ s = t := by
  simp only [toHom, toHom.map, ConcreteCategory.ext_iff, UProp.homEquivClosed _ |>.apply_eq_iff_eq,
  hom_ofHom]; simp


end IsClosed

@[simp]
lemma isClosed_toHom_eq_isOpen_toHom_iff {X : TopCat}
    {s : Set X} (hs : IsClosed s) {t : Set X} (ht : IsOpen t) : hs.toHom = ht.toHom ↔ sᶜ = t := by
  simp [UProp.hom_ext'_iff, Set.ext_iff]

@[simp]
lemma isOpen_toHom_eq_isClosed_toHom_iff {X : TopCat}
    {s : Set X} (hs : IsOpen s) {t : Set X} (ht : IsClosed t) : hs.toHom = ht.toHom ↔ s = tᶜ := by
  simp [UProp.hom_ext'_iff, Set.ext_iff]
