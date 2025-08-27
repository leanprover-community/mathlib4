/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.Set.BooleanAlgebra

/-!
# Relations as sets of pairs

This file provides API to regard relations between `α` and `β`  as sets of pairs `Set (α × β)`.

This is in particular useful in the study of uniform spaces, which are topological spaces equipped
with a *uniformity*, namely a filter of pairs `α × α` whose elements can be viewed as "proximity"
relations.

## Main declarations

* `SetRel α β`: Type of relations between `α` and `β`.
* `SetRel.inv`: Turn `R : SetRel α β` into `R.inv : SetRel β α` by swapping the arguments.
* `SetRel.dom`: Domain of a relation. `a ∈ R.dom` iff there exists `b` such that `a ~[R] b`.
* `SetRel.cod`: Codomain of a relation. `b ∈ R.cod` iff there exists `a` such that `a ~[R] b`.
* `SetRel.id`: The identity relation `SetRel α α`.
* `SetRel.comp`: SetRelation composition. Note that the arguments order follows the category theory
  convention, namely `(R ○ S) a c ↔ ∃ b, a ~[R] b ∧ b ~[S] z`.
* `SetRel.image`: Image of a set under a relation. `b ∈ image R s` iff there exists `a ∈ s`
  such that `a ~[R] b`.
  If `R` is the graph of `f` (`a ~[R] b ↔ f a = b`), then `R.image = Set.image f`.
* `SetRel.preimage`: Preimage of a set under a relation. `a ∈ preimage R t` iff there exists
  `b ∈ t` such that `a ~[R] b`.
  If `R` is the graph of `f` (`a ~[R] b ↔ f a = b`), then `R.preimage = Set.preimage f`.
* `SetRel.core`: Core of a set. For `t : Set β`, `a ∈ R.core t` iff all `b` related to `a` are in
  `t`.
* `SetRel.restrictDomain`: Domain-restriction of a relation to a subtype.
* `Function.graph`: Graph of a function as a relation.

## Implementation notes

There is tension throughout the library between considering relations between `α` and `β` simply as
`α → β → Prop`, or as a bundled object `SetRel α β` with dedicated operations and API.

The former approach is used almost everywhere as it is very lightweight and has arguably native
support from core Lean features, but it cracks at the seams whenever one starts talking about
operations on relations. For example:
* composition of relations `R : α → β → Prop`, `S : β → γ → Prop` is
  `SetRelation.Comp R S := fun a c ↦ ∃ b, R a b ∧ S b c`
* map of a relation `R : α → β → Prop` under `f : α → γ`, `g : β → δ` is
  `SetRelation.map R f g := fun c d ↦ ∃ a b, r a b ∧ f a = c ∧ g b = d`.

The latter approach is embodied by `SetRel α β`, with dedicated notation like `○` for composition.

Previously, `SetRel` suffered from the leakage of its definition as
```
def SetRel (α β : Type*) := α → β → Prop
```
The fact that `SetRel` wasn't an `abbrev` confuses automation.
But simply making it an `abbrev` would
have killed the point of having a separate less see-through type to perform relation operations on,
so we instead redefined
```
def SetRel (α β : Type*) := Set (α × β) → Prop
```
This extra level of indirection guides automation correctly and prevents (some kinds of) leakage.

Simultaneously, uniform spaces need a theory of relations on a type `α` as elements of
`Set (α × α)`, and the new definition of `SetRel` fulfills this role quite well.
-/

variable {α β γ δ : Type*}

/-- A relation on `α` and `β`, aka a set-valued function, aka a partial multifunction.

We represent them as sets due to how relations are used in the context of uniform spaces. -/
abbrev SetRel (α β : Type*) := Set (α × β)

namespace SetRel
variable {R r₁ r₂ : SetRel α β} {S : SetRel β γ} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {u : Set γ}
  {a a₁ a₂ : α} {b : β} {c : γ}

/-- Notation for apply a relation `R : SetRel α β` to `a : α`, `b : β`,
scoped to the `SetRel` namespace.

Since `SetRel α β := Set (α × β)`, `a ~[R] b` is simply notation for `(a, b) ∈ R`, but this should
be considered an implementation detail. -/
scoped notation:50 a:50 " ~[" R "] " b:50 => (a, b) ∈ R

variable (R) in
/-- The inverse relation : `R.inv x y ↔ R y x`. Note that this is *not* a groupoid inverse. -/
def inv (R : SetRel α β) : SetRel β α := Prod.swap ⁻¹' R

@[simp] lemma mem_inv : b ~[R.inv] a ↔ a ~[R] b := .rfl

@[deprecated (since := "2025-07-06")] alias inv_def := mem_inv

@[simp] lemma inv_inv : R.inv.inv = R := rfl

@[gcongr] lemma inv_mono (h : r₁ ⊆ r₂) : r₁.inv ⊆ r₂.inv := fun (_a, _b) hab ↦ h hab

@[simp] lemma inv_empty : (∅ : SetRel α β).inv = ∅ := rfl
@[simp] lemma inv_univ : inv (.univ : SetRel α β) = .univ := rfl

@[deprecated (since := "2025-07-06")] alias inv_bot := inv_empty

variable (R) in
/-- Domain of a relation. -/
def dom : Set α := {a | ∃ b, a ~[R] b}

variable (R) in
/-- Codomain of a relation, aka range. -/
def cod : Set β := {b | ∃ a, a ~[R] b}

@[deprecated (since := "2025-07-06")] alias codom := cod

@[simp] lemma mem_dom : a ∈ R.dom ↔ ∃ b, a ~[R] b := .rfl
@[simp] lemma mem_cod : b ∈ R.cod ↔ ∃ a, a ~[R] b := .rfl

@[gcongr] lemma dom_mono (h : r₁ ≤ r₂) : r₁.dom ⊆ r₂.dom := fun _a ⟨b, hab⟩ ↦ ⟨b, h hab⟩
@[gcongr] lemma cod_mono (h : r₁ ≤ r₂) : r₁.cod ⊆ r₂.cod := fun _b ⟨a, hab⟩ ↦ ⟨a, h hab⟩

@[simp] lemma dom_empty : (∅ : SetRel α β).dom = ∅ := by aesop
@[simp] lemma cod_empty : (∅ : SetRel α β).cod = ∅ := by aesop

@[simp] lemma dom_univ [Nonempty β] : dom (.univ : SetRel α β) = .univ := by aesop
@[simp] lemma cod_univ [Nonempty α] : cod (.univ : SetRel α β) = .univ := by aesop

@[simp] lemma cod_inv : R.inv.cod = R.dom := rfl
@[simp] lemma dom_inv : R.inv.dom = R.cod := rfl

@[deprecated (since := "2025-07-06")] alias codom_inv := cod_inv

/-- The identity relation. -/
protected def id : SetRel α α := {(a₁, a₂) | a₁ = a₂}

@[simp] lemma mem_id : a₁ ~[SetRel.id] a₂ ↔ a₁ = a₂ := .rfl

@[simp] lemma inv_id : (.id : SetRel α α).inv = .id := by aesop

/-- Composition of relation.

Note that this follows the `CategoryTheory` order of arguments. -/
def comp (R : SetRel α β) (S : SetRel β γ) : SetRel α γ := {(a, c) | ∃ b, a ~[R] b ∧ b ~[S] c}

@[inherit_doc] scoped infixl:62 " ○ " => comp

@[simp] lemma mem_comp : a ~[R ○ S] c ↔ ∃ b, a ~[R] b ∧ b ~[S] c := .rfl

lemma comp_assoc (R : SetRel α β) (S : SetRel β γ) (t : SetRel γ δ) :
    (R ○ S) ○ t = R ○ (S ○ t) := by aesop

@[simp] lemma comp_id (R : SetRel α β) : R ○ .id = R := by aesop
@[simp] lemma id_comp (R : SetRel α β) : .id ○ R = R := by aesop

@[simp] lemma inv_comp (R : SetRel α β) (S : SetRel β γ) : (R ○ S).inv = S.inv ○ R.inv := by aesop

@[simp] lemma comp_empty (R : SetRel α β) : R ○ (∅ : SetRel β γ) = ∅ := by aesop
@[simp] lemma empty_comp (S : SetRel β γ) : (∅ : SetRel α β) ○ S = ∅ := by aesop

@[simp] lemma comp_univ (R : SetRel α β) :
    R ○ (.univ : SetRel β γ) = {(a, _c) : α × γ | a ∈ R.dom} := by
  aesop

@[simp] lemma univ_comp (S : SetRel β γ) :
    (.univ : SetRel α β) ○ S = {(_b, c) : α × γ | c ∈ S.cod} := by
  aesop

@[deprecated (since := "2025-07-06")] alias comp_right_top := comp_univ
@[deprecated (since := "2025-07-06")] alias comp_left_top := univ_comp

variable (R s) in
/-- Image of a set under a relation. -/
def image : Set β := {b | ∃ a ∈ s, a ~[R] b}

variable (R t) in
/-- Preimage of a set `t` under a relation `R`. Same as the image of `t` under `R.inv`. -/
def preimage : Set α := {a | ∃ b ∈ t, a ~[R] b}

@[simp] lemma mem_image : b ∈ image R s ↔ ∃ a ∈ s, a ~[R] b := .rfl
@[simp] lemma mem_preimage : a ∈ preimage R t ↔ ∃ b ∈ t, a ~[R] b := .rfl

@[gcongr] lemma image_subset_image (hs : s₁ ⊆ s₂) : image R s₁ ⊆ image R s₂ :=
  fun _ ⟨a, ha, hab⟩ ↦ ⟨a, hs ha, hab⟩

@[gcongr] lemma preimage_subset_preimage (ht : t₁ ⊆ t₂) : preimage R t₁ ⊆ preimage R t₂ :=
  fun _ ⟨a, ha, hab⟩ ↦ ⟨a, ht ha, hab⟩

variable (R t) in
@[simp] lemma image_inv : R.inv.image t = preimage R t := rfl

variable (R s) in
@[simp] lemma preimage_inv : R.inv.preimage s = image R s := rfl

lemma image_mono : Monotone R.image := fun _ _ ↦ image_subset_image
lemma preimage_mono : Monotone R.preimage := fun _ _ ↦ preimage_subset_preimage

@[simp] lemma image_empty_right : image R ∅ = ∅ := by aesop
@[simp] lemma preimage_empty_right : preimage R ∅ = ∅ := by aesop

@[simp] lemma image_univ_right : image R .univ = R.cod := by aesop
@[simp] lemma preimage_univ_right : preimage R .univ = R.dom := by aesop

variable (R) in
lemma image_inter_subset : image R (s₁ ∩ s₂) ⊆ image R s₁ ∩ image R s₂ := image_mono.map_inf_le ..

@[deprecated (since := "2025-07-06")] alias preimage_top := image_inter_subset

variable (R) in
lemma preimage_inter_subset : preimage R (t₁ ∩ t₂) ⊆ preimage R t₁ ∩ preimage R t₂ :=
  preimage_mono.map_inf_le ..

@[deprecated (since := "2025-07-06")] alias image_eq_dom_of_codomain_subset := preimage_inter_subset

variable (R s₁ s₂) in
lemma image_union : image R (s₁ ∪ s₂) = image R s₁ ∪ image R s₂ := by aesop

@[deprecated (since := "2025-07-06")] alias preimage_eq_codom_of_domain_subset := image_union

variable (R t₁ t₂) in
lemma preimage_union : preimage R (t₁ ∪ t₂) = preimage R t₁ ∪ preimage R t₂ := by aesop

variable (s) in
@[simp] lemma image_id : image .id s = s := by aesop

variable (s) in
@[simp] lemma preimage_id : preimage .id s = s := by aesop

variable (R S s) in
lemma image_comp : image (R ○ S) s = image S (image R s) := by aesop

variable (R S u) in
lemma preimage_comp : preimage (R ○ S) u = preimage R (preimage S u) := by aesop

variable (s) in
@[simp] lemma image_empty_left : image (∅ : SetRel α β) s = ∅ := by aesop

variable (t) in
@[simp] lemma preimage_empty_left : preimage (∅ : SetRel α β) t = ∅ := by aesop

@[deprecated (since := "2025-07-06")] alias preimage_bot := preimage_empty_left

@[simp] lemma image_univ_left (hs : s.Nonempty) : image (.univ : SetRel α β) s = .univ := by aesop
@[simp] lemma preimage_univ_left (ht : t.Nonempty) : preimage (.univ : SetRel α β) t = .univ := by
  aesop

lemma image_eq_cod_of_dom_subset (h : R.cod ⊆ t) : R.preimage t = R.dom := by aesop
lemma preimage_eq_dom_of_cod_subset (h : R.cod ⊆ t) : R.preimage t = R.dom := by aesop

variable (R s) in
@[simp] lemma image_inter_dom : image R (s ∩ R.dom) = image R s := by aesop

variable (R t) in
@[simp] lemma preimage_inter_cod : preimage R (t ∩ R.cod) = preimage R t := by aesop

@[deprecated (since := "2025-07-06")] alias preimage_inter_codom_eq := preimage_inter_cod

lemma inter_dom_subset_preimage_image : s ∩ R.dom ⊆ R.preimage (image R s) := by
  aesop (add simp [Set.subset_def])

lemma inter_cod_subset_image_preimage : t ∩ R.cod ⊆ image R (R.preimage t) := by
  aesop (add simp [Set.subset_def])

@[deprecated (since := "2025-07-06")]
alias image_preimage_subset_inter_codom := inter_cod_subset_image_preimage

variable (R t) in
/-- Core of a set `S : Set β` w.R.t `R : SetRel α β` is the set of `x : α` that are related *only*
to elements of `S`. Other generalization of `Function.preimage`. -/
def core : Set α := {a | ∀ ⦃b⦄, a ~[R] b → b ∈ t}

@[simp] lemma mem_core : a ∈ R.core t ↔ ∀ ⦃b⦄, a ~[R] b → b ∈ t := .rfl

@[gcongr]
lemma core_subset_core (ht : t₁ ⊆ t₂) : R.core t₁ ⊆ R.core t₂ := fun _a ha _b hab ↦ ht <| ha hab

lemma core_mono : Monotone R.core := fun _ _ ↦ core_subset_core

variable (R t₁ t₂) in
lemma core_inter : R.core (t₁ ∩ t₂) = R.core t₁ ∩ R.core t₂ := by aesop

lemma core_union_subset : R.core t₁ ∪ R.core t₂ ⊆ R.core (t₁ ∪ t₂) := core_mono.le_map_sup ..

@[simp] lemma core_univ : R.core Set.univ = Set.univ := by aesop

variable (t) in
@[simp] lemma core_id : core .id t = t := by aesop

variable (R S u) in
lemma core_comp : core (R ○ S) u = core R (core S u) := by aesop

lemma image_subset_iff : image R s ⊆ t ↔ s ⊆ core R t := by aesop (add simp [Set.subset_def])

lemma image_core_gc : GaloisConnection R.image R.core := fun _ _ ↦ image_subset_iff

variable (R s) in
/-- Restrict the domain of a relation to a subtype. -/
def restrictDomain : SetRel s β := {(a, b) | ↑a ~[R] b}

variable {R : SetRel α α} {S : SetRel β β} {a b c : α}

variable (R) in
/-- A relation `R` is transitive if `a ~[R] b` and `b ~[R] c` together imply `a ~[R] c`. -/
protected abbrev IsTrans : Prop := IsTrans α (· ~[R] ·)

variable (R) in
protected lemma trans [R.IsTrans] (hab : a ~[R] b) (hbc : b ~[R] c) : a ~[R] c :=
  trans_of (· ~[R] ·) hab hbc

instance {R : α → α → Prop} [IsTrans α R] : SetRel.IsTrans {(a, b) | R a b} := ‹_›

variable (R) in
/-- A relation `R` is irreflexive if `¬ a ~[R] a`. -/
protected abbrev IsIrrefl : Prop := IsIrrefl α (· ~[R] ·)

variable (R a) in
protected lemma irrefl [R.IsIrrefl] : ¬ a ~[R] a := irrefl_of (· ~[R] ·) _

instance {R : α → α → Prop} [IsIrrefl α R] : SetRel.IsIrrefl {(a, b) | R a b} := ‹_›

variable (R) in
/-- A relation `R` on a type `α` is well-founded if all elements of `α` are accessible within `R`.
-/
abbrev IsWellFounded : Prop := WellFounded (· ~[R] ·)

variable (R S) in
/-- A relation homomorphism with respect to a given pair of relations `R` and `S` s is a function
`f : α → β` such that `a ~[R] b → f a ~[s] f b`. -/
abbrev Hom := (· ~[R] ·) →r (· ~[S] ·)

end SetRel

open Set
open scoped SetRel

namespace Function
variable {f : α → β} {a : α} {b : β}

/-- The graph of a function as a relation. -/
def graph (f : α → β) : SetRel α β := {(a, b) | f a = b}

@[simp] lemma mem_graph : a ~[f.graph] b ↔ f a = b := .rfl

@[deprecated (since := "2025-07-06")] alias graph_def := mem_graph

theorem graph_injective : Injective (graph : (α → β) → SetRel α β) := by
  aesop (add simp [Injective, Set.ext_iff])

@[simp] lemma graph_inj {f g : α → β} : f.graph = g.graph ↔ f = g := graph_injective.eq_iff

@[simp] lemma graph_id : graph (id : α → α) = .id := by aesop

theorem graph_comp (f : β → γ) (g : α → β) : graph (f ∘ g) = graph g ○ graph f := by aesop

end Function

theorem Equiv.graph_inv (f : α ≃ β) : (f.symm : β → α).graph = SetRel.inv (f : α → β).graph := by
  aesop

lemma SetRel.exists_graph_eq_iff (R : SetRel α β) :
    (∃! f, Function.graph f = R) ↔ ∀ a, ∃! b, a ~[R] b := by
  constructor
  · rintro ⟨f, rfl, _⟩ x
    simp
  intro h
  choose f hf using fun x ↦ (h x).exists
  refine ⟨f, ?_, by aesop⟩
  ext ⟨a, b⟩
  constructor
  · aesop
  · exact (h _).unique (hf _)

@[deprecated (since := "2025-07-06")] alias SetRelation.is_graph_iff := SetRel.exists_graph_eq_iff

namespace Set

theorem image_eq (f : α → β) (s : Set α) : f '' s = (Function.graph f).image s := by
  rfl

theorem preimage_eq (f : α → β) (s : Set β) : f ⁻¹' s = (Function.graph f).preimage s := by
  simp [Set.preimage, SetRel.preimage]

theorem preimage_eq_core (f : α → β) (s : Set β) : f ⁻¹' s = (Function.graph f).core s := by
  simp [Set.preimage, SetRel.core]

end Set

/-- A shorthand for `α → β → Prop`.

Consider using `SetRel` instead if you want extra API for relations. -/
abbrev Rel (α β : Type*) : Type _ := α → β → Prop
