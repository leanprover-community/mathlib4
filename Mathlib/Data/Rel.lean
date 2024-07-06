/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Order.CompleteLattice
import Mathlib.Order.GaloisConnection
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.AdaptationNote

#align_import data.rel from "leanprover-community/mathlib"@"706d88f2b8fdfeb0b22796433d7a6c1a010af9f2"

/-!
# Relations

This file defines bundled relations. A relation between `α` and `β` is a function `α → β → Prop`.
Relations are also known as set-valued functions, or partial multifunctions.

## Main declarations

* `Rel α β`: Relation between `α` and `β`.
* `Rel.inv`: `r.inv` is the `Rel β α` obtained by swapping the arguments of `r`.
* `Rel.dom`: Domain of a relation. `x ∈ r.dom` iff there exists `y` such that `r x y`.
* `Rel.codom`: Codomain, aka range, of a relation. `y ∈ r.codom` iff there exists `x` such that
  `r x y`.
* `Rel.comp`: Relation composition. Note that the arguments order follows the `CategoryTheory/`
  one, so `r.comp s x z ↔ ∃ y, r x y ∧ s y z`.
* `Rel.image`: Image of a set under a relation. `r.image s` is the set of `f x` over all `x ∈ s`.
* `Rel.preimage`: Preimage of a set under a relation. Note that `r.preimage = r.inv.image`.
* `Rel.core`: Core of a set. For `s : Set β`, `r.core s` is the set of `x : α` such that all `y`
  related to `x` are in `s`.
* `Rel.restrict_domain`: Domain-restriction of a relation to a subtype.
* `Function.graph`: Graph of a function as a relation.

## TODOs

The `Rel.comp` function uses the notation `r • s`, rather than the more common `r ∘ s` for things
named `comp`. This is because the latter is already used for function composition, and causes a
clash. A better notation should be found, perhaps a variant of `r ∘r s` or `r; s`.

-/

variable {α β γ : Type*}

/-- A relation on `α` and `β`, aka a set-valued function, aka a partial multifunction -/
def Rel (α β : Type*) :=
  α → β → Prop -- deriving CompleteLattice, Inhabited
#align rel Rel

-- Porting note: `deriving` above doesn't work.
instance : CompleteLattice (Rel α β) := show CompleteLattice (α → β → Prop) from inferInstance
instance : Inhabited (Rel α β) := show Inhabited (α → β → Prop) from inferInstance

namespace Rel

variable (r : Rel α β)

-- Porting note: required for later theorems.
@[ext] theorem ext {r s : Rel α β} : (∀ a, r a = s a) → r = s := funext

/-- The inverse relation : `r.inv x y ↔ r y x`. Note that this is *not* a groupoid inverse. -/
def inv : Rel β α :=
  flip r
#align rel.inv Rel.inv

theorem inv_def (x : α) (y : β) : r.inv y x ↔ r x y :=
  Iff.rfl
#align rel.inv_def Rel.inv_def

theorem inv_inv : inv (inv r) = r := by
  ext x y
  rfl
#align rel.inv_inv Rel.inv_inv

/-- Domain of a relation -/
def dom := { x | ∃ y, r x y }
#align rel.dom Rel.dom

theorem dom_mono {r s : Rel α β} (h : r ≤ s) : dom r ⊆ dom s := fun a ⟨b, hx⟩ => ⟨b, h a b hx⟩
#align rel.dom_mono Rel.dom_mono

/-- Codomain aka range of a relation -/
def codom := { y | ∃ x, r x y }
#align rel.codom Rel.codom

theorem codom_inv : r.inv.codom = r.dom := by
  ext x
  rfl
#align rel.codom_inv Rel.codom_inv

theorem dom_inv : r.inv.dom = r.codom := by
  ext x
  rfl
#align rel.dom_inv Rel.dom_inv

/-- Composition of relation; note that it follows the `CategoryTheory/` order of arguments. -/
def comp (r : Rel α β) (s : Rel β γ) : Rel α γ := fun x z => ∃ y, r x y ∧ s y z
#align rel.comp Rel.comp

-- Porting note: the original `∘` syntax can't be overloaded here, lean considers it ambiguous.
/-- Local syntax for composition of relations. -/
local infixr:90 " • " => Rel.comp

theorem comp_assoc {δ : Type*} (r : Rel α β) (s : Rel β γ) (t : Rel γ δ) :
    (r • s) • t = r • (s • t) := by
  unfold comp; ext (x w); constructor
  · rintro ⟨z, ⟨y, rxy, syz⟩, tzw⟩; exact ⟨y, rxy, z, syz, tzw⟩
  · rintro ⟨y, rxy, z, syz, tzw⟩; exact ⟨z, ⟨y, rxy, syz⟩, tzw⟩
#align rel.comp_assoc Rel.comp_assoc

@[simp]
theorem comp_right_id (r : Rel α β) : r • @Eq β = r := by
  unfold comp
  ext y
  simp
#align rel.comp_right_id Rel.comp_right_id

@[simp]
theorem comp_left_id (r : Rel α β) : @Eq α • r = r := by
  unfold comp
  ext x
  simp
#align rel.comp_left_id Rel.comp_left_id

@[simp]
theorem comp_right_bot (r : Rel α β) : r • (⊥ : Rel β γ) = ⊥ := by
  ext x y
  simp [comp, Bot.bot]

@[simp]
theorem comp_left_bot (r : Rel α β) : (⊥ : Rel γ α) • r = ⊥ := by
  ext x y
  simp [comp, Bot.bot]

@[simp]
theorem comp_right_top (r : Rel α β) : r • (⊤ : Rel β γ) = fun x _ ↦ x ∈ r.dom := by
  ext x z
  simp [comp, Top.top, dom]

@[simp]
theorem comp_left_top (r : Rel α β) : (⊤ : Rel γ α) • r = fun _ y ↦ y ∈ r.codom := by
  ext x z
  simp [comp, Top.top, codom]

theorem inv_id : inv (@Eq α) = @Eq α := by
  ext x y
  constructor <;> apply Eq.symm
#align rel.inv_id Rel.inv_id

theorem inv_comp (r : Rel α β) (s : Rel β γ) : inv (r • s) = inv s • inv r := by
  ext x z
  simp [comp, inv, flip, and_comm]
#align rel.inv_comp Rel.inv_comp

@[simp]
theorem inv_bot : (⊥ : Rel α β).inv = (⊥ : Rel β α) := by
  #adaptation_note /-- nightly-2024-03-16: simp was `simp [Bot.bot, inv, flip]` -/
  simp [Bot.bot, inv, Function.flip_def]

@[simp]
theorem inv_top : (⊤ : Rel α β).inv = (⊤ : Rel β α) := by
  #adaptation_note /-- nightly-2024-03-16: simp was `simp [Top.top, inv, flip]` -/
  simp [Top.top, inv, Function.flip_def]

/-- Image of a set under a relation -/
def image (s : Set α) : Set β := { y | ∃ x ∈ s, r x y }
#align rel.image Rel.image

theorem mem_image (y : β) (s : Set α) : y ∈ image r s ↔ ∃ x ∈ s, r x y :=
  Iff.rfl
#align rel.mem_image Rel.mem_image

theorem image_subset : ((· ⊆ ·) ⇒ (· ⊆ ·)) r.image r.image := fun _ _ h _ ⟨x, xs, rxy⟩ =>
  ⟨x, h xs, rxy⟩
#align rel.image_subset Rel.image_subset

theorem image_mono : Monotone r.image :=
  r.image_subset
#align rel.image_mono Rel.image_mono

theorem image_inter (s t : Set α) : r.image (s ∩ t) ⊆ r.image s ∩ r.image t :=
  r.image_mono.map_inf_le s t
#align rel.image_inter Rel.image_inter

theorem image_union (s t : Set α) : r.image (s ∪ t) = r.image s ∪ r.image t :=
  le_antisymm
    (fun _y ⟨x, xst, rxy⟩ =>
      xst.elim (fun xs => Or.inl ⟨x, ⟨xs, rxy⟩⟩) fun xt => Or.inr ⟨x, ⟨xt, rxy⟩⟩)
    (r.image_mono.le_map_sup s t)
#align rel.image_union Rel.image_union

@[simp]
theorem image_id (s : Set α) : image (@Eq α) s = s := by
  ext x
  simp [mem_image]
#align rel.image_id Rel.image_id

theorem image_comp (s : Rel β γ) (t : Set α) : image (r • s) t = image s (image r t) := by
  ext z; simp only [mem_image]; constructor
  · rintro ⟨x, xt, y, rxy, syz⟩; exact ⟨y, ⟨x, xt, rxy⟩, syz⟩
  · rintro ⟨y, ⟨x, xt, rxy⟩, syz⟩; exact ⟨x, xt, y, rxy, syz⟩
#align rel.image_comp Rel.image_comp

theorem image_univ : r.image Set.univ = r.codom := by
  ext y
  simp [mem_image, codom]
#align rel.image_univ Rel.image_univ

@[simp]
theorem image_empty : r.image ∅ = ∅ := by
  ext x
  simp [mem_image]

@[simp]
theorem image_bot (s : Set α) : (⊥ : Rel α β).image s = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro x h
  simp [mem_image, Bot.bot] at h

@[simp]
theorem image_top {s : Set α} (h : Set.Nonempty s) :
    (⊤ : Rel α β).image s = Set.univ :=
  Set.eq_univ_of_forall fun x ↦ ⟨h.some, by simp [h.some_mem, Top.top]⟩

/-- Preimage of a set under a relation `r`. Same as the image of `s` under `r.inv` -/
def preimage (s : Set β) : Set α :=
  r.inv.image s
#align rel.preimage Rel.preimage

theorem mem_preimage (x : α) (s : Set β) : x ∈ r.preimage s ↔ ∃ y ∈ s, r x y :=
  Iff.rfl
#align rel.mem_preimage Rel.mem_preimage

theorem preimage_def (s : Set β) : preimage r s = { x | ∃ y ∈ s, r x y } :=
  Set.ext fun _ => mem_preimage _ _ _
#align rel.preimage_def Rel.preimage_def

theorem preimage_mono {s t : Set β} (h : s ⊆ t) : r.preimage s ⊆ r.preimage t :=
  image_mono _ h
#align rel.preimage_mono Rel.preimage_mono

theorem preimage_inter (s t : Set β) : r.preimage (s ∩ t) ⊆ r.preimage s ∩ r.preimage t :=
  image_inter _ s t
#align rel.preimage_inter Rel.preimage_inter

theorem preimage_union (s t : Set β) : r.preimage (s ∪ t) = r.preimage s ∪ r.preimage t :=
  image_union _ s t
#align rel.preimage_union Rel.preimage_union

theorem preimage_id (s : Set α) : preimage (@Eq α) s = s := by
  simp only [preimage, inv_id, image_id]
#align rel.preimage_id Rel.preimage_id

theorem preimage_comp (s : Rel β γ) (t : Set γ) :
    preimage (r • s) t = preimage r (preimage s t) := by simp only [preimage, inv_comp, image_comp]
#align rel.preimage_comp Rel.preimage_comp

theorem preimage_univ : r.preimage Set.univ = r.dom := by rw [preimage, image_univ, codom_inv]
#align rel.preimage_univ Rel.preimage_univ

@[simp]
theorem preimage_empty : r.preimage ∅ = ∅ := by rw [preimage, image_empty]

@[simp]
theorem preimage_inv (s : Set α) : r.inv.preimage s = r.image s := by rw [preimage, inv_inv]

@[simp]
theorem preimage_bot (s : Set β) : (⊥ : Rel α β).preimage s = ∅ := by
  rw [preimage, inv_bot, image_bot]

@[simp]
theorem preimage_top {s : Set β} (h : Set.Nonempty s) :
    (⊤ : Rel α β).preimage s = Set.univ := by rwa [← inv_top, preimage, inv_inv, image_top]

theorem image_eq_dom_of_codomain_subset {s : Set β} (h : r.codom ⊆ s) : r.preimage s = r.dom := by
  rw [← preimage_univ]
  apply Set.eq_of_subset_of_subset
  · exact image_subset _ (Set.subset_univ _)
  · intro x hx
    simp only [mem_preimage, Set.mem_univ, true_and] at hx
    rcases hx with ⟨y, ryx⟩
    have hy : y ∈ s := h ⟨x, ryx⟩
    exact ⟨y, ⟨hy, ryx⟩⟩

theorem preimage_eq_codom_of_domain_subset {s : Set α} (h : r.dom ⊆ s) : r.image s = r.codom := by
  apply r.inv.image_eq_dom_of_codomain_subset (by rwa [← codom_inv] at h)

theorem image_inter_dom_eq (s : Set α) : r.image (s ∩ r.dom) = r.image s := by
  apply Set.eq_of_subset_of_subset
  · apply r.image_mono (by simp)
  · intro x h
    rw [mem_image] at *
    rcases h with ⟨y, hy, ryx⟩
    use y
    suffices h : y ∈ r.dom by simp_all only [Set.mem_inter_iff, and_self]
    rw [dom, Set.mem_setOf_eq]
    use x

@[simp]
theorem preimage_inter_codom_eq (s : Set β) : r.preimage (s ∩ r.codom) = r.preimage s := by
  rw [← dom_inv, preimage, preimage, image_inter_dom_eq]

theorem inter_dom_subset_preimage_image (s : Set α) : s ∩ r.dom ⊆ r.preimage (r.image s) := by
  intro x hx
  simp only [Set.mem_inter_iff, dom] at hx
  rcases hx with ⟨hx, ⟨y, rxy⟩⟩
  use y
  simp only [image, Set.mem_setOf_eq]
  exact ⟨⟨x, hx, rxy⟩, rxy⟩

theorem image_preimage_subset_inter_codom (s : Set β) : s ∩ r.codom ⊆ r.image (r.preimage s) := by
  rw [← dom_inv, ← preimage_inv]
  apply inter_dom_subset_preimage_image

/-- Core of a set `s : Set β` w.r.t `r : Rel α β` is the set of `x : α` that are related *only*
to elements of `s`. Other generalization of `Function.preimage`. -/
def core (s : Set β) := { x | ∀ y, r x y → y ∈ s }
#align rel.core Rel.core

theorem mem_core (x : α) (s : Set β) : x ∈ r.core s ↔ ∀ y, r x y → y ∈ s :=
  Iff.rfl
#align rel.mem_core Rel.mem_core

theorem core_subset : ((· ⊆ ·) ⇒ (· ⊆ ·)) r.core r.core := fun _s _t h _x h' y rxy => h (h' y rxy)
#align rel.core_subset Rel.core_subset

theorem core_mono : Monotone r.core :=
  r.core_subset
#align rel.core_mono Rel.core_mono

theorem core_inter (s t : Set β) : r.core (s ∩ t) = r.core s ∩ r.core t :=
  Set.ext (by simp [mem_core, imp_and, forall_and])
#align rel.core_inter Rel.core_inter

theorem core_union (s t : Set β) : r.core s ∪ r.core t ⊆ r.core (s ∪ t) :=
  r.core_mono.le_map_sup s t
#align rel.core_union Rel.core_union

@[simp]
theorem core_univ : r.core Set.univ = Set.univ :=
  Set.ext (by simp [mem_core])
#align rel.core_univ Rel.core_univ

theorem core_id (s : Set α) : core (@Eq α) s = s := by simp [core]
#align rel.core_id Rel.core_id

theorem core_comp (s : Rel β γ) (t : Set γ) : core (r • s) t = core r (core s t) := by
  ext x; simp only [core, comp, forall_exists_index, and_imp, Set.mem_setOf_eq]; constructor
  · exact fun h y rxy z => h z y rxy
  · exact fun h z y rzy => h y rzy z
#align rel.core_comp Rel.core_comp

/-- Restrict the domain of a relation to a subtype. -/
def restrictDomain (s : Set α) : Rel { x // x ∈ s } β := fun x y => r x.val y
#align rel.restrict_domain Rel.restrictDomain

theorem image_subset_iff (s : Set α) (t : Set β) : image r s ⊆ t ↔ s ⊆ core r t :=
  Iff.intro (fun h x xs _y rxy => h ⟨x, xs, rxy⟩) fun h y ⟨_x, xs, rxy⟩ => h xs y rxy
#align rel.image_subset_iff Rel.image_subset_iff

theorem image_core_gc : GaloisConnection r.image r.core :=
  image_subset_iff _
#align rel.image_core_gc Rel.image_core_gc

end Rel

namespace Function

/-- The graph of a function as a relation. -/
def graph (f : α → β) : Rel α β := fun x y => f x = y
#align function.graph Function.graph

@[simp] lemma graph_def (f : α → β) (x y) : f.graph x y ↔ (f x = y) := Iff.rfl

theorem graph_injective : Injective (graph : (α → β) → Rel α β) := by
  intro _ g h
  ext x
  have h2 := congr_fun₂ h x (g x)
  simp only [graph_def, eq_iff_iff, iff_true] at h2
  exact h2

@[simp] lemma graph_inj {f g : α → β} : f.graph = g.graph ↔ f = g := graph_injective.eq_iff

theorem graph_id : graph id = @Eq α := by simp  (config := { unfoldPartialApp := true }) [graph]

theorem graph_comp {f : β → γ} {g : α → β} : graph (f ∘ g) = Rel.comp (graph g) (graph f) := by
  ext x y
  simp [Rel.comp]

end Function

theorem Equiv.graph_inv (f : α ≃ β) : (f.symm : β → α).graph = Rel.inv (f : α → β).graph := by
  ext x y
  aesop (add norm Rel.inv_def)

theorem Relation.is_graph_iff (r : Rel α β) : (∃! f, Function.graph f = r) ↔ ∀ x, ∃! y, r x y := by
  unfold Function.graph
  constructor
  · rintro ⟨f, rfl, _⟩ x
    use f x
    simp only [forall_eq', and_self]
  · intro h
    choose f hf using fun x ↦ (h x).exists
    use f
    constructor
    · ext x _
      constructor
      · rintro rfl
        exact hf x
      · exact (h x).unique (hf x)
    · rintro _ rfl
      exact funext hf

namespace Set

theorem image_eq (f : α → β) (s : Set α) : f '' s = (Function.graph f).image s := by
  rfl
#align set.image_eq Set.image_eq

theorem preimage_eq (f : α → β) (s : Set β) : f ⁻¹' s = (Function.graph f).preimage s := by
  simp [Set.preimage, Rel.preimage, Rel.inv, flip, Rel.image]
#align set.preimage_eq Set.preimage_eq

theorem preimage_eq_core (f : α → β) (s : Set β) : f ⁻¹' s = (Function.graph f).core s := by
  simp [Set.preimage, Rel.core]
#align set.preimage_eq_core Set.preimage_eq_core

end Set
