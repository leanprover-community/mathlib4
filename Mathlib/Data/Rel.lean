/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Order.CompleteLattice
import Mathlib.Order.GaloisConnection

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
-/

set_option autoImplicit true


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
  -- ⊢ inv (inv r) x y ↔ r x y
  rfl
  -- 🎉 no goals
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
  -- ⊢ x ∈ codom (inv r) ↔ x ∈ dom r
  rfl
  -- 🎉 no goals
#align rel.codom_inv Rel.codom_inv

theorem dom_inv : r.inv.dom = r.codom := by
  ext x
  -- ⊢ x ∈ dom (inv r) ↔ x ∈ codom r
  rfl
  -- 🎉 no goals
#align rel.dom_inv Rel.dom_inv

/-- Composition of relation; note that it follows the `CategoryTheory/` order of arguments. -/
def comp (r : Rel α β) (s : Rel β γ) : Rel α γ := fun x z => ∃ y, r x y ∧ s y z
#align rel.comp Rel.comp

-- Porting note: the original `∘` syntax can't be overloaded here, lean considers it ambiguous.
-- TODO: Change this syntax to something nicer?
/-- Local syntax for composition of relations. -/
local infixr:90 " • " => Rel.comp

theorem comp_assoc (r : Rel α β) (s : Rel β γ) (t : Rel γ δ) : (r • s) • t = r • (s • t) := by
  unfold comp; ext (x w); constructor
  -- ⊢ (fun x z => ∃ y, (∃ y_1, r x y_1 ∧ s y_1 y) ∧ t y z) = fun x z => ∃ y, r x y …
               -- ⊢ (∃ y, (∃ y_1, r x y_1 ∧ s y_1 y) ∧ t y w) ↔ ∃ y, r x y ∧ ∃ y_1, s y y_1 ∧ t  …
                          -- ⊢ (∃ y, (∃ y_1, r x y_1 ∧ s y_1 y) ∧ t y w) → ∃ y, r x y ∧ ∃ y_1, s y y_1 ∧ t  …
  · rintro ⟨z, ⟨y, rxy, syz⟩, tzw⟩; exact ⟨y, rxy, z, syz, tzw⟩
    -- ⊢ ∃ y, r x y ∧ ∃ y_1, s y y_1 ∧ t y_1 w
                                    -- 🎉 no goals
  · rintro ⟨y, rxy, z, syz, tzw⟩; exact ⟨z, ⟨y, rxy, syz⟩, tzw⟩
    -- ⊢ ∃ y, (∃ y_1, r x y_1 ∧ s y_1 y) ∧ t y w
                                  -- 🎉 no goals
#align rel.comp_assoc Rel.comp_assoc

@[simp]
theorem comp_right_id (r : Rel α β) : r • @Eq β = r := by
  unfold comp
  -- ⊢ (fun x z => ∃ y, r x y ∧ y = z) = r
  ext y
  -- ⊢ (∃ y_1, r y y_1 ∧ y_1 = x✝) ↔ r y x✝
  simp
  -- 🎉 no goals
#align rel.comp_right_id Rel.comp_right_id

@[simp]
theorem comp_left_id (r : Rel α β) : @Eq α • r = r := by
  unfold comp
  -- ⊢ (fun x z => ∃ y, x = y ∧ r y z) = r
  ext x
  -- ⊢ (∃ y, x = y ∧ r y x✝) ↔ r x x✝
  simp
  -- 🎉 no goals
#align rel.comp_left_id Rel.comp_left_id

theorem inv_id : inv (@Eq α) = @Eq α := by
  ext x y
  -- ⊢ inv Eq x y ↔ x = y
  constructor <;> apply Eq.symm
  -- ⊢ inv Eq x y → x = y
                  -- 🎉 no goals
                  -- 🎉 no goals
#align rel.inv_id Rel.inv_id

theorem inv_comp (r : Rel α β) (s : Rel β γ) : inv (r • s) = inv s • inv r := by
  ext x z
  -- ⊢ inv (r • s) x z ↔ (inv s • inv r) x z
  simp [comp, inv, flip, and_comm]
  -- 🎉 no goals
#align rel.inv_comp Rel.inv_comp

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
  -- ⊢ x ∈ image Eq s ↔ x ∈ s
  simp [mem_image]
  -- 🎉 no goals
#align rel.image_id Rel.image_id

theorem image_comp (s : Rel β γ) (t : Set α) : image (r • s) t = image s (image r t) := by
  ext z; simp only [mem_image]; constructor
  -- ⊢ z ∈ image (r • s) t ↔ z ∈ image s (image r t)
         -- ⊢ (∃ x, x ∈ t ∧ (r • s) x z) ↔ ∃ x, (∃ x_1, x_1 ∈ t ∧ r x_1 x) ∧ s x z
                                -- ⊢ (∃ x, x ∈ t ∧ (r • s) x z) → ∃ x, (∃ x_1, x_1 ∈ t ∧ r x_1 x) ∧ s x z
  · rintro ⟨x, xt, y, rxy, syz⟩; exact ⟨y, ⟨x, xt, rxy⟩, syz⟩
    -- ⊢ ∃ x, (∃ x_1, x_1 ∈ t ∧ r x_1 x) ∧ s x z
                                 -- 🎉 no goals
  · rintro ⟨y, ⟨x, xt, rxy⟩, syz⟩; exact ⟨x, xt, y, rxy, syz⟩
    -- ⊢ ∃ x, x ∈ t ∧ (r • s) x z
                                   -- 🎉 no goals
#align rel.image_comp Rel.image_comp

theorem image_univ : r.image Set.univ = r.codom := by
  ext y
  -- ⊢ y ∈ image r Set.univ ↔ y ∈ codom r
  simp [mem_image, codom]
  -- 🎉 no goals
#align rel.image_univ Rel.image_univ

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
  -- 🎉 no goals
#align rel.preimage_id Rel.preimage_id

theorem preimage_comp (s : Rel β γ) (t : Set γ) : preimage (r • s) t = preimage r (preimage s t) :=
  by simp only [preimage, inv_comp, image_comp]
     -- 🎉 no goals
#align rel.preimage_comp Rel.preimage_comp

theorem preimage_univ : r.preimage Set.univ = r.dom := by rw [preimage, image_univ, codom_inv]
                                                          -- 🎉 no goals
#align rel.preimage_univ Rel.preimage_univ

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
              -- 🎉 no goals
#align rel.core_inter Rel.core_inter

theorem core_union (s t : Set β) : r.core s ∪ r.core t ⊆ r.core (s ∪ t) :=
  r.core_mono.le_map_sup s t
#align rel.core_union Rel.core_union

@[simp]
theorem core_univ : r.core Set.univ = Set.univ :=
  Set.ext (by simp [mem_core])
              -- 🎉 no goals
#align rel.core_univ Rel.core_univ

theorem core_id (s : Set α) : core (@Eq α) s = s := by simp [core]
                                                       -- 🎉 no goals
#align rel.core_id Rel.core_id

theorem core_comp (s : Rel β γ) (t : Set γ) : core (r • s) t = core r (core s t) := by
  ext x; simp [core, comp]; constructor
  -- ⊢ x ∈ core (r • s) t ↔ x ∈ core r (core s t)
         -- ⊢ (∀ (y : γ) (x_1 : β), r x x_1 → s x_1 y → y ∈ t) ↔ ∀ (y : β), r x y → ∀ (y_1 …
                            -- ⊢ (∀ (y : γ) (x_1 : β), r x x_1 → s x_1 y → y ∈ t) → ∀ (y : β), r x y → ∀ (y_1 …
  · exact fun h y rxy z => h z y rxy
    -- 🎉 no goals
  · exact fun h z y rzy => h y rzy z
    -- 🎉 no goals
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

end Function

namespace Set

-- TODO: if image were defined with bounded quantification in corelib, the next two would
-- be definitional
theorem image_eq (f : α → β) (s : Set α) : f '' s = (Function.graph f).image s := by
  simp [Set.image, Function.graph, Rel.image]
  -- 🎉 no goals
#align set.image_eq Set.image_eq

theorem preimage_eq (f : α → β) (s : Set β) : f ⁻¹' s = (Function.graph f).preimage s := by
  simp [Set.preimage, Function.graph, Rel.preimage, Rel.inv, flip, Rel.image]
  -- 🎉 no goals
#align set.preimage_eq Set.preimage_eq

theorem preimage_eq_core (f : α → β) (s : Set β) : f ⁻¹' s = (Function.graph f).core s := by
  simp [Set.preimage, Function.graph, Rel.core]
  -- 🎉 no goals
#align set.preimage_eq_core Set.preimage_eq_core

end Set
