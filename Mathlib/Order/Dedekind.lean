/-
Copyright (c) 2025 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson, Violeta Hernández Palacios
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.CompleteLattice.Defs

/-!
# Dedekind-MacNeille completion

The Dedekind-MacNeille completion of a partial order is the smallest complete lattice into which it
embeds.

We provide an explicit construction, as the set of "lower cuts" of the order, meaning sets with
`lowerBounds (upperBounds s) = s`. The dual construction as upper cuts, or sets with
`upperBounds (lowerBounds s) = s` would also work; keeping this in mind, we keep the API symmetric.

The construction `DedekindCut.factorEmbedding` and the theorem `DedekindCut.factorEmbedding_factors`
formalize the notion that `DedekindCut α` is the "smallest" complete lattice containing `α`.

## Todo

- Build the order isomorphism `DedekindCut ℚ ≃o ℝ`.
-/

open Set

variable {α β γ : Type*} {s t : Set α} [Preorder α] [PartialOrder β]

/-! ### Lower cuts and upper cuts -/

/-- The set of lower cuts in a preorder is the set of sets with
`lowerBounds (upperBounds s) ⊆ s`.

The theorem `mem_lowerCuts_iff_eq` shows the equivalence to the condition
`lowerBounds (upperBounds s) = s` -/
def lowerCuts (α : Type*) [Preorder α] : Set (Set α) :=
  {s | lowerBounds (upperBounds s) ⊆ s}

theorem mem_lowerCuts_iff_eq : s ∈ lowerCuts α ↔ lowerBounds (upperBounds s) = s := by
  rw [lowerCuts, subset_antisymm_iff]
  simp [subset_lowerBounds_upperBounds]

theorem inter_mem_lowerCuts (hs : s ∈ lowerCuts α) (ht : t ∈ lowerCuts α) : s ∩ t ∈ lowerCuts α :=
  fun _ ha ↦ ⟨hs fun _ hb ↦ ha fun _ ⟨hc, _⟩ ↦ hb hc, ht fun _ hb ↦ ha fun _ ⟨_, hc⟩ ↦ hb hc⟩

theorem sInter_mem_lowerCuts {S : Set (Set α)} (hS : S ⊆ lowerCuts α) : ⋂₀ S ∈ lowerCuts α := by
  intro a ha t ht
  rw [← mem_lowerCuts_iff_eq.mp (hS ht)]
  exact fun _ hb ↦ ha fun _ hc ↦ hb (hc _ ht)

theorem Iic_mem_lowerCuts (a : α) : Iic a ∈ lowerCuts α := fun _ hb ↦ hb fun _ ↦ id

/-- The set of lower cuts in a preorder is the set of sets with
`upperBounds (lowerBounds s) ⊆ s`.

The theorem `mem_upperCuts_iff_eq` shows the equivalence to the condition
`upperBounds (lowerBounds s) = s` -/
def upperCuts (α : Type*) [Preorder α] : Set (Set α) :=
  {s | upperBounds (lowerBounds s) ⊆ s}

theorem mem_upperCuts_iff_eq : s ∈ upperCuts α ↔ upperBounds (lowerBounds s) = s :=
  mem_lowerCuts_iff_eq (α := αᵒᵈ)

theorem inter_mem_upperCuts (hs : s ∈ upperCuts α) (ht : t ∈ upperCuts α) : s ∩ t ∈ upperCuts α :=
  inter_mem_lowerCuts (α := αᵒᵈ) hs ht

theorem sInter_mem_upperCuts {S : Set (Set α)} (hS : S ⊆ upperCuts α) : ⋂₀ S ∈ upperCuts α :=
  sInter_mem_lowerCuts (α := αᵒᵈ) hS

theorem Ici_mem_lowerCuts (a : α) : Iic a ∈ lowerCuts α := fun _ hb ↦ hb fun _ ↦ id

theorem upperBounds_mem_upperCuts_of_mem_lowerCuts (H : s ∈ lowerCuts α) :
    upperBounds s ∈ upperCuts α := by
  simp_all [mem_upperCuts_iff_eq, mem_lowerCuts_iff_eq]

theorem lowerBounds_mem_lowerCuts_of_mem_upperCuts (H : s ∈ upperCuts α) :
    lowerBounds s ∈ lowerCuts α := by
  simp_all [mem_upperCuts_iff_eq, mem_lowerCuts_iff_eq]

/-! ### Dedekind cuts -/

/-- A Dedekind cut (in the Dedekind-MacNeille completion) is a defined as a member of `lowerCuts α`.

Use `DedekindCut.of_lowerCuts` to define a member of this structure. For the dual definition through
`upperCuts`, use `DedekindCut.of_upperCuts`. -/
structure DedekindCut (α : Type*) [Preorder α] where
  carrier : Set α
  carrier_mem_lowerCuts : carrier ∈ lowerCuts α

namespace DedekindCut

variable (A B : DedekindCut α)

/- The lower set in a Dedekind cut. -/
def lowerCut : Set α := A.carrier

theorem lowerCut_mem_lowerCuts : A.lowerCut ∈ lowerCuts α :=
  A.carrier_mem_lowerCuts

@[simp]
theorem lowerCut_eq : lowerBounds (upperBounds A.lowerCut) = A.lowerCut :=
  mem_lowerCuts_iff_eq.mp A.lowerCut_mem_lowerCuts

/- The upper set in a Dedekind cut. -/
def upperCut : Set α := upperBounds A.lowerCut

@[simp]
theorem upperCut_eq : upperBounds (lowerBounds A.upperCut) = A.upperCut := by
  rw [upperCut, lowerCut_eq]

theorem upperCut_mem_upperCuts : A.upperCut ∈ upperCuts α :=
  mem_upperCuts_iff_eq.mpr A.upperCut_eq

@[simp]
theorem upperBounds_lowerCut : upperBounds A.lowerCut = A.upperCut :=
  rfl

@[simp]
theorem lowerBounds_upperCut : lowerBounds A.upperCut = A.lowerCut := by
  rw [← upperBounds_lowerCut, lowerCut_eq]

/-- Build a Dedekind cut from its lower set. -/
def of_lowerCuts (s : Set α) (hs : s ∈ lowerCuts α) : DedekindCut α :=
  ⟨s, hs⟩

@[simp]
theorem lowerCut_of_lowerCuts (hs : s ∈ lowerCuts α) : lowerCut (of_lowerCuts s hs) = s :=
  rfl

@[simp]
theorem upperCut_of_lowerCuts (hs : s ∈ lowerCuts α) :
    upperCut (of_lowerCuts s hs) = upperBounds s :=
  rfl

/-- Build a Dedekind cut from its upper set. -/
def of_upperCuts (s : Set α) (hs : s ∈ upperCuts α) : DedekindCut α :=
  ⟨_, lowerBounds_mem_lowerCuts_of_mem_upperCuts hs⟩

@[simp]
theorem lowerCut_of_upperCuts (hs : s ∈ upperCuts α) :
    lowerCut (of_upperCuts s hs) = lowerBounds s :=
  rfl

@[simp]
theorem upperCut_of_upperCuts (hs : s ∈ upperCuts α) :
    upperCut (of_upperCuts s hs) = s :=
  mem_upperCuts_iff_eq.mp hs

variable {A B}

theorem lowerCut_subset_iff_subset_upperCut :
    A.lowerCut ⊆ B.lowerCut ↔ B.upperCut ⊆ A.upperCut where
  mp  H := by simpa using fun a ha ↦ upperBounds_mono_set H ha
  mpr H := by simpa using fun a ha ↦ lowerBounds_mono_set H ha

theorem lowerCut_ssubset_iff_ssubset_upperCut :
    A.lowerCut ⊂ B.lowerCut ↔ B.upperCut ⊂ A.upperCut := by
  simp [ssubset_def, lowerCut_subset_iff_subset_upperCut]

theorem lowerCut_eq_iff_upperCut_eq : A.lowerCut = B.lowerCut ↔ A.upperCut = B.upperCut := by
  simp [subset_antisymm_iff, lowerCut_subset_iff_subset_upperCut, and_comm]

theorem lowerCut_le_upperCut {x y : α} (hx : x ∈ A.lowerCut) (hy : y ∈ A.upperCut) : x ≤ y := by
  rw [← upperBounds_lowerCut] at hy
  exact hy hx

variable (A) in
theorem image_lowerCut_subset_lowerBounds {β : Type*} [Preorder β] {f : α → β} (hf : Monotone f) :
    f '' A.lowerCut ⊆ lowerBounds (f '' A.upperCut) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf <| lowerCut_le_upperCut hx hy

variable (A) in
theorem image_upperCut_subset_upperBounds {β : Type*} [Preorder β] {f : α → β} (hf : Monotone f) :
    f '' A.upperCut ⊆ upperBounds (f '' A.lowerCut) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf <| lowerCut_le_upperCut hy hx

@[ext (iff := false)]
theorem ext_lowerCut (h : A.lowerCut = B.lowerCut) : A = B := by
  cases A; cases B; simpa

theorem ext_lowerCut_iff : A = B ↔ A.lowerCut = B.lowerCut :=
  ⟨congrArg _, ext_lowerCut⟩

theorem ext_upperCut (h : A.upperCut = B.upperCut) : A = B :=
  ext_lowerCut (lowerCut_eq_iff_upperCut_eq.mpr h)

theorem ext_upperCut_iff : A = B ↔ A.upperCut = B.upperCut :=
  ⟨congrArg _, ext_upperCut⟩

/- ### Order instances -/

instance : LE (DedekindCut α) where
  le A B := A.lowerCut ⊆ B.lowerCut

instance : InfSet (DedekindCut α) where
  sInf X := .of_lowerCuts (⋂₀ (lowerCut '' X)) <| by
    apply sInter_mem_lowerCuts
    rintro A ⟨B, hB, rfl⟩
    exact lowerCut_mem_lowerCuts B

instance : Min (DedekindCut α) where
  min A B := .of_lowerCuts (A.lowerCut ∩ B.lowerCut) <| by
    apply inter_mem_lowerCuts <;> exact lowerCut_mem_lowerCuts _

instance : SupSet (DedekindCut α) where
  sSup X := .of_upperCuts (⋂₀ (upperCut '' X)) <| by
    apply sInter_mem_upperCuts
    rintro A ⟨B, hB, rfl⟩
    exact upperCut_mem_upperCuts B

instance : Max (DedekindCut α) where
  max A B := .of_upperCuts (A.upperCut ∩ B.upperCut) <| by
    apply inter_mem_upperCuts <;> exact upperCut_mem_upperCuts _

instance : Bot (DedekindCut α) where
  bot := sInf univ

instance : Top (DedekindCut α) where
  top := sSup univ

theorem le_iff_lowerCut_subset : A ≤ B ↔ A.lowerCut ⊆ B.lowerCut := .rfl
theorem le_iff_upperCut_subset : A ≤ B ↔ B.upperCut ⊆ A.upperCut := by
  rw [le_iff_lowerCut_subset, lowerCut_subset_iff_subset_upperCut]

theorem lowerCut_sInf (X : Set (DedekindCut α)) : (sInf X).lowerCut = ⋂₀ (lowerCut '' X) := rfl
theorem upperCut_sSup (X : Set (DedekindCut α)) : (sSup X).upperCut = ⋂₀ (upperCut '' X) :=
  upperCut_of_upperCuts ..

theorem lowerCut_inf (A B : DedekindCut α) : (A ⊓ B).lowerCut = A.lowerCut ∩ B.lowerCut := rfl
theorem upperCut_sup (A B : DedekindCut α) : (A ⊔ B).upperCut = A.upperCut ∩ B.upperCut :=
  upperCut_of_upperCuts ..

theorem lowerCut_bot : (⊥ : DedekindCut α).lowerCut = ⋂₀ (lowerCut '' univ) := rfl
theorem upperCut_top : (⊤ : DedekindCut α).upperCut = ⋂₀ (upperCut '' univ) :=
  upperCut_of_upperCuts ..

instance : CompleteLattice (DedekindCut α) where
  sup := max
  inf := min
  le_refl _ := .rfl
  le_trans _ _ _ := subset_trans
  le_antisymm _ _:= by simp_all [ext_lowerCut_iff, subset_antisymm_iff, le_iff_lowerCut_subset]
  le_inf A B C := le_inf (a := A.lowerCut)
  inf_le_left A B := inf_le_left (a := A.lowerCut)
  inf_le_right A B := inf_le_right (a := A.lowerCut)
  sup_le A B C := by simp_rw [le_iff_upperCut_subset, upperCut_sup]; exact le_inf
  le_sup_left A B := by rw [le_iff_upperCut_subset, upperCut_sup]; exact inf_le_left
  le_sup_right A B := by rw [le_iff_upperCut_subset, upperCut_sup]; exact inf_le_right
  sInf_le X A hA := sInter_subset_of_mem (mem_image_of_mem _ hA)
  le_sInf X A H := by rintro B hB _ ⟨C, hC, rfl⟩; exact H _ hC hB
  le_sSup X A hA := by
    rw [le_iff_upperCut_subset, upperCut_sSup]
    exact sInter_subset_of_mem (mem_image_of_mem _ hA)
  sSup_le X A H := by
    rw [le_iff_upperCut_subset, upperCut_sSup]
    simp_rw [le_iff_upperCut_subset] at H
    rintro B hB _ ⟨C, hC, rfl⟩
    exact H _ hC hB
  bot_le A := sInter_subset_of_mem (mem_image_of_mem _ ⟨⟩)
  le_top A := by
    rw [le_iff_upperCut_subset, upperCut_top]
    exact sInter_subset_of_mem (mem_image_of_mem _ ⟨⟩)

/-! ### Order embedding -/

/-- Convert an element into its Dedekind cut (`Iic a`, `Ici a`). -/
def ofElement (a : α) : DedekindCut α :=
  .of_lowerCuts _ (Iic_mem_lowerCuts a)

@[simp]
theorem lowerCut_ofElement (a : α) : (ofElement a).lowerCut = Iic a := rfl

@[simp]
theorem upperCut_ofElement (a : α) : (ofElement a).upperCut = Ici a := by
  rw [← upperBounds_lowerCut, lowerCut_ofElement, upperBounds_Iic]

@[simp]
theorem ofElement_le_ofElement {a b : α} :
    ofElement a ≤ ofElement b ↔ a ≤ b := by
  simp [le_iff_lowerCut_subset]

/-- `ofElement` is injective up to antisymmetry. -/
theorem ofElement_eq_ofElement {a b : α} :
    ofElement a = ofElement b ↔ AntisymmRel (· ≤ ·) a b := by
  simp [le_antisymm_iff, AntisymmRel]

/-- `ofElement` as an `OrderHom`.

In the case of a partial order, this can be strengthened to an `OrderEmbedding`, see
`Order.ofElementEmbedding`. -/
@[simps!]
def ofElementHom : α →o DedekindCut α where
  toFun := ofElement
  monotone' _ _ := ofElement_le_ofElement.2

@[simp] theorem ofElementHom_coe : ⇑(@ofElementHom α _) = ofElement := rfl

@[simp]
theorem ofElement_inj {a b : β} : ofElement a = ofElement b ↔ a = b := by
  simp [le_antisymm_iff]

/-- `Order.ofElement` as an `OrderEmbedding`. -/
@[simps!]
def ofElementEmbedding : β ↪o DedekindCut β where
  toFun := ofElement
  inj' _ _ := ofElement_inj.1
  map_rel_iff' := ofElement_le_ofElement

@[simp] theorem ofElementEmbedding_coe : ⇑(@ofElementEmbedding β _) = ofElement := rfl

variable [CompleteLattice γ]

/-- Any order embedding `β ↪o γ` into a complete lattice factors through `DedekindCut β`. -/
def factorEmbedding (f : β ↪o γ) : DedekindCut β ↪o γ :=
  .ofMapLEIff (fun A ↦ sSup (f '' A.lowerCut)) <| by
    refine fun A B ↦ ⟨fun h x hx ↦ ?_, fun h ↦ sSup_le_sSup (image_mono h)⟩
    rw [← lowerBounds_upperCut, lowerBounds]
    simp_rw [le_sSup_iff, sSup_le_iff, forall_mem_image] at h
    intro y hy
    rw [← f.le_iff_le]
    exact h _ (image_upperCut_subset_upperBounds _ f.monotone (mem_image_of_mem _ hy)) hx

/-- Note that `factorEmbedding f A = sInf (f '' A.upperCut)` is not necessarily true! -/
theorem factorEmbedding_apply (f : β ↪o γ) (A : DedekindCut β) :
    factorEmbedding f A = sSup (f '' A.lowerCut) :=
  rfl

@[simp]
theorem factorEmbedding_ofElement (f : β ↪o γ) (x : β) : factorEmbedding f (ofElement x) = f x := by
  rw [factorEmbedding_apply]
  apply le_antisymm
  · simp
  · rw [le_sSup_iff]
    refine fun y hy ↦ hy ?_
    simp

/-- The Dedekind-MacNeille completion of a partial order is the smallest complete lattice containing
it, in the sense that any embedding into any complete lattice factors through it. -/
theorem factorEmbedding_factors (f : β ↪o γ) :
    ofElementEmbedding.trans (factorEmbedding f) = f := by
  ext; simp

end DedekindCut
