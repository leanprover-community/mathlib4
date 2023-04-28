/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies

! This file was ported from Lean 3 source module order.complete_boolean_algebra
! leanprover-community/mathlib commit 71b36b6f3bbe3b44e6538673819324d3ee9fcc96
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.CompleteLattice
import Mathlib.Order.Directed
import Mathlib.Logic.Equiv.Set

/-!
# Frames, completely distributive lattices and Boolean algebras

In this file we define and provide API for frames, completely distributive lattices and completely
distributive Boolean algebras.

## Typeclasses

* `Order.Frame`: Frame: A complete lattice whose `⊓` distributes over `⨆`.
* `Order.Coframe`: Coframe: A complete lattice whose `⊔` distributes over `⨅`.
* `CompleteDistribLattice`: Completely distributive lattices: A complete lattice whose `⊓` and `⊔`
  distribute over `⨆` and `⨅` respectively.
* `CompleteBooleanAlgebra`: Completely distributive Boolean algebra: A Boolean algebra whose `⊓`
  and `⊔` distribute over `⨆` and `⨅` respectively.

A set of opens gives rise to a topological space precisely if it forms a frame. Such a frame is also
completely distributive, but not all frames are. `Filter` is a coframe but not a completely
distributive lattice.

## TODO

Add instances for `Prod`

## References

* [Wikipedia, *Complete Heyting algebra*](https://en.wikipedia.org/wiki/Complete_Heyting_algebra)
* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]
-/


open Function Set

universe u v w

variable {α : Type u} {β : Type v} {ι : Sort w} {κ : ι → Sort _}

/-- A frame, aka complete Heyting algebra, is a complete lattice whose `⊓` distributes over `⨆`. -/
class Order.Frame (α : Type _) extends CompleteLattice α where
  inf_supₛ_le_supᵢ_inf (a : α) (s : Set α) : a ⊓ supₛ s ≤ ⨆ b ∈ s, a ⊓ b
#align order.frame Order.Frame

/-- In a frame, `⊓` distributes over `⨆`. -/
add_decl_doc Order.Frame.inf_supₛ_le_supᵢ_inf

/-- A coframe, aka complete Brouwer algebra or complete co-Heyting algebra, is a complete lattice
whose `⊔` distributes over `⨅`. -/
class Order.Coframe (α : Type _) extends CompleteLattice α where
  infᵢ_sup_le_sup_infₛ (a : α) (s : Set α) : (⨅ b ∈ s, a ⊔ b) ≤ a ⊔ infₛ s
#align order.coframe Order.Coframe

/-- In a coframe, `⊔` distributes over `⨅`. -/
add_decl_doc Order.Coframe.infᵢ_sup_le_sup_infₛ

open Order

/-- A completely distributive lattice is a complete lattice whose `⊔` and `⊓` respectively
distribute over `⨅` and `⨆`. -/
class CompleteDistribLattice (α : Type _) extends Frame α where
  infᵢ_sup_le_sup_infₛ : ∀ a s, (⨅ b ∈ s, a ⊔ b) ≤ a ⊔ infₛ s
#align complete_distrib_lattice CompleteDistribLattice

/-- In a completely distributive lattice, `⊔` distributes over `⨅`. -/
add_decl_doc CompleteDistribLattice.infᵢ_sup_le_sup_infₛ

-- See note [lower instance priority]
instance (priority := 100) CompleteDistribLattice.toCoframe [CompleteDistribLattice α] :
    Coframe α :=
  { ‹CompleteDistribLattice α› with }
#align complete_distrib_lattice.to_coframe CompleteDistribLattice.toCoframe

section Frame

variable [Frame α] {s t : Set α} {a b : α}

instance OrderDual.coframe : Coframe αᵒᵈ :=
  { OrderDual.completeLattice α with infᵢ_sup_le_sup_infₛ := @Frame.inf_supₛ_le_supᵢ_inf α _ }
#align order_dual.coframe OrderDual.coframe

theorem inf_supₛ_eq : a ⊓ supₛ s = ⨆ b ∈ s, a ⊓ b :=
  (Frame.inf_supₛ_le_supᵢ_inf _ _).antisymm supᵢ_inf_le_inf_supₛ
#align inf_Sup_eq inf_supₛ_eq

theorem supₛ_inf_eq : supₛ s ⊓ b = ⨆ a ∈ s, a ⊓ b := by
  simpa only [inf_comm] using @inf_supₛ_eq α _ s b
#align Sup_inf_eq supₛ_inf_eq

theorem supᵢ_inf_eq (f : ι → α) (a : α) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a := by
  rw [supᵢ, supₛ_inf_eq, supᵢ_range]
#align supr_inf_eq supᵢ_inf_eq

theorem inf_supᵢ_eq (a : α) (f : ι → α) : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  simpa only [inf_comm] using supᵢ_inf_eq f a
#align inf_supr_eq inf_supᵢ_eq

theorem supᵢ₂_inf_eq {f : ∀ i, κ i → α} (a : α) : (⨆ (i) (j), f i j) ⊓ a = ⨆ (i) (j), f i j ⊓ a :=
  by simp only [supᵢ_inf_eq]
#align bsupr_inf_eq supᵢ₂_inf_eq

theorem inf_supᵢ₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊓ ⨆ (i) (j), f i j) = ⨆ (i) (j), a ⊓ f i j :=
  by simp only [inf_supᵢ_eq]
#align inf_bsupr_eq inf_supᵢ₂_eq

theorem supᵢ_inf_supᵢ {ι ι' : Type _} {f : ι → α} {g : ι' → α} :
    ((⨆ i, f i) ⊓ ⨆ j, g j) = ⨆ i : ι × ι', f i.1 ⊓ g i.2 := by
  simp_rw [supᵢ_inf_eq, inf_supᵢ_eq, supᵢ_prod]
#align supr_inf_supr supᵢ_inf_supᵢ

theorem bsupᵢ_inf_bsupᵢ {ι ι' : Type _} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨆ i ∈ s, f i) ⊓ ⨆ j ∈ t, g j) = ⨆ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊓ g p.2 := by
  simp only [supᵢ_subtype', supᵢ_inf_supᵢ]
  exact (Equiv.surjective _).supᵢ_congr (Equiv.Set.prod s t).symm fun x => rfl
#align bsupr_inf_bsupr bsupᵢ_inf_bsupᵢ

theorem supₛ_inf_supₛ : supₛ s ⊓ supₛ t = ⨆ p ∈ s ×ˢ t, (p : α × α).1 ⊓ p.2 := by
  simp only [supₛ_eq_supᵢ, bsupᵢ_inf_bsupᵢ]
#align Sup_inf_Sup supₛ_inf_supₛ

theorem supᵢ_disjoint_iff {f : ι → α} : Disjoint (⨆ i, f i) a ↔ ∀ i, Disjoint (f i) a := by
  simp only [disjoint_iff, supᵢ_inf_eq, supᵢ_eq_bot]
#align supr_disjoint_iff supᵢ_disjoint_iff

theorem disjoint_supᵢ_iff {f : ι → α} : Disjoint a (⨆ i, f i) ↔ ∀ i, Disjoint a (f i) := by
  simpa only [disjoint_comm] using @supᵢ_disjoint_iff
#align disjoint_supr_iff disjoint_supᵢ_iff

theorem supᵢ₂_disjoint_iff {f : ∀ i, κ i → α} :
    Disjoint (⨆ (i) (j), f i j) a ↔ ∀ i j, Disjoint (f i j) a := by
  simp_rw [supᵢ_disjoint_iff]
#align supr₂_disjoint_iff supᵢ₂_disjoint_iff

theorem disjoint_supᵢ₂_iff {f : ∀ i, κ i → α} :
    Disjoint a (⨆ (i) (j), f i j) ↔ ∀ i j, Disjoint a (f i j) := by
  simp_rw [disjoint_supᵢ_iff]
#align disjoint_supr₂_iff disjoint_supᵢ₂_iff

theorem supₛ_disjoint_iff {s : Set α} : Disjoint (supₛ s) a ↔ ∀ b ∈ s, Disjoint b a := by
  simp only [disjoint_iff, supₛ_inf_eq, supᵢ_eq_bot]
#align Sup_disjoint_iff supₛ_disjoint_iff

theorem disjoint_supₛ_iff {s : Set α} : Disjoint a (supₛ s) ↔ ∀ b ∈ s, Disjoint a b := by
  simpa only [disjoint_comm] using @supₛ_disjoint_iff
#align disjoint_Sup_iff disjoint_supₛ_iff

theorem supᵢ_inf_of_monotone {ι : Type _} [Preorder ι] [IsDirected ι (· ≤ ·)] {f g : ι → α}
    (hf : Monotone f) (hg : Monotone g) : (⨆ i, f i ⊓ g i) = (⨆ i, f i) ⊓ ⨆ i, g i := by
  refine' (le_supᵢ_inf_supᵢ f g).antisymm _
  rw [supᵢ_inf_supᵢ]
  refine' supᵢ_mono' fun i => _
  rcases directed_of (· ≤ ·) i.1 i.2 with ⟨j, h₁, h₂⟩
  exact ⟨j, inf_le_inf (hf h₁) (hg h₂)⟩
#align supr_inf_of_monotone supᵢ_inf_of_monotone

theorem supᵢ_inf_of_antitone {ι : Type _} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {f g : ι → α}
    (hf : Antitone f) (hg : Antitone g) : (⨆ i, f i ⊓ g i) = (⨆ i, f i) ⊓ ⨆ i, g i :=
  @supᵢ_inf_of_monotone α _ ιᵒᵈ _ _ f g hf.dual_left hg.dual_left
#align supr_inf_of_antitone supᵢ_inf_of_antitone

instance Pi.frame {ι : Type _} {π : ι → Type _} [∀ i, Frame (π i)] : Frame (∀ i, π i) :=
  { Pi.completeLattice with
    inf_supₛ_le_supᵢ_inf := fun a s i => by
      simp only [supₛ_apply, supᵢ_apply, inf_apply, inf_supᵢ_eq, ← supᵢ_subtype'']; rfl }
#align pi.frame Pi.frame

-- see Note [lower instance priority]
instance (priority := 100) Frame.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    rw [← supₛ_pair, ← supₛ_pair, inf_supₛ_eq, ← supₛ_image, image_pair]
#align frame.to_distrib_lattice Frame.toDistribLattice

end Frame

section Coframe

variable [Coframe α] {s t : Set α} {a b : α}

instance OrderDual.frame : Frame αᵒᵈ :=
  { OrderDual.completeLattice α with inf_supₛ_le_supᵢ_inf := @Coframe.infᵢ_sup_le_sup_infₛ α _ }
#align order_dual.frame OrderDual.frame

theorem sup_infₛ_eq : a ⊔ infₛ s = ⨅ b ∈ s, a ⊔ b :=
  @inf_supₛ_eq αᵒᵈ _ _ _
#align sup_Inf_eq sup_infₛ_eq

theorem infₛ_sup_eq : infₛ s ⊔ b = ⨅ a ∈ s, a ⊔ b :=
  @supₛ_inf_eq αᵒᵈ _ _ _
#align Inf_sup_eq infₛ_sup_eq

theorem infᵢ_sup_eq (f : ι → α) (a : α) : (⨅ i, f i) ⊔ a = ⨅ i, f i ⊔ a :=
  @supᵢ_inf_eq αᵒᵈ _ _ _ _
#align infi_sup_eq infᵢ_sup_eq

theorem sup_infᵢ_eq (a : α) (f : ι → α) : (a ⊔ ⨅ i, f i) = ⨅ i, a ⊔ f i :=
  @inf_supᵢ_eq αᵒᵈ _ _ _ _
#align sup_infi_eq sup_infᵢ_eq

theorem infᵢ₂_sup_eq {f : ∀ i, κ i → α} (a : α) : (⨅ (i) (j), f i j) ⊔ a = ⨅ (i) (j), f i j ⊔ a :=
  @supᵢ₂_inf_eq αᵒᵈ _ _ _ _ _
#align binfi_sup_eq infᵢ₂_sup_eq

theorem sup_infᵢ₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊔ ⨅ (i) (j), f i j) = ⨅ (i) (j), a ⊔ f i j :=
  @inf_supᵢ₂_eq αᵒᵈ _ _ _ _ _
#align sup_binfi_eq sup_infᵢ₂_eq

theorem infᵢ_sup_infᵢ {ι ι' : Type _} {f : ι → α} {g : ι' → α} :
    ((⨅ i, f i) ⊔ ⨅ i, g i) = ⨅ i : ι × ι', f i.1 ⊔ g i.2 :=
  @supᵢ_inf_supᵢ αᵒᵈ _ _ _ _ _
#align infi_sup_infi infᵢ_sup_infᵢ

theorem binfᵢ_sup_binfᵢ {ι ι' : Type _} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨅ i ∈ s, f i) ⊔ ⨅ j ∈ t, g j) = ⨅ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊔ g p.2 :=
  @bsupᵢ_inf_bsupᵢ αᵒᵈ _ _ _ _ _ _ _
#align binfi_sup_binfi binfᵢ_sup_binfᵢ

theorem infₛ_sup_infₛ : infₛ s ⊔ infₛ t = ⨅ p ∈ s ×ˢ t, (p : α × α).1 ⊔ p.2 :=
  @supₛ_inf_supₛ αᵒᵈ _ _ _
#align Inf_sup_Inf infₛ_sup_infₛ

theorem infᵢ_sup_of_monotone {ι : Type _} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {f g : ι → α}
    (hf : Monotone f) (hg : Monotone g) : (⨅ i, f i ⊔ g i) = (⨅ i, f i) ⊔ ⨅ i, g i :=
  @supᵢ_inf_of_antitone αᵒᵈ _ _ _ _ _ _ hf.dual_right hg.dual_right
#align infi_sup_of_monotone infᵢ_sup_of_monotone

theorem infᵢ_sup_of_antitone {ι : Type _} [Preorder ι] [IsDirected ι (· ≤ ·)] {f g : ι → α}
    (hf : Antitone f) (hg : Antitone g) : (⨅ i, f i ⊔ g i) = (⨅ i, f i) ⊔ ⨅ i, g i :=
  @supᵢ_inf_of_monotone αᵒᵈ _ _ _ _ _ _ hf.dual_right hg.dual_right
#align infi_sup_of_antitone infᵢ_sup_of_antitone

instance Pi.coframe {ι : Type _} {π : ι → Type _} [∀ i, Coframe (π i)] : Coframe (∀ i, π i) :=
  { Pi.completeLattice with
    infᵢ_sup_le_sup_infₛ := fun a s i => by
      simp only [infₛ_apply, infᵢ_apply, sup_apply, sup_infᵢ_eq, ← infᵢ_subtype'']; rfl }
#align pi.coframe Pi.coframe

-- see Note [lower instance priority]
instance (priority := 100) Coframe.toDistribLattice : DistribLattice α :=
  { ‹Coframe α› with
    le_sup_inf := fun a b c => by
      rw [← infₛ_pair, ← infₛ_pair, sup_infₛ_eq, ← infₛ_image, image_pair] }
#align coframe.to_distrib_lattice Coframe.toDistribLattice

end Coframe

section CompleteDistribLattice

variable [CompleteDistribLattice α] {a b : α} {s t : Set α}

-- Porting note: this is mysteriously slow. Minimised in
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Performance.20issue.20with.20.60CompleteBooleanAlgebra.60
-- but not yet resolved.
instance : CompleteDistribLattice αᵒᵈ :=
  { OrderDual.frame, OrderDual.coframe with }

instance Pi.completeDistribLattice {ι : Type _} {π : ι → Type _}
    [∀ i, CompleteDistribLattice (π i)] : CompleteDistribLattice (∀ i, π i) :=
  { Pi.frame, Pi.coframe with }
#align pi.complete_distrib_lattice Pi.completeDistribLattice

end CompleteDistribLattice

/-- A complete Boolean algebra is a completely distributive Boolean algebra. -/
class CompleteBooleanAlgebra (α) extends BooleanAlgebra α, CompleteDistribLattice α
#align complete_boolean_algebra CompleteBooleanAlgebra

instance Pi.completeBooleanAlgebra {ι : Type _} {π : ι → Type _}
    [∀ i, CompleteBooleanAlgebra (π i)] : CompleteBooleanAlgebra (∀ i, π i) :=
  { Pi.booleanAlgebra, Pi.completeDistribLattice with }
#align pi.complete_boolean_algebra Pi.completeBooleanAlgebra

instance Prop.completeBooleanAlgebra : CompleteBooleanAlgebra Prop :=
  { Prop.booleanAlgebra, Prop.completeLattice with
    infᵢ_sup_le_sup_infₛ := fun p s =>
      Iff.mp <| by simp only [forall_or_left, infᵢ_Prop_eq, infₛ_Prop_eq, sup_Prop_eq]
    inf_supₛ_le_supᵢ_inf := fun p s =>
      Iff.mp <| by
        simp only [inf_Prop_eq, exists_and_left, supᵢ_Prop_eq, supₛ_Prop_eq, exists_prop] }
#align Prop.complete_boolean_algebra Prop.completeBooleanAlgebra

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] {a b : α} {s : Set α} {f : ι → α}

theorem compl_infᵢ : infᵢ fᶜ = ⨆ i, f iᶜ :=
  le_antisymm
    (compl_le_of_compl_le <| le_infᵢ fun i => compl_le_of_compl_le <|
      le_supᵢ (HasCompl.compl ∘ f) i)
    (supᵢ_le fun _ => compl_le_compl <| infᵢ_le _ _)
#align compl_infi compl_infᵢ

theorem compl_supᵢ : supᵢ fᶜ = ⨅ i, f iᶜ :=
  compl_injective (by simp [compl_infᵢ])
#align compl_supr compl_supᵢ

theorem compl_infₛ : infₛ sᶜ = ⨆ i ∈ s, iᶜ := by simp only [infₛ_eq_infᵢ, compl_infᵢ]
#align compl_Inf compl_infₛ

theorem compl_supₛ : supₛ sᶜ = ⨅ i ∈ s, iᶜ := by simp only [supₛ_eq_supᵢ, compl_supᵢ]
#align compl_Sup compl_supₛ

theorem compl_infₛ' : infₛ sᶜ = supₛ (HasCompl.compl '' s) :=
  compl_infₛ.trans supₛ_image.symm
#align compl_Inf' compl_infₛ'

theorem compl_supₛ' : supₛ sᶜ = infₛ (HasCompl.compl '' s) :=
  compl_supₛ.trans infₛ_image.symm
#align compl_Sup' compl_supₛ'

end CompleteBooleanAlgebra

section lift

-- See note [reducible non-instances]
/-- Pullback an `Order.Frame` along an injection. -/
@[reducible]
protected def Function.Injective.frame [Sup α] [Inf α] [SupSet α] [InfSet α] [Top α] [Bot α]
    [Frame β] (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_supₛ : ∀ s, f (supₛ s) = ⨆ a ∈ s, f a)
    (map_infₛ : ∀ s, f (infₛ s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) :
    Frame α :=
  { hf.completeLattice f map_sup map_inf map_supₛ map_infₛ map_top map_bot with
    inf_supₛ_le_supᵢ_inf := fun a s => by
      change f (a ⊓ supₛ s) ≤ f _
      rw [← supₛ_image, map_inf, map_supₛ s, inf_supᵢ₂_eq]
      simp_rw [← map_inf]
      exact ((map_supₛ _).trans supᵢ_image).ge }
#align function.injective.frame Function.Injective.frame

-- See note [reducible non-instances]
/-- Pullback an `Order.Coframe` along an injection. -/
@[reducible]
protected def Function.Injective.coframe [Sup α] [Inf α] [SupSet α] [InfSet α] [Top α] [Bot α]
    [Coframe β] (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_supₛ : ∀ s, f (supₛ s) = ⨆ a ∈ s, f a)
    (map_infₛ : ∀ s, f (infₛ s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) :
    Coframe α :=
  { hf.completeLattice f map_sup map_inf map_supₛ map_infₛ map_top map_bot with
    infᵢ_sup_le_sup_infₛ := fun a s => by
      change f _ ≤ f (a ⊔ infₛ s)
      rw [← infₛ_image, map_sup, map_infₛ s, sup_infᵢ₂_eq]
      simp_rw [← map_sup]
      exact ((map_infₛ _).trans infᵢ_image).le }
#align function.injective.coframe Function.Injective.coframe

-- See note [reducible non-instances]
/-- Pullback a `CompleteDistribLattice` along an injection. -/
@[reducible]
protected def Function.Injective.completeDistribLattice [Sup α] [Inf α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [CompleteDistribLattice β] (f : α → β) (hf : Function.Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_supₛ : ∀ s, f (supₛ s) = ⨆ a ∈ s, f a) (map_infₛ : ∀ s, f (infₛ s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteDistribLattice α :=
  { hf.frame f map_sup map_inf map_supₛ map_infₛ map_top map_bot,
    hf.coframe f map_sup map_inf map_supₛ map_infₛ map_top map_bot with }
#align function.injective.complete_distrib_lattice Function.Injective.completeDistribLattice

-- See note [reducible non-instances]
/-- Pullback a `CompleteBooleanAlgebra` along an injection. -/
@[reducible]
protected def Function.Injective.completeBooleanAlgebra [Sup α] [Inf α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [HasCompl α] [SDiff α] [CompleteBooleanAlgebra β] (f : α → β)
    (hf : Function.Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_supₛ : ∀ s, f (supₛ s) = ⨆ a ∈ s, f a)
    (map_infₛ : ∀ s, f (infₛ s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f (aᶜ) = f aᶜ) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompleteBooleanAlgebra α :=
  { hf.completeDistribLattice f map_sup map_inf map_supₛ map_infₛ map_top map_bot,
    hf.booleanAlgebra f map_sup map_inf map_top map_bot map_compl map_sdiff with }
#align function.injective.complete_boolean_algebra Function.Injective.completeBooleanAlgebra

end lift

namespace PUnit

variable (s : Set PUnit.{u + 1}) (x y : PUnit.{u + 1})

-- Porting note: we don't have `refine_struct` ported yet, so we do it by hand
instance completeBooleanAlgebra : CompleteBooleanAlgebra PUnit := by
  refine'
    { PUnit.booleanAlgebra with
      supₛ := fun _ => unit
      infₛ := fun _ => unit
      .. } <;>
  intros <;>
  first|trivial

@[simp]
theorem supₛ_eq : supₛ s = unit :=
  rfl
#align punit.Sup_eq PUnit.supₛ_eq

@[simp]
theorem infₛ_eq : infₛ s = unit :=
  rfl
#align punit.Inf_eq PUnit.infₛ_eq

end PUnit
