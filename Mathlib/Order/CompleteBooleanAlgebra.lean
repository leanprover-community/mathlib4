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
  inf_sSup_le_iSup_inf (a : α) (s : Set α) : a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b
#align order.frame Order.Frame

/-- In a frame, `⊓` distributes over `⨆`. -/
add_decl_doc Order.Frame.inf_sSup_le_iSup_inf

/-- A coframe, aka complete Brouwer algebra or complete co-Heyting algebra, is a complete lattice
whose `⊔` distributes over `⨅`. -/
class Order.Coframe (α : Type _) extends CompleteLattice α where
  iInf_sup_le_sup_sInf (a : α) (s : Set α) : (⨅ b ∈ s, a ⊔ b) ≤ a ⊔ sInf s
#align order.coframe Order.Coframe

/-- In a coframe, `⊔` distributes over `⨅`. -/
add_decl_doc Order.Coframe.iInf_sup_le_sup_sInf

open Order

/-- A completely distributive lattice is a complete lattice whose `⊔` and `⊓` respectively
distribute over `⨅` and `⨆`. -/
class CompleteDistribLattice (α : Type _) extends Frame α where
  iInf_sup_le_sup_sInf : ∀ a s, (⨅ b ∈ s, a ⊔ b) ≤ a ⊔ sInf s
#align complete_distrib_lattice CompleteDistribLattice

/-- In a completely distributive lattice, `⊔` distributes over `⨅`. -/
add_decl_doc CompleteDistribLattice.iInf_sup_le_sup_sInf

-- See note [lower instance priority]
instance (priority := 100) CompleteDistribLattice.toCoframe [CompleteDistribLattice α] :
    Coframe α :=
  { ‹CompleteDistribLattice α› with }
#align complete_distrib_lattice.to_coframe CompleteDistribLattice.toCoframe

-- See note [lower instance priority]
instance (priority := 100) CompleteLinearOrder.toCompleteDistribLattice [CompleteLinearOrder α] :
    CompleteDistribLattice α where
  inf_sSup_le_iSup_inf a s := open Classical in
    if h : ∀ b ∈ s, b ≤ a then by
      rw [inf_eq_right.2 (sSup_le_iff.2 h)]
      refine sSup_le_iff.2 fun b hb => ?_
      refine le_trans ?_ (le_iSup _ b)
      refine le_trans ?_ (le_iSup _ hb)
      rw [inf_eq_right.2 (h b hb)]
    else by
      have ⟨b, hb, hab⟩ : ∃ b ∈ s, a < b := by simpa using h
      refine le_trans ?_ (le_iSup _ b)
      refine le_trans ?_ (le_iSup _ hb)
      rw [inf_eq_left.2 (by exact le_trans (le_of_lt hab) (le_sSup hb))]
      rw [inf_eq_left.2 (le_of_lt hab)]
  iInf_sup_le_sup_sInf a s := open Classical in
    if h : ∀ b ∈ s, a ≤ b then by
      rw [sup_eq_right.2 (le_sInf_iff.2 h)]
      refine le_sInf_iff.2 fun b hb => ?_
      refine le_trans (iInf_le _ b) ?_
      refine le_trans (iInf_le _ hb) ?_
      rw [sup_eq_right.2 (h b hb)]
    else by
      have ⟨b, hb, hab⟩ : ∃ b ∈ s, b < a := by simpa using h
      refine le_trans (iInf_le _ b) ?_
      refine le_trans (iInf_le _ hb) ?_
      rw [sup_eq_left.2 (le_of_lt hab)]
      rw [sup_eq_left.2 (by exact le_trans (sInf_le hb) (le_of_lt hab))]

section Frame

variable [Frame α] {s t : Set α} {a b : α}

instance OrderDual.coframe : Coframe αᵒᵈ :=
  { OrderDual.completeLattice α with iInf_sup_le_sup_sInf := @Frame.inf_sSup_le_iSup_inf α _ }
#align order_dual.coframe OrderDual.coframe

theorem inf_sSup_eq : a ⊓ sSup s = ⨆ b ∈ s, a ⊓ b :=
  (Frame.inf_sSup_le_iSup_inf _ _).antisymm iSup_inf_le_inf_sSup
#align inf_Sup_eq inf_sSup_eq

theorem sSup_inf_eq : sSup s ⊓ b = ⨆ a ∈ s, a ⊓ b := by
  simpa only [inf_comm] using @inf_sSup_eq α _ s b
#align Sup_inf_eq sSup_inf_eq

theorem iSup_inf_eq (f : ι → α) (a : α) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a := by
  rw [iSup, sSup_inf_eq, iSup_range]
#align supr_inf_eq iSup_inf_eq

theorem inf_iSup_eq (a : α) (f : ι → α) : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  simpa only [inf_comm] using iSup_inf_eq f a
#align inf_supr_eq inf_iSup_eq

theorem iSup₂_inf_eq {f : ∀ i, κ i → α} (a : α) : (⨆ (i) (j), f i j) ⊓ a = ⨆ (i) (j), f i j ⊓ a :=
  by simp only [iSup_inf_eq]
#align bsupr_inf_eq iSup₂_inf_eq

theorem inf_iSup₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊓ ⨆ (i) (j), f i j) = ⨆ (i) (j), a ⊓ f i j :=
  by simp only [inf_iSup_eq]
#align inf_bsupr_eq inf_iSup₂_eq

theorem iSup_inf_iSup {ι ι' : Type _} {f : ι → α} {g : ι' → α} :
    ((⨆ i, f i) ⊓ ⨆ j, g j) = ⨆ i : ι × ι', f i.1 ⊓ g i.2 := by
  simp_rw [iSup_inf_eq, inf_iSup_eq, iSup_prod]
#align supr_inf_supr iSup_inf_iSup

theorem biSup_inf_biSup {ι ι' : Type _} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨆ i ∈ s, f i) ⊓ ⨆ j ∈ t, g j) = ⨆ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊓ g p.2 := by
  simp only [iSup_subtype', iSup_inf_iSup]
  exact (Equiv.surjective _).iSup_congr (Equiv.Set.prod s t).symm fun x => rfl
#align bsupr_inf_bsupr biSup_inf_biSup

theorem sSup_inf_sSup : sSup s ⊓ sSup t = ⨆ p ∈ s ×ˢ t, (p : α × α).1 ⊓ p.2 := by
  simp only [sSup_eq_iSup, biSup_inf_biSup]
#align Sup_inf_Sup sSup_inf_sSup

theorem iSup_disjoint_iff {f : ι → α} : Disjoint (⨆ i, f i) a ↔ ∀ i, Disjoint (f i) a := by
  simp only [disjoint_iff, iSup_inf_eq, iSup_eq_bot]
#align supr_disjoint_iff iSup_disjoint_iff

theorem disjoint_iSup_iff {f : ι → α} : Disjoint a (⨆ i, f i) ↔ ∀ i, Disjoint a (f i) := by
  simpa only [disjoint_comm] using @iSup_disjoint_iff
#align disjoint_supr_iff disjoint_iSup_iff

theorem iSup₂_disjoint_iff {f : ∀ i, κ i → α} :
    Disjoint (⨆ (i) (j), f i j) a ↔ ∀ i j, Disjoint (f i j) a := by
  simp_rw [iSup_disjoint_iff]
#align supr₂_disjoint_iff iSup₂_disjoint_iff

theorem disjoint_iSup₂_iff {f : ∀ i, κ i → α} :
    Disjoint a (⨆ (i) (j), f i j) ↔ ∀ i j, Disjoint a (f i j) := by
  simp_rw [disjoint_iSup_iff]
#align disjoint_supr₂_iff disjoint_iSup₂_iff

theorem sSup_disjoint_iff {s : Set α} : Disjoint (sSup s) a ↔ ∀ b ∈ s, Disjoint b a := by
  simp only [disjoint_iff, sSup_inf_eq, iSup_eq_bot]
#align Sup_disjoint_iff sSup_disjoint_iff

theorem disjoint_sSup_iff {s : Set α} : Disjoint a (sSup s) ↔ ∀ b ∈ s, Disjoint a b := by
  simpa only [disjoint_comm] using @sSup_disjoint_iff
#align disjoint_Sup_iff disjoint_sSup_iff

theorem iSup_inf_of_monotone {ι : Type _} [Preorder ι] [IsDirected ι (· ≤ ·)] {f g : ι → α}
    (hf : Monotone f) (hg : Monotone g) : (⨆ i, f i ⊓ g i) = (⨆ i, f i) ⊓ ⨆ i, g i := by
  refine' (le_iSup_inf_iSup f g).antisymm _
  rw [iSup_inf_iSup]
  refine' iSup_mono' fun i => _
  rcases directed_of (· ≤ ·) i.1 i.2 with ⟨j, h₁, h₂⟩
  exact ⟨j, inf_le_inf (hf h₁) (hg h₂)⟩
#align supr_inf_of_monotone iSup_inf_of_monotone

theorem iSup_inf_of_antitone {ι : Type _} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {f g : ι → α}
    (hf : Antitone f) (hg : Antitone g) : (⨆ i, f i ⊓ g i) = (⨆ i, f i) ⊓ ⨆ i, g i :=
  @iSup_inf_of_monotone α _ ιᵒᵈ _ _ f g hf.dual_left hg.dual_left
#align supr_inf_of_antitone iSup_inf_of_antitone

instance Pi.frame {ι : Type _} {π : ι → Type _} [∀ i, Frame (π i)] : Frame (∀ i, π i) :=
  { Pi.completeLattice with
    inf_sSup_le_iSup_inf := fun a s i => by
      simp only [sSup_apply, iSup_apply, inf_apply, inf_iSup_eq, ← iSup_subtype'']; rfl }
#align pi.frame Pi.frame

-- see Note [lower instance priority]
instance (priority := 100) Frame.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    rw [← sSup_pair, ← sSup_pair, inf_sSup_eq, ← sSup_image, image_pair]
#align frame.to_distrib_lattice Frame.toDistribLattice

end Frame

section Coframe

variable [Coframe α] {s t : Set α} {a b : α}

instance OrderDual.frame : Frame αᵒᵈ :=
  { OrderDual.completeLattice α with inf_sSup_le_iSup_inf := @Coframe.iInf_sup_le_sup_sInf α _ }
#align order_dual.frame OrderDual.frame

theorem sup_sInf_eq : a ⊔ sInf s = ⨅ b ∈ s, a ⊔ b :=
  @inf_sSup_eq αᵒᵈ _ _ _
#align sup_Inf_eq sup_sInf_eq

theorem sInf_sup_eq : sInf s ⊔ b = ⨅ a ∈ s, a ⊔ b :=
  @sSup_inf_eq αᵒᵈ _ _ _
#align Inf_sup_eq sInf_sup_eq

theorem iInf_sup_eq (f : ι → α) (a : α) : (⨅ i, f i) ⊔ a = ⨅ i, f i ⊔ a :=
  @iSup_inf_eq αᵒᵈ _ _ _ _
#align infi_sup_eq iInf_sup_eq

theorem sup_iInf_eq (a : α) (f : ι → α) : (a ⊔ ⨅ i, f i) = ⨅ i, a ⊔ f i :=
  @inf_iSup_eq αᵒᵈ _ _ _ _
#align sup_infi_eq sup_iInf_eq

theorem iInf₂_sup_eq {f : ∀ i, κ i → α} (a : α) : (⨅ (i) (j), f i j) ⊔ a = ⨅ (i) (j), f i j ⊔ a :=
  @iSup₂_inf_eq αᵒᵈ _ _ _ _ _
#align binfi_sup_eq iInf₂_sup_eq

theorem sup_iInf₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊔ ⨅ (i) (j), f i j) = ⨅ (i) (j), a ⊔ f i j :=
  @inf_iSup₂_eq αᵒᵈ _ _ _ _ _
#align sup_binfi_eq sup_iInf₂_eq

theorem iInf_sup_iInf {ι ι' : Type _} {f : ι → α} {g : ι' → α} :
    ((⨅ i, f i) ⊔ ⨅ i, g i) = ⨅ i : ι × ι', f i.1 ⊔ g i.2 :=
  @iSup_inf_iSup αᵒᵈ _ _ _ _ _
#align infi_sup_infi iInf_sup_iInf

theorem biInf_sup_biInf {ι ι' : Type _} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨅ i ∈ s, f i) ⊔ ⨅ j ∈ t, g j) = ⨅ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊔ g p.2 :=
  @biSup_inf_biSup αᵒᵈ _ _ _ _ _ _ _
#align binfi_sup_binfi biInf_sup_biInf

theorem sInf_sup_sInf : sInf s ⊔ sInf t = ⨅ p ∈ s ×ˢ t, (p : α × α).1 ⊔ p.2 :=
  @sSup_inf_sSup αᵒᵈ _ _ _
#align Inf_sup_Inf sInf_sup_sInf

theorem iInf_sup_of_monotone {ι : Type _} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {f g : ι → α}
    (hf : Monotone f) (hg : Monotone g) : (⨅ i, f i ⊔ g i) = (⨅ i, f i) ⊔ ⨅ i, g i :=
  @iSup_inf_of_antitone αᵒᵈ _ _ _ _ _ _ hf.dual_right hg.dual_right
#align infi_sup_of_monotone iInf_sup_of_monotone

theorem iInf_sup_of_antitone {ι : Type _} [Preorder ι] [IsDirected ι (· ≤ ·)] {f g : ι → α}
    (hf : Antitone f) (hg : Antitone g) : (⨅ i, f i ⊔ g i) = (⨅ i, f i) ⊔ ⨅ i, g i :=
  @iSup_inf_of_monotone αᵒᵈ _ _ _ _ _ _ hf.dual_right hg.dual_right
#align infi_sup_of_antitone iInf_sup_of_antitone

instance Pi.coframe {ι : Type _} {π : ι → Type _} [∀ i, Coframe (π i)] : Coframe (∀ i, π i) :=
  { Pi.completeLattice with
    iInf_sup_le_sup_sInf := fun a s i => by
      simp only [sInf_apply, iInf_apply, sup_apply, sup_iInf_eq, ← iInf_subtype'']; rfl }
#align pi.coframe Pi.coframe

-- see Note [lower instance priority]
instance (priority := 100) Coframe.toDistribLattice : DistribLattice α :=
  { ‹Coframe α› with
    le_sup_inf := fun a b c => by
      rw [← sInf_pair, ← sInf_pair, sup_sInf_eq, ← sInf_image, image_pair] }
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
    iInf_sup_le_sup_sInf := fun p s =>
      Iff.mp <| by simp only [forall_or_left, iInf_Prop_eq, sInf_Prop_eq, sup_Prop_eq]
    inf_sSup_le_iSup_inf := fun p s =>
      Iff.mp <| by
        simp only [inf_Prop_eq, exists_and_left, iSup_Prop_eq, sSup_Prop_eq, exists_prop] }
#align Prop.complete_boolean_algebra Prop.completeBooleanAlgebra

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] {a b : α} {s : Set α} {f : ι → α}

theorem compl_iInf : iInf fᶜ = ⨆ i, f iᶜ :=
  le_antisymm
    (compl_le_of_compl_le <| le_iInf fun i => compl_le_of_compl_le <|
      le_iSup (HasCompl.compl ∘ f) i)
    (iSup_le fun _ => compl_le_compl <| iInf_le _ _)
#align compl_infi compl_iInf

theorem compl_iSup : iSup fᶜ = ⨅ i, f iᶜ :=
  compl_injective (by simp [compl_iInf])
#align compl_supr compl_iSup

theorem compl_sInf : sInf sᶜ = ⨆ i ∈ s, iᶜ := by simp only [sInf_eq_iInf, compl_iInf]
#align compl_Inf compl_sInf

theorem compl_sSup : sSup sᶜ = ⨅ i ∈ s, iᶜ := by simp only [sSup_eq_iSup, compl_iSup]
#align compl_Sup compl_sSup

theorem compl_sInf' : sInf sᶜ = sSup (HasCompl.compl '' s) :=
  compl_sInf.trans sSup_image.symm
#align compl_Inf' compl_sInf'

theorem compl_sSup' : sSup sᶜ = sInf (HasCompl.compl '' s) :=
  compl_sSup.trans sInf_image.symm
#align compl_Sup' compl_sSup'

end CompleteBooleanAlgebra

section lift

-- See note [reducible non-instances]
/-- Pullback an `Order.Frame` along an injection. -/
@[reducible]
protected def Function.Injective.frame [Sup α] [Inf α] [SupSet α] [InfSet α] [Top α] [Bot α]
    [Frame β] (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a)
    (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) :
    Frame α :=
  { hf.completeLattice f map_sup map_inf map_sSup map_sInf map_top map_bot with
    inf_sSup_le_iSup_inf := fun a s => by
      change f (a ⊓ sSup s) ≤ f _
      rw [← sSup_image, map_inf, map_sSup s, inf_iSup₂_eq]
      simp_rw [← map_inf]
      exact ((map_sSup _).trans iSup_image).ge }
#align function.injective.frame Function.Injective.frame

-- See note [reducible non-instances]
/-- Pullback an `Order.Coframe` along an injection. -/
@[reducible]
protected def Function.Injective.coframe [Sup α] [Inf α] [SupSet α] [InfSet α] [Top α] [Bot α]
    [Coframe β] (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a)
    (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) :
    Coframe α :=
  { hf.completeLattice f map_sup map_inf map_sSup map_sInf map_top map_bot with
    iInf_sup_le_sup_sInf := fun a s => by
      change f _ ≤ f (a ⊔ sInf s)
      rw [← sInf_image, map_sup, map_sInf s, sup_iInf₂_eq]
      simp_rw [← map_sup]
      exact ((map_sInf _).trans iInf_image).le }
#align function.injective.coframe Function.Injective.coframe

-- See note [reducible non-instances]
/-- Pullback a `CompleteDistribLattice` along an injection. -/
@[reducible]
protected def Function.Injective.completeDistribLattice [Sup α] [Inf α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [CompleteDistribLattice β] (f : α → β) (hf : Function.Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteDistribLattice α :=
  { hf.frame f map_sup map_inf map_sSup map_sInf map_top map_bot,
    hf.coframe f map_sup map_inf map_sSup map_sInf map_top map_bot with }
#align function.injective.complete_distrib_lattice Function.Injective.completeDistribLattice

-- See note [reducible non-instances]
/-- Pullback a `CompleteBooleanAlgebra` along an injection. -/
@[reducible]
protected def Function.Injective.completeBooleanAlgebra [Sup α] [Inf α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [HasCompl α] [SDiff α] [CompleteBooleanAlgebra β] (f : α → β)
    (hf : Function.Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a)
    (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f (aᶜ) = f aᶜ) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompleteBooleanAlgebra α :=
  { hf.completeDistribLattice f map_sup map_inf map_sSup map_sInf map_top map_bot,
    hf.booleanAlgebra f map_sup map_inf map_top map_bot map_compl map_sdiff with }
#align function.injective.complete_boolean_algebra Function.Injective.completeBooleanAlgebra

end lift

namespace PUnit

variable (s : Set PUnit.{u + 1}) (x y : PUnit.{u + 1})

instance completeBooleanAlgebra : CompleteBooleanAlgebra PUnit := by
  refine'
    { PUnit.booleanAlgebra with
      sSup := fun _ => unit
      sInf := fun _ => unit
      .. } <;>
  (intros; trivial)

@[simp]
theorem sSup_eq : sSup s = unit :=
  rfl
#align punit.Sup_eq PUnit.sSup_eq

@[simp]
theorem sInf_eq : sInf s = unit :=
  rfl
#align punit.Inf_eq PUnit.sInf_eq

end PUnit
