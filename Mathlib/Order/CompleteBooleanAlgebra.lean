/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies
-/
import Mathlib.Order.CompleteLattice
import Mathlib.Order.Directed
import Mathlib.Logic.Equiv.Set

#align_import order.complete_boolean_algebra from "leanprover-community/mathlib"@"71b36b6f3bbe3b44e6538673819324d3ee9fcc96"

/-!
# Frames, completely distributive lattices and complete Boolean algebras

In this file we define and provide API for (co)frames, completely distributive lattices and
complete Boolean algebras.

We distinguish two different distributivity properties:
 1. `inf_iSup_eq : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i` (finite `⊓` distributes over infinite `⨆`).
  This is required by `Frame`, `CompleteDistribLattice`, and `CompleteBooleanAlgebra`
  (`Coframe`, etc., require the dual property).
 2. `iInf_iSup_eq : (⨅ i, ⨆ j, f i j) = ⨆ s, ⨅ i, f i (s i)`
  (infinite `⨅` distributes over infinite `⨆`).
  This stronger property is called "completely distributive",
  and is required by `CompletelyDistribLattice` and `CompleteAtomicBooleanAlgebra`.

## Typeclasses

* `Order.Frame`: Frame: A complete lattice whose `⊓` distributes over `⨆`.
* `Order.Coframe`: Coframe: A complete lattice whose `⊔` distributes over `⨅`.
* `CompleteDistribLattice`: Complete distributive lattices: A complete lattice whose `⊓` and `⊔`
  distribute over `⨆` and `⨅` respectively.
* `CompleteBooleanAlgebra`: Complete Boolean algebra: A Boolean algebra whose `⊓`
  and `⊔` distribute over `⨆` and `⨅` respectively.
* `CompletelyDistribLattice`: Completely distributive lattices: A complete lattice whose
  `⨅` and `⨆` satisfy `iInf_iSup_eq`.
* `CompleteBooleanAlgebra`: Complete Boolean algebra: A Boolean algebra whose `⊓`
  and `⊔` distribute over `⨆` and `⨅` respectively.
* `CompleteAtomicBooleanAlgebra`: Complete atomic Boolean algebra:
  A complete Boolean algebra which is additionally completely distributive.
  (This implies that it's (co)atom(ist)ic.)

A set of opens gives rise to a topological space precisely if it forms a frame. Such a frame is also
completely distributive, but not all frames are. `Filter` is a coframe but not a completely
distributive lattice.

## References

* [Wikipedia, *Complete Heyting algebra*](https://en.wikipedia.org/wiki/Complete_Heyting_algebra)
* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]
-/

set_option autoImplicit true


open Function Set

universe u v w

variable {α : Type u} {β : Type v} {ι : Sort w} {κ : ι → Sort w'}

/-- A frame, aka complete Heyting algebra, is a complete lattice whose `⊓` distributes over `⨆`. -/
class Order.Frame (α : Type*) extends CompleteLattice α where
  inf_sSup_le_iSup_inf (a : α) (s : Set α) : a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b
#align order.frame Order.Frame

/-- In a frame, `⊓` distributes over `⨆`. -/
add_decl_doc Order.Frame.inf_sSup_le_iSup_inf

/-- A coframe, aka complete Brouwer algebra or complete co-Heyting algebra, is a complete lattice
whose `⊔` distributes over `⨅`. -/
class Order.Coframe (α : Type*) extends CompleteLattice α where
  iInf_sup_le_sup_sInf (a : α) (s : Set α) : ⨅ b ∈ s, a ⊔ b ≤ a ⊔ sInf s
#align order.coframe Order.Coframe

/-- In a coframe, `⊔` distributes over `⨅`. -/
add_decl_doc Order.Coframe.iInf_sup_le_sup_sInf

open Order

/-- A complete distributive lattice is a complete lattice whose `⊔` and `⊓` respectively
distribute over `⨅` and `⨆`. -/
class CompleteDistribLattice (α : Type*) extends Frame α where
  iInf_sup_le_sup_sInf : ∀ a s, ⨅ b ∈ s, a ⊔ b ≤ a ⊔ sInf s
#align complete_distrib_lattice CompleteDistribLattice

/-- In a complete distributive lattice, `⊔` distributes over `⨅`. -/
add_decl_doc CompleteDistribLattice.iInf_sup_le_sup_sInf

-- See note [lower instance priority]
instance (priority := 100) CompleteDistribLattice.toCoframe [CompleteDistribLattice α] :
    Coframe α :=
  { ‹CompleteDistribLattice α› with }
#align complete_distrib_lattice.to_coframe CompleteDistribLattice.toCoframe

/-- A completely distributive lattice is a complete lattice whose `⨅` and `⨆`
distribute over each other. -/
class CompletelyDistribLattice (α : Type u) extends CompleteLattice α where
  protected iInf_iSup_eq {ι : Type u} {κ : ι → Type u} (f : ∀ a, κ a → α) :
    (⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a)

theorem le_iInf_iSup [CompleteLattice α] {f : ∀ a, κ a → α} :
    (⨆ g : ∀ a, κ a, ⨅ a, f a (g a)) ≤ ⨅ a, ⨆ b, f a b :=
  iSup_le fun _ => le_iInf fun a => le_trans (iInf_le _ a) (le_iSup _ _)

theorem iInf_iSup_eq [CompletelyDistribLattice α] {f : ∀ a, κ a → α} :
    (⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a) :=
  (le_antisymm · le_iInf_iSup) <| calc
    _ = ⨅ a : range (range <| f ·), ⨆ b : a.1, b.1 := by
      simp_rw [iInf_subtype, iInf_range, iSup_subtype, iSup_range]
      -- 🎉 no goals
    _ = _ := CompletelyDistribLattice.iInf_iSup_eq _
    _ ≤ _ := iSup_le fun g => by
      refine le_trans ?_ <| le_iSup _ fun a => Classical.choose (g ⟨_, a, rfl⟩).2
      -- ⊢ ⨅ (a : ↑(range fun x => range (f x))), ↑(g a) ≤ ⨅ (a : ι), f a ((fun a => Cl …
      refine le_iInf fun a => le_trans (iInf_le _ ⟨range (f a), a, rfl⟩) ?_
      -- ⊢ ↑(g { val := range (f a), property := (_ : ∃ y, (fun x => range (f x)) y = r …
      rw [← Classical.choose_spec (g ⟨_, a, rfl⟩).2]
      -- 🎉 no goals

theorem iSup_iInf_le [CompleteLattice α] {f : ∀ a, κ a → α} :
    (⨆ a, ⨅ b, f a b) ≤ ⨅ g : ∀ a, κ a, ⨆ a, f a (g a) :=
  le_iInf_iSup (α := αᵒᵈ)

theorem iSup_iInf_eq [CompletelyDistribLattice α] {f : ∀ a, κ a → α} :
    (⨆ a, ⨅ b, f a b) = ⨅ g : ∀ a, κ a, ⨆ a, f a (g a) := by
  refine le_antisymm iSup_iInf_le ?_
  -- ⊢ ⨅ (g : (a : ι) → κ a), ⨆ (a : ι), f a (g a) ≤ ⨆ (a : ι), ⨅ (b : κ a), f a b
  rw [iInf_iSup_eq]
  -- ⊢ ⨆ (g : ((a : ι) → κ a) → ι), ⨅ (a : (a : ι) → κ a), f (g a) (a (g a)) ≤ ⨆ (a …
  refine iSup_le fun g => ?_
  -- ⊢ ⨅ (a : (a : ι) → κ a), f (g a) (a (g a)) ≤ ⨆ (a : ι), ⨅ (b : κ a), f a b
  have ⟨a, ha⟩ : ∃ a, ∀ b, ∃ f, ∃ h : a = g f, h ▸ b = f (g f) := of_not_not fun h => by
    push_neg at h
    choose h hh using h
    have := hh _ h rfl
    contradiction
  refine le_trans ?_ (le_iSup _ a)
  -- ⊢ ⨅ (a : (a : ι) → κ a), f (g a) (a (g a)) ≤ ⨅ (b : κ a), f a b
  refine le_iInf fun b => ?_
  -- ⊢ ⨅ (a : (a : ι) → κ a), f (g a) (a (g a)) ≤ f a b
  obtain ⟨h, rfl, rfl⟩ := ha b
  -- ⊢ ⨅ (a : (a : ι) → κ a), f (g a) (a (g a)) ≤ f (g h) (h (g h))
  refine iInf_le _ _
  -- 🎉 no goals

instance (priority := 100) CompletelyDistribLattice.toCompleteDistribLattice
    [CompletelyDistribLattice α] : CompleteDistribLattice α where
  iInf_sup_le_sup_sInf a s := calc
    _ = ⨅ b : s, ⨆ x : Bool, cond x a b := by simp_rw [iInf_subtype, iSup_bool_eq, cond]
                                              -- 🎉 no goals
    _ = _ := iInf_iSup_eq
    _ ≤ _ := iSup_le fun f => by
      by_cases ∀ i, f i = false
      -- ⊢ (⨅ (a_1 : ↑s), bif f a_1 then a else ↑a_1) ≤ a ⊔ sInf s
      -- ⊢ (⨅ (a_1 : ↑s), bif f a_1 then a else ↑a_1) ≤ a ⊔ sInf s
      case pos => simp [h, iInf_subtype, ← sInf_eq_iInf]
      -- ⊢ (⨅ (a_1 : ↑s), bif f a_1 then a else ↑a_1) ≤ a ⊔ sInf s
      -- 🎉 no goals
      case neg =>
        have ⟨i, h⟩ : ∃ i, f i = true := by simpa using h
      -- 🎉 no goals
        refine le_trans (iInf_le _ i) ?_
        simp [h]
  inf_sSup_le_iSup_inf a s := calc
      -- ⊢ ⨆ (g : (a : Bool) → bif a then PUnit else ↑s), a ⊓ ↑(g false) ≤ ⨆ (b : α) (_ …
    _ = ⨅ x : Bool, ⨆ y : cond x PUnit s, match x with | true => a | false => y.1 := by
      -- ⊢ a ⊓ ↑(g false) ≤ ⨆ (_ : ↑(g false) ∈ s), a ⊓ ↑(g false)
      simp_rw [iInf_bool_eq, cond, iSup_const, iSup_subtype, sSup_eq_iSup]
      -- ⊢ a ⊓ ↑(g false) ≤ a ⊓ ↑(g false)
    _ = _ := iInf_iSup_eq
      -- 🎉 no goals
    _ ≤ _ := by
      simp_rw [iInf_bool_eq]
      refine iSup_le fun g => le_trans ?_ (le_iSup _ (g false).1)
      refine le_trans ?_ (le_iSup _ (g false).2)
      rfl

-- See note [lower instance priority]
instance (priority := 100) CompleteLinearOrder.toCompletelyDistribLattice [CompleteLinearOrder α] :
    CompletelyDistribLattice α where
  iInf_iSup_eq {α β} g := by
    let lhs := ⨅ a, ⨆ b, g a b
    -- ⊢ ⨅ (a : α), ⨆ (b : β a), g a b = ⨆ (g_1 : (a : α) → β a), ⨅ (a : α), g a (g_1 …
    let rhs := ⨆ h : ∀ a, β a, ⨅ a, g a (h a)
    -- ⊢ ⨅ (a : α), ⨆ (b : β a), g a b = ⨆ (g_1 : (a : α) → β a), ⨅ (a : α), g a (g_1 …
    suffices lhs ≤ rhs from le_antisymm this le_iInf_iSup
    -- ⊢ lhs ≤ rhs
    by_cases ∃ x, rhs < x ∧ x < lhs
    -- ⊢ lhs ≤ rhs
    -- ⊢ lhs ≤ rhs
    case pos =>
      rcases h with ⟨x, hr, hl⟩
      suffices rhs ≥ x from nomatch not_lt.2 this hr
      have : ∀ a, ∃ b, x < g a b := fun a =>
        lt_iSup_iff.1 <| lt_of_not_le fun h =>
            lt_irrefl x (lt_of_lt_of_le hl (le_trans (iInf_le _ a) h))
      choose f hf using this
      refine le_trans ?_ (le_iSup _ f)
      refine le_iInf fun a => le_of_lt (hf a)
    case neg =>
      refine le_of_not_lt fun hrl : rhs < lhs => not_le_of_lt hrl ?_
      replace h : ∀ x, x ≤ rhs ∨ lhs ≤ x := by
        simpa only [not_exists, not_and_or, not_or, not_lt] using h
      have : ∀ a, ∃ b, rhs < g a b := fun a =>
        lt_iSup_iff.1 <| lt_of_lt_of_le hrl (iInf_le _ a)
      choose f hf using this
      have : ∀ a, lhs ≤ g a (f a) := fun a =>
        (h (g a (f a))).resolve_left (by simpa using hf a)
      refine le_trans ?_ (le_iSup _ f)
      refine le_iInf fun a => this _

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
  -- 🎉 no goals
#align Sup_inf_eq sSup_inf_eq

theorem iSup_inf_eq (f : ι → α) (a : α) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a := by
  rw [iSup, sSup_inf_eq, iSup_range]
  -- 🎉 no goals
#align supr_inf_eq iSup_inf_eq

theorem inf_iSup_eq (a : α) (f : ι → α) : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  simpa only [inf_comm] using iSup_inf_eq f a
  -- 🎉 no goals
#align inf_supr_eq inf_iSup_eq

instance Prod.frame (α β) [Frame α] [Frame β] : Frame (α × β) where
  __ := Prod.completeLattice α β
  inf_sSup_le_iSup_inf a s := by
    simp [Prod.le_def, sSup_eq_iSup, fst_iSup, snd_iSup, fst_iInf, snd_iInf, inf_iSup_eq]
    -- 🎉 no goals

theorem iSup₂_inf_eq {f : ∀ i, κ i → α} (a : α) : (⨆ (i) (j), f i j) ⊓ a = ⨆ (i) (j), f i j ⊓ a :=
  by simp only [iSup_inf_eq]
     -- 🎉 no goals
#align bsupr_inf_eq iSup₂_inf_eq

theorem inf_iSup₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊓ ⨆ (i) (j), f i j) = ⨆ (i) (j), a ⊓ f i j :=
  by simp only [inf_iSup_eq]
     -- 🎉 no goals
#align inf_bsupr_eq inf_iSup₂_eq

theorem iSup_inf_iSup {ι ι' : Type*} {f : ι → α} {g : ι' → α} :
    ((⨆ i, f i) ⊓ ⨆ j, g j) = ⨆ i : ι × ι', f i.1 ⊓ g i.2 := by
  simp_rw [iSup_inf_eq, inf_iSup_eq, iSup_prod]
  -- 🎉 no goals
#align supr_inf_supr iSup_inf_iSup

theorem biSup_inf_biSup {ι ι' : Type*} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨆ i ∈ s, f i) ⊓ ⨆ j ∈ t, g j) = ⨆ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊓ g p.2 := by
  simp only [iSup_subtype', iSup_inf_iSup]
  -- ⊢ ⨆ (i : { i // i ∈ s } × { i // i ∈ t }), f ↑i.fst ⊓ g ↑i.snd = ⨆ (x : { i // …
  exact (Equiv.surjective _).iSup_congr (Equiv.Set.prod s t).symm fun x => rfl
  -- 🎉 no goals
#align bsupr_inf_bsupr biSup_inf_biSup

theorem sSup_inf_sSup : sSup s ⊓ sSup t = ⨆ p ∈ s ×ˢ t, (p : α × α).1 ⊓ p.2 := by
  simp only [sSup_eq_iSup, biSup_inf_biSup]
  -- 🎉 no goals
#align Sup_inf_Sup sSup_inf_sSup

theorem iSup_disjoint_iff {f : ι → α} : Disjoint (⨆ i, f i) a ↔ ∀ i, Disjoint (f i) a := by
  simp only [disjoint_iff, iSup_inf_eq, iSup_eq_bot]
  -- 🎉 no goals
#align supr_disjoint_iff iSup_disjoint_iff

theorem disjoint_iSup_iff {f : ι → α} : Disjoint a (⨆ i, f i) ↔ ∀ i, Disjoint a (f i) := by
  simpa only [disjoint_comm] using @iSup_disjoint_iff
  -- 🎉 no goals
#align disjoint_supr_iff disjoint_iSup_iff

theorem iSup₂_disjoint_iff {f : ∀ i, κ i → α} :
    Disjoint (⨆ (i) (j), f i j) a ↔ ∀ i j, Disjoint (f i j) a := by
  simp_rw [iSup_disjoint_iff]
  -- 🎉 no goals
#align supr₂_disjoint_iff iSup₂_disjoint_iff

theorem disjoint_iSup₂_iff {f : ∀ i, κ i → α} :
    Disjoint a (⨆ (i) (j), f i j) ↔ ∀ i j, Disjoint a (f i j) := by
  simp_rw [disjoint_iSup_iff]
  -- 🎉 no goals
#align disjoint_supr₂_iff disjoint_iSup₂_iff

theorem sSup_disjoint_iff {s : Set α} : Disjoint (sSup s) a ↔ ∀ b ∈ s, Disjoint b a := by
  simp only [disjoint_iff, sSup_inf_eq, iSup_eq_bot]
  -- 🎉 no goals
#align Sup_disjoint_iff sSup_disjoint_iff

theorem disjoint_sSup_iff {s : Set α} : Disjoint a (sSup s) ↔ ∀ b ∈ s, Disjoint a b := by
  simpa only [disjoint_comm] using @sSup_disjoint_iff
  -- 🎉 no goals
#align disjoint_Sup_iff disjoint_sSup_iff

theorem iSup_inf_of_monotone {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] {f g : ι → α}
    (hf : Monotone f) (hg : Monotone g) : ⨆ i, f i ⊓ g i = (⨆ i, f i) ⊓ ⨆ i, g i := by
  refine' (le_iSup_inf_iSup f g).antisymm _
  -- ⊢ (⨆ (i : ι), f i) ⊓ ⨆ (i : ι), g i ≤ ⨆ (i : ι), f i ⊓ g i
  rw [iSup_inf_iSup]
  -- ⊢ ⨆ (i : ι × ι), f i.fst ⊓ g i.snd ≤ ⨆ (i : ι), f i ⊓ g i
  refine' iSup_mono' fun i => _
  -- ⊢ ∃ i', f i.fst ⊓ g i.snd ≤ f i' ⊓ g i'
  rcases directed_of (· ≤ ·) i.1 i.2 with ⟨j, h₁, h₂⟩
  -- ⊢ ∃ i', f i.fst ⊓ g i.snd ≤ f i' ⊓ g i'
  exact ⟨j, inf_le_inf (hf h₁) (hg h₂)⟩
  -- 🎉 no goals
#align supr_inf_of_monotone iSup_inf_of_monotone

theorem iSup_inf_of_antitone {ι : Type*} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {f g : ι → α}
    (hf : Antitone f) (hg : Antitone g) : ⨆ i, f i ⊓ g i = (⨆ i, f i) ⊓ ⨆ i, g i :=
  @iSup_inf_of_monotone α _ ιᵒᵈ _ _ f g hf.dual_left hg.dual_left
#align supr_inf_of_antitone iSup_inf_of_antitone

instance Pi.frame {ι : Type*} {π : ι → Type*} [∀ i, Frame (π i)] : Frame (∀ i, π i) :=
  { Pi.completeLattice with
    inf_sSup_le_iSup_inf := fun a s i => by
      simp only [sSup_apply, iSup_apply, inf_apply, inf_iSup_eq, ← iSup_subtype'']; rfl }
      -- ⊢ ⨆ (i_1 : ↑s), a i ⊓ ↑i_1 i ≤ ⨆ (i_1 : ↑s), a i ⊓ ↑i_1 i
                                                                                    -- 🎉 no goals
#align pi.frame Pi.frame

-- see Note [lower instance priority]
instance (priority := 100) Frame.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    rw [← sSup_pair, ← sSup_pair, inf_sSup_eq, ← sSup_image, image_pair]
    -- 🎉 no goals
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

instance Prod.coframe (α β) [Coframe α] [Coframe β] : Coframe (α × β) where
  __ := Prod.completeLattice α β
  iInf_sup_le_sup_sInf a s := by
    simp [Prod.le_def, sInf_eq_iInf, fst_iSup, snd_iSup, fst_iInf, snd_iInf, sup_iInf_eq]
    -- 🎉 no goals

theorem iInf₂_sup_eq {f : ∀ i, κ i → α} (a : α) : (⨅ (i) (j), f i j) ⊔ a = ⨅ (i) (j), f i j ⊔ a :=
  @iSup₂_inf_eq αᵒᵈ _ _ _ _ _
#align binfi_sup_eq iInf₂_sup_eq

theorem sup_iInf₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊔ ⨅ (i) (j), f i j) = ⨅ (i) (j), a ⊔ f i j :=
  @inf_iSup₂_eq αᵒᵈ _ _ _ _ _
#align sup_binfi_eq sup_iInf₂_eq

theorem iInf_sup_iInf {ι ι' : Type*} {f : ι → α} {g : ι' → α} :
    ((⨅ i, f i) ⊔ ⨅ i, g i) = ⨅ i : ι × ι', f i.1 ⊔ g i.2 :=
  @iSup_inf_iSup αᵒᵈ _ _ _ _ _
#align infi_sup_infi iInf_sup_iInf

theorem biInf_sup_biInf {ι ι' : Type*} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨅ i ∈ s, f i) ⊔ ⨅ j ∈ t, g j) = ⨅ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊔ g p.2 :=
  @biSup_inf_biSup αᵒᵈ _ _ _ _ _ _ _
#align binfi_sup_binfi biInf_sup_biInf

theorem sInf_sup_sInf : sInf s ⊔ sInf t = ⨅ p ∈ s ×ˢ t, (p : α × α).1 ⊔ p.2 :=
  @sSup_inf_sSup αᵒᵈ _ _ _
#align Inf_sup_Inf sInf_sup_sInf

theorem iInf_sup_of_monotone {ι : Type*} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {f g : ι → α}
    (hf : Monotone f) (hg : Monotone g) : ⨅ i, f i ⊔ g i = (⨅ i, f i) ⊔ ⨅ i, g i :=
  @iSup_inf_of_antitone αᵒᵈ _ _ _ _ _ _ hf.dual_right hg.dual_right
#align infi_sup_of_monotone iInf_sup_of_monotone

theorem iInf_sup_of_antitone {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] {f g : ι → α}
    (hf : Antitone f) (hg : Antitone g) : ⨅ i, f i ⊔ g i = (⨅ i, f i) ⊔ ⨅ i, g i :=
  @iSup_inf_of_monotone αᵒᵈ _ _ _ _ _ _ hf.dual_right hg.dual_right
#align infi_sup_of_antitone iInf_sup_of_antitone

instance Pi.coframe {ι : Type*} {π : ι → Type*} [∀ i, Coframe (π i)] : Coframe (∀ i, π i) :=
  { Pi.completeLattice with
    iInf_sup_le_sup_sInf := fun a s i => by
      simp only [sInf_apply, iInf_apply, sup_apply, sup_iInf_eq, ← iInf_subtype'']; rfl }
      -- ⊢ ⨅ (i_1 : ↑s), a i ⊔ ↑i_1 i ≤ ⨅ (i_1 : ↑s), a i ⊔ ↑i_1 i
                                                                                    -- 🎉 no goals
#align pi.coframe Pi.coframe

-- see Note [lower instance priority]
instance (priority := 100) Coframe.toDistribLattice : DistribLattice α :=
  { ‹Coframe α› with
    le_sup_inf := fun a b c => by
      rw [← sInf_pair, ← sInf_pair, sup_sInf_eq, ← sInf_image, image_pair] }
      -- 🎉 no goals
#align coframe.to_distrib_lattice Coframe.toDistribLattice

end Coframe

section CompleteDistribLattice

variable [CompleteDistribLattice α] {a b : α} {s t : Set α}

-- Porting note: this is mysteriously slow. Minimised in
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Performance.20issue.20with.20.60CompleteBooleanAlgebra.60
-- but not yet resolved.
instance OrderDual.completeDistribLattice (α) [CompleteDistribLattice α] :
    CompleteDistribLattice αᵒᵈ :=
  { OrderDual.frame, OrderDual.coframe with }

instance Prod.completeDistribLattice (α β)
    [CompleteDistribLattice α] [CompleteDistribLattice β] :
    CompleteDistribLattice (α × β) where
  __ := Prod.completeLattice α β
  __ := Prod.frame α β
  __ := Prod.coframe α β

instance Pi.completeDistribLattice {ι : Type*} {π : ι → Type*}
    [∀ i, CompleteDistribLattice (π i)] : CompleteDistribLattice (∀ i, π i) :=
  { Pi.frame, Pi.coframe with }
#align pi.complete_distrib_lattice Pi.completeDistribLattice

end CompleteDistribLattice

section CompletelyDistribLattice

instance OrderDual.completelyDistribLattice (α) [CompletelyDistribLattice α] :
    CompletelyDistribLattice αᵒᵈ where
  __ := OrderDual.completeLattice α
  iInf_iSup_eq _ := iSup_iInf_eq (α := α)

instance Prod.completelyDistribLattice (α β)
    [CompletelyDistribLattice α] [CompletelyDistribLattice β] :
    CompletelyDistribLattice (α × β) where
  __ := Prod.completeLattice α β
  iInf_iSup_eq f := by ext <;> simp [fst_iSup, fst_iInf, snd_iSup, snd_iInf, iInf_iSup_eq]
                       -- ⊢ (⨅ (a : ι✝), ⨆ (b : κ✝ a), f a b).fst = (⨆ (g : (a : ι✝) → κ✝ a), ⨅ (a : ι✝) …
                               -- 🎉 no goals
                               -- 🎉 no goals

instance Pi.completelyDistribLattice {ι : Type*} {π : ι → Type*}
    [∀ i, CompletelyDistribLattice (π i)] : CompletelyDistribLattice (∀ i, π i) where
  __ := Pi.completeLattice
  iInf_iSup_eq f := by ext i; simp only [iInf_apply, iSup_apply, iInf_iSup_eq]
                       -- ⊢ iInf (fun a => ⨆ (b : κ✝ a), f a b) i = iSup (fun g => ⨅ (a : ι✝), f a (g a) …
                              -- 🎉 no goals

end CompletelyDistribLattice

/--
A complete Boolean algebra is a Boolean algebra that is also a complete distributive lattice.

It is only completely distributive if it is also atomic.
-/
class CompleteBooleanAlgebra (α) extends BooleanAlgebra α, CompleteDistribLattice α
#align complete_boolean_algebra CompleteBooleanAlgebra

instance Prod.completeBooleanAlgebra (α β)
    [CompleteBooleanAlgebra α] [CompleteBooleanAlgebra β] :
    CompleteBooleanAlgebra (α × β) where
  __ := Prod.booleanAlgebra α β
  __ := Prod.completeDistribLattice α β

instance Pi.completeBooleanAlgebra {ι : Type*} {π : ι → Type*}
    [∀ i, CompleteBooleanAlgebra (π i)] : CompleteBooleanAlgebra (∀ i, π i) :=
  { Pi.booleanAlgebra, Pi.completeDistribLattice with }
#align pi.complete_boolean_algebra Pi.completeBooleanAlgebra

instance OrderDual.completeBooleanAlgebra (α) [CompleteBooleanAlgebra α] :
    CompleteBooleanAlgebra αᵒᵈ where
  __ := OrderDual.booleanAlgebra α
  __ := OrderDual.completeDistribLattice α

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] {a b : α} {s : Set α} {f : ι → α}

theorem compl_iInf : (iInf f)ᶜ = ⨆ i, (f i)ᶜ :=
  le_antisymm
    (compl_le_of_compl_le <| le_iInf fun i => compl_le_of_compl_le <|
      le_iSup (HasCompl.compl ∘ f) i)
    (iSup_le fun _ => compl_le_compl <| iInf_le _ _)
#align compl_infi compl_iInf

theorem compl_iSup : (iSup f)ᶜ = ⨅ i, (f i)ᶜ :=
  compl_injective (by simp [compl_iInf])
                      -- 🎉 no goals
#align compl_supr compl_iSup

theorem compl_sInf : (sInf s)ᶜ = ⨆ i ∈ s, iᶜ := by simp only [sInf_eq_iInf, compl_iInf]
                                                   -- 🎉 no goals
#align compl_Inf compl_sInf

theorem compl_sSup : (sSup s)ᶜ = ⨅ i ∈ s, iᶜ := by simp only [sSup_eq_iSup, compl_iSup]
                                                   -- 🎉 no goals
#align compl_Sup compl_sSup

theorem compl_sInf' : (sInf s)ᶜ = sSup (HasCompl.compl '' s) :=
  compl_sInf.trans sSup_image.symm
#align compl_Inf' compl_sInf'

theorem compl_sSup' : (sSup s)ᶜ = sInf (HasCompl.compl '' s) :=
  compl_sSup.trans sInf_image.symm
#align compl_Sup' compl_sSup'

end CompleteBooleanAlgebra

/--
A complete atomic Boolean algebra is a complete Boolean algebra
that is also completely distributive.

We take iSup_iInf_eq as the definition here,
and prove later on that this implies atomicity.
-/
class CompleteAtomicBooleanAlgebra (α : Type u) extends
    CompletelyDistribLattice α, CompleteBooleanAlgebra α where
  iInf_sup_le_sup_sInf := CompletelyDistribLattice.toCompleteDistribLattice.iInf_sup_le_sup_sInf
  inf_sSup_le_iSup_inf := CompletelyDistribLattice.toCompleteDistribLattice.inf_sSup_le_iSup_inf

instance Prod.completeAtomicBooleanAlgebra (α β)
    [CompleteAtomicBooleanAlgebra α] [CompleteAtomicBooleanAlgebra β] :
    CompleteAtomicBooleanAlgebra (α × β) where
  __ := Prod.booleanAlgebra α β
  __ := Prod.completelyDistribLattice α β

instance Pi.completeAtomicBooleanAlgebra {ι : Type*} {π : ι → Type*}
    [∀ i, CompleteAtomicBooleanAlgebra (π i)] : CompleteAtomicBooleanAlgebra (∀ i, π i) where
  __ := Pi.completeBooleanAlgebra
  iInf_iSup_eq f := by ext; rw [iInf_iSup_eq]
                       -- ⊢ iInf (fun a => ⨆ (b : κ✝ a), f a b) x✝ = iSup (fun g => ⨅ (a : ι✝), f a (g a …
                            -- 🎉 no goals

instance OrderDual.completeAtomicBooleanAlgebra (α) [CompleteAtomicBooleanAlgebra α] :
    CompleteAtomicBooleanAlgebra αᵒᵈ where
  __ := OrderDual.completeBooleanAlgebra α
  __ := OrderDual.completelyDistribLattice α

instance Prop.completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra Prop where
  __ := Prop.completeLattice
  __ := Prop.booleanAlgebra
  iInf_iSup_eq f := by simp [Classical.skolem]
                       -- 🎉 no goals

instance Prop.completeBooleanAlgebra : CompleteBooleanAlgebra Prop := inferInstance
#align Prop.complete_boolean_algebra Prop.completeBooleanAlgebra

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
      -- ⊢ f (a ⊓ sSup s) ≤ f (⨆ (b : α) (_ : b ∈ s), a ⊓ b)
      rw [← sSup_image, map_inf, map_sSup s, inf_iSup₂_eq]
      -- ⊢ ⨆ (i : α) (_ : i ∈ s), f a ⊓ f i ≤ f (sSup ((fun b => a ⊓ b) '' s))
      simp_rw [← map_inf]
      -- ⊢ ⨆ (i : α) (_ : i ∈ s), f (a ⊓ i) ≤ f (sSup ((fun a_1 => a ⊓ a_1) '' s))
      exact ((map_sSup _).trans iSup_image).ge }
      -- 🎉 no goals
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
      -- ⊢ f (⨅ (b : α) (_ : b ∈ s), a ⊔ b) ≤ f (a ⊔ sInf s)
      rw [← sInf_image, map_sup, map_sInf s, sup_iInf₂_eq]
      -- ⊢ f (sInf ((fun b => a ⊔ b) '' s)) ≤ ⨅ (i : α) (_ : i ∈ s), f a ⊔ f i
      simp_rw [← map_sup]
      -- ⊢ f (sInf ((fun a_1 => a ⊔ a_1) '' s)) ≤ ⨅ (i : α) (_ : i ∈ s), f (a ⊔ i)
      exact ((map_sInf _).trans iInf_image).le }
      -- 🎉 no goals
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
/-- Pullback a `CompletelyDistribLattice` along an injection. -/
@[reducible]
protected def Function.Injective.completelyDistribLattice [Sup α] [Inf α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [CompletelyDistribLattice β] (f : α → β) (hf : Function.Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompletelyDistribLattice α where
  __ := hf.completeLattice f map_sup map_inf map_sSup map_sInf map_top map_bot
  iInf_iSup_eq g := hf <| by
    simp_rw [iInf, map_sInf, iInf_range, iSup, map_sSup, iSup_range, map_sInf, iInf_range,
      iInf_iSup_eq]

-- See note [reducible non-instances]
/-- Pullback a `CompleteBooleanAlgebra` along an injection. -/
@[reducible]
protected def Function.Injective.completeBooleanAlgebra [Sup α] [Inf α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [HasCompl α] [SDiff α] [CompleteBooleanAlgebra β] (f : α → β)
    (hf : Function.Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a)
    (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompleteBooleanAlgebra α :=
  { hf.completeDistribLattice f map_sup map_inf map_sSup map_sInf map_top map_bot,
    hf.booleanAlgebra f map_sup map_inf map_top map_bot map_compl map_sdiff with }
#align function.injective.complete_boolean_algebra Function.Injective.completeBooleanAlgebra

-- See note [reducible non-instances]
/-- Pullback a `CompleteAtomicBooleanAlgebra` along an injection. -/
@[reducible]
protected def Function.Injective.completeAtomicBooleanAlgebra [Sup α] [Inf α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [HasCompl α] [SDiff α] [CompleteAtomicBooleanAlgebra β] (f : α → β)
    (hf : Function.Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a)
    (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompleteAtomicBooleanAlgebra α where
  __ := hf.completelyDistribLattice f map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.booleanAlgebra f map_sup map_inf map_top map_bot map_compl map_sdiff

end lift

namespace PUnit

variable (s : Set PUnit.{u + 1}) (x y : PUnit.{u + 1})

instance completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra PUnit := by
  refine'
    { PUnit.booleanAlgebra with
      sSup := fun _ => unit
      sInf := fun _ => unit
      .. } <;>
  (intros; trivial)
   -- ⊢ a✝¹ ≤ sSup s✝
           -- 🎉 no goals
   -- ⊢ sSup s✝ ≤ a✝¹
           -- 🎉 no goals
   -- ⊢ sInf s✝ ≤ a✝¹
           -- 🎉 no goals
   -- ⊢ a✝¹ ≤ sInf s✝
           -- 🎉 no goals
   -- ⊢ ⨅ (a : ι✝), ⨆ (b : κ✝ a), f✝ a b = ⨆ (g : (a : ι✝) → κ✝ a), ⨅ (a : ι✝), f✝ a …
           -- 🎉 no goals
   -- ⊢ a✝ ⊓ sSup s✝ ≤ ⨆ (b : PUnit) (_ : b ∈ s✝), a✝ ⊓ b
           -- 🎉 no goals
   -- ⊢ ⨅ (b : PUnit) (_ : b ∈ s✝), a✝ ⊔ b ≤ a✝ ⊔ sInf s✝
           -- 🎉 no goals

instance completeBooleanAlgebra : CompleteBooleanAlgebra PUnit := inferInstance

instance completeLinearOrder : CompleteLinearOrder PUnit :=
  { PUnit.completeBooleanAlgebra, PUnit.linearOrder with }

@[simp]
theorem sSup_eq : sSup s = unit :=
  rfl
#align punit.Sup_eq PUnit.sSup_eq

@[simp]
theorem sInf_eq : sInf s = unit :=
  rfl
#align punit.Inf_eq PUnit.sInf_eq

end PUnit
