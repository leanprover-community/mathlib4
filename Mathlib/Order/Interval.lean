/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.interval
! leanprover-community/mathlib commit 6623e6af705e97002a9054c1c05a980180276fc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Intervals.Basic
import Mathbin.Data.Set.Lattice
import Mathbin.Data.SetLike.Basic

/-!
# Order intervals

This file defines (nonempty) closed intervals in an order (see `set.Icc`). This is a prototype for
interval arithmetic.

## Main declarations

* `nonempty_interval`: Nonempty intervals. Pairs where the second element is greater than the first.
* `interval`: Intervals. Either `∅` or a nonempty interval.
-/


open Function OrderDual Set

variable {α β γ δ : Type _} {ι : Sort _} {κ : ι → Sort _}

/-- The nonempty closed intervals in an order.

We define intervals by the pair of endpoints `fst`, `snd`. To convert intervals to the set of
elements between these endpoints, use the coercion `nonempty_interval α → set α`. -/
@[ext]
structure NonemptyInterval (α : Type _) [LE α] extends α × α where
  fst_le_snd : fst ≤ snd
#align nonempty_interval NonemptyInterval

namespace NonemptyInterval

section LE

variable [LE α] {s t : NonemptyInterval α}

theorem toProd_injective : Injective (toProd : NonemptyInterval α → α × α) := fun s t =>
  (ext_iff _ _).2
#align nonempty_interval.to_prod_injective NonemptyInterval.toProd_injective

/-- The injection that induces the order on intervals. -/
def toDualProd : NonemptyInterval α → αᵒᵈ × α :=
  toProd
#align nonempty_interval.to_dual_prod NonemptyInterval.toDualProd

@[simp]
theorem toDualProd_apply (s : NonemptyInterval α) : s.toDualProd = (toDual s.fst, s.snd) :=
  Prod.mk.eta.symm
#align nonempty_interval.to_dual_prod_apply NonemptyInterval.toDualProd_apply

theorem toDualProd_injective : Injective (toDualProd : NonemptyInterval α → αᵒᵈ × α) :=
  toProd_injective
#align nonempty_interval.to_dual_prod_injective NonemptyInterval.toDualProd_injective

instance [IsEmpty α] : IsEmpty (NonemptyInterval α) :=
  ⟨fun s => isEmptyElim s.fst⟩

instance [Subsingleton α] : Subsingleton (NonemptyInterval α) :=
  toDualProd_injective.Subsingleton

instance : LE (NonemptyInterval α) :=
  ⟨fun s t => t.fst ≤ s.fst ∧ s.snd ≤ t.snd⟩

theorem le_def : s ≤ t ↔ t.fst ≤ s.fst ∧ s.snd ≤ t.snd :=
  Iff.rfl
#align nonempty_interval.le_def NonemptyInterval.le_def

/-- `to_dual_prod` as an order embedding. -/
@[simps]
def toDualProdHom : NonemptyInterval α ↪o αᵒᵈ × α
    where
  toFun := toDualProd
  inj' := toDualProd_injective
  map_rel_iff' _ _ := Iff.rfl
#align nonempty_interval.to_dual_prod_hom NonemptyInterval.toDualProdHom

/-- Turn an interval into an interval in the dual order. -/
def dual : NonemptyInterval α ≃ NonemptyInterval αᵒᵈ
    where
  toFun s := ⟨s.toProd.symm, s.fst_le_snd⟩
  invFun s := ⟨s.toProd.symm, s.fst_le_snd⟩
  left_inv s := ext _ _ <| Prod.swap_swap _
  right_inv s := ext _ _ <| Prod.swap_swap _
#align nonempty_interval.dual NonemptyInterval.dual

@[simp]
theorem fst_dual (s : NonemptyInterval α) : s.dual.fst = toDual s.snd :=
  rfl
#align nonempty_interval.fst_dual NonemptyInterval.fst_dual

@[simp]
theorem snd_dual (s : NonemptyInterval α) : s.dual.snd = toDual s.fst :=
  rfl
#align nonempty_interval.snd_dual NonemptyInterval.snd_dual

end LE

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] {s : NonemptyInterval α} {x : α × α}
  {a : α}

instance : Preorder (NonemptyInterval α) :=
  Preorder.lift toDualProd

instance : CoeTC (NonemptyInterval α) (Set α) :=
  ⟨fun s => Icc s.fst s.snd⟩

instance (priority := 100) : Membership α (NonemptyInterval α) :=
  ⟨fun a s => a ∈ (s : Set α)⟩

@[simp]
theorem mem_mk {hx : x.1 ≤ x.2} : a ∈ mk x hx ↔ x.1 ≤ a ∧ a ≤ x.2 :=
  Iff.rfl
#align nonempty_interval.mem_mk NonemptyInterval.mem_mk

theorem mem_def : a ∈ s ↔ s.fst ≤ a ∧ a ≤ s.snd :=
  Iff.rfl
#align nonempty_interval.mem_def NonemptyInterval.mem_def

@[simp]
theorem coe_nonempty (s : NonemptyInterval α) : (s : Set α).Nonempty :=
  nonempty_Icc.2 s.fst_le_snd
#align nonempty_interval.coe_nonempty NonemptyInterval.coe_nonempty

/-- `{a}` as an interval. -/
@[simps]
def pure (a : α) : NonemptyInterval α :=
  ⟨⟨a, a⟩, le_rfl⟩
#align nonempty_interval.pure NonemptyInterval.pure

theorem mem_pure_self (a : α) : a ∈ pure a :=
  ⟨le_rfl, le_rfl⟩
#align nonempty_interval.mem_pure_self NonemptyInterval.mem_pure_self

theorem pure_injective : Injective (pure : α → NonemptyInterval α) := fun s t =>
  congr_arg <| Prod.fst ∘ toProd
#align nonempty_interval.pure_injective NonemptyInterval.pure_injective

@[simp]
theorem dual_pure (a : α) : (pure a).dual = pure (toDual a) :=
  rfl
#align nonempty_interval.dual_pure NonemptyInterval.dual_pure

instance [Inhabited α] : Inhabited (NonemptyInterval α) :=
  ⟨pure default⟩

instance : ∀ [Nonempty α], Nonempty (NonemptyInterval α) :=
  Nonempty.map pure

instance [Nontrivial α] : Nontrivial (NonemptyInterval α) :=
  pure_injective.Nontrivial

/-- Pushforward of nonempty intervals. -/
@[simps]
def map (f : α →o β) (a : NonemptyInterval α) : NonemptyInterval β :=
  ⟨a.toProd.map f f, f.mono a.fst_le_snd⟩
#align nonempty_interval.map NonemptyInterval.map

@[simp]
theorem map_pure (f : α →o β) (a : α) : (pure a).map f = pure (f a) :=
  rfl
#align nonempty_interval.map_pure NonemptyInterval.map_pure

@[simp]
theorem map_map (g : β →o γ) (f : α →o β) (a : NonemptyInterval α) :
    (a.map f).map g = a.map (g.comp f) :=
  rfl
#align nonempty_interval.map_map NonemptyInterval.map_map

@[simp]
theorem dual_map (f : α →o β) (a : NonemptyInterval α) : (a.map f).dual = a.dual.map f.dual :=
  rfl
#align nonempty_interval.dual_map NonemptyInterval.dual_map

/-- Binary pushforward of nonempty intervals. -/
@[simps]
def map₂ (f : α → β → γ) (h₀ : ∀ b, Monotone fun a => f a b) (h₁ : ∀ a, Monotone (f a)) :
    NonemptyInterval α → NonemptyInterval β → NonemptyInterval γ := fun s t =>
  ⟨(f s.fst t.fst, f s.snd t.snd), (h₀ _ s.fst_le_snd).trans <| h₁ _ t.fst_le_snd⟩
#align nonempty_interval.map₂ NonemptyInterval.map₂

@[simp]
theorem map₂_pure (f : α → β → γ) (h₀ h₁) (a : α) (b : β) :
    map₂ f h₀ h₁ (pure a) (pure b) = pure (f a b) :=
  rfl
#align nonempty_interval.map₂_pure NonemptyInterval.map₂_pure

@[simp]
theorem dual_map₂ (f : α → β → γ) (h₀ h₁ s t) :
    (map₂ f h₀ h₁ s t).dual =
      map₂ (fun a b => toDual <| f (ofDual a) <| ofDual b) (fun _ => (h₀ _).dual)
        (fun _ => (h₁ _).dual) s.dual t.dual :=
  rfl
#align nonempty_interval.dual_map₂ NonemptyInterval.dual_map₂

variable [BoundedOrder α]

instance : OrderTop (NonemptyInterval α)
    where
  top := ⟨⟨⊥, ⊤⟩, bot_le⟩
  le_top a := ⟨bot_le, le_top⟩

@[simp]
theorem dual_top : (⊤ : NonemptyInterval α).dual = ⊤ :=
  rfl
#align nonempty_interval.dual_top NonemptyInterval.dual_top

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] {s t : NonemptyInterval α} {x : α × α} {a b : α}

instance : PartialOrder (NonemptyInterval α) :=
  PartialOrder.lift _ toDualProd_injective

/-- Consider a nonempty interval `[a, b]` as the set `[a, b]`. -/
def coeHom : NonemptyInterval α ↪o Set α :=
  OrderEmbedding.ofMapLEIff (fun s => Icc s.fst s.snd) fun s t => Icc_subset_Icc_iff s.fst_le_snd
#align nonempty_interval.coe_hom NonemptyInterval.coeHom

instance : SetLike (NonemptyInterval α) α
    where
  coe s := Icc s.fst s.snd
  coe_injective' := coeHom.Injective

@[simp, norm_cast]
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ s ≤ t :=
  (@coeHom α _).le_iff_le
#align nonempty_interval.coe_subset_coe NonemptyInterval.coe_subset_coe

@[simp, norm_cast]
theorem coe_sSubset_coe : (s : Set α) ⊂ t ↔ s < t :=
  (@coeHom α _).lt_iff_lt
#align nonempty_interval.coe_ssubset_coe NonemptyInterval.coe_sSubset_coe

@[simp]
theorem coe_coeHom : (coeHom : NonemptyInterval α → Set α) = coe :=
  rfl
#align nonempty_interval.coe_coe_hom NonemptyInterval.coe_coeHom

@[simp, norm_cast]
theorem coe_pure (a : α) : (pure a : Set α) = {a} :=
  Icc_self _
#align nonempty_interval.coe_pure NonemptyInterval.coe_pure

@[simp]
theorem mem_pure : b ∈ pure a ↔ b = a := by rw [← SetLike.mem_coe, coe_pure, mem_singleton_iff]
#align nonempty_interval.mem_pure NonemptyInterval.mem_pure

@[simp, norm_cast]
theorem coe_top [BoundedOrder α] : ((⊤ : NonemptyInterval α) : Set α) = univ :=
  Icc_bot_top
#align nonempty_interval.coe_top NonemptyInterval.coe_top

@[simp, norm_cast]
theorem coe_dual (s : NonemptyInterval α) : (s.dual : Set αᵒᵈ) = ofDual ⁻¹' s :=
  dual_Icc
#align nonempty_interval.coe_dual NonemptyInterval.coe_dual

theorem subset_coe_map (f : α →o β) (s : NonemptyInterval α) : f '' s ⊆ s.map f :=
  image_subset_iff.2 fun a ha => ⟨f.mono ha.1, f.mono ha.2⟩
#align nonempty_interval.subset_coe_map NonemptyInterval.subset_coe_map

end PartialOrder

section Lattice

variable [Lattice α]

instance : Sup (NonemptyInterval α) :=
  ⟨fun s t => ⟨⟨s.fst ⊓ t.fst, s.snd ⊔ t.snd⟩, inf_le_left.trans <| s.fst_le_snd.trans le_sup_left⟩⟩

instance : SemilatticeSup (NonemptyInterval α) :=
  toDualProd_injective.SemilatticeSup _ fun _ _ => rfl

@[simp]
theorem fst_sup (s t : NonemptyInterval α) : (s ⊔ t).fst = s.fst ⊓ t.fst :=
  rfl
#align nonempty_interval.fst_sup NonemptyInterval.fst_sup

@[simp]
theorem snd_sup (s t : NonemptyInterval α) : (s ⊔ t).snd = s.snd ⊔ t.snd :=
  rfl
#align nonempty_interval.snd_sup NonemptyInterval.snd_sup

end Lattice

end NonemptyInterval

/-- The closed intervals in an order.

We represent intervals either as `⊥` or a nonempty interval given by its endpoints `fst`, `snd`.
To convert intervals to the set of elements between these endpoints, use the coercion
`interval α → set α`. -/
def Interval (α : Type _) [LE α] :=
  WithBot (NonemptyInterval α)deriving Inhabited, LE, OrderBot
#align interval Interval

namespace Interval

section LE

variable [LE α] {s t : Interval α}

instance : CoeTC (NonemptyInterval α) (Interval α) :=
  WithBot.hasCoeT

instance canLift : CanLift (Interval α) (NonemptyInterval α) coe fun r => r ≠ ⊥ :=
  WithBot.canLift
#align interval.can_lift Interval.canLift

theorem coe_injective : Injective (coe : NonemptyInterval α → Interval α) :=
  WithBot.coe_injective
#align interval.coe_injective Interval.coe_injective

@[simp, norm_cast]
theorem coe_inj {s t : NonemptyInterval α} : (s : Interval α) = t ↔ s = t :=
  WithBot.coe_inj
#align interval.coe_inj Interval.coe_inj

@[protected]
theorem forall {p : Interval α → Prop} : (∀ s, p s) ↔ p ⊥ ∧ ∀ s : NonemptyInterval α, p s :=
  Option.forall
#align interval.forall Interval.forall

@[protected]
theorem exists {p : Interval α → Prop} : (∃ s, p s) ↔ p ⊥ ∨ ∃ s : NonemptyInterval α, p s :=
  Option.exists
#align interval.exists Interval.exists

instance [IsEmpty α] : Unique (Interval α) :=
  Option.unique

/-- Turn an interval into an interval in the dual order. -/
def dual : Interval α ≃ Interval αᵒᵈ :=
  NonemptyInterval.dual.optionCongr
#align interval.dual Interval.dual

end LE

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ]

instance : Preorder (Interval α) :=
  WithBot.preorder

/-- `{a}` as an interval. -/
def pure (a : α) : Interval α :=
  NonemptyInterval.pure a
#align interval.pure Interval.pure

theorem pure_injective : Injective (pure : α → Interval α) :=
  coe_injective.comp NonemptyInterval.pure_injective
#align interval.pure_injective Interval.pure_injective

@[simp]
theorem dual_pure (a : α) : (pure a).dual = pure (toDual a) :=
  rfl
#align interval.dual_pure Interval.dual_pure

@[simp]
theorem dual_bot : (⊥ : Interval α).dual = ⊥ :=
  rfl
#align interval.dual_bot Interval.dual_bot

@[simp]
theorem pure_ne_bot {a : α} : pure a ≠ ⊥ :=
  WithBot.coe_ne_bot
#align interval.pure_ne_bot Interval.pure_ne_bot

@[simp]
theorem bot_ne_pure {a : α} : ⊥ ≠ pure a :=
  WithBot.bot_ne_coe
#align interval.bot_ne_pure Interval.bot_ne_pure

instance [Nonempty α] : Nontrivial (Interval α) :=
  Option.nontrivial

/-- Pushforward of intervals. -/
def map (f : α →o β) : Interval α → Interval β :=
  WithBot.map (NonemptyInterval.map f)
#align interval.map Interval.map

@[simp]
theorem map_pure (f : α →o β) (a : α) : (pure a).map f = pure (f a) :=
  rfl
#align interval.map_pure Interval.map_pure

@[simp]
theorem map_map (g : β →o γ) (f : α →o β) (s : Interval α) : (s.map f).map g = s.map (g.comp f) :=
  Option.map_map _ _ _
#align interval.map_map Interval.map_map

@[simp]
theorem dual_map (f : α →o β) (s : Interval α) : (s.map f).dual = s.dual.map f.dual :=
  by
  cases s
  · rfl
  · exact WithBot.map_comm rfl _
#align interval.dual_map Interval.dual_map

variable [BoundedOrder α]

instance : BoundedOrder (Interval α) :=
  WithBot.boundedOrder

@[simp]
theorem dual_top : (⊤ : Interval α).dual = ⊤ :=
  rfl
#align interval.dual_top Interval.dual_top

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] {s t : Interval α} {a b : α}

instance : PartialOrder (Interval α) :=
  WithBot.partialOrder

/-- Consider a interval `[a, b]` as the set `[a, b]`. -/
def coeHom : Interval α ↪o Set α :=
  OrderEmbedding.ofMapLEIff
    (fun s =>
      match s with
      | ⊥ => ∅
      | some s => s)
    fun s t =>
    match s, t with
    | ⊥, t => iff_of_true bot_le bot_le
    | some s, ⊥ =>
      iff_of_false (fun h => s.coe_nonempty.ne_empty <| le_bot_iff.1 h) (WithBot.not_coe_le_bot _)
    | some s, some t => (@NonemptyInterval.coeHom α _).le_iff_le.trans WithBot.some_le_some.symm
#align interval.coe_hom Interval.coeHom

instance : SetLike (Interval α) α where
  coe := coeHom
  coe_injective' := coeHom.Injective

@[simp, norm_cast]
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ s ≤ t :=
  (@coeHom α _).le_iff_le
#align interval.coe_subset_coe Interval.coe_subset_coe

@[simp, norm_cast]
theorem coe_sSubset_coe : (s : Set α) ⊂ t ↔ s < t :=
  (@coeHom α _).lt_iff_lt
#align interval.coe_ssubset_coe Interval.coe_sSubset_coe

@[simp, norm_cast]
theorem coe_pure (a : α) : (pure a : Set α) = {a} :=
  Icc_self _
#align interval.coe_pure Interval.coe_pure

@[simp, norm_cast]
theorem coe_coe (s : NonemptyInterval α) : ((s : Interval α) : Set α) = s :=
  rfl
#align interval.coe_coe Interval.coe_coe

@[simp, norm_cast]
theorem coe_bot : ((⊥ : Interval α) : Set α) = ∅ :=
  rfl
#align interval.coe_bot Interval.coe_bot

@[simp, norm_cast]
theorem coe_top [BoundedOrder α] : ((⊤ : Interval α) : Set α) = univ :=
  Icc_bot_top
#align interval.coe_top Interval.coe_top

@[simp, norm_cast]
theorem coe_dual (s : Interval α) : (s.dual : Set αᵒᵈ) = ofDual ⁻¹' s :=
  by
  cases s
  · rfl
  exact s.coe_dual
#align interval.coe_dual Interval.coe_dual

theorem subset_coe_map (f : α →o β) : ∀ s : Interval α, f '' s ⊆ s.map f
  | ⊥ => by simp
  | (s : NonemptyInterval α) => s.subset_coe_map _
#align interval.subset_coe_map Interval.subset_coe_map

@[simp]
theorem mem_pure : b ∈ pure a ↔ b = a := by rw [← SetLike.mem_coe, coe_pure, mem_singleton_iff]
#align interval.mem_pure Interval.mem_pure

theorem mem_pure_self (a : α) : a ∈ pure a :=
  mem_pure.2 rfl
#align interval.mem_pure_self Interval.mem_pure_self

end PartialOrder

section Lattice

variable [Lattice α]

instance : SemilatticeSup (Interval α) :=
  WithBot.semilatticeSup

section Decidable

variable [@DecidableRel α (· ≤ ·)]

instance : Lattice (Interval α) :=
  {
    Interval.semilatticeSup with
    inf := fun s t =>
      match s, t with
      | ⊥, t => ⊥
      | s, ⊥ => ⊥
      | some s, some t =>
        if h : s.fst ≤ t.snd ∧ t.fst ≤ s.snd then
          some
            ⟨⟨s.fst ⊔ t.fst, s.snd ⊓ t.snd⟩,
              sup_le (le_inf s.fst_le_snd h.1) <| le_inf h.2 t.fst_le_snd⟩
        else ⊥
    inf_le_left := fun s t =>
      match s, t with
      | ⊥, ⊥ => bot_le
      | ⊥, some t => bot_le
      | some s, ⊥ => bot_le
      | some s, some t => by
        change dite _ _ _ ≤ _
        split_ifs
        · exact WithBot.some_le_some.2 ⟨le_sup_left, inf_le_left⟩
        · exact bot_le
    inf_le_right := fun s t =>
      match s, t with
      | ⊥, ⊥ => bot_le
      | ⊥, some t => bot_le
      | some s, ⊥ => bot_le
      | some s, some t => by
        change dite _ _ _ ≤ _
        split_ifs
        · exact WithBot.some_le_some.2 ⟨le_sup_right, inf_le_right⟩
        · exact bot_le
    le_inf := fun s t c =>
      match s, t, c with
      | ⊥, t, c => fun _ _ => bot_le
      | some s, t, c => fun hb hc =>
        by
        lift t to NonemptyInterval α using ne_bot_of_le_ne_bot WithBot.coe_ne_bot hb
        lift c to NonemptyInterval α using ne_bot_of_le_ne_bot WithBot.coe_ne_bot hc
        change _ ≤ dite _ _ _
        simp only [WithBot.some_eq_coe, WithBot.coe_le_coe] at hb hc⊢
        rw [dif_pos, WithBot.coe_le_coe]
        exact ⟨sup_le hb.1 hc.1, le_inf hb.2 hc.2⟩
        exact ⟨hb.1.trans <| s.fst_le_snd.trans hc.2, hc.1.trans <| s.fst_le_snd.trans hb.2⟩ }

@[simp, norm_cast]
theorem coe_inf (s t : Interval α) : (↑(s ⊓ t) : Set α) = s ∩ t :=
  by
  cases s
  · rw [WithBot.none_eq_bot, bot_inf_eq]
    exact (empty_inter _).symm
  cases t
  · rw [WithBot.none_eq_bot, inf_bot_eq]
    exact (inter_empty _).symm
  refine' (_ : coe (dite _ _ _) = _).trans Icc_inter_Icc.symm
  split_ifs
  · rfl
  ·
    exact
      (Icc_eq_empty fun H =>
          h
            ⟨le_sup_left.trans <| H.trans inf_le_right,
              le_sup_right.trans <| H.trans inf_le_left⟩).symm
#align interval.coe_inf Interval.coe_inf

end Decidable

@[simp, norm_cast]
theorem disjoint_coe (s t : Interval α) : Disjoint (s : Set α) t ↔ Disjoint s t := by
  classical
    rw [disjoint_iff_inf_le, disjoint_iff_inf_le, le_eq_subset, ← coe_subset_coe, coe_inf]
    rfl
#align interval.disjoint_coe Interval.disjoint_coe

end Lattice

end Interval

namespace NonemptyInterval

section Preorder

variable [Preorder α] {s : NonemptyInterval α} {a : α}

@[simp, norm_cast]
theorem coe_pure_interval (a : α) : (pure a : Interval α) = Interval.pure a :=
  rfl
#align nonempty_interval.coe_pure_interval NonemptyInterval.coe_pure_interval

@[simp, norm_cast]
theorem coe_eq_pure : (s : Interval α) = Interval.pure a ↔ s = pure a := by
  rw [← Interval.coe_inj, coe_pure_interval]
#align nonempty_interval.coe_eq_pure NonemptyInterval.coe_eq_pure

@[simp, norm_cast]
theorem coe_top_interval [BoundedOrder α] : ((⊤ : NonemptyInterval α) : Interval α) = ⊤ :=
  rfl
#align nonempty_interval.coe_top_interval NonemptyInterval.coe_top_interval

end Preorder

@[simp, norm_cast]
theorem mem_coe_interval [PartialOrder α] {s : NonemptyInterval α} {x : α} :
    x ∈ (s : Interval α) ↔ x ∈ s :=
  Iff.rfl
#align nonempty_interval.mem_coe_interval NonemptyInterval.mem_coe_interval

@[simp, norm_cast]
theorem coe_sup_interval [Lattice α] (s t : NonemptyInterval α) : (↑(s ⊔ t) : Interval α) = s ⊔ t :=
  rfl
#align nonempty_interval.coe_sup_interval NonemptyInterval.coe_sup_interval

end NonemptyInterval

namespace Interval

section CompleteLattice

variable [CompleteLattice α]

noncomputable instance [@DecidableRel α (· ≤ ·)] : CompleteLattice (Interval α) := by
  classical exact
      { Interval.lattice,
        Interval.boundedOrder with
        supₛ := fun S =>
          if h : S ⊆ {⊥} then ⊥
          else
            some
              ⟨⟨⨅ (s : NonemptyInterval α) (h : ↑s ∈ S), s.fst,
                  ⨆ (s : NonemptyInterval α) (h : ↑s ∈ S), s.snd⟩,
                by
                obtain ⟨s, hs, ha⟩ := not_subset.1 h
                lift s to NonemptyInterval α using ha
                exact infᵢ₂_le_of_le s hs (le_supᵢ₂_of_le s hs s.fst_le_snd)⟩
        le_sup := fun s s ha => by
          split_ifs
          · exact (h ha).le
          cases s
          · exact bot_le
          · exact WithBot.some_le_some.2 ⟨infᵢ₂_le _ ha, le_supᵢ₂_of_le _ ha le_rfl⟩
        sup_le := fun s s ha => by
          split_ifs
          · exact bot_le
          obtain ⟨b, hs, hb⟩ := not_subset.1 h
          lift s to NonemptyInterval α using ne_bot_of_le_ne_bot hb (ha _ hs)
          exact
            WithBot.coe_le_coe.2
              ⟨le_infᵢ₂ fun c hc => (WithBot.coe_le_coe.1 <| ha _ hc).1,
                supᵢ₂_le fun c hc => (WithBot.coe_le_coe.1 <| ha _ hc).2⟩
        infₛ := fun S =>
          if h :
              ⊥ ∉ S ∧
                ∀ ⦃s : NonemptyInterval α⦄,
                  ↑s ∈ S → ∀ ⦃t : NonemptyInterval α⦄, ↑t ∈ S → s.fst ≤ t.snd then
            some
              ⟨⟨⨆ (s : NonemptyInterval α) (h : ↑s ∈ S), s.fst,
                  ⨅ (s : NonemptyInterval α) (h : ↑s ∈ S), s.snd⟩,
                supᵢ₂_le fun s hs => le_infᵢ₂ <| h.2 hs⟩
          else ⊥
        inf_le := fun s s ha => by
          split_ifs
          · lift s to NonemptyInterval α using ne_of_mem_of_not_mem ha h.1
            exact WithBot.coe_le_coe.2 ⟨le_supᵢ₂ s ha, infᵢ₂_le s ha⟩
          · exact bot_le
        le_inf := fun S s ha => by
          cases s
          · exact bot_le
          split_ifs
          ·
            exact
              WithBot.some_le_some.2
                ⟨supᵢ₂_le fun t hb => (WithBot.coe_le_coe.1 <| ha _ hb).1,
                  le_infᵢ₂ fun t hb => (WithBot.coe_le_coe.1 <| ha _ hb).2⟩
          rw [not_and_or, Classical.not_not] at h
          cases h
          · exact ha _ h
          cases
            h fun t hb c hc =>
              (WithBot.coe_le_coe.1 <| ha _ hb).1.trans <|
                s.fst_le_snd.trans (WithBot.coe_le_coe.1 <| ha _ hc).2 }

@[simp, norm_cast]
theorem coe_infₛ [@DecidableRel α (· ≤ ·)] (S : Set (Interval α)) :
    ↑(infₛ S) = ⋂ s ∈ S, (s : Set α) :=
  by
  change coe (dite _ _ _) = _
  split_ifs
  · ext
    simp [WithBot.some_eq_coe, Interval.forall, h.1, ← forall_and, ← NonemptyInterval.mem_def]
  simp_rw [not_and_or, Classical.not_not] at h
  cases h
  · refine' (eq_empty_of_subset_empty _).symm
    exact Inter₂_subset_of_subset _ h subset.rfl
  · refine' (not_nonempty_iff_eq_empty.1 _).symm
    rintro ⟨x, hx⟩
    rw [mem_Inter₂] at hx
    exact h fun s ha t hb => (hx _ ha).1.trans (hx _ hb).2
#align interval.coe_Inf Interval.coe_infₛ

@[simp, norm_cast]
theorem coe_infᵢ [@DecidableRel α (· ≤ ·)] (f : ι → Interval α) :
    ↑(⨅ i, f i) = ⋂ i, (f i : Set α) := by simp [infᵢ]
#align interval.coe_infi Interval.coe_infᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp, norm_cast]
theorem coe_infi₂ [@DecidableRel α (· ≤ ·)] (f : ∀ i, κ i → Interval α) :
    ↑(⨅ (i) (j), f i j) = ⋂ (i) (j), (f i j : Set α) := by simp_rw [coe_infi]
#align interval.coe_infi₂ Interval.coe_infi₂

end CompleteLattice

end Interval

