/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.finset.lattice
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Fold
import Mathbin.Data.Finset.Option
import Mathbin.Data.Finset.Prod
import Mathbin.Data.Multiset.Lattice
import Mathbin.Order.CompleteLattice

/-!
# Lattice operations on finsets
-/


variable {α β γ ι : Type _}

namespace Finset

open Multiset OrderDual

/-! ### sup -/


section Sup

-- TODO: define with just `[has_bot α]` where some lemmas hold without requiring `[order_bot α]`
variable [SemilatticeSup α] [OrderBot α]

/-- Supremum of a finite set: `sup {a, b, c} f = f a ⊔ f b ⊔ f c` -/
def sup (s : Finset β) (f : β → α) : α :=
  s.fold (· ⊔ ·) ⊥ f
#align finset.sup Finset.sup

variable {s s₁ s₂ : Finset β} {f g : β → α} {a : α}

theorem sup_def : s.sup f = (s.1.map f).sup :=
  rfl
#align finset.sup_def Finset.sup_def

@[simp]
theorem sup_empty : (∅ : Finset β).sup f = ⊥ :=
  fold_empty
#align finset.sup_empty Finset.sup_empty

@[simp]
theorem sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b ⊔ s.sup f :=
  fold_cons h
#align finset.sup_cons Finset.sup_cons

@[simp]
theorem sup_insert [DecidableEq β] {b : β} : (insert b s : Finset β).sup f = f b ⊔ s.sup f :=
  fold_insert_idem
#align finset.sup_insert Finset.sup_insert

theorem sup_image [DecidableEq β] (s : Finset γ) (f : γ → β) (g : β → α) :
    (s.image f).sup g = s.sup (g ∘ f) :=
  fold_image_idem
#align finset.sup_image Finset.sup_image

@[simp]
theorem sup_map (s : Finset γ) (f : γ ↪ β) (g : β → α) : (s.map f).sup g = s.sup (g ∘ f) :=
  fold_map
#align finset.sup_map Finset.sup_map

@[simp]
theorem sup_singleton {b : β} : ({b} : Finset β).sup f = f b :=
  sup_singleton
#align finset.sup_singleton Finset.sup_singleton

theorem sup_union [DecidableEq β] : (s₁ ∪ s₂).sup f = s₁.sup f ⊔ s₂.sup f :=
  (Finset.induction_on s₁ (by rw [empty_union, sup_empty, bot_sup_eq])) fun a s has ih => by
    rw [insert_union, sup_insert, sup_insert, ih, sup_assoc]
#align finset.sup_union Finset.sup_union

theorem sup_sup : s.sup (f ⊔ g) = s.sup f ⊔ s.sup g :=
  by
  refine' Finset.cons_induction_on s _ fun b t _ h => _
  · rw [sup_empty, sup_empty, sup_empty, bot_sup_eq]
  · rw [sup_cons, sup_cons, sup_cons, h]
    exact sup_sup_sup_comm _ _ _ _
#align finset.sup_sup Finset.sup_sup

theorem sup_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) : s₁.sup f = s₂.sup g :=
  by subst hs <;> exact Finset.fold_congr hfg
#align finset.sup_congr Finset.sup_congr

@[simp]
protected theorem sup_le_iff {a : α} : s.sup f ≤ a ↔ ∀ b ∈ s, f b ≤ a :=
  by
  apply Iff.trans Multiset.sup_le
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩
#align finset.sup_le_iff Finset.sup_le_iff

alias Finset.sup_le_iff ↔ _ sup_le
#align finset.sup_le Finset.sup_le

attribute [protected] sup_le

theorem sup_const_le : (s.sup fun _ => a) ≤ a :=
  Finset.sup_le fun _ _ => le_rfl
#align finset.sup_const_le Finset.sup_const_le

theorem le_sup {b : β} (hb : b ∈ s) : f b ≤ s.sup f :=
  Finset.sup_le_iff.1 le_rfl _ hb
#align finset.le_sup Finset.le_sup

@[simp]
theorem sup_bUnion [DecidableEq β] (s : Finset γ) (t : γ → Finset β) :
    (s.bUnion t).sup f = s.sup fun x => (t x).sup f :=
  eq_of_forall_ge_iff fun c => by simp [@forall_swap _ β]
#align finset.sup_bUnion Finset.sup_bUnion

theorem sup_const {s : Finset β} (h : s.Nonempty) (c : α) : (s.sup fun _ => c) = c :=
  eq_of_forall_ge_iff fun b => Finset.sup_le_iff.trans h.forall_const
#align finset.sup_const Finset.sup_const

@[simp]
theorem sup_bot (s : Finset β) : (s.sup fun _ => ⊥) = (⊥ : α) :=
  by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact sup_empty
  · exact sup_const hs _
#align finset.sup_bot Finset.sup_bot

theorem sup_ite (p : β → Prop) [DecidablePred p] :
    (s.sup fun i => ite (p i) (f i) (g i)) = (s.filter p).sup f ⊔ (s.filter fun i => ¬p i).sup g :=
  fold_ite _
#align finset.sup_ite Finset.sup_ite

theorem sup_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ≤ g b) : s.sup f ≤ s.sup g :=
  Finset.sup_le fun b hb => le_trans (h b hb) (le_sup hb)
#align finset.sup_mono_fun Finset.sup_mono_fun

theorem sup_mono (h : s₁ ⊆ s₂) : s₁.sup f ≤ s₂.sup f :=
  Finset.sup_le fun b hb => le_sup <| h hb
#align finset.sup_mono Finset.sup_mono

protected theorem sup_comm (s : Finset β) (t : Finset γ) (f : β → γ → α) :
    (s.sup fun b => t.sup (f b)) = t.sup fun c => s.sup fun b => f b c :=
  by
  refine' eq_of_forall_ge_iff fun a => _
  simp_rw [Finset.sup_le_iff]
  exact ⟨fun h c hc b hb => h b hb c hc, fun h b hb c hc => h c hc b hb⟩
#align finset.sup_comm Finset.sup_comm

@[simp]
theorem sup_attach (s : Finset β) (f : β → α) : (s.attach.sup fun x => f x) = s.sup f :=
  (s.attach.sup_map (Function.Embedding.subtype _) f).symm.trans <| congr_arg _ attach_map_val
#align finset.sup_attach Finset.sup_attach

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- See also `finset.product_bUnion`. -/
theorem sup_product_left (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).sup f = s.sup fun i => t.sup fun i' => f ⟨i, i'⟩ :=
  by
  simp only [le_antisymm_iff, Finset.sup_le_iff, mem_product, and_imp, Prod.forall]
  exact
    ⟨fun b c hb hc => (le_sup hb).trans' <| le_sup hc, fun b hb c hc =>
      le_sup <| mem_product.2 ⟨hb, hc⟩⟩
#align finset.sup_product_left Finset.sup_product_left

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem sup_product_right (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).sup f = t.sup fun i' => s.sup fun i => f ⟨i, i'⟩ := by
  rw [sup_product_left, Finset.sup_comm]
#align finset.sup_product_right Finset.sup_product_right

@[simp]
theorem sup_erase_bot [DecidableEq α] (s : Finset α) : (s.erase ⊥).sup id = s.sup id :=
  by
  refine' (sup_mono (s.erase_subset _)).antisymm (Finset.sup_le_iff.2 fun a ha => _)
  obtain rfl | ha' := eq_or_ne a ⊥
  · exact bot_le
  · exact le_sup (mem_erase.2 ⟨ha', ha⟩)
#align finset.sup_erase_bot Finset.sup_erase_bot

theorem sup_sdiff_right {α β : Type _} [GeneralizedBooleanAlgebra α] (s : Finset β) (f : β → α)
    (a : α) : (s.sup fun b => f b \ a) = s.sup f \ a :=
  by
  refine' Finset.cons_induction_on s _ fun b t _ h => _
  · rw [sup_empty, sup_empty, bot_sdiff]
  · rw [sup_cons, sup_cons, h, sup_sdiff]
#align finset.sup_sdiff_right Finset.sup_sdiff_right

theorem comp_sup_eq_sup_comp [SemilatticeSup γ] [OrderBot γ] {s : Finset β} {f : β → α} (g : α → γ)
    (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
  Finset.cons_induction_on s bot fun c t hc ih => by rw [sup_cons, sup_cons, g_sup, ih]
#align finset.comp_sup_eq_sup_comp Finset.comp_sup_eq_sup_comp

/-- Computing `sup` in a subtype (closed under `sup`) is the same as computing it in `α`. -/
theorem sup_coe {P : α → Prop} {Pbot : P ⊥} {Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)} (t : Finset β)
    (f : β → { x : α // P x }) :
    (@sup _ _ (Subtype.semilatticeSup Psup) (Subtype.orderBot Pbot) t f : α) = t.sup fun x => f x :=
  by rw [comp_sup_eq_sup_comp coe] <;> intros <;> rfl
#align finset.sup_coe Finset.sup_coe

@[simp]
theorem sup_to_finset {α β} [DecidableEq β] (s : Finset α) (f : α → Multiset β) :
    (s.sup f).toFinset = s.sup fun x => (f x).toFinset :=
  comp_sup_eq_sup_comp Multiset.toFinset to_finset_union rfl
#align finset.sup_to_finset Finset.sup_to_finset

theorem List.foldr_sup_eq_sup_to_finset [DecidableEq α] (l : List α) :
    l.foldr (· ⊔ ·) ⊥ = l.toFinset.sup id :=
  by
  rw [← coe_fold_r, ← Multiset.fold_dedup_idem, sup_def, ← List.to_finset_coe, to_finset_val,
    Multiset.map_id]
  rfl
#align list.foldr_sup_eq_sup_to_finset List.foldr_sup_eq_sup_to_finset

theorem subset_range_sup_succ (s : Finset ℕ) : s ⊆ range (s.sup id).succ := fun n hn =>
  mem_range.2 <| Nat.lt_succ_of_le <| le_sup hn
#align finset.subset_range_sup_succ Finset.subset_range_sup_succ

theorem exists_nat_subset_range (s : Finset ℕ) : ∃ n : ℕ, s ⊆ range n :=
  ⟨_, s.subset_range_sup_succ⟩
#align finset.exists_nat_subset_range Finset.exists_nat_subset_range

theorem sup_induction {p : α → Prop} (hb : p ⊥) (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊔ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.sup f) :=
  by
  induction' s using Finset.cons_induction with c s hc ih
  · exact hb
  · rw [sup_cons]
    apply hp
    · exact hs c (mem_cons.2 (Or.inl rfl))
    · exact ih fun b h => hs b (mem_cons.2 (Or.inr h))
#align finset.sup_induction Finset.sup_induction

theorem sup_le_of_le_directed {α : Type _} [SemilatticeSup α] [OrderBot α] (s : Set α)
    (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) (t : Finset α) :
    (∀ x ∈ t, ∃ y ∈ s, x ≤ y) → ∃ x, x ∈ s ∧ t.sup id ≤ x := by
  classical
    apply Finset.induction_on t
    ·
      simpa only [forall_prop_of_true, and_true_iff, forall_prop_of_false, bot_le, not_false_iff,
        sup_empty, forall_true_iff, not_mem_empty]
    · intro a r har ih h
      have incs : ↑r ⊆ ↑(insert a r) := by
        rw [Finset.coe_subset]
        apply Finset.subset_insert
      -- x ∈ s is above the sup of r
      obtain ⟨x, ⟨hxs, hsx_sup⟩⟩ := ih fun x hx => h x <| incs hx
      -- y ∈ s is above a
      obtain ⟨y, hys, hay⟩ := h a (Finset.mem_insert_self a r)
      -- z ∈ s is above x and y
      obtain ⟨z, hzs, ⟨hxz, hyz⟩⟩ := hdir x hxs y hys
      use z, hzs
      rw [sup_insert, id.def, sup_le_iff]
      exact ⟨le_trans hay hyz, le_trans hsx_sup hxz⟩
#align finset.sup_le_of_le_directed Finset.sup_le_of_le_directed

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x y «expr ∈ » s) -/
-- If we acquire sublattices
-- the hypotheses should be reformulated as `s : subsemilattice_sup_bot`
theorem sup_mem (s : Set α) (w₁ : ⊥ ∈ s) (w₂ : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), x ⊔ y ∈ s)
    {ι : Type _} (t : Finset ι) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.sup p ∈ s :=
  @sup_induction _ _ _ _ _ _ (· ∈ s) w₁ w₂ h
#align finset.sup_mem Finset.sup_mem

@[simp]
theorem sup_eq_bot_iff (f : β → α) (S : Finset β) : S.sup f = ⊥ ↔ ∀ s ∈ S, f s = ⊥ := by
  classical induction' S using Finset.induction with a S haS hi <;> simp [*]
#align finset.sup_eq_bot_iff Finset.sup_eq_bot_iff

end Sup

theorem sup_eq_supr [CompleteLattice β] (s : Finset α) (f : α → β) : s.sup f = ⨆ a ∈ s, f a :=
  le_antisymm (Finset.sup_le fun a ha => le_supᵢ_of_le a <| le_supᵢ _ ha)
    (supᵢ_le fun a => supᵢ_le fun ha => le_sup ha)
#align finset.sup_eq_supr Finset.sup_eq_supr

theorem sup_id_eq_Sup [CompleteLattice α] (s : Finset α) : s.sup id = supₛ s := by
  simp [supₛ_eq_supᵢ, sup_eq_supᵢ]
#align finset.sup_id_eq_Sup Finset.sup_id_eq_Sup

theorem sup_id_set_eq_sUnion (s : Finset (Set α)) : s.sup id = ⋃₀ ↑s :=
  sup_id_eq_Sup _
#align finset.sup_id_set_eq_sUnion Finset.sup_id_set_eq_sUnion

@[simp]
theorem sup_set_eq_bUnion (s : Finset α) (f : α → Set β) : s.sup f = ⋃ x ∈ s, f x :=
  sup_eq_supr _ _
#align finset.sup_set_eq_bUnion Finset.sup_set_eq_bUnion

theorem sup_eq_Sup_image [CompleteLattice β] (s : Finset α) (f : α → β) : s.sup f = supₛ (f '' s) :=
  by classical rw [← Finset.coe_image, ← sup_id_eq_Sup, sup_image, Function.comp.left_id]
#align finset.sup_eq_Sup_image Finset.sup_eq_Sup_image

/-! ### inf -/


section Inf

-- TODO: define with just `[has_top α]` where some lemmas hold without requiring `[order_top α]`
variable [SemilatticeInf α] [OrderTop α]

/-- Infimum of a finite set: `inf {a, b, c} f = f a ⊓ f b ⊓ f c` -/
def inf (s : Finset β) (f : β → α) : α :=
  s.fold (· ⊓ ·) ⊤ f
#align finset.inf Finset.inf

variable {s s₁ s₂ : Finset β} {f g : β → α} {a : α}

theorem inf_def : s.inf f = (s.1.map f).inf :=
  rfl
#align finset.inf_def Finset.inf_def

@[simp]
theorem inf_empty : (∅ : Finset β).inf f = ⊤ :=
  fold_empty
#align finset.inf_empty Finset.inf_empty

@[simp]
theorem inf_cons {b : β} (h : b ∉ s) : (cons b s h).inf f = f b ⊓ s.inf f :=
  @sup_cons αᵒᵈ _ _ _ _ _ _ h
#align finset.inf_cons Finset.inf_cons

@[simp]
theorem inf_insert [DecidableEq β] {b : β} : (insert b s : Finset β).inf f = f b ⊓ s.inf f :=
  fold_insert_idem
#align finset.inf_insert Finset.inf_insert

theorem inf_image [DecidableEq β] (s : Finset γ) (f : γ → β) (g : β → α) :
    (s.image f).inf g = s.inf (g ∘ f) :=
  fold_image_idem
#align finset.inf_image Finset.inf_image

@[simp]
theorem inf_map (s : Finset γ) (f : γ ↪ β) (g : β → α) : (s.map f).inf g = s.inf (g ∘ f) :=
  fold_map
#align finset.inf_map Finset.inf_map

@[simp]
theorem inf_singleton {b : β} : ({b} : Finset β).inf f = f b :=
  inf_singleton
#align finset.inf_singleton Finset.inf_singleton

theorem inf_union [DecidableEq β] : (s₁ ∪ s₂).inf f = s₁.inf f ⊓ s₂.inf f :=
  @sup_union αᵒᵈ _ _ _ _ _ _ _
#align finset.inf_union Finset.inf_union

theorem inf_inf : s.inf (f ⊓ g) = s.inf f ⊓ s.inf g :=
  @sup_sup αᵒᵈ _ _ _ _ _ _
#align finset.inf_inf Finset.inf_inf

theorem inf_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) : s₁.inf f = s₂.inf g :=
  by subst hs <;> exact Finset.fold_congr hfg
#align finset.inf_congr Finset.inf_congr

@[simp]
theorem inf_bUnion [DecidableEq β] (s : Finset γ) (t : γ → Finset β) :
    (s.bUnion t).inf f = s.inf fun x => (t x).inf f :=
  @sup_bUnion αᵒᵈ _ _ _ _ _ _ _ _
#align finset.inf_bUnion Finset.inf_bUnion

theorem inf_const {s : Finset β} (h : s.Nonempty) (c : α) : (s.inf fun _ => c) = c :=
  @sup_const αᵒᵈ _ _ _ _ h _
#align finset.inf_const Finset.inf_const

@[simp]
theorem inf_top (s : Finset β) : (s.inf fun _ => ⊤) = (⊤ : α) :=
  @sup_bot αᵒᵈ _ _ _ _
#align finset.inf_top Finset.inf_top

protected theorem le_inf_iff {a : α} : a ≤ s.inf f ↔ ∀ b ∈ s, a ≤ f b :=
  @Finset.sup_le_iff αᵒᵈ _ _ _ _ _ _
#align finset.le_inf_iff Finset.le_inf_iff

alias Finset.le_inf_iff ↔ _ le_inf
#align finset.le_inf Finset.le_inf

attribute [protected] le_inf

theorem le_inf_const_le : a ≤ s.inf fun _ => a :=
  Finset.le_inf fun _ _ => le_rfl
#align finset.le_inf_const_le Finset.le_inf_const_le

theorem inf_le {b : β} (hb : b ∈ s) : s.inf f ≤ f b :=
  Finset.le_inf_iff.1 le_rfl _ hb
#align finset.inf_le Finset.inf_le

theorem inf_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ≤ g b) : s.inf f ≤ s.inf g :=
  Finset.le_inf fun b hb => le_trans (inf_le hb) (h b hb)
#align finset.inf_mono_fun Finset.inf_mono_fun

theorem inf_mono (h : s₁ ⊆ s₂) : s₂.inf f ≤ s₁.inf f :=
  Finset.le_inf fun b hb => inf_le <| h hb
#align finset.inf_mono Finset.inf_mono

theorem inf_attach (s : Finset β) (f : β → α) : (s.attach.inf fun x => f x) = s.inf f :=
  @sup_attach αᵒᵈ _ _ _ _ _
#align finset.inf_attach Finset.inf_attach

protected theorem inf_comm (s : Finset β) (t : Finset γ) (f : β → γ → α) :
    (s.inf fun b => t.inf (f b)) = t.inf fun c => s.inf fun b => f b c :=
  @Finset.sup_comm αᵒᵈ _ _ _ _ _ _ _
#align finset.inf_comm Finset.inf_comm

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem inf_product_left (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).inf f = s.inf fun i => t.inf fun i' => f ⟨i, i'⟩ :=
  @sup_product_left αᵒᵈ _ _ _ _ _ _ _
#align finset.inf_product_left Finset.inf_product_left

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem inf_product_right (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).inf f = t.inf fun i' => s.inf fun i => f ⟨i, i'⟩ :=
  @sup_product_right αᵒᵈ _ _ _ _ _ _ _
#align finset.inf_product_right Finset.inf_product_right

@[simp]
theorem inf_erase_top [DecidableEq α] (s : Finset α) : (s.erase ⊤).inf id = s.inf id :=
  @sup_erase_bot αᵒᵈ _ _ _ _
#align finset.inf_erase_top Finset.inf_erase_top

theorem sup_sdiff_left {α β : Type _} [BooleanAlgebra α] (s : Finset β) (f : β → α) (a : α) :
    (s.sup fun b => a \ f b) = a \ s.inf f :=
  by
  refine' Finset.cons_induction_on s _ fun b t _ h => _
  · rw [sup_empty, inf_empty, sdiff_top]
  · rw [sup_cons, inf_cons, h, sdiff_inf]
#align finset.sup_sdiff_left Finset.sup_sdiff_left

theorem inf_sdiff_left {α β : Type _} [BooleanAlgebra α] {s : Finset β} (hs : s.Nonempty)
    (f : β → α) (a : α) : (s.inf fun b => a \ f b) = a \ s.sup f :=
  by
  induction' hs using Finset.Nonempty.cons_induction with b b t _ _ h
  · rw [sup_singleton, inf_singleton]
  · rw [sup_cons, inf_cons, h, sdiff_sup]
#align finset.inf_sdiff_left Finset.inf_sdiff_left

theorem inf_sdiff_right {α β : Type _} [BooleanAlgebra α] {s : Finset β} (hs : s.Nonempty)
    (f : β → α) (a : α) : (s.inf fun b => f b \ a) = s.inf f \ a :=
  by
  induction' hs using Finset.Nonempty.cons_induction with b b t _ _ h
  · rw [inf_singleton, inf_singleton]
  · rw [inf_cons, inf_cons, h, inf_sdiff]
#align finset.inf_sdiff_right Finset.inf_sdiff_right

theorem comp_inf_eq_inf_comp [SemilatticeInf γ] [OrderTop γ] {s : Finset β} {f : β → α} (g : α → γ)
    (g_inf : ∀ x y, g (x ⊓ y) = g x ⊓ g y) (top : g ⊤ = ⊤) : g (s.inf f) = s.inf (g ∘ f) :=
  @comp_sup_eq_sup_comp αᵒᵈ _ γᵒᵈ _ _ _ _ _ _ _ g_inf top
#align finset.comp_inf_eq_inf_comp Finset.comp_inf_eq_inf_comp

/-- Computing `inf` in a subtype (closed under `inf`) is the same as computing it in `α`. -/
theorem inf_coe {P : α → Prop} {Ptop : P ⊤} {Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)} (t : Finset β)
    (f : β → { x : α // P x }) :
    (@inf _ _ (Subtype.semilatticeInf Pinf) (Subtype.orderTop Ptop) t f : α) = t.inf fun x => f x :=
  @sup_coe αᵒᵈ _ _ _ _ Ptop Pinf t f
#align finset.inf_coe Finset.inf_coe

theorem List.foldr_inf_eq_inf_to_finset [DecidableEq α] (l : List α) :
    l.foldr (· ⊓ ·) ⊤ = l.toFinset.inf id :=
  by
  rw [← coe_fold_r, ← Multiset.fold_dedup_idem, inf_def, ← List.to_finset_coe, to_finset_val,
    Multiset.map_id]
  rfl
#align list.foldr_inf_eq_inf_to_finset List.foldr_inf_eq_inf_to_finset

theorem inf_induction {p : α → Prop} (ht : p ⊤) (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊓ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.inf f) :=
  @sup_induction αᵒᵈ _ _ _ _ _ _ ht hp hs
#align finset.inf_induction Finset.inf_induction

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem inf_mem (s : Set α) (w₁ : ⊤ ∈ s) (w₂ : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), x ⊓ y ∈ s)
    {ι : Type _} (t : Finset ι) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.inf p ∈ s :=
  @inf_induction _ _ _ _ _ _ (· ∈ s) w₁ w₂ h
#align finset.inf_mem Finset.inf_mem

@[simp]
theorem inf_eq_top_iff (f : β → α) (S : Finset β) : S.inf f = ⊤ ↔ ∀ s ∈ S, f s = ⊤ :=
  @Finset.sup_eq_bot_iff αᵒᵈ _ _ _ _ _
#align finset.inf_eq_top_iff Finset.inf_eq_top_iff

end Inf

@[simp]
theorem to_dual_sup [SemilatticeSup α] [OrderBot α] (s : Finset β) (f : β → α) :
    toDual (s.sup f) = s.inf (to_dual ∘ f) :=
  rfl
#align finset.to_dual_sup Finset.to_dual_sup

@[simp]
theorem to_dual_inf [SemilatticeInf α] [OrderTop α] (s : Finset β) (f : β → α) :
    toDual (s.inf f) = s.sup (to_dual ∘ f) :=
  rfl
#align finset.to_dual_inf Finset.to_dual_inf

@[simp]
theorem of_dual_sup [SemilatticeInf α] [OrderTop α] (s : Finset β) (f : β → αᵒᵈ) :
    ofDual (s.sup f) = s.inf (of_dual ∘ f) :=
  rfl
#align finset.of_dual_sup Finset.of_dual_sup

@[simp]
theorem of_dual_inf [SemilatticeSup α] [OrderBot α] (s : Finset β) (f : β → αᵒᵈ) :
    ofDual (s.inf f) = s.sup (of_dual ∘ f) :=
  rfl
#align finset.of_dual_inf Finset.of_dual_inf

section DistribLattice

variable [DistribLattice α]

section OrderBot

variable [OrderBot α] {s : Finset β} {f : β → α} {a : α}

theorem sup_inf_distrib_left (s : Finset ι) (f : ι → α) (a : α) :
    a ⊓ s.sup f = s.sup fun i => a ⊓ f i :=
  by
  induction' s using Finset.cons_induction with i s hi h
  · simp_rw [Finset.sup_empty, inf_bot_eq]
  · rw [sup_cons, sup_cons, inf_sup_left, h]
#align finset.sup_inf_distrib_left Finset.sup_inf_distrib_left

theorem sup_inf_distrib_right (s : Finset ι) (f : ι → α) (a : α) :
    s.sup f ⊓ a = s.sup fun i => f i ⊓ a :=
  by
  rw [_root_.inf_comm, s.sup_inf_distrib_left]
  simp_rw [_root_.inf_comm]
#align finset.sup_inf_distrib_right Finset.sup_inf_distrib_right

theorem disjoint_sup_right : Disjoint a (s.sup f) ↔ ∀ i ∈ s, Disjoint a (f i) := by
  simp only [disjoint_iff, sup_inf_distrib_left, sup_eq_bot_iff]
#align finset.disjoint_sup_right Finset.disjoint_sup_right

theorem disjoint_sup_left : Disjoint (s.sup f) a ↔ ∀ i ∈ s, Disjoint (f i) a := by
  simp only [disjoint_iff, sup_inf_distrib_right, sup_eq_bot_iff]
#align finset.disjoint_sup_left Finset.disjoint_sup_left

end OrderBot

section OrderTop

variable [OrderTop α]

theorem inf_sup_distrib_left (s : Finset ι) (f : ι → α) (a : α) :
    a ⊔ s.inf f = s.inf fun i => a ⊔ f i :=
  @sup_inf_distrib_left αᵒᵈ _ _ _ _ _ _
#align finset.inf_sup_distrib_left Finset.inf_sup_distrib_left

theorem inf_sup_distrib_right (s : Finset ι) (f : ι → α) (a : α) :
    s.inf f ⊔ a = s.inf fun i => f i ⊔ a :=
  @sup_inf_distrib_right αᵒᵈ _ _ _ _ _ _
#align finset.inf_sup_distrib_right Finset.inf_sup_distrib_right

end OrderTop

end DistribLattice

section LinearOrder

variable [LinearOrder α]

section OrderBot

variable [OrderBot α] {s : Finset ι} {f : ι → α} {a : α}

theorem comp_sup_eq_sup_comp_of_is_total [SemilatticeSup β] [OrderBot β] (g : α → β)
    (mono_g : Monotone g) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
  comp_sup_eq_sup_comp g mono_g.map_sup bot
#align finset.comp_sup_eq_sup_comp_of_is_total Finset.comp_sup_eq_sup_comp_of_is_total

@[simp]
protected theorem le_sup_iff (ha : ⊥ < a) : a ≤ s.sup f ↔ ∃ b ∈ s, a ≤ f b :=
  ⟨Finset.cons_induction_on s (fun h => absurd h (not_le_of_lt ha)) fun c t hc ih => by
      simpa using
        @Or.ndrec _ _ (∃ b, (b = c ∨ b ∈ t) ∧ a ≤ f b) (fun h => ⟨c, Or.inl rfl, h⟩) fun h =>
          let ⟨b, hb, hle⟩ := ih h
          ⟨b, Or.inr hb, hle⟩,
    fun ⟨b, hb, hle⟩ => trans hle (le_sup hb)⟩
#align finset.le_sup_iff Finset.le_sup_iff

@[simp]
protected theorem lt_sup_iff : a < s.sup f ↔ ∃ b ∈ s, a < f b :=
  ⟨Finset.cons_induction_on s (fun h => absurd h not_lt_bot) fun c t hc ih => by
      simpa using
        @Or.ndrec _ _ (∃ b, (b = c ∨ b ∈ t) ∧ a < f b) (fun h => ⟨c, Or.inl rfl, h⟩) fun h =>
          let ⟨b, hb, hlt⟩ := ih h
          ⟨b, Or.inr hb, hlt⟩,
    fun ⟨b, hb, hlt⟩ => lt_of_lt_of_le hlt (le_sup hb)⟩
#align finset.lt_sup_iff Finset.lt_sup_iff

@[simp]
protected theorem sup_lt_iff (ha : ⊥ < a) : s.sup f < a ↔ ∀ b ∈ s, f b < a :=
  ⟨fun hs b hb => lt_of_le_of_lt (le_sup hb) hs,
    Finset.cons_induction_on s (fun _ => ha) fun c t hc => by
      simpa only [sup_cons, sup_lt_iff, mem_cons, forall_eq_or_imp] using And.imp_right⟩
#align finset.sup_lt_iff Finset.sup_lt_iff

end OrderBot

section OrderTop

variable [OrderTop α] {s : Finset ι} {f : ι → α} {a : α}

theorem comp_inf_eq_inf_comp_of_is_total [SemilatticeInf β] [OrderTop β] (g : α → β)
    (mono_g : Monotone g) (top : g ⊤ = ⊤) : g (s.inf f) = s.inf (g ∘ f) :=
  comp_inf_eq_inf_comp g mono_g.map_inf top
#align finset.comp_inf_eq_inf_comp_of_is_total Finset.comp_inf_eq_inf_comp_of_is_total

@[simp]
protected theorem inf_le_iff (ha : a < ⊤) : s.inf f ≤ a ↔ ∃ b ∈ s, f b ≤ a :=
  @Finset.le_sup_iff αᵒᵈ _ _ _ _ _ _ ha
#align finset.inf_le_iff Finset.inf_le_iff

@[simp]
protected theorem inf_lt_iff : s.inf f < a ↔ ∃ b ∈ s, f b < a :=
  @Finset.lt_sup_iff αᵒᵈ _ _ _ _ _ _
#align finset.inf_lt_iff Finset.inf_lt_iff

@[simp]
protected theorem lt_inf_iff (ha : a < ⊤) : a < s.inf f ↔ ∀ b ∈ s, a < f b :=
  @Finset.sup_lt_iff αᵒᵈ _ _ _ _ _ _ ha
#align finset.lt_inf_iff Finset.lt_inf_iff

end OrderTop

end LinearOrder

theorem inf_eq_infi [CompleteLattice β] (s : Finset α) (f : α → β) : s.inf f = ⨅ a ∈ s, f a :=
  @sup_eq_supr _ βᵒᵈ _ _ _
#align finset.inf_eq_infi Finset.inf_eq_infi

theorem inf_id_eq_Inf [CompleteLattice α] (s : Finset α) : s.inf id = infₛ s :=
  @sup_id_eq_Sup αᵒᵈ _ _
#align finset.inf_id_eq_Inf Finset.inf_id_eq_Inf

theorem inf_id_set_eq_sInter (s : Finset (Set α)) : s.inf id = ⋂₀ ↑s :=
  inf_id_eq_Inf _
#align finset.inf_id_set_eq_sInter Finset.inf_id_set_eq_sInter

@[simp]
theorem inf_set_eq_bInter (s : Finset α) (f : α → Set β) : s.inf f = ⋂ x ∈ s, f x :=
  inf_eq_infi _ _
#align finset.inf_set_eq_bInter Finset.inf_set_eq_bInter

theorem inf_eq_Inf_image [CompleteLattice β] (s : Finset α) (f : α → β) : s.inf f = infₛ (f '' s) :=
  @sup_eq_Sup_image _ βᵒᵈ _ _ _
#align finset.inf_eq_Inf_image Finset.inf_eq_Inf_image

section Sup'

variable [SemilatticeSup α]

theorem sup_of_mem {s : Finset β} (f : β → α) {b : β} (h : b ∈ s) :
    ∃ a : α, s.sup (coe ∘ f : β → WithBot α) = ↑a :=
  Exists.imp (fun a => Exists.fst) (@le_sup (WithBot α) _ _ _ _ _ _ h (f b) rfl)
#align finset.sup_of_mem Finset.sup_of_mem

/-- Given nonempty finset `s` then `s.sup' H f` is the supremum of its image under `f` in (possibly
unbounded) join-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a bottom element
you may instead use `finset.sup` which does not require `s` nonempty. -/
def sup' (s : Finset β) (H : s.Nonempty) (f : β → α) : α :=
  WithBot.unbot (s.sup (coe ∘ f)) (by simpa using H)
#align finset.sup' Finset.sup'

variable {s : Finset β} (H : s.Nonempty) (f : β → α)

@[simp]
theorem coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup (coe ∘ f) := by
  rw [sup', WithBot.coe_unbot]
#align finset.coe_sup' Finset.coe_sup'

@[simp]
theorem sup'_cons {b : β} {hb : b ∉ s} {h : (cons b s hb).Nonempty} :
    (cons b s hb).sup' h f = f b ⊔ s.sup' H f :=
  by
  rw [← WithBot.coe_eq_coe]
  simp only [coe_sup', sup_cons, WithBot.coe_sup]
#align finset.sup'_cons Finset.sup'_cons

@[simp]
theorem sup'_insert [DecidableEq β] {b : β} {h : (insert b s).Nonempty} :
    (insert b s).sup' h f = f b ⊔ s.sup' H f :=
  by
  rw [← WithBot.coe_eq_coe]
  simp only [coe_sup', sup_insert, WithBot.coe_sup]
#align finset.sup'_insert Finset.sup'_insert

@[simp]
theorem sup'_singleton {b : β} {h : ({b} : Finset β).Nonempty} : ({b} : Finset β).sup' h f = f b :=
  rfl
#align finset.sup'_singleton Finset.sup'_singleton

theorem sup'_le {a : α} (hs : ∀ b ∈ s, f b ≤ a) : s.sup' H f ≤ a :=
  by
  rw [← WithBot.coe_le_coe, coe_sup']
  exact Finset.sup_le fun b h => WithBot.coe_le_coe.2 <| hs b h
#align finset.sup'_le Finset.sup'_le

theorem le_sup' {b : β} (h : b ∈ s) : f b ≤ s.sup' ⟨b, h⟩ f :=
  by
  rw [← WithBot.coe_le_coe, coe_sup']
  exact le_sup h
#align finset.le_sup' Finset.le_sup'

@[simp]
theorem sup'_const (a : α) : (s.sup' H fun b => a) = a :=
  by
  apply le_antisymm
  · apply sup'_le
    intros
    exact le_rfl
  · apply le_sup' (fun b => a) H.some_spec
#align finset.sup'_const Finset.sup'_const

@[simp]
theorem sup'_le_iff {a : α} : s.sup' H f ≤ a ↔ ∀ b ∈ s, f b ≤ a :=
  Iff.intro (fun h b hb => trans (le_sup' f hb) h) (sup'_le H f)
#align finset.sup'_le_iff Finset.sup'_le_iff

theorem sup'_bUnion [DecidableEq β] {s : Finset γ} (Hs : s.Nonempty) {t : γ → Finset β}
    (Ht : ∀ b, (t b).Nonempty) :
    (s.bUnion t).sup' (Hs.bUnion fun b _ => Ht b) f = s.sup' Hs fun b => (t b).sup' (Ht b) f :=
  eq_of_forall_ge_iff fun c => by simp [@forall_swap _ β]
#align finset.sup'_bUnion Finset.sup'_bUnion

theorem comp_sup'_eq_sup'_comp [SemilatticeSup γ] {s : Finset β} (H : s.Nonempty) {f : β → α}
    (g : α → γ) (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) : g (s.sup' H f) = s.sup' H (g ∘ f) :=
  by
  rw [← WithBot.coe_eq_coe, coe_sup']
  let g' := WithBot.map g
  show g' ↑(s.sup' H f) = s.sup fun a => g' ↑(f a)
  rw [coe_sup']
  refine' comp_sup_eq_sup_comp g' _ rfl
  intro f₁ f₂
  induction f₁ using WithBot.recBotCoe
  · rw [bot_sup_eq]
    exact bot_sup_eq.symm
  · induction f₂ using WithBot.recBotCoe
    · rfl
    · exact congr_arg coe (g_sup f₁ f₂)
#align finset.comp_sup'_eq_sup'_comp Finset.comp_sup'_eq_sup'_comp

theorem sup'_induction {p : α → Prop} (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊔ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.sup' H f) :=
  by
  show @WithBot.recBotCoe α (fun _ => Prop) True p ↑(s.sup' H f)
  rw [coe_sup']
  refine' sup_induction trivial _ hs
  rintro (_ | a₁) h₁ a₂ h₂
  · rw [WithBot.none_eq_bot, bot_sup_eq]
    exact h₂
  cases a₂
  exacts[h₁, hp a₁ h₁ a₂ h₂]
#align finset.sup'_induction Finset.sup'_induction

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem sup'_mem (s : Set α) (w : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), x ⊔ y ∈ s) {ι : Type _}
    (t : Finset ι) (H : t.Nonempty) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.sup' H p ∈ s :=
  sup'_induction H p w h
#align finset.sup'_mem Finset.sup'_mem

@[congr]
theorem sup'_congr {t : Finset β} {f g : β → α} (h₁ : s = t) (h₂ : ∀ x ∈ s, f x = g x) :
    s.sup' H f = t.sup' (h₁ ▸ H) g := by
  subst s
  refine' eq_of_forall_ge_iff fun c => _
  simp (config := { contextual := true }) only [sup'_le_iff, h₂]
#align finset.sup'_congr Finset.sup'_congr

@[simp]
theorem sup'_map {s : Finset γ} {f : γ ↪ β} (g : β → α) (hs : (s.map f).Nonempty)
    (hs' : s.Nonempty := Finset.map_nonempty.mp hs) : (s.map f).sup' hs g = s.sup' hs' (g ∘ f) := by
  rw [← WithBot.coe_eq_coe, coe_sup', sup_map, coe_sup']
#align finset.sup'_map Finset.sup'_map

end Sup'

section Inf'

variable [SemilatticeInf α]

theorem inf_of_mem {s : Finset β} (f : β → α) {b : β} (h : b ∈ s) :
    ∃ a : α, s.inf (coe ∘ f : β → WithTop α) = ↑a :=
  @sup_of_mem αᵒᵈ _ _ _ f _ h
#align finset.inf_of_mem Finset.inf_of_mem

/-- Given nonempty finset `s` then `s.inf' H f` is the infimum of its image under `f` in (possibly
unbounded) meet-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a top element you
may instead use `finset.inf` which does not require `s` nonempty. -/
def inf' (s : Finset β) (H : s.Nonempty) (f : β → α) : α :=
  WithTop.untop (s.inf (coe ∘ f)) (by simpa using H)
#align finset.inf' Finset.inf'

variable {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α} {b : β}

@[simp]
theorem coe_inf' : ((s.inf' H f : α) : WithTop α) = s.inf (coe ∘ f) :=
  @coe_sup' αᵒᵈ _ _ _ H f
#align finset.coe_inf' Finset.coe_inf'

@[simp]
theorem inf'_cons {b : β} {hb : b ∉ s} {h : (cons b s hb).Nonempty} :
    (cons b s hb).inf' h f = f b ⊓ s.inf' H f :=
  @sup'_cons αᵒᵈ _ _ _ H f _ _ h
#align finset.inf'_cons Finset.inf'_cons

@[simp]
theorem inf'_insert [DecidableEq β] {b : β} {h : (insert b s).Nonempty} :
    (insert b s).inf' h f = f b ⊓ s.inf' H f :=
  @sup'_insert αᵒᵈ _ _ _ H f _ _ h
#align finset.inf'_insert Finset.inf'_insert

@[simp]
theorem inf'_singleton {b : β} {h : ({b} : Finset β).Nonempty} : ({b} : Finset β).inf' h f = f b :=
  rfl
#align finset.inf'_singleton Finset.inf'_singleton

theorem le_inf' (hs : ∀ b ∈ s, a ≤ f b) : a ≤ s.inf' H f :=
  @sup'_le αᵒᵈ _ _ _ H f _ hs
#align finset.le_inf' Finset.le_inf'

theorem inf'_le (h : b ∈ s) : s.inf' ⟨b, h⟩ f ≤ f b :=
  @le_sup' αᵒᵈ _ _ _ f _ h
#align finset.inf'_le Finset.inf'_le

@[simp]
theorem inf'_const (a : α) : (s.inf' H fun b => a) = a :=
  @sup'_const αᵒᵈ _ _ _ H _
#align finset.inf'_const Finset.inf'_const

@[simp]
theorem le_inf'_iff : a ≤ s.inf' H f ↔ ∀ b ∈ s, a ≤ f b :=
  @sup'_le_iff αᵒᵈ _ _ _ H f _
#align finset.le_inf'_iff Finset.le_inf'_iff

theorem inf'_bUnion [DecidableEq β] {s : Finset γ} (Hs : s.Nonempty) {t : γ → Finset β}
    (Ht : ∀ b, (t b).Nonempty) :
    (s.bUnion t).inf' (Hs.bUnion fun b _ => Ht b) f = s.inf' Hs fun b => (t b).inf' (Ht b) f :=
  @sup'_bUnion αᵒᵈ _ _ _ _ _ _ Hs _ Ht
#align finset.inf'_bUnion Finset.inf'_bUnion

theorem comp_inf'_eq_inf'_comp [SemilatticeInf γ] {s : Finset β} (H : s.Nonempty) {f : β → α}
    (g : α → γ) (g_inf : ∀ x y, g (x ⊓ y) = g x ⊓ g y) : g (s.inf' H f) = s.inf' H (g ∘ f) :=
  @comp_sup'_eq_sup'_comp αᵒᵈ _ γᵒᵈ _ _ _ H f g g_inf
#align finset.comp_inf'_eq_inf'_comp Finset.comp_inf'_eq_inf'_comp

theorem inf'_induction {p : α → Prop} (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊓ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.inf' H f) :=
  @sup'_induction αᵒᵈ _ _ _ H f _ hp hs
#align finset.inf'_induction Finset.inf'_induction

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem inf'_mem (s : Set α) (w : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), x ⊓ y ∈ s) {ι : Type _}
    (t : Finset ι) (H : t.Nonempty) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.inf' H p ∈ s :=
  inf'_induction H p w h
#align finset.inf'_mem Finset.inf'_mem

@[congr]
theorem inf'_congr {t : Finset β} {f g : β → α} (h₁ : s = t) (h₂ : ∀ x ∈ s, f x = g x) :
    s.inf' H f = t.inf' (h₁ ▸ H) g :=
  @sup'_congr αᵒᵈ _ _ _ H _ _ _ h₁ h₂
#align finset.inf'_congr Finset.inf'_congr

@[simp]
theorem inf'_map {s : Finset γ} {f : γ ↪ β} (g : β → α) (hs : (s.map f).Nonempty)
    (hs' : s.Nonempty := Finset.map_nonempty.mp hs) : (s.map f).inf' hs g = s.inf' hs' (g ∘ f) :=
  @sup'_map αᵒᵈ _ _ _ _ _ _ hs hs'
#align finset.inf'_map Finset.inf'_map

end Inf'

section Sup

variable [SemilatticeSup α] [OrderBot α]

theorem sup'_eq_sup {s : Finset β} (H : s.Nonempty) (f : β → α) : s.sup' H f = s.sup f :=
  le_antisymm (sup'_le H f fun b => le_sup) (Finset.sup_le fun b => le_sup' f)
#align finset.sup'_eq_sup Finset.sup'_eq_sup

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (a b «expr ∈ » s) -/
theorem sup_closed_of_sup_closed {s : Set α} (t : Finset α) (htne : t.Nonempty) (h_subset : ↑t ⊆ s)
    (h : ∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s), a ⊔ b ∈ s) : t.sup id ∈ s :=
  sup'_eq_sup htne id ▸ sup'_induction _ _ h h_subset
#align finset.sup_closed_of_sup_closed Finset.sup_closed_of_sup_closed

theorem coe_sup_of_nonempty {s : Finset β} (h : s.Nonempty) (f : β → α) :
    (↑(s.sup f) : WithBot α) = s.sup (coe ∘ f) := by simp only [← sup'_eq_sup h, coe_sup' h]
#align finset.coe_sup_of_nonempty Finset.coe_sup_of_nonempty

end Sup

section Inf

variable [SemilatticeInf α] [OrderTop α]

theorem inf'_eq_inf {s : Finset β} (H : s.Nonempty) (f : β → α) : s.inf' H f = s.inf f :=
  @sup'_eq_sup αᵒᵈ _ _ _ _ H f
#align finset.inf'_eq_inf Finset.inf'_eq_inf

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (a b «expr ∈ » s) -/
theorem inf_closed_of_inf_closed {s : Set α} (t : Finset α) (htne : t.Nonempty) (h_subset : ↑t ⊆ s)
    (h : ∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s), a ⊓ b ∈ s) : t.inf id ∈ s :=
  @sup_closed_of_sup_closed αᵒᵈ _ _ _ t htne h_subset h
#align finset.inf_closed_of_inf_closed Finset.inf_closed_of_inf_closed

theorem coe_inf_of_nonempty {s : Finset β} (h : s.Nonempty) (f : β → α) :
    (↑(s.inf f) : WithTop α) = s.inf fun i => f i :=
  @coe_sup_of_nonempty αᵒᵈ _ _ _ _ h f
#align finset.coe_inf_of_nonempty Finset.coe_inf_of_nonempty

end Inf

section Sup

variable {C : β → Type _} [∀ b : β, SemilatticeSup (C b)] [∀ b : β, OrderBot (C b)]

@[simp]
protected theorem sup_apply (s : Finset α) (f : α → ∀ b : β, C b) (b : β) :
    s.sup f b = s.sup fun a => f a b :=
  comp_sup_eq_sup_comp (fun x : ∀ b : β, C b => x b) (fun i j => rfl) rfl
#align finset.sup_apply Finset.sup_apply

end Sup

section Inf

variable {C : β → Type _} [∀ b : β, SemilatticeInf (C b)] [∀ b : β, OrderTop (C b)]

@[simp]
protected theorem inf_apply (s : Finset α) (f : α → ∀ b : β, C b) (b : β) :
    s.inf f b = s.inf fun a => f a b :=
  @Finset.sup_apply _ _ (fun b => (C b)ᵒᵈ) _ _ s f b
#align finset.inf_apply Finset.inf_apply

end Inf

section Sup'

variable {C : β → Type _} [∀ b : β, SemilatticeSup (C b)]

@[simp]
protected theorem sup'_apply {s : Finset α} (H : s.Nonempty) (f : α → ∀ b : β, C b) (b : β) :
    s.sup' H f b = s.sup' H fun a => f a b :=
  comp_sup'_eq_sup'_comp H (fun x : ∀ b : β, C b => x b) fun i j => rfl
#align finset.sup'_apply Finset.sup'_apply

end Sup'

section Inf'

variable {C : β → Type _} [∀ b : β, SemilatticeInf (C b)]

@[simp]
protected theorem inf'_apply {s : Finset α} (H : s.Nonempty) (f : α → ∀ b : β, C b) (b : β) :
    s.inf' H f b = s.inf' H fun a => f a b :=
  @Finset.sup'_apply _ _ (fun b => (C b)ᵒᵈ) _ _ H f b
#align finset.inf'_apply Finset.inf'_apply

end Inf'

@[simp]
theorem to_dual_sup' [SemilatticeSup α] {s : Finset ι} (hs : s.Nonempty) (f : ι → α) :
    toDual (s.sup' hs f) = s.inf' hs (to_dual ∘ f) :=
  rfl
#align finset.to_dual_sup' Finset.to_dual_sup'

@[simp]
theorem to_dual_inf' [SemilatticeInf α] {s : Finset ι} (hs : s.Nonempty) (f : ι → α) :
    toDual (s.inf' hs f) = s.sup' hs (to_dual ∘ f) :=
  rfl
#align finset.to_dual_inf' Finset.to_dual_inf'

@[simp]
theorem of_dual_sup' [SemilatticeInf α] {s : Finset ι} (hs : s.Nonempty) (f : ι → αᵒᵈ) :
    ofDual (s.sup' hs f) = s.inf' hs (of_dual ∘ f) :=
  rfl
#align finset.of_dual_sup' Finset.of_dual_sup'

@[simp]
theorem of_dual_inf' [SemilatticeSup α] {s : Finset ι} (hs : s.Nonempty) (f : ι → αᵒᵈ) :
    ofDual (s.inf' hs f) = s.sup' hs (of_dual ∘ f) :=
  rfl
#align finset.of_dual_inf' Finset.of_dual_inf'

section LinearOrder

variable [LinearOrder α] {s : Finset ι} (H : s.Nonempty) {f : ι → α} {a : α}

@[simp]
theorem le_sup'_iff : a ≤ s.sup' H f ↔ ∃ b ∈ s, a ≤ f b :=
  by
  rw [← WithBot.coe_le_coe, coe_sup', Finset.le_sup_iff (WithBot.bot_lt_coe a)]
  exact bex_congr fun b hb => WithBot.coe_le_coe
#align finset.le_sup'_iff Finset.le_sup'_iff

@[simp]
theorem lt_sup'_iff : a < s.sup' H f ↔ ∃ b ∈ s, a < f b :=
  by
  rw [← WithBot.coe_lt_coe, coe_sup', Finset.lt_sup_iff]
  exact bex_congr fun b hb => WithBot.coe_lt_coe
#align finset.lt_sup'_iff Finset.lt_sup'_iff

@[simp]
theorem sup'_lt_iff : s.sup' H f < a ↔ ∀ i ∈ s, f i < a :=
  by
  rw [← WithBot.coe_lt_coe, coe_sup', Finset.sup_lt_iff (WithBot.bot_lt_coe a)]
  exact ball_congr fun b hb => WithBot.coe_lt_coe
#align finset.sup'_lt_iff Finset.sup'_lt_iff

@[simp]
theorem inf'_le_iff : s.inf' H f ≤ a ↔ ∃ i ∈ s, f i ≤ a :=
  @le_sup'_iff αᵒᵈ _ _ _ H f _
#align finset.inf'_le_iff Finset.inf'_le_iff

@[simp]
theorem inf'_lt_iff : s.inf' H f < a ↔ ∃ i ∈ s, f i < a :=
  @lt_sup'_iff αᵒᵈ _ _ _ H f _
#align finset.inf'_lt_iff Finset.inf'_lt_iff

@[simp]
theorem lt_inf'_iff : a < s.inf' H f ↔ ∀ i ∈ s, a < f i :=
  @sup'_lt_iff αᵒᵈ _ _ _ H f _
#align finset.lt_inf'_iff Finset.lt_inf'_iff

theorem exists_mem_eq_sup' (f : ι → α) : ∃ i, i ∈ s ∧ s.sup' H f = f i :=
  by
  refine' H.cons_induction (fun c => _) fun c s hc hs ih => _
  · exact ⟨c, mem_singleton_self c, rfl⟩
  · rcases ih with ⟨b, hb, h'⟩
    rw [sup'_cons hs, h']
    cases' total_of (· ≤ ·) (f b) (f c) with h h
    · exact ⟨c, mem_cons.2 (Or.inl rfl), sup_eq_left.2 h⟩
    · exact ⟨b, mem_cons.2 (Or.inr hb), sup_eq_right.2 h⟩
#align finset.exists_mem_eq_sup' Finset.exists_mem_eq_sup'

theorem exists_mem_eq_inf' (f : ι → α) : ∃ i, i ∈ s ∧ s.inf' H f = f i :=
  @exists_mem_eq_sup' αᵒᵈ _ _ _ H f
#align finset.exists_mem_eq_inf' Finset.exists_mem_eq_inf'

theorem exists_mem_eq_sup [OrderBot α] (s : Finset ι) (h : s.Nonempty) (f : ι → α) :
    ∃ i, i ∈ s ∧ s.sup f = f i :=
  sup'_eq_sup h f ▸ exists_mem_eq_sup' h f
#align finset.exists_mem_eq_sup Finset.exists_mem_eq_sup

theorem exists_mem_eq_inf [OrderTop α] (s : Finset ι) (h : s.Nonempty) (f : ι → α) :
    ∃ i, i ∈ s ∧ s.inf f = f i :=
  @exists_mem_eq_sup αᵒᵈ _ _ _ _ h f
#align finset.exists_mem_eq_inf Finset.exists_mem_eq_inf

end LinearOrder

/-! ### max and min of finite sets -/


section MaxMin

variable [LinearOrder α]

/-- Let `s` be a finset in a linear order. Then `s.max` is the maximum of `s` if `s` is not empty,
and `⊥` otherwise. It belongs to `with_bot α`. If you want to get an element of `α`, see
`s.max'`. -/
protected def max (s : Finset α) : WithBot α :=
  sup s coe
#align finset.max Finset.max

theorem max_eq_sup_coe {s : Finset α} : s.max = s.sup coe :=
  rfl
#align finset.max_eq_sup_coe Finset.max_eq_sup_coe

theorem max_eq_sup_with_bot (s : Finset α) : s.max = sup s coe :=
  rfl
#align finset.max_eq_sup_with_bot Finset.max_eq_sup_with_bot

@[simp]
theorem max_empty : (∅ : Finset α).max = ⊥ :=
  rfl
#align finset.max_empty Finset.max_empty

@[simp]
theorem max_insert {a : α} {s : Finset α} : (insert a s).max = max a s.max :=
  fold_insert_idem
#align finset.max_insert Finset.max_insert

@[simp]
theorem max_singleton {a : α} : Finset.max {a} = (a : WithBot α) :=
  by
  rw [← insert_emptyc_eq]
  exact max_insert
#align finset.max_singleton Finset.max_singleton

theorem max_of_mem {s : Finset α} {a : α} (h : a ∈ s) : ∃ b : α, s.max = b :=
  (@le_sup (WithBot α) _ _ _ _ _ _ h _ rfl).imp fun b => Exists.fst
#align finset.max_of_mem Finset.max_of_mem

theorem max_of_nonempty {s : Finset α} (h : s.Nonempty) : ∃ a : α, s.max = a :=
  let ⟨a, ha⟩ := h
  max_of_mem ha
#align finset.max_of_nonempty Finset.max_of_nonempty

theorem max_eq_bot {s : Finset α} : s.max = ⊥ ↔ s = ∅ :=
  ⟨fun h =>
    s.eq_empty_or_nonempty.elim id fun H =>
      by
      let ⟨a, ha⟩ := max_of_nonempty H
      rw [h] at ha <;> cases ha,
    fun h => h.symm ▸ max_empty⟩
#align finset.max_eq_bot Finset.max_eq_bot

theorem mem_of_max {s : Finset α} : ∀ {a : α}, s.max = a → a ∈ s :=
  Finset.induction_on s (fun _ H => by cases H)
    fun b s _ (ih : ∀ {a : α}, s.max = a → a ∈ s) a (h : (insert b s).max = a) =>
    by
    by_cases p : b = a
    · induction p
      exact mem_insert_self b s
    · cases' max_choice (↑b) s.max with q q <;> rw [max_insert, q] at h
      · cases h
        cases p rfl
      · exact mem_insert_of_mem (ih h)
#align finset.mem_of_max Finset.mem_of_max

theorem le_max {a : α} {s : Finset α} (as : a ∈ s) : ↑a ≤ s.max :=
  le_sup as
#align finset.le_max Finset.le_max

theorem not_mem_of_max_lt_coe {a : α} {s : Finset α} (h : s.max < a) : a ∉ s :=
  mt le_max h.not_le
#align finset.not_mem_of_max_lt_coe Finset.not_mem_of_max_lt_coe

theorem le_max_of_eq {s : Finset α} {a b : α} (h₁ : a ∈ s) (h₂ : s.max = b) : a ≤ b :=
  WithBot.coe_le_coe.mp <| (le_max h₁).trans h₂.le
#align finset.le_max_of_eq Finset.le_max_of_eq

theorem not_mem_of_max_lt {s : Finset α} {a b : α} (h₁ : b < a) (h₂ : s.max = ↑b) : a ∉ s :=
  Finset.not_mem_of_max_lt_coe <| h₂.trans_lt <| WithBot.coe_lt_coe.mpr h₁
#align finset.not_mem_of_max_lt Finset.not_mem_of_max_lt

theorem max_mono {s t : Finset α} (st : s ⊆ t) : s.max ≤ t.max :=
  sup_mono st
#align finset.max_mono Finset.max_mono

protected theorem max_le {M : WithBot α} {s : Finset α} (st : ∀ a ∈ s, (a : WithBot α) ≤ M) :
    s.max ≤ M :=
  Finset.sup_le st
#align finset.max_le Finset.max_le

/-- Let `s` be a finset in a linear order. Then `s.min` is the minimum of `s` if `s` is not empty,
and `⊤` otherwise. It belongs to `with_top α`. If you want to get an element of `α`, see
`s.min'`. -/
protected def min (s : Finset α) : WithTop α :=
  inf s coe
#align finset.min Finset.min

theorem min_eq_inf_with_top (s : Finset α) : s.min = inf s coe :=
  rfl
#align finset.min_eq_inf_with_top Finset.min_eq_inf_with_top

@[simp]
theorem min_empty : (∅ : Finset α).min = ⊤ :=
  rfl
#align finset.min_empty Finset.min_empty

@[simp]
theorem min_insert {a : α} {s : Finset α} : (insert a s).min = min (↑a) s.min :=
  fold_insert_idem
#align finset.min_insert Finset.min_insert

@[simp]
theorem min_singleton {a : α} : Finset.min {a} = (a : WithTop α) :=
  by
  rw [← insert_emptyc_eq]
  exact min_insert
#align finset.min_singleton Finset.min_singleton

theorem min_of_mem {s : Finset α} {a : α} (h : a ∈ s) : ∃ b : α, s.min = b :=
  (@inf_le (WithTop α) _ _ _ _ _ _ h _ rfl).imp fun b => Exists.fst
#align finset.min_of_mem Finset.min_of_mem

theorem min_of_nonempty {s : Finset α} (h : s.Nonempty) : ∃ a : α, s.min = a :=
  let ⟨a, ha⟩ := h
  min_of_mem ha
#align finset.min_of_nonempty Finset.min_of_nonempty

theorem min_eq_top {s : Finset α} : s.min = ⊤ ↔ s = ∅ :=
  ⟨fun h =>
    s.eq_empty_or_nonempty.elim id fun H =>
      by
      let ⟨a, ha⟩ := min_of_nonempty H
      rw [h] at ha <;> cases ha,
    fun h => h.symm ▸ min_empty⟩
#align finset.min_eq_top Finset.min_eq_top

theorem mem_of_min {s : Finset α} : ∀ {a : α}, s.min = a → a ∈ s :=
  @mem_of_max αᵒᵈ _ s
#align finset.mem_of_min Finset.mem_of_min

theorem min_le {a : α} {s : Finset α} (as : a ∈ s) : s.min ≤ a :=
  inf_le as
#align finset.min_le Finset.min_le

theorem not_mem_of_coe_lt_min {a : α} {s : Finset α} (h : ↑a < s.min) : a ∉ s :=
  mt min_le h.not_le
#align finset.not_mem_of_coe_lt_min Finset.not_mem_of_coe_lt_min

theorem min_le_of_eq {s : Finset α} {a b : α} (h₁ : b ∈ s) (h₂ : s.min = a) : a ≤ b :=
  WithTop.coe_le_coe.mp <| h₂.ge.trans (min_le h₁)
#align finset.min_le_of_eq Finset.min_le_of_eq

theorem not_mem_of_lt_min {s : Finset α} {a b : α} (h₁ : a < b) (h₂ : s.min = ↑b) : a ∉ s :=
  Finset.not_mem_of_coe_lt_min <| (WithTop.coe_lt_coe.mpr h₁).trans_eq h₂.symm
#align finset.not_mem_of_lt_min Finset.not_mem_of_lt_min

theorem min_mono {s t : Finset α} (st : s ⊆ t) : t.min ≤ s.min :=
  inf_mono st
#align finset.min_mono Finset.min_mono

protected theorem le_min {m : WithTop α} {s : Finset α} (st : ∀ a : α, a ∈ s → m ≤ a) : m ≤ s.min :=
  Finset.le_inf st
#align finset.le_min Finset.le_min

/-- Given a nonempty finset `s` in a linear order `α`, then `s.min' h` is its minimum, as an
element of `α`, where `h` is a proof of nonemptiness. Without this assumption, use instead `s.min`,
taking values in `with_top α`. -/
def min' (s : Finset α) (H : s.Nonempty) : α :=
  inf' s H id
#align finset.min' Finset.min'

/-- Given a nonempty finset `s` in a linear order `α`, then `s.max' h` is its maximum, as an
element of `α`, where `h` is a proof of nonemptiness. Without this assumption, use instead `s.max`,
taking values in `with_bot α`. -/
def max' (s : Finset α) (H : s.Nonempty) : α :=
  sup' s H id
#align finset.max' Finset.max'

variable (s : Finset α) (H : s.Nonempty) {x : α}

theorem min'_mem : s.min' H ∈ s :=
  mem_of_min <| by simp [min', Finset.min]
#align finset.min'_mem Finset.min'_mem

theorem min'_le (x) (H2 : x ∈ s) : s.min' ⟨x, H2⟩ ≤ x :=
  min_le_of_eq H2 (WithTop.coe_untop _ _).symm
#align finset.min'_le Finset.min'_le

theorem le_min' (x) (H2 : ∀ y ∈ s, x ≤ y) : x ≤ s.min' H :=
  H2 _ <| min'_mem _ _
#align finset.le_min' Finset.le_min'

theorem is_least_min' : IsLeast (↑s) (s.min' H) :=
  ⟨min'_mem _ _, min'_le _⟩
#align finset.is_least_min' Finset.is_least_min'

@[simp]
theorem le_min'_iff {x} : x ≤ s.min' H ↔ ∀ y ∈ s, x ≤ y :=
  le_isGLB_iff (is_least_min' s H).IsGlb
#align finset.le_min'_iff Finset.le_min'_iff

/-- `{a}.min' _` is `a`. -/
@[simp]
theorem min'_singleton (a : α) : ({a} : Finset α).min' (singleton_nonempty _) = a := by simp [min']
#align finset.min'_singleton Finset.min'_singleton

theorem max'_mem : s.max' H ∈ s :=
  mem_of_max <| by simp [max', Finset.max]
#align finset.max'_mem Finset.max'_mem

theorem le_max' (x) (H2 : x ∈ s) : x ≤ s.max' ⟨x, H2⟩ :=
  le_max_of_eq H2 (WithBot.coe_unbot _ _).symm
#align finset.le_max' Finset.le_max'

theorem max'_le (x) (H2 : ∀ y ∈ s, y ≤ x) : s.max' H ≤ x :=
  H2 _ <| max'_mem _ _
#align finset.max'_le Finset.max'_le

theorem is_greatest_max' : IsGreatest (↑s) (s.max' H) :=
  ⟨max'_mem _ _, le_max' _⟩
#align finset.is_greatest_max' Finset.is_greatest_max'

@[simp]
theorem max'_le_iff {x} : s.max' H ≤ x ↔ ∀ y ∈ s, y ≤ x :=
  isLUB_le_iff (is_greatest_max' s H).IsLub
#align finset.max'_le_iff Finset.max'_le_iff

@[simp]
theorem max'_lt_iff {x} : s.max' H < x ↔ ∀ y ∈ s, y < x :=
  ⟨fun Hlt y hy => (s.le_max' y hy).trans_lt Hlt, fun H => H _ <| s.max'_mem _⟩
#align finset.max'_lt_iff Finset.max'_lt_iff

@[simp]
theorem lt_min'_iff : x < s.min' H ↔ ∀ y ∈ s, x < y :=
  @max'_lt_iff αᵒᵈ _ _ H _
#align finset.lt_min'_iff Finset.lt_min'_iff

theorem max'_eq_sup' : s.max' H = s.sup' H id :=
  eq_of_forall_ge_iff fun a => (max'_le_iff _ _).trans (sup'_le_iff _ _).symm
#align finset.max'_eq_sup' Finset.max'_eq_sup'

theorem min'_eq_inf' : s.min' H = s.inf' H id :=
  @max'_eq_sup' αᵒᵈ _ s H
#align finset.min'_eq_inf' Finset.min'_eq_inf'

/-- `{a}.max' _` is `a`. -/
@[simp]
theorem max'_singleton (a : α) : ({a} : Finset α).max' (singleton_nonempty _) = a := by simp [max']
#align finset.max'_singleton Finset.max'_singleton

theorem min'_lt_max' {i j} (H1 : i ∈ s) (H2 : j ∈ s) (H3 : i ≠ j) :
    s.min' ⟨i, H1⟩ < s.max' ⟨i, H1⟩ :=
  isGLB_lt_isLUB_of_ne (s.is_least_min' _).IsGlb (s.is_greatest_max' _).IsLub H1 H2 H3
#align finset.min'_lt_max' Finset.min'_lt_max'

/-- If there's more than 1 element, the min' is less than the max'. An alternate version of
`min'_lt_max'` which is sometimes more convenient.
-/
theorem min'_lt_max'_of_card (h₂ : 1 < card s) :
    s.min' (Finset.card_pos.mp <| lt_trans zero_lt_one h₂) <
      s.max' (Finset.card_pos.mp <| lt_trans zero_lt_one h₂) :=
  by
  rcases one_lt_card.1 h₂ with ⟨a, ha, b, hb, hab⟩
  exact s.min'_lt_max' ha hb hab
#align finset.min'_lt_max'_of_card Finset.min'_lt_max'_of_card

theorem map_of_dual_min (s : Finset αᵒᵈ) : s.min.map ofDual = (s.image ofDual).max :=
  by
  rw [max_eq_sup_with_bot, sup_image]
  exact congr_fun Option.map_id _
#align finset.map_of_dual_min Finset.map_of_dual_min

theorem map_of_dual_max (s : Finset αᵒᵈ) : s.max.map ofDual = (s.image ofDual).min :=
  by
  rw [min_eq_inf_with_top, inf_image]
  exact congr_fun Option.map_id _
#align finset.map_of_dual_max Finset.map_of_dual_max

theorem map_to_dual_min (s : Finset α) : s.min.map toDual = (s.image toDual).max :=
  by
  rw [max_eq_sup_with_bot, sup_image]
  exact congr_fun Option.map_id _
#align finset.map_to_dual_min Finset.map_to_dual_min

theorem map_to_dual_max (s : Finset α) : s.max.map toDual = (s.image toDual).min :=
  by
  rw [min_eq_inf_with_top, inf_image]
  exact congr_fun Option.map_id _
#align finset.map_to_dual_max Finset.map_to_dual_max

theorem of_dual_min' {s : Finset αᵒᵈ} (hs : s.Nonempty) :
    ofDual (min' s hs) = max' (s.image ofDual) (hs.image _) :=
  by
  convert rfl
  exact image_id
#align finset.of_dual_min' Finset.of_dual_min'

theorem of_dual_max' {s : Finset αᵒᵈ} (hs : s.Nonempty) :
    ofDual (max' s hs) = min' (s.image ofDual) (hs.image _) :=
  by
  convert rfl
  exact image_id
#align finset.of_dual_max' Finset.of_dual_max'

theorem to_dual_min' {s : Finset α} (hs : s.Nonempty) :
    toDual (min' s hs) = max' (s.image toDual) (hs.image _) :=
  by
  convert rfl
  exact image_id
#align finset.to_dual_min' Finset.to_dual_min'

theorem to_dual_max' {s : Finset α} (hs : s.Nonempty) :
    toDual (max' s hs) = min' (s.image toDual) (hs.image _) :=
  by
  convert rfl
  exact image_id
#align finset.to_dual_max' Finset.to_dual_max'

theorem max'_subset {s t : Finset α} (H : s.Nonempty) (hst : s ⊆ t) :
    s.max' H ≤ t.max' (H.mono hst) :=
  le_max' _ _ (hst (s.max'_mem H))
#align finset.max'_subset Finset.max'_subset

theorem min'_subset {s t : Finset α} (H : s.Nonempty) (hst : s ⊆ t) :
    t.min' (H.mono hst) ≤ s.min' H :=
  min'_le _ _ (hst (s.min'_mem H))
#align finset.min'_subset Finset.min'_subset

theorem max'_insert (a : α) (s : Finset α) (H : s.Nonempty) :
    (insert a s).max' (s.insert_nonempty a) = max (s.max' H) a :=
  (is_greatest_max' _ _).unique <| by
    rw [coe_insert, max_comm]
    exact (is_greatest_max' _ _).insert _
#align finset.max'_insert Finset.max'_insert

theorem min'_insert (a : α) (s : Finset α) (H : s.Nonempty) :
    (insert a s).min' (s.insert_nonempty a) = min (s.min' H) a :=
  (is_least_min' _ _).unique <| by
    rw [coe_insert, min_comm]
    exact (is_least_min' _ _).insert _
#align finset.min'_insert Finset.min'_insert

theorem lt_max'_of_mem_erase_max' [DecidableEq α] {a : α} (ha : a ∈ s.erase (s.max' H)) :
    a < s.max' H :=
  lt_of_le_of_ne (le_max' _ _ (mem_of_mem_erase ha)) <| ne_of_mem_of_not_mem ha <| not_mem_erase _ _
#align finset.lt_max'_of_mem_erase_max' Finset.lt_max'_of_mem_erase_max'

theorem min'_lt_of_mem_erase_min' [DecidableEq α] {a : α} (ha : a ∈ s.erase (s.min' H)) :
    s.min' H < a :=
  @lt_max'_of_mem_erase_max' αᵒᵈ _ s H _ a ha
#align finset.min'_lt_of_mem_erase_min' Finset.min'_lt_of_mem_erase_min'

@[simp]
theorem max'_image [LinearOrder β] {f : α → β} (hf : Monotone f) (s : Finset α)
    (h : (s.image f).Nonempty) : (s.image f).max' h = f (s.max' ((Nonempty.image_iff f).mp h)) :=
  by
  refine'
    le_antisymm (max'_le _ _ _ fun y hy => _) (le_max' _ _ (mem_image.mpr ⟨_, max'_mem _ _, rfl⟩))
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  exact hf (le_max' _ _ hx)
#align finset.max'_image Finset.max'_image

@[simp]
theorem min'_image [LinearOrder β] {f : α → β} (hf : Monotone f) (s : Finset α)
    (h : (s.image f).Nonempty) : (s.image f).min' h = f (s.min' ((Nonempty.image_iff f).mp h)) :=
  by
  convert @max'_image αᵒᵈ βᵒᵈ _ _ (fun a : αᵒᵈ => to_dual (f (of_dual a))) (by simpa) _ _ <;>
    convert h
  rw [nonempty.image_iff]
#align finset.min'_image Finset.min'_image

theorem coe_max' {s : Finset α} (hs : s.Nonempty) : ↑(s.max' hs) = s.max :=
  coe_sup' hs id
#align finset.coe_max' Finset.coe_max'

theorem coe_min' {s : Finset α} (hs : s.Nonempty) : ↑(s.min' hs) = s.min :=
  coe_inf' hs id
#align finset.coe_min' Finset.coe_min'

theorem max_mem_image_coe {s : Finset α} (hs : s.Nonempty) :
    s.max ∈ (s.image coe : Finset (WithBot α)) :=
  mem_image.2 ⟨max' s hs, max'_mem _ _, coe_max' hs⟩
#align finset.max_mem_image_coe Finset.max_mem_image_coe

theorem min_mem_image_coe {s : Finset α} (hs : s.Nonempty) :
    s.min ∈ (s.image coe : Finset (WithTop α)) :=
  mem_image.2 ⟨min' s hs, min'_mem _ _, coe_min' hs⟩
#align finset.min_mem_image_coe Finset.min_mem_image_coe

theorem max_mem_insert_bot_image_coe (s : Finset α) :
    s.max ∈ (insert ⊥ (s.image coe) : Finset (WithBot α)) :=
  mem_insert.2 <| s.eq_empty_or_nonempty.imp max_eq_bot.2 max_mem_image_coe
#align finset.max_mem_insert_bot_image_coe Finset.max_mem_insert_bot_image_coe

theorem min_mem_insert_top_image_coe (s : Finset α) :
    s.min ∈ (insert ⊤ (s.image coe) : Finset (WithTop α)) :=
  mem_insert.2 <| s.eq_empty_or_nonempty.imp min_eq_top.2 min_mem_image_coe
#align finset.min_mem_insert_top_image_coe Finset.min_mem_insert_top_image_coe

theorem max'_erase_ne_self {s : Finset α} (s0 : (s.erase x).Nonempty) : (s.erase x).max' s0 ≠ x :=
  ne_of_mem_erase (max'_mem _ s0)
#align finset.max'_erase_ne_self Finset.max'_erase_ne_self

theorem min'_erase_ne_self {s : Finset α} (s0 : (s.erase x).Nonempty) : (s.erase x).min' s0 ≠ x :=
  ne_of_mem_erase (min'_mem _ s0)
#align finset.min'_erase_ne_self Finset.min'_erase_ne_self

theorem max_erase_ne_self {s : Finset α} : (s.erase x).max ≠ x :=
  by
  by_cases s0 : (s.erase x).Nonempty
  · refine' ne_of_eq_of_ne (coe_max' s0).symm _
    exact with_bot.coe_eq_coe.not.mpr (max'_erase_ne_self _)
  · rw [not_nonempty_iff_eq_empty.mp s0, max_empty]
    exact WithBot.bot_ne_coe
#align finset.max_erase_ne_self Finset.max_erase_ne_self

theorem min_erase_ne_self {s : Finset α} : (s.erase x).min ≠ x := by
  convert @max_erase_ne_self αᵒᵈ _ _ _
#align finset.min_erase_ne_self Finset.min_erase_ne_self

theorem exists_next_right {x : α} {s : Finset α} (h : ∃ y ∈ s, x < y) :
    ∃ y ∈ s, x < y ∧ ∀ z ∈ s, x < z → y ≤ z :=
  have Hne : (s.filter ((· < ·) x)).Nonempty := h.imp fun y hy => mem_filter.2 ⟨hy.fst, hy.snd⟩
  ⟨min' _ Hne, (mem_filter.1 (min'_mem _ Hne)).1, (mem_filter.1 (min'_mem _ Hne)).2, fun z hzs hz =>
    min'_le _ _ <| mem_filter.2 ⟨hzs, hz⟩⟩
#align finset.exists_next_right Finset.exists_next_right

theorem exists_next_left {x : α} {s : Finset α} (h : ∃ y ∈ s, y < x) :
    ∃ y ∈ s, y < x ∧ ∀ z ∈ s, z < x → z ≤ y :=
  @exists_next_right αᵒᵈ _ x s h
#align finset.exists_next_left Finset.exists_next_left

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x y «expr ∈ » s) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x y «expr ∈ » s) -/
/-- If finsets `s` and `t` are interleaved, then `finset.card s ≤ finset.card t + 1`. -/
theorem card_le_of_interleaved {s t : Finset α}
    (h :
      ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s),
        x < y → (∀ z ∈ s, z ∉ Set.Ioo x y) → ∃ z ∈ t, x < z ∧ z < y) :
    s.card ≤ t.card + 1 :=
  by
  replace h : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), x < y → ∃ z ∈ t, x < z ∧ z < y
  · intro x hx y hy hxy
    rcases exists_next_right ⟨y, hy, hxy⟩ with ⟨a, has, hxa, ha⟩
    rcases h x hx a has hxa fun z hzs hz => hz.2.not_le <| ha _ hzs hz.1 with ⟨b, hbt, hxb, hba⟩
    exact ⟨b, hbt, hxb, hba.trans_le <| ha _ hy hxy⟩
  set f : α → WithTop α := fun x => (t.filter fun y => x < y).min
  have f_mono : StrictMonoOn f s := by
    intro x hx y hy hxy
    rcases h x hx y hy hxy with ⟨a, hat, hxa, hay⟩
    calc
      f x ≤ a := min_le (mem_filter.2 ⟨hat, hxa⟩)
      _ < f y :=
        (Finset.lt_inf_iff <| WithTop.coe_lt_top a).2 fun b hb =>
          WithTop.coe_lt_coe.2 <| hay.trans (mem_filter.1 hb).2
      
  calc
    s.card = (s.image f).card := (card_image_of_inj_on f_mono.inj_on).symm
    _ ≤ (insert ⊤ (t.image coe) : Finset (WithTop α)).card :=
      card_mono <|
        image_subset_iff.2 fun x hx =>
          insert_subset_insert _ (image_subset_image <| filter_subset _ _)
            (min_mem_insert_top_image_coe _)
    _ ≤ t.card + 1 := (card_insert_le _ _).trans (add_le_add_right card_image_le _)
    
#align finset.card_le_of_interleaved Finset.card_le_of_interleaved

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x y «expr ∈ » s) -/
/-- If finsets `s` and `t` are interleaved, then `finset.card s ≤ finset.card (t \ s) + 1`. -/
theorem card_le_diff_of_interleaved {s t : Finset α}
    (h :
      ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s),
        x < y → (∀ z ∈ s, z ∉ Set.Ioo x y) → ∃ z ∈ t, x < z ∧ z < y) :
    s.card ≤ (t \ s).card + 1 :=
  card_le_of_interleaved fun x hx y hy hxy hs =>
    let ⟨z, hzt, hxz, hzy⟩ := h x hx y hy hxy hs
    ⟨z, mem_sdiff.2 ⟨hzt, fun hzs => hs z hzs ⟨hxz, hzy⟩⟩, hxz, hzy⟩
#align finset.card_le_diff_of_interleaved Finset.card_le_diff_of_interleaved

/-- Induction principle for `finset`s in a linearly ordered type: a predicate is true on all
`s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` strictly greater than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_elim]
theorem induction_on_max [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h0 : p ∅)
    (step : ∀ a s, (∀ x ∈ s, x < a) → p s → p (insert a s)) : p s :=
  by
  induction' s using Finset.strongInductionOn with s ihs
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · exact h0
  · have H : s.max' hne ∈ s := max'_mem s hne
    rw [← insert_erase H]
    exact step _ _ (fun x => s.lt_max'_of_mem_erase_max' hne) (ihs _ <| erase_ssubset H)
#align finset.induction_on_max Finset.induction_on_max

/-- Induction principle for `finset`s in a linearly ordered type: a predicate is true on all
`s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` strictly less than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_elim]
theorem induction_on_min [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h0 : p ∅)
    (step : ∀ a s, (∀ x ∈ s, a < x) → p s → p (insert a s)) : p s :=
  @induction_on_max αᵒᵈ _ _ _ s h0 step
#align finset.induction_on_min Finset.induction_on_min

end MaxMin

section MaxMinInductionValue

variable [LinearOrder α] [LinearOrder β]

/-- Induction principle for `finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` such that for elements of `s` denoted by `x` we have
  `f x ≤ f a`, `p s` implies `p (insert a s)`. -/
@[elab_as_elim]
theorem induction_on_max_value [DecidableEq ι] (f : ι → α) {p : Finset ι → Prop} (s : Finset ι)
    (h0 : p ∅) (step : ∀ a s, a ∉ s → (∀ x ∈ s, f x ≤ f a) → p s → p (insert a s)) : p s :=
  by
  induction' s using Finset.strongInductionOn with s ihs
  rcases(s.image f).eq_empty_or_nonempty with (hne | hne)
  · simp only [image_eq_empty] at hne
    simp only [hne, h0]
  · have H : (s.image f).max' hne ∈ s.image f := max'_mem (s.image f) hne
    simp only [mem_image, exists_prop] at H
    rcases H with ⟨a, has, hfa⟩
    rw [← insert_erase has]
    refine' step _ _ (not_mem_erase a s) (fun x hx => _) (ihs _ <| erase_ssubset has)
    rw [hfa]
    exact le_max' _ _ (mem_image_of_mem _ <| mem_of_mem_erase hx)
#align finset.induction_on_max_value Finset.induction_on_max_value

/-- Induction principle for `finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` such that for elements of `s` denoted by `x` we have
  `f a ≤ f x`, `p s` implies `p (insert a s)`. -/
@[elab_as_elim]
theorem induction_on_min_value [DecidableEq ι] (f : ι → α) {p : Finset ι → Prop} (s : Finset ι)
    (h0 : p ∅) (step : ∀ a s, a ∉ s → (∀ x ∈ s, f a ≤ f x) → p s → p (insert a s)) : p s :=
  @induction_on_max_value αᵒᵈ ι _ _ _ _ s h0 step
#align finset.induction_on_min_value Finset.induction_on_min_value

end MaxMinInductionValue

section ExistsMaxMin

variable [LinearOrder α]

theorem exists_max_image (s : Finset β) (f : β → α) (h : s.Nonempty) :
    ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x :=
  by
  cases' max_of_nonempty (h.image f) with y hy
  rcases mem_image.mp (mem_of_max hy) with ⟨x, hx, rfl⟩
  exact ⟨x, hx, fun x' hx' => le_max_of_eq (mem_image_of_mem f hx') hy⟩
#align finset.exists_max_image Finset.exists_max_image

theorem exists_min_image (s : Finset β) (f : β → α) (h : s.Nonempty) :
    ∃ x ∈ s, ∀ x' ∈ s, f x ≤ f x' :=
  @exists_max_image αᵒᵈ β _ s f h
#align finset.exists_min_image Finset.exists_min_image

end ExistsMaxMin

theorem is_glb_iff_is_least [LinearOrder α] (i : α) (s : Finset α) (hs : s.Nonempty) :
    IsGLB (s : Set α) i ↔ IsLeast (↑s) i :=
  by
  refine' ⟨fun his => _, IsLeast.isGLB⟩
  suffices i = min' s hs by
    rw [this]
    exact is_least_min' s hs
  rw [IsGLB, IsGreatest, mem_lowerBounds, mem_upperBounds] at his
  exact le_antisymm (his.1 (Finset.min' s hs) (Finset.min'_mem s hs)) (his.2 _ (Finset.min'_le s))
#align finset.is_glb_iff_is_least Finset.is_glb_iff_is_least

theorem is_lub_iff_is_greatest [LinearOrder α] (i : α) (s : Finset α) (hs : s.Nonempty) :
    IsLUB (s : Set α) i ↔ IsGreatest (↑s) i :=
  @is_glb_iff_is_least αᵒᵈ _ i s hs
#align finset.is_lub_iff_is_greatest Finset.is_lub_iff_is_greatest

theorem is_glb_mem [LinearOrder α] {i : α} (s : Finset α) (his : IsGLB (s : Set α) i)
    (hs : s.Nonempty) : i ∈ s := by
  rw [← mem_coe]
  exact ((is_glb_iff_is_least i s hs).mp his).1
#align finset.is_glb_mem Finset.is_glb_mem

theorem is_lub_mem [LinearOrder α] {i : α} (s : Finset α) (his : IsLUB (s : Set α) i)
    (hs : s.Nonempty) : i ∈ s :=
  @is_glb_mem αᵒᵈ _ i s his hs
#align finset.is_lub_mem Finset.is_lub_mem

end Finset

namespace Multiset

theorem map_finset_sup [DecidableEq α] [DecidableEq β] (s : Finset γ) (f : γ → Multiset β)
    (g : β → α) (hg : Function.Injective g) : map g (s.sup f) = s.sup (map g ∘ f) :=
  Finset.comp_sup_eq_sup_comp _ (fun _ _ => map_union hg) (map_zero _)
#align multiset.map_finset_sup Multiset.map_finset_sup

theorem count_finset_sup [DecidableEq β] (s : Finset α) (f : α → Multiset β) (b : β) :
    count b (s.sup f) = s.sup fun a => count b (f a) :=
  by
  letI := Classical.decEq α
  refine' s.induction _ _
  · exact count_zero _
  · intro i s his ih
    rw [Finset.sup_insert, sup_eq_union, count_union, Finset.sup_insert, ih]
    rfl
#align multiset.count_finset_sup Multiset.count_finset_sup

theorem mem_sup {α β} [DecidableEq β] {s : Finset α} {f : α → Multiset β} {x : β} :
    x ∈ s.sup f ↔ ∃ v ∈ s, x ∈ f v := by
  classical
    apply s.induction_on
    · simp
    · intro a s has hxs
      rw [Finset.sup_insert, Multiset.sup_eq_union, Multiset.mem_union]
      constructor
      · intro hxi
        cases' hxi with hf hf
        · refine' ⟨a, _, hf⟩
          simp only [true_or_iff, eq_self_iff_true, Finset.mem_insert]
        · rcases hxs.mp hf with ⟨v, hv, hfv⟩
          refine' ⟨v, _, hfv⟩
          simp only [hv, or_true_iff, Finset.mem_insert]
      · rintro ⟨v, hv, hfv⟩
        rw [Finset.mem_insert] at hv
        rcases hv with (rfl | hv)
        · exact Or.inl hfv
        · refine' Or.inr (hxs.mpr ⟨v, hv, hfv⟩)
#align multiset.mem_sup Multiset.mem_sup

end Multiset

namespace Finset

theorem mem_sup {α β} [DecidableEq β] {s : Finset α} {f : α → Finset β} {x : β} :
    x ∈ s.sup f ↔ ∃ v ∈ s, x ∈ f v :=
  by
  change _ ↔ ∃ v ∈ s, x ∈ (f v).val
  rw [← Multiset.mem_sup, ← Multiset.mem_to_finset, sup_to_finset]
  simp_rw [val_to_finset]
#align finset.mem_sup Finset.mem_sup

theorem sup_eq_bUnion {α β} [DecidableEq β] (s : Finset α) (t : α → Finset β) :
    s.sup t = s.bUnion t := by
  ext
  rw [mem_sup, mem_bUnion]
#align finset.sup_eq_bUnion Finset.sup_eq_bUnion

@[simp]
theorem sup_singleton'' [DecidableEq α] (s : Finset β) (f : β → α) :
    (s.sup fun b => {f b}) = s.image f := by
  ext a
  rw [mem_sup, mem_image]
  simp only [mem_singleton, eq_comm]
#align finset.sup_singleton'' Finset.sup_singleton''

@[simp]
theorem sup_singleton' [DecidableEq α] (s : Finset α) : s.sup singleton = s :=
  (s.sup_singleton'' _).trans image_id
#align finset.sup_singleton' Finset.sup_singleton'

end Finset

section Lattice

variable {ι' : Sort _} [CompleteLattice α]

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : finset ι` of suprema
`⨆ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `supr_eq_supr_finset'` for a version
that works for `ι : Sort*`. -/
theorem supr_eq_supr_finset (s : ι → α) : (⨆ i, s i) = ⨆ t : Finset ι, ⨆ i ∈ t, s i := by
  classical exact
      le_antisymm
        (supᵢ_le fun b => le_supᵢ_of_le {b} <| le_supᵢ_of_le b <| le_supᵢ_of_le (by simp) <| le_rfl)
        (supᵢ_le fun t => supᵢ_le fun b => supᵢ_le fun hb => le_supᵢ _ _)
#align supr_eq_supr_finset supr_eq_supr_finset

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : finset ι` of suprema
`⨆ i ∈ t, s i`. This version works for `ι : Sort*`. See `supr_eq_supr_finset` for a version
that assumes `ι : Type*` but has no `plift`s. -/
theorem supr_eq_supr_finset' (s : ι' → α) :
    (⨆ i, s i) = ⨆ t : Finset (PLift ι'), ⨆ i ∈ t, s (PLift.down i) := by
  rw [← supr_eq_supr_finset, ← equiv.plift.surjective.supr_comp] <;> rfl
#align supr_eq_supr_finset' supr_eq_supr_finset'

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : finset ι` of infima
`⨅ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `infi_eq_infi_finset'` for a version
that works for `ι : Sort*`. -/
theorem infi_eq_infi_finset (s : ι → α) : (⨅ i, s i) = ⨅ (t : Finset ι) (i ∈ t), s i :=
  @supr_eq_supr_finset αᵒᵈ _ _ _
#align infi_eq_infi_finset infi_eq_infi_finset

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : finset ι` of infima
`⨅ i ∈ t, s i`. This version works for `ι : Sort*`. See `infi_eq_infi_finset` for a version
that assumes `ι : Type*` but has no `plift`s. -/
theorem infi_eq_infi_finset' (s : ι' → α) :
    (⨅ i, s i) = ⨅ t : Finset (PLift ι'), ⨅ i ∈ t, s (PLift.down i) :=
  @supr_eq_supr_finset' αᵒᵈ _ _ _
#align infi_eq_infi_finset' infi_eq_infi_finset'

end Lattice

namespace Set

variable {ι' : Sort _}

/-- Union of an indexed family of sets `s : ι → set α` is equal to the union of the unions
of finite subfamilies. This version assumes `ι : Type*`. See also `Union_eq_Union_finset'` for
a version that works for `ι : Sort*`. -/
theorem Union_eq_Union_finset (s : ι → Set α) : (⋃ i, s i) = ⋃ t : Finset ι, ⋃ i ∈ t, s i :=
  supr_eq_supr_finset s
#align set.Union_eq_Union_finset Set.Union_eq_Union_finset

/-- Union of an indexed family of sets `s : ι → set α` is equal to the union of the unions
of finite subfamilies. This version works for `ι : Sort*`. See also `Union_eq_Union_finset` for
a version that assumes `ι : Type*` but avoids `plift`s in the right hand side. -/
theorem Union_eq_Union_finset' (s : ι' → Set α) :
    (⋃ i, s i) = ⋃ t : Finset (PLift ι'), ⋃ i ∈ t, s (PLift.down i) :=
  supr_eq_supr_finset' s
#align set.Union_eq_Union_finset' Set.Union_eq_Union_finset'

/-- Intersection of an indexed family of sets `s : ι → set α` is equal to the intersection of the
intersections of finite subfamilies. This version assumes `ι : Type*`. See also
`Inter_eq_Inter_finset'` for a version that works for `ι : Sort*`. -/
theorem Inter_eq_Inter_finset (s : ι → Set α) : (⋂ i, s i) = ⋂ t : Finset ι, ⋂ i ∈ t, s i :=
  infi_eq_infi_finset s
#align set.Inter_eq_Inter_finset Set.Inter_eq_Inter_finset

/-- Intersection of an indexed family of sets `s : ι → set α` is equal to the intersection of the
intersections of finite subfamilies. This version works for `ι : Sort*`. See also
`Inter_eq_Inter_finset` for a version that assumes `ι : Type*` but avoids `plift`s in the right
hand side. -/
theorem Inter_eq_Inter_finset' (s : ι' → Set α) :
    (⋂ i, s i) = ⋂ t : Finset (PLift ι'), ⋂ i ∈ t, s (PLift.down i) :=
  infi_eq_infi_finset' s
#align set.Inter_eq_Inter_finset' Set.Inter_eq_Inter_finset'

end Set

namespace Finset

/-! ### Interaction with ordered algebra structures -/


theorem sup_mul_le_mul_sup_of_nonneg [LinearOrderedSemiring α] [OrderBot α] {a b : ι → α}
    (s : Finset ι) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    s.sup (a * b) ≤ s.sup a * s.sup b :=
  Finset.sup_le fun i hi =>
    mul_le_mul (le_sup hi) (le_sup hi) (hb _ hi) ((ha _ hi).trans <| le_sup hi)
#align finset.sup_mul_le_mul_sup_of_nonneg Finset.sup_mul_le_mul_sup_of_nonneg

theorem mul_inf_le_inf_mul_of_nonneg [LinearOrderedSemiring α] [OrderTop α] {a b : ι → α}
    (s : Finset ι) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    s.inf a * s.inf b ≤ s.inf (a * b) :=
  Finset.le_inf fun i hi => mul_le_mul (inf_le hi) (inf_le hi) (Finset.le_inf hb) (ha i hi)
#align finset.mul_inf_le_inf_mul_of_nonneg Finset.mul_inf_le_inf_mul_of_nonneg

theorem sup'_mul_le_mul_sup'_of_nonneg [LinearOrderedSemiring α] {a b : ι → α} (s : Finset ι)
    (H : s.Nonempty) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    s.sup' H (a * b) ≤ s.sup' H a * s.sup' H b :=
  (sup'_le _ _) fun i hi =>
    mul_le_mul (le_sup' _ hi) (le_sup' _ hi) (hb _ hi) ((ha _ hi).trans <| le_sup' _ hi)
#align finset.sup'_mul_le_mul_sup'_of_nonneg Finset.sup'_mul_le_mul_sup'_of_nonneg

theorem inf'_mul_le_mul_inf'_of_nonneg [LinearOrderedSemiring α] {a b : ι → α} (s : Finset ι)
    (H : s.Nonempty) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    s.inf' H a * s.inf' H b ≤ s.inf' H (a * b) :=
  (le_inf' _ _) fun i hi => mul_le_mul (inf'_le _ hi) (inf'_le _ hi) (le_inf' _ _ hb) (ha _ hi)
#align finset.inf'_mul_le_mul_inf'_of_nonneg Finset.inf'_mul_le_mul_inf'_of_nonneg

open Function

/-! ### Interaction with big lattice/set operations -/


section Lattice

theorem supr_coe [SupSet β] (f : α → β) (s : Finset α) : (⨆ x ∈ (↑s : Set α), f x) = ⨆ x ∈ s, f x :=
  rfl
#align finset.supr_coe Finset.supr_coe

theorem infi_coe [InfSet β] (f : α → β) (s : Finset α) : (⨅ x ∈ (↑s : Set α), f x) = ⨅ x ∈ s, f x :=
  rfl
#align finset.infi_coe Finset.infi_coe

variable [CompleteLattice β]

theorem supr_singleton (a : α) (s : α → β) : (⨆ x ∈ ({a} : Finset α), s x) = s a := by simp
#align finset.supr_singleton Finset.supr_singleton

theorem infi_singleton (a : α) (s : α → β) : (⨅ x ∈ ({a} : Finset α), s x) = s a := by simp
#align finset.infi_singleton Finset.infi_singleton

theorem supr_option_to_finset (o : Option α) (f : α → β) : (⨆ x ∈ o.toFinset, f x) = ⨆ x ∈ o, f x :=
  by simp
#align finset.supr_option_to_finset Finset.supr_option_to_finset

theorem infi_option_to_finset (o : Option α) (f : α → β) : (⨅ x ∈ o.toFinset, f x) = ⨅ x ∈ o, f x :=
  @supr_option_to_finset _ βᵒᵈ _ _ _
#align finset.infi_option_to_finset Finset.infi_option_to_finset

variable [DecidableEq α]

theorem supr_union {f : α → β} {s t : Finset α} :
    (⨆ x ∈ s ∪ t, f x) = (⨆ x ∈ s, f x) ⊔ ⨆ x ∈ t, f x := by simp [supᵢ_or, supᵢ_sup_eq]
#align finset.supr_union Finset.supr_union

theorem infi_union {f : α → β} {s t : Finset α} :
    (⨅ x ∈ s ∪ t, f x) = (⨅ x ∈ s, f x) ⊓ ⨅ x ∈ t, f x :=
  @supr_union α βᵒᵈ _ _ _ _ _
#align finset.infi_union Finset.infi_union

theorem supr_insert (a : α) (s : Finset α) (t : α → β) :
    (⨆ x ∈ insert a s, t x) = t a ⊔ ⨆ x ∈ s, t x :=
  by
  rw [insert_eq]
  simp only [supᵢ_union, Finset.supr_singleton]
#align finset.supr_insert Finset.supr_insert

theorem infi_insert (a : α) (s : Finset α) (t : α → β) :
    (⨅ x ∈ insert a s, t x) = t a ⊓ ⨅ x ∈ s, t x :=
  @supr_insert α βᵒᵈ _ _ _ _ _
#align finset.infi_insert Finset.infi_insert

theorem supr_finset_image {f : γ → α} {g : α → β} {s : Finset γ} :
    (⨆ x ∈ s.image f, g x) = ⨆ y ∈ s, g (f y) := by rw [← supr_coe, coe_image, supᵢ_image, supr_coe]
#align finset.supr_finset_image Finset.supr_finset_image

theorem sup_finset_image {β γ : Type _} [SemilatticeSup β] [OrderBot β] (f : γ → α) (g : α → β)
    (s : Finset γ) : (s.image f).sup g = s.sup (g ∘ f) := by
  classical induction' s using Finset.induction_on with a s' ha ih <;> simp [*]
#align finset.sup_finset_image Finset.sup_finset_image

theorem infi_finset_image {f : γ → α} {g : α → β} {s : Finset γ} :
    (⨅ x ∈ s.image f, g x) = ⨅ y ∈ s, g (f y) := by rw [← infi_coe, coe_image, infᵢ_image, infi_coe]
#align finset.infi_finset_image Finset.infi_finset_image

theorem supr_insert_update {x : α} {t : Finset α} (f : α → β) {s : β} (hx : x ∉ t) :
    (⨆ i ∈ insert x t, Function.update f x s i) = s ⊔ ⨆ i ∈ t, f i :=
  by
  simp only [Finset.supr_insert, update_same]
  rcongr (i hi); apply update_noteq; rintro rfl; exact hx hi
#align finset.supr_insert_update Finset.supr_insert_update

theorem infi_insert_update {x : α} {t : Finset α} (f : α → β) {s : β} (hx : x ∉ t) :
    (⨅ i ∈ insert x t, update f x s i) = s ⊓ ⨅ i ∈ t, f i :=
  @supr_insert_update α βᵒᵈ _ _ _ _ f _ hx
#align finset.infi_insert_update Finset.infi_insert_update

theorem supr_bUnion (s : Finset γ) (t : γ → Finset α) (f : α → β) :
    (⨆ y ∈ s.bUnion t, f y) = ⨆ (x ∈ s) (y ∈ t x), f y := by simp [@supᵢ_comm _ α, supᵢ_and]
#align finset.supr_bUnion Finset.supr_bUnion

theorem infi_bUnion (s : Finset γ) (t : γ → Finset α) (f : α → β) :
    (⨅ y ∈ s.bUnion t, f y) = ⨅ (x ∈ s) (y ∈ t x), f y :=
  @supr_bUnion _ βᵒᵈ _ _ _ _ _ _
#align finset.infi_bUnion Finset.infi_bUnion

end Lattice

theorem set_bUnion_coe (s : Finset α) (t : α → Set β) : (⋃ x ∈ (↑s : Set α), t x) = ⋃ x ∈ s, t x :=
  rfl
#align finset.set_bUnion_coe Finset.set_bUnion_coe

theorem set_bInter_coe (s : Finset α) (t : α → Set β) : (⋂ x ∈ (↑s : Set α), t x) = ⋂ x ∈ s, t x :=
  rfl
#align finset.set_bInter_coe Finset.set_bInter_coe

theorem set_bUnion_singleton (a : α) (s : α → Set β) : (⋃ x ∈ ({a} : Finset α), s x) = s a :=
  supr_singleton a s
#align finset.set_bUnion_singleton Finset.set_bUnion_singleton

theorem set_bInter_singleton (a : α) (s : α → Set β) : (⋂ x ∈ ({a} : Finset α), s x) = s a :=
  infi_singleton a s
#align finset.set_bInter_singleton Finset.set_bInter_singleton

@[simp]
theorem set_bUnion_preimage_singleton (f : α → β) (s : Finset β) : (⋃ y ∈ s, f ⁻¹' {y}) = f ⁻¹' s :=
  Set.bunionᵢ_preimage_singleton f s
#align finset.set_bUnion_preimage_singleton Finset.set_bUnion_preimage_singleton

theorem set_bUnion_option_to_finset (o : Option α) (f : α → Set β) :
    (⋃ x ∈ o.toFinset, f x) = ⋃ x ∈ o, f x :=
  supr_option_to_finset o f
#align finset.set_bUnion_option_to_finset Finset.set_bUnion_option_to_finset

theorem set_bInter_option_to_finset (o : Option α) (f : α → Set β) :
    (⋂ x ∈ o.toFinset, f x) = ⋂ x ∈ o, f x :=
  infi_option_to_finset o f
#align finset.set_bInter_option_to_finset Finset.set_bInter_option_to_finset

theorem subset_set_bUnion_of_mem {s : Finset α} {f : α → Set β} {x : α} (h : x ∈ s) :
    f x ⊆ ⋃ y ∈ s, f y :=
  show f x ≤ ⨆ y ∈ s, f y from le_supᵢ_of_le x <| le_supᵢ _ h
#align finset.subset_set_bUnion_of_mem Finset.subset_set_bUnion_of_mem

variable [DecidableEq α]

theorem set_bUnion_union (s t : Finset α) (u : α → Set β) :
    (⋃ x ∈ s ∪ t, u x) = (⋃ x ∈ s, u x) ∪ ⋃ x ∈ t, u x :=
  supᵢ_union
#align finset.set_bUnion_union Finset.set_bUnion_union

theorem set_bInter_inter (s t : Finset α) (u : α → Set β) :
    (⋂ x ∈ s ∪ t, u x) = (⋂ x ∈ s, u x) ∩ ⋂ x ∈ t, u x :=
  infᵢ_union
#align finset.set_bInter_inter Finset.set_bInter_inter

theorem set_bUnion_insert (a : α) (s : Finset α) (t : α → Set β) :
    (⋃ x ∈ insert a s, t x) = t a ∪ ⋃ x ∈ s, t x :=
  supr_insert a s t
#align finset.set_bUnion_insert Finset.set_bUnion_insert

theorem set_bInter_insert (a : α) (s : Finset α) (t : α → Set β) :
    (⋂ x ∈ insert a s, t x) = t a ∩ ⋂ x ∈ s, t x :=
  infi_insert a s t
#align finset.set_bInter_insert Finset.set_bInter_insert

theorem set_bUnion_finset_image {f : γ → α} {g : α → Set β} {s : Finset γ} :
    (⋃ x ∈ s.image f, g x) = ⋃ y ∈ s, g (f y) :=
  supr_finset_image
#align finset.set_bUnion_finset_image Finset.set_bUnion_finset_image

theorem set_bInter_finset_image {f : γ → α} {g : α → Set β} {s : Finset γ} :
    (⋂ x ∈ s.image f, g x) = ⋂ y ∈ s, g (f y) :=
  infi_finset_image
#align finset.set_bInter_finset_image Finset.set_bInter_finset_image

theorem set_bUnion_insert_update {x : α} {t : Finset α} (f : α → Set β) {s : Set β} (hx : x ∉ t) :
    (⋃ i ∈ insert x t, @update _ _ _ f x s i) = s ∪ ⋃ i ∈ t, f i :=
  supr_insert_update f hx
#align finset.set_bUnion_insert_update Finset.set_bUnion_insert_update

theorem set_bInter_insert_update {x : α} {t : Finset α} (f : α → Set β) {s : Set β} (hx : x ∉ t) :
    (⋂ i ∈ insert x t, @update _ _ _ f x s i) = s ∩ ⋂ i ∈ t, f i :=
  infi_insert_update f hx
#align finset.set_bInter_insert_update Finset.set_bInter_insert_update

theorem set_bUnion_bUnion (s : Finset γ) (t : γ → Finset α) (f : α → Set β) :
    (⋃ y ∈ s.bUnion t, f y) = ⋃ (x ∈ s) (y ∈ t x), f y :=
  supr_bUnion s t f
#align finset.set_bUnion_bUnion Finset.set_bUnion_bUnion

theorem set_bInter_bUnion (s : Finset γ) (t : γ → Finset α) (f : α → Set β) :
    (⋂ y ∈ s.bUnion t, f y) = ⋂ (x ∈ s) (y ∈ t x), f y :=
  infi_bUnion s t f
#align finset.set_bInter_bUnion Finset.set_bInter_bUnion

end Finset

