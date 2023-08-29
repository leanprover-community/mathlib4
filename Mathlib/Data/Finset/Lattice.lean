/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Multiset.Lattice
import Mathlib.Order.CompleteLattice
import Mathlib.Order.Hom.Lattice

#align_import data.finset.lattice from "leanprover-community/mathlib"@"1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29"

/-!
# Lattice operations on finsets
-/

set_option autoImplicit true


variable {F α β γ ι κ : Type*}

namespace Finset

open Multiset OrderDual

/-! ### sup -/


section Sup

-- TODO: define with just `[Bot α]` where some lemmas hold without requiring `[OrderBot α]`
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
  Multiset.sup_singleton
#align finset.sup_singleton Finset.sup_singleton

theorem sup_union [DecidableEq β] : (s₁ ∪ s₂).sup f = s₁.sup f ⊔ s₂.sup f :=
  Finset.induction_on s₁
    (by rw [empty_union, sup_empty, bot_sup_eq])
        -- 🎉 no goals
    (fun a s _ ih => by rw [insert_union, sup_insert, sup_insert, ih, sup_assoc])
                        -- 🎉 no goals
#align finset.sup_union Finset.sup_union

theorem sup_sup : s.sup (f ⊔ g) = s.sup f ⊔ s.sup g := by
  refine' Finset.cons_induction_on s _ fun b t _ h => _
  -- ⊢ sup ∅ (f ⊔ g) = sup ∅ f ⊔ sup ∅ g
  · rw [sup_empty, sup_empty, sup_empty, bot_sup_eq]
    -- 🎉 no goals
  · rw [sup_cons, sup_cons, sup_cons, h]
    -- ⊢ (f ⊔ g) b ⊔ (sup t f ⊔ sup t g) = f b ⊔ sup t f ⊔ (g b ⊔ sup t g)
    exact sup_sup_sup_comm _ _ _ _
    -- 🎉 no goals
#align finset.sup_sup Finset.sup_sup

theorem sup_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) :
    s₁.sup f = s₂.sup g := by
  subst hs
  -- ⊢ sup s₁ f = sup s₁ g
  exact Finset.fold_congr hfg
  -- 🎉 no goals
#align finset.sup_congr Finset.sup_congr

@[simp]
theorem _root_.map_finset_sup [SemilatticeSup β] [OrderBot β] [SupBotHomClass F α β] (f : F)
    (s : Finset ι) (g : ι → α) : f (s.sup g) = s.sup (f ∘ g) :=
  Finset.cons_induction_on s (map_bot f) fun i s _ h => by
    rw [sup_cons, sup_cons, map_sup, h, Function.comp_apply]
    -- 🎉 no goals
#align map_finset_sup map_finset_sup

@[simp]
protected theorem sup_le_iff {a : α} : s.sup f ≤ a ↔ ∀ b ∈ s, f b ≤ a := by
  apply Iff.trans Multiset.sup_le
  -- ⊢ (∀ (b : α), b ∈ Multiset.map f s.val → b ≤ a) ↔ ∀ (b : β), b ∈ s → f b ≤ a
  simp only [Multiset.mem_map, and_imp, exists_imp]
  -- ⊢ (∀ (b : α) (x : β), x ∈ s.val → f x = b → b ≤ a) ↔ ∀ (b : β), b ∈ s → f b ≤ a
  exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩
  -- 🎉 no goals
#align finset.sup_le_iff Finset.sup_le_iff

alias ⟨_, sup_le⟩ := Finset.sup_le_iff
#align finset.sup_le Finset.sup_le

-- Porting note: removed `attribute [protected] sup_le`

theorem sup_const_le : (s.sup fun _ => a) ≤ a :=
  Finset.sup_le fun _ _ => le_rfl
#align finset.sup_const_le Finset.sup_const_le

theorem le_sup {b : β} (hb : b ∈ s) : f b ≤ s.sup f :=
  Finset.sup_le_iff.1 le_rfl _ hb
#align finset.le_sup Finset.le_sup

theorem le_sup_of_le {b : β} (hb : b ∈ s) (h : a ≤ f b) : a ≤ s.sup f := h.trans <| le_sup hb
#align finset.le_sup_of_le Finset.le_sup_of_le

@[simp]
theorem sup_biUnion [DecidableEq β] (s : Finset γ) (t : γ → Finset β) :
    (s.biUnion t).sup f = s.sup fun x => (t x).sup f :=
  eq_of_forall_ge_iff fun c => by simp [@forall_swap _ β]
                                  -- 🎉 no goals
#align finset.sup_bUnion Finset.sup_biUnion

theorem sup_const {s : Finset β} (h : s.Nonempty) (c : α) : (s.sup fun _ => c) = c :=
  eq_of_forall_ge_iff (fun _ => Finset.sup_le_iff.trans h.forall_const)
#align finset.sup_const Finset.sup_const

@[simp]
theorem sup_bot (s : Finset β) : (s.sup fun _ => ⊥) = (⊥ : α) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  -- ⊢ (sup ∅ fun x => ⊥) = ⊥
  · exact sup_empty
    -- 🎉 no goals
  · exact sup_const hs _
    -- 🎉 no goals
#align finset.sup_bot Finset.sup_bot

theorem sup_ite (p : β → Prop) [DecidablePred p] :
    (s.sup fun i => ite (p i) (f i) (g i)) = (s.filter p).sup f ⊔ (s.filter fun i => ¬p i).sup g :=
  fold_ite _
#align finset.sup_ite Finset.sup_ite

theorem sup_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ≤ g b) : s.sup f ≤ s.sup g :=
  Finset.sup_le fun b hb => le_trans (h b hb) (le_sup hb)
#align finset.sup_mono_fun Finset.sup_mono_fun

theorem sup_mono (h : s₁ ⊆ s₂) : s₁.sup f ≤ s₂.sup f :=
  Finset.sup_le (fun _ hb => le_sup (h hb))
#align finset.sup_mono Finset.sup_mono

protected theorem sup_comm (s : Finset β) (t : Finset γ) (f : β → γ → α) :
    (s.sup fun b => t.sup (f b)) = t.sup fun c => s.sup fun b => f b c := by
  refine' eq_of_forall_ge_iff fun a => _
  -- ⊢ (sup s fun b => sup t (f b)) ≤ a ↔ (sup t fun c => sup s fun b => f b c) ≤ a
  simp_rw [Finset.sup_le_iff]
  -- ⊢ (∀ (b : β), b ∈ s → ∀ (b_1 : γ), b_1 ∈ t → f b b_1 ≤ a) ↔ ∀ (b : γ), b ∈ t → …
  exact ⟨fun h c hc b hb => h b hb c hc, fun h b hb c hc => h c hc b hb⟩
  -- 🎉 no goals
#align finset.sup_comm Finset.sup_comm

@[simp, nolint simpNF] -- Porting note: linter claims that LHS does not simplify
theorem sup_attach (s : Finset β) (f : β → α) : (s.attach.sup fun x => f x) = s.sup f :=
  (s.attach.sup_map (Function.Embedding.subtype _) f).symm.trans <| congr_arg _ attach_map_val
#align finset.sup_attach Finset.sup_attach

/-- See also `Finset.product_biUnion`. -/
theorem sup_product_left (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).sup f = s.sup fun i => t.sup fun i' => f ⟨i, i'⟩ := by
  simp only [le_antisymm_iff, Finset.sup_le_iff, mem_product, and_imp, Prod.forall]
  -- ⊢ (∀ (a : β) (b : γ), a ∈ s → b ∈ t → f (a, b) ≤ sup s fun i => sup t fun i' = …
  -- Porting note: was one expression.
  refine ⟨fun b c hb hc => ?_, fun b hb c hc => ?_⟩
  -- ⊢ f (b, c) ≤ sup s fun i => sup t fun i' => f (i, i')
  · refine (le_sup hb).trans' ?_
    -- ⊢ f (b, c) ≤ sup t fun i' => f (b, i')
    exact @le_sup _ _ _ _ _ (fun c => f (b, c)) c hc
    -- 🎉 no goals
  · exact le_sup <| mem_product.2 ⟨hb, hc⟩
    -- 🎉 no goals
#align finset.sup_product_left Finset.sup_product_left

theorem sup_product_right (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).sup f = t.sup fun i' => s.sup fun i => f ⟨i, i'⟩ := by
  rw [sup_product_left, Finset.sup_comm]
  -- 🎉 no goals
#align finset.sup_product_right Finset.sup_product_right

@[simp]
theorem sup_erase_bot [DecidableEq α] (s : Finset α) : (s.erase ⊥).sup id = s.sup id := by
  refine' (sup_mono (s.erase_subset _)).antisymm (Finset.sup_le_iff.2 fun a ha => _)
  -- ⊢ id a ≤ sup (erase s ⊥) id
  obtain rfl | ha' := eq_or_ne a ⊥
  -- ⊢ id ⊥ ≤ sup (erase s ⊥) id
  · exact bot_le
    -- 🎉 no goals
  · exact le_sup (mem_erase.2 ⟨ha', ha⟩)
    -- 🎉 no goals
#align finset.sup_erase_bot Finset.sup_erase_bot

theorem sup_sdiff_right {α β : Type*} [GeneralizedBooleanAlgebra α] (s : Finset β) (f : β → α)
    (a : α) : (s.sup fun b => f b \ a) = s.sup f \ a := by
  refine' Finset.cons_induction_on s _ fun b t _ h => _
  -- ⊢ (sup ∅ fun b => f b \ a) = sup ∅ f \ a
  · rw [sup_empty, sup_empty, bot_sdiff]
    -- 🎉 no goals
  · rw [sup_cons, sup_cons, h, sup_sdiff]
    -- 🎉 no goals
#align finset.sup_sdiff_right Finset.sup_sdiff_right

theorem comp_sup_eq_sup_comp [SemilatticeSup γ] [OrderBot γ] {s : Finset β} {f : β → α} (g : α → γ)
    (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
  Finset.cons_induction_on s bot fun c t hc ih => by
    rw [sup_cons, sup_cons, g_sup, ih, Function.comp_apply]
    -- 🎉 no goals
#align finset.comp_sup_eq_sup_comp Finset.comp_sup_eq_sup_comp

/-- Computing `sup` in a subtype (closed under `sup`) is the same as computing it in `α`. -/
theorem sup_coe {P : α → Prop} {Pbot : P ⊥} {Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)} (t : Finset β)
    (f : β → { x : α // P x }) :
    (@sup { x // P x } _ (Subtype.semilatticeSup Psup) (Subtype.orderBot Pbot) t f : α) =
      t.sup fun x => ↑(f x) := by
  letI := Subtype.semilatticeSup Psup
  -- ⊢ ↑(sup t f) = sup t fun x => ↑(f x)
  letI := Subtype.orderBot Pbot
  -- ⊢ ↑(sup t f) = sup t fun x => ↑(f x)
  apply comp_sup_eq_sup_comp Subtype.val <;> intros <;> rfl
  -- ⊢ ∀ (x y : { x // P x }), ↑(x ⊔ y) = ↑x ⊔ ↑y
                                             -- ⊢ ↑(x✝ ⊔ y✝) = ↑x✝ ⊔ ↑y✝
                                             -- ⊢ ↑⊥ = ⊥
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
#align finset.sup_coe Finset.sup_coe

@[simp]
theorem sup_toFinset {α β} [DecidableEq β] (s : Finset α) (f : α → Multiset β) :
    (s.sup f).toFinset = s.sup fun x => (f x).toFinset :=
  comp_sup_eq_sup_comp Multiset.toFinset toFinset_union rfl
#align finset.sup_to_finset Finset.sup_toFinset

theorem _root_.List.foldr_sup_eq_sup_toFinset [DecidableEq α] (l : List α) :
    l.foldr (· ⊔ ·) ⊥ = l.toFinset.sup id := by
  rw [← coe_fold_r, ← Multiset.fold_dedup_idem, sup_def, ← List.toFinset_coe, toFinset_val,
    Multiset.map_id]
  rfl
  -- 🎉 no goals
#align list.foldr_sup_eq_sup_to_finset List.foldr_sup_eq_sup_toFinset

theorem subset_range_sup_succ (s : Finset ℕ) : s ⊆ range (s.sup id).succ := fun _ hn =>
  mem_range.2 <| Nat.lt_succ_of_le <| @le_sup _ _ _ _ _ id _ hn
#align finset.subset_range_sup_succ Finset.subset_range_sup_succ

theorem exists_nat_subset_range (s : Finset ℕ) : ∃ n : ℕ, s ⊆ range n :=
  ⟨_, s.subset_range_sup_succ⟩
#align finset.exists_nat_subset_range Finset.exists_nat_subset_range

theorem sup_induction {p : α → Prop} (hb : p ⊥) (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊔ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.sup f) := by
  induction' s using Finset.cons_induction with c s hc ih
  -- ⊢ p (sup ∅ f)
  · exact hb
    -- 🎉 no goals
  · rw [sup_cons]
    -- ⊢ p (f c ⊔ sup s f)
    apply hp
    -- ⊢ p (f c)
    · exact hs c (mem_cons.2 (Or.inl rfl))
      -- 🎉 no goals
    · exact ih fun b h => hs b (mem_cons.2 (Or.inr h))
      -- 🎉 no goals
#align finset.sup_induction Finset.sup_induction

theorem sup_le_of_le_directed {α : Type*} [SemilatticeSup α] [OrderBot α] (s : Set α)
    (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) (t : Finset α) :
    (∀ x ∈ t, ∃ y ∈ s, x ≤ y) → ∃ x, x ∈ s ∧ t.sup id ≤ x := by
  classical
    induction' t using Finset.induction_on with a r _ ih h
    · simpa only [forall_prop_of_true, and_true_iff, forall_prop_of_false, bot_le, not_false_iff,
        sup_empty, forall_true_iff, not_mem_empty]
    · intro h
      have incs : (r : Set α) ⊆ ↑(insert a r) := by
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

-- If we acquire sublattices
-- the hypotheses should be reformulated as `s : SubsemilatticeSupBot`
theorem sup_mem (s : Set α) (w₁ : ⊥ ∈ s) (w₂ : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), x ⊔ y ∈ s)
    {ι : Type*} (t : Finset ι) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.sup p ∈ s :=
  @sup_induction _ _ _ _ _ _ (· ∈ s) w₁ w₂ h
#align finset.sup_mem Finset.sup_mem

@[simp]
protected theorem sup_eq_bot_iff (f : β → α) (S : Finset β) : S.sup f = ⊥ ↔ ∀ s ∈ S, f s = ⊥ := by
  classical induction' S using Finset.induction with a S _ hi <;> simp [*]
  -- 🎉 no goals
#align finset.sup_eq_bot_iff Finset.sup_eq_bot_iff

end Sup

theorem sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : α → β) : s.sup f = ⨆ a ∈ s, f a :=
  le_antisymm
    (Finset.sup_le (fun a ha => le_iSup_of_le a <| le_iSup (fun _ => f a) ha))
    (iSup_le fun _ => iSup_le fun ha => le_sup ha)
#align finset.sup_eq_supr Finset.sup_eq_iSup

theorem sup_id_eq_sSup [CompleteLattice α] (s : Finset α) : s.sup id = sSup s := by
  simp [sSup_eq_iSup, sup_eq_iSup]
  -- 🎉 no goals
#align finset.sup_id_eq_Sup Finset.sup_id_eq_sSup

theorem sup_id_set_eq_sUnion (s : Finset (Set α)) : s.sup id = ⋃₀ ↑s :=
  sup_id_eq_sSup _
#align finset.sup_id_set_eq_sUnion Finset.sup_id_set_eq_sUnion

@[simp]
theorem sup_set_eq_biUnion (s : Finset α) (f : α → Set β) : s.sup f = ⋃ x ∈ s, f x :=
  sup_eq_iSup _ _
#align finset.sup_set_eq_bUnion Finset.sup_set_eq_biUnion

theorem sup_eq_sSup_image [CompleteLattice β] (s : Finset α) (f : α → β) :
    s.sup f = sSup (f '' s) :=
  by classical rw [← Finset.coe_image, ← sup_id_eq_sSup, sup_image, Function.comp.left_id]
     -- 🎉 no goals
#align finset.sup_eq_Sup_image Finset.sup_eq_sSup_image

/-! ### inf -/


section Inf

-- TODO: define with just `[Top α]` where some lemmas hold without requiring `[OrderTop α]`
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
  Multiset.inf_singleton
#align finset.inf_singleton Finset.inf_singleton

theorem inf_union [DecidableEq β] : (s₁ ∪ s₂).inf f = s₁.inf f ⊓ s₂.inf f :=
  @sup_union αᵒᵈ _ _ _ _ _ _ _
#align finset.inf_union Finset.inf_union

theorem inf_inf : s.inf (f ⊓ g) = s.inf f ⊓ s.inf g :=
  @sup_sup αᵒᵈ _ _ _ _ _ _
#align finset.inf_inf Finset.inf_inf

theorem inf_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) :
    s₁.inf f = s₂.inf g := by
  subst hs
  -- ⊢ inf s₁ f = inf s₁ g
  exact Finset.fold_congr hfg
  -- 🎉 no goals
#align finset.inf_congr Finset.inf_congr

@[simp]
theorem _root_.map_finset_inf [SemilatticeInf β] [OrderTop β] [InfTopHomClass F α β] (f : F)
    (s : Finset ι) (g : ι → α) : f (s.inf g) = s.inf (f ∘ g) :=
  Finset.cons_induction_on s (map_top f) fun i s _ h => by
    rw [inf_cons, inf_cons, map_inf, h, Function.comp_apply]
    -- 🎉 no goals
#align map_finset_inf map_finset_inf

@[simp]
theorem inf_biUnion [DecidableEq β] (s : Finset γ) (t : γ → Finset β) :
    (s.biUnion t).inf f = s.inf fun x => (t x).inf f :=
  @sup_biUnion αᵒᵈ _ _ _ _ _ _ _ _
#align finset.inf_bUnion Finset.inf_biUnion

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

alias ⟨_, le_inf⟩ := Finset.le_inf_iff
#align finset.le_inf Finset.le_inf

-- Porting note: removed attribute [protected] le_inf

theorem le_inf_const_le : a ≤ s.inf fun _ => a :=
  Finset.le_inf fun _ _ => le_rfl
#align finset.le_inf_const_le Finset.le_inf_const_le

theorem inf_le {b : β} (hb : b ∈ s) : s.inf f ≤ f b :=
  Finset.le_inf_iff.1 le_rfl _ hb
#align finset.inf_le Finset.inf_le

theorem inf_le_of_le {b : β} (hb : b ∈ s) (h : f b ≤ a) : s.inf f ≤ a := (inf_le hb).trans h
#align finset.inf_le_of_le Finset.inf_le_of_le

theorem inf_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ≤ g b) : s.inf f ≤ s.inf g :=
  Finset.le_inf fun b hb => le_trans (inf_le hb) (h b hb)
#align finset.inf_mono_fun Finset.inf_mono_fun

theorem inf_mono (h : s₁ ⊆ s₂) : s₂.inf f ≤ s₁.inf f :=
  Finset.le_inf (fun _ hb => inf_le (h hb))
#align finset.inf_mono Finset.inf_mono

theorem inf_attach (s : Finset β) (f : β → α) : (s.attach.inf fun x => f x) = s.inf f :=
  @sup_attach αᵒᵈ _ _ _ _ _
#align finset.inf_attach Finset.inf_attach

protected theorem inf_comm (s : Finset β) (t : Finset γ) (f : β → γ → α) :
    (s.inf fun b => t.inf (f b)) = t.inf fun c => s.inf fun b => f b c :=
  @Finset.sup_comm αᵒᵈ _ _ _ _ _ _ _
#align finset.inf_comm Finset.inf_comm

theorem inf_product_left (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).inf f = s.inf fun i => t.inf fun i' => f ⟨i, i'⟩ :=
  @sup_product_left αᵒᵈ _ _ _ _ _ _ _
#align finset.inf_product_left Finset.inf_product_left

theorem inf_product_right (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).inf f = t.inf fun i' => s.inf fun i => f ⟨i, i'⟩ :=
  @sup_product_right αᵒᵈ _ _ _ _ _ _ _
#align finset.inf_product_right Finset.inf_product_right

@[simp]
theorem inf_erase_top [DecidableEq α] (s : Finset α) : (s.erase ⊤).inf id = s.inf id :=
  @sup_erase_bot αᵒᵈ _ _ _ _
#align finset.inf_erase_top Finset.inf_erase_top

theorem comp_inf_eq_inf_comp [SemilatticeInf γ] [OrderTop γ] {s : Finset β} {f : β → α} (g : α → γ)
    (g_inf : ∀ x y, g (x ⊓ y) = g x ⊓ g y) (top : g ⊤ = ⊤) : g (s.inf f) = s.inf (g ∘ f) :=
  @comp_sup_eq_sup_comp αᵒᵈ _ γᵒᵈ _ _ _ _ _ _ _ g_inf top
#align finset.comp_inf_eq_inf_comp Finset.comp_inf_eq_inf_comp

/-- Computing `inf` in a subtype (closed under `inf`) is the same as computing it in `α`. -/
theorem inf_coe {P : α → Prop} {Ptop : P ⊤} {Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)} (t : Finset β)
    (f : β → { x : α // P x }) :
    (@inf { x // P x } _ (Subtype.semilatticeInf Pinf) (Subtype.orderTop Ptop) t f : α) =
      t.inf fun x => ↑(f x) :=
  @sup_coe αᵒᵈ _ _ _ _ Ptop Pinf t f
#align finset.inf_coe Finset.inf_coe

theorem _root_.List.foldr_inf_eq_inf_toFinset [DecidableEq α] (l : List α) :
    l.foldr (· ⊓ ·) ⊤ = l.toFinset.inf id := by
  rw [← coe_fold_r, ← Multiset.fold_dedup_idem, inf_def, ← List.toFinset_coe, toFinset_val,
    Multiset.map_id]
  rfl
  -- 🎉 no goals
#align list.foldr_inf_eq_inf_to_finset List.foldr_inf_eq_inf_toFinset

theorem inf_induction {p : α → Prop} (ht : p ⊤) (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊓ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.inf f) :=
  @sup_induction αᵒᵈ _ _ _ _ _ _ ht hp hs
#align finset.inf_induction Finset.inf_induction

theorem inf_mem (s : Set α) (w₁ : ⊤ ∈ s) (w₂ : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), x ⊓ y ∈ s)
    {ι : Type*} (t : Finset ι) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.inf p ∈ s :=
  @inf_induction _ _ _ _ _ _ (· ∈ s) w₁ w₂ h
#align finset.inf_mem Finset.inf_mem

@[simp]
protected theorem inf_eq_top_iff (f : β → α) (S : Finset β) : S.inf f = ⊤ ↔ ∀ s ∈ S, f s = ⊤ :=
  @Finset.sup_eq_bot_iff αᵒᵈ _ _ _ _ _
#align finset.inf_eq_top_iff Finset.inf_eq_top_iff

end Inf

@[simp]
theorem toDual_sup [SemilatticeSup α] [OrderBot α] (s : Finset β) (f : β → α) :
    toDual (s.sup f) = s.inf (toDual ∘ f) :=
  rfl
#align finset.to_dual_sup Finset.toDual_sup

@[simp]
theorem toDual_inf [SemilatticeInf α] [OrderTop α] (s : Finset β) (f : β → α) :
    toDual (s.inf f) = s.sup (toDual ∘ f) :=
  rfl
#align finset.to_dual_inf Finset.toDual_inf

@[simp]
theorem ofDual_sup [SemilatticeInf α] [OrderTop α] (s : Finset β) (f : β → αᵒᵈ) :
    ofDual (s.sup f) = s.inf (ofDual ∘ f) :=
  rfl
#align finset.of_dual_sup Finset.ofDual_sup

@[simp]
theorem ofDual_inf [SemilatticeSup α] [OrderBot α] (s : Finset β) (f : β → αᵒᵈ) :
    ofDual (s.inf f) = s.sup (ofDual ∘ f) :=
  rfl
#align finset.of_dual_inf Finset.ofDual_inf

section DistribLattice

variable [DistribLattice α]

section OrderBot

variable [OrderBot α] {s : Finset ι} {t : Finset κ} {f : ι → α} {g : κ → α} {a : α}

theorem sup_inf_distrib_left (s : Finset ι) (f : ι → α) (a : α) :
    a ⊓ s.sup f = s.sup fun i => a ⊓ f i := by
  induction' s using Finset.cons_induction with i s hi h
  -- ⊢ a ⊓ sup ∅ f = sup ∅ fun i => a ⊓ f i
  · simp_rw [Finset.sup_empty, inf_bot_eq]
    -- 🎉 no goals
  · rw [sup_cons, sup_cons, inf_sup_left, h]
    -- 🎉 no goals
#align finset.sup_inf_distrib_left Finset.sup_inf_distrib_left

theorem sup_inf_distrib_right (s : Finset ι) (f : ι → α) (a : α) :
    s.sup f ⊓ a = s.sup fun i => f i ⊓ a := by
  rw [_root_.inf_comm, s.sup_inf_distrib_left]
  -- ⊢ (sup s fun i => a ⊓ f i) = sup s fun i => f i ⊓ a
  simp_rw [_root_.inf_comm]
  -- 🎉 no goals
#align finset.sup_inf_distrib_right Finset.sup_inf_distrib_right

protected theorem disjoint_sup_right : Disjoint a (s.sup f) ↔ ∀ ⦃i⦄, i ∈ s → Disjoint a (f i) := by
  simp only [disjoint_iff, sup_inf_distrib_left, Finset.sup_eq_bot_iff]
  -- 🎉 no goals
#align finset.disjoint_sup_right Finset.disjoint_sup_right

protected theorem disjoint_sup_left : Disjoint (s.sup f) a ↔ ∀ ⦃i⦄, i ∈ s → Disjoint (f i) a := by
  simp only [disjoint_iff, sup_inf_distrib_right, Finset.sup_eq_bot_iff]
  -- 🎉 no goals
#align finset.disjoint_sup_left Finset.disjoint_sup_left

theorem sup_inf_sup (s : Finset ι) (t : Finset κ) (f : ι → α) (g : κ → α) :
    s.sup f ⊓ t.sup g = (s ×ˢ t).sup fun i => f i.1 ⊓ g i.2 := by
  simp_rw [Finset.sup_inf_distrib_right, Finset.sup_inf_distrib_left, sup_product_left]
  -- 🎉 no goals
#align finset.sup_inf_sup Finset.sup_inf_sup

end OrderBot

section OrderTop

variable [OrderTop α] {f : ι → α} {g : κ → α} {s : Finset ι} {t : Finset κ} {a : α}

theorem inf_sup_distrib_left (s : Finset ι) (f : ι → α) (a : α) :
    a ⊔ s.inf f = s.inf fun i => a ⊔ f i :=
  @sup_inf_distrib_left αᵒᵈ _ _ _ _ _ _
#align finset.inf_sup_distrib_left Finset.inf_sup_distrib_left

theorem inf_sup_distrib_right (s : Finset ι) (f : ι → α) (a : α) :
    s.inf f ⊔ a = s.inf fun i => f i ⊔ a :=
  @sup_inf_distrib_right αᵒᵈ _ _ _ _ _ _
#align finset.inf_sup_distrib_right Finset.inf_sup_distrib_right

protected theorem codisjoint_inf_right :
    Codisjoint a (s.inf f) ↔ ∀ ⦃i⦄, i ∈ s → Codisjoint a (f i) :=
  @Finset.disjoint_sup_right αᵒᵈ _ _ _ _ _ _
#align finset.codisjoint_inf_right Finset.codisjoint_inf_right

protected theorem codisjoint_inf_left :
    Codisjoint (s.inf f) a ↔ ∀ ⦃i⦄, i ∈ s → Codisjoint (f i) a :=
  @Finset.disjoint_sup_left αᵒᵈ _ _ _ _ _ _
#align finset.codisjoint_inf_left Finset.codisjoint_inf_left

theorem inf_sup_inf (s : Finset ι) (t : Finset κ) (f : ι → α) (g : κ → α) :
    s.inf f ⊔ t.inf g = (s ×ˢ t).inf fun i => f i.1 ⊔ g i.2 :=
  @sup_inf_sup αᵒᵈ _ _ _ _ _ _ _ _
#align finset.inf_sup_inf Finset.inf_sup_inf

end OrderTop

section BoundedOrder

variable [BoundedOrder α] [DecidableEq ι]

--TODO: Extract out the obvious isomorphism `(insert i s).pi t ≃ t i ×ˢ s.pi t` from this proof
theorem inf_sup {κ : ι → Type*} (s : Finset ι) (t : ∀ i, Finset (κ i)) (f : ∀ i, κ i → α) :
    (s.inf fun i => (t i).sup (f i)) =
      (s.pi t).sup fun g => s.attach.inf fun i => f _ <| g _ i.2 := by
  induction' s using Finset.induction with i s hi ih
  -- ⊢ (inf ∅ fun i => sup (t i) (f i)) = sup (pi ∅ t) fun g => inf (attach ∅) fun  …
  · simp
    -- 🎉 no goals
  rw [inf_insert, ih, attach_insert, sup_inf_sup]
  -- ⊢ (sup (t i ×ˢ pi s t) fun i_1 => f i i_1.fst ⊓ inf (attach s) fun i_2 => f (↑ …
  refine' eq_of_forall_ge_iff fun c => _
  -- ⊢ (sup (t i ×ˢ pi s t) fun i_1 => f i i_1.fst ⊓ inf (attach s) fun i_2 => f (↑ …
  simp only [Finset.sup_le_iff, mem_product, mem_pi, and_imp, Prod.forall,
    inf_insert, inf_image]
  refine'
    ⟨fun h g hg =>
      h (g i <| mem_insert_self _ _) (fun j hj => g j <| mem_insert_of_mem hj)
        (hg _ <| mem_insert_self _ _) fun j hj => hg _ <| mem_insert_of_mem hj,
      fun h a g ha hg => _⟩
  -- TODO: This `have` must be named to prevent it being shadowed by the internal `this` in `simpa`
  have aux : ∀ j : { x // x ∈ s }, ↑j ≠ i := fun j : s => ne_of_mem_of_not_mem j.2 hi
  -- ⊢ (f i a ⊓ inf (attach s) fun i => f (↑i) (g ↑i (_ : ↑i ∈ s))) ≤ c
  -- porting note: `simpa` doesn't support placeholders in proof terms
  have := h (fun j hj => if hji : j = i then cast (congr_arg κ hji.symm) a
      else g _ <| mem_of_mem_insert_of_ne hj hji) (fun j hj => ?_)
  simpa only [cast_eq, dif_pos, Function.comp, Subtype.coe_mk, dif_neg, aux] using this
  -- ⊢ (fun j hj => if hji : j = i then cast (_ : κ i = κ j) a else g j (_ : j ∈ s) …
  rw [mem_insert] at hj
  -- ⊢ (fun j hj => if hji : j = i then cast (_ : κ i = κ j) a else g j (_ : j ∈ s) …
  obtain (rfl | hj) := hj
  -- ⊢ (fun j_1 hj => if hji : j_1 = j then cast (_ : κ j = κ j_1) a else g j_1 (_  …
  · simpa
    -- 🎉 no goals
  · simpa [ne_of_mem_of_not_mem hj hi] using hg _ _
    -- 🎉 no goals
#align finset.inf_sup Finset.inf_sup

theorem sup_inf {κ : ι → Type*} (s : Finset ι) (t : ∀ i, Finset (κ i)) (f : ∀ i, κ i → α) :
    (s.sup fun i => (t i).inf (f i)) = (s.pi t).inf fun g => s.attach.sup fun i => f _ <| g _ i.2 :=
  @inf_sup αᵒᵈ _ _ _ _ _ _ _ _
#align finset.sup_inf Finset.sup_inf

end BoundedOrder

end DistribLattice

section BooleanAlgebra

variable [BooleanAlgebra α] {s : Finset ι}

theorem sup_sdiff_left (s : Finset ι) (f : ι → α) (a : α) :
    (s.sup fun b => a \ f b) = a \ s.inf f := by
  refine' Finset.cons_induction_on s _ fun b t _ h => _
  -- ⊢ (sup ∅ fun b => a \ f b) = a \ inf ∅ f
  · rw [sup_empty, inf_empty, sdiff_top]
    -- 🎉 no goals
  · rw [sup_cons, inf_cons, h, sdiff_inf]
    -- 🎉 no goals
#align finset.sup_sdiff_left Finset.sup_sdiff_left

theorem inf_sdiff_left (hs : s.Nonempty) (f : ι → α) (a : α) :
    (s.inf fun b => a \ f b) = a \ s.sup f := by
  induction' hs using Finset.Nonempty.cons_induction with b b t _ _ h
  -- ⊢ (inf {b} fun b => a \ f b) = a \ sup {b} f
  · rw [sup_singleton, inf_singleton]
    -- 🎉 no goals
  · rw [sup_cons, inf_cons, h, sdiff_sup]
    -- 🎉 no goals
#align finset.inf_sdiff_left Finset.inf_sdiff_left

theorem inf_sdiff_right (hs : s.Nonempty) (f : ι → α) (a : α) :
    (s.inf fun b => f b \ a) = s.inf f \ a := by
  induction' hs using Finset.Nonempty.cons_induction with b b t _ _ h
  -- ⊢ (inf {b} fun b => f b \ a) = inf {b} f \ a
  · rw [inf_singleton, inf_singleton]
    -- 🎉 no goals
  · rw [inf_cons, inf_cons, h, inf_sdiff]
    -- 🎉 no goals
#align finset.inf_sdiff_right Finset.inf_sdiff_right

theorem inf_himp_right (s : Finset ι) (f : ι → α) (a : α) :
    (s.inf fun b => f b ⇨ a) = s.sup f ⇨ a :=
  @sup_sdiff_left αᵒᵈ _ _ _ _ _
#align finset.inf_himp_right Finset.inf_himp_right

theorem sup_himp_right (hs : s.Nonempty) (f : ι → α) (a : α) :
    (s.sup fun b => f b ⇨ a) = s.inf f ⇨ a :=
  @inf_sdiff_left αᵒᵈ _ _ _ hs _ _
#align finset.sup_himp_right Finset.sup_himp_right

theorem sup_himp_left (hs : s.Nonempty) (f : ι → α) (a : α) :
    (s.sup fun b => a ⇨ f b) = a ⇨ s.sup f :=
  @inf_sdiff_right αᵒᵈ _ _ _ hs _ _
#align finset.sup_himp_left Finset.sup_himp_left

@[simp]
protected theorem compl_sup (s : Finset ι) (f : ι → α) : (s.sup f)ᶜ = s.inf fun i => (f i)ᶜ :=
  map_finset_sup (OrderIso.compl α) _ _
#align finset.compl_sup Finset.compl_sup

@[simp]
protected theorem compl_inf (s : Finset ι) (f : ι → α) : (s.inf f)ᶜ = s.sup fun i => (f i)ᶜ :=
  map_finset_inf (OrderIso.compl α) _ _
#align finset.compl_inf Finset.compl_inf

end BooleanAlgebra

section LinearOrder

variable [LinearOrder α]

section OrderBot

variable [OrderBot α] {s : Finset ι} {f : ι → α} {a : α}

theorem comp_sup_eq_sup_comp_of_is_total [SemilatticeSup β] [OrderBot β] (g : α → β)
    (mono_g : Monotone g) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
  comp_sup_eq_sup_comp g mono_g.map_sup bot
#align finset.comp_sup_eq_sup_comp_of_is_total Finset.comp_sup_eq_sup_comp_of_is_total

@[simp]
protected theorem le_sup_iff (ha : ⊥ < a) : a ≤ s.sup f ↔ ∃ b ∈ s, a ≤ f b := by
  apply Iff.intro
  -- ⊢ a ≤ sup s f → ∃ b, b ∈ s ∧ a ≤ f b
  · induction s using cons_induction with
    | empty => exact (absurd · (not_le_of_lt ha))
    | @cons c t hc ih =>
      rw [sup_cons, le_sup_iff]
      exact fun
      | Or.inl h => ⟨c, mem_cons.2 (Or.inl rfl), h⟩
      | Or.inr h => let ⟨b, hb, hle⟩ := ih h; ⟨b, mem_cons.2 (Or.inr hb), hle⟩
  · exact fun ⟨b, hb, hle⟩ => le_trans hle (le_sup hb)
    -- 🎉 no goals
#align finset.le_sup_iff Finset.le_sup_iff

@[simp]
protected theorem lt_sup_iff : a < s.sup f ↔ ∃ b ∈ s, a < f b := by
  apply Iff.intro
  -- ⊢ a < sup s f → ∃ b, b ∈ s ∧ a < f b
  · induction s using cons_induction with
    | empty => exact (absurd · not_lt_bot)
    | @cons c t hc ih =>
      rw [sup_cons, lt_sup_iff]
      exact fun
      | Or.inl h => ⟨c, mem_cons.2 (Or.inl rfl), h⟩
      | Or.inr h => let ⟨b, hb, hlt⟩ := ih h; ⟨b, mem_cons.2 (Or.inr hb), hlt⟩
  · exact fun ⟨b, hb, hlt⟩ => lt_of_lt_of_le hlt (le_sup hb)
    -- 🎉 no goals
#align finset.lt_sup_iff Finset.lt_sup_iff

@[simp]
protected theorem sup_lt_iff (ha : ⊥ < a) : s.sup f < a ↔ ∀ b ∈ s, f b < a :=
  ⟨fun hs b hb => lt_of_le_of_lt (le_sup hb) hs,
    Finset.cons_induction_on s (fun _ => ha) fun c t hc => by
      simpa only [sup_cons, sup_lt_iff, mem_cons, forall_eq_or_imp] using And.imp_right⟩
      -- 🎉 no goals
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

theorem inf_eq_iInf [CompleteLattice β] (s : Finset α) (f : α → β) : s.inf f = ⨅ a ∈ s, f a :=
  @sup_eq_iSup _ βᵒᵈ _ _ _
#align finset.inf_eq_infi Finset.inf_eq_iInf

theorem inf_id_eq_sInf [CompleteLattice α] (s : Finset α) : s.inf id = sInf s :=
  @sup_id_eq_sSup αᵒᵈ _ _
#align finset.inf_id_eq_Inf Finset.inf_id_eq_sInf

theorem inf_id_set_eq_sInter (s : Finset (Set α)) : s.inf id = ⋂₀ ↑s :=
  inf_id_eq_sInf _
#align finset.inf_id_set_eq_sInter Finset.inf_id_set_eq_sInter

@[simp]
theorem inf_set_eq_iInter (s : Finset α) (f : α → Set β) : s.inf f = ⋂ x ∈ s, f x :=
  inf_eq_iInf _ _
#align finset.inf_set_eq_bInter Finset.inf_set_eq_iInter

theorem inf_eq_sInf_image [CompleteLattice β] (s : Finset α) (f : α → β) :
    s.inf f = sInf (f '' s) :=
  @sup_eq_sSup_image _ βᵒᵈ _ _ _
#align finset.inf_eq_Inf_image Finset.inf_eq_sInf_image

section Sup'

variable [SemilatticeSup α]

theorem sup_of_mem {s : Finset β} (f : β → α) {b : β} (h : b ∈ s) :
    ∃ a : α, s.sup ((↑) ∘ f : β → WithBot α) = ↑a :=
  Exists.imp (fun _ => And.left) (@le_sup (WithBot α) _ _ _ _ _ _ h (f b) rfl)
#align finset.sup_of_mem Finset.sup_of_mem

/-- Given nonempty finset `s` then `s.sup' H f` is the supremum of its image under `f` in (possibly
unbounded) join-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a bottom element
you may instead use `Finset.sup` which does not require `s` nonempty. -/
def sup' (s : Finset β) (H : s.Nonempty) (f : β → α) : α :=
  WithBot.unbot (s.sup ((↑) ∘ f)) (by simpa using H)
                                      -- 🎉 no goals
#align finset.sup' Finset.sup'

variable {s : Finset β} (H : s.Nonempty) (f : β → α)

@[simp]
theorem coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) ∘ f) := by
  rw [sup', WithBot.coe_unbot]
  -- 🎉 no goals
#align finset.coe_sup' Finset.coe_sup'

@[simp]
theorem sup'_cons {b : β} {hb : b ∉ s} {h : (cons b s hb).Nonempty} :
    (cons b s hb).sup' h f = f b ⊔ s.sup' H f := by
  rw [← WithBot.coe_eq_coe]
  -- ⊢ ↑(sup' (cons b s hb) h f) = ↑(f b ⊔ sup' s H f)
  simp [WithBot.coe_sup]
  -- 🎉 no goals
#align finset.sup'_cons Finset.sup'_cons

@[simp]
theorem sup'_insert [DecidableEq β] {b : β} {h : (insert b s).Nonempty} :
    (insert b s).sup' h f = f b ⊔ s.sup' H f := by
  rw [← WithBot.coe_eq_coe]
  -- ⊢ ↑(sup' (insert b s) h f) = ↑(f b ⊔ sup' s H f)
  simp [WithBot.coe_sup]
  -- 🎉 no goals
#align finset.sup'_insert Finset.sup'_insert

@[simp]
theorem sup'_singleton {b : β} {h : ({b} : Finset β).Nonempty} : ({b} : Finset β).sup' h f = f b :=
  rfl
#align finset.sup'_singleton Finset.sup'_singleton

theorem sup'_le {a : α} (hs : ∀ b ∈ s, f b ≤ a) : s.sup' H f ≤ a := by
  rw [← WithBot.coe_le_coe, coe_sup']
  -- ⊢ sup s (WithBot.some ∘ f) ≤ ↑a
  exact Finset.sup_le fun b h => WithBot.coe_le_coe.2 <| hs b h
  -- 🎉 no goals
#align finset.sup'_le Finset.sup'_le

theorem le_sup' {b : β} (h : b ∈ s) : f b ≤ s.sup' ⟨b, h⟩ f := by
  rw [← WithBot.coe_le_coe, coe_sup']
  -- ⊢ ↑(f b) ≤ sup s (WithBot.some ∘ f)
  exact le_sup (f := fun c => WithBot.some (f c)) h
  -- 🎉 no goals
#align finset.le_sup' Finset.le_sup'

theorem le_sup'_of_le {a : α} {b : β} (hb : b ∈ s) (h : a ≤ f b) : a ≤ s.sup' ⟨b, hb⟩ f :=
  h.trans <| le_sup' _ hb
#align finset.le_sup'_of_le Finset.le_sup'_of_le

@[simp]
theorem sup'_const (a : α) : s.sup' H (fun _ => a) = a := by
  apply le_antisymm
  -- ⊢ (sup' s H fun x => a) ≤ a
  · apply sup'_le
    -- ⊢ ∀ (b : β), b ∈ s → a ≤ a
    intros
    -- ⊢ a ≤ a
    exact le_rfl
    -- 🎉 no goals
  · apply le_sup' (fun _ => a) H.choose_spec
    -- 🎉 no goals
#align finset.sup'_const Finset.sup'_const

@[simp]
theorem sup'_le_iff {a : α} : s.sup' H f ≤ a ↔ ∀ b ∈ s, f b ≤ a :=
  Iff.intro (fun h _ hb => le_trans (le_sup' f hb) h) (sup'_le H f)
#align finset.sup'_le_iff Finset.sup'_le_iff

theorem sup'_biUnion [DecidableEq β] {s : Finset γ} (Hs : s.Nonempty) {t : γ → Finset β}
    (Ht : ∀ b, (t b).Nonempty) :
    (s.biUnion t).sup' (Hs.biUnion fun b _ => Ht b) f = s.sup' Hs (fun b => (t b).sup' (Ht b) f) :=
  eq_of_forall_ge_iff fun c => by simp [@forall_swap _ β]
                                  -- 🎉 no goals
#align finset.sup'_bUnion Finset.sup'_biUnion

theorem comp_sup'_eq_sup'_comp [SemilatticeSup γ] {s : Finset β} (H : s.Nonempty) {f : β → α}
    (g : α → γ) (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) : g (s.sup' H f) = s.sup' H (g ∘ f) := by
  rw [← WithBot.coe_eq_coe, coe_sup']
  -- ⊢ ↑(g (sup' s H f)) = sup s (WithBot.some ∘ g ∘ f)
  let g' := WithBot.map g
  -- ⊢ ↑(g (sup' s H f)) = sup s (WithBot.some ∘ g ∘ f)
  show g' ↑(s.sup' H f) = s.sup fun a => g' ↑(f a)
  -- ⊢ g' ↑(sup' s H f) = sup s fun a => g' ↑(f a)
  rw [coe_sup']
  -- ⊢ g' (sup s (WithBot.some ∘ f)) = sup s fun a => g' ↑(f a)
  refine' comp_sup_eq_sup_comp g' _ rfl
  -- ⊢ ∀ (x y : WithBot α), g' (x ⊔ y) = g' x ⊔ g' y
  intro f₁ f₂
  -- ⊢ g' (f₁ ⊔ f₂) = g' f₁ ⊔ g' f₂
  cases f₁ using WithBot.recBotCoe with
  | bot =>
    rw [bot_sup_eq]
    exact bot_sup_eq.symm
  | coe f₁ =>
    cases f₂ using WithBot.recBotCoe with
    | bot => rfl
    | coe f₂ => exact congr_arg _ (g_sup f₁ f₂)
#align finset.comp_sup'_eq_sup'_comp Finset.comp_sup'_eq_sup'_comp

theorem sup'_induction {p : α → Prop} (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊔ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.sup' H f) := by
  show @WithBot.recBotCoe α (fun _ => Prop) True p ↑(s.sup' H f)
  -- ⊢ WithBot.recBotCoe True p ↑(sup' s H f)
  rw [coe_sup']
  -- ⊢ WithBot.recBotCoe True p (sup s (WithBot.some ∘ f))
  refine' sup_induction trivial _ hs
  -- ⊢ ∀ (a₁ : WithBot α), WithBot.recBotCoe True p a₁ → ∀ (a₂ : WithBot α), WithBo …
  rintro (_ | a₁) h₁ a₂ h₂
  -- ⊢ WithBot.recBotCoe True p (none ⊔ a₂)
  · rw [WithBot.none_eq_bot, bot_sup_eq]
    -- ⊢ WithBot.recBotCoe True p a₂
    exact h₂
    -- 🎉 no goals
  · cases a₂ using WithBot.recBotCoe with
    | bot => exact h₁
    | coe a₂ => exact hp a₁ h₁ a₂ h₂
#align finset.sup'_induction Finset.sup'_induction

theorem sup'_mem (s : Set α) (w : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), x ⊔ y ∈ s) {ι : Type*}
    (t : Finset ι) (H : t.Nonempty) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.sup' H p ∈ s :=
  sup'_induction H p w h
#align finset.sup'_mem Finset.sup'_mem

@[congr]
theorem sup'_congr {t : Finset β} {f g : β → α} (h₁ : s = t) (h₂ : ∀ x ∈ s, f x = g x) :
    s.sup' H f = t.sup' (h₁ ▸ H) g := by
  subst s
  -- ⊢ sup' t H f = sup' t (_ : Finset.Nonempty t) g
  refine' eq_of_forall_ge_iff fun c => _
  -- ⊢ sup' t H f ≤ c ↔ sup' t (_ : Finset.Nonempty t) g ≤ c
  simp (config := { contextual := true }) only [sup'_le_iff, h₂]
  -- 🎉 no goals
#align finset.sup'_congr Finset.sup'_congr

@[simp]
theorem sup'_map {s : Finset γ} {f : γ ↪ β} (g : β → α) (hs : (s.map f).Nonempty)
    (hs' : s.Nonempty := Finset.map_nonempty.mp hs) : (s.map f).sup' hs g = s.sup' hs' (g ∘ f) := by
  rw [← WithBot.coe_eq_coe, coe_sup', sup_map, coe_sup']
  -- ⊢ sup s ((WithBot.some ∘ g) ∘ ↑f) = sup s (WithBot.some ∘ g ∘ ↑f)
  rfl
  -- 🎉 no goals
#align finset.sup'_map Finset.sup'_map

theorem sup'_mono {s₁ s₂ : Finset β} (h : s₁ ⊆ s₂) (h₁ : s₁.Nonempty):
    s₁.sup' h₁ f ≤ s₂.sup' (h₁.mono h) f :=
  Finset.sup'_le h₁ _ (fun _ hb => le_sup' _ (h hb))

end Sup'

section Inf'

variable [SemilatticeInf α]

theorem inf_of_mem {s : Finset β} (f : β → α) {b : β} (h : b ∈ s) :
    ∃ a : α, s.inf ((↑) ∘ f : β → WithTop α) = ↑a :=
  @sup_of_mem αᵒᵈ _ _ _ f _ h
#align finset.inf_of_mem Finset.inf_of_mem

/-- Given nonempty finset `s` then `s.inf' H f` is the infimum of its image under `f` in (possibly
unbounded) meet-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a top element you
may instead use `Finset.inf` which does not require `s` nonempty. -/
def inf' (s : Finset β) (H : s.Nonempty) (f : β → α) : α :=
  WithTop.untop (s.inf ((↑) ∘ f)) (by simpa using H)
                                      -- 🎉 no goals
#align finset.inf' Finset.inf'

variable {s : Finset β} (H : s.Nonempty) (f : β → α)

@[simp]
theorem coe_inf' : ((s.inf' H f : α) : WithTop α) = s.inf ((↑) ∘ f) :=
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

theorem le_inf' {a : α} (hs : ∀ b ∈ s, a ≤ f b) : a ≤ s.inf' H f :=
  sup'_le (α := αᵒᵈ) H f hs
#align finset.le_inf' Finset.le_inf'

theorem inf'_le {b : β} (h : b ∈ s) : s.inf' ⟨b, h⟩ f ≤ f b :=
  le_sup' (α := αᵒᵈ) f h
#align finset.inf'_le Finset.inf'_le

theorem inf'_le_of_le (hb : b ∈ s) (h : f b ≤ a) : s.inf' ⟨b, hb⟩ f ≤ a := (inf'_le _ hb).trans h
#align finset.inf'_le_of_le Finset.inf'_le_of_le

@[simp]
theorem inf'_const (a : α) : (s.inf' H fun _ => a) = a :=
  sup'_const (α := αᵒᵈ) H a
#align finset.inf'_const Finset.inf'_const

@[simp]
theorem le_inf'_iff {a : α} : a ≤ s.inf' H f ↔ ∀ b ∈ s, a ≤ f b :=
  sup'_le_iff (α := αᵒᵈ) H f
#align finset.le_inf'_iff Finset.le_inf'_iff

theorem inf'_biUnion [DecidableEq β] {s : Finset γ} (Hs : s.Nonempty) {t : γ → Finset β}
    (Ht : ∀ b, (t b).Nonempty) :
    (s.biUnion t).inf' (Hs.biUnion fun b _ => Ht b) f = s.inf' Hs (fun b => (t b).inf' (Ht b) f) :=
  sup'_biUnion (α := αᵒᵈ) _ Hs Ht
#align finset.inf'_bUnion Finset.inf'_biUnion

theorem comp_inf'_eq_inf'_comp [SemilatticeInf γ] {s : Finset β} (H : s.Nonempty) {f : β → α}
    (g : α → γ) (g_inf : ∀ x y, g (x ⊓ y) = g x ⊓ g y) : g (s.inf' H f) = s.inf' H (g ∘ f) :=
  comp_sup'_eq_sup'_comp (α := αᵒᵈ) (γ := γᵒᵈ) H g g_inf
#align finset.comp_inf'_eq_inf'_comp Finset.comp_inf'_eq_inf'_comp

theorem inf'_induction {p : α → Prop} (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊓ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.inf' H f) :=
  sup'_induction (α := αᵒᵈ) H f hp hs
#align finset.inf'_induction Finset.inf'_induction

theorem inf'_mem (s : Set α) (w : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), x ⊓ y ∈ s) {ι : Type*}
    (t : Finset ι) (H : t.Nonempty) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.inf' H p ∈ s :=
  inf'_induction H p w h
#align finset.inf'_mem Finset.inf'_mem

@[congr]
theorem inf'_congr {t : Finset β} {f g : β → α} (h₁ : s = t) (h₂ : ∀ x ∈ s, f x = g x) :
    s.inf' H f = t.inf' (h₁ ▸ H) g :=
  sup'_congr (α := αᵒᵈ) H h₁ h₂
#align finset.inf'_congr Finset.inf'_congr

@[simp]
theorem inf'_map {s : Finset γ} {f : γ ↪ β} (g : β → α) (hs : (s.map f).Nonempty)
    (hs' : s.Nonempty := Finset.map_nonempty.mp hs) : (s.map f).inf' hs g = s.inf' hs' (g ∘ f) :=
  sup'_map (α := αᵒᵈ) _ hs hs'
#align finset.inf'_map Finset.inf'_map

theorem inf'_mono {s₁ s₂ : Finset β} (h : s₁ ⊆ s₂) (h₁ : s₁.Nonempty) :
    s₂.inf' (h₁.mono h) f ≤ s₁.inf' h₁ f :=
  Finset.le_inf' h₁ _ (fun _ hb => inf'_le _ (h hb))

end Inf'

section Sup

variable [SemilatticeSup α] [OrderBot α]

theorem sup'_eq_sup {s : Finset β} (H : s.Nonempty) (f : β → α) : s.sup' H f = s.sup f :=
  le_antisymm (sup'_le H f fun _ => le_sup) (Finset.sup_le fun _ => le_sup' f)
#align finset.sup'_eq_sup Finset.sup'_eq_sup

theorem sup_closed_of_sup_closed {s : Set α} (t : Finset α) (htne : t.Nonempty) (h_subset : ↑t ⊆ s)
    (h : ∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s), a ⊔ b ∈ s) : t.sup id ∈ s :=
  sup'_eq_sup htne id ▸ sup'_induction _ _ h h_subset
#align finset.sup_closed_of_sup_closed Finset.sup_closed_of_sup_closed

theorem coe_sup_of_nonempty {s : Finset β} (h : s.Nonempty) (f : β → α) :
    (↑(s.sup f) : WithBot α) = s.sup ((↑) ∘ f) := by simp only [← sup'_eq_sup h, coe_sup' h]
                                                     -- 🎉 no goals
#align finset.coe_sup_of_nonempty Finset.coe_sup_of_nonempty

end Sup

section Inf

variable [SemilatticeInf α] [OrderTop α]

theorem inf'_eq_inf {s : Finset β} (H : s.Nonempty) (f : β → α) : s.inf' H f = s.inf f :=
  sup'_eq_sup (α := αᵒᵈ) H f
#align finset.inf'_eq_inf Finset.inf'_eq_inf

theorem inf_closed_of_inf_closed {s : Set α} (t : Finset α) (htne : t.Nonempty) (h_subset : ↑t ⊆ s)
    (h : ∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s), a ⊓ b ∈ s) : t.inf id ∈ s :=
  sup_closed_of_sup_closed (α := αᵒᵈ) t htne h_subset h
#align finset.inf_closed_of_inf_closed Finset.inf_closed_of_inf_closed

theorem coe_inf_of_nonempty {s : Finset β} (h : s.Nonempty) (f : β → α) :
    (↑(s.inf f) : WithTop α) = s.inf ((↑) ∘ f) :=
  coe_sup_of_nonempty (α := αᵒᵈ) h f
#align finset.coe_inf_of_nonempty Finset.coe_inf_of_nonempty

end Inf

@[simp]
protected theorem sup_apply {C : β → Type*} [∀ b : β, SemilatticeSup (C b)]
    [∀ b : β, OrderBot (C b)] (s : Finset α) (f : α → ∀ b : β, C b) (b : β) :
    s.sup f b = s.sup fun a => f a b :=
  comp_sup_eq_sup_comp (fun x : ∀ b : β, C b => x b) (fun _ _ => rfl) rfl
#align finset.sup_apply Finset.sup_apply

@[simp]
protected theorem inf_apply {C : β → Type*} [∀ b : β, SemilatticeInf (C b)]
    [∀ b : β, OrderTop (C b)] (s : Finset α) (f : α → ∀ b : β, C b) (b : β) :
    s.inf f b = s.inf fun a => f a b :=
  Finset.sup_apply (C := fun b => (C b)ᵒᵈ) s f b
#align finset.inf_apply Finset.inf_apply

@[simp]
protected theorem sup'_apply {C : β → Type*} [∀ b : β, SemilatticeSup (C b)]
    {s : Finset α} (H : s.Nonempty) (f : α → ∀ b : β, C b) (b : β) :
    s.sup' H f b = s.sup' H fun a => f a b :=
  comp_sup'_eq_sup'_comp H (fun x : ∀ b : β, C b => x b) fun _ _ => rfl
#align finset.sup'_apply Finset.sup'_apply

@[simp]
protected theorem inf'_apply {C : β → Type*} [∀ b : β, SemilatticeInf (C b)]
    {s : Finset α} (H : s.Nonempty) (f : α → ∀ b : β, C b) (b : β) :
    s.inf' H f b = s.inf' H fun a => f a b :=
  Finset.sup'_apply (C := fun b => (C b)ᵒᵈ) H f b
#align finset.inf'_apply Finset.inf'_apply

@[simp]
theorem toDual_sup' [SemilatticeSup α] {s : Finset ι} (hs : s.Nonempty) (f : ι → α) :
    toDual (s.sup' hs f) = s.inf' hs (toDual ∘ f) :=
  rfl
#align finset.to_dual_sup' Finset.toDual_sup'

@[simp]
theorem toDual_inf' [SemilatticeInf α] {s : Finset ι} (hs : s.Nonempty) (f : ι → α) :
    toDual (s.inf' hs f) = s.sup' hs (toDual ∘ f) :=
  rfl
#align finset.to_dual_inf' Finset.toDual_inf'

@[simp]
theorem ofDual_sup' [SemilatticeInf α] {s : Finset ι} (hs : s.Nonempty) (f : ι → αᵒᵈ) :
    ofDual (s.sup' hs f) = s.inf' hs (ofDual ∘ f) :=
  rfl
#align finset.of_dual_sup' Finset.ofDual_sup'

@[simp]
theorem ofDual_inf' [SemilatticeSup α] {s : Finset ι} (hs : s.Nonempty) (f : ι → αᵒᵈ) :
    ofDual (s.inf' hs f) = s.sup' hs (ofDual ∘ f) :=
  rfl
#align finset.of_dual_inf' Finset.ofDual_inf'

section LinearOrder

variable [LinearOrder α] {s : Finset ι} (H : s.Nonempty) {f : ι → α} {a : α}

@[simp]
theorem le_sup'_iff : a ≤ s.sup' H f ↔ ∃ b ∈ s, a ≤ f b := by
  rw [← WithBot.coe_le_coe, coe_sup', Finset.le_sup_iff (WithBot.bot_lt_coe a)]
  -- ⊢ (∃ b, b ∈ s ∧ ↑a ≤ (WithBot.some ∘ f) b) ↔ ∃ b, b ∈ s ∧ a ≤ f b
  exact exists_congr (fun _ => and_congr_right' WithBot.coe_le_coe)
  -- 🎉 no goals
#align finset.le_sup'_iff Finset.le_sup'_iff

@[simp]
theorem lt_sup'_iff : a < s.sup' H f ↔ ∃ b ∈ s, a < f b := by
  rw [← WithBot.coe_lt_coe, coe_sup', Finset.lt_sup_iff]
  -- ⊢ (∃ b, b ∈ s ∧ ↑a < (WithBot.some ∘ f) b) ↔ ∃ b, b ∈ s ∧ a < f b
  exact exists_congr (fun _ => and_congr_right' WithBot.coe_lt_coe)
  -- 🎉 no goals
#align finset.lt_sup'_iff Finset.lt_sup'_iff

@[simp]
theorem sup'_lt_iff : s.sup' H f < a ↔ ∀ i ∈ s, f i < a := by
  rw [← WithBot.coe_lt_coe, coe_sup', Finset.sup_lt_iff (WithBot.bot_lt_coe a)]
  -- ⊢ (∀ (b : ι), b ∈ s → (WithBot.some ∘ f) b < ↑a) ↔ ∀ (i : ι), i ∈ s → f i < a
  exact ball_congr (fun _ _ => WithBot.coe_lt_coe)
  -- 🎉 no goals
#align finset.sup'_lt_iff Finset.sup'_lt_iff

@[simp]
theorem inf'_le_iff : s.inf' H f ≤ a ↔ ∃ i ∈ s, f i ≤ a :=
  le_sup'_iff (α := αᵒᵈ) H
#align finset.inf'_le_iff Finset.inf'_le_iff

@[simp]
theorem inf'_lt_iff : s.inf' H f < a ↔ ∃ i ∈ s, f i < a :=
  lt_sup'_iff (α := αᵒᵈ) H
#align finset.inf'_lt_iff Finset.inf'_lt_iff

@[simp]
theorem lt_inf'_iff : a < s.inf' H f ↔ ∀ i ∈ s, a < f i :=
  sup'_lt_iff (α := αᵒᵈ) H
#align finset.lt_inf'_iff Finset.lt_inf'_iff

theorem exists_mem_eq_sup' (f : ι → α) : ∃ i, i ∈ s ∧ s.sup' H f = f i := by
  refine' H.cons_induction (fun c => _) fun c s hc hs ih => _
  -- ⊢ ∃ i, i ∈ {c} ∧ sup' {c} (_ : Finset.Nonempty {c}) f = f i
  · exact ⟨c, mem_singleton_self c, rfl⟩
    -- 🎉 no goals
  · rcases ih with ⟨b, hb, h'⟩
    -- ⊢ ∃ i, i ∈ cons c s hc ∧ sup' (cons c s hc) (_ : Finset.Nonempty (cons c s hc) …
    rw [sup'_cons hs, h']
    -- ⊢ ∃ i, i ∈ cons c s hc ∧ f c ⊔ f b = f i
    cases le_total (f b) (f c) with
    | inl h => exact ⟨c, mem_cons.2 (Or.inl rfl), sup_eq_left.2 h⟩
    | inr h => exact ⟨b, mem_cons.2 (Or.inr hb), sup_eq_right.2 h⟩
#align finset.exists_mem_eq_sup' Finset.exists_mem_eq_sup'

theorem exists_mem_eq_inf' (f : ι → α) : ∃ i, i ∈ s ∧ s.inf' H f = f i :=
  exists_mem_eq_sup' (α := αᵒᵈ) H f
#align finset.exists_mem_eq_inf' Finset.exists_mem_eq_inf'

theorem exists_mem_eq_sup [OrderBot α] (s : Finset ι) (h : s.Nonempty) (f : ι → α) :
    ∃ i, i ∈ s ∧ s.sup f = f i :=
  sup'_eq_sup h f ▸ exists_mem_eq_sup' h f
#align finset.exists_mem_eq_sup Finset.exists_mem_eq_sup

theorem exists_mem_eq_inf [OrderTop α] (s : Finset ι) (h : s.Nonempty) (f : ι → α) :
    ∃ i, i ∈ s ∧ s.inf f = f i :=
  exists_mem_eq_sup (α := αᵒᵈ) s h f
#align finset.exists_mem_eq_inf Finset.exists_mem_eq_inf

end LinearOrder

/-! ### max and min of finite sets -/


section MaxMin

variable [LinearOrder α]

/-- Let `s` be a finset in a linear order. Then `s.max` is the maximum of `s` if `s` is not empty,
and `⊥` otherwise. It belongs to `WithBot α`. If you want to get an element of `α`, see
`s.max'`. -/
protected def max (s : Finset α) : WithBot α :=
  sup s (↑)
#align finset.max Finset.max

theorem max_eq_sup_coe {s : Finset α} : s.max = s.sup (↑) :=
  rfl
#align finset.max_eq_sup_coe Finset.max_eq_sup_coe

theorem max_eq_sup_withBot (s : Finset α) : s.max = sup s (↑) :=
  rfl
#align finset.max_eq_sup_with_bot Finset.max_eq_sup_withBot

@[simp]
theorem max_empty : (∅ : Finset α).max = ⊥ :=
  rfl
#align finset.max_empty Finset.max_empty

@[simp]
theorem max_insert {a : α} {s : Finset α} : (insert a s).max = max ↑a s.max :=
  fold_insert_idem
#align finset.max_insert Finset.max_insert

@[simp]
theorem max_singleton {a : α} : Finset.max {a} = (a : WithBot α) := by
  rw [← insert_emptyc_eq]
  -- ⊢ Finset.max (insert a ∅) = ↑a
  exact max_insert
  -- 🎉 no goals
#align finset.max_singleton Finset.max_singleton

theorem max_of_mem {s : Finset α} {a : α} (h : a ∈ s) : ∃ b : α, s.max = b := by
  obtain ⟨b, h, _⟩ := le_sup (α := WithBot α) h _ rfl
  -- ⊢ ∃ b, Finset.max s = ↑b
  exact ⟨b, h⟩
  -- 🎉 no goals
#align finset.max_of_mem Finset.max_of_mem

theorem max_of_nonempty {s : Finset α} (h : s.Nonempty) : ∃ a : α, s.max = a :=
  let ⟨_, h⟩ := h
  max_of_mem h
#align finset.max_of_nonempty Finset.max_of_nonempty

theorem max_eq_bot {s : Finset α} : s.max = ⊥ ↔ s = ∅ :=
  ⟨fun h ↦ s.eq_empty_or_nonempty.elim id fun H ↦ by
      obtain ⟨a, ha⟩ := max_of_nonempty H
      -- ⊢ s = ∅
      rw [h] at ha; cases ha; done, -- Porting note: error without `done`
      -- ⊢ s = ∅
                    -- 🎉 no goals
                              -- 🎉 no goals
    fun h ↦ h.symm ▸ max_empty⟩
#align finset.max_eq_bot Finset.max_eq_bot

theorem mem_of_max {s : Finset α} : ∀ {a : α}, s.max = a → a ∈ s := by
  induction' s using Finset.induction_on with b s _ ih
  -- ⊢ ∀ {a : α}, Finset.max ∅ = ↑a → a ∈ ∅
  · intro _ H; cases H
    -- ⊢ a✝ ∈ ∅
               -- 🎉 no goals
  · intro a h
    -- ⊢ a ∈ insert b s
    by_cases p : b = a
    -- ⊢ a ∈ insert b s
    · induction p
      -- ⊢ b ∈ insert b s
      exact mem_insert_self b s
      -- 🎉 no goals
    · cases' max_choice (↑b) s.max with q q <;> rw [max_insert, q] at h
      -- ⊢ a ∈ insert b s
                                                -- ⊢ a ∈ insert b s
                                                -- ⊢ a ∈ insert b s
      · cases h
        -- ⊢ b ∈ insert b s
        cases p rfl
        -- 🎉 no goals
      · exact mem_insert_of_mem (ih h)
        -- 🎉 no goals
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
and `⊤` otherwise. It belongs to `WithTop α`. If you want to get an element of `α`, see
`s.min'`. -/
protected def min (s : Finset α) : WithTop α :=
  inf s (↑)
#align finset.min Finset.min

theorem min_eq_inf_withTop (s : Finset α) : s.min = inf s (↑) :=
  rfl
#align finset.min_eq_inf_with_top Finset.min_eq_inf_withTop

@[simp]
theorem min_empty : (∅ : Finset α).min = ⊤ :=
  rfl
#align finset.min_empty Finset.min_empty

@[simp]
theorem min_insert {a : α} {s : Finset α} : (insert a s).min = min (↑a) s.min :=
  fold_insert_idem
#align finset.min_insert Finset.min_insert

@[simp]
theorem min_singleton {a : α} : Finset.min {a} = (a : WithTop α) := by
  rw [← insert_emptyc_eq]
  -- ⊢ Finset.min (insert a ∅) = ↑a
  exact min_insert
  -- 🎉 no goals
#align finset.min_singleton Finset.min_singleton

theorem min_of_mem {s : Finset α} {a : α} (h : a ∈ s) : ∃ b : α, s.min = b := by
  obtain ⟨b, h, _⟩ := inf_le (α := WithTop α) h _ rfl
  -- ⊢ ∃ b, Finset.min s = ↑b
  exact ⟨b, h⟩
  -- 🎉 no goals
#align finset.min_of_mem Finset.min_of_mem

theorem min_of_nonempty {s : Finset α} (h : s.Nonempty) : ∃ a : α, s.min = a :=
  let ⟨_, h⟩ := h
  min_of_mem h
#align finset.min_of_nonempty Finset.min_of_nonempty

theorem min_eq_top {s : Finset α} : s.min = ⊤ ↔ s = ∅ :=
  ⟨fun h =>
    s.eq_empty_or_nonempty.elim id fun H => by
      let ⟨a, ha⟩ := min_of_nonempty H
      -- ⊢ s = ∅
      rw [h] at ha; cases ha; done, -- Porting note: error without `done`
      -- ⊢ s = ∅
                    -- 🎉 no goals
                              -- 🎉 no goals
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
taking values in `WithTop α`. -/
def min' (s : Finset α) (H : s.Nonempty) : α :=
  inf' s H id
#align finset.min' Finset.min'

/-- Given a nonempty finset `s` in a linear order `α`, then `s.max' h` is its maximum, as an
element of `α`, where `h` is a proof of nonemptiness. Without this assumption, use instead `s.max`,
taking values in `WithBot α`. -/
def max' (s : Finset α) (H : s.Nonempty) : α :=
  sup' s H id
#align finset.max' Finset.max'

variable (s : Finset α) (H : s.Nonempty) {x : α}

theorem min'_mem : s.min' H ∈ s :=
  mem_of_min <| by simp only [Finset.min, min', id_eq, coe_inf']; rfl
                   -- ⊢ inf s WithTop.some = inf s (WithTop.some ∘ fun x => x)
                                                                  -- 🎉 no goals
#align finset.min'_mem Finset.min'_mem

theorem min'_le (x) (H2 : x ∈ s) : s.min' ⟨x, H2⟩ ≤ x :=
  min_le_of_eq H2 (WithTop.coe_untop _ _).symm
#align finset.min'_le Finset.min'_le

theorem le_min' (x) (H2 : ∀ y ∈ s, x ≤ y) : x ≤ s.min' H :=
  H2 _ <| min'_mem _ _
#align finset.le_min' Finset.le_min'

theorem isLeast_min' : IsLeast (↑s) (s.min' H) :=
  ⟨min'_mem _ _, min'_le _⟩
#align finset.is_least_min' Finset.isLeast_min'

@[simp]
theorem le_min'_iff {x} : x ≤ s.min' H ↔ ∀ y ∈ s, x ≤ y :=
  le_isGLB_iff (isLeast_min' s H).isGLB
#align finset.le_min'_iff Finset.le_min'_iff

/-- `{a}.min' _` is `a`. -/
@[simp]
theorem min'_singleton (a : α) : ({a} : Finset α).min' (singleton_nonempty _) = a := by simp [min']
                                                                                        -- 🎉 no goals
#align finset.min'_singleton Finset.min'_singleton

theorem max'_mem : s.max' H ∈ s :=
  mem_of_max <| by simp only [max', Finset.max, id_eq, coe_sup']; rfl
                   -- ⊢ sup s WithBot.some = sup s (WithBot.some ∘ fun x => x)
                                                                  -- 🎉 no goals
#align finset.max'_mem Finset.max'_mem

theorem le_max' (x) (H2 : x ∈ s) : x ≤ s.max' ⟨x, H2⟩ :=
  le_max_of_eq H2 (WithBot.coe_unbot _ _).symm
#align finset.le_max' Finset.le_max'

theorem max'_le (x) (H2 : ∀ y ∈ s, y ≤ x) : s.max' H ≤ x :=
  H2 _ <| max'_mem _ _
#align finset.max'_le Finset.max'_le

theorem isGreatest_max' : IsGreatest (↑s) (s.max' H) :=
  ⟨max'_mem _ _, le_max' _⟩
#align finset.is_greatest_max' Finset.isGreatest_max'

@[simp]
theorem max'_le_iff {x} : s.max' H ≤ x ↔ ∀ y ∈ s, y ≤ x :=
  isLUB_le_iff (isGreatest_max' s H).isLUB
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
  eq_of_forall_ge_iff fun _ => (max'_le_iff _ _).trans (sup'_le_iff _ _).symm
#align finset.max'_eq_sup' Finset.max'_eq_sup'

theorem min'_eq_inf' : s.min' H = s.inf' H id :=
  @max'_eq_sup' αᵒᵈ _ s H
#align finset.min'_eq_inf' Finset.min'_eq_inf'

/-- `{a}.max' _` is `a`. -/
@[simp]
theorem max'_singleton (a : α) : ({a} : Finset α).max' (singleton_nonempty _) = a := by simp [max']
                                                                                        -- 🎉 no goals
#align finset.max'_singleton Finset.max'_singleton

theorem min'_lt_max' {i j} (H1 : i ∈ s) (H2 : j ∈ s) (H3 : i ≠ j) :
    s.min' ⟨i, H1⟩ < s.max' ⟨i, H1⟩ :=
  isGLB_lt_isLUB_of_ne (s.isLeast_min' _).isGLB (s.isGreatest_max' _).isLUB H1 H2 H3
#align finset.min'_lt_max' Finset.min'_lt_max'

/-- If there's more than 1 element, the min' is less than the max'. An alternate version of
`min'_lt_max'` which is sometimes more convenient.
-/
theorem min'_lt_max'_of_card (h₂ : 1 < card s) :
    s.min' (Finset.card_pos.mp <| lt_trans zero_lt_one h₂) <
      s.max' (Finset.card_pos.mp <| lt_trans zero_lt_one h₂) := by
  rcases one_lt_card.1 h₂ with ⟨a, ha, b, hb, hab⟩
  -- ⊢ min' s (_ : Finset.Nonempty s) < max' s (_ : Finset.Nonempty s)
  exact s.min'_lt_max' ha hb hab
  -- 🎉 no goals
#align finset.min'_lt_max'_of_card Finset.min'_lt_max'_of_card

theorem map_ofDual_min (s : Finset αᵒᵈ) : s.min.map ofDual = (s.image ofDual).max := by
  rw [max_eq_sup_withBot, sup_image]
  -- ⊢ WithTop.map (↑ofDual) (Finset.min s) = sup s (WithBot.some ∘ ↑ofDual)
  exact congr_fun Option.map_id _
  -- 🎉 no goals
#align finset.map_of_dual_min Finset.map_ofDual_min

theorem map_ofDual_max (s : Finset αᵒᵈ) : s.max.map ofDual = (s.image ofDual).min := by
  rw [min_eq_inf_withTop, inf_image]
  -- ⊢ WithBot.map (↑ofDual) (Finset.max s) = inf s (WithTop.some ∘ ↑ofDual)
  exact congr_fun Option.map_id _
  -- 🎉 no goals
#align finset.map_of_dual_max Finset.map_ofDual_max

theorem map_toDual_min (s : Finset α) : s.min.map toDual = (s.image toDual).max := by
  rw [max_eq_sup_withBot, sup_image]
  -- ⊢ WithTop.map (↑toDual) (Finset.min s) = sup s (WithBot.some ∘ ↑toDual)
  exact congr_fun Option.map_id _
  -- 🎉 no goals
#align finset.map_to_dual_min Finset.map_toDual_min

theorem map_toDual_max (s : Finset α) : s.max.map toDual = (s.image toDual).min := by
  rw [min_eq_inf_withTop, inf_image]
  -- ⊢ WithBot.map (↑toDual) (Finset.max s) = inf s (WithTop.some ∘ ↑toDual)
  exact congr_fun Option.map_id _
  -- 🎉 no goals
#align finset.map_to_dual_max Finset.map_toDual_max

-- Porting note: new proofs without `convert` for the next four theorems.

theorem ofDual_min' {s : Finset αᵒᵈ} (hs : s.Nonempty) :
    ofDual (min' s hs) = max' (s.image ofDual) (hs.image _) := by
  rw [← WithBot.coe_eq_coe]
  -- ⊢ ↑(↑ofDual (min' s hs)) = ↑(max' (image (↑ofDual) s) (_ : Finset.Nonempty (im …
  simp only [min'_eq_inf', id_eq, ofDual_inf', Function.comp_apply, coe_sup', max'_eq_sup',
    sup_image]
  rfl
  -- 🎉 no goals
#align finset.of_dual_min' Finset.ofDual_min'

theorem ofDual_max' {s : Finset αᵒᵈ} (hs : s.Nonempty) :
    ofDual (max' s hs) = min' (s.image ofDual) (hs.image _) := by
  rw [← WithTop.coe_eq_coe]
  -- ⊢ ↑(↑ofDual (max' s hs)) = ↑(min' (image (↑ofDual) s) (_ : Finset.Nonempty (im …
  simp only [max'_eq_sup', id_eq, ofDual_sup', Function.comp_apply, coe_inf', min'_eq_inf',
    inf_image]
  rfl
  -- 🎉 no goals
#align finset.of_dual_max' Finset.ofDual_max'

theorem toDual_min' {s : Finset α} (hs : s.Nonempty) :
    toDual (min' s hs) = max' (s.image toDual) (hs.image _) := by
  rw [← WithBot.coe_eq_coe]
  -- ⊢ ↑(↑toDual (min' s hs)) = ↑(max' (image (↑toDual) s) (_ : Finset.Nonempty (im …
  simp only [min'_eq_inf', id_eq, toDual_inf', Function.comp_apply, coe_sup', max'_eq_sup',
    sup_image]
  rfl
  -- 🎉 no goals
#align finset.to_dual_min' Finset.toDual_min'

theorem toDual_max' {s : Finset α} (hs : s.Nonempty) :
    toDual (max' s hs) = min' (s.image toDual) (hs.image _) := by
  rw [← WithTop.coe_eq_coe]
  -- ⊢ ↑(↑toDual (max' s hs)) = ↑(min' (image (↑toDual) s) (_ : Finset.Nonempty (im …
  simp only [max'_eq_sup', id_eq, toDual_sup', Function.comp_apply, coe_inf', min'_eq_inf',
    inf_image]
  rfl
  -- 🎉 no goals
#align finset.to_dual_max' Finset.toDual_max'

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
  (isGreatest_max' _ _).unique <| by
    rw [coe_insert, max_comm]
    -- ⊢ IsGreatest (insert a ↑s) (max a (max' s H))
    exact (isGreatest_max' _ _).insert _
    -- 🎉 no goals
#align finset.max'_insert Finset.max'_insert

theorem min'_insert (a : α) (s : Finset α) (H : s.Nonempty) :
    (insert a s).min' (s.insert_nonempty a) = min (s.min' H) a :=
  (isLeast_min' _ _).unique <| by
    rw [coe_insert, min_comm]
    -- ⊢ IsLeast (insert a ↑s) (min a (min' s H))
    exact (isLeast_min' _ _).insert _
    -- 🎉 no goals
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
    (h : (s.image f).Nonempty) : (s.image f).max' h = f (s.max' ((Nonempty.image_iff f).mp h)) := by
  refine'
    le_antisymm (max'_le _ _ _ fun y hy => _) (le_max' _ _ (mem_image.mpr ⟨_, max'_mem _ _, rfl⟩))
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  -- ⊢ f x ≤ f (max' s (_ : Finset.Nonempty s))
  exact hf (le_max' _ _ hx)
  -- 🎉 no goals
#align finset.max'_image Finset.max'_image

@[simp]
theorem min'_image [LinearOrder β] {f : α → β} (hf : Monotone f) (s : Finset α)
    (h : (s.image f).Nonempty) : (s.image f).min' h = f (s.min' ((Nonempty.image_iff f).mp h)) := by
  refine'
    le_antisymm (min'_le _ _ (mem_image.mpr ⟨_, min'_mem _ _, rfl⟩)) (le_min' _ _ _ fun y hy => _)
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  -- ⊢ f (min' s (_ : Finset.Nonempty s)) ≤ f x
  exact hf (min'_le _ _ hx)
  -- 🎉 no goals
#align finset.min'_image Finset.min'_image

theorem coe_max' {s : Finset α} (hs : s.Nonempty) : ↑(s.max' hs) = s.max :=
  coe_sup' hs id
#align finset.coe_max' Finset.coe_max'

theorem coe_min' {s : Finset α} (hs : s.Nonempty) : ↑(s.min' hs) = s.min :=
  coe_inf' hs id
#align finset.coe_min' Finset.coe_min'

theorem max_mem_image_coe {s : Finset α} (hs : s.Nonempty) :
    s.max ∈ (s.image (↑) : Finset (WithBot α)) :=
  mem_image.2 ⟨max' s hs, max'_mem _ _, coe_max' hs⟩
#align finset.max_mem_image_coe Finset.max_mem_image_coe

theorem min_mem_image_coe {s : Finset α} (hs : s.Nonempty) :
    s.min ∈ (s.image (↑) : Finset (WithTop α)) :=
  mem_image.2 ⟨min' s hs, min'_mem _ _, coe_min' hs⟩
#align finset.min_mem_image_coe Finset.min_mem_image_coe

theorem max_mem_insert_bot_image_coe (s : Finset α) :
    s.max ∈ (insert ⊥ (s.image (↑)) : Finset (WithBot α)) :=
  mem_insert.2 <| s.eq_empty_or_nonempty.imp max_eq_bot.2 max_mem_image_coe
#align finset.max_mem_insert_bot_image_coe Finset.max_mem_insert_bot_image_coe

theorem min_mem_insert_top_image_coe (s : Finset α) :
    s.min ∈ (insert ⊤ (s.image (↑)) : Finset (WithTop α)) :=
  mem_insert.2 <| s.eq_empty_or_nonempty.imp min_eq_top.2 min_mem_image_coe
#align finset.min_mem_insert_top_image_coe Finset.min_mem_insert_top_image_coe

theorem max'_erase_ne_self {s : Finset α} (s0 : (s.erase x).Nonempty) : (s.erase x).max' s0 ≠ x :=
  ne_of_mem_erase (max'_mem _ s0)
#align finset.max'_erase_ne_self Finset.max'_erase_ne_self

theorem min'_erase_ne_self {s : Finset α} (s0 : (s.erase x).Nonempty) : (s.erase x).min' s0 ≠ x :=
  ne_of_mem_erase (min'_mem _ s0)
#align finset.min'_erase_ne_self Finset.min'_erase_ne_self

theorem max_erase_ne_self {s : Finset α} : (s.erase x).max ≠ x := by
  by_cases s0 : (s.erase x).Nonempty
  -- ⊢ Finset.max (erase s x) ≠ ↑x
  · refine' ne_of_eq_of_ne (coe_max' s0).symm _
    -- ⊢ ↑(max' (erase s x) s0) ≠ ↑x
    exact WithBot.coe_eq_coe.not.mpr (max'_erase_ne_self _)
    -- 🎉 no goals
  · rw [not_nonempty_iff_eq_empty.mp s0, max_empty]
    -- ⊢ ⊥ ≠ ↑x
    exact WithBot.bot_ne_coe
    -- 🎉 no goals
#align finset.max_erase_ne_self Finset.max_erase_ne_self

theorem min_erase_ne_self {s : Finset α} : (s.erase x).min ≠ x := by
  -- Porting note: old proof `convert @max_erase_ne_self αᵒᵈ _ _ _`
  convert @max_erase_ne_self αᵒᵈ _ (toDual x) (s.map toDual.toEmbedding) using 1
  -- ⊢ Finset.min (erase s x) = Finset.max (erase (map (Equiv.toEmbedding toDual) s …
  apply congr_arg -- porting note: forces unfolding to see `Finset.min` is `Finset.max`
  -- ⊢ erase s x = erase (map (Equiv.toEmbedding toDual) s) (↑toDual x)
  congr!
  -- ⊢ s = map (Equiv.toEmbedding toDual) s
  · ext; simp only [mem_map_equiv]; exact Iff.rfl
    -- ⊢ a✝ ∈ s ↔ a✝ ∈ map (Equiv.toEmbedding toDual) s
         -- ⊢ a✝ ∈ s ↔ ↑toDual.symm a✝ ∈ s
                                    -- 🎉 no goals
#align finset.min_erase_ne_self Finset.min_erase_ne_self

theorem exists_next_right {x : α} {s : Finset α} (h : ∃ y ∈ s, x < y) :
    ∃ y ∈ s, x < y ∧ ∀ z ∈ s, x < z → y ≤ z :=
  have Hne : (s.filter ((· < ·) x)).Nonempty := h.imp fun y hy => mem_filter.2 (by simpa)
                                                                                   -- 🎉 no goals
  have aux := (mem_filter.1 (min'_mem _ Hne))
  ⟨min' _ Hne, aux.1, by simp, fun z hzs hz => min'_le _ _ <| mem_filter.2 ⟨hzs, by simpa⟩⟩
                         -- 🎉 no goals
                                                                                    -- 🎉 no goals
#align finset.exists_next_right Finset.exists_next_right

theorem exists_next_left {x : α} {s : Finset α} (h : ∃ y ∈ s, y < x) :
    ∃ y ∈ s, y < x ∧ ∀ z ∈ s, z < x → z ≤ y :=
  @exists_next_right αᵒᵈ _ x s h
#align finset.exists_next_left Finset.exists_next_left

/-- If finsets `s` and `t` are interleaved, then `Finset.card s ≤ Finset.card t + 1`. -/
theorem card_le_of_interleaved {s t : Finset α}
    (h : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s),
        x < y → (∀ z ∈ s, z ∉ Set.Ioo x y) → ∃ z ∈ t, x < z ∧ z < y) :
    s.card ≤ t.card + 1 := by
  replace h : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), x < y → ∃ z ∈ t, x < z ∧ z < y
  -- ⊢ ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → x < y → ∃ z, z ∈ t ∧ x < z ∧ z < y
  · intro x hx y hy hxy
    -- ⊢ ∃ z, z ∈ t ∧ x < z ∧ z < y
    rcases exists_next_right ⟨y, hy, hxy⟩ with ⟨a, has, hxa, ha⟩
    -- ⊢ ∃ z, z ∈ t ∧ x < z ∧ z < y
    rcases h x hx a has hxa fun z hzs hz => hz.2.not_le <| ha _ hzs hz.1 with ⟨b, hbt, hxb, hba⟩
    -- ⊢ ∃ z, z ∈ t ∧ x < z ∧ z < y
    exact ⟨b, hbt, hxb, hba.trans_le <| ha _ hy hxy⟩
    -- 🎉 no goals
  set f : α → WithTop α := fun x => (t.filter fun y => x < y).min
  -- ⊢ card s ≤ card t + 1
  have f_mono : StrictMonoOn f s := by
    intro x hx y hy hxy
    rcases h x hx y hy hxy with ⟨a, hat, hxa, hay⟩
    calc
      f x ≤ a := min_le (mem_filter.2 ⟨hat, by simpa⟩)
      _ < f y :=
        (Finset.lt_inf_iff <| WithTop.coe_lt_top a).2 fun b hb =>
          WithTop.coe_lt_coe.2 <| hay.trans (by simpa using (mem_filter.1 hb).2)

  calc
    s.card = (s.image f).card := (card_image_of_injOn f_mono.injOn).symm
    _ ≤ (insert ⊤ (t.image (↑)) : Finset (WithTop α)).card :=
      card_mono <| image_subset_iff.2 fun x _ =>
          insert_subset_insert _ (image_subset_image <| filter_subset _ _)
            (min_mem_insert_top_image_coe _)
    _ ≤ t.card + 1 := (card_insert_le _ _).trans (add_le_add_right card_image_le _)
#align finset.card_le_of_interleaved Finset.card_le_of_interleaved

/-- If finsets `s` and `t` are interleaved, then `Finset.card s ≤ Finset.card (t \ s) + 1`. -/
theorem card_le_diff_of_interleaved {s t : Finset α}
    (h :
      ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s),
        x < y → (∀ z ∈ s, z ∉ Set.Ioo x y) → ∃ z ∈ t, x < z ∧ z < y) :
    s.card ≤ (t \ s).card + 1 :=
  card_le_of_interleaved fun x hx y hy hxy hs =>
    let ⟨z, hzt, hxz, hzy⟩ := h x hx y hy hxy hs
    ⟨z, mem_sdiff.2 ⟨hzt, fun hzs => hs z hzs ⟨hxz, hzy⟩⟩, hxz, hzy⟩
#align finset.card_le_diff_of_interleaved Finset.card_le_diff_of_interleaved

/-- Induction principle for `Finset`s in a linearly ordered type: a predicate is true on all
`s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` strictly greater than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_elim]
theorem induction_on_max [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h0 : p ∅)
    (step : ∀ a s, (∀ x ∈ s, x < a) → p s → p (insert a s)) : p s := by
  induction' s using Finset.strongInductionOn with s ihs
  -- ⊢ p s
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  -- ⊢ p ∅
  · exact h0
    -- 🎉 no goals
  · have H : s.max' hne ∈ s := max'_mem s hne
    -- ⊢ p s
    rw [← insert_erase H]
    -- ⊢ p (insert (max' s hne) (erase s (max' s hne)))
    exact step _ _ (fun x => s.lt_max'_of_mem_erase_max' hne) (ihs _ <| erase_ssubset H)
    -- 🎉 no goals
#align finset.induction_on_max Finset.induction_on_max

/-- Induction principle for `Finset`s in a linearly ordered type: a predicate is true on all
`s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` strictly less than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_elim]
theorem induction_on_min [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h0 : p ∅)
    (step : ∀ a s, (∀ x ∈ s, a < x) → p s → p (insert a s)) : p s :=
  @induction_on_max αᵒᵈ _ _ _ s h0 step
#align finset.induction_on_min Finset.induction_on_min

end MaxMin

section MaxMinInductionValue

variable [LinearOrder α] [LinearOrder β]

/-- Induction principle for `Finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` such that for elements of `s` denoted by `x` we have
  `f x ≤ f a`, `p s` implies `p (insert a s)`. -/
@[elab_as_elim]
theorem induction_on_max_value [DecidableEq ι] (f : ι → α) {p : Finset ι → Prop} (s : Finset ι)
    (h0 : p ∅) (step : ∀ a s, a ∉ s → (∀ x ∈ s, f x ≤ f a) → p s → p (insert a s)) : p s := by
  induction' s using Finset.strongInductionOn with s ihs
  -- ⊢ p s
  rcases(s.image f).eq_empty_or_nonempty with (hne | hne)
  -- ⊢ p s
  · simp only [image_eq_empty] at hne
    -- ⊢ p s
    simp only [hne, h0]
    -- 🎉 no goals
  · have H : (s.image f).max' hne ∈ s.image f := max'_mem (s.image f) hne
    -- ⊢ p s
    simp only [mem_image, exists_prop] at H
    -- ⊢ p s
    rcases H with ⟨a, has, hfa⟩
    -- ⊢ p s
    rw [← insert_erase has]
    -- ⊢ p (insert a (erase s a))
    refine' step _ _ (not_mem_erase a s) (fun x hx => _) (ihs _ <| erase_ssubset has)
    -- ⊢ f x ≤ f a
    rw [hfa]
    -- ⊢ f x ≤ max' (image f s) hne
    exact le_max' _ _ (mem_image_of_mem _ <| mem_of_mem_erase hx)
    -- 🎉 no goals
#align finset.induction_on_max_value Finset.induction_on_max_value

/-- Induction principle for `Finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` such that for elements of `s` denoted by `x` we have
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
    ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x := by
  cases' max_of_nonempty (h.image f) with y hy
  -- ⊢ ∃ x, x ∈ s ∧ ∀ (x' : β), x' ∈ s → f x' ≤ f x
  rcases mem_image.mp (mem_of_max hy) with ⟨x, hx, rfl⟩
  -- ⊢ ∃ x, x ∈ s ∧ ∀ (x' : β), x' ∈ s → f x' ≤ f x
  exact ⟨x, hx, fun x' hx' => le_max_of_eq (mem_image_of_mem f hx') hy⟩
  -- 🎉 no goals
#align finset.exists_max_image Finset.exists_max_image

theorem exists_min_image (s : Finset β) (f : β → α) (h : s.Nonempty) :
    ∃ x ∈ s, ∀ x' ∈ s, f x ≤ f x' :=
  @exists_max_image αᵒᵈ β _ s f h
#align finset.exists_min_image Finset.exists_min_image

end ExistsMaxMin

theorem isGLB_iff_isLeast [LinearOrder α] (i : α) (s : Finset α) (hs : s.Nonempty) :
    IsGLB (s : Set α) i ↔ IsLeast (↑s) i := by
  refine' ⟨fun his => _, IsLeast.isGLB⟩
  -- ⊢ IsLeast (↑s) i
  suffices i = min' s hs by
    rw [this]
    exact isLeast_min' s hs
  rw [IsGLB, IsGreatest, mem_lowerBounds, mem_upperBounds] at his
  -- ⊢ i = min' s hs
  exact le_antisymm (his.1 (Finset.min' s hs) (Finset.min'_mem s hs)) (his.2 _ (Finset.min'_le s))
  -- 🎉 no goals
#align finset.is_glb_iff_is_least Finset.isGLB_iff_isLeast

theorem isLUB_iff_isGreatest [LinearOrder α] (i : α) (s : Finset α) (hs : s.Nonempty) :
    IsLUB (s : Set α) i ↔ IsGreatest (↑s) i :=
  @isGLB_iff_isLeast αᵒᵈ _ i s hs
#align finset.is_lub_iff_is_greatest Finset.isLUB_iff_isGreatest

theorem isGLB_mem [LinearOrder α] {i : α} (s : Finset α) (his : IsGLB (s : Set α) i)
    (hs : s.Nonempty) : i ∈ s := by
  rw [← mem_coe]
  -- ⊢ i ∈ ↑s
  exact ((isGLB_iff_isLeast i s hs).mp his).1
  -- 🎉 no goals
#align finset.is_glb_mem Finset.isGLB_mem

theorem isLUB_mem [LinearOrder α] {i : α} (s : Finset α) (his : IsLUB (s : Set α) i)
    (hs : s.Nonempty) : i ∈ s :=
  @isGLB_mem αᵒᵈ _ i s his hs
#align finset.is_lub_mem Finset.isLUB_mem

end Finset

namespace Multiset

theorem map_finset_sup [DecidableEq α] [DecidableEq β] (s : Finset γ) (f : γ → Multiset β)
    (g : β → α) (hg : Function.Injective g) : map g (s.sup f) = s.sup (map g ∘ f) :=
  Finset.comp_sup_eq_sup_comp _ (fun _ _ => map_union hg) (map_zero _)
#align multiset.map_finset_sup Multiset.map_finset_sup

theorem count_finset_sup [DecidableEq β] (s : Finset α) (f : α → Multiset β) (b : β) :
    count b (s.sup f) = s.sup fun a => count b (f a) := by
  letI := Classical.decEq α
  -- ⊢ count b (Finset.sup s f) = Finset.sup s fun a => count b (f a)
  refine' s.induction _ _
  -- ⊢ count b (Finset.sup ∅ f) = Finset.sup ∅ fun a => count b (f a)
  · exact count_zero _
    -- 🎉 no goals
  · intro i s _ ih
    -- ⊢ count b (Finset.sup (insert i s) f) = Finset.sup (insert i s) fun a => count …
    rw [Finset.sup_insert, sup_eq_union, count_union, Finset.sup_insert, ih]
    -- ⊢ max (count b (f i)) (Finset.sup s fun a => count b (f a)) = count b (f i) ⊔  …
    rfl
    -- 🎉 no goals
#align multiset.count_finset_sup Multiset.count_finset_sup

theorem mem_sup {α β} [DecidableEq β] {s : Finset α} {f : α → Multiset β} {x : β} :
    x ∈ s.sup f ↔ ∃ v ∈ s, x ∈ f v := by
  classical
    induction' s using Finset.induction_on with a s has hxs
    · simp
    · rw [Finset.sup_insert, Multiset.sup_eq_union, Multiset.mem_union]
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
    x ∈ s.sup f ↔ ∃ v ∈ s, x ∈ f v := by
  change _ ↔ ∃ v ∈ s, x ∈ (f v).val
  -- ⊢ x ∈ sup s f ↔ ∃ v, v ∈ s ∧ x ∈ (f v).val
  rw [← Multiset.mem_sup, ← Multiset.mem_toFinset, sup_toFinset]
  -- ⊢ x ∈ sup s f ↔ x ∈ sup s fun x => Multiset.toFinset (f x).val
  simp_rw [val_toFinset]
  -- 🎉 no goals
#align finset.mem_sup Finset.mem_sup

theorem sup_eq_biUnion {α β} [DecidableEq β] (s : Finset α) (t : α → Finset β) :
    s.sup t = s.biUnion t := by
  ext
  -- ⊢ a✝ ∈ sup s t ↔ a✝ ∈ Finset.biUnion s t
  rw [mem_sup, mem_biUnion]
  -- 🎉 no goals
#align finset.sup_eq_bUnion Finset.sup_eq_biUnion

@[simp]
theorem sup_singleton'' [DecidableEq α] (s : Finset β) (f : β → α) :
    (s.sup fun b => {f b}) = s.image f := by
  ext a
  -- ⊢ (a ∈ sup s fun b => {f b}) ↔ a ∈ image f s
  rw [mem_sup, mem_image]
  -- ⊢ (∃ v, v ∈ s ∧ a ∈ {f v}) ↔ ∃ a_1, a_1 ∈ s ∧ f a_1 = a
  simp only [mem_singleton, eq_comm]
  -- 🎉 no goals
#align finset.sup_singleton'' Finset.sup_singleton''

@[simp]
theorem sup_singleton' [DecidableEq α] (s : Finset α) : s.sup singleton = s :=
  (s.sup_singleton'' _).trans image_id
#align finset.sup_singleton' Finset.sup_singleton'

end Finset

section Lattice

variable {ι' : Sort*} [CompleteLattice α]

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : Finset ι` of suprema
`⨆ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `iSup_eq_iSup_finset'` for a version
that works for `ι : Sort*`. -/
theorem iSup_eq_iSup_finset (s : ι → α) : ⨆ i, s i = ⨆ t : Finset ι, ⨆ i ∈ t, s i := by
  classical
  refine le_antisymm ?_ ?_
  · exact iSup_le fun b => le_iSup_of_le {b} <| le_iSup_of_le b <| le_iSup_of_le (by simp) <| le_rfl
  · exact iSup_le fun t => iSup_le fun b => iSup_le fun _ => le_iSup _ _
#align supr_eq_supr_finset iSup_eq_iSup_finset

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : Finset ι` of suprema
`⨆ i ∈ t, s i`. This version works for `ι : Sort*`. See `iSup_eq_iSup_finset` for a version
that assumes `ι : Type*` but has no `PLift`s. -/
theorem iSup_eq_iSup_finset' (s : ι' → α) :
    ⨆ i, s i = ⨆ t : Finset (PLift ι'), ⨆ i ∈ t, s (PLift.down i) := by
  rw [← iSup_eq_iSup_finset, ← Equiv.plift.surjective.iSup_comp]; rfl
  -- ⊢ ⨆ (x : PLift ι'), s (↑Equiv.plift x) = ⨆ (i : PLift ι'), s i.down
                                                                  -- 🎉 no goals
#align supr_eq_supr_finset' iSup_eq_iSup_finset'

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : Finset ι` of infima
`⨅ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `iInf_eq_iInf_finset'` for a version
that works for `ι : Sort*`. -/
theorem iInf_eq_iInf_finset (s : ι → α) : ⨅ i, s i = ⨅ (t : Finset ι) (i ∈ t), s i :=
  @iSup_eq_iSup_finset αᵒᵈ _ _ _
#align infi_eq_infi_finset iInf_eq_iInf_finset

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : Finset ι` of infima
`⨅ i ∈ t, s i`. This version works for `ι : Sort*`. See `iInf_eq_iInf_finset` for a version
that assumes `ι : Type*` but has no `PLift`s. -/
theorem iInf_eq_iInf_finset' (s : ι' → α) :
    ⨅ i, s i = ⨅ t : Finset (PLift ι'), ⨅ i ∈ t, s (PLift.down i) :=
  @iSup_eq_iSup_finset' αᵒᵈ _ _ _
#align infi_eq_infi_finset' iInf_eq_iInf_finset'

end Lattice

namespace Set

variable {ι' : Sort*}

/-- Union of an indexed family of sets `s : ι → Set α` is equal to the union of the unions
of finite subfamilies. This version assumes `ι : Type*`. See also `iUnion_eq_iUnion_finset'` for
a version that works for `ι : Sort*`. -/
theorem iUnion_eq_iUnion_finset (s : ι → Set α) : ⋃ i, s i = ⋃ t : Finset ι, ⋃ i ∈ t, s i :=
  iSup_eq_iSup_finset s
#align set.Union_eq_Union_finset Set.iUnion_eq_iUnion_finset

/-- Union of an indexed family of sets `s : ι → Set α` is equal to the union of the unions
of finite subfamilies. This version works for `ι : Sort*`. See also `iUnion_eq_iUnion_finset` for
a version that assumes `ι : Type*` but avoids `PLift`s in the right hand side. -/
theorem iUnion_eq_iUnion_finset' (s : ι' → Set α) :
    ⋃ i, s i = ⋃ t : Finset (PLift ι'), ⋃ i ∈ t, s (PLift.down i) :=
  iSup_eq_iSup_finset' s
#align set.Union_eq_Union_finset' Set.iUnion_eq_iUnion_finset'

/-- Intersection of an indexed family of sets `s : ι → Set α` is equal to the intersection of the
intersections of finite subfamilies. This version assumes `ι : Type*`. See also
`iInter_eq_iInter_finset'` for a version that works for `ι : Sort*`. -/
theorem iInter_eq_iInter_finset (s : ι → Set α) : ⋂ i, s i = ⋂ t : Finset ι, ⋂ i ∈ t, s i :=
  iInf_eq_iInf_finset s
#align set.Inter_eq_Inter_finset Set.iInter_eq_iInter_finset

/-- Intersection of an indexed family of sets `s : ι → Set α` is equal to the intersection of the
intersections of finite subfamilies. This version works for `ι : Sort*`. See also
`iInter_eq_iInter_finset` for a version that assumes `ι : Type*` but avoids `PLift`s in the right
hand side. -/
theorem iInter_eq_iInter_finset' (s : ι' → Set α) :
    ⋂ i, s i = ⋂ t : Finset (PLift ι'), ⋂ i ∈ t, s (PLift.down i) :=
  iInf_eq_iInf_finset' s
#align set.Inter_eq_Inter_finset' Set.iInter_eq_iInter_finset'

end Set

namespace Finset

/-! ### Interaction with ordered algebra structures -/


theorem sup_mul_le_mul_sup_of_nonneg [LinearOrderedSemiring α] [OrderBot α] {a b : ι → α}
    (s : Finset ι) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    s.sup (a * b) ≤ s.sup a * s.sup b :=
  Finset.sup_le fun _i hi =>
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
  (sup'_le _ _) fun _i hi =>
    mul_le_mul (le_sup' _ hi) (le_sup' _ hi) (hb _ hi) ((ha _ hi).trans <| le_sup' _ hi)
#align finset.sup'_mul_le_mul_sup'_of_nonneg Finset.sup'_mul_le_mul_sup'_of_nonneg

theorem inf'_mul_le_mul_inf'_of_nonneg [LinearOrderedSemiring α] {a b : ι → α} (s : Finset ι)
    (H : s.Nonempty) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    s.inf' H a * s.inf' H b ≤ s.inf' H (a * b) :=
  (le_inf' _ _) fun _i hi => mul_le_mul (inf'_le _ hi) (inf'_le _ hi) (le_inf' _ _ hb) (ha _ hi)
#align finset.inf'_mul_le_mul_inf'_of_nonneg Finset.inf'_mul_le_mul_inf'_of_nonneg

open Function

/-! ### Interaction with big lattice/set operations -/


section Lattice

theorem iSup_coe [SupSet β] (f : α → β) (s : Finset α) : ⨆ x ∈ (↑s : Set α), f x = ⨆ x ∈ s, f x :=
  rfl
#align finset.supr_coe Finset.iSup_coe

theorem iInf_coe [InfSet β] (f : α → β) (s : Finset α) : ⨅ x ∈ (↑s : Set α), f x = ⨅ x ∈ s, f x :=
  rfl
#align finset.infi_coe Finset.iInf_coe

variable [CompleteLattice β]

theorem iSup_singleton (a : α) (s : α → β) : ⨆ x ∈ ({a} : Finset α), s x = s a := by simp
                                                                                     -- 🎉 no goals
#align finset.supr_singleton Finset.iSup_singleton

theorem iInf_singleton (a : α) (s : α → β) : ⨅ x ∈ ({a} : Finset α), s x = s a := by simp
                                                                                     -- 🎉 no goals
#align finset.infi_singleton Finset.iInf_singleton

theorem iSup_option_toFinset (o : Option α) (f : α → β) : ⨆ x ∈ o.toFinset, f x = ⨆ x ∈ o, f x :=
  by simp
     -- 🎉 no goals
#align finset.supr_option_to_finset Finset.iSup_option_toFinset

theorem iInf_option_toFinset (o : Option α) (f : α → β) : ⨅ x ∈ o.toFinset, f x = ⨅ x ∈ o, f x :=
  @iSup_option_toFinset _ βᵒᵈ _ _ _
#align finset.infi_option_to_finset Finset.iInf_option_toFinset

variable [DecidableEq α]

theorem iSup_union {f : α → β} {s t : Finset α} :
    ⨆ x ∈ s ∪ t, f x = (⨆ x ∈ s, f x) ⊔ ⨆ x ∈ t, f x := by simp [iSup_or, iSup_sup_eq]
                                                           -- 🎉 no goals
#align finset.supr_union Finset.iSup_union

theorem iInf_union {f : α → β} {s t : Finset α} :
    ⨅ x ∈ s ∪ t, f x = (⨅ x ∈ s, f x) ⊓ ⨅ x ∈ t, f x :=
  @iSup_union α βᵒᵈ _ _ _ _ _
#align finset.infi_union Finset.iInf_union

theorem iSup_insert (a : α) (s : Finset α) (t : α → β) :
    ⨆ x ∈ insert a s, t x = t a ⊔ ⨆ x ∈ s, t x := by
  rw [insert_eq]
  -- ⊢ ⨆ (x : α) (_ : x ∈ {a} ∪ s), t x = t a ⊔ ⨆ (x : α) (_ : x ∈ s), t x
  simp only [iSup_union, Finset.iSup_singleton]
  -- 🎉 no goals
#align finset.supr_insert Finset.iSup_insert

theorem iInf_insert (a : α) (s : Finset α) (t : α → β) :
    ⨅ x ∈ insert a s, t x = t a ⊓ ⨅ x ∈ s, t x :=
  @iSup_insert α βᵒᵈ _ _ _ _ _
#align finset.infi_insert Finset.iInf_insert

theorem iSup_finset_image {f : γ → α} {g : α → β} {s : Finset γ} :
    ⨆ x ∈ s.image f, g x = ⨆ y ∈ s, g (f y) := by rw [← iSup_coe, coe_image, iSup_image, iSup_coe]
                                                  -- 🎉 no goals
#align finset.supr_finset_image Finset.iSup_finset_image

theorem iInf_finset_image {f : γ → α} {g : α → β} {s : Finset γ} :
    ⨅ x ∈ s.image f, g x = ⨅ y ∈ s, g (f y) := by rw [← iInf_coe, coe_image, iInf_image, iInf_coe]
                                                  -- 🎉 no goals
#align finset.infi_finset_image Finset.iInf_finset_image

theorem iSup_insert_update {x : α} {t : Finset α} (f : α → β) {s : β} (hx : x ∉ t) :
    ⨆ i ∈ insert x t, Function.update f x s i = s ⊔ ⨆ i ∈ t, f i := by
  simp only [Finset.iSup_insert, update_same]
  -- ⊢ s ⊔ ⨆ (x_1 : α) (_ : x_1 ∈ t), update f x s x_1 = s ⊔ ⨆ (i : α) (_ : i ∈ t), …
  rcongr (i hi); apply update_noteq; rintro rfl; exact hx hi
  -- ⊢ update f x s i = f i
                 -- ⊢ i ≠ x
                                     -- ⊢ False
                                                 -- 🎉 no goals
#align finset.supr_insert_update Finset.iSup_insert_update

theorem iInf_insert_update {x : α} {t : Finset α} (f : α → β) {s : β} (hx : x ∉ t) :
    ⨅ i ∈ insert x t, update f x s i = s ⊓ ⨅ i ∈ t, f i :=
  @iSup_insert_update α βᵒᵈ _ _ _ _ f _ hx
#align finset.infi_insert_update Finset.iInf_insert_update

theorem iSup_biUnion (s : Finset γ) (t : γ → Finset α) (f : α → β) :
    ⨆ y ∈ s.biUnion t, f y = ⨆ (x ∈ s) (y ∈ t x), f y := by simp [@iSup_comm _ α, iSup_and]
                                                            -- 🎉 no goals
#align finset.supr_bUnion Finset.iSup_biUnion

theorem iInf_biUnion (s : Finset γ) (t : γ → Finset α) (f : α → β) :
    ⨅ y ∈ s.biUnion t, f y = ⨅ (x ∈ s) (y ∈ t x), f y :=
  @iSup_biUnion _ βᵒᵈ _ _ _ _ _ _
#align finset.infi_bUnion Finset.iInf_biUnion

end Lattice

theorem set_biUnion_coe (s : Finset α) (t : α → Set β) : ⋃ x ∈ (↑s : Set α), t x = ⋃ x ∈ s, t x :=
  rfl
#align finset.set_bUnion_coe Finset.set_biUnion_coe

theorem set_biInter_coe (s : Finset α) (t : α → Set β) : ⋂ x ∈ (↑s : Set α), t x = ⋂ x ∈ s, t x :=
  rfl
#align finset.set_bInter_coe Finset.set_biInter_coe

theorem set_biUnion_singleton (a : α) (s : α → Set β) : ⋃ x ∈ ({a} : Finset α), s x = s a :=
  iSup_singleton a s
#align finset.set_bUnion_singleton Finset.set_biUnion_singleton

theorem set_biInter_singleton (a : α) (s : α → Set β) : ⋂ x ∈ ({a} : Finset α), s x = s a :=
  iInf_singleton a s
#align finset.set_bInter_singleton Finset.set_biInter_singleton

@[simp]
theorem set_biUnion_preimage_singleton (f : α → β) (s : Finset β) :
    ⋃ y ∈ s, f ⁻¹' {y} = f ⁻¹' s :=
  Set.biUnion_preimage_singleton f s
#align finset.set_bUnion_preimage_singleton Finset.set_biUnion_preimage_singleton

theorem set_biUnion_option_toFinset (o : Option α) (f : α → Set β) :
    ⋃ x ∈ o.toFinset, f x = ⋃ x ∈ o, f x :=
  iSup_option_toFinset o f
#align finset.set_bUnion_option_to_finset Finset.set_biUnion_option_toFinset

theorem set_biInter_option_toFinset (o : Option α) (f : α → Set β) :
    ⋂ x ∈ o.toFinset, f x = ⋂ x ∈ o, f x :=
  iInf_option_toFinset o f
#align finset.set_bInter_option_to_finset Finset.set_biInter_option_toFinset

theorem subset_set_biUnion_of_mem {s : Finset α} {f : α → Set β} {x : α} (h : x ∈ s) :
    f x ⊆ ⋃ y ∈ s, f y :=
  show f x ≤ ⨆ y ∈ s, f y from le_iSup_of_le x <| by simp only [h, iSup_pos, le_refl]
                                                     -- 🎉 no goals
#align finset.subset_set_bUnion_of_mem Finset.subset_set_biUnion_of_mem

variable [DecidableEq α]

theorem set_biUnion_union (s t : Finset α) (u : α → Set β) :
    ⋃ x ∈ s ∪ t, u x = (⋃ x ∈ s, u x) ∪ ⋃ x ∈ t, u x :=
  iSup_union
#align finset.set_bUnion_union Finset.set_biUnion_union

theorem set_biInter_inter (s t : Finset α) (u : α → Set β) :
    ⋂ x ∈ s ∪ t, u x = (⋂ x ∈ s, u x) ∩ ⋂ x ∈ t, u x :=
  iInf_union
#align finset.set_bInter_inter Finset.set_biInter_inter

theorem set_biUnion_insert (a : α) (s : Finset α) (t : α → Set β) :
    ⋃ x ∈ insert a s, t x = t a ∪ ⋃ x ∈ s, t x :=
  iSup_insert a s t
#align finset.set_bUnion_insert Finset.set_biUnion_insert

theorem set_biInter_insert (a : α) (s : Finset α) (t : α → Set β) :
    ⋂ x ∈ insert a s, t x = t a ∩ ⋂ x ∈ s, t x :=
  iInf_insert a s t
#align finset.set_bInter_insert Finset.set_biInter_insert

theorem set_biUnion_finset_image {f : γ → α} {g : α → Set β} {s : Finset γ} :
    ⋃ x ∈ s.image f, g x = ⋃ y ∈ s, g (f y) :=
  iSup_finset_image
#align finset.set_bUnion_finset_image Finset.set_biUnion_finset_image

theorem set_biInter_finset_image {f : γ → α} {g : α → Set β} {s : Finset γ} :
    ⋂ x ∈ s.image f, g x = ⋂ y ∈ s, g (f y) :=
  iInf_finset_image
#align finset.set_bInter_finset_image Finset.set_biInter_finset_image

theorem set_biUnion_insert_update {x : α} {t : Finset α} (f : α → Set β) {s : Set β} (hx : x ∉ t) :
    ⋃ i ∈ insert x t, @update _ _ _ f x s i = s ∪ ⋃ i ∈ t, f i :=
  iSup_insert_update f hx
#align finset.set_bUnion_insert_update Finset.set_biUnion_insert_update

theorem set_biInter_insert_update {x : α} {t : Finset α} (f : α → Set β) {s : Set β} (hx : x ∉ t) :
    ⋂ i ∈ insert x t, @update _ _ _ f x s i = s ∩ ⋂ i ∈ t, f i :=
  iInf_insert_update f hx
#align finset.set_bInter_insert_update Finset.set_biInter_insert_update

theorem set_biUnion_biUnion (s : Finset γ) (t : γ → Finset α) (f : α → Set β) :
    ⋃ y ∈ s.biUnion t, f y = ⋃ (x ∈ s) (y ∈ t x), f y :=
  iSup_biUnion s t f
#align finset.set_bUnion_bUnion Finset.set_biUnion_biUnion

theorem set_biInter_biUnion (s : Finset γ) (t : γ → Finset α) (f : α → Set β) :
    ⋂ y ∈ s.biUnion t, f y = ⋂ (x ∈ s) (y ∈ t x), f y :=
  iInf_biUnion s t f
#align finset.set_bInter_bUnion Finset.set_biInter_biUnion

end Finset
