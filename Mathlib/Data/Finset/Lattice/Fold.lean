/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Multiset.Lattice
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Order.Nat

/-!
# Lattice operations on finsets

This file is concerned with folding binary lattice operations over finsets.

For the special case of maximum and minimum of a finset, see Max.lean.

See also `Mathlib/Order/CompleteLattice/Finset.lean`, which is instead concerned with how big
lattice or set operations behave when indexed by a finset.
-/

open Function Multiset OrderDual

variable {F α β γ ι κ : Type*}

namespace Finset

/-! ### sup -/


section Sup

-- TODO: define with just `[Bot α]` where some lemmas hold without requiring `[OrderBot α]`
variable [SemilatticeSup α] [OrderBot α]

/-- Supremum of a finite set: `sup {a, b, c} f = f a ⊔ f b ⊔ f c` -/
def sup (s : Finset β) (f : β → α) : α :=
  s.fold (· ⊔ ·) ⊥ f

variable {s s₁ s₂ : Finset β} {f g : β → α} {a : α}

theorem sup_def : s.sup f = (s.1.map f).sup :=
  rfl

@[simp]
theorem sup_empty : (∅ : Finset β).sup f = ⊥ :=
  fold_empty

@[simp]
theorem sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b ⊔ s.sup f :=
  fold_cons h

@[simp]
theorem sup_insert [DecidableEq β] {b : β} : (insert b s : Finset β).sup f = f b ⊔ s.sup f :=
  fold_insert_idem

@[simp]
theorem sup_image [DecidableEq β] (s : Finset γ) (f : γ → β) (g : β → α) :
    (s.image f).sup g = s.sup (g ∘ f) :=
  fold_image_idem

@[simp]
theorem sup_map (s : Finset γ) (f : γ ↪ β) (g : β → α) : (s.map f).sup g = s.sup (g ∘ f) :=
  fold_map

@[simp]
theorem sup_singleton {b : β} : ({b} : Finset β).sup f = f b :=
  Multiset.sup_singleton

theorem sup_sup : s.sup (f ⊔ g) = s.sup f ⊔ s.sup g := by
  induction s using Finset.cons_induction with
  | empty => rw [sup_empty, sup_empty, sup_empty, bot_sup_eq]
  | cons _ _ _ ih =>
    rw [sup_cons, sup_cons, sup_cons, ih]
    exact sup_sup_sup_comm _ _ _ _

theorem sup_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) :
    s₁.sup f = s₂.sup g := by
  subst hs
  exact Finset.fold_congr hfg

@[simp]
theorem _root_.map_finset_sup [SemilatticeSup β] [OrderBot β]
    [FunLike F α β] [SupBotHomClass F α β]
    (f : F) (s : Finset ι) (g : ι → α) : f (s.sup g) = s.sup (f ∘ g) :=
  Finset.cons_induction_on s (map_bot f) fun i s _ h => by
    rw [sup_cons, sup_cons, map_sup, h, Function.comp_apply]

@[simp]
protected theorem sup_le_iff {a : α} : s.sup f ≤ a ↔ ∀ b ∈ s, f b ≤ a := by
  apply Iff.trans Multiset.sup_le
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩

protected alias ⟨_, sup_le⟩ := Finset.sup_le_iff

theorem sup_const_le : (s.sup fun _ => a) ≤ a :=
  Finset.sup_le fun _ _ => le_rfl

theorem le_sup {b : β} (hb : b ∈ s) : f b ≤ s.sup f :=
  Finset.sup_le_iff.1 le_rfl _ hb

lemma isLUB_sup : IsLUB (f '' s) (s.sup f) := by
  simp +contextual [IsLUB, IsLeast, upperBounds, lowerBounds, le_sup]

lemma isLUB_sup_id {s : Finset α} : IsLUB s (s.sup id) := by simpa using isLUB_sup (f := id)

theorem le_sup_of_le {b : β} (hb : b ∈ s) (h : a ≤ f b) : a ≤ s.sup f := h.trans <| le_sup hb

theorem sup_union [DecidableEq β] : (s₁ ∪ s₂).sup f = s₁.sup f ⊔ s₂.sup f :=
  eq_of_forall_ge_iff fun c => by simp [or_imp, forall_and]

theorem sup_const {s : Finset β} (h : s.Nonempty) (c : α) : (s.sup fun _ => c) = c :=
  eq_of_forall_ge_iff (fun _ => Finset.sup_le_iff.trans h.forall_const)

@[simp]
theorem sup_bot (s : Finset β) : (s.sup fun _ => ⊥) = (⊥ : α) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact sup_empty
  · exact sup_const hs _

theorem sup_ite (p : β → Prop) [DecidablePred p] :
    (s.sup fun i => ite (p i) (f i) (g i)) = (s.filter p).sup f ⊔ (s.filter fun i => ¬p i).sup g :=
  fold_ite _

@[gcongr]
theorem sup_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ≤ g b) : s.sup f ≤ s.sup g :=
  Finset.sup_le fun b hb => le_trans (h b hb) (le_sup hb)

@[gcongr]
theorem sup_mono (h : s₁ ⊆ s₂) : s₁.sup f ≤ s₂.sup f :=
  Finset.sup_le (fun _ hb => le_sup (h hb))

protected theorem sup_comm (s : Finset β) (t : Finset γ) (f : β → γ → α) :
    (s.sup fun b => t.sup (f b)) = t.sup fun c => s.sup fun b => f b c :=
  eq_of_forall_ge_iff fun a => by simpa using forall₂_swap

@[simp]
theorem sup_attach (s : Finset β) (f : β → α) : (s.attach.sup fun x => f x) = s.sup f :=
  (s.attach.sup_map (Function.Embedding.subtype _) f).symm.trans <| congr_arg _ attach_map_val

@[simp]
theorem sup_erase_bot [DecidableEq α] (s : Finset α) : (s.erase ⊥).sup id = s.sup id := by
  refine (sup_mono (s.erase_subset _)).antisymm (Finset.sup_le_iff.2 fun a ha => ?_)
  obtain rfl | ha' := eq_or_ne a ⊥
  · exact bot_le
  · exact le_sup (mem_erase.2 ⟨ha', ha⟩)

theorem sup_sdiff_right {α β : Type*} [GeneralizedBooleanAlgebra α] (s : Finset β) (f : β → α)
    (a : α) : (s.sup fun b => f b \ a) = s.sup f \ a := by
  induction s using Finset.cons_induction with
  | empty => rw [sup_empty, sup_empty, bot_sdiff]
  | cons _ _ _ h => rw [sup_cons, sup_cons, h, sup_sdiff]

theorem comp_sup_eq_sup_comp [SemilatticeSup γ] [OrderBot γ] {s : Finset β} {f : β → α} (g : α → γ)
    (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
  Finset.cons_induction_on s bot fun c t hc ih => by
    rw [sup_cons, sup_cons, g_sup, ih, Function.comp_apply]

/-- Computing `sup` in a subtype (closed under `sup`) is the same as computing it in `α`. -/
theorem sup_coe {P : α → Prop} {Pbot : P ⊥} {Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)} (t : Finset β)
    (f : β → { x : α // P x }) :
    (@sup { x // P x } _ (Subtype.semilatticeSup Psup) (Subtype.orderBot Pbot) t f : α) =
      t.sup fun x => ↑(f x) := by
  letI := Subtype.semilatticeSup Psup
  letI := Subtype.orderBot Pbot
  apply comp_sup_eq_sup_comp Subtype.val <;> intros <;> rfl

@[simp]
theorem sup_toFinset {α β} [DecidableEq β] (s : Finset α) (f : α → Multiset β) :
    (s.sup f).toFinset = s.sup fun x => (f x).toFinset :=
  comp_sup_eq_sup_comp Multiset.toFinset toFinset_union rfl

theorem _root_.List.foldr_sup_eq_sup_toFinset [DecidableEq α] (l : List α) :
    l.foldr (· ⊔ ·) ⊥ = l.toFinset.sup id := by
  rw [← coe_fold_r, ← Multiset.fold_dedup_idem, sup_def, ← List.toFinset_coe, toFinset_val,
    Multiset.map_id]
  rfl

theorem subset_range_sup_succ (s : Finset ℕ) : s ⊆ range (s.sup id).succ := fun _ hn =>
  mem_range.2 <| Nat.lt_succ_of_le <| @le_sup _ _ _ _ _ id _ hn

theorem sup_induction {p : α → Prop} (hb : p ⊥) (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊔ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.sup f) := by
  induction s using Finset.cons_induction with
  | empty => exact hb
  | cons _ _ _ ih =>
    simp only [sup_cons, forall_mem_cons] at hs ⊢
    exact hp _ hs.1 _ (ih hs.2)

theorem sup_le_of_le_directed {α : Type*} [SemilatticeSup α] [OrderBot α] (s : Set α)
    (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) (t : Finset α) :
    (∀ x ∈ t, ∃ y ∈ s, x ≤ y) → ∃ x ∈ s, t.sup id ≤ x := by
  classical
    induction t using Finset.induction_on with
    | empty =>
      simpa only [forall_prop_of_true, and_true, forall_prop_of_false, bot_le, not_false_iff,
        sup_empty, forall_true_iff, notMem_empty]
    | insert a r _ ih =>
      intro h
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
      rw [sup_insert, id, sup_le_iff]
      exact ⟨le_trans hay hyz, le_trans hsx_sup hxz⟩

-- If we acquire sublattices
-- the hypotheses should be reformulated as `s : SubsemilatticeSupBot`
theorem sup_mem (s : Set α) (w₁ : ⊥ ∈ s) (w₂ : ∀ᵉ (x ∈ s) (y ∈ s), x ⊔ y ∈ s)
    {ι : Type*} (t : Finset ι) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.sup p ∈ s :=
  @sup_induction _ _ _ _ _ _ (· ∈ s) w₁ w₂ h

@[simp]
protected theorem sup_eq_bot_iff (f : β → α) (S : Finset β) : S.sup f = ⊥ ↔ ∀ s ∈ S, f s = ⊥ := by
  classical induction' S using Finset.induction with a S _ hi <;> simp [*]

@[simp]
lemma sup_disjSum (s : Finset β) (t : Finset γ) (f : β ⊕ γ → α) :
    (s.disjSum t).sup f = (s.sup fun x ↦ f (.inl x)) ⊔ (t.sup fun x ↦ f (.inr x)) :=
  congr(fold _ $(bot_sup_eq _ |>.symm) _ _).trans (fold_disjSum _ _ _ _ _ _)

@[simp]
theorem sup_eq_bot_of_isEmpty [IsEmpty β] (f : β → α) (S : Finset β) : S.sup f = ⊥ := by
  rw [Finset.sup_eq_bot_iff]
  exact fun x _ => False.elim <| IsEmpty.false x

theorem le_sup_dite_pos (p : β → Prop) [DecidablePred p]
    {f : (b : β) → p b → α} {g : (b : β) → ¬p b → α} {b : β} (h₀ : b ∈ s) (h₁ : p b) :
    f b h₁ ≤ s.sup fun i ↦ if h : p i then f i h else g i h := by
  have : f b h₁ = (fun i ↦ if h : p i then f i h else g i h) b := by simp [h₁]
  rw [this]
  apply le_sup h₀

theorem le_sup_dite_neg (p : β → Prop) [DecidablePred p]
    {f : (b : β) → p b → α} {g : (b : β) → ¬p b → α} {b : β} (h₀ : b ∈ s) (h₁ : ¬p b) :
    g b h₁ ≤ s.sup fun i ↦ if h : p i then f i h else g i h := by
  have : g b h₁ = (fun i ↦ if h : p i then f i h else g i h) b := by simp [h₁]
  rw [this]
  apply le_sup h₀

end Sup

theorem sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : α → β) : s.sup f = ⨆ a ∈ s, f a :=
  le_antisymm
    (Finset.sup_le (fun a ha => le_iSup_of_le a <| le_iSup (fun _ => f a) ha))
    (iSup_le fun _ => iSup_le fun ha => le_sup ha)

theorem sup_id_eq_sSup [CompleteLattice α] (s : Finset α) : s.sup id = sSup s := by
  simp [sSup_eq_iSup, sup_eq_iSup]

theorem sup_id_set_eq_sUnion (s : Finset (Set α)) : s.sup id = ⋃₀ ↑s :=
  sup_id_eq_sSup _

@[simp]
theorem sup_set_eq_biUnion (s : Finset α) (f : α → Set β) : s.sup f = ⋃ x ∈ s, f x :=
  sup_eq_iSup _ _

theorem sup_eq_sSup_image [CompleteLattice β] (s : Finset α) (f : α → β) :
    s.sup f = sSup (f '' s) := by
  classical rw [← Finset.coe_image, ← sup_id_eq_sSup, sup_image, Function.id_comp]

theorem exists_sup_ge [SemilatticeSup β] [OrderBot β] [WellFoundedGT β] (f : α → β) :
    ∃ t : Finset α, ∀ a, f a ≤ t.sup f := by
  cases isEmpty_or_nonempty α
  · exact ⟨⊥, isEmptyElim⟩
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := wellFounded_gt.has_min _ (Set.range_nonempty (sup · f))
  refine ⟨t, fun a ↦ ?_⟩
  classical
  have := ht (f a ⊔ t.sup f) ⟨insert a t, by simp⟩
  rwa [GT.gt, right_lt_sup, not_not] at this

theorem exists_sup_eq_iSup [CompleteLattice β] [WellFoundedGT β] (f : α → β) :
    ∃ t : Finset α, t.sup f = ⨆ a, f a :=
  have ⟨t, ht⟩ := exists_sup_ge f
  ⟨t, (Finset.sup_le fun _ _ ↦ le_iSup ..).antisymm <| iSup_le ht⟩

/-! ### inf -/


section Inf

-- TODO: define with just `[Top α]` where some lemmas hold without requiring `[OrderTop α]`
variable [SemilatticeInf α] [OrderTop α]

/-- Infimum of a finite set: `inf {a, b, c} f = f a ⊓ f b ⊓ f c` -/
def inf (s : Finset β) (f : β → α) : α :=
  s.fold (· ⊓ ·) ⊤ f

variable {s s₁ s₂ : Finset β} {f g : β → α} {a : α}

theorem inf_def : s.inf f = (s.1.map f).inf :=
  rfl

@[simp]
theorem inf_empty : (∅ : Finset β).inf f = ⊤ :=
  fold_empty

@[simp]
theorem inf_cons {b : β} (h : b ∉ s) : (cons b s h).inf f = f b ⊓ s.inf f :=
  @sup_cons αᵒᵈ _ _ _ _ _ _ h

@[simp]
theorem inf_insert [DecidableEq β] {b : β} : (insert b s : Finset β).inf f = f b ⊓ s.inf f :=
  fold_insert_idem

@[simp]
theorem inf_image [DecidableEq β] (s : Finset γ) (f : γ → β) (g : β → α) :
    (s.image f).inf g = s.inf (g ∘ f) :=
  fold_image_idem

@[simp]
theorem inf_map (s : Finset γ) (f : γ ↪ β) (g : β → α) : (s.map f).inf g = s.inf (g ∘ f) :=
  fold_map

@[simp]
theorem inf_singleton {b : β} : ({b} : Finset β).inf f = f b :=
  Multiset.inf_singleton

theorem inf_inf : s.inf (f ⊓ g) = s.inf f ⊓ s.inf g :=
  @sup_sup αᵒᵈ _ _ _ _ _ _

theorem inf_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) :
    s₁.inf f = s₂.inf g := by
  subst hs
  exact Finset.fold_congr hfg

@[simp]
theorem _root_.map_finset_inf [SemilatticeInf β] [OrderTop β]
    [FunLike F α β] [InfTopHomClass F α β]
    (f : F) (s : Finset ι) (g : ι → α) : f (s.inf g) = s.inf (f ∘ g) :=
  Finset.cons_induction_on s (map_top f) fun i s _ h => by
    rw [inf_cons, inf_cons, map_inf, h, Function.comp_apply]

@[simp] protected theorem le_inf_iff {a : α} : a ≤ s.inf f ↔ ∀ b ∈ s, a ≤ f b :=
  @Finset.sup_le_iff αᵒᵈ _ _ _ _ _ _

protected alias ⟨_, le_inf⟩ := Finset.le_inf_iff

theorem le_inf_const_le : a ≤ s.inf fun _ => a :=
  Finset.le_inf fun _ _ => le_rfl

theorem inf_le {b : β} (hb : b ∈ s) : s.inf f ≤ f b :=
  Finset.le_inf_iff.1 le_rfl _ hb

lemma isGLB_inf : IsGLB (f '' s) (s.inf f) := by
  simp +contextual [IsGLB, IsGreatest, upperBounds, lowerBounds, inf_le]

lemma isGLB_inf_id {s : Finset α} : IsGLB s (s.inf id) := by simpa using isGLB_inf (f := id)

theorem inf_le_of_le {b : β} (hb : b ∈ s) (h : f b ≤ a) : s.inf f ≤ a := (inf_le hb).trans h

theorem inf_union [DecidableEq β] : (s₁ ∪ s₂).inf f = s₁.inf f ⊓ s₂.inf f :=
  eq_of_forall_le_iff fun c ↦ by simp [or_imp, forall_and]

theorem inf_const (h : s.Nonempty) (c : α) : (s.inf fun _ => c) = c := @sup_const αᵒᵈ _ _ _ _ h _

@[simp] theorem inf_top (s : Finset β) : (s.inf fun _ => ⊤) = (⊤ : α) := @sup_bot αᵒᵈ _ _ _ _

theorem inf_ite (p : β → Prop) [DecidablePred p] :
    (s.inf fun i ↦ ite (p i) (f i) (g i)) = (s.filter p).inf f ⊓ (s.filter fun i ↦ ¬ p i).inf g :=
  fold_ite _

@[gcongr]
theorem inf_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ≤ g b) : s.inf f ≤ s.inf g :=
  Finset.le_inf fun b hb => le_trans (inf_le hb) (h b hb)

@[gcongr]
theorem inf_mono (h : s₁ ⊆ s₂) : s₂.inf f ≤ s₁.inf f :=
  Finset.le_inf (fun _ hb => inf_le (h hb))

protected theorem inf_comm (s : Finset β) (t : Finset γ) (f : β → γ → α) :
    (s.inf fun b => t.inf (f b)) = t.inf fun c => s.inf fun b => f b c :=
  @Finset.sup_comm αᵒᵈ _ _ _ _ _ _ _

theorem inf_attach (s : Finset β) (f : β → α) : (s.attach.inf fun x => f x) = s.inf f :=
  @sup_attach αᵒᵈ _ _ _ _ _

@[simp]
theorem inf_erase_top [DecidableEq α] (s : Finset α) : (s.erase ⊤).inf id = s.inf id :=
  @sup_erase_bot αᵒᵈ _ _ _ _

theorem comp_inf_eq_inf_comp [SemilatticeInf γ] [OrderTop γ] {s : Finset β} {f : β → α} (g : α → γ)
    (g_inf : ∀ x y, g (x ⊓ y) = g x ⊓ g y) (top : g ⊤ = ⊤) : g (s.inf f) = s.inf (g ∘ f) :=
  @comp_sup_eq_sup_comp αᵒᵈ _ γᵒᵈ _ _ _ _ _ _ _ g_inf top

/-- Computing `inf` in a subtype (closed under `inf`) is the same as computing it in `α`. -/
theorem inf_coe {P : α → Prop} {Ptop : P ⊤} {Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)} (t : Finset β)
    (f : β → { x : α // P x }) :
    (@inf { x // P x } _ (Subtype.semilatticeInf Pinf) (Subtype.orderTop Ptop) t f : α) =
      t.inf fun x => ↑(f x) :=
  @sup_coe αᵒᵈ _ _ _ _ Ptop Pinf t f

theorem _root_.List.foldr_inf_eq_inf_toFinset [DecidableEq α] (l : List α) :
    l.foldr (· ⊓ ·) ⊤ = l.toFinset.inf id := by
  rw [← coe_fold_r, ← Multiset.fold_dedup_idem, inf_def, ← List.toFinset_coe, toFinset_val,
    Multiset.map_id]
  rfl

theorem inf_induction {p : α → Prop} (ht : p ⊤) (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊓ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.inf f) :=
  @sup_induction αᵒᵈ _ _ _ _ _ _ ht hp hs

theorem inf_mem (s : Set α) (w₁ : ⊤ ∈ s) (w₂ : ∀ᵉ (x ∈ s) (y ∈ s), x ⊓ y ∈ s)
    {ι : Type*} (t : Finset ι) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.inf p ∈ s :=
  @inf_induction _ _ _ _ _ _ (· ∈ s) w₁ w₂ h

@[simp]
protected theorem inf_eq_top_iff (f : β → α) (S : Finset β) : S.inf f = ⊤ ↔ ∀ s ∈ S, f s = ⊤ :=
  @Finset.sup_eq_bot_iff αᵒᵈ _ _ _ _ _

@[simp]
lemma inf_disjSum (s : Finset β) (t : Finset γ) (f : β ⊕ γ → α) :
    (s.disjSum t).inf f = (s.inf fun x ↦ f (.inl x)) ⊓ (t.inf fun x ↦ f (.inr x)) :=
  congr(fold _ $(top_inf_eq _ |>.symm) _ _).trans (fold_disjSum _ _ _ _ _ _)

theorem inf_dite_pos_le (p : β → Prop) [DecidablePred p]
    {f : (b : β) → p b → α} {g : (b : β) → ¬p b → α} {b : β} (h₀ : b ∈ s) (h₁ : p b) :
    (s.inf fun i ↦ if h : p i then f i h else g i h) ≤ f b h₁ := by
  have : f b h₁ = (fun i ↦ if h : p i then f i h else g i h) b := by simp [h₁]
  rw [this]
  apply inf_le h₀

theorem inf_dite_neg_le (p : β → Prop) [DecidablePred p]
    {f : (b : β) → p b → α} {g : (b : β) → ¬p b → α} {b : β} (h₀ : b ∈ s) (h₁ : ¬p b) :
    (s.inf fun i ↦ if h : p i then f i h else g i h) ≤ g b h₁ := by
  have : g b h₁ = (fun i ↦ if h : p i then f i h else g i h) b := by simp [h₁]
  rw [this]
  apply inf_le h₀

end Inf

@[simp]
theorem toDual_sup [SemilatticeSup α] [OrderBot α] (s : Finset β) (f : β → α) :
    toDual (s.sup f) = s.inf (toDual ∘ f) :=
  rfl

@[simp]
theorem toDual_inf [SemilatticeInf α] [OrderTop α] (s : Finset β) (f : β → α) :
    toDual (s.inf f) = s.sup (toDual ∘ f) :=
  rfl

@[simp]
theorem ofDual_sup [SemilatticeInf α] [OrderTop α] (s : Finset β) (f : β → αᵒᵈ) :
    ofDual (s.sup f) = s.inf (ofDual ∘ f) :=
  rfl

@[simp]
theorem ofDual_inf [SemilatticeSup α] [OrderBot α] (s : Finset β) (f : β → αᵒᵈ) :
    ofDual (s.inf f) = s.sup (ofDual ∘ f) :=
  rfl

section DistribLattice

variable [DistribLattice α]

section OrderBot

variable [OrderBot α] {s : Finset ι} {t : Finset κ} {f : ι → α} {g : κ → α} {a : α}

theorem sup_inf_distrib_left (s : Finset ι) (f : ι → α) (a : α) :
    a ⊓ s.sup f = s.sup fun i => a ⊓ f i := by
  induction s using Finset.cons_induction with
  | empty => simp_rw [Finset.sup_empty, inf_bot_eq]
  | cons _ _ _ h => rw [sup_cons, sup_cons, inf_sup_left, h]

theorem sup_inf_distrib_right (s : Finset ι) (f : ι → α) (a : α) :
    s.sup f ⊓ a = s.sup fun i => f i ⊓ a := by
  rw [_root_.inf_comm, s.sup_inf_distrib_left]
  simp_rw [_root_.inf_comm]

protected theorem disjoint_sup_right : Disjoint a (s.sup f) ↔ ∀ ⦃i⦄, i ∈ s → Disjoint a (f i) := by
  simp only [disjoint_iff, sup_inf_distrib_left, Finset.sup_eq_bot_iff]

protected theorem disjoint_sup_left : Disjoint (s.sup f) a ↔ ∀ ⦃i⦄, i ∈ s → Disjoint (f i) a := by
  simp only [disjoint_iff, sup_inf_distrib_right, Finset.sup_eq_bot_iff]

end OrderBot

section OrderTop

variable [OrderTop α] {f : ι → α} {g : κ → α} {s : Finset ι} {t : Finset κ} {a : α}

theorem inf_sup_distrib_left (s : Finset ι) (f : ι → α) (a : α) :
    a ⊔ s.inf f = s.inf fun i => a ⊔ f i :=
  @sup_inf_distrib_left αᵒᵈ _ _ _ _ _ _

theorem inf_sup_distrib_right (s : Finset ι) (f : ι → α) (a : α) :
    s.inf f ⊔ a = s.inf fun i => f i ⊔ a :=
  @sup_inf_distrib_right αᵒᵈ _ _ _ _ _ _

protected theorem codisjoint_inf_right :
    Codisjoint a (s.inf f) ↔ ∀ ⦃i⦄, i ∈ s → Codisjoint a (f i) :=
  @Finset.disjoint_sup_right αᵒᵈ _ _ _ _ _ _

protected theorem codisjoint_inf_left :
    Codisjoint (s.inf f) a ↔ ∀ ⦃i⦄, i ∈ s → Codisjoint (f i) a :=
  @Finset.disjoint_sup_left αᵒᵈ _ _ _ _ _ _

end OrderTop

end DistribLattice

section BooleanAlgebra

variable [BooleanAlgebra α] {s : Finset ι}

theorem sup_sdiff_left (s : Finset ι) (f : ι → α) (a : α) :
    (s.sup fun b => a \ f b) = a \ s.inf f := by
  induction s using Finset.cons_induction with
  | empty => rw [sup_empty, inf_empty, sdiff_top]
  | cons _ _ _ h => rw [sup_cons, inf_cons, h, sdiff_inf]

theorem inf_sdiff_left (hs : s.Nonempty) (f : ι → α) (a : α) :
    (s.inf fun b => a \ f b) = a \ s.sup f := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => rw [sup_singleton, inf_singleton]
  | cons _ _ _ _ ih => rw [sup_cons, inf_cons, ih, sdiff_sup]

theorem inf_sdiff_right (hs : s.Nonempty) (f : ι → α) (a : α) :
    (s.inf fun b => f b \ a) = s.inf f \ a := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => rw [inf_singleton, inf_singleton]
  | cons _ _ _ _ ih => rw [inf_cons, inf_cons, ih, inf_sdiff]

theorem inf_himp_right (s : Finset ι) (f : ι → α) (a : α) :
    (s.inf fun b => f b ⇨ a) = s.sup f ⇨ a :=
  @sup_sdiff_left αᵒᵈ _ _ _ _ _

theorem sup_himp_right (hs : s.Nonempty) (f : ι → α) (a : α) :
    (s.sup fun b => f b ⇨ a) = s.inf f ⇨ a :=
  @inf_sdiff_left αᵒᵈ _ _ _ hs _ _

theorem sup_himp_left (hs : s.Nonempty) (f : ι → α) (a : α) :
    (s.sup fun b => a ⇨ f b) = a ⇨ s.sup f :=
  @inf_sdiff_right αᵒᵈ _ _ _ hs _ _

@[simp]
protected theorem compl_sup (s : Finset ι) (f : ι → α) : (s.sup f)ᶜ = s.inf fun i => (f i)ᶜ :=
  map_finset_sup (OrderIso.compl α) _ _

@[simp]
protected theorem compl_inf (s : Finset ι) (f : ι → α) : (s.inf f)ᶜ = s.sup fun i => (f i)ᶜ :=
  map_finset_inf (OrderIso.compl α) _ _

end BooleanAlgebra

section LinearOrder

variable [LinearOrder α]

section OrderBot

variable [OrderBot α] {s : Finset ι} {f : ι → α} {a : α}

theorem comp_sup_eq_sup_comp_of_is_total [SemilatticeSup β] [OrderBot β] (g : α → β)
    (mono_g : Monotone g) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
  comp_sup_eq_sup_comp g mono_g.map_sup bot

@[simp]
protected theorem le_sup_iff (ha : ⊥ < a) : a ≤ s.sup f ↔ ∃ b ∈ s, a ≤ f b := by
  apply Iff.intro
  · induction s using cons_induction with
    | empty => exact (absurd · (not_le_of_gt ha))
    | cons c t hc ih =>
      rw [sup_cons, le_sup_iff]
      exact fun
      | Or.inl h => ⟨c, mem_cons.2 (Or.inl rfl), h⟩
      | Or.inr h => let ⟨b, hb, hle⟩ := ih h; ⟨b, mem_cons.2 (Or.inr hb), hle⟩
  · exact fun ⟨b, hb, hle⟩ => le_trans hle (le_sup hb)

protected theorem sup_eq_top_iff {α : Type*} [LinearOrder α] [BoundedOrder α] [Nontrivial α]
    {s : Finset ι} {f : ι → α} : s.sup f = ⊤ ↔ ∃ b ∈ s, f b = ⊤ := by
  simp only [← top_le_iff]
  exact Finset.le_sup_iff bot_lt_top

protected theorem Nonempty.sup_eq_top_iff {α : Type*} [LinearOrder α] [BoundedOrder α]
    {s : Finset ι} {f : ι → α} (hs : s.Nonempty) : s.sup f = ⊤ ↔ ∃ b ∈ s, f b = ⊤ := by
  cases subsingleton_or_nontrivial α
  · simpa [Subsingleton.elim _ (⊤ : α)]
  · exact Finset.sup_eq_top_iff

@[simp]
protected theorem lt_sup_iff : a < s.sup f ↔ ∃ b ∈ s, a < f b := by
  apply Iff.intro
  · induction s using cons_induction with
    | empty => exact (absurd · not_lt_bot)
    | cons c t hc ih =>
      rw [sup_cons, lt_sup_iff]
      exact fun
      | Or.inl h => ⟨c, mem_cons.2 (Or.inl rfl), h⟩
      | Or.inr h => let ⟨b, hb, hlt⟩ := ih h; ⟨b, mem_cons.2 (Or.inr hb), hlt⟩
  · exact fun ⟨b, hb, hlt⟩ => lt_of_lt_of_le hlt (le_sup hb)

@[simp]
protected theorem sup_lt_iff (ha : ⊥ < a) : s.sup f < a ↔ ∀ b ∈ s, f b < a :=
  ⟨fun hs _ hb => lt_of_le_of_lt (le_sup hb) hs,
    Finset.cons_induction_on s (fun _ => ha) fun c t hc => by
      simpa only [sup_cons, sup_lt_iff, mem_cons, forall_eq_or_imp] using And.imp_right⟩

theorem sup_mem_of_nonempty (hs : s.Nonempty) : s.sup f ∈ f '' s := by
  classical
  induction s using Finset.induction with
  | empty => exfalso; simp only [Finset.not_nonempty_empty] at hs
  | insert a s _ h =>
    rw [Finset.sup_insert (b := a) (s := s) (f := f)]
    cases s.eq_empty_or_nonempty with
    | inl hs => simp [hs]
    | inr hs =>
      simp only [Finset.coe_insert]
      rcases le_total (f a) (s.sup f) with (ha | ha)
      · rw [sup_eq_right.mpr ha]
        exact Set.image_mono (Set.subset_insert a s) (h hs)
      · rw [sup_eq_left.mpr ha]
        apply Set.mem_image_of_mem _ (Set.mem_insert a ↑s)

end OrderBot

section OrderTop

variable [OrderTop α] {s : Finset ι} {f : ι → α} {a : α}

theorem comp_inf_eq_inf_comp_of_is_total [SemilatticeInf β] [OrderTop β] (g : α → β)
    (mono_g : Monotone g) (top : g ⊤ = ⊤) : g (s.inf f) = s.inf (g ∘ f) :=
  comp_inf_eq_inf_comp g mono_g.map_inf top

@[simp]
protected theorem inf_le_iff (ha : a < ⊤) : s.inf f ≤ a ↔ ∃ b ∈ s, f b ≤ a :=
  @Finset.le_sup_iff αᵒᵈ _ _ _ _ _ _ ha

protected theorem inf_eq_bot_iff {α : Type*} [LinearOrder α] [BoundedOrder α] [Nontrivial α]
    {s : Finset ι} {f : ι → α} : s.inf f = ⊥ ↔ ∃ b ∈ s, f b = ⊥ :=
  Finset.sup_eq_top_iff (α := αᵒᵈ)

protected theorem Nonempty.inf_eq_bot_iff {α : Type*} [LinearOrder α] [BoundedOrder α]
    {s : Finset ι} {f : ι → α} (h : s.Nonempty) : s.inf f = ⊥ ↔ ∃ b ∈ s, f b = ⊥ :=
  h.sup_eq_top_iff (α := αᵒᵈ)

@[simp]
protected theorem inf_lt_iff : s.inf f < a ↔ ∃ b ∈ s, f b < a :=
  @Finset.lt_sup_iff αᵒᵈ _ _ _ _ _ _

@[simp]
protected theorem lt_inf_iff (ha : a < ⊤) : a < s.inf f ↔ ∀ b ∈ s, a < f b :=
  @Finset.sup_lt_iff αᵒᵈ _ _ _ _ _ _ ha

end OrderTop

end LinearOrder

theorem inf_eq_iInf [CompleteLattice β] (s : Finset α) (f : α → β) : s.inf f = ⨅ a ∈ s, f a :=
  sup_eq_iSup (β := βᵒᵈ) ..

theorem inf_id_eq_sInf [CompleteLattice α] (s : Finset α) : s.inf id = sInf s :=
  sup_id_eq_sSup (α := αᵒᵈ) _

theorem inf_id_set_eq_sInter (s : Finset (Set α)) : s.inf id = ⋂₀ ↑s :=
  inf_id_eq_sInf _

@[simp]
theorem inf_set_eq_iInter (s : Finset α) (f : α → Set β) : s.inf f = ⋂ x ∈ s, f x :=
  inf_eq_iInf _ _

theorem inf_eq_sInf_image [CompleteLattice β] (s : Finset α) (f : α → β) :
    s.inf f = sInf (f '' s) :=
  sup_eq_sSup_image (β := βᵒᵈ) ..

theorem exists_inf_le [SemilatticeInf β] [OrderTop β] [WellFoundedLT β] (f : α → β) :
    ∃ t : Finset α, ∀ a, t.inf f ≤ f a :=
  exists_sup_ge (β := βᵒᵈ) _

theorem exists_inf_eq_iInf [CompleteLattice β] [WellFoundedLT β] (f : α → β) :
    ∃ t : Finset α, t.inf f = ⨅ a, f a :=
  exists_sup_eq_iSup (β := βᵒᵈ) _

section Sup'

variable [SemilatticeSup α]

theorem sup_of_mem {s : Finset β} (f : β → α) {b : β} (h : b ∈ s) :
    ∃ a : α, s.sup ((↑) ∘ f : β → WithBot α) = ↑a :=
  Exists.imp (fun _ => And.left) (@le_sup (WithBot α) _ _ _ _ _ _ h (f b) rfl)

/-- Given nonempty finset `s` then `s.sup' H f` is the supremum of its image under `f` in (possibly
unbounded) join-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a bottom element
you may instead use `Finset.sup` which does not require `s` nonempty. -/
def sup' (s : Finset β) (H : s.Nonempty) (f : β → α) : α :=
  WithBot.unbot (s.sup ((↑) ∘ f)) (by simpa using H)

variable {s : Finset β} (H : s.Nonempty) (f : β → α)

@[simp]
theorem coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) ∘ f) := by
  rw [sup', WithBot.coe_unbot]

@[simp]
theorem sup'_cons {b : β} {hb : b ∉ s} :
    (cons b s hb).sup' (cons_nonempty hb) f = f b ⊔ s.sup' H f := by
  rw [← WithBot.coe_eq_coe]
  simp [WithBot.coe_sup]

@[simp]
theorem sup'_insert [DecidableEq β] {b : β} :
    (insert b s).sup' (insert_nonempty _ _) f = f b ⊔ s.sup' H f := by
  rw [← WithBot.coe_eq_coe]
  simp [WithBot.coe_sup]

@[simp]
theorem sup'_singleton {b : β} : ({b} : Finset β).sup' (singleton_nonempty _) f = f b :=
  rfl

@[simp]
theorem sup'_le_iff {a : α} : s.sup' H f ≤ a ↔ ∀ b ∈ s, f b ≤ a := by
  simp_rw [← @WithBot.coe_le_coe α, coe_sup', Finset.sup_le_iff]; rfl

alias ⟨_, sup'_le⟩ := sup'_le_iff

theorem le_sup' {b : β} (h : b ∈ s) : f b ≤ s.sup' ⟨b, h⟩ f :=
  (sup'_le_iff ⟨b, h⟩ f).1 le_rfl b h

set_option linter.docPrime false in
theorem isLUB_sup' {s : Finset α} (hs : s.Nonempty) : IsLUB s (sup' s hs id) :=
  ⟨fun x h => id_eq x ▸ le_sup' id h, fun _ h => Finset.sup'_le hs id h⟩

theorem le_sup'_of_le {a : α} {b : β} (hb : b ∈ s) (h : a ≤ f b) : a ≤ s.sup' ⟨b, hb⟩ f :=
  h.trans <| le_sup' _ hb

lemma sup'_eq_of_forall {a : α} (h : ∀ b ∈ s, f b = a) : s.sup' H f = a :=
  le_antisymm (sup'_le _ _ (fun _ hb ↦ (h _ hb).le))
    (le_sup'_of_le _ H.choose_spec (h _ H.choose_spec).ge)

@[simp]
theorem sup'_const (a : α) : s.sup' H (fun _ => a) = a := by
  apply le_antisymm
  · apply sup'_le
    intros
    exact le_rfl
  · apply le_sup' (fun _ => a) H.choose_spec

theorem sup'_union [DecidableEq β] {s₁ s₂ : Finset β} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
    (f : β → α) :
    (s₁ ∪ s₂).sup' (h₁.mono subset_union_left) f = s₁.sup' h₁ f ⊔ s₂.sup' h₂ f :=
  eq_of_forall_ge_iff fun a => by simp [or_imp, forall_and]

protected theorem sup'_comm {t : Finset γ} (hs : s.Nonempty) (ht : t.Nonempty) (f : β → γ → α) :
    (s.sup' hs fun b => t.sup' ht (f b)) = t.sup' ht fun c => s.sup' hs fun b => f b c :=
  eq_of_forall_ge_iff fun a => by simpa using forall₂_swap

theorem sup'_induction {p : α → Prop} (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊔ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.sup' H f) := by
  show @WithBot.recBotCoe α (fun _ => Prop) True p ↑(s.sup' H f)
  rw [coe_sup']
  refine sup_induction trivial (fun a₁ h₁ a₂ h₂ ↦ ?_) hs
  match a₁, a₂ with
  | ⊥, _ => rwa [bot_sup_eq]
  | (a₁ : α), ⊥ => rwa [sup_bot_eq]
  | (a₁ : α), (a₂ : α) => exact hp a₁ h₁ a₂ h₂

theorem sup'_mem (s : Set α) (w : ∀ᵉ (x ∈ s) (y ∈ s), x ⊔ y ∈ s) {ι : Type*}
    (t : Finset ι) (H : t.Nonempty) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.sup' H p ∈ s :=
  sup'_induction H p w h

@[congr]
theorem sup'_congr {t : Finset β} {f g : β → α} (h₁ : s = t) (h₂ : ∀ x ∈ s, f x = g x) :
    s.sup' H f = t.sup' (h₁ ▸ H) g := by
  subst s
  refine eq_of_forall_ge_iff fun c => ?_
  simp +contextual only [sup'_le_iff, h₂]

theorem comp_sup'_eq_sup'_comp [SemilatticeSup γ] {s : Finset β} (H : s.Nonempty) {f : β → α}
    (g : α → γ) (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) : g (s.sup' H f) = s.sup' H (g ∘ f) := by
  refine H.cons_induction ?_ ?_ <;> intros <;> simp [*]

@[simp]
theorem _root_.map_finset_sup' [SemilatticeSup β] [FunLike F α β] [SupHomClass F α β]
    (f : F) {s : Finset ι} (hs) (g : ι → α) :
    f (s.sup' hs g) = s.sup' hs (f ∘ g) := by
  refine hs.cons_induction ?_ ?_ <;> intros <;> simp [*]

/-- To rewrite from right to left, use `Finset.sup'_comp_eq_image`. -/
@[simp]
theorem sup'_image [DecidableEq β] {s : Finset γ} {f : γ → β} (hs : (s.image f).Nonempty)
    (g : β → α) :
    (s.image f).sup' hs g = s.sup' hs.of_image (g ∘ f) := by
  rw [← WithBot.coe_eq_coe]; simp only [coe_sup', sup_image, WithBot.coe_sup]; rfl

/-- A version of `Finset.sup'_image` with LHS and RHS reversed.
Also, this lemma assumes that `s` is nonempty instead of assuming that its image is nonempty. -/
lemma sup'_comp_eq_image [DecidableEq β] {s : Finset γ} {f : γ → β} (hs : s.Nonempty) (g : β → α) :
    s.sup' hs (g ∘ f) = (s.image f).sup' (hs.image f) g :=
  .symm <| sup'_image _ _

/-- To rewrite from right to left, use `Finset.sup'_comp_eq_map`. -/
@[simp]
theorem sup'_map {s : Finset γ} {f : γ ↪ β} (g : β → α) (hs : (s.map f).Nonempty) :
    (s.map f).sup' hs g = s.sup' (map_nonempty.1 hs) (g ∘ f) := by
  rw [← WithBot.coe_eq_coe, coe_sup', sup_map, coe_sup']
  rfl

/-- A version of `Finset.sup'_map` with LHS and RHS reversed.
Also, this lemma assumes that `s` is nonempty instead of assuming that its image is nonempty. -/
lemma sup'_comp_eq_map {s : Finset γ} {f : γ ↪ β} (g : β → α) (hs : s.Nonempty) :
    s.sup' hs (g ∘ f) = (s.map f).sup' (map_nonempty.2 hs) g :=
  .symm <| sup'_map _ _


@[gcongr]
theorem sup'_mono {s₁ s₂ : Finset β} (h : s₁ ⊆ s₂) (h₁ : s₁.Nonempty) :
    s₁.sup' h₁ f ≤ s₂.sup' (h₁.mono h) f :=
  Finset.sup'_le h₁ _ (fun _ hb => le_sup' _ (h hb))

@[gcongr]
lemma sup'_mono_fun {hs : s.Nonempty} {f g : β → α} (h : ∀ b ∈ s, f b ≤ g b) :
    s.sup' hs f ≤ s.sup' hs g := sup'_le _ _ fun b hb ↦ (h b hb).trans (le_sup' _ hb)

end Sup'

section Inf'

variable [SemilatticeInf α]

theorem inf_of_mem {s : Finset β} (f : β → α) {b : β} (h : b ∈ s) :
    ∃ a : α, s.inf ((↑) ∘ f : β → WithTop α) = ↑a :=
  @sup_of_mem αᵒᵈ _ _ _ f _ h

/-- Given nonempty finset `s` then `s.inf' H f` is the infimum of its image under `f` in (possibly
unbounded) meet-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a top element you
may instead use `Finset.inf` which does not require `s` nonempty. -/
def inf' (s : Finset β) (H : s.Nonempty) (f : β → α) : α :=
  WithTop.untop (s.inf ((↑) ∘ f)) (by simpa using H)

variable {s : Finset β} (H : s.Nonempty) (f : β → α)

@[simp]
theorem coe_inf' : ((s.inf' H f : α) : WithTop α) = s.inf ((↑) ∘ f) :=
  @coe_sup' αᵒᵈ _ _ _ H f

@[simp]
theorem inf'_cons {b : β} {hb : b ∉ s} :
    (cons b s hb).inf' (cons_nonempty hb) f = f b ⊓ s.inf' H f :=
  @sup'_cons αᵒᵈ _ _ _ H f _ _

@[simp]
theorem inf'_insert [DecidableEq β] {b : β} :
    (insert b s).inf' (insert_nonempty _ _) f = f b ⊓ s.inf' H f :=
  @sup'_insert αᵒᵈ _ _ _ H f _ _

@[simp]
theorem inf'_singleton {b : β} : ({b} : Finset β).inf' (singleton_nonempty _) f = f b :=
  rfl

@[simp]
theorem le_inf'_iff {a : α} : a ≤ s.inf' H f ↔ ∀ b ∈ s, a ≤ f b :=
  sup'_le_iff (α := αᵒᵈ) H f

theorem le_inf' {a : α} (hs : ∀ b ∈ s, a ≤ f b) : a ≤ s.inf' H f :=
  sup'_le (α := αᵒᵈ) H f hs

theorem inf'_le {b : β} (h : b ∈ s) : s.inf' ⟨b, h⟩ f ≤ f b :=
  le_sup' (α := αᵒᵈ) f h

set_option linter.docPrime false in
theorem isGLB_inf' {s : Finset α} (hs : s.Nonempty) : IsGLB s (inf' s hs id) :=
  ⟨fun x h => id_eq x ▸ inf'_le id h, fun _ h => Finset.le_inf' hs id h⟩

theorem inf'_le_of_le {a : α} {b : β} (hb : b ∈ s) (h : f b ≤ a) :
    s.inf' ⟨b, hb⟩ f ≤ a := (inf'_le _ hb).trans h

lemma inf'_eq_of_forall {a : α} (h : ∀ b ∈ s, f b = a) : s.inf' H f = a :=
  sup'_eq_of_forall (α := αᵒᵈ) H f h

@[simp]
theorem inf'_const (a : α) : (s.inf' H fun _ => a) = a :=
  sup'_const (α := αᵒᵈ) H a

theorem inf'_union [DecidableEq β] {s₁ s₂ : Finset β} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
    (f : β → α) :
    (s₁ ∪ s₂).inf' (h₁.mono subset_union_left) f = s₁.inf' h₁ f ⊓ s₂.inf' h₂ f :=
  @sup'_union αᵒᵈ _ _ _ _ _ h₁ h₂ _

protected theorem inf'_comm {t : Finset γ} (hs : s.Nonempty) (ht : t.Nonempty) (f : β → γ → α) :
    (s.inf' hs fun b => t.inf' ht (f b)) = t.inf' ht fun c => s.inf' hs fun b => f b c :=
  @Finset.sup'_comm αᵒᵈ _ _ _ _ _ hs ht _

theorem comp_inf'_eq_inf'_comp [SemilatticeInf γ] {s : Finset β} (H : s.Nonempty) {f : β → α}
    (g : α → γ) (g_inf : ∀ x y, g (x ⊓ y) = g x ⊓ g y) : g (s.inf' H f) = s.inf' H (g ∘ f) :=
  comp_sup'_eq_sup'_comp (α := αᵒᵈ) (γ := γᵒᵈ) H g g_inf

theorem inf'_induction {p : α → Prop} (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊓ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.inf' H f) :=
  sup'_induction (α := αᵒᵈ) H f hp hs

theorem inf'_mem (s : Set α) (w : ∀ᵉ (x ∈ s) (y ∈ s), x ⊓ y ∈ s) {ι : Type*}
    (t : Finset ι) (H : t.Nonempty) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.inf' H p ∈ s :=
  inf'_induction H p w h

@[congr]
theorem inf'_congr {t : Finset β} {f g : β → α} (h₁ : s = t) (h₂ : ∀ x ∈ s, f x = g x) :
    s.inf' H f = t.inf' (h₁ ▸ H) g :=
  sup'_congr (α := αᵒᵈ) H h₁ h₂

@[simp]
theorem _root_.map_finset_inf' [SemilatticeInf β] [FunLike F α β] [InfHomClass F α β]
    (f : F) {s : Finset ι} (hs) (g : ι → α) :
    f (s.inf' hs g) = s.inf' hs (f ∘ g) := by
  refine hs.cons_induction ?_ ?_ <;> intros <;> simp [*]

/-- To rewrite from right to left, use `Finset.inf'_comp_eq_image`. -/
@[simp]
theorem inf'_image [DecidableEq β] {s : Finset γ} {f : γ → β} (hs : (s.image f).Nonempty)
    (g : β → α) :
    (s.image f).inf' hs g = s.inf' hs.of_image (g ∘ f) :=
  @sup'_image αᵒᵈ _ _ _ _ _ _ hs _

/-- A version of `Finset.inf'_image` with LHS and RHS reversed.
Also, this lemma assumes that `s` is nonempty instead of assuming that its image is nonempty. -/
lemma inf'_comp_eq_image [DecidableEq β] {s : Finset γ} {f : γ → β} (hs : s.Nonempty) (g : β → α) :
    s.inf' hs (g ∘ f) = (s.image f).inf' (hs.image f) g :=
  sup'_comp_eq_image (α := αᵒᵈ) hs g

/-- To rewrite from right to left, use `Finset.inf'_comp_eq_map`. -/
@[simp]
theorem inf'_map {s : Finset γ} {f : γ ↪ β} (g : β → α) (hs : (s.map f).Nonempty) :
    (s.map f).inf' hs g = s.inf' (map_nonempty.1 hs) (g ∘ f) :=
  sup'_map (α := αᵒᵈ) _ hs

/-- A version of `Finset.inf'_map` with LHS and RHS reversed.
Also, this lemma assumes that `s` is nonempty instead of assuming that its image is nonempty. -/
lemma inf'_comp_eq_map {s : Finset γ} {f : γ ↪ β} (g : β → α) (hs : s.Nonempty) :
    s.inf' hs (g ∘ f) = (s.map f).inf' (map_nonempty.2 hs) g :=
  sup'_comp_eq_map (α := αᵒᵈ) g hs

@[gcongr]
theorem inf'_mono {s₁ s₂ : Finset β} (h : s₁ ⊆ s₂) (h₁ : s₁.Nonempty) :
    s₂.inf' (h₁.mono h) f ≤ s₁.inf' h₁ f :=
  Finset.le_inf' h₁ _ (fun _ hb => inf'_le _ (h hb))

end Inf'

section Sup

variable [SemilatticeSup α] [OrderBot α]

theorem sup'_eq_sup {s : Finset β} (H : s.Nonempty) (f : β → α) : s.sup' H f = s.sup f :=
  le_antisymm (sup'_le H f fun _ => le_sup) (Finset.sup_le fun _ => le_sup' f)

theorem coe_sup_of_nonempty {s : Finset β} (h : s.Nonempty) (f : β → α) :
    (↑(s.sup f) : WithBot α) = s.sup ((↑) ∘ f) := by simp only [← sup'_eq_sup h, coe_sup' h]

end Sup

section Inf

variable [SemilatticeInf α] [OrderTop α]

theorem inf'_eq_inf {s : Finset β} (H : s.Nonempty) (f : β → α) : s.inf' H f = s.inf f :=
  sup'_eq_sup (α := αᵒᵈ) H f

theorem coe_inf_of_nonempty {s : Finset β} (h : s.Nonempty) (f : β → α) :
    (↑(s.inf f) : WithTop α) = s.inf ((↑) ∘ f) :=
  coe_sup_of_nonempty (α := αᵒᵈ) h f

end Inf

@[simp]
protected theorem sup_apply {C : β → Type*} [∀ b : β, SemilatticeSup (C b)]
    [∀ b : β, OrderBot (C b)] (s : Finset α) (f : α → ∀ b : β, C b) (b : β) :
    s.sup f b = s.sup fun a => f a b :=
  comp_sup_eq_sup_comp (fun x : ∀ b : β, C b => x b) (fun _ _ => rfl) rfl

@[simp]
protected theorem inf_apply {C : β → Type*} [∀ b : β, SemilatticeInf (C b)]
    [∀ b : β, OrderTop (C b)] (s : Finset α) (f : α → ∀ b : β, C b) (b : β) :
    s.inf f b = s.inf fun a => f a b :=
  Finset.sup_apply (C := fun b => (C b)ᵒᵈ) s f b

@[simp]
protected theorem sup'_apply {C : β → Type*} [∀ b : β, SemilatticeSup (C b)]
    {s : Finset α} (H : s.Nonempty) (f : α → ∀ b : β, C b) (b : β) :
    s.sup' H f b = s.sup' H fun a => f a b :=
  comp_sup'_eq_sup'_comp H (fun x : ∀ b : β, C b => x b) fun _ _ => rfl

@[simp]
protected theorem inf'_apply {C : β → Type*} [∀ b : β, SemilatticeInf (C b)]
    {s : Finset α} (H : s.Nonempty) (f : α → ∀ b : β, C b) (b : β) :
    s.inf' H f b = s.inf' H fun a => f a b :=
  Finset.sup'_apply (C := fun b => (C b)ᵒᵈ) H f b

@[simp]
theorem toDual_sup' [SemilatticeSup α] {s : Finset ι} (hs : s.Nonempty) (f : ι → α) :
    toDual (s.sup' hs f) = s.inf' hs (toDual ∘ f) :=
  rfl

@[simp]
theorem toDual_inf' [SemilatticeInf α] {s : Finset ι} (hs : s.Nonempty) (f : ι → α) :
    toDual (s.inf' hs f) = s.sup' hs (toDual ∘ f) :=
  rfl

@[simp]
theorem ofDual_sup' [SemilatticeInf α] {s : Finset ι} (hs : s.Nonempty) (f : ι → αᵒᵈ) :
    ofDual (s.sup' hs f) = s.inf' hs (ofDual ∘ f) :=
  rfl

@[simp]
theorem ofDual_inf' [SemilatticeSup α] {s : Finset ι} (hs : s.Nonempty) (f : ι → αᵒᵈ) :
    ofDual (s.inf' hs f) = s.sup' hs (ofDual ∘ f) :=
  rfl

section DistribLattice
variable [DistribLattice α] {s : Finset ι} {t : Finset κ} (hs : s.Nonempty) (ht : t.Nonempty)
  {f : ι → α} {g : κ → α} {a : α}

theorem sup'_inf_distrib_left (f : ι → α) (a : α) :
    a ⊓ s.sup' hs f = s.sup' hs fun i ↦ a ⊓ f i := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => simp
  | cons _ _ _ hs ih => simp_rw [sup'_cons hs, inf_sup_left, ih]

theorem sup'_inf_distrib_right (f : ι → α) (a : α) :
    s.sup' hs f ⊓ a = s.sup' hs fun i => f i ⊓ a := by
  rw [inf_comm, sup'_inf_distrib_left]; simp_rw [inf_comm]

theorem inf'_sup_distrib_left (f : ι → α) (a : α) : a ⊔ s.inf' hs f = s.inf' hs fun i => a ⊔ f i :=
  @sup'_inf_distrib_left αᵒᵈ _ _ _ hs _ _

theorem inf'_sup_distrib_right (f : ι → α) (a : α) : s.inf' hs f ⊔ a = s.inf' hs fun i => f i ⊔ a :=
  @sup'_inf_distrib_right αᵒᵈ _ _ _ hs _ _

end DistribLattice

section LinearOrder

variable [LinearOrder α] {s : Finset ι} (H : s.Nonempty) {f : ι → α} {a : α}

theorem comp_sup_eq_sup_comp_of_nonempty [OrderBot α] [SemilatticeSup β] [OrderBot β]
    {g : α → β} (mono_g : Monotone g) (H : s.Nonempty) : g (s.sup f) = s.sup (g ∘ f) := by
  rw [← Finset.sup'_eq_sup H, ← Finset.sup'_eq_sup H]
  exact Finset.comp_sup'_eq_sup'_comp H g (fun x y ↦ Monotone.map_sup mono_g x y)

@[simp]
theorem le_sup'_iff : a ≤ s.sup' H f ↔ ∃ b ∈ s, a ≤ f b := by
  rw [← WithBot.coe_le_coe, coe_sup', Finset.le_sup_iff (WithBot.bot_lt_coe a)]
  exact exists_congr (fun _ => and_congr_right' WithBot.coe_le_coe)

@[simp]
theorem lt_sup'_iff : a < s.sup' H f ↔ ∃ b ∈ s, a < f b := by
  rw [← WithBot.coe_lt_coe, coe_sup', Finset.lt_sup_iff]
  exact exists_congr (fun _ => and_congr_right' WithBot.coe_lt_coe)

@[simp]
theorem sup'_lt_iff : s.sup' H f < a ↔ ∀ i ∈ s, f i < a := by
  rw [← WithBot.coe_lt_coe, coe_sup', Finset.sup_lt_iff (WithBot.bot_lt_coe a)]
  exact forall₂_congr (fun _ _ => WithBot.coe_lt_coe)

@[simp]
theorem inf'_le_iff : s.inf' H f ≤ a ↔ ∃ i ∈ s, f i ≤ a :=
  le_sup'_iff (α := αᵒᵈ) H

@[simp]
theorem inf'_lt_iff : s.inf' H f < a ↔ ∃ i ∈ s, f i < a :=
  lt_sup'_iff (α := αᵒᵈ) H

@[simp]
theorem lt_inf'_iff : a < s.inf' H f ↔ ∀ i ∈ s, a < f i :=
  sup'_lt_iff (α := αᵒᵈ) H

theorem exists_mem_eq_sup' (f : ι → α) : ∃ i, i ∈ s ∧ s.sup' H f = f i := by
  induction H using Finset.Nonempty.cons_induction with
  | singleton c =>  exact ⟨c, mem_singleton_self c, rfl⟩
  | cons c s hcs hs ih =>
    rcases ih with ⟨b, hb, h'⟩
    rw [sup'_cons hs, h']
    cases le_total (f b) (f c) with
    | inl h => exact ⟨c, mem_cons.2 (Or.inl rfl), sup_eq_left.2 h⟩
    | inr h => exact ⟨b, mem_cons.2 (Or.inr hb), sup_eq_right.2 h⟩

theorem exists_mem_eq_inf' (f : ι → α) : ∃ i, i ∈ s ∧ s.inf' H f = f i :=
  exists_mem_eq_sup' (α := αᵒᵈ) H f

theorem exists_mem_eq_sup [OrderBot α] (s : Finset ι) (h : s.Nonempty) (f : ι → α) :
    ∃ i, i ∈ s ∧ s.sup f = f i :=
  sup'_eq_sup h f ▸ exists_mem_eq_sup' h f

theorem exists_mem_eq_inf [OrderTop α] (s : Finset ι) (h : s.Nonempty) (f : ι → α) :
    ∃ i, i ∈ s ∧ s.inf f = f i :=
  exists_mem_eq_sup (α := αᵒᵈ) s h f

end LinearOrder

end Finset

namespace Multiset

theorem map_finset_sup [DecidableEq α] [DecidableEq β] (s : Finset γ) (f : γ → Multiset β)
    (g : β → α) (hg : Function.Injective g) : map g (s.sup f) = s.sup (map g ∘ f) :=
  Finset.comp_sup_eq_sup_comp _ (fun _ _ => map_union hg) (map_zero _)

theorem count_finset_sup [DecidableEq β] (s : Finset α) (f : α → Multiset β) (b : β) :
    count b (s.sup f) = s.sup fun a => count b (f a) := by
  letI := Classical.decEq α
  refine s.induction ?_ ?_
  · exact count_zero _
  · intro i s _ ih
    rw [Finset.sup_insert, sup_eq_union, count_union, Finset.sup_insert, ih]

theorem mem_sup {α β} [DecidableEq β] {s : Finset α} {f : α → Multiset β} {x : β} :
    x ∈ s.sup f ↔ ∃ v ∈ s, x ∈ f v := by
  induction s using Finset.cons_induction <;> simp [*]

end Multiset

namespace Finset
variable [DecidableEq α] {s : Finset ι} {f : ι → Finset α} {a : α}

set_option linter.docPrime false in
@[simp] lemma mem_sup' (hs) : a ∈ s.sup' hs f ↔ ∃ i ∈ s, a ∈ f i := by
  induction' hs using Nonempty.cons_induction <;> simp [*]

set_option linter.docPrime false in
@[simp] lemma mem_inf' (hs) : a ∈ s.inf' hs f ↔ ∀ i ∈ s, a ∈ f i := by
  induction' hs using Nonempty.cons_induction <;> simp [*]

@[simp] lemma mem_sup : a ∈ s.sup f ↔ ∃ i ∈ s, a ∈ f i := by
  induction' s using cons_induction <;> simp [*]

@[simp]
theorem sup_singleton_apply (s : Finset β) (f : β → α) :
    (s.sup fun b => {f b}) = s.image f := by
  ext a
  rw [mem_sup, mem_image]
  simp only [mem_singleton, eq_comm]

@[deprecated (since := "2025-05-24")]
alias sup_singleton'' := sup_singleton_apply

@[simp]
theorem sup_singleton_eq_self (s : Finset α) : s.sup singleton = s :=
  (s.sup_singleton_apply _).trans image_id

@[deprecated (since := "2025-05-24")]
alias sup_singleton' := sup_singleton_eq_self

end Finset
