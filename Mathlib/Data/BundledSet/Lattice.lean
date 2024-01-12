import Mathlib.Tactic.SetLike
import Mathlib.Data.BundledSet.Basic

open Set

namespace BundledSet

section SemilatticeInf

class InterPred (α : Type*) (p : Set α → Prop) : Prop where
  inter : ∀ s, p s → ∀ t, p t → p (s ∩ t)

variable {α : Type*} {p : Set α → Prop} [InterPred α p]

instance InterPred.and {q : Set α → Prop} [InterPred α q] : InterPred α (fun s ↦ p s ∧ q s) :=
  ⟨fun s hs t ht ↦ ⟨inter s hs.1 t ht.1, inter s hs.2 t ht.2⟩⟩

instance InterPred.mem_implies {x : α} : InterPred α (fun s ↦ x ∈ s → p s) :=
  ⟨fun s hs t ht ⟨hxs, hxt⟩ ↦ inter s (hs hxs) t (ht hxt)⟩

instance InterPred.forall {ι : Sort*} {p : ι → Set α → Prop} [∀ i, InterPred α (p i)] :
    InterPred α (∀ i, p i ·) :=
  ⟨fun s hs t ht i ↦ inter s (hs i) t (ht i)⟩

instance InterPred.mem {x : α} : InterPred α (x ∈ ·) := ⟨fun _s hs _t ht ↦ ⟨hs, ht⟩⟩

protected instance instInf : Inf (BundledSet α p) where
  inf s t := ⟨s ∩ t, InterPred.inter s s.2 t t.2⟩

@[simp]
theorem inf_carrier (s t : BundledSet α p) : (s ⊓ t).carrier = ↑s ∩ ↑t := rfl

@[simp] theorem mem_inf {s t : BundledSet α p} {x : α} : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t := .rfl

protected instance instSemilatticeInf : SemilatticeInf (BundledSet α p) where
  toPartialOrder := BundledSet.instPartialOrder
  toInf := BundledSet.instInf
  __ := carrier_injective.semilatticeInf _ inf_carrier

end SemilatticeInf

section SemilatticeSup

class SupPred (α : Type*) (p : Set α → Prop) (op : outParam <| Set α → Set α → Set α) : Prop where
  sup : ∀ ⦃s⦄, p s → ∀ ⦃t⦄, p t → p (op s t)
  left_subset_sup (s t : BundledSet α p) : s.1 ⊆ op s t
  right_subset_sup (s t : BundledSet α p) : t.1 ⊆ op s t
  sup_subset (s t u : BundledSet α p) : s ≤ u → t ≤ u → op s t ⊆ u

variable {α : Type*} {p : Set α → Prop} {op : Set α → Set α → Set α}

theorem SupPred.mk_union (h : ∀ ⦃s⦄, p s → ∀ ⦃t⦄, p t → p (s ∪ t)) : SupPred α p (· ∪ ·) where
  sup := h
  left_subset_sup _ _ := subset_union_left _ _
  right_subset_sup _ _ := subset_union_right _ _
  sup_subset _ _ _ := union_subset

variable [SupPred α p op]

protected instance instSemilatticeSup : SemilatticeSup (BundledSet α p) where
  sup s t := ⟨op s t, SupPred.sup s.2 t.2⟩
  le_sup_left := SupPred.left_subset_sup
  le_sup_right := SupPred.right_subset_sup
  sup_le := SupPred.sup_subset

@[simp]
lemma carrier_sup_eq_union [SupPred α p (· ∪ ·)] (s t : BundledSet α p) :
    (s ⊔ t).1 = s.1 ∪ t :=
  rfl

lemma mem_sup_left {s t : BundledSet α p} {x : α} (h : x ∈ s) : x ∈ s ⊔ t :=
  (le_sup_left : s ≤ s ⊔ t) h

lemma mem_sup_right {s t : BundledSet α p} {x : α} (h : x ∈ t) : x ∈ s ⊔ t :=
  (le_sup_right : t ≤ s ⊔ t) h

end SemilatticeSup

protected instance instLattice {α : Type*} {p : Set α → Prop} {op : Set α → Set α → Set α}
    [InterPred α p] [SupPred α p op] : Lattice (BundledSet α p) where
  toSemilatticeSup := BundledSet.instSemilatticeSup
  __ := BundledSet.instSemilatticeInf

section OrderTop

class UnivPred (α : Type*) (p : Set α → Prop) : Prop where
  univ : p Set.univ

variable {α : Type*} {p : Set α → Prop} [UnivPred α p]

instance UnivPred.and {q : Set α → Prop} [UnivPred α q] : UnivPred α (fun s ↦ p s ∧ q s) :=
  ⟨univ, univ⟩

instance UnivPred.mem_implies {x : α} : UnivPred α (fun s ↦ x ∈ s → p s) :=
  ⟨fun _ ↦ univ⟩

instance UnivPred.forall {ι : Sort*} {p : ι → Set α → Prop} [∀ i, UnivPred α (p i)] :
    UnivPred α (∀ i, p i ·) :=
  ⟨fun _ ↦ univ⟩

instance UnivPred.mem {x : α} : UnivPred α (x ∈ ·) := ⟨mem_univ x⟩

protected instance instOrderTop : OrderTop (BundledSet α p) where
  top := ⟨univ, UnivPred.univ⟩
  le_top s := subset_univ s.1

@[simp] theorem top_carrier : (⊤ : BundledSet α p).1 = univ := rfl
@[simp] theorem mem_top (x : α) : x ∈ (⊤ : BundledSet α p) := trivial

end OrderTop

section OrderBot

class BotPred (α : Type*) (p : Set α → Prop) (b : outParam (Set α)) : Prop where
  bot : p b
  bot_subset {t} : p t → b ⊆ t

theorem BotPred.mk_empty {α : Type*} {p : Set α → Prop} (h : p ∅) : BotPred α p ∅ :=
  ⟨h, fun _ ↦ empty_subset _⟩

variable {α : Type*} {p : Set α → Prop} {b : Set α} [BotPred α p b]

protected instance instOrderBot : OrderBot (BundledSet α p) where
  bot := ⟨b, BotPred.bot⟩
  bot_le t := BotPred.bot_subset t.2

@[simp] theorem bot_carrier : (⊥ : BundledSet α p).1 = b := rfl
protected theorem mem_bot {x : α} : x ∈ (⊥ : BundledSet α p) ↔ x ∈ b := .rfl

variable [UnivPred α p]

protected instance instBoundedOrder : BoundedOrder (BundledSet α p) where

theorem subsingleton_iff : Subsingleton (BundledSet α p) ↔ b = univ := by
  rw [← subsingleton_iff_bot_eq_top, ← carrier_inj]; rfl

theorem nontrivial_iff : Nontrivial (BundledSet α p) ↔ b ≠ univ := by
  rw [← not_iff_not, not_nontrivial_iff_subsingleton, subsingleton_iff, Ne.def, not_not]

end OrderBot

@[simp]
theorem not_mem_bot {α : Type*} {p : Set α → Prop} [BotPred α p ∅] {x : α} :
    x ∉ (⊥ : BundledSet α p) :=
  not_false

end BundledSet
