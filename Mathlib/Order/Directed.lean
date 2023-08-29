/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Set.Image
import Mathlib.Order.Lattice
import Mathlib.Order.Max
import Mathlib.Order.Bounds.Basic

#align_import order.directed from "leanprover-community/mathlib"@"3efd324a3a31eaa40c9d5bfc669c4fafee5f9423"

/-!
# Directed indexed families and sets

This file defines directed indexed families and directed sets. An indexed family/set is
directed iff each pair of elements has a shared upper bound.

## Main declarations

* `Directed r f`: Predicate stating that the indexed family `f` is `r`-directed.
* `DirectedOn r s`: Predicate stating that the set `s` is `r`-directed.
* `IsDirected α r`: Prop-valued mixin stating that `α` is `r`-directed. Follows the style of the
  unbundled relation classes such as `IsTotal`.
* `ScottContinuous`: Predicate stating that a function between preorders preserves `IsLUB` on
  directed sets.

## References
* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]
-/


open Function

universe u v w

variable {α : Type u} {β : Type v} {ι : Sort w} (r r' s : α → α → Prop)

/-- Local notation for a relation -/
local infixl:50 " ≼ " => r

/-- A family of elements of α is directed (with respect to a relation `≼` on α)
  if there is a member of the family `≼`-above any pair in the family.  -/
def Directed (f : ι → α) :=
  ∀ x y, ∃ z, f x ≼ f z ∧ f y ≼ f z
#align directed Directed

/-- A subset of α is directed if there is an element of the set `≼`-above any
  pair of elements in the set. -/
def DirectedOn (s : Set α) :=
  ∀ x ∈ s, ∀ y ∈ s, ∃ z ∈ s, x ≼ z ∧ y ≼ z
#align directed_on DirectedOn

variable {r r'}

theorem directedOn_iff_directed {s} : @DirectedOn α r s ↔ Directed r (Subtype.val : s → α) := by
  simp [Directed, DirectedOn]; refine' ball_congr fun x _ => by simp [And.comm, and_assoc]
  -- ⊢ (∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → ∃ z, z ∈ s ∧ r x z ∧ r y z) ↔ ∀ (a :  …
                               -- 🎉 no goals
#align directed_on_iff_directed directedOn_iff_directed

alias ⟨DirectedOn.directed_val, _⟩ := directedOn_iff_directed
#align directed_on.directed_coe DirectedOn.directed_val

theorem directedOn_range {f : ι → α} : Directed r f ↔ DirectedOn r (Set.range f) := by
  simp_rw [Directed, DirectedOn, Set.forall_range_iff, Set.exists_range_iff]
  -- 🎉 no goals
#align directed_on_range directedOn_range

-- porting note: This alias was misplaced in `order/compactly_generated.lean` in mathlib3
alias ⟨Directed.directedOn_range, _⟩ := directedOn_range
#align directed.directed_on_range Directed.directedOn_range

-- porting note: `attribute [protected]` doesn't work
-- attribute [protected] Directed.directedOn_range

theorem directedOn_image {s : Set β} {f : β → α} :
    DirectedOn r (f '' s) ↔ DirectedOn (f ⁻¹'o r) s := by
  simp only [DirectedOn, Set.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Order.Preimage]
#align directed_on_image directedOn_image

theorem DirectedOn.mono' {s : Set α} (hs : DirectedOn r s)
    (h : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b → r' a b) : DirectedOn r' s := fun _ hx _ hy =>
  let ⟨z, hz, hxz, hyz⟩ := hs _ hx _ hy
  ⟨z, hz, h hx hz hxz, h hy hz hyz⟩
#align directed_on.mono' DirectedOn.mono'

theorem DirectedOn.mono {s : Set α} (h : DirectedOn r s) (H : ∀ {a b}, r a b → r' a b) :
    DirectedOn r' s :=
  h.mono' fun _ _ _ _ => H
#align directed_on.mono DirectedOn.mono

theorem directed_comp {ι} {f : ι → β} {g : β → α} : Directed r (g ∘ f) ↔ Directed (g ⁻¹'o r) f :=
  Iff.rfl
#align directed_comp directed_comp

theorem Directed.mono {s : α → α → Prop} {ι} {f : ι → α} (H : ∀ a b, r a b → s a b)
    (h : Directed r f) : Directed s f := fun a b =>
  let ⟨c, h₁, h₂⟩ := h a b
  ⟨c, H _ _ h₁, H _ _ h₂⟩
#align directed.mono Directed.mono

-- Porting note: due to some interaction with the local notation, `r` became explicit here in lean3
theorem Directed.mono_comp (r : α → α → Prop) {ι} {rb : β → β → Prop} {g : α → β} {f : ι → α}
    (hg : ∀ ⦃x y⦄, r x y → rb (g x) (g y)) (hf : Directed r f) : Directed rb (g ∘ f) :=
  directed_comp.2 <| hf.mono hg
#align directed.mono_comp Directed.mono_comp

/-- A monotone function on a sup-semilattice is directed. -/
theorem directed_of_sup [SemilatticeSup α] {f : α → β} {r : β → β → Prop}
    (H : ∀ ⦃i j⦄, i ≤ j → r (f i) (f j)) : Directed r f := fun a b =>
  ⟨a ⊔ b, H le_sup_left, H le_sup_right⟩
#align directed_of_sup directed_of_sup

theorem Monotone.directed_le [SemilatticeSup α] [Preorder β] {f : α → β} :
    Monotone f → Directed (· ≤ ·) f :=
  directed_of_sup
#align monotone.directed_le Monotone.directed_le

theorem Antitone.directed_ge [SemilatticeSup α] [Preorder β] {f : α → β} (hf : Antitone f) :
    Directed (· ≥ ·) f :=
  directed_of_sup hf
#align antitone.directed_ge Antitone.directed_ge

/-- A set stable by supremum is `≤`-directed. -/
theorem directedOn_of_sup_mem [SemilatticeSup α] {S : Set α}
    (H : ∀ ⦃i j⦄, i ∈ S → j ∈ S → i ⊔ j ∈ S) : DirectedOn (· ≤ ·) S := fun a ha b hb =>
  ⟨a ⊔ b, H ha hb, le_sup_left, le_sup_right⟩
#align directed_on_of_sup_mem directedOn_of_sup_mem

theorem Directed.extend_bot [Preorder α] [OrderBot α] {e : ι → β} {f : ι → α}
    (hf : Directed (· ≤ ·) f) (he : Function.Injective e) :
    Directed (· ≤ ·) (Function.extend e f ⊥) := by
  intro a b
  -- ⊢ ∃ z, (fun x x_1 => x ≤ x_1) (extend e f ⊥ a) (extend e f ⊥ z) ∧ (fun x x_1 = …
  rcases(em (∃ i, e i = a)).symm with (ha | ⟨i, rfl⟩)
  -- ⊢ ∃ z, (fun x x_1 => x ≤ x_1) (extend e f ⊥ a) (extend e f ⊥ z) ∧ (fun x x_1 = …
  · use b
    -- ⊢ (fun x x_1 => x ≤ x_1) (extend e f ⊥ a) (extend e f ⊥ b) ∧ (fun x x_1 => x ≤ …
    simp [Function.extend_apply' _ _ _ ha]
    -- 🎉 no goals
  rcases(em (∃ i, e i = b)).symm with (hb | ⟨j, rfl⟩)
  -- ⊢ ∃ z, (fun x x_1 => x ≤ x_1) (extend e f ⊥ (e i)) (extend e f ⊥ z) ∧ (fun x x …
  · use e i
    -- ⊢ (fun x x_1 => x ≤ x_1) (extend e f ⊥ (e i)) (extend e f ⊥ (e i)) ∧ (fun x x_ …
    simp [Function.extend_apply' _ _ _ hb]
    -- 🎉 no goals
  rcases hf i j with ⟨k, hi, hj⟩
  -- ⊢ ∃ z, (fun x x_1 => x ≤ x_1) (extend e f ⊥ (e i)) (extend e f ⊥ z) ∧ (fun x x …
  use e k
  -- ⊢ (fun x x_1 => x ≤ x_1) (extend e f ⊥ (e i)) (extend e f ⊥ (e k)) ∧ (fun x x_ …
  simp only [he.extend_apply, *, true_and_iff]
  -- 🎉 no goals
#align directed.extend_bot Directed.extend_bot

/-- An antitone function on an inf-semilattice is directed. -/
theorem directed_of_inf [SemilatticeInf α] {r : β → β → Prop} {f : α → β}
    (hf : ∀ a₁ a₂, a₁ ≤ a₂ → r (f a₂) (f a₁)) : Directed r f := fun x y =>
  ⟨x ⊓ y, hf _ _ inf_le_left, hf _ _ inf_le_right⟩
#align directed_of_inf directed_of_inf

theorem Monotone.directed_ge [SemilatticeInf α] [Preorder β] {f : α → β} (hf : Monotone f) :
    Directed (· ≥ ·) f :=
  directed_of_inf hf
#align monotone.directed_ge Monotone.directed_ge

theorem Antitone.directed_le [SemilatticeInf α] [Preorder β] {f : α → β} (hf : Antitone f) :
    Directed (· ≤ ·) f :=
  directed_of_inf hf
#align antitone.directed_le Antitone.directed_le

/-- A set stable by infimum is `≥`-directed. -/
theorem directedOn_of_inf_mem [SemilatticeInf α] {S : Set α}
    (H : ∀ ⦃i j⦄, i ∈ S → j ∈ S → i ⊓ j ∈ S) : DirectedOn (· ≥ ·) S := fun a ha b hb =>
  ⟨a ⊓ b, H ha hb, inf_le_left, inf_le_right⟩
#align directed_on_of_inf_mem directedOn_of_inf_mem

theorem IsTotal.directed [IsTotal α r] (f : ι → α) : Directed r f := fun i j =>
  Or.casesOn (total_of r (f i) (f j)) (fun h => ⟨j, h, refl _⟩) fun h => ⟨i, refl _, h⟩
#align is_total.directed IsTotal.directed

/-- `IsDirected α r` states that for any elements `a`, `b` there exists an element `c` such that
`r a c` and `r b c`. -/
class IsDirected (α : Type*) (r : α → α → Prop) : Prop where
  /-- For every pair of elements `a` and `b` there is a `c` such that `r a c` and `r b c` -/
  directed (a b : α) : ∃ c, r a c ∧ r b c
#align is_directed IsDirected
#align is_directed.directed IsDirected.directed

theorem directed_of (r : α → α → Prop) [IsDirected α r] (a b : α) : ∃ c, r a c ∧ r b c :=
  IsDirected.directed _ _
#align directed_of directed_of

theorem directed_id [IsDirected α r] : Directed r id := by convert directed_of r
                                                           -- 🎉 no goals
#align directed_id directed_id

theorem directed_id_iff : Directed r id ↔ IsDirected α r :=
  ⟨fun h => ⟨h⟩, @directed_id _ _⟩
#align directed_id_iff directed_id_iff

theorem directedOn_univ [IsDirected α r] : DirectedOn r Set.univ := fun a _ b _ =>
  let ⟨c, hc⟩ := directed_of r a b
  ⟨c, trivial, hc⟩
#align directed_on_univ directedOn_univ

theorem directedOn_univ_iff : DirectedOn r Set.univ ↔ IsDirected α r :=
  ⟨fun h =>
    ⟨fun a b =>
      let ⟨c, _, hc⟩ := h a trivial b trivial
      ⟨c, hc⟩⟩,
    @directedOn_univ _ _⟩
#align directed_on_univ_iff directedOn_univ_iff

-- see Note [lower instance priority]
instance (priority := 100) IsTotal.to_isDirected [IsTotal α r] : IsDirected α r := by
  rw [← directed_id_iff]; exact IsTotal.directed _
  -- ⊢ Directed r id
                          -- 🎉 no goals
#align is_total.to_is_directed IsTotal.to_isDirected

theorem isDirected_mono [IsDirected α r] (h : ∀ ⦃a b⦄, r a b → s a b) : IsDirected α s :=
  ⟨fun a b =>
    let ⟨c, ha, hb⟩ := IsDirected.directed a b
    ⟨c, h ha, h hb⟩⟩
#align is_directed_mono isDirected_mono

theorem exists_ge_ge [LE α] [IsDirected α (· ≤ ·)] (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
  directed_of (· ≤ ·) a b
#align exists_ge_ge exists_ge_ge

theorem exists_le_le [LE α] [IsDirected α (· ≥ ·)] (a b : α) : ∃ c, c ≤ a ∧ c ≤ b :=
  directed_of (· ≥ ·) a b
#align exists_le_le exists_le_le

instance OrderDual.isDirected_ge [LE α] [IsDirected α (· ≤ ·)] : IsDirected αᵒᵈ (· ≥ ·) := by
  assumption
  -- 🎉 no goals
#align order_dual.is_directed_ge OrderDual.isDirected_ge

instance OrderDual.isDirected_le [LE α] [IsDirected α (· ≥ ·)] : IsDirected αᵒᵈ (· ≤ ·) := by
  assumption
  -- 🎉 no goals
#align order_dual.is_directed_le OrderDual.isDirected_le

section Reflexive

protected theorem DirectedOn.insert (h : Reflexive r) (a : α) {s : Set α} (hd : DirectedOn r s)
    (ha : ∀ b ∈ s, ∃ c ∈ s, a ≼ c ∧ b ≼ c) : DirectedOn r (insert a s) := by
  rintro x (rfl | hx) y (rfl | hy)
  · exact ⟨y, Set.mem_insert _ _, h _, h _⟩
    -- 🎉 no goals
  · obtain ⟨w, hws, hwr⟩ := ha y hy
    -- ⊢ ∃ z, z ∈ insert x s ∧ r x z ∧ r y z
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr⟩
    -- 🎉 no goals
  · obtain ⟨w, hws, hwr⟩ := ha x hx
    -- ⊢ ∃ z, z ∈ insert y s ∧ r x z ∧ r y z
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr.symm⟩
    -- 🎉 no goals
  · obtain ⟨w, hws, hwr⟩ := hd x hx y hy
    -- ⊢ ∃ z, z ∈ insert a s ∧ r x z ∧ r y z
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr⟩
    -- 🎉 no goals
#align directed_on.insert DirectedOn.insert

theorem directedOn_singleton (h : Reflexive r) (a : α) : DirectedOn r ({a} : Set α) :=
  fun x hx _ hy => ⟨x, hx, h _, hx.symm ▸ hy.symm ▸ h _⟩
#align directed_on_singleton directedOn_singleton

theorem directedOn_pair (h : Reflexive r) {a b : α} (hab : a ≼ b) : DirectedOn r ({a, b} : Set α) :=
  (directedOn_singleton h _).insert h _ fun c hc => ⟨c, hc, hc.symm ▸ hab, h _⟩
#align directed_on_pair directedOn_pair

theorem directedOn_pair' (h : Reflexive r) {a b : α} (hab : a ≼ b) :
    DirectedOn r ({b, a} : Set α) := by
  rw [Set.pair_comm]
  -- ⊢ DirectedOn r {a, b}
  apply directedOn_pair h hab
  -- 🎉 no goals
#align directed_on_pair' directedOn_pair'

end Reflexive

section Preorder

variable [Preorder α] {a : α}

protected theorem IsMin.isBot [IsDirected α (· ≥ ·)] (h : IsMin a) : IsBot a := fun b =>
  let ⟨_, hca, hcb⟩ := exists_le_le a b
  (h hca).trans hcb
#align is_min.is_bot IsMin.isBot

protected theorem IsMax.isTop [IsDirected α (· ≤ ·)] (h : IsMax a) : IsTop a :=
  h.toDual.isBot
#align is_max.is_top IsMax.isTop

lemma DirectedOn.is_bot_of_is_min {s : Set α} (hd : DirectedOn (· ≥ ·) s)
    {m} (hm : m ∈ s) (hmin : ∀ a ∈ s, a ≤ m → m ≤ a) : ∀ a ∈ s, m ≤ a := fun a as =>
  let ⟨x, xs, xm, xa⟩ := hd m hm a as
  (hmin x xs xm).trans xa
#align directed_on.is_bot_of_is_min DirectedOn.is_bot_of_is_min

lemma DirectedOn.is_top_of_is_max {s : Set α} (hd : DirectedOn (· ≤ ·) s)
    {m} (hm : m ∈ s) (hmax : ∀ a ∈ s, m ≤ a → a ≤ m) : ∀ a ∈ s, a ≤ m :=
  @DirectedOn.is_bot_of_is_min αᵒᵈ _ s hd m hm hmax
#align directed_on.is_top_of_is_max DirectedOn.is_top_of_is_max

theorem isTop_or_exists_gt [IsDirected α (· ≤ ·)] (a : α) : IsTop a ∨ ∃ b, a < b :=
  (em (IsMax a)).imp IsMax.isTop not_isMax_iff.mp
#align is_top_or_exists_gt isTop_or_exists_gt

theorem isBot_or_exists_lt [IsDirected α (· ≥ ·)] (a : α) : IsBot a ∨ ∃ b, b < a :=
  @isTop_or_exists_gt αᵒᵈ _ _ a
#align is_bot_or_exists_lt isBot_or_exists_lt

theorem isBot_iff_isMin [IsDirected α (· ≥ ·)] : IsBot a ↔ IsMin a :=
  ⟨IsBot.isMin, IsMin.isBot⟩
#align is_bot_iff_is_min isBot_iff_isMin

theorem isTop_iff_isMax [IsDirected α (· ≤ ·)] : IsTop a ↔ IsMax a :=
  ⟨IsTop.isMax, IsMax.isTop⟩
#align is_top_iff_is_max isTop_iff_isMax

variable (β) [PartialOrder β]

theorem exists_lt_of_directed_ge [IsDirected β (· ≥ ·)] [Nontrivial β] : ∃ a b : β, a < b := by
  rcases exists_pair_ne β with ⟨a, b, hne⟩
  -- ⊢ ∃ a b, a < b
  rcases isBot_or_exists_lt a with (ha | ⟨c, hc⟩)
  -- ⊢ ∃ a b, a < b
  exacts [⟨a, b, (ha b).lt_of_ne hne⟩, ⟨_, _, hc⟩]
  -- 🎉 no goals
#align exists_lt_of_directed_ge exists_lt_of_directed_ge

theorem exists_lt_of_directed_le [IsDirected β (· ≤ ·)] [Nontrivial β] : ∃ a b : β, a < b :=
  let ⟨a, b, h⟩ := exists_lt_of_directed_ge βᵒᵈ
  ⟨b, a, h⟩
#align exists_lt_of_directed_le exists_lt_of_directed_le

end Preorder

-- see Note [lower instance priority]
instance (priority := 100) SemilatticeSup.to_isDirected_le [SemilatticeSup α] :
    IsDirected α (· ≤ ·) :=
  ⟨fun a b => ⟨a ⊔ b, le_sup_left, le_sup_right⟩⟩
#align semilattice_sup.to_is_directed_le SemilatticeSup.to_isDirected_le

-- see Note [lower instance priority]
instance (priority := 100) SemilatticeInf.to_isDirected_ge [SemilatticeInf α] :
    IsDirected α (· ≥ ·) :=
  ⟨fun a b => ⟨a ⊓ b, inf_le_left, inf_le_right⟩⟩
#align semilattice_inf.to_is_directed_ge SemilatticeInf.to_isDirected_ge

-- see Note [lower instance priority]
instance (priority := 100) OrderTop.to_isDirected_le [LE α] [OrderTop α] : IsDirected α (· ≤ ·) :=
  ⟨fun _ _ => ⟨⊤, le_top _, le_top _⟩⟩
#align order_top.to_is_directed_le OrderTop.to_isDirected_le

-- see Note [lower instance priority]
instance (priority := 100) OrderBot.to_isDirected_ge [LE α] [OrderBot α] : IsDirected α (· ≥ ·) :=
  ⟨fun _ _ => ⟨⊥, bot_le _, bot_le _⟩⟩
#align order_bot.to_is_directed_ge OrderBot.to_isDirected_ge

section ScottContinuous

variable [Preorder α] {a : α}

/-- A function between preorders is said to be Scott continuous if it preserves `IsLUB` on directed
sets. It can be shown that a function is Scott continuous if and only if it is continuous wrt the
Scott topology.

The dual notion

```lean
∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≥ ·) d → ∀ ⦃a⦄, IsGLB d a → IsGLB (f '' d) (f a)
```

does not appear to play a significant role in the literature, so is omitted here.
-/
def ScottContinuous [Preorder β] (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → IsLUB (f '' d) (f a)
#align scott_continuous ScottContinuous

protected theorem ScottContinuous.monotone [Preorder β] {f : α → β} (h : ScottContinuous f) :
    Monotone f := by
  intro a b hab
  -- ⊢ f a ≤ f b
  have e1 : IsLUB (f '' {a, b}) (f b) := by
    apply h
    · exact Set.insert_nonempty _ _
    · exact directedOn_pair le_refl hab
    · rw [IsLUB, upperBounds_insert, upperBounds_singleton,
        Set.inter_eq_self_of_subset_right (Set.Ici_subset_Ici.mpr hab)]
      exact isLeast_Ici
  apply e1.1
  -- ⊢ f a ∈ f '' {a, b}
  rw [Set.image_pair]
  -- ⊢ f a ∈ {f a, f b}
  exact Set.mem_insert _ _
  -- 🎉 no goals
#align scott_continuous.monotone ScottContinuous.monotone

end ScottContinuous
