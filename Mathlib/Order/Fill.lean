/-
Copyright (c) 2026 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.Completion
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Topology.Order.Basic

/-!
# `OrderEmbedding` of a partial order into a dense and complete linear order

* `DedekindCut.embedLex`: given `b : β`,
  embeds a partial order `α` into `DedekindCut (α ×ₗ β)`.

* `DedekindCut.embedBotTopLex`: given `b : β`,
  embeds a partial order `α` into `WithBot (WithTop (DedekindCut (α ×ₗ β)))`.

The interest of these definitions is that when `β` is linearly ordered, densely ordered
and has no extremal elements, the target orders is dense and,
in the second case, complete. It suffices to take `β := ℚ`.

-/

@[expose] public section

namespace Order

/-- a `Hole` in a partial order is a (nontrivially) empty open interval -/
structure Hole (α : Type*) [PartialOrder α] where
  left : α
  right : α
  left_lt_right : left < right
  Ioo_empty : Set.Ioo left right = ∅

namespace Hole

section PartialOrder

variable {α : Type*} [PartialOrder α]

theorem forall_notMem (x : Hole α) (a : α) : ¬ a ∈ Set.Ioo x.left x.right :=
  Set.eq_empty_iff_forall_notMem.mp x.Ioo_empty a

/- This is not the good definition for a preorder,
because one should identify holes ]a;b[ and ]c;d[ when a ~ c and b ~ d ! -/

/-- The natural preordering on `Hole α` -/
instance : Preorder (Hole α) where
  le x y := x.left ≤ y.left
  lt x y := x.left < y.left
  le_refl _ := by simp
  le_trans x y z h k := Preorder.le_trans _ _ _ h k
  lt_iff_le_not_ge x y := Preorder.lt_iff_le_not_ge x.left y.left

theorem lt_iff_left {x y : Hole α} : x < y ↔ x.left < y.left := Iff.rfl

theorem le_iff_left {x y : Hole α} : x ≤ y ↔ x.left ≤ y.left := Iff.rfl

end PartialOrder

section LinearOrder

variable {α : Type*} [LinearOrder α]

theorem le_right_of_lt_left (x : Hole α) (a : α) (h : x.left < a) : x.right ≤ a := by
  rw [← not_lt]
  intro k
  apply x.forall_notMem a ⟨h, k⟩

theorem le_left_of_lt_right (x : Hole α) (a : α) (h : a < x.right) : a ≤ x.left := by
  rw [← not_lt]
  intro k
  apply x.forall_notMem a ⟨k, h⟩

theorem lt_iff_right {x y : Hole α} : x < y ↔ x.right < y.right := by
  rw [Hole.lt_iff_left]
  constructor
  · intro hl
    rw [← not_le]
    exact fun hr ↦ x.forall_notMem y.left ⟨hl, lt_of_lt_of_le y.left_lt_right hr⟩
  · intro hr
    rw [← not_le]
    exact fun hl ↦ y.forall_notMem x.right ⟨lt_of_le_of_lt hl x.left_lt_right, hr⟩

theorem le_iff_right {x y : Hole α} : x ≤ y ↔ x.right ≤ y.right := by
  simpa [Hole.le_iff_left, ← not_lt, not_iff_not] using lt_iff_right

/-- The natural partial ordering on `Hole α` -/
instance : PartialOrder (Hole α) where
  le_antisymm x y h k := by
    rw [mk.injEq]
    exact ⟨le_antisymm (le_iff_left.mpr h) (le_iff_left.mpr k),
      le_antisymm (le_iff_right.mp h) (le_iff_right.mp k)⟩

theorem left_injective : Function.Injective (fun x : Hole α ↦ x.left) := fun x y h  ↦ by
  rw [mk.injEq]
  refine ⟨h, ?_⟩
  simp [le_antisymm_iff, ← le_iff_right, le_iff_left, h]

theorem right_injective : Function.Injective (fun x : Hole α ↦ x.right) := fun x y h  ↦ by
  rw [mk.injEq]
  refine ⟨?_, h⟩
  simp [le_antisymm_iff, ← le_iff_left, le_iff_right, h]

noncomputable instance : LinearOrder (Hole α) where
  le_total x t := by simp [le_iff_left, Std.le_total]
  toDecidableLE := Classical.decRel LE.le

end LinearOrder

end Hole

/-- The `Fill α f` of a preorder `α` replaces all `x : Hole α` with the preorder `f x`  -/
inductive Fill {α : Type*} [PartialOrder α] (f : Hole α → Type*)
  | some (a : α)
  | hole (x : Hole α) (t : f x)

namespace Fill

section lt

variable {α : Type*} [PartialOrder α] (f : Hole α → Type*) [∀ x, LT (f x)]

instance : LT (Fill f) where
  lt
  | some (a : α), some (b : α) => a < b
  | some (a : α), hole y _ => a ≤ y.left
  | hole x _, some b => x.right ≤ b
  | hole x t, hole y u => x < y ∨ ∃ (h : y = x), t < h ▸ u

variable {f}

theorem some_lt_some_iff {a b : α} : (some a : Fill f) < some b ↔ a < b := Iff.rfl

theorem some_lt_hole_iff {a : α} {y : Hole α} {u : f y} :
    some a < hole y u ↔ a ≤ y.left:= Iff.rfl

theorem hole_lt_some_iff {x : Hole α} {t : f x} {b : α} :
    hole x t < some b ↔ x.right ≤ b := Iff.rfl

theorem hole_lt_hole_iff {x y : Hole α} {t : f x} {u : f y} :
    hole x t < hole y u ↔ x < y ∨ ∃ (h : y = x), t < h ▸ u :=
  Iff.rfl

theorem hole_lt_hole_of_left {x y : Hole α} {t : f x} {u : f y}
    (h : x < y) : hole x t < hole y u := by
  simp [hole_lt_hole_iff, h]

theorem hole_lt_hole_of_right {x : Hole α} {t u : f x} (h : t < u) : hole x t < hole x u := by
  simp [hole_lt_hole_iff, h]

end lt

section le

variable {α : Type*} [PartialOrder α] (f : Hole α → Type*) [∀ x, LE (f x)]

instance : LE (Fill f) where
  le
  | some (a : α), some (b : α) => a ≤ b
  | some (a : α), hole y _ => a ≤ y.left
  | hole y _, some b => y.right ≤ b
  | hole x t, hole y u => x < y ∨ ∃ (h : y = x), t ≤ h ▸ u

theorem some_le_some_iff {a b : α} : (some a : Fill f) ≤ some b ↔ a ≤ b := Iff.rfl

theorem some_le_hole_iff {a : α} {y : Hole α} {u : f y} :
    some a ≤ hole y u ↔ a ≤ y.left:= Iff.rfl

theorem hole_le_some_iff {x : Hole α} {t : f x} {b : α} :
    hole x t ≤ some b ↔ x.right ≤ b := Iff.rfl

theorem hole_le_hole_iff {x y : Hole α} {t : f x} {u : f y} :
    hole x t ≤ hole y u ↔ x < y ∨ ∃ (h : y = x), t ≤ h ▸ u :=
  Iff.rfl

theorem hole_le_hole_of_left {x y : Hole α} {t : f x} {u : f y}
    (h : x < y) : hole x t ≤ hole y u := by
  simp [hole_le_hole_iff, h]

theorem hole_le_hole_iff_right {x : Hole α} {t u : f x} :
    hole x t ≤ hole x u  ↔ t ≤ u := by
  simp [hole_le_hole_iff]

theorem hole_le_hole_of_right {x : Hole α} {t u : f x} (h : t ≤ u) : hole x t ≤ hole x u := by
  simp [hole_le_hole_iff, h]

end le

section partialorder

variable {α : Type*} [PartialOrder α] {f : Hole α → Type*} [∀ x, PartialOrder (f x)]

theorem hole_lt_hole_iff_right {x : Hole α} {t u : f x} :
    hole x t < hole x u ↔ t < u := by
  simp only [hole_lt_hole_iff, exists_const, or_iff_right_iff_imp, lt_irrefl x]
  exact False.elim

end partialorder

section linear

variable {α : Type*} [LinearOrder α] {f : Hole α → Type*}

instance [∀ x, PartialOrder (f x)] : PartialOrder (Fill f) where
  le_refl x := match x with
    | some a => by simp [some_le_some_iff]
    | hole x t => by simp [hole_le_hole_iff]
  le_trans x y z := match x, y, z with
    | some a, some b, some c => by
        simp only [some_le_some_iff]
        exact le_trans
    | some a, hole y u, some c => by
        simp only [some_le_hole_iff, hole_le_some_iff, some_le_some_iff]
        intro h k
        exact le_trans h (le_trans y.left_lt_right.le k)
    | hole x t, some b, some c => by
        simp only [hole_le_some_iff, some_le_some_iff]
        exact le_trans
    | hole x t, hole y u, some c => by
        simp only [hole_le_hole_iff, hole_le_some_iff]
        rintro (h | ⟨e, h⟩) k
        · apply le_trans _ k
          simp [← x.le_iff_right, h.le]
        · simp [← e, k]
    | some a, some b, hole z v => by
        simp only [some_le_some_iff, some_le_hole_iff]
        exact le_trans
    | some a, hole y u, hole z v => by
        simp only [some_le_hole_iff, hole_le_hole_iff]
        rintro h (k | ⟨e, k⟩)
        · apply le_trans h
          rw [← Hole.le_iff_left]
          exact k.le
        · simp [e, h]
    | hole x t, some b, hole z v => by
        rw [hole_le_some_iff, some_le_hole_iff, hole_le_hole_iff]
        intro h k
        apply Or.intro_left
        rw [Hole.lt_iff_left]
        exact lt_of_lt_of_le x.left_lt_right (le_trans h k)
    | hole x t, hole y u, hole z v => by
        simp only [hole_le_hole_iff]
        rintro (h | ⟨e, h⟩) (k | ⟨e', k⟩)
        · left; exact lt_trans h k
        · left; rwa [e']
        · left; rwa [← e]
        · right
          subst e' e
          simp only [exists_const] at h k ⊢
          exact le_trans h k
  le_antisymm x y h k := by
    match x, y with
    | some a, some b =>
        simp only [some_le_some_iff] at h k
        simp only [some.injEq]
        exact le_antisymm h k
    | some a, hole y u =>
        apply False.elim
        simp only [some_le_hole_iff] at h
        simp only [hole_le_some_iff] at k
        exact lt_irrefl a <| lt_of_le_of_lt h (lt_of_lt_of_le y.left_lt_right k)
    | hole x t, some b =>
        apply False.elim
        simp only [hole_le_some_iff] at h
        simp only [some_le_hole_iff] at k
        exact lt_irrefl b <| lt_of_le_of_lt k (lt_of_lt_of_le x.left_lt_right h)
    | hole x t, hole y u =>
        rw [hole_le_hole_iff] at h k
        rcases h with (h | ⟨e, h⟩)
        · apply False.elim
          apply lt_irrefl x
          rcases k with (k | ⟨e', k⟩)
          · exact lt_trans h k
          · exact lt_of_lt_of_eq h e'.symm
        · subst e
          simp only at h
          simp only [lt_self_iff_false, exists_const, false_or] at k
          rw [le_antisymm h k]
  lt_iff_le_not_ge x y := match x, y with
    | some a, some b => by
        simp only [some_lt_some_iff, some_le_some_iff]
        exact lt_iff_le_not_ge
    | some a, hole y u => by
        rw [some_lt_hole_iff, some_le_hole_iff, hole_le_some_iff]
        simp only [iff_self_and]
        intro h k
        exact lt_irrefl a (lt_of_le_of_lt h (lt_of_lt_of_le y.left_lt_right k))
    | hole x t, some b => by
        rw [some_le_hole_iff, hole_le_some_iff, hole_lt_some_iff]
        simp only [iff_self_and]
        intro h k
        exact lt_irrefl b (lt_of_le_of_lt k (lt_of_lt_of_le x.left_lt_right h))
    | hole x t, hole y u => by
        simp only [hole_lt_hole_iff, hole_le_hole_iff]
        rw [not_or, not_exists]
        constructor
        · rintro (h | ⟨e, h⟩)
          · refine ⟨Or.intro_left _ h, Std.not_gt_of_lt h,
              fun e k ↦ lt_irrefl x (lt_of_lt_of_eq h e.symm)⟩
          · refine ⟨Or.intro_right _ ⟨e, h.le⟩, e.symm.not_gt, fun _ ↦ ?_⟩
            subst e
            simp only at h ⊢
            exact Std.not_le_of_gt h
        · rintro ⟨(h | ⟨e, h⟩), k, k'⟩
          · apply Or.intro_left _ h
          · apply Or.intro_right
            subst e
            simp only [lt_iff_le_not_ge, exists_const]
            exact ⟨h, k' rfl⟩

variable [∀ x, LinearOrder (f x)]

/-- The linear ordering on `Fill f` when `a` and all `f x` are linearly ordered -/
noncomputable instance : LinearOrder (Fill f) where
  toDecidableLE := Classical.decRel LE.le
  le_total x y := match x, y with
  | some a, some b => by simp only [some_le_some_iff, le_total]
  | some a, hole y u => by
      simp only [some_le_hole_iff, hole_le_some_iff]
      apply Or.imp (h := le_or_gt a y.left) id
      exact y.le_right_of_lt_left a
  | hole x t, some b => by
      simp only [some_le_hole_iff, hole_le_some_iff]
      apply Or.imp (h := le_or_gt x.right b) id
      exact Hole.le_left_of_lt_right x b
  | hole x t, hole y u => by
      simp only [hole_le_hole_iff]
      rcases lt_trichotomy x y with (h | h | h)
      · left; left; exact h
      · subst h
        simp [le_total]
      · right; left; exact h

instance [∀ x, Nonempty (f x)] [∀ x, NoMinOrder (f x)] [∀ x, NoMaxOrder (f x)]
    [∀ x, DenselyOrdered (f x)] : DenselyOrdered (Fill f) where
  dense x y h := match x, y with
  | some a, some b => by
      simp only [some_lt_some_iff] at h
      rcases (Set.Ioo a b).eq_empty_or_nonempty with (k | ⟨⟨c, k⟩⟩)
      · let x : Hole α := ⟨a, b, h, k⟩
        let t : f x := Classical.ofNonempty
        refine ⟨hole x t, by simp [some_lt_hole_iff, hole_lt_some_iff, x]⟩
      · use some c
        simp [some_lt_some_iff]
        exact k
  | some a, hole y u => by
      obtain ⟨t, ht⟩ := exists_lt u
      use hole y t
      simp only [some_lt_hole_iff, hole_lt_hole_iff] at h ⊢
      simp [h, ht]
  | hole x t, some b => by
      obtain ⟨u, hu⟩ := exists_gt t
      use hole x u
      simp only [hole_lt_hole_iff, hole_lt_some_iff] at h ⊢
      simp [hu, h]
  | hole x t, hole y u => by
      simp only [hole_lt_hole_iff] at h
      rcases h with (h | ⟨e, h⟩)
      · obtain ⟨v, hv⟩ := exists_gt t
        use hole x v
        simp [hole_lt_hole_iff, h, hv]
      · subst e
        simp only at h
        obtain ⟨v, hv, hv'⟩ := DenselyOrdered.dense t u h
        use hole y v
        simp [hole_lt_hole_iff, hv, hv']

theorem continuous_some [TopologicalSpace α] [OrderTopology α]
    [∀ x, Nonempty (f x)] [∀ x, NoMinOrder (f x)] [∀ x, NoMaxOrder (f x)]
    [∀ x, DenselyOrdered (f x)]
    [TopologicalSpace (Fill f)] [OrderTopology (Fill f)] :
    Continuous (fun a ↦ (some a : Fill f)) := by
  rw [OrderTopology.continuous_iff]
  intro x
  simp only [isOpen_iff_nhds]
  match x with
  | some a =>
    refine ⟨fun b h ↦ ?_, fun b h ↦ ?_⟩
    · simp only [Set.mem_preimage, Set.mem_Ioi, some_lt_some_iff] at h
      simp only [Filter.le_principal_iff, mem_nhds_iff]
      rcases (Set.Ioo a b).eq_empty_or_nonempty with (k | ⟨⟨c, k⟩⟩)
      · let x : Hole α := ⟨a, b, h, k⟩
        let t : f x := Classical.ofNonempty
        refine ⟨Set.Ioi a, fun c h ↦ ?_, isOpen_Ioi, h⟩
        simp only [Set.mem_preimage, Set.mem_Ioi, some_lt_some_iff]
        exact h
      · refine ⟨Set.Ioi c, fun x h ↦ ?_, isOpen_Ioi, k.2⟩
        simp only [Set.mem_preimage, Set.mem_Ioi, some_lt_some_iff]
        apply lt_trans k.1 h
    · simp only [Set.mem_preimage, Set.mem_Iio, some_lt_some_iff] at h
      simp only [Filter.le_principal_iff, mem_nhds_iff]
      rcases (Set.Ioo b a).eq_empty_or_nonempty with (k | ⟨⟨c, k⟩⟩)
      · let x : Hole α := ⟨b, a, h, k⟩
        let t : f x := Classical.ofNonempty
        refine ⟨Set.Iio a, fun c h ↦ ?_, isOpen_Iio, h⟩
        simp only [Set.mem_preimage, Set.mem_Iio, some_lt_some_iff]
        exact h
      · refine ⟨Set.Iio c, fun x h ↦ ?_, isOpen_Iio, k.1⟩
        simp only [Set.mem_preimage, Set.mem_Iio, some_lt_some_iff]
        apply lt_trans h k.2
  | hole x t =>
    refine ⟨fun a h ↦ ?_, fun a h ↦ ?_⟩
    · simp only [Set.mem_preimage, Set.mem_Ioi, hole_lt_some_iff] at h
      rw [Filter.le_principal_iff, mem_nhds_iff]
      refine ⟨Set.Ioi x.left, fun b k ↦ ?_, isOpen_Ioi, lt_of_lt_of_le x.left_lt_right h⟩
      simp only [Set.mem_preimage, Set.mem_Ioi, hole_lt_some_iff]
      exact Hole.le_right_of_lt_left x b k
    · simp only [Set.mem_preimage, Set.mem_Iio, some_lt_hole_iff] at h
      rw [Filter.le_principal_iff, mem_nhds_iff]
      refine ⟨Set.Iio x.right, fun b k ↦ ?_, isOpen_Iio, ?_⟩
      · simp only [Set.mem_preimage, Set.mem_Iio, some_lt_hole_iff]
        exact Hole.le_left_of_lt_right x b k
      · apply lt_of_le_of_lt h x.left_lt_right

end linear

end Fill

end Order

end

/-
namespace DedekindCut

open Set Concept

noncomputable def embedLex [PartialOrder α] [PartialOrder β] (b : β) :
    α ↪o DedekindCut (Lex (α × β)) :=
  RelEmbedding.trans principalEmbedding (factorEmbedding (
    ({toFun c := toLex (c, b),
      inj' x y h := by simpa using h,
      map_rel_iff' {x y} := by
        simp [Prod.Lex.toLex_le_toLex, ← le_iff_lt_or_eq] } : α ↪o Lex (α × β)).trans
        principalEmbedding))

variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
variable [LinearOrder β] [TopologicalSpace β] [OrderTopology β]
  [DenselyOrdered β] [NoMinOrder β]

#synth DenselyOrdered (DedekindCut (α ×ₗβ))
#synth CompleteLinearOrder (DedekindCut (α ×ₗβ))

example : @OrderTopology (DedekindCut (α ×ₗ β)) (Preorder.topology _) _ :=
  let := Preorder.topology (DedekindCut (Lex (α × β)))
  { topology_eq_generate_intervals := rfl }

variable [TopologicalSpace (DedekindCut (α ×ₗ β))]
  [OrderTopology (DedekindCut (α ×ₗ β))]

variable {b : β} {ι : α ↪o DedekindCut (α ×ₗ β)}
    (hι : ι = embedLex b)

example : Continuous ι := by
  rw [OrderTopology.continuous_iff]
  intro c
  constructor
  · have H (a : α) : a ∈ ι ⁻¹' Ioi c ↔ toLex (a, b) ∉ c.left := by
      conv_lhs =>
        rw [mem_preimage, mem_Ioi]
        simp [hι, embedLex]
        rw [← not_le, DedekindCut.principal_le_iff]
    rw [← DedekindCut.lowerBounds_right] at H
    simp only [mem_lowerBounds] at H
    push Not at H
    rw [isOpen_iff_nhds]
    intro a ha
    rw [H] at ha
    obtain ⟨x, hx⟩ := ha
    have : ∃ u v, x = toLex (u, v)   := sorry
    rcases this with ⟨u, v, rfl⟩
    simp only [Prod.Lex.lt_iff, ofLex_toLex] at hx
    intro F hF
    simp only [Filter.mem_principal] at hF
    rcases hx.2 with (h | h)
    · sorry
    · sorry
  · sorry

/-
noncomputable def embedBotTopLex (b : β) :
    α ↪o WithBot (WithTop (DedekindCut (Lex (α × β)))) :=
  (RelEmbedding.trans WithTop.coeOrderHom WithBot.coeOrderHom).trans
    (embedLex b).withTopMap.withBotMap
-/

end DedekindCut
-/
