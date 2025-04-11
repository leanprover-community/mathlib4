/-
Copyright (c) 2024 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
import Mathlib.Order.CompleteLattice.SetLike

/-!
# Trees in the sense of descriptive set theory

This file defines trees of depth `ω` in the sense of descriptive set theory as sets of finite
sequences that are stable under taking prefixes.

## Main declarations

* `tree A`: a (possibly infinite) tree of depth at most `ω` with nodes in `A`
-/

namespace Descriptive

/-- A tree is a set of finite sequences, implemented as `List A`, that is stable under
  taking prefixes. For the definition we use the equivalent property `x ++ [a] ∈ T → x ∈ T`,
  which is more convenient to check. We define `tree A` as a complete sublattice of
  `Set (List A)`, which coerces to the type of trees on `A`. -/
def tree (A : Type*) : CompleteSublattice (Set (List A)) :=
  CompleteSublattice.mk' {T | ∀ ⦃x : List A⦄ ⦃a : A⦄, x ++ [a] ∈ T → x ∈ T}
    (by rintro S hS x a ⟨t, ht, hx⟩; use t, ht, hS ht hx)
    (by rintro S hS x a h T hT; exact hS hT <| h T hT)

@[simps!] instance (A : Type*) : SetLike (tree A) (List A) := SetLike.instSubtypeSet

namespace Tree
variable {A : Type*} {S T : tree A}

lemma mem_of_append {x y : List A} (h : x ++ y ∈ T) : x ∈ T := by
  induction y generalizing x with
  | nil => simpa using h
  | cons y ys ih => exact T.prop (ih (by simpa))

lemma mem_of_prefix {x y : List A} (h' : x <+: y) (h : y ∈ T) : x ∈ T := by
  obtain ⟨_, rfl⟩ := h'; exact mem_of_append h

instance : Trans List.IsPrefix (fun x (T : tree A) ↦ x ∈ T) (fun x T ↦ x ∈ T) where
  trans := mem_of_prefix

lemma singleton_mem (T : tree A) {a : A} {x : List A} (h : a :: x ∈ T) : [a] ∈ T :=
  mem_of_prefix ⟨x, rfl⟩ h

@[simp] lemma tree_eq_bot : T = ⊥ ↔ [] ∉ T where
  mp := by rintro rfl; simp
  mpr h := by ext x; simpa using fun h' ↦ h <| mem_of_prefix x.nil_prefix h'

lemma take_mem {n : ℕ} (x : T) : x.val.take n ∈ T :=
  mem_of_prefix (x.val.take_prefix n) x.prop

/-- A variant of `List.take` internally to a tree -/
@[simps] def take (n : ℕ) (x : T) : T := ⟨x.val.take n, take_mem x⟩

@[simp] lemma take_take (m n : ℕ) (x : T) :
  take m (take n x) = take (m ⊓ n) x := by simp [Subtype.ext_iff, List.take_take]

@[simp] lemma take_eq_take {x : T} {m n : ℕ} :
  take m x = take n x ↔ m ⊓ x.val.length = n ⊓ x.val.length := by simp [Subtype.ext_iff]

-- ### `subAt`

variable (T) (x y : List A)
/-- The residual tree obtained by regarding the node x as new root -/
def subAt : tree A := ⟨(x ++ ·)⁻¹' T, fun _ _ _ ↦ mem_of_append (by rwa [List.append_assoc])⟩

@[simp] lemma mem_subAt : y ∈ subAt T x ↔ x ++ y ∈ T := Iff.rfl

@[simp] lemma subAt_nil : subAt T [] = T := rfl

@[simp] lemma subAt_append : subAt (subAt T x) y = subAt T (x ++ y) := by ext; simp

@[gcongr] lemma subAt_mono (h : S ≤ T) : subAt S x ≤ subAt T x :=
  Set.preimage_mono h

/-- A variant of `List.drop` that takes values in `subAt` -/
@[simps] def drop (n : ℕ) (x : T) : subAt T (Tree.take n x).val :=
  ⟨x.val.drop n, by simp⟩

-- ### `pullSub`

/-- Adjoint of `subAt`, given by pasting x before the root of T. Explicitly,
  elements are prefixes of x or x with an element of T appended -/
def pullSub : tree A where
  val := { y | y.take x.length <+: x ∧ y.drop x.length ∈ T }
  property := fun y a ⟨h1, h2⟩ ↦
    ⟨((y.prefix_append [a]).take x.length).trans h1,
    mem_of_prefix ((y.prefix_append [a]).drop x.length) h2⟩

variable {T x y}

lemma mem_pullSub_short (hl : y.length ≤ x.length) :
  y ∈ pullSub T x ↔ y <+: x ∧ [] ∈ T := by
  simp [pullSub, List.take_of_length_le hl, List.drop_eq_nil_iff.mpr hl]

lemma mem_pullSub_long (hl : x.length ≤ y.length) :
  y ∈ pullSub T x ↔ ∃ z ∈ T, y = x ++ z where
  mp := by
    intro ⟨h1, h2⟩; use y.drop x.length, h2
    nth_rw 1 [← List.take_append_drop x.length y]
    simpa [- List.take_append_drop, List.prefix_iff_eq_take, hl] using h1
  mpr := by simp +contextual [pullSub]

@[simp] lemma mem_pullSub_append : x ++ y ∈ pullSub T x ↔ y ∈ T := by simp [mem_pullSub_long]

@[simp] lemma mem_pullSub_self : x ∈ pullSub T x ↔ [] ∈ T := by
  simpa using mem_pullSub_append (y := [])


variable (T x y)

lemma pullSub_subAt : pullSub (subAt T x) x ≤ T := by
  intro y (h : y ∈ pullSub _ x); rcases le_total y.length x.length with h' | h'
  · rw [mem_pullSub_short h'] at h; exact mem_of_prefix h.1 (by simpa using h.2)
  · rw [mem_pullSub_long h'] at h; obtain ⟨_, h, rfl⟩ := h; exact h

@[simp] lemma subAt_pullSub : subAt (pullSub T x) x = T := by
  ext y; simp

@[gcongr] lemma pullSub_mono (h : S ≤ T) x : pullSub S x ≤ pullSub T x :=
  fun _ ⟨h1, h2⟩ ↦ ⟨h1, h h2⟩

lemma pullSub_adjunction (S T : tree A) (x : List A) : pullSub S x ≤ T ↔ S ≤ subAt T x where
  mp _ := by rw [← subAt_pullSub S x]; gcongr
  mpr _ := le_trans (by gcongr) (pullSub_subAt T x)

@[simp] lemma pullSub_nil : pullSub T [] = T := by simp [pullSub]

@[simp] lemma pullSub_append : pullSub (pullSub T y) x = pullSub T (x ++ y) := by
  ext z; rcases le_total x.length z.length with hl | hl
  · by_cases hp : x <+: z
    · obtain ⟨z, rfl⟩ := hp
      simp [pullSub, List.take_add]
    · constructor <;> intro ⟨h, _⟩ <;>
        [skip; replace h := by simpa [List.take_take] using h.take x.length] <;>
        cases hp <| List.prefix_iff_eq_take.mpr (h.eq_of_length (by simpa)).symm
  · rw [mem_pullSub_short hl, mem_pullSub_short (by simp), mem_pullSub_short (by simp; omega)]
    simpa using fun _ ↦ (z.isPrefix_append_of_length hl).symm

end Descriptive.Tree
