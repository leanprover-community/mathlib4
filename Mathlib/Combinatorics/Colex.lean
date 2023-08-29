/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.GeomSum

#align_import combinatorics.colex from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Colex

We define the colex ordering for finite sets, and give a couple of important
lemmas and properties relating to it.

The colex ordering likes to avoid large values - it can be thought of on
`Finset ℕ` as the "binary" ordering. That is, order A based on
`∑_{i ∈ A} 2^i`.
It's defined here in a slightly more general way, requiring only `LT α` in
the definition of colex on `Finset α`. In the context of the Kruskal-Katona
theorem, we are interested in particular on how colex behaves for sets of a
fixed size. If the size is 3, colex on ℕ starts
123, 124, 134, 234, 125, 135, 235, 145, 245, 345, ...

## Main statements
* `Colex.hom_lt_iff`: strictly monotone functions preserve colex
* Colex order properties - linearity, decidability and so on.
* `forall_lt_of_colex_lt_of_forall_lt`: if A < B in colex, and everything
  in B is < t, then everything in A is < t. This confirms the idea that
  an enumeration under colex will exhaust all sets using elements < t before
  allowing t to be included.
* `sum_two_pow_le_iff_lt`: colex for α = ℕ is the same as binary
  (this also proves binary expansions are unique)

## See also

Related files are:
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Pi.Lex`: Lexicographic order on `(i : α) → α i`.
* `Data.PSigma.Order`: Lexicographic order on `Σ' i, α i`.
* `Data.Sigma.Order`: Lexicographic order on `Σ i, α i`.
* `Data.Prod.Lex`: Lexicographic order on `α × β`.

## Tags
colex, colexicographic, binary

## References
* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

-/


variable {α : Type*}

open Finset
open BigOperators

/-- We define this type synonym to refer to the colexicographic ordering on finsets
rather than the natural subset ordering.
-/
def Finset.Colex (α) :=
  Finset α
-- Porting note: `deriving Inhabited` doesn't work
#align finset.colex Finset.Colex

instance : Inhabited (Finset.Colex α) := inferInstanceAs (Inhabited (Finset α))

/-- A convenience constructor to turn a `Finset α` into a `Finset.Colex α`, useful in order to
use the colex ordering rather than the subset ordering.
-/
def Finset.toColex {α} (s : Finset α) : Finset.Colex α :=
  s
#align finset.to_colex Finset.toColex

@[simp]
theorem Colex.eq_iff (A B : Finset α) : A.toColex = B.toColex ↔ A = B :=
  Iff.rfl
#align colex.eq_iff Colex.eq_iff

/-- `A` is less than `B` in the colex ordering if the largest thing that's not in both sets is in B.
In other words, `max (A ∆ B) ∈ B` (if the maximum exists).
-/
instance Colex.instLT [LT α] : LT (Finset.Colex α) :=
  ⟨fun A B : Finset α => ∃ k : α, (∀ {x}, k < x → (x ∈ A ↔ x ∈ B)) ∧ k ∉ A ∧ k ∈ B⟩

/-- We can define (≤) in the obvious way. -/
instance Colex.instLE [LT α] : LE (Finset.Colex α) :=
  ⟨fun A B => A < B ∨ A = B⟩

theorem Colex.lt_def [LT α] (A B : Finset α) :
    A.toColex < B.toColex ↔ ∃ k, (∀ {x}, k < x → (x ∈ A ↔ x ∈ B)) ∧ k ∉ A ∧ k ∈ B :=
  Iff.rfl
#align colex.lt_def Colex.lt_def

theorem Colex.le_def [LT α] (A B : Finset α) :
    A.toColex ≤ B.toColex ↔ A.toColex < B.toColex ∨ A = B :=
  Iff.rfl
#align colex.le_def Colex.le_def

/-- If everything in `A` is less than `k`, we can bound the sum of powers. -/
theorem Nat.sum_two_pow_lt {k : ℕ} {A : Finset ℕ} (h₁ : ∀ {x}, x ∈ A → x < k) :
    A.sum (Nat.pow 2) < 2 ^ k := by
  apply lt_of_le_of_lt (sum_le_sum_of_subset fun t => mem_range.2 ∘ h₁)
  -- ⊢ ∑ x in range k, Nat.pow 2 x < 2 ^ k
  have z := geom_sum_mul_add 1 k
  -- ⊢ ∑ x in range k, Nat.pow 2 x < 2 ^ k
  rw [mul_one, one_add_one_eq_two] at z
  -- ⊢ ∑ x in range k, Nat.pow 2 x < 2 ^ k
  rw [← z]
  -- ⊢ ∑ x in range k, Nat.pow 2 x < ∑ i in range k, 2 ^ i + 1
  apply Nat.lt_succ_self
  -- 🎉 no goals
#align nat.sum_two_pow_lt Nat.sum_two_pow_lt

namespace Colex

/-- Strictly monotone functions preserve the colex ordering. -/
theorem hom_lt_iff {β : Type*} [LinearOrder α] [DecidableEq β] [Preorder β] {f : α → β}
    (h₁ : StrictMono f) (A B : Finset α) :
    (A.image f).toColex < (B.image f).toColex ↔ A.toColex < B.toColex := by
  simp only [Colex.lt_def, not_exists, mem_image, exists_prop, not_and]
  -- ⊢ (∃ k, (∀ {x : β}, k < x → ((∃ a, a ∈ A ∧ f a = x) ↔ ∃ a, a ∈ B ∧ f a = x)) ∧ …
  constructor
  -- ⊢ (∃ k, (∀ {x : β}, k < x → ((∃ a, a ∈ A ∧ f a = x) ↔ ∃ a, a ∈ B ∧ f a = x)) ∧ …
  · rintro ⟨k, z, q, k', _, rfl⟩
    -- ⊢ ∃ k, (∀ {x : α}, k < x → (x ∈ A ↔ x ∈ B)) ∧ ¬k ∈ A ∧ k ∈ B
    exact
      ⟨k', @fun x hx => by
        simpa [h₁.injective.eq_iff] using z (h₁ hx), fun t => q _ t rfl, ‹k' ∈ B›⟩
  rintro ⟨k, z, ka, _⟩
  -- ⊢ ∃ k, (∀ {x : β}, k < x → ((∃ a, a ∈ A ∧ f a = x) ↔ ∃ a, a ∈ B ∧ f a = x)) ∧  …
  refine' ⟨f k, @fun x hx => _, _, k, ‹k ∈ B›, rfl⟩
  -- ⊢ (∃ a, a ∈ A ∧ f a = x) ↔ ∃ a, a ∈ B ∧ f a = x
  · constructor
    -- ⊢ (∃ a, a ∈ A ∧ f a = x) → ∃ a, a ∈ B ∧ f a = x
    any_goals
      rintro ⟨x', hx', rfl⟩
      refine' ⟨x', _, rfl⟩
      first |rwa [← z _]|rwa [z _]
      rwa [StrictMono.lt_iff_lt h₁] at hx
  · simp only [h₁.injective, Function.Injective.eq_iff]
    -- ⊢ ∀ (x : α), x ∈ A → ¬x = k
    exact fun x hx => ne_of_mem_of_not_mem hx ka
    -- 🎉 no goals
#align colex.hom_lt_iff Colex.hom_lt_iff

/-- A special case of `Colex.hom_lt_iff` which is sometimes useful. -/
@[simp]
theorem hom_fin_lt_iff {n : ℕ} (A B : Finset (Fin n)) :
    (A.image fun i : Fin n => (i : ℕ)).toColex < (B.image fun i : Fin n => (i : ℕ)).toColex ↔
      A.toColex < B.toColex := by
  refine' Colex.hom_lt_iff _ _ _
  -- ⊢ StrictMono fun i => ↑i
  exact (fun x y k => k)
  -- 🎉 no goals
#align colex.hom_fin_lt_iff Colex.hom_fin_lt_iff

instance [LT α] : IsIrrefl (Finset.Colex α) (· < ·) :=
  ⟨fun _ h => Exists.elim h fun _ ⟨_, a, b⟩ => a b⟩

@[trans]
theorem lt_trans [LinearOrder α] {a b c : Finset.Colex α} : a < b → b < c → a < c := by
  rintro ⟨k₁, k₁z, notinA, inB⟩ ⟨k₂, k₂z, notinB, inC⟩
  -- ⊢ a < c
  cases' lt_or_gt_of_ne (ne_of_mem_of_not_mem inB notinB) with h h
  -- ⊢ a < c
  · refine' ⟨k₂, @fun x hx => _, _, inC⟩
    -- ⊢ x ∈ a ↔ x ∈ c
    rw [← k₂z hx]
    -- ⊢ x ∈ a ↔ x ∈ b
    apply k₁z (Trans.trans h hx)
    -- ⊢ ¬k₂ ∈ a
    rwa [k₁z h]
    -- 🎉 no goals
  · refine' ⟨k₁, @fun x hx => _, notinA, by rwa [← k₂z h]⟩
    -- ⊢ x ∈ a ↔ x ∈ c
    rw [k₁z hx]
    -- ⊢ x ∈ b ↔ x ∈ c
    apply k₂z (Trans.trans h hx)
    -- 🎉 no goals
#align colex.lt_trans Colex.lt_trans

@[trans]
theorem le_trans [LinearOrder α] (a b c : Finset.Colex α) : a ≤ b → b ≤ c → a ≤ c := fun AB BC =>
  AB.elim (fun k => BC.elim (fun t => Or.inl (lt_trans k t)) fun t => t ▸ AB) fun k => k.symm ▸ BC
#align colex.le_trans Colex.le_trans

instance [LinearOrder α] : IsTrans (Finset.Colex α) (· < ·) :=
  ⟨fun _ _ _ => Colex.lt_trans⟩

theorem lt_trichotomy [LinearOrder α] (A B : Finset.Colex α) : A < B ∨ A = B ∨ B < A := by
  by_cases h₁ : A = B
  -- ⊢ A < B ∨ A = B ∨ B < A
  · tauto
    -- 🎉 no goals
  have h : Finset.Nonempty (A \ B ∪ B \ A) := by
    rw [nonempty_iff_ne_empty]
    intro a
    simp only [union_eq_empty_iff, sdiff_eq_empty_iff_subset] at a
    apply h₁ (Subset.antisymm a.1 a.2)
  rcases exists_max_image (A \ B ∪ B \ A) id h with ⟨k, ⟨hk, z⟩⟩
  -- ⊢ A < B ∨ A = B ∨ B < A
  · simp only [mem_union, mem_sdiff] at hk
    -- ⊢ A < B ∨ A = B ∨ B < A
    cases' hk with hk hk
    -- ⊢ A < B ∨ A = B ∨ B < A
    · right
      -- ⊢ A = B ∨ B < A
      right
      -- ⊢ B < A
      refine' ⟨k, @fun t th => _, hk.2, hk.1⟩
      -- ⊢ t ∈ B ↔ t ∈ A
      specialize z t
      -- ⊢ t ∈ B ↔ t ∈ A
      by_contra h₂
      -- ⊢ False
      simp only [mem_union, mem_sdiff, id.def] at z
      -- ⊢ False
      rw [not_iff, iff_iff_and_or_not_and_not, not_not, and_comm] at h₂
      -- ⊢ False
      apply not_le_of_lt th (z h₂)
      -- 🎉 no goals
    · left
      -- ⊢ A < B
      refine' ⟨k, @fun t th => _, hk.2, hk.1⟩
      -- ⊢ t ∈ A ↔ t ∈ B
      specialize z t
      -- ⊢ t ∈ A ↔ t ∈ B
      by_contra h₃
      -- ⊢ False
      simp only [mem_union, mem_sdiff, id.def] at z
      -- ⊢ False
      rw [not_iff, iff_iff_and_or_not_and_not, not_not, and_comm, or_comm] at h₃
      -- ⊢ False
      apply not_le_of_lt th (z h₃)
      -- 🎉 no goals
#align colex.lt_trichotomy Colex.lt_trichotomy

instance [LinearOrder α] : IsTrichotomous (Finset.Colex α) (· < ·) :=
  ⟨lt_trichotomy⟩

instance decidableLt [LinearOrder α] : ∀ {A B : Finset.Colex α}, Decidable (A < B) :=
  show ∀ {A B : Finset α}, Decidable (A.toColex < B.toColex) from @fun A B =>
    decidable_of_iff' (∃ k ∈ B, (∀ x ∈ A ∪ B, k < x → (x ∈ A ↔ x ∈ B)) ∧ k ∉ A)
      (by
        rw [Colex.lt_def]
        -- ⊢ (∃ k, (∀ {x : α}, k < x → (x ∈ A ↔ x ∈ B)) ∧ ¬k ∈ A ∧ k ∈ B) ↔ ∃ k, k ∈ B ∧  …
        apply exists_congr
        -- ⊢ ∀ (a : α), (∀ {x : α}, a < x → (x ∈ A ↔ x ∈ B)) ∧ ¬a ∈ A ∧ a ∈ B ↔ a ∈ B ∧ ( …
        simp only [mem_union, exists_prop, or_imp, and_comm (a := _ ∈ B), and_assoc]
        -- ⊢ ∀ (a : α), (∀ {x : α}, a < x → (x ∈ A ↔ x ∈ B)) ∧ ¬a ∈ A ∧ a ∈ B ↔ (∀ (x : α …
        intro k
        -- ⊢ (∀ {x : α}, k < x → (x ∈ A ↔ x ∈ B)) ∧ ¬k ∈ A ∧ k ∈ B ↔ (∀ (x : α), (x ∈ A → …
        refine' and_congr_left' (forall_congr' _)
        -- ⊢ ∀ (a : α), k < a → (a ∈ A ↔ a ∈ B) ↔ (a ∈ A → k < a → (a ∈ A ↔ a ∈ B)) ∧ (a  …
        tauto)
        -- 🎉 no goals
#align colex.decidable_lt Colex.decidableLt

instance [LinearOrder α] : LinearOrder (Finset.Colex α) :=
  { instLT,
    instLE with
    le_refl := fun A => Or.inr rfl
    le_trans := le_trans
    le_antisymm := fun A B AB BA =>
      AB.elim (fun k => BA.elim (fun t => (asymm k t).elim) fun t => t.symm) id
    le_total := fun A B =>
      (lt_trichotomy A B).elim3 (Or.inl ∘ Or.inl) (Or.inl ∘ Or.inr) (Or.inr ∘ Or.inl)
    -- Porting note: we must give some hints for instances
    decidableLE := by
      letI : DecidableEq (Finset.Colex α) := inferInstanceAs (DecidableEq (Finset α))
      -- ⊢ DecidableRel fun x x_1 => x ≤ x_1
      exact fun A B => inferInstanceAs (Decidable (A < B ∨ A = B))
      -- 🎉 no goals
    decidableLT := inferInstance
    decidableEq := inferInstanceAs (DecidableEq (Finset α))
      -- ⊢ A < B → A ≤ B ∧ ¬B ≤ A
    lt_iff_le_not_le := fun A B => by
        -- ⊢ A ≤ B ∧ ¬B ≤ A
      constructor
        -- ⊢ ¬B ≤ A
      · intro t
        -- ⊢ False
        refine' ⟨Or.inl t, _⟩
          -- 🎉 no goals
        rintro (i | rfl)
          -- 🎉 no goals
        · apply asymm_of _ t i
      -- ⊢ A < B
        · apply irrefl _ t
        -- 🎉 no goals
      rintro ⟨h₁ | rfl, h₂⟩
      -- 🎉 no goals
      · apply h₁
      apply h₂.elim (Or.inr rfl) }

/-- The instances set up let us infer that `(· < ·)` is a strict total order. -/
example [LinearOrder α] : IsStrictTotalOrder (Finset.Colex α) (· < ·) :=
  inferInstance

/-- Strictly monotone functions preserve the colex ordering. -/
theorem hom_le_iff {β : Type*} [LinearOrder α] [LinearOrder β] {f : α → β} (h₁ : StrictMono f)
    (A B : Finset α) : (A.image f).toColex ≤ (B.image f).toColex ↔ A.toColex ≤ B.toColex := by
  rw [le_iff_le_iff_lt_iff_lt, hom_lt_iff h₁]
  -- 🎉 no goals
#align colex.hom_le_iff Colex.hom_le_iff

-- Porting note: fixed the doc
/-- A special case of `hom_le_iff` which is sometimes useful. -/
@[simp]
theorem hom_fin_le_iff {n : ℕ} (A B : Finset (Fin n)) :
    (A.image fun i : Fin n => (i : ℕ)).toColex ≤ (B.image fun i : Fin n => (i : ℕ)).toColex ↔
      A.toColex ≤ B.toColex :=
  Colex.hom_le_iff Fin.val_strictMono _ _
#align colex.hom_fin_le_iff Colex.hom_fin_le_iff

/-- If `A` is before `B` in colex, and everything in `B` is small, then everything in `A` is small.
-/
theorem forall_lt_of_colex_lt_of_forall_lt [LinearOrder α] {A B : Finset α} (t : α)
    (h₁ : A.toColex < B.toColex) (h₂ : ∀ x ∈ B, x < t) : ∀ x ∈ A, x < t := by
  rw [Colex.lt_def] at h₁
  -- ⊢ ∀ (x : α), x ∈ A → x < t
  rcases h₁ with ⟨k, z, _, _⟩
  -- ⊢ ∀ (x : α), x ∈ A → x < t
  intro x hx
  -- ⊢ x < t
  apply lt_of_not_ge
  -- ⊢ ¬x ≥ t
  intro a
  -- ⊢ False
  refine' not_lt_of_ge a (h₂ x _)
  -- ⊢ x ∈ B
  rwa [← z]
  -- ⊢ k < x
  apply lt_of_lt_of_le (h₂ k ‹_›) a
  -- 🎉 no goals
#align colex.forall_lt_of_colex_lt_of_forall_lt Colex.forall_lt_of_colex_lt_of_forall_lt

/-- `s.toColex < {r}.toColex` iff all elements of `s` are less than `r`. -/
theorem lt_singleton_iff_mem_lt [LinearOrder α] {r : α} {s : Finset α} :
    s.toColex < ({r} : Finset α).toColex ↔ ∀ x ∈ s, x < r := by
  simp only [lt_def, mem_singleton, ← and_assoc, exists_eq_right]
  -- ⊢ (∀ {x : α}, r < x → (x ∈ s ↔ x = r)) ∧ ¬r ∈ s ↔ ∀ (x : α), x ∈ s → x < r
  constructor
  -- ⊢ (∀ {x : α}, r < x → (x ∈ s ↔ x = r)) ∧ ¬r ∈ s → ∀ (x : α), x ∈ s → x < r
  · intro t x hx
    -- ⊢ x < r
    rw [← not_le]
    -- ⊢ ¬r ≤ x
    intro h
    -- ⊢ False
    rcases lt_or_eq_of_le h with (h₁ | rfl)
    -- ⊢ False
    · exact ne_of_irrefl h₁ ((t.1 h₁).1 hx).symm
      -- 🎉 no goals
    · exact t.2 hx
      -- 🎉 no goals
  · exact fun h =>
      ⟨fun {z} hz => ⟨fun i => (asymm hz (h _ i)).elim, fun i => (hz.ne' i).elim⟩,
          by simpa using h r⟩
#align colex.lt_singleton_iff_mem_lt Colex.lt_singleton_iff_mem_lt

-- Porting note: fixed the doc
/-- If `{r}` is less than or equal to s in the colexicographical sense,
  then s contains an element greater than or equal to r. -/
theorem mem_le_of_singleton_le [LinearOrder α] {r : α} {s : Finset α} :
    ({r} : Finset α).toColex ≤ s.toColex ↔ ∃ x ∈ s, r ≤ x := by
  simp only [← not_lt]
  -- ⊢ ¬toColex s < toColex {r} ↔ ∃ x, x ∈ s ∧ ¬x < r
  simp [lt_singleton_iff_mem_lt]
  -- 🎉 no goals
#align colex.mem_le_of_singleton_le Colex.mem_le_of_singleton_le

/-- Colex is an extension of the base ordering on α. -/
theorem singleton_lt_iff_lt [LinearOrder α] {r s : α} :
    ({r} : Finset α).toColex < ({s} : Finset α).toColex ↔ r < s := by simp [lt_singleton_iff_mem_lt]
                                                                      -- 🎉 no goals
#align colex.singleton_lt_iff_lt Colex.singleton_lt_iff_lt

/-- Colex is an extension of the base ordering on α. -/
theorem singleton_le_iff_le [LinearOrder α] {r s : α} :
    ({r} : Finset α).toColex ≤ ({s} : Finset α).toColex ↔ r ≤ s := by
  rw [le_iff_le_iff_lt_iff_lt, singleton_lt_iff_lt]
  -- 🎉 no goals
#align colex.singleton_le_iff_le Colex.singleton_le_iff_le

/-- Colex doesn't care if you remove the other set -/
@[simp]
theorem sdiff_lt_sdiff_iff_lt [LT α] [DecidableEq α] (A B : Finset α) :
    (A \ B).toColex < (B \ A).toColex ↔ A.toColex < B.toColex := by
  rw [Colex.lt_def, Colex.lt_def]
  -- ⊢ (∃ k, (∀ {x : α}, k < x → (x ∈ A \ B ↔ x ∈ B \ A)) ∧ ¬k ∈ A \ B ∧ k ∈ B \ A) …
  apply exists_congr
  -- ⊢ ∀ (a : α), (∀ {x : α}, a < x → (x ∈ A \ B ↔ x ∈ B \ A)) ∧ ¬a ∈ A \ B ∧ a ∈ B …
  intro k
  -- ⊢ (∀ {x : α}, k < x → (x ∈ A \ B ↔ x ∈ B \ A)) ∧ ¬k ∈ A \ B ∧ k ∈ B \ A ↔ (∀ { …
  simp only [mem_sdiff, not_and, not_not]
  -- ⊢ (∀ {x : α}, k < x → (x ∈ A ∧ ¬x ∈ B ↔ x ∈ B ∧ ¬x ∈ A)) ∧ (k ∈ A → k ∈ B) ∧ k …
  constructor
  -- ⊢ (∀ {x : α}, k < x → (x ∈ A ∧ ¬x ∈ B ↔ x ∈ B ∧ ¬x ∈ A)) ∧ (k ∈ A → k ∈ B) ∧ k …
  · rintro ⟨z, kAB, kB, kA⟩
    -- ⊢ (∀ {x : α}, k < x → (x ∈ A ↔ x ∈ B)) ∧ ¬k ∈ A ∧ k ∈ B
    refine' ⟨_, kA, kB⟩
    -- ⊢ ∀ {x : α}, k < x → (x ∈ A ↔ x ∈ B)
    · intro x hx
      -- ⊢ x ∈ A ↔ x ∈ B
      specialize z hx
      -- ⊢ x ∈ A ↔ x ∈ B
      tauto
      -- 🎉 no goals
  · rintro ⟨z, kA, kB⟩
    -- ⊢ (∀ {x : α}, k < x → (x ∈ A ∧ ¬x ∈ B ↔ x ∈ B ∧ ¬x ∈ A)) ∧ (k ∈ A → k ∈ B) ∧ k …
    refine' ⟨_, fun _ => kB, kB, kA⟩
    -- ⊢ ∀ {x : α}, k < x → (x ∈ A ∧ ¬x ∈ B ↔ x ∈ B ∧ ¬x ∈ A)
    intro x hx
    -- ⊢ x ∈ A ∧ ¬x ∈ B ↔ x ∈ B ∧ ¬x ∈ A
    rw [z hx]
    -- 🎉 no goals
#align colex.sdiff_lt_sdiff_iff_lt Colex.sdiff_lt_sdiff_iff_lt

/-- Colex doesn't care if you remove the other set -/
@[simp]
theorem sdiff_le_sdiff_iff_le [LinearOrder α] (A B : Finset α) :
    (A \ B).toColex ≤ (B \ A).toColex ↔ A.toColex ≤ B.toColex := by
  rw [le_iff_le_iff_lt_iff_lt, sdiff_lt_sdiff_iff_lt]
  -- 🎉 no goals
#align colex.sdiff_le_sdiff_iff_le Colex.sdiff_le_sdiff_iff_le

theorem empty_toColex_lt [LinearOrder α] {A : Finset α} (hA : A.Nonempty) :
    (∅ : Finset α).toColex < A.toColex := by
  rw [Colex.lt_def]
  -- ⊢ ∃ k, (∀ {x : α}, k < x → (x ∈ ∅ ↔ x ∈ A)) ∧ ¬k ∈ ∅ ∧ k ∈ A
  refine' ⟨max' _ hA, _, by simp, max'_mem _ _⟩
  -- ⊢ ∀ {x : α}, max' A hA < x → (x ∈ ∅ ↔ x ∈ A)
  simp only [false_iff_iff, not_mem_empty]
  -- ⊢ ∀ {x : α}, max' A hA < x → ¬x ∈ A
  intro x hx t
  -- ⊢ False
  apply not_le_of_lt hx (le_max' _ _ t)
  -- 🎉 no goals
#align colex.empty_to_colex_lt Colex.empty_toColex_lt

/-- If `A ⊂ B`, then `A` is less than `B` in the colex order. Note the converse does not hold, as
`⊆` is not a linear order. -/
theorem colex_lt_of_ssubset [LinearOrder α] {A B : Finset α} (h : A ⊂ B) :
    A.toColex < B.toColex := by
  rw [← sdiff_lt_sdiff_iff_lt, sdiff_eq_empty_iff_subset.2 h.1]
  -- ⊢ toColex ∅ < toColex (B \ A)
  exact empty_toColex_lt (by simpa [Finset.Nonempty] using exists_of_ssubset h)
  -- 🎉 no goals
#align colex.colex_lt_of_ssubset Colex.colex_lt_of_ssubset

@[simp]
theorem empty_toColex_le [LinearOrder α] {A : Finset α} : (∅ : Finset α).toColex ≤ A.toColex := by
  rcases A.eq_empty_or_nonempty with (rfl | hA)
  -- ⊢ toColex ∅ ≤ toColex ∅
  · simp
    -- 🎉 no goals
  · apply (empty_toColex_lt hA).le
    -- 🎉 no goals
#align colex.empty_to_colex_le Colex.empty_toColex_le

/-- If `A ⊆ B`, then `A ≤ B` in the colex order. Note the converse does not hold, as `⊆` is not a
linear order. -/
theorem colex_le_of_subset [LinearOrder α] {A B : Finset α} (h : A ⊆ B) :
    A.toColex ≤ B.toColex := by
  rw [← sdiff_le_sdiff_iff_le, sdiff_eq_empty_iff_subset.2 h]
  -- ⊢ toColex ∅ ≤ toColex (B \ A)
  apply empty_toColex_le
  -- 🎉 no goals
#align colex.colex_le_of_subset Colex.colex_le_of_subset

/-- The function from finsets to finsets with the colex order is a relation homomorphism. -/
@[simps]
def toColexRelHom [LinearOrder α] :
    ((· ⊆ ·) : Finset α → Finset α → Prop) →r ((· ≤ ·) : Finset.Colex α → Finset.Colex α → Prop)
    where
  toFun := Finset.toColex
  map_rel' {_ _} := colex_le_of_subset
#align colex.to_colex_rel_hom Colex.toColexRelHom

instance [LinearOrder α] : OrderBot (Finset.Colex α) where
  bot := (∅ : Finset α).toColex
  bot_le _ := empty_toColex_le

instance [LinearOrder α] [Fintype α] : OrderTop (Finset.Colex α) where
  top := Finset.univ.toColex
  le_top _ := colex_le_of_subset (subset_univ _)

instance [LinearOrder α] : Lattice (Finset.Colex α) :=
  { inferInstanceAs (SemilatticeSup (Finset.Colex α)),
    inferInstanceAs (SemilatticeInf (Finset.Colex α)) with }

instance [LinearOrder α] [Fintype α] : BoundedOrder (Finset.Colex α) :=
  { inferInstanceAs (OrderTop (Finset.Colex α)),
    inferInstanceAs (OrderBot (Finset.Colex α)) with }

/-- For subsets of ℕ, we can show that colex is equivalent to binary. -/
theorem sum_two_pow_lt_iff_lt (A B : Finset ℕ) :
    ((∑ i in A, 2 ^ i) < ∑ i in B, 2 ^ i) ↔ A.toColex < B.toColex := by
  have z : ∀ A B : Finset ℕ, A.toColex < B.toColex → ∑ i in A, 2 ^ i < ∑ i in B, 2 ^ i := by
    intro A B
    rw [← sdiff_lt_sdiff_iff_lt, Colex.lt_def]
    rintro ⟨k, z, kA, kB⟩
    rw [← sdiff_union_inter A B]
    conv_rhs => rw [← sdiff_union_inter B A]
    rw [sum_union (disjoint_sdiff_inter _ _), sum_union (disjoint_sdiff_inter _ _), inter_comm,
      add_lt_add_iff_right]
    apply lt_of_lt_of_le (@Nat.sum_two_pow_lt k (A \ B) _)
    · apply single_le_sum (fun _ _ => Nat.zero_le _) kB
    intro x hx
    apply lt_of_le_of_ne (le_of_not_lt _)
    · apply ne_of_mem_of_not_mem hx kA
    -- Porting note: `intro` required because `apply` behaves differently
    intro kx
    have := (z kx).1 hx
    rw [mem_sdiff] at this hx
    exact hx.2 this.1
  refine'
    ⟨fun h => (lt_trichotomy A B).resolve_right fun h₁ => h₁.elim _ (not_lt_of_gt h ∘ z _ _), z A B⟩
  rintro rfl
  -- ⊢ False
  apply irrefl _ h
  -- 🎉 no goals
#align colex.sum_two_pow_lt_iff_lt Colex.sum_two_pow_lt_iff_lt

/-- For subsets of ℕ, we can show that colex is equivalent to binary. -/
theorem sum_two_pow_le_iff_lt (A B : Finset ℕ) :
    ((∑ i in A, 2 ^ i) ≤ ∑ i in B, 2 ^ i) ↔ A.toColex ≤ B.toColex := by
  rw [le_iff_le_iff_lt_iff_lt, sum_two_pow_lt_iff_lt]
  -- 🎉 no goals
#align colex.sum_two_pow_le_iff_lt Colex.sum_two_pow_le_iff_lt

end Colex
