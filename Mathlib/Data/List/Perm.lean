import Mathlib.Init.Set
import Mathlib.Data.List.Pairwise

namespace List

/-- `Perm l₁ l₂` or `l₁ ~ l₂` asserts that `l₁` and `l₂` are Permutations
  of each other. This is defined by induction using pairwise swaps. -/
inductive Perm {α} : List α → List α → Prop
| nil   : Perm [] []
| cons  : ∀ (x : α) {l₁ l₂ : List α}, Perm l₁ l₂ → Perm (x::l₁) (x::l₂)
| swap  : ∀ (x y : α) (l : List α), Perm (y::x::l) (x::y::l)
| trans : ∀ {l₁ l₂ l₃ : List α}, Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃

open Perm

infixl:50 " ~ " => Perm

protected theorem Perm.refl : ∀ (l : List α), l ~ l
| []      => Perm.nil
| (x::xs) => (Perm.refl xs).cons x

protected theorem Perm.symm {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₂ ~ l₁ := by
induction p with
| nil => exact Perm.nil
| cons x _ ih => exact Perm.cons x ih
| swap x y l => exact Perm.swap y x l
| trans _ _ ih₁ ih₂ => exact Perm.trans ih₂ ih₁

theorem Perm_comm {l₁ l₂ : List α} : l₁ ~ l₂ ↔ l₂ ~ l₁ := ⟨Perm.symm, Perm.symm⟩

theorem Perm.swap' (x y : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) : y::x::l₁ ~ x::y::l₂ :=
  have h1 : y :: l₁ ~ y :: l₂ := Perm.cons y p
  have h2 : x :: y :: l₁ ~ x :: y :: l₂ := Perm.cons x h1
  have h3 : y :: x :: l₁ ~ x :: y :: l₁ := Perm.swap x y l₁
  Perm.trans h3 h2

theorem Perm.Equivalence : Equivalence (@Perm α) := ⟨Perm.refl, Perm.symm, Perm.trans⟩

instance (α : Type u) : Setoid (List α) := ⟨Perm, Perm.Equivalence⟩

theorem Perm.subset {α : Type u} {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁ ⊆ l₂ := by
  induction p with
  | nil => exact nil_subset _
  | cons _ _ ih => exact cons_subset_cons _ ih
  | swap x y l =>
    intro a
    rw [mem_cons]
    exact fun
    | Or.inl rfl => Mem.tail _ (Mem.head ..)
    | Or.inr (Mem.head ..) => Mem.head ..
    | Or.inr (Mem.tail _ a_mem_l) => Mem.tail _ (Mem.tail _ a_mem_l)
  | trans _ _ ih₁ ih₂ => exact Subset.trans ih₁ ih₂

theorem perm_middle {a : α} : ∀ {l₁ l₂ : List α}, l₁++a::l₂ ~ a::(l₁++l₂)
| [], _ => Perm.refl _
| b::l₁, l₂ =>
  let h2 := @perm_middle α a l₁ l₂
  (h2.cons _).trans (swap a b _)

set_option linter.unusedVariables false in -- FIXME: lean4#1214
theorem perm_insertNth {x : α} : ∀ {l : List α} {n : Nat}, n ≤ l.length →
  insertNth n x l ~ x :: l
| [], 0, _ => Perm.refl _
| [], _+1, h => False.elim (Nat.not_succ_le_zero _ h)
| _::_, 0, _ => Perm.refl _
| _::_, _+1, h =>
  Perm.trans
    (Perm.cons _ (perm_insertNth (Nat.le_of_succ_le_succ h)))
    (Perm.swap _ _ _)

theorem Perm.mem_iff {a : α} {l₁ l₂ : List α} (h : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ :=
  Iff.intro (fun m => h.subset m) fun m => h.symm.subset m

/-- The way Lean 4 computes the motive with `elabAsElim` has changed
relative to the behaviour of `elab_as_eliminator` in Lean 3.
See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Potential.20elaboration.20bug.20with.20.60elabAsElim.60/near/299573172
for an explanation of the change made here relative to mathlib3.
-/
@[elabAsElim]
theorem perm_induction_on
    {P : (l₁ : List α) → (l₂ : List α) → l₁ ~ l₂ → Prop} {l₁ l₂ : List α} (p : l₁ ~ l₂)
    (h₁ : P [] [] .nil)
    (h₂ : ∀ x l₁ l₂, (h : l₁ ~ l₂) → P l₁ l₂ h → P (x :: l₁) (x :: l₂) (.cons x h))
    (h₃ : ∀ x y l₁ l₂, (h : l₁ ~ l₂) → P l₁ l₂ h →
      P (y :: x :: l₁) (x :: y :: l₂) (.trans (.swap x y _) (.cons _ (.cons _ h))))
    (h₄ : ∀ l₁ l₂ l₃, (h₁ : l₁ ~ l₂) → (h₂ : l₂ ~ l₃) → P l₁ l₂ h₁ → P l₂ l₃ h₂ →
      P l₁ l₃ (.trans h₁ h₂)) : P l₁ l₂ p :=
  have P_refl : ∀ l, P l l (.refl l) :=
    fun l => List.recOn l h₁ fun x xs ih => h₂ x xs xs (Perm.refl xs) ih
  Perm.recOn p h₁ h₂ (fun x y l => h₃ x y l l (Perm.refl l) (P_refl l)) @h₄

theorem perm_inv_core {a : α} {l₁ l₂ r₁ r₂ : List α} :
    l₁ ++ a :: r₁ ~ l₂ ++ a :: r₂ → l₁ ++ r₁ ~ l₂ ++ r₂ := by
  generalize e₁ : l₁ ++ a :: r₁ = s₁
  generalize e₂ : l₂ ++ a :: r₂ = s₂
  intro p
  revert l₁ l₂ r₁ r₂ e₁ e₂
  refine' @(perm_induction_on p _ _ _ _)
  · intro l₁ l₂ r₁ r₂ e₁ _
    apply (not_mem_nil a).elim
    rw [← e₁]
    simp
  · intro x t₁ t₂ p w l₁ l₂ r₁ r₂ e₁ e₂
    rcases l₁ with ⟨⟩ | ⟨y,l₁⟩ <;> rcases l₂ with ⟨⟩ | ⟨z,l₂⟩ <;> dsimp at e₁ e₂
      <;> injections <;> subst x
    · subst t₁ t₂
      exact p
    · subst z t₁ t₂
      exact p.trans perm_middle
    · subst y t₁ t₂
      exact perm_middle.symm.trans p
    · subst z t₁ t₂
      exact (w rfl rfl).cons y
  · intro x y t₁ t₂ p w l₁ l₂ r₁ r₂ e₁ e₂
    rcases l₁ with (_ | ⟨y, _ | ⟨z, l₁⟩⟩) <;>
      rcases l₂ with (_ | ⟨u, _ | ⟨v, l₂⟩⟩) <;> dsimp at e₁ e₂ <;> injections <;> subst x y
    · subst r₁ r₂
      exact p.cons a
    · subst r₁ r₂
      exact p.cons u
    · subst r₁ v t₂
      exact (p.trans perm_middle).cons u
    · subst r₁ r₂
      exact p.cons y
    · subst r₁ r₂ y u
      exact p.cons a
    · subst r₁ u v t₂
      exact ((p.trans perm_middle).cons y).trans (swap _ _ _)
    · subst r₂ z t₁
      exact (perm_middle.symm.trans p).cons y
    · subst r₂ y z t₁
      exact (swap _ _ _).trans ((perm_middle.symm.trans p).cons u)
    · subst u v t₁ t₂
      exact (w rfl rfl).swap' _ _
  · intro t₁ t₂ t₃ p₁ p₂ w₁ w₂ l₁ l₂ r₁ r₂ e₁ e₂
    subst t₁ t₃
    have : a ∈ t₂ :=
      p₁.subset
        (by simp)
    rcases mem_split this with ⟨l₂, r₂, e₂⟩
    subst t₂
    exact (w₁ rfl rfl).trans (w₂ rfl rfl)

theorem Perm.cons_inv {a : α} {l₁ l₂ : List α} : a :: l₁ ~ a :: l₂ → l₁ ~ l₂ :=
  @perm_inv_core _ _ [] [] _ _

theorem Perm.length_eq {l₁ l₂ : List α} (p : l₁ ~ l₂) : length l₁ = length l₂ := by
  induction p with
  | nil => simp
  | cons _ _ ih => simp [ih]
  | swap _ _ l => simp
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem Perm.eq_nil {l : List α} (p : l ~ []) : l = [] :=
  eq_nil_of_length_eq_zero p.length_eq

theorem Perm.nil_eq {l : List α} (p : [] ~ l) : [] = l :=
  p.symm.eq_nil.symm

theorem Perm.pairwise_iff {R : α → α → Prop} (S : symmetric R) :
  ∀ {l₁ l₂ : List α}, l₁ ~ l₂ → (Pairwise R l₁ ↔ Pairwise R l₂) := by
  suffices ∀ {l₁ l₂}, l₁ ~ l₂ → Pairwise R l₁ → Pairwise R l₂ from
    fun l₁ l₂ p => ⟨this p, this p.symm⟩
  intros l₁ l₂ p d
  induction d generalizing l₂ with
  | nil =>
      rw [←p.nil_eq]
      constructor
  | @cons a h d _ ih =>
      have : a ∈ l₂ := p.subset (mem_cons_self _ _)
      rcases mem_split this with ⟨s₂, t₂, rfl⟩
      have p' := (p.trans perm_middle).cons_inv
      refine' (pairwise_middle S).2 (Pairwise_cons.2 ⟨_, ih p'⟩)
      intro b m
      exact d _ (p'.symm.subset m)

theorem Perm.nodup_iff {l₁ l₂ : List α} : l₁ ~ l₂ → (Nodup l₁ ↔ Nodup l₂) :=
  Perm.pairwise_iff <| @Ne.symm α
