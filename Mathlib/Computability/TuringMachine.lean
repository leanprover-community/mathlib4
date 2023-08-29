/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Vector.Basic
import Mathlib.Data.PFun
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Basic
import Mathlib.Tactic.ApplyFun

#align_import computability.turing_machine from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# Turing machines

This file defines a sequence of simple machine languages, starting with Turing machines and working
up to more complex languages based on Wang B-machines.

## Naming conventions

Each model of computation in this file shares a naming convention for the elements of a model of
computation. These are the parameters for the language:

* `Γ` is the alphabet on the tape.
* `Λ` is the set of labels, or internal machine states.
* `σ` is the type of internal memory, not on the tape. This does not exist in the TM0 model, and
  later models achieve this by mixing it into `Λ`.
* `K` is used in the TM2 model, which has multiple stacks, and denotes the number of such stacks.

All of these variables denote "essentially finite" types, but for technical reasons it is
convenient to allow them to be infinite anyway. When using an infinite type, we will be interested
to prove that only finitely many values of the type are ever interacted with.

Given these parameters, there are a few common structures for the model that arise:

* `Stmt` is the set of all actions that can be performed in one step. For the TM0 model this set is
  finite, and for later models it is an infinite inductive type representing "possible program
  texts".
* `Cfg` is the set of instantaneous configurations, that is, the state of the machine together with
  its environment.
* `Machine` is the set of all machines in the model. Usually this is approximately a function
  `Λ → Stmt`, although different models have different ways of halting and other actions.
* `step : Cfg → Option Cfg` is the function that describes how the state evolves over one step.
  If `step c = none`, then `c` is a terminal state, and the result of the computation is read off
  from `c`. Because of the type of `step`, these models are all deterministic by construction.
* `init : Input → Cfg` sets up the initial state. The type `Input` depends on the model;
  in most cases it is `List Γ`.
* `eval : Machine → Input → Part Output`, given a machine `M` and input `i`, starts from
  `init i`, runs `step` until it reaches an output, and then applies a function `Cfg → Output` to
  the final state to obtain the result. The type `Output` depends on the model.
* `Supports : Machine → Finset Λ → Prop` asserts that a machine `M` starts in `S : Finset Λ`, and
  can only ever jump to other states inside `S`. This implies that the behavior of `M` on any input
  cannot depend on its values outside `S`. We use this to allow `Λ` to be an infinite set when
  convenient, and prove that only finitely many of these states are actually accessible. This
  formalizes "essentially finite" mentioned above.
-/


open Relation

open Nat (iterate)

open Function (update iterate_succ iterate_succ_apply iterate_succ' iterate_succ_apply'
  iterate_zero_apply)

namespace Turing

/-- The `BlankExtends` partial order holds of `l₁` and `l₂` if `l₂` is obtained by adding
blanks (`default : Γ`) to the end of `l₁`. -/
def BlankExtends {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) : Prop :=
  ∃ n, l₂ = l₁ ++ List.replicate n default
#align turing.blank_extends Turing.BlankExtends

@[refl]
theorem BlankExtends.refl {Γ} [Inhabited Γ] (l : List Γ) : BlankExtends l l :=
  ⟨0, by simp⟩
         -- 🎉 no goals
#align turing.blank_extends.refl Turing.BlankExtends.refl

@[trans]
theorem BlankExtends.trans {Γ} [Inhabited Γ] {l₁ l₂ l₃ : List Γ} :
    BlankExtends l₁ l₂ → BlankExtends l₂ l₃ → BlankExtends l₁ l₃ := by
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩
  -- ⊢ BlankExtends l₁ (l₁ ++ List.replicate i default ++ List.replicate j default)
  exact ⟨i + j, by simp [List.replicate_add]⟩
  -- 🎉 no goals
#align turing.blank_extends.trans Turing.BlankExtends.trans

theorem BlankExtends.below_of_le {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} :
    BlankExtends l l₁ → BlankExtends l l₂ → l₁.length ≤ l₂.length → BlankExtends l₁ l₂ := by
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩ h; use j - i
  -- ⊢ BlankExtends (l ++ List.replicate i default) (l ++ List.replicate j default)
                              -- ⊢ l ++ List.replicate j default = l ++ List.replicate i default ++ List.replic …
  simp only [List.length_append, add_le_add_iff_left, List.length_replicate] at h
  -- ⊢ l ++ List.replicate j default = l ++ List.replicate i default ++ List.replic …
  simp only [← List.replicate_add, add_tsub_cancel_of_le h, List.append_assoc]
  -- 🎉 no goals
#align turing.blank_extends.below_of_le Turing.BlankExtends.below_of_le

/-- Any two extensions by blank `l₁,l₂` of `l` have a common join (which can be taken to be the
longer of `l₁` and `l₂`). -/
def BlankExtends.above {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} (h₁ : BlankExtends l l₁)
    (h₂ : BlankExtends l l₂) : { l' // BlankExtends l₁ l' ∧ BlankExtends l₂ l' } :=
  if h : l₁.length ≤ l₂.length then ⟨l₂, h₁.below_of_le h₂ h, BlankExtends.refl _⟩
  else ⟨l₁, BlankExtends.refl _, h₂.below_of_le h₁ (le_of_not_ge h)⟩
#align turing.blank_extends.above Turing.BlankExtends.above

theorem BlankExtends.above_of_le {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} :
    BlankExtends l₁ l → BlankExtends l₂ l → l₁.length ≤ l₂.length → BlankExtends l₁ l₂ := by
  rintro ⟨i, rfl⟩ ⟨j, e⟩ h; use i - j
  -- ⊢ BlankExtends l₁ l₂
                            -- ⊢ l₂ = l₁ ++ List.replicate (i - j) default
  refine' List.append_right_cancel (e.symm.trans _)
  -- ⊢ l₁ ++ List.replicate i default = l₁ ++ List.replicate (i - j) default ++ Lis …
  rw [List.append_assoc, ← List.replicate_add, tsub_add_cancel_of_le]
  -- ⊢ j ≤ i
  apply_fun List.length at e
  -- ⊢ j ≤ i
  simp only [List.length_append, List.length_replicate] at e
  -- ⊢ j ≤ i
  rwa [← add_le_add_iff_left, e, add_le_add_iff_right]
  -- 🎉 no goals
#align turing.blank_extends.above_of_le Turing.BlankExtends.above_of_le

/-- `BlankRel` is the symmetric closure of `BlankExtends`, turning it into an equivalence
relation. Two lists are related by `BlankRel` if one extends the other by blanks. -/
def BlankRel {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) : Prop :=
  BlankExtends l₁ l₂ ∨ BlankExtends l₂ l₁
#align turing.blank_rel Turing.BlankRel

@[refl]
theorem BlankRel.refl {Γ} [Inhabited Γ] (l : List Γ) : BlankRel l l :=
  Or.inl (BlankExtends.refl _)
#align turing.blank_rel.refl Turing.BlankRel.refl

@[symm]
theorem BlankRel.symm {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} : BlankRel l₁ l₂ → BlankRel l₂ l₁ :=
  Or.symm
#align turing.blank_rel.symm Turing.BlankRel.symm

@[trans]
theorem BlankRel.trans {Γ} [Inhabited Γ] {l₁ l₂ l₃ : List Γ} :
    BlankRel l₁ l₂ → BlankRel l₂ l₃ → BlankRel l₁ l₃ := by
  rintro (h₁ | h₁) (h₂ | h₂)
  · exact Or.inl (h₁.trans h₂)
    -- 🎉 no goals
  · cases' le_total l₁.length l₃.length with h h
    -- ⊢ BlankRel l₁ l₃
    · exact Or.inl (h₁.above_of_le h₂ h)
      -- 🎉 no goals
    · exact Or.inr (h₂.above_of_le h₁ h)
      -- 🎉 no goals
  · cases' le_total l₁.length l₃.length with h h
    -- ⊢ BlankRel l₁ l₃
    · exact Or.inl (h₁.below_of_le h₂ h)
      -- 🎉 no goals
    · exact Or.inr (h₂.below_of_le h₁ h)
      -- 🎉 no goals
  · exact Or.inr (h₂.trans h₁)
    -- 🎉 no goals
#align turing.blank_rel.trans Turing.BlankRel.trans

/-- Given two `BlankRel` lists, there exists (constructively) a common join. -/
def BlankRel.above {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} (h : BlankRel l₁ l₂) :
    { l // BlankExtends l₁ l ∧ BlankExtends l₂ l } := by
  refine'
    if hl : l₁.length ≤ l₂.length then ⟨l₂, Or.elim h id fun h' ↦ _, BlankExtends.refl _⟩
    else ⟨l₁, BlankExtends.refl _, Or.elim h (fun h' ↦ _) id⟩
  exact (BlankExtends.refl _).above_of_le h' hl
  -- ⊢ BlankExtends l₂ l₁
  exact (BlankExtends.refl _).above_of_le h' (le_of_not_ge hl)
  -- 🎉 no goals
#align turing.blank_rel.above Turing.BlankRel.above

/-- Given two `BlankRel` lists, there exists (constructively) a common meet. -/
def BlankRel.below {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} (h : BlankRel l₁ l₂) :
    { l // BlankExtends l l₁ ∧ BlankExtends l l₂ } := by
  refine'
    if hl : l₁.length ≤ l₂.length then ⟨l₁, BlankExtends.refl _, Or.elim h id fun h' ↦ _⟩
    else ⟨l₂, Or.elim h (fun h' ↦ _) id, BlankExtends.refl _⟩
  exact (BlankExtends.refl _).above_of_le h' hl
  -- ⊢ BlankExtends l₂ l₁
  exact (BlankExtends.refl _).above_of_le h' (le_of_not_ge hl)
  -- 🎉 no goals
#align turing.blank_rel.below Turing.BlankRel.below

theorem BlankRel.equivalence (Γ) [Inhabited Γ] : Equivalence (@BlankRel Γ _) :=
  ⟨BlankRel.refl, @BlankRel.symm _ _, @BlankRel.trans _ _⟩
#align turing.blank_rel.equivalence Turing.BlankRel.equivalence

/-- Construct a setoid instance for `BlankRel`. -/
def BlankRel.setoid (Γ) [Inhabited Γ] : Setoid (List Γ) :=
  ⟨_, BlankRel.equivalence _⟩
#align turing.blank_rel.setoid Turing.BlankRel.setoid

/-- A `ListBlank Γ` is a quotient of `List Γ` by extension by blanks at the end. This is used to
represent half-tapes of a Turing machine, so that we can pretend that the list continues
infinitely with blanks. -/
def ListBlank (Γ) [Inhabited Γ] :=
  Quotient (BlankRel.setoid Γ)
#align turing.list_blank Turing.ListBlank

instance ListBlank.inhabited {Γ} [Inhabited Γ] : Inhabited (ListBlank Γ) :=
  ⟨Quotient.mk'' []⟩
#align turing.list_blank.inhabited Turing.ListBlank.inhabited

instance ListBlank.hasEmptyc {Γ} [Inhabited Γ] : EmptyCollection (ListBlank Γ) :=
  ⟨Quotient.mk'' []⟩
#align turing.list_blank.has_emptyc Turing.ListBlank.hasEmptyc

/-- A modified version of `Quotient.liftOn'` specialized for `ListBlank`, with the stronger
precondition `BlankExtends` instead of `BlankRel`. -/
@[reducible]  -- Porting note: Removed `@[elab_as_elim]`
protected def ListBlank.liftOn {Γ} [Inhabited Γ] {α} (l : ListBlank Γ) (f : List Γ → α)
    (H : ∀ a b, BlankExtends a b → f a = f b) : α :=
  l.liftOn' f <| by rintro a b (h | h) <;> [exact H _ _ h; exact (H _ _ h).symm]
                    -- 🎉 no goals
#align turing.list_blank.lift_on Turing.ListBlank.liftOn

/-- The quotient map turning a `List` into a `ListBlank`. -/
def ListBlank.mk {Γ} [Inhabited Γ] : List Γ → ListBlank Γ :=
  Quotient.mk''
#align turing.list_blank.mk Turing.ListBlank.mk

@[elab_as_elim]
protected theorem ListBlank.induction_on {Γ} [Inhabited Γ] {p : ListBlank Γ → Prop}
    (q : ListBlank Γ) (h : ∀ a, p (ListBlank.mk a)) : p q :=
  Quotient.inductionOn' q h
#align turing.list_blank.induction_on Turing.ListBlank.induction_on

/-- The head of a `ListBlank` is well defined. -/
def ListBlank.head {Γ} [Inhabited Γ] (l : ListBlank Γ) : Γ := by
  apply l.liftOn List.headI
  -- ⊢ ∀ (a b : List Γ), BlankExtends a b → List.headI a = List.headI b
  rintro a _ ⟨i, rfl⟩
  -- ⊢ List.headI a = List.headI (a ++ List.replicate i default)
  cases a
  -- ⊢ List.headI [] = List.headI ([] ++ List.replicate i default)
  · cases i <;> rfl
    -- ⊢ List.headI [] = List.headI ([] ++ List.replicate Nat.zero default)
                -- 🎉 no goals
                -- 🎉 no goals
  rfl
  -- 🎉 no goals
#align turing.list_blank.head Turing.ListBlank.head

@[simp]
theorem ListBlank.head_mk {Γ} [Inhabited Γ] (l : List Γ) :
    ListBlank.head (ListBlank.mk l) = l.headI :=
  rfl
#align turing.list_blank.head_mk Turing.ListBlank.head_mk

/-- The tail of a `ListBlank` is well defined (up to the tail of blanks). -/
def ListBlank.tail {Γ} [Inhabited Γ] (l : ListBlank Γ) : ListBlank Γ := by
  apply l.liftOn (fun l ↦ ListBlank.mk l.tail)
  -- ⊢ ∀ (a b : List Γ), BlankExtends a b → mk (List.tail a) = mk (List.tail b)
  rintro a _ ⟨i, rfl⟩
  -- ⊢ mk (List.tail a) = mk (List.tail (a ++ List.replicate i default))
  refine' Quotient.sound' (Or.inl _)
  -- ⊢ BlankExtends (List.tail a) (List.tail (a ++ List.replicate i default))
  cases a
  -- ⊢ BlankExtends (List.tail []) (List.tail ([] ++ List.replicate i default))
  · cases' i with i <;> [exact ⟨0, rfl⟩; exact ⟨i, rfl⟩]
    -- 🎉 no goals
  exact ⟨i, rfl⟩
  -- 🎉 no goals
#align turing.list_blank.tail Turing.ListBlank.tail

@[simp]
theorem ListBlank.tail_mk {Γ} [Inhabited Γ] (l : List Γ) :
    ListBlank.tail (ListBlank.mk l) = ListBlank.mk l.tail :=
  rfl
#align turing.list_blank.tail_mk Turing.ListBlank.tail_mk

/-- We can cons an element onto a `ListBlank`. -/
def ListBlank.cons {Γ} [Inhabited Γ] (a : Γ) (l : ListBlank Γ) : ListBlank Γ := by
  apply l.liftOn (fun l ↦ ListBlank.mk (List.cons a l))
  -- ⊢ ∀ (a_1 b : List Γ), BlankExtends a_1 b → mk (a :: a_1) = mk (a :: b)
  rintro _ _ ⟨i, rfl⟩
  -- ⊢ mk (a :: a✝) = mk (a :: (a✝ ++ List.replicate i default))
  exact Quotient.sound' (Or.inl ⟨i, rfl⟩)
  -- 🎉 no goals
#align turing.list_blank.cons Turing.ListBlank.cons

@[simp]
theorem ListBlank.cons_mk {Γ} [Inhabited Γ] (a : Γ) (l : List Γ) :
    ListBlank.cons a (ListBlank.mk l) = ListBlank.mk (a :: l) :=
  rfl
#align turing.list_blank.cons_mk Turing.ListBlank.cons_mk

@[simp]
theorem ListBlank.head_cons {Γ} [Inhabited Γ] (a : Γ) : ∀ l : ListBlank Γ, (l.cons a).head = a :=
  Quotient.ind' fun _ ↦ rfl
#align turing.list_blank.head_cons Turing.ListBlank.head_cons

@[simp]
theorem ListBlank.tail_cons {Γ} [Inhabited Γ] (a : Γ) : ∀ l : ListBlank Γ, (l.cons a).tail = l :=
  Quotient.ind' fun _ ↦ rfl
#align turing.list_blank.tail_cons Turing.ListBlank.tail_cons

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `List` where
this only holds for nonempty lists. -/
@[simp]
theorem ListBlank.cons_head_tail {Γ} [Inhabited Γ] : ∀ l : ListBlank Γ, l.tail.cons l.head = l := by
  apply Quotient.ind'
  -- ⊢ ∀ (a : List Γ), cons (head (Quotient.mk'' a)) (tail (Quotient.mk'' a)) = Quo …
  refine' fun l ↦ Quotient.sound' (Or.inr _)
  -- ⊢ BlankExtends l (head (Quotient.mk'' l) :: List.tail l)
  cases l
  -- ⊢ BlankExtends [] (head (Quotient.mk'' []) :: List.tail [])
  · exact ⟨1, rfl⟩
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align turing.list_blank.cons_head_tail Turing.ListBlank.cons_head_tail

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `List` where
this only holds for nonempty lists. -/
theorem ListBlank.exists_cons {Γ} [Inhabited Γ] (l : ListBlank Γ) :
    ∃ a l', l = ListBlank.cons a l' :=
  ⟨_, _, (ListBlank.cons_head_tail _).symm⟩
#align turing.list_blank.exists_cons Turing.ListBlank.exists_cons

/-- The n-th element of a `ListBlank` is well defined for all `n : ℕ`, unlike in a `List`. -/
def ListBlank.nth {Γ} [Inhabited Γ] (l : ListBlank Γ) (n : ℕ) : Γ := by
  apply l.liftOn (fun l ↦ List.getI l n)
  -- ⊢ ∀ (a b : List Γ), BlankExtends a b → List.getI a n = List.getI b n
  rintro l _ ⟨i, rfl⟩
  -- ⊢ List.getI l n = List.getI (l ++ List.replicate i default) n
  cases' lt_or_le n _ with h h
  -- ⊢ List.getI l n = List.getI (l ++ List.replicate i default) n
  · rw [List.getI_append _ _ _ h]
    -- 🎉 no goals
  rw [List.getI_eq_default _ h]
  -- ⊢ default = List.getI (l ++ List.replicate i default) n
  cases' le_or_lt _ n with h₂ h₂
  -- ⊢ default = List.getI (l ++ List.replicate i default) n
  · rw [List.getI_eq_default _ h₂]
    -- 🎉 no goals
  rw [List.getI_eq_get _ h₂, List.get_append_right' h, List.get_replicate]
  -- 🎉 no goals
#align turing.list_blank.nth Turing.ListBlank.nth

@[simp]
theorem ListBlank.nth_mk {Γ} [Inhabited Γ] (l : List Γ) (n : ℕ) :
    (ListBlank.mk l).nth n = l.getI n :=
  rfl
#align turing.list_blank.nth_mk Turing.ListBlank.nth_mk

@[simp]
theorem ListBlank.nth_zero {Γ} [Inhabited Γ] (l : ListBlank Γ) : l.nth 0 = l.head := by
  conv => lhs; rw [← ListBlank.cons_head_tail l]
  -- ⊢ nth (cons (head l) (tail l)) 0 = head l
  exact Quotient.inductionOn' l.tail fun l ↦ rfl
  -- 🎉 no goals
#align turing.list_blank.nth_zero Turing.ListBlank.nth_zero

@[simp]
theorem ListBlank.nth_succ {Γ} [Inhabited Γ] (l : ListBlank Γ) (n : ℕ) :
    l.nth (n + 1) = l.tail.nth n := by
  conv => lhs; rw [← ListBlank.cons_head_tail l]
  -- ⊢ nth (cons (head l) (tail l)) (n + 1) = nth (tail l) n
  exact Quotient.inductionOn' l.tail fun l ↦ rfl
  -- 🎉 no goals
#align turing.list_blank.nth_succ Turing.ListBlank.nth_succ

@[ext]
theorem ListBlank.ext {Γ} [i : Inhabited Γ] {L₁ L₂ : ListBlank Γ} :
    (∀ i, L₁.nth i = L₂.nth i) → L₁ = L₂ := by
  refine' ListBlank.induction_on L₁ fun l₁ ↦ ListBlank.induction_on L₂ fun l₂ H ↦ _
  -- ⊢ mk l₁ = mk l₂
  wlog h : l₁.length ≤ l₂.length
  -- ⊢ mk l₁ = mk l₂
  · cases le_total l₁.length l₂.length <;> [skip; symm] <;> apply this <;> try assumption
    -- ⊢ mk l₁ = mk l₂
                                                                           -- 🎉 no goals
                                                                           -- 🎉 no goals
                                                                           -- 🎉 no goals
                                                                           -- 🎉 no goals
                                                                           -- 🎉 no goals
                                                                           -- 🎉 no goals
                                                                           -- ⊢ ∀ (i_1 : ℕ), nth (mk l₂) i_1 = nth (mk l₁) i_1
                                                                           -- 🎉 no goals
    intro
    -- ⊢ nth (mk l₂) i✝ = nth (mk l₁) i✝
    rw [H]
    -- 🎉 no goals
  refine' Quotient.sound' (Or.inl ⟨l₂.length - l₁.length, _⟩)
  -- ⊢ l₂ = l₁ ++ List.replicate (List.length l₂ - List.length l₁) default
  refine' List.ext_get _ fun i h h₂ ↦ Eq.symm _
  -- ⊢ List.length l₂ = List.length (l₁ ++ List.replicate (List.length l₂ - List.le …
  · simp only [add_tsub_cancel_of_le h, List.length_append, List.length_replicate]
    -- 🎉 no goals
  simp only [ListBlank.nth_mk] at H
  -- ⊢ List.get (l₁ ++ List.replicate (List.length l₂ - List.length l₁) default) {  …
  cases' lt_or_le i l₁.length with h' h'
  -- ⊢ List.get (l₁ ++ List.replicate (List.length l₂ - List.length l₁) default) {  …
  · simp only [List.get_append _ h', List.get?_eq_get h, List.get?_eq_get h',
      ← List.getI_eq_get _ h, ← List.getI_eq_get _ h', H]
  · simp only [List.get_append_right' h', List.get_replicate, List.get?_eq_get h,
      List.get?_len_le h', ← List.getI_eq_default _ h', H, List.getI_eq_get _ h]
#align turing.list_blank.ext Turing.ListBlank.ext

/-- Apply a function to a value stored at the nth position of the list. -/
@[simp]
def ListBlank.modifyNth {Γ} [Inhabited Γ] (f : Γ → Γ) : ℕ → ListBlank Γ → ListBlank Γ
  | 0, L => L.tail.cons (f L.head)
  | n + 1, L => (L.tail.modifyNth f n).cons L.head
#align turing.list_blank.modify_nth Turing.ListBlank.modifyNth

theorem ListBlank.nth_modifyNth {Γ} [Inhabited Γ] (f : Γ → Γ) (n i) (L : ListBlank Γ) :
    (L.modifyNth f n).nth i = if i = n then f (L.nth i) else L.nth i := by
  induction' n with n IH generalizing i L
  -- ⊢ nth (modifyNth f Nat.zero L) i = if i = Nat.zero then f (nth L i) else nth L i
  · cases i <;> simp only [ListBlank.nth_zero, if_true, ListBlank.head_cons, ListBlank.modifyNth,
    -- ⊢ nth (modifyNth f Nat.zero L) Nat.zero = if Nat.zero = Nat.zero then f (nth L …
      ListBlank.nth_succ, if_false, ListBlank.tail_cons, Nat.zero_eq]
  · cases i
    -- ⊢ nth (modifyNth f (Nat.succ n) L) Nat.zero = if Nat.zero = Nat.succ n then f  …
    · rw [if_neg (Nat.succ_ne_zero _).symm]
      -- ⊢ nth (modifyNth f (Nat.succ n) L) Nat.zero = nth L Nat.zero
      simp only [ListBlank.nth_zero, ListBlank.head_cons, ListBlank.modifyNth, Nat.zero_eq]
      -- 🎉 no goals
    · simp only [IH, ListBlank.modifyNth, ListBlank.nth_succ, ListBlank.tail_cons, Nat.succ.injEq]
      -- 🎉 no goals
#align turing.list_blank.nth_modify_nth Turing.ListBlank.nth_modifyNth

/-- A pointed map of `Inhabited` types is a map that sends one default value to the other. -/
structure PointedMap.{u, v} (Γ : Type u) (Γ' : Type v) [Inhabited Γ] [Inhabited Γ'] :
    Type max u v where
  f : Γ → Γ'
  map_pt' : f default = default
#align turing.pointed_map Turing.PointedMap

instance {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] : Inhabited (PointedMap Γ Γ') :=
  ⟨⟨default, rfl⟩⟩

instance {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] : CoeFun (PointedMap Γ Γ') fun _ ↦ Γ → Γ' :=
  ⟨PointedMap.f⟩

-- @[simp] -- Porting note: dsimp can prove this
theorem PointedMap.mk_val {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : Γ → Γ') (pt) :
    (PointedMap.mk f pt : Γ → Γ') = f :=
  rfl
#align turing.pointed_map.mk_val Turing.PointedMap.mk_val

@[simp]
theorem PointedMap.map_pt {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') :
    f default = default :=
  PointedMap.map_pt' _
#align turing.pointed_map.map_pt Turing.PointedMap.map_pt

@[simp]
theorem PointedMap.headI_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : List Γ) : (l.map f).headI = f l.headI := by
  cases l <;> [exact (PointedMap.map_pt f).symm; rfl]
  -- 🎉 no goals
#align turing.pointed_map.head_map Turing.PointedMap.headI_map

/-- The `map` function on lists is well defined on `ListBlank`s provided that the map is
pointed. -/
def ListBlank.map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : ListBlank Γ) :
    ListBlank Γ' := by
  apply l.liftOn (fun l ↦ ListBlank.mk (List.map f l))
  -- ⊢ ∀ (a b : List Γ), BlankExtends a b → mk (List.map f.f a) = mk (List.map f.f b)
  rintro l _ ⟨i, rfl⟩; refine' Quotient.sound' (Or.inl ⟨i, _⟩)
  -- ⊢ mk (List.map f.f l) = mk (List.map f.f (l ++ List.replicate i default))
                       -- ⊢ List.map f.f (l ++ List.replicate i default) = List.map f.f l ++ List.replic …
  simp only [PointedMap.map_pt, List.map_append, List.map_replicate]
  -- 🎉 no goals
#align turing.list_blank.map Turing.ListBlank.map

@[simp]
theorem ListBlank.map_mk {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : List Γ) :
    (ListBlank.mk l).map f = ListBlank.mk (l.map f) :=
  rfl
#align turing.list_blank.map_mk Turing.ListBlank.map_mk

@[simp]
theorem ListBlank.head_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) : (l.map f).head = f l.head := by
  conv => lhs; rw [← ListBlank.cons_head_tail l]
  -- ⊢ head (map f (cons (head l) (tail l))) = PointedMap.f f (head l)
  exact Quotient.inductionOn' l fun a ↦ rfl
  -- 🎉 no goals
#align turing.list_blank.head_map Turing.ListBlank.head_map

@[simp]
theorem ListBlank.tail_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) : (l.map f).tail = l.tail.map f := by
  conv => lhs; rw [← ListBlank.cons_head_tail l]
  -- ⊢ tail (map f (cons (head l) (tail l))) = map f (tail l)
  exact Quotient.inductionOn' l fun a ↦ rfl
  -- 🎉 no goals
#align turing.list_blank.tail_map Turing.ListBlank.tail_map

@[simp]
theorem ListBlank.map_cons {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) (a : Γ) : (l.cons a).map f = (l.map f).cons (f a) := by
  refine' (ListBlank.cons_head_tail _).symm.trans _
  -- ⊢ cons (head (map f (cons a l))) (tail (map f (cons a l))) = cons (PointedMap. …
  simp only [ListBlank.head_map, ListBlank.head_cons, ListBlank.tail_map, ListBlank.tail_cons]
  -- 🎉 no goals
#align turing.list_blank.map_cons Turing.ListBlank.map_cons

@[simp]
theorem ListBlank.nth_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) (n : ℕ) : (l.map f).nth n = f (l.nth n) := by
  refine' l.inductionOn fun l ↦ _
  -- ⊢ nth (map f (Quotient.mk (BlankRel.setoid Γ) l)) n = PointedMap.f f (nth (Quo …
  -- Porting note: Added `suffices` to get `simp` to work.
  suffices ((mk l).map f).nth n = f ((mk l).nth n) by exact this
  -- ⊢ nth (map f (mk l)) n = PointedMap.f f (nth (mk l) n)
  simp only [List.get?_map, ListBlank.map_mk, ListBlank.nth_mk, List.getI_eq_iget_get?]
  -- ⊢ Option.iget (Option.map f.f (List.get? l n)) = PointedMap.f f (Option.iget ( …
  cases l.get? n
  -- ⊢ Option.iget (Option.map f.f none) = PointedMap.f f (Option.iget none)
  · exact f.2.symm
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align turing.list_blank.nth_map Turing.ListBlank.nth_map

/-- The `i`-th projection as a pointed map. -/
def proj {ι : Type*} {Γ : ι → Type*} [∀ i, Inhabited (Γ i)] (i : ι) :
    PointedMap (∀ i, Γ i) (Γ i) :=
  ⟨fun a ↦ a i, rfl⟩
#align turing.proj Turing.proj

theorem proj_map_nth {ι : Type*} {Γ : ι → Type*} [∀ i, Inhabited (Γ i)] (i : ι) (L n) :
    (ListBlank.map (@proj ι Γ _ i) L).nth n = L.nth n i := by
  rw [ListBlank.nth_map]; rfl
  -- ⊢ PointedMap.f (proj i) (ListBlank.nth L n) = ListBlank.nth L n i
                          -- 🎉 no goals
#align turing.proj_map_nth Turing.proj_map_nth

theorem ListBlank.map_modifyNth {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (F : PointedMap Γ Γ')
    (f : Γ → Γ) (f' : Γ' → Γ') (H : ∀ x, F (f x) = f' (F x)) (n) (L : ListBlank Γ) :
    (L.modifyNth f n).map F = (L.map F).modifyNth f' n := by
  induction' n with n IH generalizing L <;>
  -- ⊢ map F (modifyNth f Nat.zero L) = modifyNth f' Nat.zero (map F L)
    simp only [*, ListBlank.head_map, ListBlank.modifyNth, ListBlank.map_cons, ListBlank.tail_map]
    -- 🎉 no goals
    -- 🎉 no goals
#align turing.list_blank.map_modify_nth Turing.ListBlank.map_modifyNth

/-- Append a list on the left side of a `ListBlank`. -/
@[simp]
def ListBlank.append {Γ} [Inhabited Γ] : List Γ → ListBlank Γ → ListBlank Γ
  | [], L => L
  | a :: l, L => ListBlank.cons a (ListBlank.append l L)
#align turing.list_blank.append Turing.ListBlank.append

@[simp]
theorem ListBlank.append_mk {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) :
    ListBlank.append l₁ (ListBlank.mk l₂) = ListBlank.mk (l₁ ++ l₂) := by
  induction l₁ <;>
  -- ⊢ append [] (mk l₂) = mk ([] ++ l₂)
    simp only [*, ListBlank.append, List.nil_append, List.cons_append, ListBlank.cons_mk]
    -- 🎉 no goals
    -- 🎉 no goals
#align turing.list_blank.append_mk Turing.ListBlank.append_mk

theorem ListBlank.append_assoc {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) (l₃ : ListBlank Γ) :
    ListBlank.append (l₁ ++ l₂) l₃ = ListBlank.append l₁ (ListBlank.append l₂ l₃) := by
  refine' l₃.inductionOn fun l ↦ _
  -- ⊢ append (l₁ ++ l₂) (Quotient.mk (BlankRel.setoid Γ) l) = append l₁ (append l₂ …
  -- Porting note: Added `suffices` to get `simp` to work.
  suffices append (l₁ ++ l₂) (mk l) = append l₁ (append l₂ (mk l)) by exact this
  -- ⊢ append (l₁ ++ l₂) (mk l) = append l₁ (append l₂ (mk l))
  simp only [ListBlank.append_mk, List.append_assoc]
  -- 🎉 no goals
#align turing.list_blank.append_assoc Turing.ListBlank.append_assoc

/-- The `bind` function on lists is well defined on `ListBlank`s provided that the default element
is sent to a sequence of default elements. -/
def ListBlank.bind {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (l : ListBlank Γ) (f : Γ → List Γ')
    (hf : ∃ n, f default = List.replicate n default) : ListBlank Γ' := by
  apply l.liftOn (fun l ↦ ListBlank.mk (List.bind l f))
  -- ⊢ ∀ (a b : List Γ), BlankExtends a b → mk (List.bind a f) = mk (List.bind b f)
  rintro l _ ⟨i, rfl⟩; cases' hf with n e; refine' Quotient.sound' (Or.inl ⟨i * n, _⟩)
  -- ⊢ mk (List.bind l f) = mk (List.bind (l ++ List.replicate i default) f)
                       -- ⊢ mk (List.bind l f) = mk (List.bind (l ++ List.replicate i default) f)
                                           -- ⊢ List.bind (l ++ List.replicate i default) f = List.bind l f ++ List.replicat …
  rw [List.append_bind, mul_comm]; congr
  -- ⊢ List.bind l f ++ List.bind (List.replicate i default) f = List.bind l f ++ L …
                                   -- ⊢ List.bind (List.replicate i default) f = List.replicate (n * i) default
  induction' i with i IH; rfl
  -- ⊢ List.bind (List.replicate Nat.zero default) f = List.replicate (n * Nat.zero …
                          -- ⊢ List.bind (List.replicate (Nat.succ i) default) f = List.replicate (n * Nat. …
  simp only [IH, e, List.replicate_add, Nat.mul_succ, add_comm, List.replicate_succ, List.cons_bind]
  -- 🎉 no goals
#align turing.list_blank.bind Turing.ListBlank.bind

@[simp]
theorem ListBlank.bind_mk {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (l : List Γ) (f : Γ → List Γ') (hf) :
    (ListBlank.mk l).bind f hf = ListBlank.mk (l.bind f) :=
  rfl
#align turing.list_blank.bind_mk Turing.ListBlank.bind_mk

@[simp]
theorem ListBlank.cons_bind {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (a : Γ) (l : ListBlank Γ)
    (f : Γ → List Γ') (hf) : (l.cons a).bind f hf = (l.bind f hf).append (f a) := by
  refine' l.inductionOn fun l ↦ _
  -- ⊢ bind (cons a (Quotient.mk (BlankRel.setoid Γ) l)) f hf = append (f a) (bind  …
  -- Porting note: Added `suffices` to get `simp` to work.
  suffices ((mk l).cons a).bind f hf = ((mk l).bind f hf).append (f a) by exact this
  -- ⊢ bind (cons a (mk l)) f hf = append (f a) (bind (mk l) f hf)
  simp only [ListBlank.append_mk, ListBlank.bind_mk, ListBlank.cons_mk, List.cons_bind]
  -- 🎉 no goals
#align turing.list_blank.cons_bind Turing.ListBlank.cons_bind

/-- The tape of a Turing machine is composed of a head element (which we imagine to be the
current position of the head), together with two `ListBlank`s denoting the portions of the tape
going off to the left and right. When the Turing machine moves right, an element is pulled from the
right side and becomes the new head, while the head element is consed onto the left side. -/
structure Tape (Γ : Type*) [Inhabited Γ] where
  head : Γ
  left : ListBlank Γ
  right : ListBlank Γ
#align turing.tape Turing.Tape

instance Tape.inhabited {Γ} [Inhabited Γ] : Inhabited (Tape Γ) :=
  ⟨by constructor <;> apply default⟩
                      -- 🎉 no goals
                      -- 🎉 no goals
                      -- 🎉 no goals
#align turing.tape.inhabited Turing.Tape.inhabited

/-- A direction for the turing machine `move` command, either
  left or right. -/
inductive Dir
  | left
  | right
  deriving DecidableEq, Inhabited
#align turing.dir Turing.Dir

/-- The "inclusive" left side of the tape, including both `left` and `head`. -/
def Tape.left₀ {Γ} [Inhabited Γ] (T : Tape Γ) : ListBlank Γ :=
  T.left.cons T.head
#align turing.tape.left₀ Turing.Tape.left₀

/-- The "inclusive" right side of the tape, including both `right` and `head`. -/
def Tape.right₀ {Γ} [Inhabited Γ] (T : Tape Γ) : ListBlank Γ :=
  T.right.cons T.head
#align turing.tape.right₀ Turing.Tape.right₀

/-- Move the tape in response to a motion of the Turing machine. Note that `T.move Dir.left` makes
`T.left` smaller; the Turing machine is moving left and the tape is moving right. -/
def Tape.move {Γ} [Inhabited Γ] : Dir → Tape Γ → Tape Γ
  | Dir.left, ⟨a, L, R⟩ => ⟨L.head, L.tail, R.cons a⟩
  | Dir.right, ⟨a, L, R⟩ => ⟨R.head, L.cons a, R.tail⟩
#align turing.tape.move Turing.Tape.move

@[simp]
theorem Tape.move_left_right {Γ} [Inhabited Γ] (T : Tape Γ) :
    (T.move Dir.left).move Dir.right = T := by
  cases T; simp [Tape.move]
  -- ⊢ move Dir.right (move Dir.left { head := head✝, left := left✝, right := right …
           -- 🎉 no goals
#align turing.tape.move_left_right Turing.Tape.move_left_right

@[simp]
theorem Tape.move_right_left {Γ} [Inhabited Γ] (T : Tape Γ) :
    (T.move Dir.right).move Dir.left = T := by
  cases T; simp [Tape.move]
  -- ⊢ move Dir.left (move Dir.right { head := head✝, left := left✝, right := right …
           -- 🎉 no goals
#align turing.tape.move_right_left Turing.Tape.move_right_left

/-- Construct a tape from a left side and an inclusive right side. -/
def Tape.mk' {Γ} [Inhabited Γ] (L R : ListBlank Γ) : Tape Γ :=
  ⟨R.head, L, R.tail⟩
#align turing.tape.mk' Turing.Tape.mk'

@[simp]
theorem Tape.mk'_left {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).left = L :=
  rfl
#align turing.tape.mk'_left Turing.Tape.mk'_left

@[simp]
theorem Tape.mk'_head {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).head = R.head :=
  rfl
#align turing.tape.mk'_head Turing.Tape.mk'_head

@[simp]
theorem Tape.mk'_right {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).right = R.tail :=
  rfl
#align turing.tape.mk'_right Turing.Tape.mk'_right

@[simp]
theorem Tape.mk'_right₀ {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).right₀ = R :=
  ListBlank.cons_head_tail _
#align turing.tape.mk'_right₀ Turing.Tape.mk'_right₀

@[simp]
theorem Tape.mk'_left_right₀ {Γ} [Inhabited Γ] (T : Tape Γ) : Tape.mk' T.left T.right₀ = T := by
  cases T
  -- ⊢ mk' { head := head✝, left := left✝, right := right✝ }.left (right₀ { head := …
  simp only [Tape.right₀, Tape.mk', ListBlank.head_cons, ListBlank.tail_cons, eq_self_iff_true,
    and_self_iff]
#align turing.tape.mk'_left_right₀ Turing.Tape.mk'_left_right₀

theorem Tape.exists_mk' {Γ} [Inhabited Γ] (T : Tape Γ) : ∃ L R, T = Tape.mk' L R :=
  ⟨_, _, (Tape.mk'_left_right₀ _).symm⟩
#align turing.tape.exists_mk' Turing.Tape.exists_mk'

@[simp]
theorem Tape.move_left_mk' {Γ} [Inhabited Γ] (L R : ListBlank Γ) :
    (Tape.mk' L R).move Dir.left = Tape.mk' L.tail (R.cons L.head) := by
  simp only [Tape.move, Tape.mk', ListBlank.head_cons, eq_self_iff_true, ListBlank.cons_head_tail,
    and_self_iff, ListBlank.tail_cons]
#align turing.tape.move_left_mk' Turing.Tape.move_left_mk'

@[simp]
theorem Tape.move_right_mk' {Γ} [Inhabited Γ] (L R : ListBlank Γ) :
    (Tape.mk' L R).move Dir.right = Tape.mk' (L.cons R.head) R.tail := by
  simp only [Tape.move, Tape.mk', ListBlank.head_cons, eq_self_iff_true, ListBlank.cons_head_tail,
    and_self_iff, ListBlank.tail_cons]
#align turing.tape.move_right_mk' Turing.Tape.move_right_mk'

/-- Construct a tape from a left side and an inclusive right side. -/
def Tape.mk₂ {Γ} [Inhabited Γ] (L R : List Γ) : Tape Γ :=
  Tape.mk' (ListBlank.mk L) (ListBlank.mk R)
#align turing.tape.mk₂ Turing.Tape.mk₂

/-- Construct a tape from a list, with the head of the list at the TM head and the rest going
to the right. -/
def Tape.mk₁ {Γ} [Inhabited Γ] (l : List Γ) : Tape Γ :=
  Tape.mk₂ [] l
#align turing.tape.mk₁ Turing.Tape.mk₁

/-- The `nth` function of a tape is integer-valued, with index `0` being the head, negative indexes
on the left and positive indexes on the right. (Picture a number line.) -/
def Tape.nth {Γ} [Inhabited Γ] (T : Tape Γ) : ℤ → Γ
  | 0 => T.head
  | (n + 1 : ℕ) => T.right.nth n
  | -(n + 1 : ℕ) => T.left.nth n
#align turing.tape.nth Turing.Tape.nth

@[simp]
theorem Tape.nth_zero {Γ} [Inhabited Γ] (T : Tape Γ) : T.nth 0 = T.1 :=
  rfl
#align turing.tape.nth_zero Turing.Tape.nth_zero

theorem Tape.right₀_nth {Γ} [Inhabited Γ] (T : Tape Γ) (n : ℕ) : T.right₀.nth n = T.nth n := by
  cases n <;> simp only [Tape.nth, Tape.right₀, Int.ofNat_zero, ListBlank.nth_zero,
  -- ⊢ ListBlank.nth (right₀ T) Nat.zero = nth T ↑Nat.zero
    ListBlank.nth_succ, ListBlank.head_cons, ListBlank.tail_cons, Nat.zero_eq]
#align turing.tape.right₀_nth Turing.Tape.right₀_nth

@[simp]
theorem Tape.mk'_nth_nat {Γ} [Inhabited Γ] (L R : ListBlank Γ) (n : ℕ) :
    (Tape.mk' L R).nth n = R.nth n := by
  rw [← Tape.right₀_nth, Tape.mk'_right₀]
  -- 🎉 no goals
#align turing.tape.mk'_nth_nat Turing.Tape.mk'_nth_nat

@[simp]
theorem Tape.move_left_nth {Γ} [Inhabited Γ] :
    ∀ (T : Tape Γ) (i : ℤ), (T.move Dir.left).nth i = T.nth (i - 1)
  | ⟨_, L, _⟩, -(n + 1 : ℕ) => (ListBlank.nth_succ _ _).symm
  | ⟨_, L, _⟩, 0 => (ListBlank.nth_zero _).symm
  | ⟨a, L, R⟩, 1 => (ListBlank.nth_zero _).trans (ListBlank.head_cons _ _)
  | ⟨a, L, R⟩, (n + 1 : ℕ) + 1 => by
    rw [add_sub_cancel]
    -- ⊢ nth (move Dir.left { head := a, left := L, right := R }) (↑(n + 1) + 1) = nt …
    change (R.cons a).nth (n + 1) = R.nth n
    -- ⊢ ListBlank.nth (ListBlank.cons a R) (n + 1) = ListBlank.nth R n
    rw [ListBlank.nth_succ, ListBlank.tail_cons]
    -- 🎉 no goals
#align turing.tape.move_left_nth Turing.Tape.move_left_nth

@[simp]
theorem Tape.move_right_nth {Γ} [Inhabited Γ] (T : Tape Γ) (i : ℤ) :
    (T.move Dir.right).nth i = T.nth (i + 1) := by
  conv => rhs; rw [← T.move_right_left]
  -- ⊢ nth (move Dir.right T) i = nth (move Dir.left (move Dir.right T)) (i + 1)
  rw [Tape.move_left_nth, add_sub_cancel]
  -- 🎉 no goals
#align turing.tape.move_right_nth Turing.Tape.move_right_nth

@[simp]
theorem Tape.move_right_n_head {Γ} [Inhabited Γ] (T : Tape Γ) (i : ℕ) :
    ((Tape.move Dir.right)^[i] T).head = T.nth i := by
  induction i generalizing T
  -- ⊢ ((move Dir.right)^[Nat.zero] T).head = nth T ↑Nat.zero
  · rfl
    -- 🎉 no goals
  · simp only [*, Tape.move_right_nth, Int.ofNat_succ, iterate_succ, Function.comp_apply]
    -- 🎉 no goals
#align turing.tape.move_right_n_head Turing.Tape.move_right_n_head

/-- Replace the current value of the head on the tape. -/
def Tape.write {Γ} [Inhabited Γ] (b : Γ) (T : Tape Γ) : Tape Γ :=
  { T with head := b }
#align turing.tape.write Turing.Tape.write

@[simp]
theorem Tape.write_self {Γ} [Inhabited Γ] : ∀ T : Tape Γ, T.write T.1 = T := by
  rintro ⟨⟩; rfl
  -- ⊢ write { head := head✝, left := left✝, right := right✝ }.head { head := head✝ …
             -- 🎉 no goals
#align turing.tape.write_self Turing.Tape.write_self

@[simp]
theorem Tape.write_nth {Γ} [Inhabited Γ] (b : Γ) :
    ∀ (T : Tape Γ) {i : ℤ}, (T.write b).nth i = if i = 0 then b else T.nth i
  | _, 0 => rfl
  | _, (_ + 1 : ℕ) => rfl
  | _, -(_ + 1 : ℕ) => rfl
#align turing.tape.write_nth Turing.Tape.write_nth

@[simp]
theorem Tape.write_mk' {Γ} [Inhabited Γ] (a b : Γ) (L R : ListBlank Γ) :
    (Tape.mk' L (R.cons a)).write b = Tape.mk' L (R.cons b) := by
  simp only [Tape.write, Tape.mk', ListBlank.head_cons, ListBlank.tail_cons, eq_self_iff_true,
    and_self_iff]
#align turing.tape.write_mk' Turing.Tape.write_mk'

/-- Apply a pointed map to a tape to change the alphabet. -/
def Tape.map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (T : Tape Γ) : Tape Γ' :=
  ⟨f T.1, T.2.map f, T.3.map f⟩
#align turing.tape.map Turing.Tape.map

@[simp]
theorem Tape.map_fst {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') :
    ∀ T : Tape Γ, (T.map f).1 = f T.1 := by
  rintro ⟨⟩; rfl
  -- ⊢ (map f { head := head✝, left := left✝, right := right✝ }).head = PointedMap. …
             -- 🎉 no goals
#align turing.tape.map_fst Turing.Tape.map_fst

@[simp]
theorem Tape.map_write {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (b : Γ) :
    ∀ T : Tape Γ, (T.write b).map f = (T.map f).write (f b) := by
  rintro ⟨⟩; rfl
  -- ⊢ map f (write b { head := head✝, left := left✝, right := right✝ }) = write (P …
             -- 🎉 no goals
#align turing.tape.map_write Turing.Tape.map_write

-- Porting note: `simpNF` complains about LHS does not simplify when using the simp lemma on
--               itself, but it does indeed.
@[simp, nolint simpNF]
theorem Tape.write_move_right_n {Γ} [Inhabited Γ] (f : Γ → Γ) (L R : ListBlank Γ) (n : ℕ) :
    ((Tape.move Dir.right)^[n] (Tape.mk' L R)).write (f (R.nth n)) =
      (Tape.move Dir.right)^[n] (Tape.mk' L (R.modifyNth f n)) := by
  induction' n with n IH generalizing L R
  -- ⊢ write (f (ListBlank.nth R Nat.zero)) ((move Dir.right)^[Nat.zero] (mk' L R)) …
  · simp only [ListBlank.nth_zero, ListBlank.modifyNth, iterate_zero_apply, Nat.zero_eq]
    -- ⊢ write (f (ListBlank.head R)) (mk' L R) = mk' L (ListBlank.cons (f (ListBlank …
    rw [← Tape.write_mk', ListBlank.cons_head_tail]
    -- 🎉 no goals
  simp only [ListBlank.head_cons, ListBlank.nth_succ, ListBlank.modifyNth, Tape.move_right_mk',
    ListBlank.tail_cons, iterate_succ_apply, IH]
#align turing.tape.write_move_right_n Turing.Tape.write_move_right_n

theorem Tape.map_move {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (T : Tape Γ) (d) :
    (T.move d).map f = (T.map f).move d := by
  cases T
  -- ⊢ map f (move d { head := head✝, left := left✝, right := right✝ }) = move d (m …
  cases d <;> simp only [Tape.move, Tape.map, ListBlank.head_map, eq_self_iff_true,
  -- ⊢ map f (move Dir.left { head := head✝, left := left✝, right := right✝ }) = mo …
    ListBlank.map_cons, and_self_iff, ListBlank.tail_map]
#align turing.tape.map_move Turing.Tape.map_move

theorem Tape.map_mk' {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (L R : ListBlank Γ) :
    (Tape.mk' L R).map f = Tape.mk' (L.map f) (R.map f) := by
  simp only [Tape.mk', Tape.map, ListBlank.head_map, eq_self_iff_true, and_self_iff,
    ListBlank.tail_map]
#align turing.tape.map_mk' Turing.Tape.map_mk'

theorem Tape.map_mk₂ {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (L R : List Γ) :
    (Tape.mk₂ L R).map f = Tape.mk₂ (L.map f) (R.map f) := by
  simp only [Tape.mk₂, Tape.map_mk', ListBlank.map_mk]
  -- 🎉 no goals
#align turing.tape.map_mk₂ Turing.Tape.map_mk₂

theorem Tape.map_mk₁ {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : List Γ) :
    (Tape.mk₁ l).map f = Tape.mk₁ (l.map f) :=
  Tape.map_mk₂ _ _ _
#align turing.tape.map_mk₁ Turing.Tape.map_mk₁

/-- Run a state transition function `σ → Option σ` "to completion". The return value is the last
state returned before a `none` result. If the state transition function always returns `some`,
then the computation diverges, returning `Part.none`. -/
def eval {σ} (f : σ → Option σ) : σ → Part σ :=
  PFun.fix fun s ↦ Part.some <| (f s).elim (Sum.inl s) Sum.inr
#align turing.eval Turing.eval

/-- The reflexive transitive closure of a state transition function. `Reaches f a b` means
there is a finite sequence of steps `f a = some a₁`, `f a₁ = some a₂`, ... such that `aₙ = b`.
This relation permits zero steps of the state transition function. -/
def Reaches {σ} (f : σ → Option σ) : σ → σ → Prop :=
  ReflTransGen fun a b ↦ b ∈ f a
#align turing.reaches Turing.Reaches

/-- The transitive closure of a state transition function. `Reaches₁ f a b` means there is a
nonempty finite sequence of steps `f a = some a₁`, `f a₁ = some a₂`, ... such that `aₙ = b`.
This relation does not permit zero steps of the state transition function. -/
def Reaches₁ {σ} (f : σ → Option σ) : σ → σ → Prop :=
  TransGen fun a b ↦ b ∈ f a
#align turing.reaches₁ Turing.Reaches₁

theorem reaches₁_eq {σ} {f : σ → Option σ} {a b c} (h : f a = f b) :
    Reaches₁ f a c ↔ Reaches₁ f b c :=
  TransGen.head'_iff.trans (TransGen.head'_iff.trans <| by rw [h]).symm
                                                           -- 🎉 no goals
#align turing.reaches₁_eq Turing.reaches₁_eq

theorem reaches_total {σ} {f : σ → Option σ} {a b c} (hab : Reaches f a b) (hac : Reaches f a c) :
    Reaches f b c ∨ Reaches f c b :=
  ReflTransGen.total_of_right_unique (fun _ _ _ ↦ Option.mem_unique) hab hac
#align turing.reaches_total Turing.reaches_total

theorem reaches₁_fwd {σ} {f : σ → Option σ} {a b c} (h₁ : Reaches₁ f a c) (h₂ : b ∈ f a) :
    Reaches f b c := by
  rcases TransGen.head'_iff.1 h₁ with ⟨b', hab, hbc⟩
  -- ⊢ Reaches f b c
  cases Option.mem_unique hab h₂; exact hbc
  -- ⊢ Reaches f b c
                                  -- 🎉 no goals
#align turing.reaches₁_fwd Turing.reaches₁_fwd

/-- A variation on `Reaches`. `Reaches₀ f a b` holds if whenever `Reaches₁ f b c` then
`Reaches₁ f a c`. This is a weaker property than `Reaches` and is useful for replacing states with
equivalent states without taking a step. -/
def Reaches₀ {σ} (f : σ → Option σ) (a b : σ) : Prop :=
  ∀ c, Reaches₁ f b c → Reaches₁ f a c
#align turing.reaches₀ Turing.Reaches₀

theorem Reaches₀.trans {σ} {f : σ → Option σ} {a b c : σ} (h₁ : Reaches₀ f a b)
    (h₂ : Reaches₀ f b c) : Reaches₀ f a c
  | _, h₃ => h₁ _ (h₂ _ h₃)
#align turing.reaches₀.trans Turing.Reaches₀.trans

@[refl]
theorem Reaches₀.refl {σ} {f : σ → Option σ} (a : σ) : Reaches₀ f a a
  | _, h => h
#align turing.reaches₀.refl Turing.Reaches₀.refl

theorem Reaches₀.single {σ} {f : σ → Option σ} {a b : σ} (h : b ∈ f a) : Reaches₀ f a b
  | _, h₂ => h₂.head h
#align turing.reaches₀.single Turing.Reaches₀.single

theorem Reaches₀.head {σ} {f : σ → Option σ} {a b c : σ} (h : b ∈ f a) (h₂ : Reaches₀ f b c) :
    Reaches₀ f a c :=
  (Reaches₀.single h).trans h₂
#align turing.reaches₀.head Turing.Reaches₀.head

theorem Reaches₀.tail {σ} {f : σ → Option σ} {a b c : σ} (h₁ : Reaches₀ f a b) (h : c ∈ f b) :
    Reaches₀ f a c :=
  h₁.trans (Reaches₀.single h)
#align turing.reaches₀.tail Turing.Reaches₀.tail

theorem reaches₀_eq {σ} {f : σ → Option σ} {a b} (e : f a = f b) : Reaches₀ f a b
  | _, h => (reaches₁_eq e).2 h
#align turing.reaches₀_eq Turing.reaches₀_eq

theorem Reaches₁.to₀ {σ} {f : σ → Option σ} {a b : σ} (h : Reaches₁ f a b) : Reaches₀ f a b
  | _, h₂ => h.trans h₂
#align turing.reaches₁.to₀ Turing.Reaches₁.to₀

theorem Reaches.to₀ {σ} {f : σ → Option σ} {a b : σ} (h : Reaches f a b) : Reaches₀ f a b
  | _, h₂ => h₂.trans_right h
#align turing.reaches.to₀ Turing.Reaches.to₀

theorem Reaches₀.tail' {σ} {f : σ → Option σ} {a b c : σ} (h : Reaches₀ f a b) (h₂ : c ∈ f b) :
    Reaches₁ f a c :=
  h _ (TransGen.single h₂)
#align turing.reaches₀.tail' Turing.Reaches₀.tail'

/-- (co-)Induction principle for `eval`. If a property `C` holds of any point `a` evaluating to `b`
which is either terminal (meaning `a = b`) or where the next point also satisfies `C`, then it
holds of any point where `eval f a` evaluates to `b`. This formalizes the notion that if
`eval f a` evaluates to `b` then it reaches terminal state `b` in finitely many steps. -/
@[elab_as_elim]
def evalInduction {σ} {f : σ → Option σ} {b : σ} {C : σ → Sort*} {a : σ}
    (h : b ∈ eval f a) (H : ∀ a, b ∈ eval f a → (∀ a', f a = some a' → C a') → C a) : C a :=
  PFun.fixInduction h fun a' ha' h' ↦
    H _ ha' fun b' e ↦ h' _ <| Part.mem_some_iff.2 <| by rw [e]; rfl
                                                         -- ⊢ Sum.inr b' = Option.elim (some b') (Sum.inl a') Sum.inr
                                                                 -- 🎉 no goals
#align turing.eval_induction Turing.evalInduction

theorem mem_eval {σ} {f : σ → Option σ} {a b} : b ∈ eval f a ↔ Reaches f a b ∧ f b = none := by
  refine' ⟨fun h ↦ _, fun ⟨h₁, h₂⟩ ↦ _⟩
  -- ⊢ Reaches f a b ∧ f b = none
  · -- Porting note: Explicitly specify `c`.
    refine' @evalInduction _ _ _ (fun a ↦ Reaches f a b ∧ f b = none) _ h fun a h IH ↦ _
    -- ⊢ (fun a => Reaches f a b ∧ f b = none) a
    cases' e : f a with a'
    -- ⊢ Reaches f a b ∧ f b = none
    · rw [Part.mem_unique h
          (PFun.mem_fix_iff.2 <| Or.inl <| Part.mem_some_iff.2 <| by rw [e] <;> rfl)]
      exact ⟨ReflTransGen.refl, e⟩
      -- 🎉 no goals
    · rcases PFun.mem_fix_iff.1 h with (h | ⟨_, h, _⟩) <;> rw [e] at h <;>
      -- ⊢ Reaches f a b ∧ f b = none
                                                           -- ⊢ Reaches f a b ∧ f b = none
                                                           -- ⊢ Reaches f a b ∧ f b = none
        cases Part.mem_some_iff.1 h
        -- 🎉 no goals
        -- ⊢ Reaches f a b ∧ f b = none
      cases' IH a' e with h₁ h₂
      -- ⊢ Reaches f a b ∧ f b = none
      exact ⟨ReflTransGen.head e h₁, h₂⟩
      -- 🎉 no goals
  · refine' ReflTransGen.head_induction_on h₁ _ fun h _ IH ↦ _
    -- ⊢ b ∈ eval f b
    · refine' PFun.mem_fix_iff.2 (Or.inl _)
      -- ⊢ Sum.inl b ∈ Part.some (Option.elim (f b) (Sum.inl b) Sum.inr)
      rw [h₂]
      -- ⊢ Sum.inl b ∈ Part.some (Option.elim none (Sum.inl b) Sum.inr)
      apply Part.mem_some
      -- 🎉 no goals
    · refine' PFun.mem_fix_iff.2 (Or.inr ⟨_, _, IH⟩)
      -- ⊢ Sum.inr c✝ ∈ Part.some (Option.elim (f a✝) (Sum.inl a✝) Sum.inr)
      rw [h]
      -- ⊢ Sum.inr c✝ ∈ Part.some (Option.elim (some c✝) (Sum.inl a✝) Sum.inr)
      apply Part.mem_some
      -- 🎉 no goals
#align turing.mem_eval Turing.mem_eval

theorem eval_maximal₁ {σ} {f : σ → Option σ} {a b} (h : b ∈ eval f a) (c) : ¬Reaches₁ f b c
  | bc => by
    let ⟨_, b0⟩ := mem_eval.1 h
    -- ⊢ False
    let ⟨b', h', _⟩ := TransGen.head'_iff.1 bc
    -- ⊢ False
    cases b0.symm.trans h'
    -- 🎉 no goals
#align turing.eval_maximal₁ Turing.eval_maximal₁

theorem eval_maximal {σ} {f : σ → Option σ} {a b} (h : b ∈ eval f a) {c} : Reaches f b c ↔ c = b :=
  let ⟨_, b0⟩ := mem_eval.1 h
  reflTransGen_iff_eq fun b' h' ↦ by cases b0.symm.trans h'
                                     -- 🎉 no goals
#align turing.eval_maximal Turing.eval_maximal

theorem reaches_eval {σ} {f : σ → Option σ} {a b} (ab : Reaches f a b) : eval f a = eval f b := by
  refine' Part.ext fun _ ↦ ⟨fun h ↦ _, fun h ↦ _⟩
  -- ⊢ x✝ ∈ eval f b
  · have ⟨ac, c0⟩ := mem_eval.1 h
    -- ⊢ x✝ ∈ eval f b
    exact mem_eval.2 ⟨(or_iff_left_of_imp fun cb ↦ (eval_maximal h).1 cb ▸ ReflTransGen.refl).1
      (reaches_total ab ac), c0⟩
  · have ⟨bc, c0⟩ := mem_eval.1 h
    -- ⊢ x✝ ∈ eval f a
    exact mem_eval.2 ⟨ab.trans bc, c0⟩
    -- 🎉 no goals
#align turing.reaches_eval Turing.reaches_eval

/-- Given a relation `tr : σ₁ → σ₂ → Prop` between state spaces, and state transition functions
`f₁ : σ₁ → Option σ₁` and `f₂ : σ₂ → Option σ₂`, `Respects f₁ f₂ tr` means that if `tr a₁ a₂` holds
initially and `f₁` takes a step to `a₂` then `f₂` will take one or more steps before reaching a
state `b₂` satisfying `tr a₂ b₂`, and if `f₁ a₁` terminates then `f₂ a₂` also terminates.
Such a relation `tr` is also known as a refinement. -/
def Respects {σ₁ σ₂} (f₁ : σ₁ → Option σ₁) (f₂ : σ₂ → Option σ₂) (tr : σ₁ → σ₂ → Prop) :=
  ∀ ⦃a₁ a₂⦄, tr a₁ a₂ → (match f₁ a₁ with
    | some b₁ => ∃ b₂, tr b₁ b₂ ∧ Reaches₁ f₂ a₂ b₂
    | none => f₂ a₂ = none : Prop)
#align turing.respects Turing.Respects

theorem tr_reaches₁ {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) {b₁} (ab : Reaches₁ f₁ a₁ b₁) : ∃ b₂, tr b₁ b₂ ∧ Reaches₁ f₂ a₂ b₂ := by
  induction' ab with c₁ ac c₁ d₁ _ cd IH
  -- ⊢ ∃ b₂, tr c₁ b₂ ∧ Reaches₁ f₂ a₂ b₂
  · have := H aa
    -- ⊢ ∃ b₂, tr c₁ b₂ ∧ Reaches₁ f₂ a₂ b₂
    rwa [show f₁ a₁ = _ from ac] at this
    -- 🎉 no goals
  · rcases IH with ⟨c₂, cc, ac₂⟩
    -- ⊢ ∃ b₂, tr d₁ b₂ ∧ Reaches₁ f₂ a₂ b₂
    have := H cc
    -- ⊢ ∃ b₂, tr d₁ b₂ ∧ Reaches₁ f₂ a₂ b₂
    rw [show f₁ c₁ = _ from cd] at this
    -- ⊢ ∃ b₂, tr d₁ b₂ ∧ Reaches₁ f₂ a₂ b₂
    rcases this with ⟨d₂, dd, cd₂⟩
    -- ⊢ ∃ b₂, tr d₁ b₂ ∧ Reaches₁ f₂ a₂ b₂
    exact ⟨_, dd, ac₂.trans cd₂⟩
    -- 🎉 no goals
#align turing.tr_reaches₁ Turing.tr_reaches₁

theorem tr_reaches {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) {b₁} (ab : Reaches f₁ a₁ b₁) : ∃ b₂, tr b₁ b₂ ∧ Reaches f₂ a₂ b₂ := by
  rcases reflTransGen_iff_eq_or_transGen.1 ab with (rfl | ab)
  -- ⊢ ∃ b₂, tr b₁ b₂ ∧ Reaches f₂ a₂ b₂
  · exact ⟨_, aa, ReflTransGen.refl⟩
    -- 🎉 no goals
  · have ⟨b₂, bb, h⟩ := tr_reaches₁ H aa ab
    -- ⊢ ∃ b₂, tr b₁ b₂ ∧ Reaches f₂ a₂ b₂
    exact ⟨b₂, bb, h.to_reflTransGen⟩
    -- 🎉 no goals
#align turing.tr_reaches Turing.tr_reaches

theorem tr_reaches_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) {b₂} (ab : Reaches f₂ a₂ b₂) :
    ∃ c₁ c₂, Reaches f₂ b₂ c₂ ∧ tr c₁ c₂ ∧ Reaches f₁ a₁ c₁ := by
  induction' ab with c₂ d₂ _ cd IH
  -- ⊢ ∃ c₁ c₂, Reaches f₂ a₂ c₂ ∧ tr c₁ c₂ ∧ Reaches f₁ a₁ c₁
  · exact ⟨_, _, ReflTransGen.refl, aa, ReflTransGen.refl⟩
    -- 🎉 no goals
  · rcases IH with ⟨e₁, e₂, ce, ee, ae⟩
    -- ⊢ ∃ c₁ c₂, Reaches f₂ d₂ c₂ ∧ tr c₁ c₂ ∧ Reaches f₁ a₁ c₁
    rcases ReflTransGen.cases_head ce with (rfl | ⟨d', cd', de⟩)
    -- ⊢ ∃ c₁ c₂, Reaches f₂ d₂ c₂ ∧ tr c₁ c₂ ∧ Reaches f₁ a₁ c₁
    · have := H ee
      -- ⊢ ∃ c₁ c₂, Reaches f₂ d₂ c₂ ∧ tr c₁ c₂ ∧ Reaches f₁ a₁ c₁
      revert this
      -- ⊢ (match f₁ e₁ with
      cases' eg : f₁ e₁ with g₁ <;> simp only [Respects, and_imp, exists_imp]
                                    -- ⊢ f₂ c₂ = none → ∃ c₁ c₂, Reaches f₂ d₂ c₂ ∧ tr c₁ c₂ ∧ Reaches f₁ a₁ c₁
                                    -- ⊢ ∀ (x : σ₂), tr g₁ x → Reaches₁ f₂ c₂ x → ∃ c₁ c₂, Reaches f₂ d₂ c₂ ∧ tr c₁ c …
      · intro c0
        -- ⊢ ∃ c₁ c₂, Reaches f₂ d₂ c₂ ∧ tr c₁ c₂ ∧ Reaches f₁ a₁ c₁
        cases cd.symm.trans c0
        -- 🎉 no goals
      · intro g₂ gg cg
        -- ⊢ ∃ c₁ c₂, Reaches f₂ d₂ c₂ ∧ tr c₁ c₂ ∧ Reaches f₁ a₁ c₁
        rcases TransGen.head'_iff.1 cg with ⟨d', cd', dg⟩
        -- ⊢ ∃ c₁ c₂, Reaches f₂ d₂ c₂ ∧ tr c₁ c₂ ∧ Reaches f₁ a₁ c₁
        cases Option.mem_unique cd cd'
        -- ⊢ ∃ c₁ c₂, Reaches f₂ d₂ c₂ ∧ tr c₁ c₂ ∧ Reaches f₁ a₁ c₁
        exact ⟨_, _, dg, gg, ae.tail eg⟩
        -- 🎉 no goals
    · cases Option.mem_unique cd cd'
      -- ⊢ ∃ c₁ c₂, Reaches f₂ d₂ c₂ ∧ tr c₁ c₂ ∧ Reaches f₁ a₁ c₁
      exact ⟨_, _, de, ee, ae⟩
      -- 🎉 no goals
#align turing.tr_reaches_rev Turing.tr_reaches_rev

theorem tr_eval {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ b₁ a₂}
    (aa : tr a₁ a₂) (ab : b₁ ∈ eval f₁ a₁) : ∃ b₂, tr b₁ b₂ ∧ b₂ ∈ eval f₂ a₂ := by
  cases' mem_eval.1 ab with ab b0
  -- ⊢ ∃ b₂, tr b₁ b₂ ∧ b₂ ∈ eval f₂ a₂
  rcases tr_reaches H aa ab with ⟨b₂, bb, ab⟩
  -- ⊢ ∃ b₂, tr b₁ b₂ ∧ b₂ ∈ eval f₂ a₂
  refine' ⟨_, bb, mem_eval.2 ⟨ab, _⟩⟩
  -- ⊢ f₂ b₂ = none
  have := H bb; rwa [b0] at this
  -- ⊢ f₂ b₂ = none
                -- 🎉 no goals
#align turing.tr_eval Turing.tr_eval

theorem tr_eval_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ b₂ a₂}
    (aa : tr a₁ a₂) (ab : b₂ ∈ eval f₂ a₂) : ∃ b₁, tr b₁ b₂ ∧ b₁ ∈ eval f₁ a₁ := by
  cases' mem_eval.1 ab with ab b0
  -- ⊢ ∃ b₁, tr b₁ b₂ ∧ b₁ ∈ eval f₁ a₁
  rcases tr_reaches_rev H aa ab with ⟨c₁, c₂, bc, cc, ac⟩
  -- ⊢ ∃ b₁, tr b₁ b₂ ∧ b₁ ∈ eval f₁ a₁
  cases (reflTransGen_iff_eq (Option.eq_none_iff_forall_not_mem.1 b0)).1 bc
  -- ⊢ ∃ b₁, tr b₁ b₂ ∧ b₁ ∈ eval f₁ a₁
  refine' ⟨_, cc, mem_eval.2 ⟨ac, _⟩⟩
  -- ⊢ f₁ c₁ = none
  have := H cc
  -- ⊢ f₁ c₁ = none
  cases' hfc : f₁ c₁ with d₁
  · rfl
    -- 🎉 no goals
  rw [hfc] at this
  -- ⊢ some d₁ = none
  rcases this with ⟨d₂, _, bd⟩
  -- ⊢ some d₁ = none
  rcases TransGen.head'_iff.1 bd with ⟨e, h, _⟩
  -- ⊢ some d₁ = none
  cases b0.symm.trans h
  -- 🎉 no goals
#align turing.tr_eval_rev Turing.tr_eval_rev

theorem tr_eval_dom {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop} (H : Respects f₁ f₂ tr) {a₁ a₂}
    (aa : tr a₁ a₂) : (eval f₂ a₂).Dom ↔ (eval f₁ a₁).Dom :=
  ⟨fun h ↦
    let ⟨_, _, h, _⟩ := tr_eval_rev H aa ⟨h, rfl⟩
    h,
    fun h ↦
    let ⟨_, _, h, _⟩ := tr_eval H aa ⟨h, rfl⟩
    h⟩
#align turing.tr_eval_dom Turing.tr_eval_dom

/-- A simpler version of `Respects` when the state transition relation `tr` is a function. -/
def FRespects {σ₁ σ₂} (f₂ : σ₂ → Option σ₂) (tr : σ₁ → σ₂) (a₂ : σ₂) : Option σ₁ → Prop
  | some b₁ => Reaches₁ f₂ a₂ (tr b₁)
  | none => f₂ a₂ = none
#align turing.frespects Turing.FRespects

theorem frespects_eq {σ₁ σ₂} {f₂ : σ₂ → Option σ₂} {tr : σ₁ → σ₂} {a₂ b₂} (h : f₂ a₂ = f₂ b₂) :
    ∀ {b₁}, FRespects f₂ tr a₂ b₁ ↔ FRespects f₂ tr b₂ b₁
  | some b₁ => reaches₁_eq h
  | none => by unfold FRespects; rw [h]
               -- ⊢ (match none with
                                 -- 🎉 no goals
#align turing.frespects_eq Turing.frespects_eq

theorem fun_respects {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂} :
    (Respects f₁ f₂ fun a b ↦ tr a = b) ↔ ∀ ⦃a₁⦄, FRespects f₂ tr (tr a₁) (f₁ a₁) :=
  forall_congr' fun a₁ ↦ by
    cases f₁ a₁ <;> simp only [FRespects, Respects, exists_eq_left', forall_eq']
                    -- 🎉 no goals
                    -- 🎉 no goals
#align turing.fun_respects Turing.fun_respects

theorem tr_eval' {σ₁ σ₂} (f₁ : σ₁ → Option σ₁) (f₂ : σ₂ → Option σ₂) (tr : σ₁ → σ₂)
    (H : Respects f₁ f₂ fun a b ↦ tr a = b) (a₁) : eval f₂ (tr a₁) = tr <$> eval f₁ a₁ :=
  Part.ext fun b₂ ↦
    ⟨fun h ↦
      let ⟨b₁, bb, hb⟩ := tr_eval_rev H rfl h
      (Part.mem_map_iff _).2 ⟨b₁, hb, bb⟩,
      fun h ↦ by
      rcases(Part.mem_map_iff _).1 h with ⟨b₁, ab, bb⟩
      -- ⊢ b₂ ∈ eval f₂ (tr a₁)
      rcases tr_eval H rfl ab with ⟨_, rfl, h⟩
      -- ⊢ b₂ ∈ eval f₂ (tr a₁)
      rwa [bb] at h⟩
      -- 🎉 no goals
#align turing.tr_eval' Turing.tr_eval'

/-!
## The TM0 model

A TM0 turing machine is essentially a Post-Turing machine, adapted for type theory.

A Post-Turing machine with symbol type `Γ` and label type `Λ` is a function
`Λ → Γ → Option (Λ × Stmt)`, where a `Stmt` can be either `move left`, `move right` or `write a`
for `a : Γ`. The machine works over a "tape", a doubly-infinite sequence of elements of `Γ`, and
an instantaneous configuration, `Cfg`, is a label `q : Λ` indicating the current internal state of
the machine, and a `Tape Γ` (which is essentially `ℤ →₀ Γ`). The evolution is described by the
`step` function:

* If `M q T.head = none`, then the machine halts.
* If `M q T.head = some (q', s)`, then the machine performs action `s : Stmt` and then transitions
  to state `q'`.

The initial state takes a `List Γ` and produces a `Tape Γ` where the head of the list is the head
of the tape and the rest of the list extends to the right, with the left side all blank. The final
state takes the entire right side of the tape right or equal to the current position of the
machine. (This is actually a `ListBlank Γ`, not a `List Γ`, because we don't know, at this level
of generality, where the output ends. If equality to `default : Γ` is decidable we can trim the list
to remove the infinite tail of blanks.)
-/


namespace TM0

-- "TM0"
set_option linter.uppercaseLean3 false

section

variable (Γ : Type*) [Inhabited Γ]

-- type of tape symbols
variable (Λ : Type*) [Inhabited Λ]

-- type of "labels" or TM states
/-- A Turing machine "statement" is just a command to either move
  left or right, or write a symbol on the tape. -/
inductive Stmt
  | move : Dir → Stmt
  | write : Γ → Stmt
#align turing.TM0.stmt Turing.TM0.Stmt

local notation "Stmt₀" => Stmt Γ  -- Porting note: Added this to clean up types.

instance Stmt.inhabited : Inhabited Stmt₀ :=
  ⟨Stmt.write default⟩
#align turing.TM0.stmt.inhabited Turing.TM0.Stmt.inhabited

/-- A Post-Turing machine with symbol type `Γ` and label type `Λ`
  is a function which, given the current state `q : Λ` and
  the tape head `a : Γ`, either halts (returns `none`) or returns
  a new state `q' : Λ` and a `Stmt` describing what to do,
  either a move left or right, or a write command.

  Both `Λ` and `Γ` are required to be inhabited; the default value
  for `Γ` is the "blank" tape value, and the default value of `Λ` is
  the initial state. -/
@[nolint unusedArguments] -- this is a deliberate addition, see comment
def Machine [Inhabited Λ] :=
  Λ → Γ → Option (Λ × Stmt₀)
#align turing.TM0.machine Turing.TM0.Machine

local notation "Machine₀" => Machine Γ Λ  -- Porting note: Added this to clean up types.

instance Machine.inhabited : Inhabited Machine₀ := by
  unfold Machine; infer_instance
  -- ⊢ Inhabited (Λ → Γ → Option (Λ × Stmt₀))
                  -- 🎉 no goals
#align turing.TM0.machine.inhabited Turing.TM0.Machine.inhabited

/-- The configuration state of a Turing machine during operation
  consists of a label (machine state), and a tape, represented in
  the form `(a, L, R)` meaning the tape looks like `L.rev ++ [a] ++ R`
  with the machine currently reading the `a`. The lists are
  automatically extended with blanks as the machine moves around. -/
structure Cfg where
  q : Λ
  Tape : Tape Γ
#align turing.TM0.cfg Turing.TM0.Cfg

local notation "Cfg₀" => Cfg Γ Λ  -- Porting note: Added this to clean up types.

instance Cfg.inhabited : Inhabited Cfg₀ :=
  ⟨⟨default, default⟩⟩
#align turing.TM0.cfg.inhabited Turing.TM0.Cfg.inhabited

variable {Γ Λ}

/-- Execution semantics of the Turing machine. -/
def step (M : Machine₀) : Cfg₀ → Option Cfg₀ :=
  fun ⟨q, T⟩ ↦ (M q T.1).map fun ⟨q', a⟩ ↦ ⟨q', match a with
    | Stmt.move d => T.move d
    | Stmt.write a => T.write a⟩
#align turing.TM0.step Turing.TM0.step

/-- The statement `Reaches M s₁ s₂` means that `s₂` is obtained
  starting from `s₁` after a finite number of steps from `s₂`. -/
def Reaches (M : Machine₀) : Cfg₀ → Cfg₀ → Prop :=
  ReflTransGen fun a b ↦ b ∈ step M a
#align turing.TM0.reaches Turing.TM0.Reaches

/-- The initial configuration. -/
def init (l : List Γ) : Cfg₀ :=
  ⟨default, Tape.mk₁ l⟩
#align turing.TM0.init Turing.TM0.init

/-- Evaluate a Turing machine on initial input to a final state,
  if it terminates. -/
def eval (M : Machine₀) (l : List Γ) : Part (ListBlank Γ) :=
  (Turing.eval (step M) (init l)).map fun c ↦ c.Tape.right₀
#align turing.TM0.eval Turing.TM0.eval

/-- The raw definition of a Turing machine does not require that
  `Γ` and `Λ` are finite, and in practice we will be interested
  in the infinite `Λ` case. We recover instead a notion of
  "effectively finite" Turing machines, which only make use of a
  finite subset of their states. We say that a set `S ⊆ Λ`
  supports a Turing machine `M` if `S` is closed under the
  transition function and contains the initial state. -/
def Supports (M : Machine₀) (S : Set Λ) :=
  default ∈ S ∧ ∀ {q a q' s}, (q', s) ∈ M q a → q ∈ S → q' ∈ S
#align turing.TM0.supports Turing.TM0.Supports

theorem step_supports (M : Machine₀) {S : Set Λ} (ss : Supports M S) :
    ∀ {c c' : Cfg₀}, c' ∈ step M c → c.q ∈ S → c'.q ∈ S := by
  intro ⟨q, T⟩ c' h₁ h₂
  -- ⊢ c'.q ∈ S
  rcases Option.map_eq_some'.1 h₁ with ⟨⟨q', a⟩, h, rfl⟩
  -- ⊢ ((fun x =>
  exact ss.2 h h₂
  -- 🎉 no goals
#align turing.TM0.step_supports Turing.TM0.step_supports

theorem univ_supports (M : Machine₀) : Supports M Set.univ := by
  constructor <;> intros <;> apply Set.mem_univ
  -- ⊢ default ∈ Set.univ
                  -- ⊢ default ∈ Set.univ
                  -- ⊢ q'✝ ∈ Set.univ
                             -- 🎉 no goals
                             -- 🎉 no goals
#align turing.TM0.univ_supports Turing.TM0.univ_supports

end

section

variable {Γ : Type*} [Inhabited Γ]

variable {Γ' : Type*} [Inhabited Γ']

variable {Λ : Type*} [Inhabited Λ]

variable {Λ' : Type*} [Inhabited Λ']

/-- Map a TM statement across a function. This does nothing to move statements and maps the write
values. -/
def Stmt.map (f : PointedMap Γ Γ') : Stmt Γ → Stmt Γ'
  | Stmt.move d => Stmt.move d
  | Stmt.write a => Stmt.write (f a)
#align turing.TM0.stmt.map Turing.TM0.Stmt.map

/-- Map a configuration across a function, given `f : Γ → Γ'` a map of the alphabets and
`g : Λ → Λ'` a map of the machine states. -/
def Cfg.map (f : PointedMap Γ Γ') (g : Λ → Λ') : Cfg Γ Λ → Cfg Γ' Λ'
  | ⟨q, T⟩ => ⟨g q, T.map f⟩
#align turing.TM0.cfg.map Turing.TM0.Cfg.map

variable (M : Machine Γ Λ) (f₁ : PointedMap Γ Γ') (f₂ : PointedMap Γ' Γ) (g₁ : Λ → Λ') (g₂ : Λ' → Λ)

/-- Because the state transition function uses the alphabet and machine states in both the input
and output, to map a machine from one alphabet and machine state space to another we need functions
in both directions, essentially an `Equiv` without the laws. -/
def Machine.map : Machine Γ' Λ'
  | q, l => (M (g₂ q) (f₂ l)).map (Prod.map g₁ (Stmt.map f₁))
#align turing.TM0.machine.map Turing.TM0.Machine.map

theorem Machine.map_step {S : Set Λ} (f₂₁ : Function.RightInverse f₁ f₂)
    (g₂₁ : ∀ q ∈ S, g₂ (g₁ q) = q) :
    ∀ c : Cfg Γ Λ,
      c.q ∈ S → (step M c).map (Cfg.map f₁ g₁) = step (M.map f₁ f₂ g₁ g₂) (Cfg.map f₁ g₁ c)
  | ⟨q, T⟩, h => by
    unfold step Machine.map Cfg.map
    -- ⊢ Option.map
    simp only [Turing.Tape.map_fst, g₂₁ q h, f₂₁ _]
    -- ⊢ Option.map (fun x => { q := g₁ x.q, Tape := Tape.map f₁ x.Tape })
    rcases M q T.1 with (_ | ⟨q', d | a⟩); · rfl
                                             -- 🎉 no goals
    · simp only [step, Cfg.map, Option.map_some', Tape.map_move f₁]
      -- ⊢ some { q := g₁ q', Tape := Tape.move d (Tape.map f₁ T) } =
      rfl
      -- 🎉 no goals
    · simp only [step, Cfg.map, Option.map_some', Tape.map_write]
      -- ⊢ some { q := g₁ q', Tape := Tape.write (PointedMap.f f₁ a) (Tape.map f₁ T) } =
      rfl
      -- 🎉 no goals
#align turing.TM0.machine.map_step Turing.TM0.Machine.map_step

theorem map_init (g₁ : PointedMap Λ Λ') (l : List Γ) : (init l).map f₁ g₁ = init (l.map f₁) :=
  congr (congr_arg Cfg.mk g₁.map_pt) (Tape.map_mk₁ _ _)
#align turing.TM0.map_init Turing.TM0.map_init

theorem Machine.map_respects (g₁ : PointedMap Λ Λ') (g₂ : Λ' → Λ) {S} (ss : Supports M S)
    (f₂₁ : Function.RightInverse f₁ f₂) (g₂₁ : ∀ q ∈ S, g₂ (g₁ q) = q) :
    Respects (step M) (step (M.map f₁ f₂ g₁ g₂)) fun a b ↦ a.q ∈ S ∧ Cfg.map f₁ g₁ a = b := by
  intro c _ ⟨cs, rfl⟩
  -- ⊢ match step M c with
  cases e : step M c
  · rw [← M.map_step f₁ f₂ g₁ g₂ f₂₁ g₂₁ _ cs, e]
    -- ⊢ match none with
    rfl
    -- 🎉 no goals
  · refine' ⟨_, ⟨step_supports M ss e cs, rfl⟩, TransGen.single _⟩
    -- ⊢ Cfg.map f₁ g₁.f val✝ ∈ step (map M f₁ f₂ g₁.f g₂) (Cfg.map f₁ g₁.f c)
    rw [← M.map_step f₁ f₂ g₁ g₂ f₂₁ g₂₁ _ cs, e]
    -- ⊢ Cfg.map f₁ g₁.f val✝ ∈ Option.map (Cfg.map f₁ g₁.f) (some val✝)
    rfl
    -- 🎉 no goals
#align turing.TM0.machine.map_respects Turing.TM0.Machine.map_respects

end

end TM0

/-!
## The TM1 model

The TM1 model is a simplification and extension of TM0 (Post-Turing model) in the direction of
Wang B-machines. The machine's internal state is extended with a (finite) store `σ` of variables
that may be accessed and updated at any time.

A machine is given by a `Λ` indexed set of procedures or functions. Each function has a body which
is a `Stmt`. Most of the regular commands are allowed to use the current value `a` of the local
variables and the value `T.head` on the tape to calculate what to write or how to change local
state, but the statements themselves have a fixed structure. The `Stmt`s can be as follows:

* `move d q`: move left or right, and then do `q`
* `write (f : Γ → σ → Γ) q`: write `f a T.head` to the tape, then do `q`
* `load (f : Γ → σ → σ) q`: change the internal state to `f a T.head`
* `branch (f : Γ → σ → Bool) qtrue qfalse`: If `f a T.head` is true, do `qtrue`, else `qfalse`
* `goto (f : Γ → σ → Λ)`: Go to label `f a T.head`
* `halt`: Transition to the halting state, which halts on the following step

Note that here most statements do not have labels; `goto` commands can only go to a new function.
Only the `goto` and `halt` statements actually take a step; the rest is done by recursion on
statements and so take 0 steps. (There is a uniform bound on many statements can be executed before
the next `goto`, so this is an `O(1)` speedup with the constant depending on the machine.)

The `halt` command has a one step stutter before actually halting so that any changes made before
the halt have a chance to be "committed", since the `eval` relation uses the final configuration
before the halt as the output, and `move` and `write` etc. take 0 steps in this model.
-/


namespace TM1

-- "TM1"
set_option linter.uppercaseLean3 false

section

variable (Γ : Type*) [Inhabited Γ]

-- Type of tape symbols
variable (Λ : Type*)

-- Type of function labels
variable (σ : Type*)

-- Type of variable settings
/-- The TM1 model is a simplification and extension of TM0
  (Post-Turing model) in the direction of Wang B-machines. The machine's
  internal state is extended with a (finite) store `σ` of variables
  that may be accessed and updated at any time.
  A machine is given by a `Λ` indexed set of procedures or functions.
  Each function has a body which is a `Stmt`, which can either be a
  `move` or `write` command, a `branch` (if statement based on the
  current tape value), a `load` (set the variable value),
  a `goto` (call another function), or `halt`. Note that here
  most statements do not have labels; `goto` commands can only
  go to a new function. All commands have access to the variable value
  and current tape value. -/
inductive Stmt
  | move : Dir → Stmt → Stmt
  | write : (Γ → σ → Γ) → Stmt → Stmt
  | load : (Γ → σ → σ) → Stmt → Stmt
  | branch : (Γ → σ → Bool) → Stmt → Stmt → Stmt
  | goto : (Γ → σ → Λ) → Stmt
  | halt : Stmt
#align turing.TM1.stmt Turing.TM1.Stmt

local notation "Stmt₁" => Stmt Γ Λ σ  -- Porting note: Added this to clean up types.

open Stmt

instance Stmt.inhabited : Inhabited Stmt₁ :=
  ⟨halt⟩
#align turing.TM1.stmt.inhabited Turing.TM1.Stmt.inhabited

/-- The configuration of a TM1 machine is given by the currently
  evaluating statement, the variable store value, and the tape. -/
structure Cfg where
  l : Option Λ
  var : σ
  Tape : Tape Γ
#align turing.TM1.cfg Turing.TM1.Cfg

local notation "Cfg₁" => Cfg Γ Λ σ  -- Porting note: Added this to clean up types.

instance Cfg.inhabited [Inhabited σ] : Inhabited Cfg₁ :=
  ⟨⟨default, default, default⟩⟩
#align turing.TM1.cfg.inhabited Turing.TM1.Cfg.inhabited

variable {Γ Λ σ}

/-- The semantics of TM1 evaluation. -/
def stepAux : Stmt₁ → σ → Tape Γ → Cfg₁
  | move d q, v, T => stepAux q v (T.move d)
  | write a q, v, T => stepAux q v (T.write (a T.1 v))
  | load s q, v, T => stepAux q (s T.1 v) T
  | branch p q₁ q₂, v, T => cond (p T.1 v) (stepAux q₁ v T) (stepAux q₂ v T)
  | goto l, v, T => ⟨some (l T.1 v), v, T⟩
  | halt, v, T => ⟨none, v, T⟩
#align turing.TM1.step_aux Turing.TM1.stepAux

/-- The state transition function. -/
def step (M : Λ → Stmt₁) : Cfg₁ → Option Cfg₁
  | ⟨none, _, _⟩ => none
  | ⟨some l, v, T⟩ => some (stepAux (M l) v T)
#align turing.TM1.step Turing.TM1.step

/-- A set `S` of labels supports the statement `q` if all the `goto`
  statements in `q` refer only to other functions in `S`. -/
def SupportsStmt (S : Finset Λ) : Stmt₁ → Prop
  | move _ q => SupportsStmt S q
  | write _ q => SupportsStmt S q
  | load _ q => SupportsStmt S q
  | branch _ q₁ q₂ => SupportsStmt S q₁ ∧ SupportsStmt S q₂
  | goto l => ∀ a v, l a v ∈ S
  | halt => True
#align turing.TM1.supports_stmt Turing.TM1.SupportsStmt

open Classical

/-- The subterm closure of a statement. -/
noncomputable def stmts₁ : Stmt₁ → Finset Stmt₁
  | Q@(move _ q) => insert Q (stmts₁ q)
  | Q@(write _ q) => insert Q (stmts₁ q)
  | Q@(load _ q) => insert Q (stmts₁ q)
  | Q@(branch _ q₁ q₂) => insert Q (stmts₁ q₁ ∪ stmts₁ q₂)
  | Q => {Q}
#align turing.TM1.stmts₁ Turing.TM1.stmts₁

theorem stmts₁_self {q : Stmt₁} : q ∈ stmts₁ q := by
  cases q <;> simp only [stmts₁, Finset.mem_insert_self, Finset.mem_singleton_self]
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
#align turing.TM1.stmts₁_self Turing.TM1.stmts₁_self

theorem stmts₁_trans {q₁ q₂ : Stmt₁} : q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ := by
  intro h₁₂ q₀ h₀₁
  -- ⊢ q₀ ∈ stmts₁ q₂
  induction' q₂ with _ q IH _ q IH _ q IH <;> simp only [stmts₁] at h₁₂ ⊢ <;>
                                              -- ⊢ q₀ ∈ insert (move a✝ q) (stmts₁ q)
                                              -- ⊢ q₀ ∈ insert (write a✝ q) (stmts₁ q)
                                              -- ⊢ q₀ ∈ insert (load a✝ q) (stmts₁ q)
                                              -- ⊢ q₀ ∈ insert (branch a✝² a✝¹ a✝) (stmts₁ a✝¹ ∪ stmts₁ a✝)
                                              -- ⊢ q₀ ∈ {goto a✝}
                                              -- ⊢ q₀ ∈ {halt}
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at h₁₂
    -- ⊢ q₀ ∈ insert (move a✝ q) (stmts₁ q)
    -- ⊢ q₀ ∈ insert (write a✝ q) (stmts₁ q)
    -- ⊢ q₀ ∈ insert (load a✝ q) (stmts₁ q)
    -- ⊢ q₀ ∈ insert (branch a✝² a✝¹ a✝) (stmts₁ a✝¹ ∪ stmts₁ a✝)
    -- ⊢ q₀ ∈ {goto a✝}
    -- ⊢ q₀ ∈ {halt}
  iterate 3
    rcases h₁₂ with (rfl | h₁₂)
    · unfold stmts₁ at h₀₁
      exact h₀₁
    · exact Finset.mem_insert_of_mem (IH h₁₂)
  case branch p q₁ q₂ IH₁ IH₂ =>
    rcases h₁₂ with (rfl | h₁₂ | h₁₂)
    · unfold stmts₁ at h₀₁
      exact h₀₁
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ <| IH₁ h₁₂)
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ <| IH₂ h₁₂)
  case goto l => subst h₁₂; exact h₀₁
  -- ⊢ q₀ ∈ {halt}
  -- 🎉 no goals
  case halt => subst h₁₂; exact h₀₁
  -- 🎉 no goals
  -- 🎉 no goals
#align turing.TM1.stmts₁_trans Turing.TM1.stmts₁_trans

theorem stmts₁_supportsStmt_mono {S : Finset Λ} {q₁ q₂ : Stmt₁} (h : q₁ ∈ stmts₁ q₂)
    (hs : SupportsStmt S q₂) : SupportsStmt S q₁ := by
  induction' q₂ with _ q IH _ q IH _ q IH <;>
    simp only [stmts₁, SupportsStmt, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      at h hs
  iterate 3 rcases h with (rfl | h) <;> [exact hs; exact IH h hs]
  case branch p q₁ q₂ IH₁ IH₂ => rcases h with (rfl | h | h); exacts [hs, IH₁ h hs.1, IH₂ h hs.2]
  -- ⊢ SupportsStmt S q₁
  -- 🎉 no goals
  case goto l => subst h; exact hs
  -- ⊢ SupportsStmt S q₁
  -- 🎉 no goals
  case halt => subst h; trivial
  -- 🎉 no goals
  -- 🎉 no goals
#align turing.TM1.stmts₁_supports_stmt_mono Turing.TM1.stmts₁_supportsStmt_mono

/-- The set of all statements in a turing machine, plus one extra value `none` representing the
halt state. This is used in the TM1 to TM0 reduction. -/
noncomputable def stmts (M : Λ → Stmt₁) (S : Finset Λ) : Finset (Option Stmt₁) :=
  Finset.insertNone (S.biUnion fun q ↦ stmts₁ (M q))
#align turing.TM1.stmts Turing.TM1.stmts

theorem stmts_trans {M : Λ → Stmt₁} {S : Finset Λ} {q₁ q₂ : Stmt₁} (h₁ : q₁ ∈ stmts₁ q₂) :
    some q₂ ∈ stmts M S → some q₁ ∈ stmts M S := by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h₂ ↦ ⟨_, ls, stmts₁_trans h₂ h₁⟩
  -- 🎉 no goals
#align turing.TM1.stmts_trans Turing.TM1.stmts_trans

variable [Inhabited Λ]

/-- A set `S` of labels supports machine `M` if all the `goto`
  statements in the functions in `S` refer only to other functions
  in `S`. -/
def Supports (M : Λ → Stmt₁) (S : Finset Λ) :=
  default ∈ S ∧ ∀ q ∈ S, SupportsStmt S (M q)
#align turing.TM1.supports Turing.TM1.Supports

theorem stmts_supportsStmt {M : Λ → Stmt₁} {S : Finset Λ} {q : Stmt₁} (ss : Supports M S) :
    some q ∈ stmts M S → SupportsStmt S q := by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h ↦ stmts₁_supportsStmt_mono h (ss.2 _ ls)
  -- 🎉 no goals
#align turing.TM1.stmts_supports_stmt Turing.TM1.stmts_supportsStmt

theorem step_supports (M : Λ → Stmt₁) {S : Finset Λ} (ss : Supports M S) :
    ∀ {c c' : Cfg₁}, c' ∈ step M c → c.l ∈ Finset.insertNone S → c'.l ∈ Finset.insertNone S
  | ⟨some l₁, v, T⟩, c', h₁, h₂ => by
    replace h₂ := ss.2 _ (Finset.some_mem_insertNone.1 h₂)
    -- ⊢ c'.l ∈ ↑Finset.insertNone S
    simp only [step, Option.mem_def, Option.some.injEq] at h₁; subst c'
    -- ⊢ c'.l ∈ ↑Finset.insertNone S
                                                               -- ⊢ (stepAux (M l₁) v T).l ∈ ↑Finset.insertNone S
    revert h₂; induction' M l₁ with _ q IH _ q IH _ q IH generalizing v T <;> intro hs
    -- ⊢ SupportsStmt S (M l₁) → (stepAux (M l₁) v T).l ∈ ↑Finset.insertNone S
                                                                              -- ⊢ (stepAux (move a✝ q) v T).l ∈ ↑Finset.insertNone S
                                                                              -- ⊢ (stepAux (write a✝ q) v T).l ∈ ↑Finset.insertNone S
                                                                              -- ⊢ (stepAux (load a✝ q) v T).l ∈ ↑Finset.insertNone S
                                                                              -- ⊢ (stepAux (branch a✝² a✝¹ a✝) v T).l ∈ ↑Finset.insertNone S
                                                                              -- ⊢ (stepAux (goto a✝) v T).l ∈ ↑Finset.insertNone S
                                                                              -- ⊢ (stepAux halt v T).l ∈ ↑Finset.insertNone S
    iterate 3 exact IH _ _ hs
    case branch p q₁' q₂' IH₁ IH₂ =>
      unfold stepAux; cases p T.1 v
      · exact IH₂ _ _ hs.2
      · exact IH₁ _ _ hs.1
    case goto => exact Finset.some_mem_insertNone.2 (hs _ _)
    -- ⊢ (stepAux halt v T).l ∈ ↑Finset.insertNone S
    -- 🎉 no goals
    case halt => apply Multiset.mem_cons_self
    -- 🎉 no goals
    -- 🎉 no goals
#align turing.TM1.step_supports Turing.TM1.step_supports

variable [Inhabited σ]

/-- The initial state, given a finite input that is placed on the tape starting at the TM head and
going to the right. -/
def init (l : List Γ) : Cfg₁ :=
  ⟨some default, default, Tape.mk₁ l⟩
#align turing.TM1.init Turing.TM1.init

/-- Evaluate a TM to completion, resulting in an output list on the tape (with an indeterminate
number of blanks on the end). -/
def eval (M : Λ → Stmt₁) (l : List Γ) : Part (ListBlank Γ) :=
  (Turing.eval (step M) (init l)).map fun c ↦ c.Tape.right₀
#align turing.TM1.eval Turing.TM1.eval

end

end TM1

/-!
## TM1 emulator in TM0

To prove that TM1 computable functions are TM0 computable, we need to reduce each TM1 program to a
TM0 program. So suppose a TM1 program is given. We take the following:

* The alphabet `Γ` is the same for both TM1 and TM0
* The set of states `Λ'` is defined to be `Option Stmt₁ × σ`, that is, a TM1 statement or `none`
  representing halt, and the possible settings of the internal variables.
  Note that this is an infinite set, because `Stmt₁` is infinite. This is okay because we assume
  that from the initial TM1 state, only finitely many other labels are reachable, and there are
  only finitely many statements that appear in all of these functions.

Even though `Stmt₁` contains a statement called `halt`, we must separate it from `none`
(`some halt` steps to `none` and `none` actually halts) because there is a one step stutter in the
TM1 semantics.
-/


namespace TM1to0

-- "TM1to0"
set_option linter.uppercaseLean3 false

section

variable {Γ : Type*} [Inhabited Γ]

variable {Λ : Type*} [Inhabited Λ]

variable {σ : Type*} [Inhabited σ]

local notation "Stmt₁" => TM1.Stmt Γ Λ σ

local notation "Cfg₁" => TM1.Cfg Γ Λ σ

local notation "Stmt₀" => TM0.Stmt Γ

variable (M : Λ → TM1.Stmt Γ Λ σ)  -- Porting note: Unfolded `Stmt₁`.

-- Porting note: `Inhabited`s are not necessary, but `M` is necessary.
set_option linter.unusedVariables false in
/-- The base machine state space is a pair of an `Option Stmt₁` representing the current program
to be executed, or `none` for the halt state, and a `σ` which is the local state (stored in the TM,
not the tape). Because there are an infinite number of programs, this state space is infinite, but
for a finitely supported TM1 machine and a finite type `σ`, only finitely many of these states are
reachable. -/
@[nolint unusedArguments] -- We need the M assumption
def Λ' (M : Λ → TM1.Stmt Γ Λ σ) :=
  Option Stmt₁ × σ
#align turing.TM1to0.Λ' Turing.TM1to0.Λ'

local notation "Λ'₁₀" => Λ' M -- Porting note: Added this to clean up types.

instance : Inhabited Λ'₁₀ :=
  ⟨(some (M default), default)⟩

open TM0.Stmt

/-- The core TM1 → TM0 translation function. Here `s` is the current value on the tape, and the
`Stmt₁` is the TM1 statement to translate, with local state `v : σ`. We evaluate all regular
instructions recursively until we reach either a `move` or `write` command, or a `goto`; in the
latter case we emit a dummy `write s` step and transition to the new target location. -/
def trAux (s : Γ) : Stmt₁ → σ → Λ'₁₀ × Stmt₀
  | TM1.Stmt.move d q, v => ((some q, v), move d)
  | TM1.Stmt.write a q, v => ((some q, v), write (a s v))
  | TM1.Stmt.load a q, v => trAux s q (a s v)
  | TM1.Stmt.branch p q₁ q₂, v => cond (p s v) (trAux s q₁ v) (trAux s q₂ v)
  | TM1.Stmt.goto l, v => ((some (M (l s v)), v), write s)
  | TM1.Stmt.halt, v => ((none, v), write s)
#align turing.TM1to0.tr_aux Turing.TM1to0.trAux

local notation "Cfg₁₀" => TM0.Cfg Γ Λ'₁₀

/-- The translated TM0 machine (given the TM1 machine input). -/
def tr : TM0.Machine Γ Λ'₁₀
  | (none, _), _ => none
  | (some q, v), s => some (trAux M s q v)
#align turing.TM1to0.tr Turing.TM1to0.tr

/-- Translate configurations from TM1 to TM0. -/
def trCfg : Cfg₁ → Cfg₁₀
  | ⟨l, v, T⟩ => ⟨(l.map M, v), T⟩
#align turing.TM1to0.tr_cfg Turing.TM1to0.trCfg

theorem tr_respects :
    Respects (TM1.step M) (TM0.step (tr M)) fun (c₁ : Cfg₁) (c₂ : Cfg₁₀) ↦ trCfg M c₁ = c₂ :=
  fun_respects.2 fun ⟨l₁, v, T⟩ ↦ by
    cases' l₁ with l₁; · exact rfl
    -- ⊢ FRespects (TM0.step (tr M)) (fun c₁ => trCfg M c₁) (trCfg M { l := none, var …
                         -- 🎉 no goals
    simp only [trCfg, TM1.step, FRespects, Option.map]
    -- ⊢ Reaches₁ (TM0.step (tr M)) { q := (some (M l₁), v), Tape := T }
    induction' M l₁ with _ q IH _ q IH _ q IH generalizing v T
    case move d q IH => exact TransGen.head rfl (IH _ _)
    -- 🎉 no goals
    case write a q IH => exact TransGen.head rfl (IH _ _)
    -- 🎉 no goals
    case load a q IH => exact (reaches₁_eq (by rfl)).2 (IH _ _)
    -- 🎉 no goals
    case branch p q₁ q₂ IH₁ IH₂ =>
      unfold TM1.stepAux; cases e : p T.1 v
      · exact (reaches₁_eq (by simp only [TM0.step, tr, trAux, e]; rfl)).2 (IH₂ _ _)
      · exact (reaches₁_eq (by simp only [TM0.step, tr, trAux, e]; rfl)).2 (IH₁ _ _)
    iterate 2
      exact TransGen.single (congr_arg some (congr (congr_arg TM0.Cfg.mk rfl) (Tape.write_self T)))
#align turing.TM1to0.tr_respects Turing.TM1to0.tr_respects

theorem tr_eval (l : List Γ) : TM0.eval (tr M) l = TM1.eval M l :=
  (congr_arg _ (tr_eval' _ _ _ (tr_respects M) ⟨some _, _, _⟩)).trans
    (by
      rw [Part.map_eq_map, Part.map_map, TM1.eval]
      -- ⊢ Part.map ((fun c => Tape.right₀ c.Tape) ∘ fun a => trCfg M a) (eval (TM1.ste …
      congr with ⟨⟩)
      -- 🎉 no goals
#align turing.TM1to0.tr_eval Turing.TM1to0.tr_eval

variable [Fintype σ]

/-- Given a finite set of accessible `Λ` machine states, there is a finite set of accessible
machine states in the target (even though the type `Λ'` is infinite). -/
noncomputable def trStmts (S : Finset Λ) : Finset Λ'₁₀ :=
  (TM1.stmts M S) ×ˢ Finset.univ
#align turing.TM1to0.tr_stmts Turing.TM1to0.trStmts

open Classical

attribute [local simp] TM1.stmts₁_self

theorem tr_supports {S : Finset Λ} (ss : TM1.Supports M S) :
    TM0.Supports (tr M) ↑(trStmts M S) := by
  constructor
  -- ⊢ default ∈ ↑(trStmts M S)
  · apply Finset.mem_product.2
    -- ⊢ default.fst ∈ TM1.stmts M S ∧ default.snd ∈ Finset.univ
    constructor
    -- ⊢ default.fst ∈ TM1.stmts M S
    · simp only [default, TM1.stmts, Finset.mem_insertNone, Option.mem_def, Option.some_inj,
        forall_eq', Finset.mem_biUnion]
      exact ⟨_, ss.1, TM1.stmts₁_self⟩
      -- 🎉 no goals
    · apply Finset.mem_univ
      -- 🎉 no goals
  · intro q a q' s h₁ h₂
    -- ⊢ q' ∈ ↑(trStmts M S)
    rcases q with ⟨_ | q, v⟩; · cases h₁
    -- ⊢ q' ∈ ↑(trStmts M S)
                                -- 🎉 no goals
    cases' q' with q' v'
    -- ⊢ (q', v') ∈ ↑(trStmts M S)
    simp only [trStmts, Finset.mem_coe] at h₂ ⊢
    -- ⊢ (q', v') ∈ TM1.stmts M S ×ˢ Finset.univ
    rw [Finset.mem_product] at h₂ ⊢
    -- ⊢ (q', v').fst ∈ TM1.stmts M S ∧ (q', v').snd ∈ Finset.univ
    simp only [Finset.mem_univ, and_true_iff] at h₂ ⊢
    -- ⊢ q' ∈ TM1.stmts M S
    cases q'; · exact Multiset.mem_cons_self _ _
    -- ⊢ none ∈ TM1.stmts M S
                -- 🎉 no goals
    simp only [tr, Option.mem_def] at h₁
    -- ⊢ some val✝ ∈ TM1.stmts M S
    have := TM1.stmts_supportsStmt ss h₂
    -- ⊢ some val✝ ∈ TM1.stmts M S
    revert this; induction q generalizing v <;> intro hs
    -- ⊢ TM1.SupportsStmt S q → some val✝ ∈ TM1.stmts M S
                                                -- ⊢ some val✝ ∈ TM1.stmts M S
                                                -- ⊢ some val✝ ∈ TM1.stmts M S
                                                -- ⊢ some val✝ ∈ TM1.stmts M S
                                                -- ⊢ some val✝ ∈ TM1.stmts M S
                                                -- ⊢ some val✝ ∈ TM1.stmts M S
                                                -- ⊢ some val✝ ∈ TM1.stmts M S
    case move d q =>
      cases h₁; refine' TM1.stmts_trans _ h₂
      unfold TM1.stmts₁
      exact Finset.mem_insert_of_mem TM1.stmts₁_self
    case write b q =>
      cases h₁; refine' TM1.stmts_trans _ h₂
      unfold TM1.stmts₁
      exact Finset.mem_insert_of_mem TM1.stmts₁_self
    case load b q IH =>
      refine' IH _ (TM1.stmts_trans _ h₂) h₁ hs
      unfold TM1.stmts₁
      exact Finset.mem_insert_of_mem TM1.stmts₁_self
    case branch p q₁ q₂ IH₁ IH₂ =>
      cases h : p a v <;> rw [trAux, h] at h₁
      · refine' IH₂ _ (TM1.stmts_trans _ h₂) h₁ hs.2
        unfold TM1.stmts₁
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ TM1.stmts₁_self)
      · refine' IH₁ _ (TM1.stmts_trans _ h₂) h₁ hs.1
        unfold TM1.stmts₁
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ TM1.stmts₁_self)
    case goto l =>
      cases h₁
      exact Finset.some_mem_insertNone.2 (Finset.mem_biUnion.2 ⟨_, hs _ _, TM1.stmts₁_self⟩)
    case halt => cases h₁
    -- 🎉 no goals
    -- 🎉 no goals
#align turing.TM1to0.tr_supports Turing.TM1to0.tr_supports

end

end TM1to0

/-!
## TM1(Γ) emulator in TM1(Bool)

The most parsimonious Turing machine model that is still Turing complete is `TM0` with `Γ = Bool`.
Because our construction in the previous section reducing `TM1` to `TM0` doesn't change the
alphabet, we can do the alphabet reduction on `TM1` instead of `TM0` directly.

The basic idea is to use a bijection between `Γ` and a subset of `Vector Bool n`, where `n` is a
fixed constant. Each tape element is represented as a block of `n` bools. Whenever the machine
wants to read a symbol from the tape, it traverses over the block, performing `n` `branch`
instructions to each any of the `2^n` results.

For the `write` instruction, we have to use a `goto` because we need to follow a different code
path depending on the local state, which is not available in the TM1 model, so instead we jump to
a label computed using the read value and the local state, which performs the writing and returns
to normal execution.

Emulation overhead is `O(1)`. If not for the above `write` behavior it would be 1-1 because we are
exploiting the 0-step behavior of regular commands to avoid taking steps, but there are
nevertheless a bounded number of `write` calls between `goto` statements because TM1 statements are
finitely long.
-/


namespace TM1to1

-- "TM1to1"
set_option linter.uppercaseLean3 false

open TM1

section

variable {Γ : Type*} [Inhabited Γ]

theorem exists_enc_dec [Fintype Γ] : ∃ (n : ℕ) (enc : Γ → Vector Bool n) (dec : Vector Bool n → Γ),
    enc default = Vector.replicate n false ∧ ∀ a, dec (enc a) = a := by
  letI := Classical.decEq Γ
  -- ⊢ ∃ n enc dec, enc default = Vector.replicate n false ∧ ∀ (a : Γ), dec (enc a) …
  let n := Fintype.card Γ
  -- ⊢ ∃ n enc dec, enc default = Vector.replicate n false ∧ ∀ (a : Γ), dec (enc a) …
  obtain ⟨F⟩ := Fintype.truncEquivFin Γ
  -- ⊢ ∃ n enc dec, enc default = Vector.replicate n false ∧ ∀ (a : Γ), dec (enc a) …
  let G : Fin n ↪ Fin n → Bool :=
    ⟨fun a b ↦ a = b, fun a b h ↦
      Bool.of_decide_true <| (congr_fun h b).trans <| Bool.decide_true rfl⟩
  let H := (F.toEmbedding.trans G).trans (Equiv.vectorEquivFin _ _).symm.toEmbedding
  -- ⊢ ∃ n enc dec, enc default = Vector.replicate n false ∧ ∀ (a : Γ), dec (enc a) …
  classical
    let enc := H.setValue default (Vector.replicate n false)
    exact ⟨_, enc, Function.invFun enc, H.setValue_eq _ _, Function.leftInverse_invFun enc.2⟩
#align turing.TM1to1.exists_enc_dec Turing.TM1to1.exists_enc_dec

variable {Λ : Type*} [Inhabited Λ]

variable {σ : Type*} [Inhabited σ]

local notation "Stmt₁" => Stmt Γ Λ σ

local notation "Cfg₁" => Cfg Γ Λ σ

/-- The configuration state of the TM. -/
inductive Λ'
  | normal : Λ → Λ'
  | write : Γ → Stmt₁ → Λ'
#align turing.TM1to1.Λ' Turing.TM1to1.Λ'

local notation "Λ'₁" => @Λ' Γ Λ σ  -- Porting note: Added this to clean up types.

instance : Inhabited Λ'₁ :=
  ⟨Λ'.normal default⟩

local notation "Stmt'₁" => Stmt Bool Λ'₁ σ

local notation "Cfg'₁" => Cfg Bool Λ'₁ σ

/-- Read a vector of length `n` from the tape. -/
def readAux : ∀ n, (Vector Bool n → Stmt'₁) → Stmt'₁
  | 0, f => f Vector.nil
  | i + 1, f =>
    Stmt.branch (fun a _ ↦ a) (Stmt.move Dir.right <| readAux i fun v ↦ f (true ::ᵥ v))
      (Stmt.move Dir.right <| readAux i fun v ↦ f (false ::ᵥ v))
#align turing.TM1to1.read_aux Turing.TM1to1.readAux

variable {n : ℕ} (enc : Γ → Vector Bool n) (dec : Vector Bool n → Γ)

/-- A move left or right corresponds to `n` moves across the super-cell. -/
def move (d : Dir) (q : Stmt'₁) : Stmt'₁ :=
  (Stmt.move d)^[n] q
#align turing.TM1to1.move Turing.TM1to1.move

local notation "moveₙ" => @move Γ Λ σ n  -- Porting note: Added this to clean up types.

/-- To read a symbol from the tape, we use `readAux` to traverse the symbol,
then return to the original position with `n` moves to the left. -/
def read (f : Γ → Stmt'₁) : Stmt'₁ :=
  readAux n fun v ↦ moveₙ Dir.left <| f (dec v)
#align turing.TM1to1.read Turing.TM1to1.read

/-- Write a list of bools on the tape. -/
def write : List Bool → Stmt'₁ → Stmt'₁
  | [], q => q
  | a :: l, q => (Stmt.write fun _ _ ↦ a) <| Stmt.move Dir.right <| write l q
#align turing.TM1to1.write Turing.TM1to1.write

/-- Translate a normal instruction. For the `write` command, we use a `goto` indirection so that
we can access the current value of the tape. -/
def trNormal : Stmt₁ → Stmt'₁
  | Stmt.move d q => moveₙ d <| trNormal q
  | Stmt.write f q => read dec fun a ↦ Stmt.goto fun _ s ↦ Λ'.write (f a s) q
  | Stmt.load f q => read dec fun a ↦ (Stmt.load fun _ s ↦ f a s) <| trNormal q
  | Stmt.branch p q₁ q₂ =>
    read dec fun a ↦ Stmt.branch (fun _ s ↦ p a s) (trNormal q₁) (trNormal q₂)
  | Stmt.goto l => read dec fun a ↦ Stmt.goto fun _ s ↦ Λ'.normal (l a s)
  | Stmt.halt => Stmt.halt
#align turing.TM1to1.tr_normal Turing.TM1to1.trNormal

theorem stepAux_move (d : Dir) (q : Stmt'₁) (v : σ) (T : Tape Bool) :
    stepAux (moveₙ d q) v T = stepAux q v ((Tape.move d)^[n] T) := by
  suffices : ∀ i, stepAux ((Stmt.move d)^[i] q) v T = stepAux q v ((Tape.move d)^[i] T)
  -- ⊢ stepAux (move d q) v T = stepAux q v ((Tape.move d)^[n] T)
  exact this n
  -- ⊢ ∀ (i : ℕ), stepAux ((Stmt.move d)^[i] q) v T = stepAux q v ((Tape.move d)^[i …
  intro i; induction' i with i IH generalizing T; · rfl
  -- ⊢ stepAux ((Stmt.move d)^[i] q) v T = stepAux q v ((Tape.move d)^[i] T)
           -- ⊢ stepAux ((Stmt.move d)^[Nat.zero] q) v T = stepAux q v ((Tape.move d)^[Nat.z …
                                                    -- 🎉 no goals
  rw [iterate_succ', iterate_succ]
  -- ⊢ stepAux ((Stmt.move d ∘ (Stmt.move d)^[i]) q) v T = stepAux q v (((Tape.move …
  simp only [stepAux, Function.comp_apply]
  -- ⊢ stepAux ((Stmt.move d)^[i] q) v (Tape.move d T) = stepAux q v ((Tape.move d) …
  rw [IH]
  -- 🎉 no goals
#align turing.TM1to1.step_aux_move Turing.TM1to1.stepAux_move

theorem supportsStmt_move {S : Finset Λ'₁} {d : Dir} {q : Stmt'₁} :
    SupportsStmt S (moveₙ d q) = SupportsStmt S q := by
  suffices ∀ {i}, SupportsStmt S ((Stmt.move d)^[i] q) = _ from this
  -- ⊢ ∀ {i : ℕ}, SupportsStmt S ((Stmt.move d)^[i] q) = SupportsStmt S q
  intro i; induction i generalizing q <;> simp only [*, iterate]; rfl
  -- ⊢ SupportsStmt S ((Stmt.move d)^[i] q) = SupportsStmt S q
           -- ⊢ SupportsStmt S ((Stmt.move d)^[Nat.zero] q) = SupportsStmt S q
                                          -- 🎉 no goals
                                          -- ⊢ SupportsStmt S (Stmt.move d q) = SupportsStmt S q
                                                                  -- 🎉 no goals
#align turing.TM1to1.supports_stmt_move Turing.TM1to1.supportsStmt_move

theorem supportsStmt_write {S : Finset Λ'₁} {l : List Bool} {q : Stmt'₁} :
    SupportsStmt S (write l q) = SupportsStmt S q := by
  induction' l with _ l IH <;> simp only [write, SupportsStmt, *]
  -- ⊢ SupportsStmt S (write [] q) = SupportsStmt S q
                               -- 🎉 no goals
                               -- 🎉 no goals
#align turing.TM1to1.supports_stmt_write Turing.TM1to1.supportsStmt_write

theorem supportsStmt_read {S : Finset Λ'₁} :
    ∀ {f : Γ → Stmt'₁}, (∀ a, SupportsStmt S (f a)) → SupportsStmt S (read dec f) :=
  suffices
    ∀ (i) (f : Vector Bool i → Stmt'₁), (∀ v, SupportsStmt S (f v)) → SupportsStmt S (readAux i f)
    from fun hf ↦ this n _ (by intro; simp only [supportsStmt_move, hf])
                               -- ⊢ SupportsStmt S (move Dir.left (f✝ (dec v✝)))
                                      -- 🎉 no goals
  -- ⊢ SupportsStmt S (readAux Nat.zero f)
                            -- 🎉 no goals
  fun i f hf ↦ by
  -- ⊢ SupportsStmt S (Stmt.move Dir.right (readAux i fun v => f (true ::ᵥ v)))
                  -- ⊢ ∀ (v : Vector Bool i), SupportsStmt S (f (true ::ᵥ v))
                  -- ⊢ ∀ (v : Vector Bool i), SupportsStmt S (f (false ::ᵥ v))
                               -- ⊢ SupportsStmt S (f (true ::ᵥ v✝))
                               -- ⊢ SupportsStmt S (f (false ::ᵥ v✝))
                                         -- 🎉 no goals
                                         -- 🎉 no goals
  induction' i with i IH; · exact hf _
  constructor <;> apply IH <;> intro <;> apply hf
#align turing.TM1to1.supports_stmt_read Turing.TM1to1.supportsStmt_read

variable (enc0 : enc default = Vector.replicate n false)

section

variable {enc}

/-- The low level tape corresponding to the given tape over alphabet `Γ`. -/
def trTape' (L R : ListBlank Γ) : Tape Bool := by
  refine'
      Tape.mk' (L.bind (fun x ↦ (enc x).toList.reverse) ⟨n, _⟩)
        (R.bind (fun x ↦ (enc x).toList) ⟨n, _⟩) <;>
    simp only [enc0, Vector.replicate, List.reverse_replicate, Bool.default_bool, Vector.toList_mk]
    -- 🎉 no goals
    -- 🎉 no goals
#align turing.TM1to1.tr_tape' Turing.TM1to1.trTape'

/-- The low level tape corresponding to the given tape over alphabet `Γ`. -/
def trTape (T : Tape Γ) : Tape Bool :=
  trTape' enc0 T.left T.right₀
#align turing.TM1to1.tr_tape Turing.TM1to1.trTape

theorem trTape_mk' (L R : ListBlank Γ) : trTape enc0 (Tape.mk' L R) = trTape' enc0 L R := by
  simp only [trTape, Tape.mk'_left, Tape.mk'_right₀]
  -- 🎉 no goals
#align turing.TM1to1.tr_tape_mk' Turing.TM1to1.trTape_mk'

end

variable (M : Λ → TM1.Stmt Γ Λ σ)  -- Porting note: Unfolded `Stmt₁`.

/-- The top level program. -/
def tr : Λ'₁ → Stmt'₁
  | Λ'.normal l => trNormal dec (M l)
  | Λ'.write a q => write (enc a).toList <| moveₙ Dir.left <| trNormal dec q
#align turing.TM1to1.tr Turing.TM1to1.tr

/-- The machine configuration translation. -/
def trCfg : Cfg₁ → Cfg'₁
  | ⟨l, v, T⟩ => ⟨l.map Λ'.normal, v, trTape enc0 T⟩
#align turing.TM1to1.tr_cfg Turing.TM1to1.trCfg

variable {enc}

theorem trTape'_move_left (L R : ListBlank Γ) :
    (Tape.move Dir.left)^[n] (trTape' enc0 L R) = trTape' enc0 L.tail (R.cons L.head) := by
  obtain ⟨a, L, rfl⟩ := L.exists_cons
  -- ⊢ (Tape.move Dir.left)^[n] (trTape' enc0 (ListBlank.cons a L) R) = trTape' enc …
  simp only [trTape', ListBlank.cons_bind, ListBlank.head_cons, ListBlank.tail_cons]
  -- ⊢ (Tape.move Dir.left)^[n] (Tape.mk' (ListBlank.append (List.reverse (Vector.t …
  suffices ∀ {L' R' l₁ l₂} (_ : Vector.toList (enc a) = List.reverseAux l₁ l₂),
      (Tape.move Dir.left)^[l₁.length]
      (Tape.mk' (ListBlank.append l₁ L') (ListBlank.append l₂ R')) =
      Tape.mk' L' (ListBlank.append (Vector.toList (enc a)) R') by
    simpa only [List.length_reverse, Vector.toList_length] using this (List.reverse_reverse _).symm
  intro _ _ l₁ l₂ e
  -- ⊢ (Tape.move Dir.left)^[List.length l₁] (Tape.mk' (ListBlank.append l₁ L'✝) (L …
  induction' l₁ with b l₁ IH generalizing l₂
  -- ⊢ (Tape.move Dir.left)^[List.length []] (Tape.mk' (ListBlank.append [] L'✝) (L …
  · cases e
    -- ⊢ (Tape.move Dir.left)^[List.length []] (Tape.mk' (ListBlank.append [] L'✝) (L …
    rfl
    -- 🎉 no goals
  simp only [List.length, List.cons_append, iterate_succ_apply]
  -- ⊢ (Tape.move Dir.left)^[List.length l₁] (Tape.move Dir.left (Tape.mk' (ListBla …
  convert IH e
  -- ⊢ Tape.move Dir.left (Tape.mk' (ListBlank.append (b :: l₁) L'✝) (ListBlank.app …
  simp only [ListBlank.tail_cons, ListBlank.append, Tape.move_left_mk', ListBlank.head_cons]
  -- 🎉 no goals
#align turing.TM1to1.tr_tape'_move_left Turing.TM1to1.trTape'_move_left

theorem trTape'_move_right (L R : ListBlank Γ) :
    (Tape.move Dir.right)^[n] (trTape' enc0 L R) = trTape' enc0 (L.cons R.head) R.tail := by
  suffices ∀ i L, (Tape.move Dir.right)^[i] ((Tape.move Dir.left)^[i] L) = L by
    refine' (Eq.symm _).trans (this n _)
    simp only [trTape'_move_left, ListBlank.cons_head_tail, ListBlank.head_cons,
      ListBlank.tail_cons]
  intro i _
  -- ⊢ (Tape.move Dir.right)^[i] ((Tape.move Dir.left)^[i] L✝) = L✝
  induction' i with i IH
  -- ⊢ (Tape.move Dir.right)^[Nat.zero] ((Tape.move Dir.left)^[Nat.zero] L✝) = L✝
  · rfl
    -- 🎉 no goals
  rw [iterate_succ_apply, iterate_succ_apply', Tape.move_left_right, IH]
  -- 🎉 no goals
#align turing.TM1to1.tr_tape'_move_right Turing.TM1to1.trTape'_move_right

theorem stepAux_write (q : Stmt'₁) (v : σ) (a b : Γ) (L R : ListBlank Γ) :
    stepAux (write (enc a).toList q) v (trTape' enc0 L (ListBlank.cons b R)) =
      stepAux q v (trTape' enc0 (ListBlank.cons a L) R) := by
  simp only [trTape', ListBlank.cons_bind]
  -- ⊢ stepAux (write (Vector.toList (enc a)) q) v (Tape.mk' (ListBlank.bind L (fun …
  suffices ∀ {L' R'} (l₁ l₂ l₂' : List Bool) (_ : l₂'.length = l₂.length),
      stepAux (write l₂ q) v (Tape.mk' (ListBlank.append l₁ L') (ListBlank.append l₂' R')) =
      stepAux q v (Tape.mk' (L'.append (List.reverseAux l₂ l₁)) R') by
    refine' this [] _ _ ((enc b).2.trans (enc a).2.symm)
  clear a b L R
  -- ⊢ ∀ {L' R' : ListBlank Bool} (l₁ l₂ l₂' : List Bool), List.length l₂' = List.l …
  intro L' R' l₁ l₂ l₂' e
  -- ⊢ stepAux (write l₂ q) v (Tape.mk' (ListBlank.append l₁ L') (ListBlank.append  …
  induction' l₂ with a l₂ IH generalizing l₁ l₂'
  -- ⊢ stepAux (write [] q) v (Tape.mk' (ListBlank.append l₁ L') (ListBlank.append  …
  · cases List.length_eq_zero.1 e
    -- ⊢ stepAux (write [] q) v (Tape.mk' (ListBlank.append l₁ L') (ListBlank.append  …
    rfl
    -- 🎉 no goals
  cases' l₂' with b l₂' <;> simp only [List.length_nil, List.length_cons, Nat.succ_inj'] at e
  -- ⊢ stepAux (write (a :: l₂) q) v (Tape.mk' (ListBlank.append l₁ L') (ListBlank. …
                            -- 🎉 no goals
                            -- ⊢ stepAux (write (a :: l₂) q) v (Tape.mk' (ListBlank.append l₁ L') (ListBlank. …
  rw [List.reverseAux, ← IH (a :: l₁) l₂' e]
  -- ⊢ stepAux (write (a :: l₂) q) v (Tape.mk' (ListBlank.append l₁ L') (ListBlank. …
  simp only [stepAux, ListBlank.append, Tape.write_mk', Tape.move_right_mk', ListBlank.head_cons,
    ListBlank.tail_cons]
#align turing.TM1to1.step_aux_write Turing.TM1to1.stepAux_write

variable (encdec : ∀ a, dec (enc a) = a)

theorem stepAux_read (f : Γ → Stmt'₁) (v : σ) (L R : ListBlank Γ) :
    stepAux (read dec f) v (trTape' enc0 L R) = stepAux (f R.head) v (trTape' enc0 L R) := by
  suffices ∀ f, stepAux (readAux n f) v (trTape' enc0 L R) =
      stepAux (f (enc R.head)) v (trTape' enc0 (L.cons R.head) R.tail) by
    rw [read, this, stepAux_move, encdec, trTape'_move_left enc0]
    simp only [ListBlank.head_cons, ListBlank.cons_head_tail, ListBlank.tail_cons]
  obtain ⟨a, R, rfl⟩ := R.exists_cons
  -- ⊢ ∀ (f : Vector Bool n → Stmt Bool Λ' σ), stepAux (readAux n f) v (trTape' enc …
  simp only [ListBlank.head_cons, ListBlank.tail_cons, trTape', ListBlank.cons_bind,
    ListBlank.append_assoc]
  suffices ∀ i f L' R' l₁ l₂ h,
      stepAux (readAux i f) v (Tape.mk' (ListBlank.append l₁ L') (ListBlank.append l₂ R')) =
      stepAux (f ⟨l₂, h⟩) v (Tape.mk' (ListBlank.append (l₂.reverseAux l₁) L') R') by
    intro f
    -- Porting note: Here was `change`.
    exact this n f (L.bind (fun x => (enc x).1.reverse) _)
      (R.bind (fun x => (enc x).1) _) [] _ (enc a).2
  clear f L a R
  -- ⊢ ∀ (i : ℕ) (f : Vector Bool i → Stmt Bool Λ' σ) (L' R' : ListBlank Bool) (l₁  …
  intro i f L' R' l₁ l₂ _
  -- ⊢ stepAux (readAux i f) v (Tape.mk' (ListBlank.append l₁ L') (ListBlank.append …
  subst i
  -- ⊢ stepAux (readAux (List.length l₂) f) v (Tape.mk' (ListBlank.append l₁ L') (L …
  induction' l₂ with a l₂ IH generalizing l₁
  -- ⊢ stepAux (readAux (List.length []) f) v (Tape.mk' (ListBlank.append l₁ L') (L …
  · rfl
    -- 🎉 no goals
  trans
    stepAux (readAux l₂.length fun v ↦ f (a ::ᵥ v)) v
      (Tape.mk' ((L'.append l₁).cons a) (R'.append l₂))
  · dsimp [readAux, stepAux]
    -- ⊢ (bif ListBlank.head (ListBlank.cons a (ListBlank.append l₂ R')) then stepAux …
    simp
    -- ⊢ (bif a then stepAux (readAux (List.length l₂) fun v => f (true ::ᵥ v)) v (Ta …
    cases a <;> rfl
    -- ⊢ (bif false then stepAux (readAux (List.length l₂) fun v => f (true ::ᵥ v)) v …
                -- 🎉 no goals
                -- 🎉 no goals
  rw [← ListBlank.append, IH]
  -- ⊢ stepAux (f (a ::ᵥ { val := l₂, property := (_ : List.length l₂ = List.length …
  rfl
  -- 🎉 no goals
#align turing.TM1to1.step_aux_read Turing.TM1to1.stepAux_read

theorem tr_respects {enc₀} :
    Respects (step M) (step (tr enc dec M)) fun c₁ c₂ ↦ trCfg enc enc₀ c₁ = c₂ :=
  fun_respects.2 fun ⟨l₁, v, T⟩ ↦ by
    obtain ⟨L, R, rfl⟩ := T.exists_mk'
    -- ⊢ FRespects (step (tr enc dec M)) (fun c₁ => trCfg enc enc₀ c₁) (trCfg enc enc …
    cases' l₁ with l₁
    -- ⊢ FRespects (step (tr enc dec M)) (fun c₁ => trCfg enc enc₀ c₁) (trCfg enc enc …
    · exact rfl
      -- 🎉 no goals
    suffices ∀ q R, Reaches (step (tr enc dec M)) (stepAux (trNormal dec q) v (trTape' enc0 L R))
        (trCfg enc enc0 (stepAux q v (Tape.mk' L R))) by
      refine' TransGen.head' rfl _
      rw [trTape_mk']
      exact this _ R
    clear R l₁
    -- ⊢ ∀ (q : Stmt₁) (R : ListBlank Γ), Reaches (step (tr enc dec M)) (stepAux (trN …
    intro q R
    -- ⊢ Reaches (step (tr enc dec M)) (stepAux (trNormal dec q) v (trTape' enc0 L R) …
    induction' q generalizing v L R
    case move d q IH =>
      cases d <;>
          simp only [trNormal, iterate, stepAux_move, stepAux, ListBlank.head_cons,
            Tape.move_left_mk', ListBlank.cons_head_tail, ListBlank.tail_cons,
            trTape'_move_left enc0, trTape'_move_right enc0] <;>
        apply IH
    case write f q IH =>
      simp only [trNormal, stepAux_read dec enc0 encdec, stepAux]
      refine' ReflTransGen.head rfl _
      obtain ⟨a, R, rfl⟩ := R.exists_cons
      rw [tr, Tape.mk'_head, stepAux_write, ListBlank.head_cons, stepAux_move,
        trTape'_move_left enc0, ListBlank.head_cons, ListBlank.tail_cons, Tape.write_mk']
      apply IH
    case load a q IH =>
      simp only [trNormal, stepAux_read dec enc0 encdec]
      apply IH
    case branch p q₁ q₂ IH₁ IH₂ =>
      simp only [trNormal, stepAux_read dec enc0 encdec, stepAux]
      cases p R.head v <;> [apply IH₂; apply IH₁]
    case goto l =>
      simp only [trNormal, stepAux_read dec enc0 encdec, stepAux, trCfg, trTape_mk']
      apply ReflTransGen.refl
    case halt =>
      simp only [trNormal, stepAux, trCfg, stepAux_move, trTape'_move_left enc0,
        trTape'_move_right enc0, trTape_mk']
      apply ReflTransGen.refl
#align turing.TM1to1.tr_respects Turing.TM1to1.tr_respects

open Classical

variable [Fintype Γ]

/-- The set of accessible `Λ'.write` machine states. -/
noncomputable def writes : Stmt₁ → Finset Λ'₁
  | Stmt.move _ q => writes q
  | Stmt.write _ q => (Finset.univ.image fun a ↦ Λ'.write a q) ∪ writes q
  | Stmt.load _ q => writes q
  | Stmt.branch _ q₁ q₂ => writes q₁ ∪ writes q₂
  | Stmt.goto _ => ∅
  | Stmt.halt => ∅
#align turing.TM1to1.writes Turing.TM1to1.writes

/-- The set of accessible machine states, assuming that the input machine is supported on `S`,
are the normal states embedded from `S`, plus all write states accessible from these states. -/
noncomputable def trSupp (S : Finset Λ) : Finset Λ'₁ :=
  S.biUnion fun l ↦ insert (Λ'.normal l) (writes (M l))
#align turing.TM1to1.tr_supp Turing.TM1to1.trSupp

theorem tr_supports {S : Finset Λ} (ss : Supports M S) : Supports (tr enc dec M) (trSupp M S) :=
  ⟨Finset.mem_biUnion.2 ⟨_, ss.1, Finset.mem_insert_self _ _⟩, fun q h ↦ by
    suffices ∀ q, SupportsStmt S q → (∀ q' ∈ writes q, q' ∈ trSupp M S) →
        SupportsStmt (trSupp M S) (trNormal dec q) ∧
        ∀ q' ∈ writes q, SupportsStmt (trSupp M S) (tr enc dec M q') by
      rcases Finset.mem_biUnion.1 h with ⟨l, hl, h⟩
      have :=
        this _ (ss.2 _ hl) fun q' hq ↦ Finset.mem_biUnion.2 ⟨_, hl, Finset.mem_insert_of_mem hq⟩
      rcases Finset.mem_insert.1 h with (rfl | h)
      exacts [this.1, this.2 _ h]
    intro q hs hw
    -- ⊢ SupportsStmt (trSupp M S) (trNormal dec q) ∧ ∀ (q' : Λ'), q' ∈ writes q → Su …
    induction q
    case move d q IH =>
      unfold writes at hw ⊢
      replace IH := IH hs hw; refine' ⟨_, IH.2⟩
      cases d <;> simp only [trNormal, iterate, supportsStmt_move, IH]
    case write f q IH =>
      unfold writes at hw ⊢
      simp only [Finset.mem_image, Finset.mem_union, Finset.mem_univ, exists_prop, true_and_iff]
        at hw ⊢
      replace IH := IH hs fun q hq ↦ hw q (Or.inr hq)
      refine' ⟨supportsStmt_read _ fun a _ s ↦ hw _ (Or.inl ⟨_, rfl⟩), fun q' hq ↦ _⟩
      rcases hq with (⟨a, q₂, rfl⟩ | hq)
      · simp only [tr, supportsStmt_write, supportsStmt_move, IH.1]
      · exact IH.2 _ hq
    case load a q IH =>
      unfold writes at hw ⊢
      replace IH := IH hs hw
      refine' ⟨supportsStmt_read _ fun _ ↦ IH.1, IH.2⟩
    case branch p q₁ q₂ IH₁ IH₂ =>
      unfold writes at hw ⊢
      simp only [Finset.mem_union] at hw ⊢
      replace IH₁ := IH₁ hs.1 fun q hq ↦ hw q (Or.inl hq)
      replace IH₂ := IH₂ hs.2 fun q hq ↦ hw q (Or.inr hq)
      exact ⟨supportsStmt_read _ fun _ ↦ ⟨IH₁.1, IH₂.1⟩, fun q ↦ Or.rec (IH₁.2 _) (IH₂.2 _)⟩
    case goto l =>
      simp only [writes, Finset.not_mem_empty]; refine' ⟨_, fun _ ↦ False.elim⟩
      refine' supportsStmt_read _ fun a _ s ↦ _
      exact Finset.mem_biUnion.2 ⟨_, hs _ _, Finset.mem_insert_self _ _⟩
    case halt =>
      simp only [writes, Finset.not_mem_empty]; refine' ⟨_, fun _ ↦ False.elim⟩
      simp only [SupportsStmt, supportsStmt_move, trNormal]⟩
#align turing.TM1to1.tr_supports Turing.TM1to1.tr_supports

end

end TM1to1

/-!
## TM0 emulator in TM1

To establish that TM0 and TM1 are equivalent computational models, we must also have a TM0 emulator
in TM1. The main complication here is that TM0 allows an action to depend on the value at the head
and local state, while TM1 doesn't (in order to have more programming language-like semantics).
So we use a computed `goto` to go to a state that performs the desired action and then returns to
normal execution.

One issue with this is that the `halt` instruction is supposed to halt immediately, not take a step
to a halting state. To resolve this we do a check for `halt` first, then `goto` (with an
unreachable branch).
-/


namespace TM0to1

-- "TM0to1"
set_option linter.uppercaseLean3 false

section

variable {Γ : Type*} [Inhabited Γ]

variable {Λ : Type*} [Inhabited Λ]

/-- The machine states for a TM1 emulating a TM0 machine. States of the TM0 machine are embedded
as `normal q` states, but the actual operation is split into two parts, a jump to `act s q`
followed by the action and a jump to the next `normal` state. -/
inductive Λ'
  | normal : Λ → Λ'
  | act : TM0.Stmt Γ → Λ → Λ'
#align turing.TM0to1.Λ' Turing.TM0to1.Λ'

local notation "Λ'₁" => @Λ' Γ Λ  -- Porting note: Added this to clean up types.

instance : Inhabited Λ'₁ :=
  ⟨Λ'.normal default⟩

local notation "Cfg₀" => TM0.Cfg Γ Λ

local notation "Stmt₁" => TM1.Stmt Γ Λ'₁ Unit

local notation "Cfg₁" => TM1.Cfg Γ Λ'₁ Unit

variable (M : TM0.Machine Γ Λ)

open TM1.Stmt

/-- The program. -/
def tr : Λ'₁ → Stmt₁
  | Λ'.normal q =>
    branch (fun a _ ↦ (M q a).isNone) halt <|
      goto fun a _ ↦ match M q a with
      | none => default -- unreachable
      | some (q', s) => Λ'.act s q'
  | Λ'.act (TM0.Stmt.move d) q => move d <| goto fun _ _ ↦ Λ'.normal q
  | Λ'.act (TM0.Stmt.write a) q => (write fun _ _ ↦ a) <| goto fun _ _ ↦ Λ'.normal q
#align turing.TM0to1.tr Turing.TM0to1.tr

/-- The configuration translation. -/
def trCfg : Cfg₀ → Cfg₁
  | ⟨q, T⟩ => ⟨cond (M q T.1).isSome (some (Λ'.normal q)) none, (), T⟩
#align turing.TM0to1.tr_cfg Turing.TM0to1.trCfg

theorem tr_respects : Respects (TM0.step M) (TM1.step (tr M)) fun a b ↦ trCfg M a = b :=
  fun_respects.2 fun ⟨q, T⟩ ↦ by
    cases' e : M q T.1 with val
    -- ⊢ FRespects (TM1.step (tr M)) (fun a => trCfg M a) (trCfg M { q := q, Tape :=  …
    · simp only [TM0.step, trCfg, e]; exact Eq.refl none
      -- ⊢ FRespects (TM1.step (tr M)) (fun a => { l := bif Option.isSome (M a.q a.Tape …
                                      -- 🎉 no goals
    cases' val with q' s
    -- ⊢ FRespects (TM1.step (tr M)) (fun a => trCfg M a) (trCfg M { q := q, Tape :=  …
    simp only [FRespects, TM0.step, trCfg, e, Option.isSome, cond, Option.map_some']
    -- ⊢ Reaches₁ (TM1.step (tr M)) { l := some (Λ'.normal q), var := (), Tape := T }
    revert e  -- Porting note: Added this so that `e` doesn't get into the `match`.
    -- ⊢ M q T.head = some (q', s) →
    have : TM1.step (tr M) ⟨some (Λ'.act s q'), (), T⟩ = some ⟨some (Λ'.normal q'), (), match s with
        | TM0.Stmt.move d => T.move d
        | TM0.Stmt.write a => T.write a⟩ := by
      cases' s with d a <;> rfl
    intro e
    -- ⊢ Reaches₁ (TM1.step (tr M)) { l := some (Λ'.normal q), var := (), Tape := T }
    refine' TransGen.head _ (TransGen.head' this _)
    · simp only [TM1.step, TM1.stepAux]
      -- ⊢ { l := some (Λ'.act s q'), var := (), Tape := T } ∈
      rw [e]
      -- ⊢ { l := some (Λ'.act s q'), var := (), Tape := T } ∈
      rfl
      -- 🎉 no goals
    cases e' : M q' _
    · apply ReflTransGen.single
      -- ⊢ {
      simp only [TM1.step, TM1.stepAux]
      -- ⊢ { l := none, var := (),
      rw [e']
      -- ⊢ { l := none, var := (),
      rfl
      -- 🎉 no goals
    · rfl
      -- 🎉 no goals
#align turing.TM0to1.tr_respects Turing.TM0to1.tr_respects

end

end TM0to1

/-!
## The TM2 model

The TM2 model removes the tape entirely from the TM1 model, replacing it with an arbitrary (finite)
collection of stacks, each with elements of different types (the alphabet of stack `k : K` is
`Γ k`). The statements are:

* `push k (f : σ → Γ k) q` puts `f a` on the `k`-th stack, then does `q`.
* `pop k (f : σ → Option (Γ k) → σ) q` changes the state to `f a (S k).head`, where `S k` is the
  value of the `k`-th stack, and removes this element from the stack, then does `q`.
* `peek k (f : σ → Option (Γ k) → σ) q` changes the state to `f a (S k).head`, where `S k` is the
  value of the `k`-th stack, then does `q`.
* `load (f : σ → σ) q` reads nothing but applies `f` to the internal state, then does `q`.
* `branch (f : σ → Bool) qtrue qfalse` does `qtrue` or `qfalse` according to `f a`.
* `goto (f : σ → Λ)` jumps to label `f a`.
* `halt` halts on the next step.

The configuration is a tuple `(l, var, stk)` where `l : Option Λ` is the current label to run or
`none` for the halting state, `var : σ` is the (finite) internal state, and `stk : ∀ k, List (Γ k)`
is the collection of stacks. (Note that unlike the `TM0` and `TM1` models, these are not
`ListBlank`s, they have definite ends that can be detected by the `pop` command.)

Given a designated stack `k` and a value `L : List (Γ k)`, the initial configuration has all the
stacks empty except the designated "input" stack; in `eval` this designated stack also functions
as the output stack.
-/


namespace TM2

-- "TM2"
set_option linter.uppercaseLean3 false

section

variable {K : Type*} [DecidableEq K]

-- Index type of stacks
variable (Γ : K → Type*)

-- Type of stack elements
variable (Λ : Type*)

-- Type of function labels
variable (σ : Type*)

-- Type of variable settings
/-- The TM2 model removes the tape entirely from the TM1 model,
  replacing it with an arbitrary (finite) collection of stacks.
  The operation `push` puts an element on one of the stacks,
  and `pop` removes an element from a stack (and modifying the
  internal state based on the result). `peek` modifies the
  internal state but does not remove an element. -/
inductive Stmt
  | push : ∀ k, (σ → Γ k) → Stmt → Stmt
  | peek : ∀ k, (σ → Option (Γ k) → σ) → Stmt → Stmt
  | pop : ∀ k, (σ → Option (Γ k) → σ) → Stmt → Stmt
  | load : (σ → σ) → Stmt → Stmt
  | branch : (σ → Bool) → Stmt → Stmt → Stmt
  | goto : (σ → Λ) → Stmt
  | halt : Stmt
#align turing.TM2.stmt Turing.TM2.Stmt

local notation "Stmt₂" => Stmt Γ Λ σ  -- Porting note: Added this to clean up types.

open Stmt

instance Stmt.inhabited : Inhabited Stmt₂ :=
  ⟨halt⟩
#align turing.TM2.stmt.inhabited Turing.TM2.Stmt.inhabited

/-- A configuration in the TM2 model is a label (or `none` for the halt state), the state of
local variables, and the stacks. (Note that the stacks are not `ListBlank`s, they have a definite
size.) -/
structure Cfg where
  l : Option Λ
  var : σ
  stk : ∀ k, List (Γ k)
#align turing.TM2.cfg Turing.TM2.Cfg

local notation "Cfg₂" => Cfg Γ Λ σ  -- Porting note: Added this to clean up types.

instance Cfg.inhabited [Inhabited σ] : Inhabited Cfg₂ :=
  ⟨⟨default, default, default⟩⟩
#align turing.TM2.cfg.inhabited Turing.TM2.Cfg.inhabited

variable {Γ Λ σ}

/-- The step function for the TM2 model. -/
@[simp]
def stepAux : Stmt₂ → σ → (∀ k, List (Γ k)) → Cfg₂
  | push k f q, v, S => stepAux q v (update S k (f v :: S k))
  | peek k f q, v, S => stepAux q (f v (S k).head?) S
  | pop k f q, v, S => stepAux q (f v (S k).head?) (update S k (S k).tail)
  | load a q, v, S => stepAux q (a v) S
  | branch f q₁ q₂, v, S => cond (f v) (stepAux q₁ v S) (stepAux q₂ v S)
  | goto f, v, S => ⟨some (f v), v, S⟩
  | halt, v, S => ⟨none, v, S⟩
#align turing.TM2.step_aux Turing.TM2.stepAux

/-- The step function for the TM2 model. -/
@[simp]
def step (M : Λ → Stmt₂) : Cfg₂ → Option Cfg₂
  | ⟨none, _, _⟩ => none
  | ⟨some l, v, S⟩ => some (stepAux (M l) v S)
#align turing.TM2.step Turing.TM2.step

/-- The (reflexive) reachability relation for the TM2 model. -/
def Reaches (M : Λ → Stmt₂) : Cfg₂ → Cfg₂ → Prop :=
  ReflTransGen fun a b ↦ b ∈ step M a
#align turing.TM2.reaches Turing.TM2.Reaches

/-- Given a set `S` of states, `SupportsStmt S q` means that `q` only jumps to states in `S`. -/
def SupportsStmt (S : Finset Λ) : Stmt₂ → Prop
  | push _ _ q => SupportsStmt S q
  | peek _ _ q => SupportsStmt S q
  | pop _ _ q => SupportsStmt S q
  | load _ q => SupportsStmt S q
  | branch _ q₁ q₂ => SupportsStmt S q₁ ∧ SupportsStmt S q₂
  | goto l => ∀ v, l v ∈ S
  | halt => True
#align turing.TM2.supports_stmt Turing.TM2.SupportsStmt

open Classical

/-- The set of subtree statements in a statement. -/
noncomputable def stmts₁ : Stmt₂ → Finset Stmt₂
  | Q@(push _ _ q) => insert Q (stmts₁ q)
  | Q@(peek _ _ q) => insert Q (stmts₁ q)
  | Q@(pop _ _ q) => insert Q (stmts₁ q)
  | Q@(load _ q) => insert Q (stmts₁ q)
  | Q@(branch _ q₁ q₂) => insert Q (stmts₁ q₁ ∪ stmts₁ q₂)
  | Q@(goto _) => {Q}
  | Q@halt => {Q}
#align turing.TM2.stmts₁ Turing.TM2.stmts₁

theorem stmts₁_self {q : Stmt₂} : q ∈ stmts₁ q := by
  cases q <;> simp only [Finset.mem_insert_self, Finset.mem_singleton_self, stmts₁]
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
#align turing.TM2.stmts₁_self Turing.TM2.stmts₁_self

theorem stmts₁_trans {q₁ q₂ : Stmt₂} : q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ := by
  intro h₁₂ q₀ h₀₁
  -- ⊢ q₀ ∈ stmts₁ q₂
  induction' q₂ with _ _ q IH _ _ q IH _ _ q IH _ q IH <;> simp only [stmts₁] at h₁₂ ⊢ <;>
                                                           -- ⊢ q₀ ∈ insert (push k✝ a✝ q) (stmts₁ q)
                                                           -- ⊢ q₀ ∈ insert (peek k✝ a✝ q) (stmts₁ q)
                                                           -- ⊢ q₀ ∈ insert (pop k✝ a✝ q) (stmts₁ q)
                                                           -- ⊢ q₀ ∈ insert (load a✝ q) (stmts₁ q)
                                                           -- ⊢ q₀ ∈ insert (branch a✝² a✝¹ a✝) (stmts₁ a✝¹ ∪ stmts₁ a✝)
                                                           -- ⊢ q₀ ∈ {goto a✝}
                                                           -- ⊢ q₀ ∈ {halt}
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at h₁₂
    -- ⊢ q₀ ∈ insert (push k✝ a✝ q) (stmts₁ q)
    -- ⊢ q₀ ∈ insert (peek k✝ a✝ q) (stmts₁ q)
    -- ⊢ q₀ ∈ insert (pop k✝ a✝ q) (stmts₁ q)
    -- ⊢ q₀ ∈ insert (load a✝ q) (stmts₁ q)
    -- ⊢ q₀ ∈ insert (branch a✝² a✝¹ a✝) (stmts₁ a✝¹ ∪ stmts₁ a✝)
    -- ⊢ q₀ ∈ {goto a✝}
    -- ⊢ q₀ ∈ {halt}
  iterate 4
    rcases h₁₂ with (rfl | h₁₂)
    · unfold stmts₁ at h₀₁
      exact h₀₁
    · exact Finset.mem_insert_of_mem (IH h₁₂)
  case branch f q₁ q₂ IH₁ IH₂ =>
    rcases h₁₂ with (rfl | h₁₂ | h₁₂)
    · unfold stmts₁ at h₀₁
      exact h₀₁
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (IH₁ h₁₂))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (IH₂ h₁₂))
  case goto l => subst h₁₂; exact h₀₁
  -- ⊢ q₀ ∈ {halt}
  -- 🎉 no goals
  case halt => subst h₁₂; exact h₀₁
  -- 🎉 no goals
  -- 🎉 no goals
#align turing.TM2.stmts₁_trans Turing.TM2.stmts₁_trans

theorem stmts₁_supportsStmt_mono {S : Finset Λ} {q₁ q₂ : Stmt₂} (h : q₁ ∈ stmts₁ q₂)
    (hs : SupportsStmt S q₂) : SupportsStmt S q₁ := by
  induction' q₂ with _ _ q IH _ _ q IH _ _ q IH _ q IH <;>
    simp only [stmts₁, SupportsStmt, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      at h hs
  iterate 4 rcases h with (rfl | h) <;> [exact hs; exact IH h hs]
  case branch f q₁ q₂ IH₁ IH₂ => rcases h with (rfl | h | h); exacts [hs, IH₁ h hs.1, IH₂ h hs.2]
  -- ⊢ SupportsStmt S q₁
  -- 🎉 no goals
  case goto l => subst h; exact hs
  -- ⊢ SupportsStmt S q₁
  -- 🎉 no goals
  case halt => subst h; trivial
  -- 🎉 no goals
  -- 🎉 no goals
#align turing.TM2.stmts₁_supports_stmt_mono Turing.TM2.stmts₁_supportsStmt_mono

/-- The set of statements accessible from initial set `S` of labels. -/
noncomputable def stmts (M : Λ → Stmt₂) (S : Finset Λ) : Finset (Option Stmt₂) :=
  Finset.insertNone (S.biUnion fun q ↦ stmts₁ (M q))
#align turing.TM2.stmts Turing.TM2.stmts

theorem stmts_trans {M : Λ → Stmt₂} {S : Finset Λ} {q₁ q₂ : Stmt₂} (h₁ : q₁ ∈ stmts₁ q₂) :
    some q₂ ∈ stmts M S → some q₁ ∈ stmts M S := by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h₂ ↦ ⟨_, ls, stmts₁_trans h₂ h₁⟩
  -- 🎉 no goals
#align turing.TM2.stmts_trans Turing.TM2.stmts_trans

variable [Inhabited Λ]

/-- Given a TM2 machine `M` and a set `S` of states, `Supports M S` means that all states in
`S` jump only to other states in `S`. -/
def Supports (M : Λ → Stmt₂) (S : Finset Λ) :=
  default ∈ S ∧ ∀ q ∈ S, SupportsStmt S (M q)
#align turing.TM2.supports Turing.TM2.Supports

theorem stmts_supportsStmt {M : Λ → Stmt₂} {S : Finset Λ} {q : Stmt₂} (ss : Supports M S) :
    some q ∈ stmts M S → SupportsStmt S q := by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h ↦ stmts₁_supportsStmt_mono h (ss.2 _ ls)
  -- 🎉 no goals
#align turing.TM2.stmts_supports_stmt Turing.TM2.stmts_supportsStmt

theorem step_supports (M : Λ → Stmt₂) {S : Finset Λ} (ss : Supports M S) :
    ∀ {c c' : Cfg₂}, c' ∈ step M c → c.l ∈ Finset.insertNone S → c'.l ∈ Finset.insertNone S
  | ⟨some l₁, v, T⟩, c', h₁, h₂ => by
    replace h₂ := ss.2 _ (Finset.some_mem_insertNone.1 h₂)
    -- ⊢ c'.l ∈ ↑Finset.insertNone S
    simp only [step, Option.mem_def, Option.some.injEq] at h₁; subst c'
    -- ⊢ c'.l ∈ ↑Finset.insertNone S
                                                               -- ⊢ (stepAux (M l₁) v T).l ∈ ↑Finset.insertNone S
    revert h₂; induction' M l₁ with _ _ q IH _ _ q IH _ _ q IH _ q IH generalizing v T <;> intro hs
    -- ⊢ SupportsStmt S (M l₁) → (stepAux (M l₁) v T).l ∈ ↑Finset.insertNone S
                                                                                           -- ⊢ (stepAux (push k✝ a✝ q) v T).l ∈ ↑Finset.insertNone S
                                                                                           -- ⊢ (stepAux (peek k✝ a✝ q) v T).l ∈ ↑Finset.insertNone S
                                                                                           -- ⊢ (stepAux (pop k✝ a✝ q) v T).l ∈ ↑Finset.insertNone S
                                                                                           -- ⊢ (stepAux (load a✝ q) v T).l ∈ ↑Finset.insertNone S
                                                                                           -- ⊢ (stepAux (branch a✝² a✝¹ a✝) v T).l ∈ ↑Finset.insertNone S
                                                                                           -- ⊢ (stepAux (goto a✝) v T).l ∈ ↑Finset.insertNone S
                                                                                           -- ⊢ (stepAux halt v T).l ∈ ↑Finset.insertNone S
    iterate 4 exact IH _ _ hs
    case branch p q₁' q₂' IH₁ IH₂ =>
      unfold stepAux; cases p v
      · exact IH₂ _ _ hs.2
      · exact IH₁ _ _ hs.1
    case goto => exact Finset.some_mem_insertNone.2 (hs _)
    -- ⊢ (stepAux halt v T).l ∈ ↑Finset.insertNone S
    -- 🎉 no goals
    case halt => apply Multiset.mem_cons_self
    -- 🎉 no goals
    -- 🎉 no goals
#align turing.TM2.step_supports Turing.TM2.step_supports

variable [Inhabited σ]

/-- The initial state of the TM2 model. The input is provided on a designated stack. -/
def init (k : K) (L : List (Γ k)) : Cfg₂ :=
  ⟨some default, default, update (fun _ ↦ []) k L⟩
#align turing.TM2.init Turing.TM2.init

/-- Evaluates a TM2 program to completion, with the output on the same stack as the input. -/
def eval (M : Λ → Stmt₂) (k : K) (L : List (Γ k)) : Part (List (Γ k)) :=
  (Turing.eval (step M) (init k L)).map fun c ↦ c.stk k
#align turing.TM2.eval Turing.TM2.eval

end

end TM2

/-!
## TM2 emulator in TM1

To prove that TM2 computable functions are TM1 computable, we need to reduce each TM2 program to a
TM1 program. So suppose a TM2 program is given. This program has to maintain a whole collection of
stacks, but we have only one tape, so we must "multiplex" them all together. Pictorially, if stack
1 contains `[a, b]` and stack 2 contains `[c, d, e, f]` then the tape looks like this:

```
 bottom:  ... | _ | T | _ | _ | _ | _ | ...
 stack 1: ... | _ | b | a | _ | _ | _ | ...
 stack 2: ... | _ | f | e | d | c | _ | ...
```

where a tape element is a vertical slice through the diagram. Here the alphabet is
`Γ' := Bool × ∀ k, Option (Γ k)`, where:

* `bottom : Bool` is marked only in one place, the initial position of the TM, and represents the
  tail of all stacks. It is never modified.
* `stk k : Option (Γ k)` is the value of the `k`-th stack, if in range, otherwise `none` (which is
  the blank value). Note that the head of the stack is at the far end; this is so that push and pop
  don't have to do any shifting.

In "resting" position, the TM is sitting at the position marked `bottom`. For non-stack actions,
it operates in place, but for the stack actions `push`, `peek`, and `pop`, it must shuttle to the
end of the appropriate stack, make its changes, and then return to the bottom. So the states are:

* `normal (l : Λ)`: waiting at `bottom` to execute function `l`
* `go k (s : StAct k) (q : Stmt₂)`: travelling to the right to get to the end of stack `k` in
  order to perform stack action `s`, and later continue with executing `q`
* `ret (q : Stmt₂)`: travelling to the left after having performed a stack action, and executing
  `q` once we arrive

Because of the shuttling, emulation overhead is `O(n)`, where `n` is the current maximum of the
length of all stacks. Therefore a program that takes `k` steps to run in TM2 takes `O((m+k)k)`
steps to run when emulated in TM1, where `m` is the length of the input.
-/


namespace TM2to1

-- "TM2to1"
set_option linter.uppercaseLean3 false

-- A displaced lemma proved in unnecessary generality
theorem stk_nth_val {K : Type*} {Γ : K → Type*} {L : ListBlank (∀ k, Option (Γ k))} {k S} (n)
    (hL : ListBlank.map (proj k) L = ListBlank.mk (List.map some S).reverse) :
    L.nth n k = S.reverse.get? n := by
  rw [← proj_map_nth, hL, ← List.map_reverse, ListBlank.nth_mk, List.getI_eq_iget_get?,
    List.get?_map]
  cases S.reverse.get? n <;> rfl
  -- ⊢ Option.iget (Option.map some none) = none
                             -- 🎉 no goals
                             -- 🎉 no goals
#align turing.TM2to1.stk_nth_val Turing.TM2to1.stk_nth_val

section

variable {K : Type*} [DecidableEq K]

variable {Γ : K → Type*}

variable {Λ : Type*} [Inhabited Λ]

variable {σ : Type*} [Inhabited σ]

local notation "Stmt₂" => TM2.Stmt Γ Λ σ

local notation "Cfg₂" => TM2.Cfg Γ Λ σ

-- Porting note: `DecidableEq K` is not necessary.
/-- The alphabet of the TM2 simulator on TM1 is a marker for the stack bottom,
plus a vector of stack elements for each stack, or none if the stack does not extend this far. -/
def Γ' :=
  Bool × ∀ k, Option (Γ k)
#align turing.TM2to1.Γ' Turing.TM2to1.Γ'

local notation "Γ'₂₁" => @Γ' K Γ  -- Porting note: Added this to clean up types.

instance Γ'.inhabited : Inhabited Γ'₂₁ :=
  ⟨⟨false, fun _ ↦ none⟩⟩
#align turing.TM2to1.Γ'.inhabited Turing.TM2to1.Γ'.inhabited

instance Γ'.fintype [Fintype K] [∀ k, Fintype (Γ k)] : Fintype Γ'₂₁ :=
  instFintypeProd _ _
#align turing.TM2to1.Γ'.fintype Turing.TM2to1.Γ'.fintype

/-- The bottom marker is fixed throughout the calculation, so we use the `addBottom` function
to express the program state in terms of a tape with only the stacks themselves. -/
def addBottom (L : ListBlank (∀ k, Option (Γ k))) : ListBlank Γ'₂₁ :=
  ListBlank.cons (true, L.head) (L.tail.map ⟨Prod.mk false, rfl⟩)
#align turing.TM2to1.add_bottom Turing.TM2to1.addBottom

theorem addBottom_map (L : ListBlank (∀ k, Option (Γ k))) :
    (addBottom L).map ⟨Prod.snd, by rfl⟩ = L := by
                                    -- 🎉 no goals
  simp only [addBottom, ListBlank.map_cons]
  -- ⊢ ListBlank.cons (ListBlank.head L) (ListBlank.map { f := Prod.snd, map_pt' := …
  convert ListBlank.cons_head_tail L
  -- ⊢ ListBlank.map { f := Prod.snd, map_pt' := (_ : default.snd = default.snd) }  …
  generalize ListBlank.tail L = L'
  -- ⊢ ListBlank.map { f := Prod.snd, map_pt' := (_ : default.snd = default.snd) }  …
  refine' L'.induction_on fun l ↦ _; simp
  -- ⊢ ListBlank.map { f := Prod.snd, map_pt' := (_ : default.snd = default.snd) }  …
                                     -- 🎉 no goals
#align turing.TM2to1.add_bottom_map Turing.TM2to1.addBottom_map

theorem addBottom_modifyNth (f : (∀ k, Option (Γ k)) → ∀ k, Option (Γ k))
    (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    (addBottom L).modifyNth (fun a ↦ (a.1, f a.2)) n = addBottom (L.modifyNth f n) := by
  cases n <;>
  -- ⊢ ListBlank.modifyNth (fun a => (a.fst, f a.snd)) Nat.zero (addBottom L) = add …
    simp only [addBottom, ListBlank.head_cons, ListBlank.modifyNth, ListBlank.tail_cons]
    -- 🎉 no goals
    -- ⊢ ListBlank.cons (true, ListBlank.head L) (ListBlank.modifyNth (fun a => (a.fs …
  congr; symm; apply ListBlank.map_modifyNth; intro; rfl
  -- ⊢ ListBlank.modifyNth (fun a => (a.fst, f a.snd)) n✝ (ListBlank.map { f := Pro …
         -- ⊢ ListBlank.map { f := Prod.mk false, map_pt' := (_ : (false, default) = (fals …
               -- ⊢ ∀ (x : (k : K) → Option (Γ k)), PointedMap.f { f := Prod.mk false, map_pt' : …
                                              -- ⊢ PointedMap.f { f := Prod.mk false, map_pt' := (_ : (false, default) = (false …
                                                     -- 🎉 no goals
#align turing.TM2to1.add_bottom_modify_nth Turing.TM2to1.addBottom_modifyNth

theorem addBottom_nth_snd (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    ((addBottom L).nth n).2 = L.nth n := by
  conv => rhs; rw [← addBottom_map L, ListBlank.nth_map]
  -- 🎉 no goals
#align turing.TM2to1.add_bottom_nth_snd Turing.TM2to1.addBottom_nth_snd

theorem addBottom_nth_succ_fst (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    ((addBottom L).nth (n + 1)).1 = false := by
  rw [ListBlank.nth_succ, addBottom, ListBlank.tail_cons, ListBlank.nth_map]
  -- 🎉 no goals
#align turing.TM2to1.add_bottom_nth_succ_fst Turing.TM2to1.addBottom_nth_succ_fst

theorem addBottom_head_fst (L : ListBlank (∀ k, Option (Γ k))) : (addBottom L).head.1 = true := by
  rw [addBottom, ListBlank.head_cons]
  -- 🎉 no goals
#align turing.TM2to1.add_bottom_head_fst Turing.TM2to1.addBottom_head_fst

/-- A stack action is a command that interacts with the top of a stack. Our default position
is at the bottom of all the stacks, so we have to hold on to this action while going to the end
to modify the stack. -/
inductive StAct (k : K)
  | push : (σ → Γ k) → StAct k
  | peek : (σ → Option (Γ k) → σ) → StAct k
  | pop : (σ → Option (Γ k) → σ) → StAct k
#align turing.TM2to1.st_act Turing.TM2to1.StAct

local notation "StAct₂" => @StAct K Γ σ  -- Porting note: Added this to clean up types.

instance StAct.inhabited {k : K} : Inhabited (StAct₂ k) :=
  ⟨StAct.peek fun s _ ↦ s⟩
#align turing.TM2to1.st_act.inhabited Turing.TM2to1.StAct.inhabited

section

open StAct

-- Porting note: `Inhabited Γ` is not necessary.
/-- The TM2 statement corresponding to a stack action. -/
def stRun {k : K} : StAct₂ k → Stmt₂ → Stmt₂
  | push f => TM2.Stmt.push k f
  | peek f => TM2.Stmt.peek k f
  | pop f => TM2.Stmt.pop k f
#align turing.TM2to1.st_run Turing.TM2to1.stRun

/-- The effect of a stack action on the local variables, given the value of the stack. -/
def stVar {k : K} (v : σ) (l : List (Γ k)) : StAct₂ k → σ
  | push _ => v
  | peek f => f v l.head?
  | pop f => f v l.head?
#align turing.TM2to1.st_var Turing.TM2to1.stVar

/-- The effect of a stack action on the stack. -/
def stWrite {k : K} (v : σ) (l : List (Γ k)) : StAct₂ k → List (Γ k)
  | push f => f v :: l
  | peek _ => l
  | pop _ => l.tail
#align turing.TM2to1.st_write Turing.TM2to1.stWrite

/-- We have partitioned the TM2 statements into "stack actions", which require going to the end
of the stack, and all other actions, which do not. This is a modified recursor which lumps the
stack actions into one. -/
@[elab_as_elim]
def stmtStRec.{l} {C : Stmt₂ → Sort l} (H₁ : ∀ (k) (s : StAct₂ k) (q) (_ : C q), C (stRun s q))
    (H₂ : ∀ (a q) (_ : C q), C (TM2.Stmt.load a q))
    (H₃ : ∀ (p q₁ q₂) (_ : C q₁) (_ : C q₂), C (TM2.Stmt.branch p q₁ q₂))
    (H₄ : ∀ l, C (TM2.Stmt.goto l)) (H₅ : C TM2.Stmt.halt) : ∀ n, C n
  | TM2.Stmt.push _ f q => H₁ _ (push f) _ (stmtStRec H₁ H₂ H₃ H₄ H₅ q)
  | TM2.Stmt.peek _ f q => H₁ _ (peek f) _ (stmtStRec H₁ H₂ H₃ H₄ H₅ q)
  | TM2.Stmt.pop _ f q => H₁ _ (pop f) _ (stmtStRec H₁ H₂ H₃ H₄ H₅ q)
  | TM2.Stmt.load _ q => H₂ _ _ (stmtStRec H₁ H₂ H₃ H₄ H₅ q)
  | TM2.Stmt.branch _ q₁ q₂ => H₃ _ _ _ (stmtStRec H₁ H₂ H₃ H₄ H₅ q₁) (stmtStRec H₁ H₂ H₃ H₄ H₅ q₂)
  | TM2.Stmt.goto _ => H₄ _
  | TM2.Stmt.halt => H₅
#align turing.TM2to1.stmt_st_rec Turing.TM2to1.stmtStRec

theorem supports_run (S : Finset Λ) {k : K} (s : StAct₂ k) (q : Stmt₂) :
    TM2.SupportsStmt S (stRun s q) ↔ TM2.SupportsStmt S q := by
  cases s <;> rfl
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
#align turing.TM2to1.supports_run Turing.TM2to1.supports_run

end

/-- The machine states of the TM2 emulator. We can either be in a normal state when waiting for the
next TM2 action, or we can be in the "go" and "return" states to go to the top of the stack and
return to the bottom, respectively. -/
inductive Λ'
  | normal : Λ → Λ'
  | go (k : K) : StAct₂ k → Stmt₂ → Λ'
  | ret : Stmt₂ → Λ'
#align turing.TM2to1.Λ' Turing.TM2to1.Λ'

local notation "Λ'₂₁" => @Λ' K Γ Λ σ  -- Porting note: Added this to clean up types.

open Λ'

instance Λ'.inhabited : Inhabited Λ'₂₁ :=
  ⟨normal default⟩
#align turing.TM2to1.Λ'.inhabited Turing.TM2to1.Λ'.inhabited

local notation "Stmt₂₁" => TM1.Stmt Γ'₂₁ Λ'₂₁ σ

local notation "Cfg₂₁" => TM1.Cfg Γ'₂₁ Λ'₂₁ σ

open TM1.Stmt

/-- The program corresponding to state transitions at the end of a stack. Here we start out just
after the top of the stack, and should end just after the new top of the stack. -/
def trStAct {k : K} (q : Stmt₂₁) : StAct₂ k → Stmt₂₁
  | StAct.push f => (write fun a s ↦ (a.1, update a.2 k <| some <| f s)) <| move Dir.right q
  | StAct.peek f => move Dir.left <| (load fun a s ↦ f s (a.2 k)) <| move Dir.right q
  | StAct.pop f =>
    branch (fun a _ ↦ a.1) (load (fun _ s ↦ f s none) q)
      (move Dir.left <|
        (load fun a s ↦ f s (a.2 k)) <| write (fun a _ ↦ (a.1, update a.2 k none)) q)
#align turing.TM2to1.tr_st_act Turing.TM2to1.trStAct

/-- The initial state for the TM2 emulator, given an initial TM2 state. All stacks start out empty
except for the input stack, and the stack bottom mark is set at the head. -/
def trInit (k : K) (L : List (Γ k)) : List Γ'₂₁ :=
  let L' : List Γ'₂₁ := L.reverse.map fun a ↦ (false, update (fun _ ↦ none) k (some a))
  (true, L'.headI.2) :: L'.tail
#align turing.TM2to1.tr_init Turing.TM2to1.trInit

theorem step_run {k : K} (q : Stmt₂) (v : σ) (S : ∀ k, List (Γ k)) : ∀ s : StAct₂ k,
    TM2.stepAux (stRun s q) v S = TM2.stepAux q (stVar v (S k) s) (update S k (stWrite v (S k) s))
  | StAct.push f => rfl
  | StAct.peek f => by unfold stWrite; rw [Function.update_eq_self]; rfl
                       -- ⊢ TM2.stepAux (stRun (StAct.peek f) q) v S =
                                       -- ⊢ TM2.stepAux (stRun (StAct.peek f) q) v S = TM2.stepAux q (stVar v (S k) (StA …
                                                                     -- 🎉 no goals
  | StAct.pop f => rfl
#align turing.TM2to1.step_run Turing.TM2to1.step_run

/-- The translation of TM2 statements to TM1 statements. regular actions have direct equivalents,
but stack actions are deferred by going to the corresponding `go` state, so that we can find the
appropriate stack top. -/
def trNormal : Stmt₂ → Stmt₂₁
  | TM2.Stmt.push k f q => goto fun _ _ ↦ go k (StAct.push f) q
  | TM2.Stmt.peek k f q => goto fun _ _ ↦ go k (StAct.peek f) q
  | TM2.Stmt.pop k f q => goto fun _ _ ↦ go k (StAct.pop f) q
  | TM2.Stmt.load a q => load (fun _ ↦ a) (trNormal q)
  | TM2.Stmt.branch f q₁ q₂ => branch (fun _ ↦ f) (trNormal q₁) (trNormal q₂)
  | TM2.Stmt.goto l => goto fun _ s ↦ normal (l s)
  | TM2.Stmt.halt => halt
#align turing.TM2to1.tr_normal Turing.TM2to1.trNormal

theorem trNormal_run {k : K} (s : StAct₂ k) (q : Stmt₂) :
    trNormal (stRun s q) = goto fun _ _ ↦ go k s q := by
  cases s <;> rfl
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
#align turing.TM2to1.tr_normal_run Turing.TM2to1.trNormal_run

open Classical

/-- The set of machine states accessible from an initial TM2 statement. -/
noncomputable def trStmts₁ : Stmt₂ → Finset Λ'₂₁
  | TM2.Stmt.push k f q => {go k (StAct.push f) q, ret q} ∪ trStmts₁ q
  | TM2.Stmt.peek k f q => {go k (StAct.peek f) q, ret q} ∪ trStmts₁ q
  | TM2.Stmt.pop k f q => {go k (StAct.pop f) q, ret q} ∪ trStmts₁ q
  | TM2.Stmt.load _ q => trStmts₁ q
  | TM2.Stmt.branch _ q₁ q₂ => trStmts₁ q₁ ∪ trStmts₁ q₂
  | _ => ∅
#align turing.TM2to1.tr_stmts₁ Turing.TM2to1.trStmts₁

theorem trStmts₁_run {k : K} {s : StAct₂ k} {q : Stmt₂} :
    trStmts₁ (stRun s q) = {go k s q, ret q} ∪ trStmts₁ q := by
  cases s <;> simp only [trStmts₁]
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
#align turing.TM2to1.tr_stmts₁_run Turing.TM2to1.trStmts₁_run

theorem tr_respects_aux₂ {k : K} {q : Stmt₂₁} {v : σ} {S : ∀ k, List (Γ k)}
    {L : ListBlank (∀ k, Option (Γ k))}
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) (o : StAct₂ k) :
    let v' := stVar v (S k) o
    let Sk' := stWrite v (S k) o
    let S' := update S k Sk'
    ∃ L' : ListBlank (∀ k, Option (Γ k)),
      (∀ k, L'.map (proj k) = ListBlank.mk ((S' k).map some).reverse) ∧
        TM1.stepAux (trStAct q o) v
            ((Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))) =
          TM1.stepAux q v' ((Tape.move Dir.right)^[(S' k).length] (Tape.mk' ∅ (addBottom L'))) := by
  dsimp only; simp; cases o <;> simp only [stWrite, stVar, trStAct, TM1.stepAux]
  -- ⊢ ∃ L', (∀ (k_1 : K), ListBlank.map (proj k_1) L' = ListBlank.mk (List.reverse …
              -- ⊢ ∃ L', (∀ (k_1 : K), ListBlank.map (proj k_1) L' = ListBlank.mk (List.reverse …
                                -- ⊢ ∃ L', (∀ (k_1 : K), ListBlank.map (proj k_1) L' = ListBlank.mk (List.reverse …
                                -- ⊢ ∃ L', (∀ (k_1 : K), ListBlank.map (proj k_1) L' = ListBlank.mk (List.reverse …
                                -- ⊢ ∃ L', (∀ (k_1 : K), ListBlank.map (proj k_1) L' = ListBlank.mk (List.reverse …
  case push f =>
    have := Tape.write_move_right_n fun a : Γ' ↦ (a.1, update a.2 k (some (f v)))
    refine'
      ⟨_, fun k' ↦ _, by
        -- Porting note: `rw [...]` to `erw [...]; rfl`.
        -- https://github.com/leanprover-community/mathlib4/issues/5164
        erw [Tape.move_right_n_head, List.length, Tape.mk'_nth_nat, this,
          addBottom_modifyNth fun a ↦ update a k (some (f v)), Nat.add_one, iterate_succ']
        rfl⟩
    refine' ListBlank.ext fun i ↦ _
    rw [ListBlank.nth_map, ListBlank.nth_modifyNth, proj, PointedMap.mk_val]
    by_cases h' : k' = k
    · subst k'
      split_ifs with h
        <;> simp only [List.reverse_cons, Function.update_same, ListBlank.nth_mk, List.map]
      -- Porting note: `le_refl` is required.
      · rw [List.getI_eq_get, List.get_append_right'] <;>
          simp only [h, List.get_singleton, List.length_map, List.length_reverse, Nat.succ_pos',
            List.length_append, lt_add_iff_pos_right, List.length, le_refl]
      rw [← proj_map_nth, hL, ListBlank.nth_mk]
      cases' lt_or_gt_of_ne h with h h
      · rw [List.getI_append]
        simpa only [List.length_map, List.length_reverse] using h
      · rw [gt_iff_lt] at h
        rw [List.getI_eq_default, List.getI_eq_default] <;>
          simp only [Nat.add_one_le_iff, h, List.length, le_of_lt, List.length_reverse,
            List.length_append, List.length_map]
    · split_ifs <;> rw [Function.update_noteq h', ← proj_map_nth, hL]
      rw [Function.update_noteq h']
  case peek f =>
    rw [Function.update_eq_self]
    use L, hL; rw [Tape.move_left_right]; congr
    cases e : S k; · rfl
    rw [List.length_cons, iterate_succ', Function.comp, Tape.move_right_left,
      Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_snd, stk_nth_val _ (hL k), e,
      List.reverse_cons, ← List.length_reverse, List.get?_concat_length]
    rfl
  case pop f =>
    cases' e : S k with hd tl
    · simp only [Tape.mk'_head, ListBlank.head_cons, Tape.move_left_mk', List.length,
        Tape.write_mk', List.head?, iterate_zero_apply, List.tail_nil]
      rw [← e, Function.update_eq_self]
      exact ⟨L, hL, by rw [addBottom_head_fst, cond]⟩
    · refine'
        ⟨_, fun k' ↦ _, by
          erw [List.length_cons, Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_succ_fst,
            cond, iterate_succ', Function.comp, Tape.move_right_left, Tape.move_right_n_head,
            Tape.mk'_nth_nat, Tape.write_move_right_n fun a : Γ' ↦ (a.1, update a.2 k none),
            addBottom_modifyNth fun a ↦ update a k none, addBottom_nth_snd,
            stk_nth_val _ (hL k), e,
            show (List.cons hd tl).reverse.get? tl.length = some hd by
              rw [List.reverse_cons, ← List.length_reverse, List.get?_concat_length],
            List.head?, List.tail]⟩
      refine' ListBlank.ext fun i ↦ _
      rw [ListBlank.nth_map, ListBlank.nth_modifyNth, proj, PointedMap.mk_val]
      by_cases h' : k' = k
      · subst k'
        split_ifs with h <;> simp only [Function.update_same, ListBlank.nth_mk, List.tail]
        · rw [List.getI_eq_default]
          · rfl
          rw [h, List.length_reverse, List.length_map]
        rw [← proj_map_nth, hL, ListBlank.nth_mk, e, List.map, List.reverse_cons]
        cases' lt_or_gt_of_ne h with h h
        · rw [List.getI_append]
          simpa only [List.length_map, List.length_reverse] using h
        · rw [gt_iff_lt] at h
          rw [List.getI_eq_default, List.getI_eq_default] <;>
            simp only [Nat.add_one_le_iff, h, List.length, le_of_lt, List.length_reverse,
              List.length_append, List.length_map]
      · split_ifs <;> rw [Function.update_noteq h', ← proj_map_nth, hL]
        rw [Function.update_noteq h']
#align turing.TM2to1.tr_respects_aux₂ Turing.TM2to1.tr_respects_aux₂

variable (M : Λ → TM2.Stmt Γ Λ σ)  -- Porting note: Unfolded `Stmt₂`.

/-- The TM2 emulator machine states written as a TM1 program.
This handles the `go` and `ret` states, which shuttle to and from a stack top. -/
def tr : Λ'₂₁ → Stmt₂₁
  | normal q => trNormal (M q)
  | go k s q =>
    branch (fun a _ ↦ (a.2 k).isNone) (trStAct (goto fun _ _ ↦ ret q) s)
      (move Dir.right <| goto fun _ _ ↦ go k s q)
  | ret q => branch (fun a _ ↦ a.1) (trNormal q) (move Dir.left <| goto fun _ _ ↦ ret q)
#align turing.TM2to1.tr Turing.TM2to1.tr

-- Porting note: unknown attribute
-- attribute [local pp_using_anonymous_constructor] Turing.TM1.Cfg

/-- The relation between TM2 configurations and TM1 configurations of the TM2 emulator. -/
inductive TrCfg : Cfg₂ → Cfg₂₁ → Prop
  | mk {q : Option Λ} {v : σ} {S : ∀ k, List (Γ k)} (L : ListBlank (∀ k, Option (Γ k))) :
    (∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) →
      TrCfg ⟨q, v, S⟩ ⟨q.map normal, v, Tape.mk' ∅ (addBottom L)⟩
#align turing.TM2to1.tr_cfg Turing.TM2to1.TrCfg

theorem tr_respects_aux₁ {k} (o q v) {S : List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse) (n) (H : n ≤ S.length) :
    Reaches₀ (TM1.step (tr M)) ⟨some (go k o q), v, Tape.mk' ∅ (addBottom L)⟩
      ⟨some (go k o q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction' n with n IH; · rfl
  -- ⊢ Reaches₀ (TM1.step (tr M)) { l := some (go k o q), var := v, Tape := Tape.mk …
                            -- 🎉 no goals
  apply (IH (le_of_lt H)).tail
  -- ⊢ { l := some (go k o q), var := v, Tape := (Tape.move Dir.right)^[Nat.succ n] …
  rw [iterate_succ_apply'];
  -- ⊢ { l := some (go k o q), var := v, Tape := Tape.move Dir.right ((Tape.move Di …
  simp only [TM1.step, TM1.stepAux, tr, Tape.mk'_nth_nat, Tape.move_right_n_head,
    addBottom_nth_snd, Option.mem_def]
  rw [stk_nth_val _ hL, List.get?_eq_get]; rfl; rwa [List.length_reverse]
  -- ⊢ some (bif Option.isNone (some (List.get (List.reverse S) { val := n, isLt := …
                                           -- ⊢ n < List.length (List.reverse S)
                                                -- 🎉 no goals
#align turing.TM2to1.tr_respects_aux₁ Turing.TM2to1.tr_respects_aux₁

theorem tr_respects_aux₃ {q v} {L : ListBlank (∀ k, Option (Γ k))} (n) : Reaches₀ (TM1.step (tr M))
    ⟨some (ret q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
    ⟨some (ret q), v, Tape.mk' ∅ (addBottom L)⟩ := by
  induction' n with n IH; · rfl
  -- ⊢ Reaches₀ (TM1.step (tr M)) { l := some (ret q), var := v, Tape := (Tape.move …
                            -- 🎉 no goals
  refine' Reaches₀.head _ IH
  -- ⊢ { l := some (ret q), var := v, Tape := (Tape.move Dir.right)^[n] (Tape.mk' ∅ …
  simp only [Option.mem_def, TM1.step]
  -- ⊢ some (TM1.stepAux (tr M (ret q)) v ((Tape.move Dir.right)^[Nat.succ n] (Tape …
  rw [Option.some_inj, tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat,
    addBottom_nth_succ_fst, TM1.stepAux, iterate_succ', Function.comp_apply, Tape.move_right_left]
  rfl
  -- 🎉 no goals
#align turing.TM2to1.tr_respects_aux₃ Turing.TM2to1.tr_respects_aux₃

theorem tr_respects_aux {q v T k} {S : ∀ k, List (Γ k)}
    (hT : ∀ k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map some).reverse) (o : StAct₂ k)
    (IH : ∀ {v : σ} {S : ∀ k : K, List (Γ k)} {T : ListBlank (∀ k, Option (Γ k))},
      (∀ k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map some).reverse) →
      ∃ b, TrCfg (TM2.stepAux q v S) b ∧
        Reaches (TM1.step (tr M)) (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom T))) b) :
    ∃ b, TrCfg (TM2.stepAux (stRun o q) v S) b ∧ Reaches (TM1.step (tr M))
      (TM1.stepAux (trNormal (stRun o q)) v (Tape.mk' ∅ (addBottom T))) b := by
  simp only [trNormal_run, step_run]
  -- ⊢ ∃ b, TrCfg (TM2.stepAux q (stVar v (S k) o) (update S k (stWrite v (S k) o)) …
  have hgo := tr_respects_aux₁ M o q v (hT k) _ le_rfl
  -- ⊢ ∃ b, TrCfg (TM2.stepAux q (stVar v (S k) o) (update S k (stWrite v (S k) o)) …
  obtain ⟨T', hT', hrun⟩ := tr_respects_aux₂ hT o
  -- ⊢ ∃ b, TrCfg (TM2.stepAux q (stVar v (S k) o) (update S k (stWrite v (S k) o)) …
  have := hgo.tail' rfl
  -- ⊢ ∃ b, TrCfg (TM2.stepAux q (stVar v (S k) o) (update S k (stWrite v (S k) o)) …
  rw [tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_snd,
    stk_nth_val _ (hT k), List.get?_len_le (le_of_eq (List.length_reverse _)), Option.isNone, cond,
    hrun, TM1.stepAux] at this
  obtain ⟨c, gc, rc⟩ := IH hT'
  -- ⊢ ∃ b, TrCfg (TM2.stepAux q (stVar v (S k) o) (update S k (stWrite v (S k) o)) …
  refine' ⟨c, gc, (this.to₀.trans (tr_respects_aux₃ M _) c (TransGen.head' rfl _)).to_reflTransGen⟩
  -- ⊢ ReflTransGen (fun a b => b ∈ TM1.step (tr M) a) (TM1.stepAux (tr M (ret q))  …
  rw [tr, TM1.stepAux, Tape.mk'_head, addBottom_head_fst]
  -- ⊢ ReflTransGen (fun a b => b ∈ TM1.step (tr M) a) (bif true then TM1.stepAux ( …
  exact rc
  -- 🎉 no goals
#align turing.TM2to1.tr_respects_aux Turing.TM2to1.tr_respects_aux

attribute [local simp] Respects TM2.step TM2.stepAux trNormal

theorem tr_respects : Respects (TM2.step M) (TM1.step (tr M)) TrCfg := by
  -- Porting note: `simp only`s are required for beta reductions.
  intro c₁ c₂ h
  -- ⊢ match TM2.step M c₁ with
  cases' h with l v S L hT
  -- ⊢ match TM2.step M { l := l, var := v, stk := S } with
  cases' l with l; · constructor
                     -- 🎉 no goals
  simp only [TM2.step, Respects, Option.map_some']
  -- ⊢ ∃ b₂, TrCfg (TM2.stepAux (M l) v S) b₂ ∧ Reaches₁ (TM1.step (tr M)) { l := s …
  rsuffices ⟨b, c, r⟩ : ∃ b, _ ∧ Reaches (TM1.step (tr M)) _ _
  -- ⊢ ∃ b₂, TrCfg (TM2.stepAux (M l) v S) b₂ ∧ Reaches₁ (TM1.step (tr M)) { l := s …
  · exact ⟨b, c, TransGen.head' rfl r⟩
    -- 🎉 no goals
  simp only [tr]
  -- ⊢ ∃ b, TrCfg (TM2.stepAux (M l) v S) b ∧ Reaches (TM1.step (tr M)) (TM1.stepAu …
  -- Porting note: `refine'` failed because of implicit lambda, so `induction` is used.
  generalize M l = N
  -- ⊢ ∃ b, TrCfg (TM2.stepAux N v S) b ∧ Reaches (TM1.step (tr M)) (TM1.stepAux (t …
  induction N using stmtStRec generalizing v S L hT with
  | H₁ k s q IH => exact tr_respects_aux M hT s @IH
  | H₂ a _ IH => exact IH _ hT
  | H₃ p q₁ q₂ IH₁ IH₂ =>
    unfold TM2.stepAux trNormal TM1.stepAux
    simp only []
    cases p v <;> [exact IH₂ _ hT; exact IH₁ _ hT]
  | H₄ => exact ⟨_, ⟨_, hT⟩, ReflTransGen.refl⟩
  | H₅ => exact ⟨_, ⟨_, hT⟩, ReflTransGen.refl⟩
#align turing.TM2to1.tr_respects Turing.TM2to1.tr_respects

theorem trCfg_init (k) (L : List (Γ k)) : TrCfg (TM2.init k L) (TM1.init (trInit k L) : Cfg₂₁) := by
  rw [(_ : TM1.init _ = _)]
  · refine' ⟨ListBlank.mk (L.reverse.map fun a ↦ update default k (some a)), fun k' ↦ _⟩
    -- ⊢ ListBlank.map (proj k') (ListBlank.mk (List.map (fun a => update default k ( …
    refine' ListBlank.ext fun i ↦ _
    -- ⊢ ListBlank.nth (ListBlank.map (proj k') (ListBlank.mk (List.map (fun a => upd …
    rw [ListBlank.map_mk, ListBlank.nth_mk, List.getI_eq_iget_get?, List.map_map]
    -- ⊢ Option.iget (List.get? (List.map ((proj k').f ∘ fun a => update default k (s …
    have : ((proj k').f ∘ fun a => update (β := fun k => Option (Γ k)) default k (some a))
      = fun a => (proj k').f (update (β := fun k => Option (Γ k)) default k (some a)) := rfl
    rw [this, List.get?_map, proj, PointedMap.mk_val]
    -- ⊢ Option.iget (Option.map (fun a => update default k (some a) k') (List.get? ( …
    simp only []
    -- ⊢ Option.iget (Option.map (fun a => update default k (some a) k') (List.get? ( …
    by_cases h : k' = k
    -- ⊢ Option.iget (Option.map (fun a => update default k (some a) k') (List.get? ( …
    · subst k'
      -- ⊢ Option.iget (Option.map (fun a => update default k (some a) k) (List.get? (L …
      simp only [Function.update_same]
      -- ⊢ Option.iget (Option.map (fun a => some a) (List.get? (List.reverse L) i)) =  …
      rw [ListBlank.nth_mk, List.getI_eq_iget_get?, ← List.map_reverse, List.get?_map]
      -- 🎉 no goals
    · simp only [Function.update_noteq h]
      -- ⊢ Option.iget (Option.map (fun a => default k') (List.get? (List.reverse L) i) …
      rw [ListBlank.nth_mk, List.getI_eq_iget_get?, List.map, List.reverse_nil]
      -- ⊢ Option.iget (Option.map (fun a => default k') (List.get? (List.reverse L) i) …
      cases L.reverse.get? i <;> rfl
      -- ⊢ Option.iget (Option.map (fun a => default k') none) = Option.iget (List.get? …
                                 -- 🎉 no goals
                                 -- 🎉 no goals
  · rw [trInit, TM1.init]
    -- ⊢ { l := some default, var := default,
    dsimp only
    -- ⊢ { l := some default, var := default, Tape := Tape.mk₁ ((true, (List.headI (L …
    congr <;> cases L.reverse <;> try rfl
    -- ⊢ (List.headI (List.map (fun a => (false, update (fun x => none) k (some a)))  …
              -- ⊢ (List.headI (List.map (fun a => (false, update (fun x => none) k (some a)))  …
              -- ⊢ List.tail (List.map (fun a => (false, update (fun x => none) k (some a))) [] …
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- ⊢ List.tail (List.map (fun a => (false, update (fun x => none) k (some a))) (h …
    simp only [List.map_map, List.tail_cons, List.map]
    -- ⊢ List.map (fun a => (false, update (fun x => none) k (some a))) tail✝ = List. …
    rfl
    -- 🎉 no goals
#align turing.TM2to1.tr_cfg_init Turing.TM2to1.trCfg_init

theorem tr_eval_dom (k) (L : List (Γ k)) :
    (TM1.eval (tr M) (trInit k L)).Dom ↔ (TM2.eval M k L).Dom :=
  Turing.tr_eval_dom (tr_respects M) (trCfg_init k L)
#align turing.TM2to1.tr_eval_dom Turing.TM2to1.tr_eval_dom

theorem tr_eval (k) (L : List (Γ k)) {L₁ L₂} (H₁ : L₁ ∈ TM1.eval (tr M) (trInit k L))
    (H₂ : L₂ ∈ TM2.eval M k L) :
    ∃ (S : ∀ k, List (Γ k)) (L' : ListBlank (∀ k, Option (Γ k))),
      addBottom L' = L₁ ∧
        (∀ k, L'.map (proj k) = ListBlank.mk ((S k).map some).reverse) ∧ S k = L₂ := by
  obtain ⟨c₁, h₁, rfl⟩ := (Part.mem_map_iff _).1 H₁
  -- ⊢ ∃ S L', addBottom L' = Tape.right₀ c₁.Tape ∧ (∀ (k : K), ListBlank.map (proj …
  obtain ⟨c₂, h₂, rfl⟩ := (Part.mem_map_iff _).1 H₂
  -- ⊢ ∃ S L', addBottom L' = Tape.right₀ c₁.Tape ∧ (∀ (k : K), ListBlank.map (proj …
  obtain ⟨_, ⟨L', hT⟩, h₃⟩ := Turing.tr_eval (tr_respects M) (trCfg_init k L) h₂
  -- ⊢ ∃ S L', addBottom L' = Tape.right₀ c₁.Tape ∧ (∀ (k : K), ListBlank.map (proj …
  cases Part.mem_unique h₁ h₃
  -- ⊢ ∃ S L'_1, addBottom L'_1 = Tape.right₀ { l := Option.map normal q✝, var := v …
  exact ⟨_, L', by simp only [Tape.mk'_right₀], hT, rfl⟩
  -- 🎉 no goals
#align turing.TM2to1.tr_eval Turing.TM2to1.tr_eval

/-- The support of a set of TM2 states in the TM2 emulator. -/
noncomputable def trSupp (S : Finset Λ) : Finset Λ'₂₁ :=
  S.biUnion fun l ↦ insert (normal l) (trStmts₁ (M l))
#align turing.TM2to1.tr_supp Turing.TM2to1.trSupp

theorem tr_supports {S} (ss : TM2.Supports M S) : TM1.Supports (tr M) (trSupp M S) :=
  ⟨Finset.mem_biUnion.2 ⟨_, ss.1, Finset.mem_insert.2 <| Or.inl rfl⟩, fun l' h ↦ by
    suffices ∀ (q) (_ : TM2.SupportsStmt S q) (_ : ∀ x ∈ trStmts₁ q, x ∈ trSupp M S),
        TM1.SupportsStmt (trSupp M S) (trNormal q) ∧
        ∀ l' ∈ trStmts₁ q, TM1.SupportsStmt (trSupp M S) (tr M l') by
      rcases Finset.mem_biUnion.1 h with ⟨l, lS, h⟩
      have :=
        this _ (ss.2 l lS) fun x hx ↦ Finset.mem_biUnion.2 ⟨_, lS, Finset.mem_insert_of_mem hx⟩
      rcases Finset.mem_insert.1 h with (rfl | h) <;> [exact this.1; exact this.2 _ h]
    clear h l'
    -- ⊢ ∀ (q : Stmt₂), TM2.SupportsStmt S q → (∀ (x : Λ'), x ∈ trStmts₁ q → x ∈ trSu …
    refine' stmtStRec _ _ _ _ _
    · intro _ s _ IH ss' sub -- stack op
      -- ⊢ TM1.SupportsStmt (trSupp M S) (trNormal (stRun s q✝)) ∧ ∀ (l' : Λ'), l' ∈ tr …
      rw [TM2to1.supports_run] at ss'
      -- ⊢ TM1.SupportsStmt (trSupp M S) (trNormal (stRun s q✝)) ∧ ∀ (l' : Λ'), l' ∈ tr …
      simp only [TM2to1.trStmts₁_run, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        at sub
      have hgo := sub _ (Or.inl <| Or.inl rfl)
      -- ⊢ TM1.SupportsStmt (trSupp M S) (trNormal (stRun s q✝)) ∧ ∀ (l' : Λ'), l' ∈ tr …
      have hret := sub _ (Or.inl <| Or.inr rfl)
      -- ⊢ TM1.SupportsStmt (trSupp M S) (trNormal (stRun s q✝)) ∧ ∀ (l' : Λ'), l' ∈ tr …
      cases' IH ss' fun x hx ↦ sub x <| Or.inr hx with IH₁ IH₂
      -- ⊢ TM1.SupportsStmt (trSupp M S) (trNormal (stRun s q✝)) ∧ ∀ (l' : Λ'), l' ∈ tr …
      refine' ⟨by simp only [trNormal_run, TM1.SupportsStmt]; intros; exact hgo, fun l h ↦ _⟩
      -- ⊢ TM1.SupportsStmt (trSupp M S) (tr M l)
      rw [trStmts₁_run] at h
      -- ⊢ TM1.SupportsStmt (trSupp M S) (tr M l)
      simp only [TM2to1.trStmts₁_run, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        at h
      rcases h with (⟨rfl | rfl⟩ | h)
      · cases s
        · exact ⟨fun _ _ ↦ hret, fun _ _ ↦ hgo⟩
          -- 🎉 no goals
        · exact ⟨fun _ _ ↦ hret, fun _ _ ↦ hgo⟩
          -- 🎉 no goals
        · exact ⟨⟨fun _ _ ↦ hret, fun _ _ ↦ hret⟩, fun _ _ ↦ hgo⟩
          -- 🎉 no goals
      · unfold TM1.SupportsStmt TM2to1.tr
        -- ⊢ match
        exact ⟨IH₁, fun _ _ ↦ hret⟩
        -- 🎉 no goals
      · exact IH₂ _ h
        -- 🎉 no goals
    · intro _ _ IH ss' sub -- load
      -- ⊢ TM1.SupportsStmt (trSupp M S) (trNormal (TM2.Stmt.load a✝ q✝)) ∧ ∀ (l' : Λ') …
      unfold TM2to1.trStmts₁ at ss' sub ⊢
      -- ⊢ TM1.SupportsStmt (trSupp M S) (trNormal (TM2.Stmt.load a✝ q✝)) ∧ ∀ (l' : Λ') …
      exact IH ss' sub
      -- 🎉 no goals
    · intro _ _ _ IH₁ IH₂ ss' sub -- branch
      -- ⊢ TM1.SupportsStmt (trSupp M S) (trNormal (TM2.Stmt.branch p✝ q₁✝ q₂✝)) ∧ ∀ (l …
      unfold TM2to1.trStmts₁ at sub
      -- ⊢ TM1.SupportsStmt (trSupp M S) (trNormal (TM2.Stmt.branch p✝ q₁✝ q₂✝)) ∧ ∀ (l …
      cases' IH₁ ss'.1 fun x hx ↦ sub x <| Finset.mem_union_left _ hx with IH₁₁ IH₁₂
      -- ⊢ TM1.SupportsStmt (trSupp M S) (trNormal (TM2.Stmt.branch p✝ q₁✝ q₂✝)) ∧ ∀ (l …
      cases' IH₂ ss'.2 fun x hx ↦ sub x <| Finset.mem_union_right _ hx with IH₂₁ IH₂₂
      -- ⊢ TM1.SupportsStmt (trSupp M S) (trNormal (TM2.Stmt.branch p✝ q₁✝ q₂✝)) ∧ ∀ (l …
      refine' ⟨⟨IH₁₁, IH₂₁⟩, fun l h ↦ _⟩
      -- ⊢ TM1.SupportsStmt (trSupp M S) (tr M l)
      rw [trStmts₁] at h
      -- ⊢ TM1.SupportsStmt (trSupp M S) (tr M l)
      rcases Finset.mem_union.1 h with (h | h) <;> [exact IH₁₂ _ h; exact IH₂₂ _ h]
      -- 🎉 no goals
    · intro _ ss' _ -- goto
      -- ⊢ TM1.SupportsStmt (trSupp M S) (trNormal (TM2.Stmt.goto l✝)) ∧ ∀ (l' : Λ'), l …
      simp only [trStmts₁, Finset.not_mem_empty]; refine' ⟨_, fun _ ↦ False.elim⟩
      -- ⊢ TM1.SupportsStmt (trSupp M S) (trNormal (TM2.Stmt.goto l✝)) ∧ ∀ (l' : Λ'), F …
                                                  -- ⊢ TM1.SupportsStmt (trSupp M S) (trNormal (TM2.Stmt.goto l✝))
      exact fun _ v ↦ Finset.mem_biUnion.2 ⟨_, ss' v, Finset.mem_insert_self _ _⟩
      -- 🎉 no goals
    · intro _ _ -- halt
      -- ⊢ TM1.SupportsStmt (trSupp M S) (trNormal TM2.Stmt.halt) ∧ ∀ (l' : Λ'), l' ∈ t …
      simp only [trStmts₁, Finset.not_mem_empty]
      -- ⊢ TM1.SupportsStmt (trSupp M S) (trNormal TM2.Stmt.halt) ∧ ∀ (l' : Λ'), False  …
      exact ⟨trivial, fun _ ↦ False.elim⟩⟩
      -- 🎉 no goals
#align turing.TM2to1.tr_supports Turing.TM2to1.tr_supports

end

end TM2to1

end Turing
