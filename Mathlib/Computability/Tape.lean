/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Vector.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Basic
import Mathlib.Tactic.ApplyFun
import Mathlib.Data.List.GetD

/-!
# Turing machine tapes

This file defines the notion of a Turing machine tape, and the operations on it. A tape is a
bidirectional infinite sequence of cells, each of which stores an element of a given alphabet `Γ`.
All but finitely many of the cells are required to hold the blank symbol `default : Γ`.

## Main definitions

* `ListBlank Γ` is the type of one-directional tapes with alphabet `Γ`. Implemented as a quotient
  of `List Γ` by extension by blanks at the end.
* `Tape Γ` is the type of Turing machine tapes with alphabet `Γ`. Implemented as two
  `ListBlank Γ` instances, one for each direction, as well as a head symbol.

-/

assert_not_exists MonoidWithZero

open Function (iterate_succ iterate_succ_apply iterate_zero_apply)

namespace Turing

section ListBlank

/-- The `BlankExtends` partial order holds of `l₁` and `l₂` if `l₂` is obtained by adding
blanks (`default : Γ`) to the end of `l₁`. -/
def BlankExtends {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) : Prop :=
  ∃ n, l₂ = l₁ ++ List.replicate n default

@[refl]
theorem BlankExtends.refl {Γ} [Inhabited Γ] (l : List Γ) : BlankExtends l l :=
  ⟨0, by simp⟩

@[trans]
theorem BlankExtends.trans {Γ} [Inhabited Γ] {l₁ l₂ l₃ : List Γ} :
    BlankExtends l₁ l₂ → BlankExtends l₂ l₃ → BlankExtends l₁ l₃ := by
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩
  exact ⟨i + j, by simp⟩

theorem BlankExtends.below_of_le {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} :
    BlankExtends l l₁ → BlankExtends l l₂ → l₁.length ≤ l₂.length → BlankExtends l₁ l₂ := by
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩ h; use j - i
  simp only [List.length_append, Nat.add_le_add_iff_left, List.length_replicate] at h
  simp only [← List.replicate_add, Nat.add_sub_cancel' h, List.append_assoc]

/-- Any two extensions by blank `l₁,l₂` of `l` have a common join (which can be taken to be the
longer of `l₁` and `l₂`). -/
def BlankExtends.above {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} (h₁ : BlankExtends l l₁)
    (h₂ : BlankExtends l l₂) : { l' // BlankExtends l₁ l' ∧ BlankExtends l₂ l' } :=
  if h : l₁.length ≤ l₂.length then ⟨l₂, h₁.below_of_le h₂ h, BlankExtends.refl _⟩
  else ⟨l₁, BlankExtends.refl _, h₂.below_of_le h₁ (le_of_not_ge h)⟩

theorem BlankExtends.above_of_le {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} :
    BlankExtends l₁ l → BlankExtends l₂ l → l₁.length ≤ l₂.length → BlankExtends l₁ l₂ := by
  rintro ⟨i, rfl⟩ ⟨j, e⟩ h; use i - j
  refine List.append_cancel_right (e.symm.trans ?_)
  rw [List.append_assoc, ← List.replicate_add, Nat.sub_add_cancel]
  apply_fun List.length at e
  simp only [List.length_append, List.length_replicate] at e
  rwa [← Nat.add_le_add_iff_left, e, Nat.add_le_add_iff_right]

/-- `BlankRel` is the symmetric closure of `BlankExtends`, turning it into an equivalence
relation. Two lists are related by `BlankRel` if one extends the other by blanks. -/
def BlankRel {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) : Prop :=
  BlankExtends l₁ l₂ ∨ BlankExtends l₂ l₁

@[refl]
theorem BlankRel.refl {Γ} [Inhabited Γ] (l : List Γ) : BlankRel l l :=
  Or.inl (BlankExtends.refl _)

@[symm]
theorem BlankRel.symm {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} : BlankRel l₁ l₂ → BlankRel l₂ l₁ :=
  Or.symm

@[trans]
theorem BlankRel.trans {Γ} [Inhabited Γ] {l₁ l₂ l₃ : List Γ} :
    BlankRel l₁ l₂ → BlankRel l₂ l₃ → BlankRel l₁ l₃ := by
  rintro (h₁ | h₁) (h₂ | h₂)
  · exact Or.inl (h₁.trans h₂)
  · rcases le_total l₁.length l₃.length with h | h
    · exact Or.inl (h₁.above_of_le h₂ h)
    · exact Or.inr (h₂.above_of_le h₁ h)
  · rcases le_total l₁.length l₃.length with h | h
    · exact Or.inl (h₁.below_of_le h₂ h)
    · exact Or.inr (h₂.below_of_le h₁ h)
  · exact Or.inr (h₂.trans h₁)

/-- Given two `BlankRel` lists, there exists (constructively) a common join. -/
def BlankRel.above {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} (h : BlankRel l₁ l₂) :
    { l // BlankExtends l₁ l ∧ BlankExtends l₂ l } := by
  refine
    if hl : l₁.length ≤ l₂.length then ⟨l₂, Or.elim h id fun h' ↦ ?_, BlankExtends.refl _⟩
    else ⟨l₁, BlankExtends.refl _, Or.elim h (fun h' ↦ ?_) id⟩
  · exact (BlankExtends.refl _).above_of_le h' hl
  · exact (BlankExtends.refl _).above_of_le h' (le_of_not_ge hl)

/-- Given two `BlankRel` lists, there exists (constructively) a common meet. -/
def BlankRel.below {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} (h : BlankRel l₁ l₂) :
    { l // BlankExtends l l₁ ∧ BlankExtends l l₂ } := by
  refine
    if hl : l₁.length ≤ l₂.length then ⟨l₁, BlankExtends.refl _, Or.elim h id fun h' ↦ ?_⟩
    else ⟨l₂, Or.elim h (fun h' ↦ ?_) id, BlankExtends.refl _⟩
  · exact (BlankExtends.refl _).above_of_le h' hl
  · exact (BlankExtends.refl _).above_of_le h' (le_of_not_ge hl)

theorem BlankRel.equivalence (Γ) [Inhabited Γ] : Equivalence (@BlankRel Γ _) :=
  ⟨BlankRel.refl, @BlankRel.symm _ _, @BlankRel.trans _ _⟩

/-- Construct a setoid instance for `BlankRel`. -/
def BlankRel.setoid (Γ) [Inhabited Γ] : Setoid (List Γ) :=
  ⟨_, BlankRel.equivalence _⟩

/-- A `ListBlank Γ` is a quotient of `List Γ` by extension by blanks at the end. This is used to
represent half-tapes of a Turing machine, so that we can pretend that the list continues
infinitely with blanks. -/
def ListBlank (Γ) [Inhabited Γ] :=
  Quotient (BlankRel.setoid Γ)

instance ListBlank.inhabited {Γ} [Inhabited Γ] : Inhabited (ListBlank Γ) :=
  ⟨Quotient.mk'' []⟩

instance ListBlank.hasEmptyc {Γ} [Inhabited Γ] : EmptyCollection (ListBlank Γ) :=
  ⟨Quotient.mk'' []⟩

/-- A modified version of `Quotient.liftOn'` specialized for `ListBlank`, with the stronger
precondition `BlankExtends` instead of `BlankRel`. -/
protected abbrev ListBlank.liftOn {Γ} [Inhabited Γ] {α} (l : ListBlank Γ) (f : List Γ → α)
    (H : ∀ a b, BlankExtends a b → f a = f b) : α :=
  l.liftOn' f <| by rintro a b (h | h) <;> [exact H _ _ h; exact (H _ _ h).symm]

/-- The quotient map turning a `List` into a `ListBlank`. -/
def ListBlank.mk {Γ} [Inhabited Γ] : List Γ → ListBlank Γ :=
  Quotient.mk''

@[elab_as_elim]
protected theorem ListBlank.induction_on {Γ} [Inhabited Γ] {p : ListBlank Γ → Prop}
    (q : ListBlank Γ) (h : ∀ a, p (ListBlank.mk a)) : p q :=
  Quotient.inductionOn' q h

/-- The head of a `ListBlank` is well defined. -/
def ListBlank.head {Γ} [Inhabited Γ] (l : ListBlank Γ) : Γ := by
  apply l.liftOn List.headI
  rintro a _ ⟨i, rfl⟩
  cases a
  · cases i <;> rfl
  rfl

@[simp]
theorem ListBlank.head_mk {Γ} [Inhabited Γ] (l : List Γ) :
    ListBlank.head (ListBlank.mk l) = l.headI :=
  rfl

/-- The tail of a `ListBlank` is well defined (up to the tail of blanks). -/
def ListBlank.tail {Γ} [Inhabited Γ] (l : ListBlank Γ) : ListBlank Γ := by
  apply l.liftOn (fun l ↦ ListBlank.mk l.tail)
  rintro a _ ⟨i, rfl⟩
  refine Quotient.sound' (Or.inl ?_)
  cases a
  · rcases i with - | i <;> [exact ⟨0, rfl⟩; exact ⟨i, rfl⟩]
  exact ⟨i, rfl⟩

@[simp]
theorem ListBlank.tail_mk {Γ} [Inhabited Γ] (l : List Γ) :
    ListBlank.tail (ListBlank.mk l) = ListBlank.mk l.tail :=
  rfl

/-- We can cons an element onto a `ListBlank`. -/
def ListBlank.cons {Γ} [Inhabited Γ] (a : Γ) (l : ListBlank Γ) : ListBlank Γ := by
  apply l.liftOn (fun l ↦ ListBlank.mk (List.cons a l))
  rintro _ _ ⟨i, rfl⟩
  exact Quotient.sound' (Or.inl ⟨i, rfl⟩)

@[simp]
theorem ListBlank.cons_mk {Γ} [Inhabited Γ] (a : Γ) (l : List Γ) :
    ListBlank.cons a (ListBlank.mk l) = ListBlank.mk (a :: l) :=
  rfl

@[simp]
theorem ListBlank.head_cons {Γ} [Inhabited Γ] (a : Γ) : ∀ l : ListBlank Γ, (l.cons a).head = a :=
  Quotient.ind' fun _ ↦ rfl

@[simp]
theorem ListBlank.tail_cons {Γ} [Inhabited Γ] (a : Γ) : ∀ l : ListBlank Γ, (l.cons a).tail = l :=
  Quotient.ind' fun _ ↦ rfl

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `List` where
this only holds for nonempty lists. -/
@[simp]
theorem ListBlank.cons_head_tail {Γ} [Inhabited Γ] : ∀ l : ListBlank Γ, l.tail.cons l.head = l := by
  apply Quotient.ind'
  refine fun l ↦ Quotient.sound' (Or.inr ?_)
  cases l
  · exact ⟨1, rfl⟩
  · rfl

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `List` where
this only holds for nonempty lists. -/
theorem ListBlank.exists_cons {Γ} [Inhabited Γ] (l : ListBlank Γ) :
    ∃ a l', l = ListBlank.cons a l' :=
  ⟨_, _, (ListBlank.cons_head_tail _).symm⟩

/-- The n-th element of a `ListBlank` is well defined for all `n : ℕ`, unlike in a `List`. -/
def ListBlank.nth {Γ} [Inhabited Γ] (l : ListBlank Γ) (n : ℕ) : Γ := by
  apply l.liftOn (fun l ↦ List.getI l n)
  rintro l _ ⟨i, rfl⟩
  rcases lt_or_ge n _ with h | h
  · rw [List.getI_append _ _ _ h]
  rw [List.getI_eq_default _ h]
  rcases le_or_gt _ n with h₂ | h₂
  · rw [List.getI_eq_default _ h₂]
  rw [List.getI_eq_getElem _ h₂, List.getElem_append_right h, List.getElem_replicate]

@[simp]
theorem ListBlank.nth_mk {Γ} [Inhabited Γ] (l : List Γ) (n : ℕ) :
    (ListBlank.mk l).nth n = l.getI n :=
  rfl

@[simp]
theorem ListBlank.nth_zero {Γ} [Inhabited Γ] (l : ListBlank Γ) : l.nth 0 = l.head := by
  conv => lhs; rw [← ListBlank.cons_head_tail l]
  exact Quotient.inductionOn' l.tail fun l ↦ rfl

@[simp]
theorem ListBlank.nth_succ {Γ} [Inhabited Γ] (l : ListBlank Γ) (n : ℕ) :
    l.nth (n + 1) = l.tail.nth n := by
  conv => lhs; rw [← ListBlank.cons_head_tail l]
  exact Quotient.inductionOn' l.tail fun l ↦ rfl

@[ext]
theorem ListBlank.ext {Γ} [i : Inhabited Γ] {L₁ L₂ : ListBlank Γ} :
    (∀ i, L₁.nth i = L₂.nth i) → L₁ = L₂ := by
  refine ListBlank.induction_on L₁ fun l₁ ↦ ListBlank.induction_on L₂ fun l₂ H ↦ ?_
  wlog h : l₁.length ≤ l₂.length
  · cases le_total l₁.length l₂.length <;> [skip; symm] <;> apply this <;> try assumption
    intro
    rw [H]
  refine Quotient.sound' (Or.inl ⟨l₂.length - l₁.length, ?_⟩)
  refine List.ext_getElem ?_ fun i h h₂ ↦ Eq.symm ?_
  · simp only [Nat.add_sub_cancel' h, List.length_append, List.length_replicate]
  simp only [ListBlank.nth_mk] at H
  rcases lt_or_ge i l₁.length with h' | h'
  · simp [h', List.getElem_append h₂, ← List.getI_eq_getElem _ h, ← List.getI_eq_getElem _ h', H]
  · rw [List.getElem_append_right h', List.getElem_replicate,
      ← List.getI_eq_default _ h', H, List.getI_eq_getElem _ h]

/-- Apply a function to a value stored at the nth position of the list. -/
@[simp]
def ListBlank.modifyNth {Γ} [Inhabited Γ] (f : Γ → Γ) : ℕ → ListBlank Γ → ListBlank Γ
  | 0, L => L.tail.cons (f L.head)
  | n + 1, L => (L.tail.modifyNth f n).cons L.head

theorem ListBlank.nth_modifyNth {Γ} [Inhabited Γ] (f : Γ → Γ) (n i) (L : ListBlank Γ) :
    (L.modifyNth f n).nth i = if i = n then f (L.nth i) else L.nth i := by
  induction n generalizing i L with
  | zero =>
    cases i <;> simp only [ListBlank.nth_zero, if_true, ListBlank.head_cons, ListBlank.modifyNth,
      ListBlank.nth_succ, if_false, ListBlank.tail_cons, reduceCtorEq]
  | succ n IH =>
    cases i
    · rw [if_neg (Nat.succ_ne_zero _).symm]
      simp only [ListBlank.nth_zero, ListBlank.head_cons, ListBlank.modifyNth]
    · simp only [IH, ListBlank.modifyNth, ListBlank.nth_succ, ListBlank.tail_cons, Nat.succ.injEq]

/-- A pointed map of `Inhabited` types is a map that sends one default value to the other. -/
structure PointedMap.{u, v} (Γ : Type u) (Γ' : Type v) [Inhabited Γ] [Inhabited Γ'] :
    Type max u v where
  /-- The map underlying this instance. -/
  f : Γ → Γ'
  map_pt' : f default = default

instance {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] : Inhabited (PointedMap Γ Γ') :=
  ⟨⟨default, rfl⟩⟩

instance {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] : CoeFun (PointedMap Γ Γ') fun _ ↦ Γ → Γ' :=
  ⟨PointedMap.f⟩

-- @[simp] -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10685): dsimp can prove this
theorem PointedMap.mk_val {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : Γ → Γ') (pt) :
    (PointedMap.mk f pt : Γ → Γ') = f :=
  rfl

@[simp]
theorem PointedMap.map_pt {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') :
    f default = default :=
  PointedMap.map_pt' _

@[simp]
theorem PointedMap.headI_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : List Γ) : (l.map f).headI = f l.headI := by
  cases l <;> [exact (PointedMap.map_pt f).symm; rfl]

/-- The `map` function on lists is well defined on `ListBlank`s provided that the map is
pointed. -/
def ListBlank.map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : ListBlank Γ) :
    ListBlank Γ' := by
  apply l.liftOn (fun l ↦ ListBlank.mk (List.map f l))
  rintro l _ ⟨i, rfl⟩; refine Quotient.sound' (Or.inl ⟨i, ?_⟩)
  simp only [PointedMap.map_pt, List.map_append, List.map_replicate]

@[simp]
theorem ListBlank.map_mk {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : List Γ) :
    (ListBlank.mk l).map f = ListBlank.mk (l.map f) :=
  rfl

@[simp]
theorem ListBlank.head_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) : (l.map f).head = f l.head := by
  conv => lhs; rw [← ListBlank.cons_head_tail l]
  exact Quotient.inductionOn' l fun a ↦ rfl

@[simp]
theorem ListBlank.tail_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) : (l.map f).tail = l.tail.map f := by
  conv => lhs; rw [← ListBlank.cons_head_tail l]
  exact Quotient.inductionOn' l fun a ↦ rfl

@[simp]
theorem ListBlank.map_cons {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) (a : Γ) : (l.cons a).map f = (l.map f).cons (f a) := by
  refine (ListBlank.cons_head_tail _).symm.trans ?_
  simp only [ListBlank.head_map, ListBlank.head_cons, ListBlank.tail_map, ListBlank.tail_cons]

@[simp]
theorem ListBlank.nth_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) (n : ℕ) : (l.map f).nth n = f (l.nth n) := by
  refine l.inductionOn fun l ↦ ?_
  -- Porting note: Added `suffices` to get `simp` to work.
  suffices ((mk l).map f).nth n = f ((mk l).nth n) by exact this
  simp only [ListBlank.map_mk, ListBlank.nth_mk, ← List.getD_default_eq_getI]
  rw [← List.getD_map _ _ f]
  simp

/-- The `i`-th projection as a pointed map. -/
def proj {ι : Type*} {Γ : ι → Type*} [∀ i, Inhabited (Γ i)] (i : ι) :
    PointedMap (∀ i, Γ i) (Γ i) :=
  ⟨fun a ↦ a i, rfl⟩

theorem proj_map_nth {ι : Type*} {Γ : ι → Type*} [∀ i, Inhabited (Γ i)] (i : ι) (L n) :
    (ListBlank.map (@proj ι Γ _ i) L).nth n = L.nth n i := by
  rw [ListBlank.nth_map]; rfl

theorem ListBlank.map_modifyNth {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (F : PointedMap Γ Γ')
    (f : Γ → Γ) (f' : Γ' → Γ') (H : ∀ x, F (f x) = f' (F x)) (n) (L : ListBlank Γ) :
    (L.modifyNth f n).map F = (L.map F).modifyNth f' n := by
  induction n generalizing L <;>
    simp only [*, ListBlank.head_map, ListBlank.modifyNth, ListBlank.map_cons, ListBlank.tail_map]

/-- Append a list on the left side of a `ListBlank`. -/
@[simp]
def ListBlank.append {Γ} [Inhabited Γ] : List Γ → ListBlank Γ → ListBlank Γ
  | [], L => L
  | a :: l, L => ListBlank.cons a (ListBlank.append l L)

@[simp]
theorem ListBlank.append_mk {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) :
    ListBlank.append l₁ (ListBlank.mk l₂) = ListBlank.mk (l₁ ++ l₂) := by
  induction l₁ <;>
    simp only [*, ListBlank.append, List.nil_append, List.cons_append, ListBlank.cons_mk]

theorem ListBlank.append_assoc {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) (l₃ : ListBlank Γ) :
    ListBlank.append (l₁ ++ l₂) l₃ = ListBlank.append l₁ (ListBlank.append l₂ l₃) := by
  refine l₃.inductionOn fun l ↦ ?_
  -- Porting note: Added `suffices` to get `simp` to work.
  suffices append (l₁ ++ l₂) (mk l) = append l₁ (append l₂ (mk l)) by exact this
  simp only [ListBlank.append_mk, List.append_assoc]

/-- The `flatMap` function on lists is well defined on `ListBlank`s provided that the default
element is sent to a sequence of default elements. -/
def ListBlank.flatMap {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (l : ListBlank Γ) (f : Γ → List Γ')
    (hf : ∃ n, f default = List.replicate n default) : ListBlank Γ' := by
  apply l.liftOn (fun l ↦ ListBlank.mk (l.flatMap f))
  rintro l _ ⟨i, rfl⟩; obtain ⟨n, e⟩ := hf; refine Quotient.sound' (Or.inl ⟨i * n, ?_⟩)
  rw [List.flatMap_append, mul_comm]; congr
  induction i with
  | zero => rfl
  | succ i IH =>
    simp only [IH, e, List.replicate_add, Nat.mul_succ, add_comm, List.replicate_succ,
      List.flatMap_cons]

@[simp]
theorem ListBlank.flatMap_mk
    {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (l : List Γ) (f : Γ → List Γ') (hf) :
    (ListBlank.mk l).flatMap f hf = ListBlank.mk (l.flatMap f) :=
  rfl

@[simp]
theorem ListBlank.cons_flatMap {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (a : Γ) (l : ListBlank Γ)
    (f : Γ → List Γ') (hf) : (l.cons a).flatMap f hf = (l.flatMap f hf).append (f a) := by
  refine l.inductionOn fun l ↦ ?_
  -- Porting note: Added `suffices` to get `simp` to work.
  suffices ((mk l).cons a).flatMap f hf = ((mk l).flatMap f hf).append (f a) by exact this
  simp only [ListBlank.append_mk, ListBlank.flatMap_mk, ListBlank.cons_mk, List.flatMap_cons]

end ListBlank

section Tape

/-- The tape of a Turing machine is composed of a head element (which we imagine to be the
current position of the head), together with two `ListBlank`s denoting the portions of the tape
going off to the left and right. When the Turing machine moves right, an element is pulled from the
right side and becomes the new head, while the head element is `cons`ed onto the left side. -/
structure Tape (Γ : Type*) [Inhabited Γ] where
  /-- The current position of the head. -/
  head : Γ
  /-- The portion of the tape going off to the left. -/
  left : ListBlank Γ
  /-- The portion of the tape going off to the right. -/
  right : ListBlank Γ

instance Tape.inhabited {Γ} [Inhabited Γ] : Inhabited (Tape Γ) :=
  ⟨by constructor <;> apply default⟩

/-- A direction for the Turing machine `move` command, either
  left or right. -/
inductive Dir
  | left
  | right
  deriving DecidableEq, Inhabited

/-- The "inclusive" left side of the tape, including both `left` and `head`. -/
def Tape.left₀ {Γ} [Inhabited Γ] (T : Tape Γ) : ListBlank Γ :=
  T.left.cons T.head

/-- The "inclusive" right side of the tape, including both `right` and `head`. -/
def Tape.right₀ {Γ} [Inhabited Γ] (T : Tape Γ) : ListBlank Γ :=
  T.right.cons T.head

/-- Move the tape in response to a motion of the Turing machine. Note that `T.move Dir.left` makes
`T.left` smaller; the Turing machine is moving left and the tape is moving right. -/
def Tape.move {Γ} [Inhabited Γ] : Dir → Tape Γ → Tape Γ
  | Dir.left, ⟨a, L, R⟩ => ⟨L.head, L.tail, R.cons a⟩
  | Dir.right, ⟨a, L, R⟩ => ⟨R.head, L.cons a, R.tail⟩

@[simp]
theorem Tape.move_left_right {Γ} [Inhabited Γ] (T : Tape Γ) :
    (T.move Dir.left).move Dir.right = T := by
  cases T; simp [Tape.move]

@[simp]
theorem Tape.move_right_left {Γ} [Inhabited Γ] (T : Tape Γ) :
    (T.move Dir.right).move Dir.left = T := by
  cases T; simp [Tape.move]

/-- Construct a tape from a left side and an inclusive right side. -/
def Tape.mk' {Γ} [Inhabited Γ] (L R : ListBlank Γ) : Tape Γ :=
  ⟨R.head, L, R.tail⟩

@[simp]
theorem Tape.mk'_left {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).left = L :=
  rfl

@[simp]
theorem Tape.mk'_head {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).head = R.head :=
  rfl

@[simp]
theorem Tape.mk'_right {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).right = R.tail :=
  rfl

@[simp]
theorem Tape.mk'_right₀ {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).right₀ = R :=
  ListBlank.cons_head_tail _

@[simp]
theorem Tape.mk'_left_right₀ {Γ} [Inhabited Γ] (T : Tape Γ) : Tape.mk' T.left T.right₀ = T := by
  cases T
  simp only [Tape.right₀, Tape.mk', ListBlank.head_cons, ListBlank.tail_cons]

theorem Tape.exists_mk' {Γ} [Inhabited Γ] (T : Tape Γ) : ∃ L R, T = Tape.mk' L R :=
  ⟨_, _, (Tape.mk'_left_right₀ _).symm⟩

@[simp]
theorem Tape.move_left_mk' {Γ} [Inhabited Γ] (L R : ListBlank Γ) :
    (Tape.mk' L R).move Dir.left = Tape.mk' L.tail (R.cons L.head) := by
  simp only [Tape.move, Tape.mk', ListBlank.head_cons, ListBlank.cons_head_tail,
    ListBlank.tail_cons]

@[simp]
theorem Tape.move_right_mk' {Γ} [Inhabited Γ] (L R : ListBlank Γ) :
    (Tape.mk' L R).move Dir.right = Tape.mk' (L.cons R.head) R.tail := by
  simp only [Tape.move, Tape.mk']

/-- Construct a tape from a left side and an inclusive right side. -/
def Tape.mk₂ {Γ} [Inhabited Γ] (L R : List Γ) : Tape Γ :=
  Tape.mk' (ListBlank.mk L) (ListBlank.mk R)

/-- Construct a tape from a list, with the head of the list at the TM head and the rest going
to the right. -/
def Tape.mk₁ {Γ} [Inhabited Γ] (l : List Γ) : Tape Γ :=
  Tape.mk₂ [] l

/-- The `nth` function of a tape is integer-valued, with index `0` being the head, negative indexes
on the left and positive indexes on the right. (Picture a number line.) -/
def Tape.nth {Γ} [Inhabited Γ] (T : Tape Γ) : ℤ → Γ
  | 0 => T.head
  | (n + 1 : ℕ) => T.right.nth n
  | -(n + 1 : ℕ) => T.left.nth n

@[simp]
theorem Tape.nth_zero {Γ} [Inhabited Γ] (T : Tape Γ) : T.nth 0 = T.1 :=
  rfl

theorem Tape.right₀_nth {Γ} [Inhabited Γ] (T : Tape Γ) (n : ℕ) : T.right₀.nth n = T.nth n := by
  cases n <;> simp only [Tape.nth, Tape.right₀, ListBlank.nth_zero,
    ListBlank.nth_succ, ListBlank.head_cons, ListBlank.tail_cons]

@[simp]
theorem Tape.mk'_nth_nat {Γ} [Inhabited Γ] (L R : ListBlank Γ) (n : ℕ) :
    (Tape.mk' L R).nth n = R.nth n := by
  rw [← Tape.right₀_nth, Tape.mk'_right₀]

@[simp]
theorem Tape.move_left_nth {Γ} [Inhabited Γ] :
    ∀ (T : Tape Γ) (i : ℤ), (T.move Dir.left).nth i = T.nth (i - 1)
  | ⟨_, _, _⟩, -(_ + 1 : ℕ) => (ListBlank.nth_succ _ _).symm
  | ⟨_, _, _⟩, 0 => (ListBlank.nth_zero _).symm
  | ⟨_, _, _⟩, 1 => (ListBlank.nth_zero _).trans (ListBlank.head_cons _ _)
  | ⟨a, L, R⟩, (n + 1 : ℕ) + 1 => by
    rw [add_sub_cancel_right]
    change (R.cons a).nth (n + 1) = R.nth n
    rw [ListBlank.nth_succ, ListBlank.tail_cons]

@[simp]
theorem Tape.move_right_nth {Γ} [Inhabited Γ] (T : Tape Γ) (i : ℤ) :
    (T.move Dir.right).nth i = T.nth (i + 1) := by
  conv => rhs; rw [← T.move_right_left]
  rw [Tape.move_left_nth, add_sub_cancel_right]

@[simp]
theorem Tape.move_right_n_head {Γ} [Inhabited Γ] (T : Tape Γ) (i : ℕ) :
    ((Tape.move Dir.right)^[i] T).head = T.nth i := by
  induction i generalizing T
  · rfl
  · simp only [*, Tape.move_right_nth, Int.natCast_succ, iterate_succ, Function.comp_apply]

/-- Replace the current value of the head on the tape. -/
def Tape.write {Γ} [Inhabited Γ] (b : Γ) (T : Tape Γ) : Tape Γ :=
  { T with head := b }

@[simp]
theorem Tape.write_self {Γ} [Inhabited Γ] : ∀ T : Tape Γ, T.write T.1 = T := by
  rintro ⟨⟩; rfl

@[simp]
theorem Tape.write_nth {Γ} [Inhabited Γ] (b : Γ) :
    ∀ (T : Tape Γ) {i : ℤ}, (T.write b).nth i = if i = 0 then b else T.nth i
  | _, 0 => rfl
  | _, (_ + 1 : ℕ) => rfl
  | _, -(_ + 1 : ℕ) => rfl

@[simp]
theorem Tape.write_mk' {Γ} [Inhabited Γ] (a b : Γ) (L R : ListBlank Γ) :
    (Tape.mk' L (R.cons a)).write b = Tape.mk' L (R.cons b) := by
  simp only [Tape.write, Tape.mk', ListBlank.head_cons, ListBlank.tail_cons]

/-- Apply a pointed map to a tape to change the alphabet. -/
def Tape.map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (T : Tape Γ) : Tape Γ' :=
  ⟨f T.1, T.2.map f, T.3.map f⟩

@[simp]
theorem Tape.map_fst {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') :
    ∀ T : Tape Γ, (T.map f).1 = f T.1 := by
  rintro ⟨⟩; rfl

@[simp]
theorem Tape.map_write {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (b : Γ) :
    ∀ T : Tape Γ, (T.write b).map f = (T.map f).write (f b) := by
  rintro ⟨⟩; rfl

@[simp]
theorem Tape.write_move_right_n {Γ} [Inhabited Γ] (f : Γ → Γ) (L R : ListBlank Γ) (n : ℕ) :
    ((Tape.move Dir.right)^[n] (Tape.mk' L R)).write (f (R.nth n)) =
      (Tape.move Dir.right)^[n] (Tape.mk' L (R.modifyNth f n)) := by
  induction n generalizing L R with
  | zero =>
    simp only [ListBlank.nth_zero, ListBlank.modifyNth, iterate_zero_apply]
    rw [← Tape.write_mk', ListBlank.cons_head_tail]
  | succ n IH =>
    simp only [ListBlank.head_cons, ListBlank.nth_succ, ListBlank.modifyNth, Tape.move_right_mk',
      ListBlank.tail_cons, iterate_succ_apply, IH]

theorem Tape.map_move {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (T : Tape Γ) (d) :
    (T.move d).map f = (T.map f).move d := by
  cases T
  cases d <;> simp only [Tape.move, Tape.map, ListBlank.head_map,
    ListBlank.map_cons, ListBlank.tail_map]

theorem Tape.map_mk' {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (L R : ListBlank Γ) :
    (Tape.mk' L R).map f = Tape.mk' (L.map f) (R.map f) := by
  simp only [Tape.mk', Tape.map, ListBlank.head_map,
    ListBlank.tail_map]

theorem Tape.map_mk₂ {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (L R : List Γ) :
    (Tape.mk₂ L R).map f = Tape.mk₂ (L.map f) (R.map f) := by
  simp only [Tape.mk₂, Tape.map_mk', ListBlank.map_mk]

theorem Tape.map_mk₁ {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : List Γ) :
    (Tape.mk₁ l).map f = Tape.mk₁ (l.map f) :=
  Tape.map_mk₂ _ _ _

end Tape

end Turing
