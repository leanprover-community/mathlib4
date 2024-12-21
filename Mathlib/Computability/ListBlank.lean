/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Mario Carneiro
-/
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Vector.Basic
import Mathlib.Data.PFun
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Basic
import Mathlib.Tactic.ApplyFun

/-!
# Blanked Lists

This file defines a Quotient type for Lists which are equivalent up to extension by some specific
value. This is useful for Turing machine tapes, as well as a computable variant of
finitely-supported functions on ℕ.

## Main Definitions

The main definitions in this file are

* `ListVal Γ val` - a Quotient type over Lists of `Γ` which are equivalent up to extension by `val`
* `ListBlank Γ` - A `ListVal` instantiation for Inhabited types, using the default as the value

-/

/-- The `val_extends` partial order holds of `l₁` and `l₂` if `l₂` is obtained by adding
vals (`val : Γ`) to the end of `l₁`. -/
def val_extends {Γ} (val : Γ) (l₁ l₂ : List Γ) : Prop :=
∃ n, l₂ = l₁ ++ List.replicate n val

@[refl] theorem val_extends.refl {Γ} (val : Γ) (l : List Γ) : val_extends val l l :=
⟨0, by simp⟩

@[trans] theorem val_extends.trans {Γ} (val : Γ) {l₁ l₂ l₃ : List Γ} :
    val_extends val l₁ l₂ → val_extends val l₂ l₃ → val_extends val l₁ l₃ := by
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩
  exact ⟨i+j, by simp [List.replicate_add]⟩

theorem val_extends.below_of_le {Γ} (val : Γ) {l l₁ l₂ : List Γ} :
  val_extends val l l₁ → val_extends val l l₂ →
  l₁.length ≤ l₂.length → val_extends val l₁ l₂ := by
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩ h
  use j - i
  simp only [List.length_append, add_le_add_iff_left, List.length_replicate] at h
  simp only [← List.replicate_add, add_tsub_cancel_of_le h, List.append_assoc]

/-- Any two extensions by val `l₁,l₂` of `l` have a common join (which can be taken to be the
longer of `l₁` and `l₂`). -/
def val_extends.above {Γ} (val : Γ) {l l₁ l₂ : List Γ}
  (h₁ : val_extends val l l₁) (h₂ : val_extends val l l₂) :
  {l' // val_extends val l₁ l' ∧ val_extends val l₂ l'} :=
if h : l₁.length ≤ l₂.length then
  ⟨l₂, h₁.below_of_le val h₂ h, val_extends.refl val _⟩
else
  ⟨l₁, val_extends.refl val _, h₂.below_of_le val h₁ (le_of_not_ge h)⟩

theorem val_extends.above_of_le {Γ} (val : Γ) {l l₁ l₂ : List Γ} :
  val_extends val l₁ l → val_extends val l₂ l →
  l₁.length ≤ l₂.length → val_extends val l₁ l₂ := by
  rintro ⟨i, rfl⟩ ⟨j, e⟩ h
  use i - j
  apply List.append_right_cancel (t := List.replicate j val)
  rw [<-e]
  simp only [ge_iff_le, List.append_assoc, List.append_cancel_left_eq]
  sorry
  -- TODO there should be a simp lemma that fires here



  -- refine List.append_right_cancel (e.symm.trans )
  -- rw [List.append_assoc, ← List.replicate_add, tsub_add_cancel_of_le]
  -- apply_fun List.length at e
  -- simp only [List.length_append, List.length_replicate] at e
  -- rwa [← add_le_add_iff_left, e, add_le_add_iff_right]


/-- `val_rel` is the symmetric closure of `val_extends`, turning it into an equivalence
relation. Two Lists are related by `val_rel` if one extends the other by vals. -/
def val_rel {Γ} (val : Γ) (l₁ l₂ : List Γ) : Prop :=
val_extends val l₁ l₂ ∨ val_extends val l₂ l₁

@[refl] theorem val_rel.refl {Γ} (val : Γ) (l : List Γ) : val_rel val l l :=
Or.inl (val_extends.refl val _)

@[symm] theorem val_rel.symm {Γ} (val : Γ) {l₁ l₂ : List Γ} :
  val_rel val l₁ l₂ → val_rel val l₂ l₁ := Or.symm

@[trans] theorem val_rel.trans {Γ} (val : Γ) {l₁ l₂ l₃ : List Γ} :
  val_rel val l₁ l₂ → val_rel val l₂ l₃ → val_rel val l₁ l₃ := by
  rintro (h₁ | h₁) (h₂ | h₂)
  · exact Or.inl (h₁.trans val h₂)
  · cases le_total l₁.length l₃.length with
    -- | a => sorry
    -- | b => sorry
    | inl h => exact Or.inl (h₁.above_of_le val h₂ h)
    | inr h => exact Or.inr (h₂.above_of_le val h₁ h)

  -- --h h
  --   · exact Or.inl (h₁.above_of_le val h₂ h)
  --   · exact Or.inr (h₂.above_of_le val h₁ h)
  · cases le_total l₁.length l₃.length with
    -- | a => sorry
    -- | b => sorry
    | inl h => exact Or.inl (h₁.below_of_le val h₂ h)
    | inr h => exact Or.inr (h₂.below_of_le val h₁ h)  --h
    -- · exact Or.inl (h₁.below_of_le val h₂ h)
    -- · exact Or.inr (h₂.below_of_le val h₁ h)
  · exact Or.inr (h₂.trans val h₁)


/-- Given two `val_rel` Lists, there exists (constructively) a common join. -/
def val_rel.above {Γ} (val : Γ) {l₁ l₂ : List Γ} (h : val_rel val l₁ l₂) :
  {l // val_extends val l₁ l ∧ val_extends val l₂ l} := by
  refine if hl : l₁.length ≤ l₂.length
    then ⟨l₂,
          Or.elim h id (λ h' => (val_extends.refl val _).above_of_le val h' hl),
          val_extends.refl val _⟩
    else ⟨l₁,
          val_extends.refl val _,
          Or.elim h (λ h' => (val_extends.refl val _).above_of_le val h' (Nat.le_of_not_le hl)) id⟩

/-- Given two `val_rel` Lists, there exists (constructively) a common meet. -/
def val_rel.below {Γ} (val : Γ) {l₁ l₂ : List Γ} (h : val_rel val l₁ l₂) :
  {l // val_extends val l l₁ ∧ val_extends val l l₂} := by
  refine if hl : l₁.length ≤ l₂.length
    then ⟨l₁, val_extends.refl val _, Or.elim h id (λ h' => (val_extends.refl val _).above_of_le val h' hl)⟩
    else ⟨l₂, Or.elim h (λ h' => (val_extends.refl val _).above_of_le val h' (le_of_not_ge hl)) id, val_extends.refl val _⟩
  -- exact (val_extends.refl val _).above_of_le val h' hl,
  -- exact (val_extends.refl val _).above_of_le val h' (le_of_not_ge hl)


theorem val_rel.equivalence (Γ) (val : Γ) : Equivalence (@val_rel Γ val) :=
⟨val_rel.refl val, @val_rel.symm _ _, @val_rel.trans _ _⟩

/-- Construct a Setoid instance for `val_rel`. -/
def val_rel.Setoid (Γ) (val : Γ) : Setoid (List Γ) := ⟨_, val_rel.equivalence _ val⟩

/-- A `ListVal Γ` is a Quotient of `List Γ` by extension by vals at the end. This is used to
represent half-tapes of a Turing machine, so that we can pretend that the List continues
infinitely with vals. -/
def ListVal (Γ) (val : Γ) := Quotient (val_rel.Setoid Γ val)

instance ListVal.inhabited {Γ} (val : Γ) : Inhabited (ListVal Γ val) :=
  ⟨Quotient.mk'' []⟩
instance ListVal.has_emptyc {Γ} (val : Γ) : EmptyCollection (ListVal Γ val) :=
  ⟨Quotient.mk'' []⟩

/-- A modified version of `Quotient.lift_on'` specialized for `ListVal`, with the stronger
precondition `val_extends` instead of `val_rel`. -/
@[reducible]
protected def ListVal.liftOn {Γ} {val : Γ} {α} (l : ListVal Γ val) (f : List Γ → α)
  (H : ∀ a b, val_extends val a b → f a = f b) : α :=
l.liftOn' f $ by
  rintro a b (h|h)
  · exact H _ _ h
  · exact (H _ _ h).symm

/-- The Quotient map turning a `List` into a `ListVal`. -/
def ListVal.mk {Γ} (val : Γ) : List Γ → ListVal Γ val := Quotient.mk''

protected lemma ListVal.induction_on {Γ} {val : Γ}
  {p : ListVal Γ val → Prop} (q : ListVal Γ val)
  (h : ∀ a, p (ListVal.mk val a)) : p q := Quotient.inductionOn' q h

/-- The head of a `ListVal` is well defined. -/
def ListVal.head {Γ} {val : Γ} (l : ListVal Γ val) : Γ := by
  apply l.liftOn (λ l => List.headD l val)
  rintro a _ ⟨i, rfl⟩
  cases a
  · cases i <;> rfl
  rfl

/-- The head of a `ListVal` is the defaulted head of a List that constructs it. -/
@[simp] theorem ListVal.head_mk {Γ} (val : Γ) (l : List Γ) :
  ListVal.head (ListVal.mk val l) = l.headD val := rfl

/-- The tail of a `ListVal` is well defined (up to the tail of vals). -/
def ListVal.tail {Γ} {val : Γ} (l : ListVal Γ val) : ListVal Γ val := by
  apply l.liftOn (fun l ↦ ListVal.mk val l.tail)
  rintro a _ ⟨i, rfl⟩
  refine' Quotient.sound' (Or.inl _)
  cases a
  · cases' i with i <;> [exact ⟨0, rfl⟩; exact ⟨i, rfl⟩]
  exact ⟨i, rfl⟩

@[simp] theorem ListVal.tail_mk {Γ} (val : Γ) (l : List Γ) :
  ListVal.tail (ListVal.mk val l) = ListVal.mk val l.tail := rfl

/-- We can cons an element onto a `ListVal`. -/
def ListVal.cons {Γ} {val : Γ} (a : Γ) (l : ListVal Γ val) : ListVal Γ val := by
  apply l.liftOn (fun l ↦ ListVal.mk val (List.cons a l))
  rintro _ _ ⟨i, rfl⟩
  exact Quotient.sound' (Or.inl ⟨i, rfl⟩)

@[simp] theorem ListVal.cons_mk {Γ} (val : Γ) (a : Γ) (l : List Γ) :
  ListVal.cons a (ListVal.mk val l) = ListVal.mk val (a :: l) := rfl

@[simp] theorem ListVal.head_cons {Γ} (val : Γ) (a : Γ) :
  ∀ (l : ListVal Γ val), (l.cons a).head = a :=
Quotient.ind' $ by exact λ l => rfl

@[simp] theorem ListVal.tail_cons {Γ} (val : Γ) (a : Γ) :
  ∀ (l : ListVal Γ val), (l.cons a).tail = l :=
Quotient.ind' $ by exact λ l => rfl

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `List` where
this only holds for nonempty Lists. -/
@[simp] theorem ListVal.cons_head_tail {Γ} {val : Γ} :
  ∀ (l : ListVal Γ val), l.tail.cons l.head = l := by
  apply Quotient.ind'
  refine' fun l ↦ Quotient.sound' (Or.inr _)
  cases l
  · exact ⟨1, rfl⟩
  · rfl

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `List` where
this only holds for nonempty Lists. -/
theorem ListVal.exists_cons {Γ} {val : Γ} (l : ListVal Γ val) :
  ∃ a l', l = ListVal.cons a l' :=
⟨_, _, (ListVal.cons_head_tail _).symm⟩

/-- The n-th element of a `ListVal` is well defined for all `n : ℕ`, unlike in a `List`. -/
def ListVal.nth {Γ} {val : Γ} (l : ListVal Γ val) (n : ℕ) : Γ := by
  apply l.liftOn (fun l ↦ List.getD l n val)
  rintro l _ ⟨i, rfl⟩
  cases' lt_or_le n _ with h h
  · rw [List.getD_append _ _ val _ h]
  rw [List.getD_eq_default _ val h]
  cases' le_or_lt _ n with h₂ h₂
  · rw [List.getD_eq_default _ val h₂]
  rw [List.getD_eq_get _ val h₂, List.get_append_right' h, List.get_replicate]

@[simp] theorem ListVal.nth_mk {Γ} (val : Γ) (l : List Γ) (n : ℕ) :
  (ListVal.mk val l).nth n = l.getD n val := rfl

@[simp] theorem ListVal.nth_zero {Γ} {val : Γ} (l : ListVal Γ val) : l.nth 0 = l.head := by
  conv => lhs; rw [← ListVal.cons_head_tail l]
  exact Quotient.inductionOn' l.tail fun l ↦ rfl

@[simp] theorem ListVal.nth_succ {Γ} {val : Γ} (l : ListVal Γ val) (n : ℕ) :
  l.nth (n + 1) = l.tail.nth n := by
  conv => lhs; rw [← ListVal.cons_head_tail l]
  exact Quotient.inductionOn' l.tail fun l ↦ rfl



-- example
--     (Γ : Type)
--     (l₁ l₂ : List Γ)
--     (h : List.length l₁ ≤ List.length l₂) :
--     List.length l₁ = List.length l₂ + (List.length l₂ - List.length l₁) := by
--   rw [add_tsub_cancel_of_le h]
--   done


@[ext] theorem ListVal.ext {Γ} {val : Γ} {L₁ L₂ : ListVal Γ val} :
  (∀ i, L₁.nth i = L₂.nth i) → L₁ = L₂ := by
  apply L₂.induction_on
  apply L₁.induction_on
  intros l₁ l₂ H
  -- refine' ListVal.induction_on L₁ _ (fun l₁ ↦ ListVal.induction_on L₂ (fun l₂ H ↦ _))
  wlog h : l₁.length ≤ l₂.length
  · cases le_total l₁.length l₂.length <;> [skip; symm] <;> apply this <;> try assumption
    intro
    rw [H]
  refine' Quotient.sound' (Or.inl ⟨l₂.length - l₁.length, _⟩)
  refine' List.ext_get _ fun i h h₂ ↦ Eq.symm _
  · simp only [List.length_append, List.length_replicate]
    rw [add_tsub_cancel_of_le h]
  simp only [ListVal.nth_mk] at H
  cases' lt_or_le i l₁.length with h' h'
  · simp only [List.get_append _ h', List.get?_eq_get h, List.get?_eq_get h',
      ← List.getD_eq_get _ val h, ← List.getD_eq_get _ val h', H]
  · rw [List.get_append_right' h', List.get_replicate, ←List.getD_eq_get _ val h, <-H i,
      List.getD_eq_default]
    exact h'

/-- Apply a function to a value stored at the nth position of the List. -/
@[simp] def ListVal.modifyNth {Γ} {val : Γ} (f : Γ → Γ) : ℕ → ListVal Γ val → ListVal Γ val
  | 0, L => L.tail.cons (f L.head)
  | n + 1, L => (L.tail.modifyNth f n).cons L.head

theorem ListVal.nth_modifyNth {Γ} {val : Γ} (f : Γ → Γ) (n i) (L : ListVal Γ val) :
  (L.modifyNth f n).nth i = if i = n then f (L.nth i) else L.nth i := by
  induction' n with n IH generalizing i L
  · cases i <;> simp only [ListVal.nth_zero, if_true, ListVal.head_cons, ListVal.modifyNth,
      ListVal.nth_succ, if_false, ListVal.tail_cons, Nat.zero_eq]
  · cases i
    · rw [if_neg (Nat.succ_ne_zero _).symm]
      simp only [ListVal.nth_zero, ListVal.head_cons, ListVal.modifyNth, Nat.zero_eq]
    · simp only [IH, ListVal.modifyNth, ListVal.nth_succ, ListVal.tail_cons, Nat.succ.injEq]

/-- A specified pointed map is a map that sends one specified value to the other. -/
structure SpecifiedPointedMap.{u, v} (Γ : Type u) (Γ' : Type v)
  (val : Γ) (val' : Γ') : Type (max u v) :=
(f : Γ → Γ') (map_pt' : f val = val')

instance {Γ Γ'} (val : Γ) (val' : Γ') : Inhabited (SpecifiedPointedMap Γ Γ' val val') :=
⟨⟨λ _ => val', rfl⟩⟩

instance {Γ Γ'} (val : Γ) (val' : Γ') :
  CoeFun (SpecifiedPointedMap Γ Γ' val val') (λ _ => Γ → Γ') :=
⟨SpecifiedPointedMap.f⟩

@[simp] theorem SpecifiedPointedMap.mk_val {Γ Γ'} (val : Γ) (val' : Γ')
  (f : Γ → Γ') (pt) : (@SpecifiedPointedMap.mk _ _ val val' f pt : Γ → Γ') = f := rfl

@[simp] theorem SpecifiedPointedMap.map_pt {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : SpecifiedPointedMap Γ Γ' val val') : f val = val' := SpecifiedPointedMap.map_pt' _

@[simp] theorem SpecifiedPointedMap.headD_map {Γ Γ'} (val : Γ) (val' : Γ')
  (f : SpecifiedPointedMap Γ Γ' val val')
  (l : List Γ) : (l.map f).headD val' = f (l.headD val) := by
  cases l <;> [exact (SpecifiedPointedMap.map_pt f).symm; rfl]

/-- The `map` function on Lists is well defined on `ListVal`s provided that the map is
pointed. -/
def ListVal.map {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : SpecifiedPointedMap Γ Γ' val val') (l : ListVal Γ val) : ListVal Γ' val' := by
  apply l.liftOn (fun l ↦ ListVal.mk val' (List.map f l))
  rintro l _ ⟨i, rfl⟩; refine' Quotient.sound' (Or.inl ⟨i, _⟩)
  simp only [SpecifiedPointedMap.map_pt, List.map_append, List.map_replicate]

@[simp] theorem ListVal.map_mk {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : SpecifiedPointedMap Γ Γ' val val') (l : List Γ) :
  (ListVal.mk val l).map f = ListVal.mk val' (l.map f) := rfl

@[simp] theorem ListVal.head_map {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : SpecifiedPointedMap Γ Γ' val val') (l : ListVal Γ val) : (l.map f).head = f l.head := by
  conv => lhs; rw [← ListVal.cons_head_tail l]
  exact Quotient.inductionOn' l fun a ↦ rfl

@[simp] theorem ListVal.tail_map {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : SpecifiedPointedMap Γ Γ' val val') (l : ListVal Γ val) : (l.map f).tail = l.tail.map f := by
  conv => lhs; rw [← ListVal.cons_head_tail l]
  exact Quotient.inductionOn' l fun a ↦ rfl

@[simp] theorem ListVal.map_cons {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : SpecifiedPointedMap Γ Γ' val val') (l : ListVal Γ val) (a : Γ) :
  (l.cons a).map f = (l.map f).cons (f a) := by
  refine' (ListVal.cons_head_tail _).symm.trans _
  simp only [ListVal.head_map, ListVal.head_cons, ListVal.tail_map, ListVal.tail_cons]

@[simp] theorem ListVal.nth_map {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : SpecifiedPointedMap Γ Γ' val val') (l : ListVal Γ val) (n : ℕ) :
  (l.map f).nth n = f (l.nth n) := by
  refine' l.inductionOn fun l ↦ _
  suffices ((mk val l).map f).nth n = f ((mk val l).nth n) by exact this
  -- simp_rw [ListVal.map_mk, ListVal.nth_mk]
  -- Depends on #7307
  sorry
  -- simp_rw [List.getD_map, ListVal.map_mk, ListVal.nth_mk, List.getI_eq_iget_get?]
  -- cases l.get? n
  -- · exact f.2.symm
  -- · rfl

-- TODO ∀ i, Γ i  to (i : ι) → Γ i


/-- The `i`-th projection as a pointed map. -/
def proj {ι : Type*} {Γ : ι → Type*} (vals : ∀ i, Γ i) (i : ι) :
  SpecifiedPointedMap (∀ i, Γ i) (Γ i) vals (vals i) := ⟨λ a => a i, rfl⟩

theorem proj_map_nth {ι : Type*} {Γ : ι → Type*} (vals : ∀ i, Γ i) (i : ι)
  (L n) : (ListVal.map (@proj ι Γ vals i) L).nth n = L.nth n i := by
  rw [ListVal.nth_map]; rfl

theorem ListVal.map_modifyNth {Γ Γ'} {val : Γ} {val' : Γ'}
  (F : SpecifiedPointedMap Γ Γ' val val') (f : Γ → Γ) (f' : Γ' → Γ')
  (H : ∀ x, F (f x) = f' (F x)) (n) (L : ListVal Γ val) :
  (L.modifyNth f n).map F = (L.map F).modifyNth f' n := by
  induction' n with n IH generalizing L <;>
    simp only [*, ListVal.head_map, ListVal.modifyNth, ListVal.map_cons, ListVal.tail_map]

/-- Append a List on the left side of a ListVal. -/
@[simp] def ListVal.append {Γ} {val : Γ} : List Γ → ListVal Γ val → ListVal Γ val
  | [], L => L
  | a :: l, L => ListVal.cons a (ListVal.append l L)

@[simp] theorem ListVal.append_mk {Γ} {val : Γ} (l₁ l₂ : List Γ) :
  ListVal.append l₁ (ListVal.mk val l₂) = ListVal.mk val (l₁ ++ l₂) := by
  induction l₁ <;>
    simp only [*, ListVal.append, List.nil_append, List.cons_append, ListVal.cons_mk]

theorem ListVal.append_assoc {Γ} {val : Γ} (l₁ l₂ : List Γ) (l₃ : ListVal Γ val) :
  ListVal.append (l₁ ++ l₂) l₃ = ListVal.append l₁ (ListVal.append l₂ l₃) := by
  refine' l₃.inductionOn fun l ↦ _
  -- Porting note: Added `suffices` to get `simp` to work.
  suffices append (l₁ ++ l₂) (mk val l) = append l₁ (append l₂ (mk val l)) by exact this
  simp only [ListVal.append_mk, List.append_assoc]

/-- The `bind` function on Lists is well defined on `ListVal`s provided that the default element
is sent to a sequence of default elements. -/
def ListVal.bind {Γ Γ'} {val : Γ} (val' : Γ')
  (l : ListVal Γ val) (f : Γ → List Γ')
  (hf : ∃ n, f val = List.replicate n val') : ListVal Γ' val' := by
  apply l.liftOn (fun l ↦ ListVal.mk val' (List.bind l f))
  rintro l _ ⟨i, rfl⟩; cases' hf with n e; refine' Quotient.sound' (Or.inl ⟨i * n, _⟩)
  rw [List.append_bind, mul_comm]; congr
  induction' i with i IH; rfl
  simp only [IH, e, List.replicate_add, Nat.mul_succ, add_comm, List.replicate_succ, List.cons_bind]

@[simp] lemma ListVal.bind_mk {Γ Γ'} (val : Γ) (val' : Γ')
  (l : List Γ) (f : Γ → List Γ') (hf) :
  (ListVal.mk val l).bind val' f hf = ListVal.mk val' (l.bind f) := rfl

@[simp] lemma ListVal.cons_bind {Γ Γ'} {val : Γ} {val' : Γ'}
  (a : Γ) (l : ListVal Γ val) (f : Γ → List Γ') (hf) :
  (l.cons a).bind val' f hf = (l.bind val' f hf).append (f a) := by
  refine' l.inductionOn fun l ↦ _
  suffices ((mk val l).cons a).bind val' f hf = ((mk val l).bind val' f hf).append (f a) by exact this
  simp only [ListVal.append_mk, ListVal.bind_mk, ListVal.cons_mk, List.cons_bind]


section ListBlank

/-- A `ListBlank Γ` is a Quotient of `List Γ` by extension by blanks at the end. This is used to
represent half-tapes of a Turing machine, so that we can pretend that the List continues
infinitely with blanks. -/
def ListBlank (Γ) [Inhabited Γ] := ListVal Γ default

instance ListBlank.inhabited {Γ} [Inhabited Γ] : Inhabited (ListBlank Γ) := ⟨Quotient.mk'' []⟩
instance ListBlank.hasEmptyc {Γ} [Inhabited Γ] : EmptyCollection (ListBlank Γ) :=
  ⟨Quotient.mk'' []⟩

/-- The Quotient map turning a `List` into a `ListBlank`. -/
def ListBlank.mk {Γ} [Inhabited Γ] : List Γ → ListBlank Γ := ListVal.mk default

protected lemma ListBlank.induction_on {Γ} [Inhabited Γ]
  {p : ListBlank Γ → Prop} (q : ListBlank Γ)
  (h : ∀ a, p (ListBlank.mk a)) : p q := Quotient.inductionOn' q h

/-- The head of a `ListBlank` is well defined. -/
def ListBlank.head {Γ} [Inhabited Γ] (l : ListBlank Γ) : Γ := ListVal.head l

@[simp] theorem ListBlank.head_mk {Γ} [Inhabited Γ] (l : List Γ) :
    ListBlank.head (ListBlank.mk l) = l.headI := by
  unfold head mk
  rw [ListVal.head_mk]
  sorry
  -- There should be a lemma for this

/-- The tail of a `ListBlank` is well defined (up to the tail of blanks). -/
def ListBlank.tail {Γ} [Inhabited Γ] (l : ListBlank Γ) : ListBlank Γ := ListVal.tail l

@[simp] theorem ListBlank.tail_mk {Γ} [Inhabited Γ] (l : List Γ) :
  ListBlank.tail (ListBlank.mk l) = ListBlank.mk l.tail := rfl

/-- We can cons an element onto a `ListBlank`. -/
def ListBlank.cons {Γ} [Inhabited Γ] (a : Γ) (l : ListBlank Γ) : ListBlank Γ := ListVal.cons a l

@[simp] theorem ListBlank.cons_mk {Γ} [Inhabited Γ] (a : Γ) (l : List Γ) :
  ListBlank.cons a (ListBlank.mk l) = ListBlank.mk (a :: l) := rfl

@[simp] theorem ListBlank.head_cons {Γ} [Inhabited Γ] (a : Γ) :
  ∀ (l : ListBlank Γ), (l.cons a).head = a :=
Quotient.ind' $ by exact λ l => rfl

@[simp] theorem ListBlank.tail_cons {Γ} [Inhabited Γ] (a : Γ) :
  ∀ (l : ListBlank Γ), (l.cons a).tail = l :=
Quotient.ind' $ by exact λ l => rfl

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `List` where
this only holds for nonempty Lists. -/
@[simp] theorem ListBlank.cons_head_tail {Γ} [Inhabited Γ] :
  ∀ (l : ListBlank Γ), l.tail.cons l.head = l := by
  apply Quotient.ind'
  refine' fun l ↦ Quotient.sound' (Or.inr _)
  cases l
  · exact ⟨1, rfl⟩
  · rfl

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `List` where
this only holds for nonempty Lists. -/
theorem ListBlank.exists_cons {Γ} [Inhabited Γ] (l : ListBlank Γ) :
  ∃ a l', l = ListBlank.cons a l' :=
⟨_, _, (ListBlank.cons_head_tail _).symm⟩

/-- The n-th element of a `ListBlank` is well defined for all `n : ℕ`, unlike in a `List`. -/
def ListBlank.nth {Γ} [Inhabited Γ] (l : ListBlank Γ) (n : ℕ) : Γ := ListVal.nth l n

@[simp] theorem ListBlank.nth_mk {Γ} [Inhabited Γ] (l : List Γ) (n : ℕ) :
  (ListBlank.mk l).nth n = l.getI n := rfl

@[simp] theorem ListBlank.nth_zero {Γ} [Inhabited Γ] (l : ListBlank Γ) : l.nth 0 = l.head :=
ListVal.nth_zero l

@[simp] theorem ListBlank.nth_succ {Γ} [Inhabited Γ] (l : ListBlank Γ) (n : ℕ) :
  l.nth (n + 1) = l.tail.nth n :=
ListVal.nth_succ l n

@[ext] theorem ListBlank.ext {Γ} [Inhabited Γ] {L₁ L₂ : ListBlank Γ} :
  (∀ i, L₁.nth i = L₂.nth i) → L₁ = L₂ :=
ListVal.ext

/-- Apply a function to a value stored at the nth position of the List. -/
def ListBlank.modifyNth {Γ} [Inhabited Γ] (f : Γ → Γ) : ℕ → ListBlank Γ → ListBlank Γ :=
ListVal.modifyNth f

@[simp] lemma ListBlank.modifyNth_zero {Γ} [Inhabited Γ] (f : Γ → Γ) (L : ListBlank Γ) :
  L.modifyNth f 0 = L.tail.cons (f L.head) := rfl

@[simp] lemma ListBlank.modifyNth_cons {Γ} [Inhabited Γ] (f : Γ → Γ) (n : ℕ) (L : ListBlank Γ) :
  L.modifyNth f (n+1) = (L.tail.modifyNth f n).cons L.head := rfl

theorem ListBlank.nth_modifyNth {Γ} [Inhabited Γ] (f : Γ → Γ) (n i) (L : ListBlank Γ) :
  (L.modifyNth f n).nth i = if i = n then f (L.nth i) else L.nth i :=
ListVal.nth_modifyNth f n i L

/-- A pointed map of `Inhabited` types is a map that sends one default value to the other. -/
def PointedMap.{u, v} (Γ : Type u) (Γ' : Type v)
  [Inhabited Γ] [Inhabited Γ'] : Type (max u v) :=
SpecifiedPointedMap Γ Γ' default default

instance {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] : Inhabited (PointedMap Γ Γ') :=
⟨⟨default, rfl⟩⟩

instance {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] : CoeFun (PointedMap Γ Γ') (λ _ => Γ → Γ') :=
⟨SpecifiedPointedMap.f⟩

-- @[simp] theorem PointedMap.mk_val {Γ Γ'} [Inhabited Γ] [Inhabited Γ']
--   (f : Γ → Γ') (pt) : (PointedMap.mk f pt : Γ → Γ') = f := rfl

@[simp] theorem PointedMap.map_pt {Γ Γ'} [Inhabited Γ] [Inhabited Γ']
  (f : PointedMap Γ Γ') : f default = default := SpecifiedPointedMap.map_pt f

@[simp] theorem PointedMap.headI_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ']
  (f : PointedMap Γ Γ') (l : List Γ) : (l.map f).headI = f l.headI := by
  cases l <;> [exact (PointedMap.map_pt f).symm; rfl]

/-- The `map` function on Lists is well defined on `ListBlank`s provided that the map is
pointed. -/
def ListBlank.map {Γ Γ'} [Inhabited Γ] [Inhabited Γ']
  (f : PointedMap Γ Γ') (l : ListBlank Γ) : ListBlank Γ' := ListVal.map f l

@[simp] theorem ListBlank.map_mk {Γ Γ'} [Inhabited Γ] [Inhabited Γ']
  (f : PointedMap Γ Γ') (l : List Γ) : (ListBlank.mk l).map f = ListBlank.mk (l.map f) := rfl

@[simp] theorem ListBlank.head_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ']
  (f : PointedMap Γ Γ') (l : ListBlank Γ) : (l.map f).head = f l.head := ListVal.head_map f l

@[simp] theorem ListBlank.tail_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ']
  (f : PointedMap Γ Γ') (l : ListBlank Γ) : (l.map f).tail = l.tail.map f := ListVal.tail_map f l

@[simp] theorem ListBlank.map_cons {Γ Γ'} [Inhabited Γ] [Inhabited Γ']
  (f : PointedMap Γ Γ') (l : ListBlank Γ) (a : Γ) : (l.cons a).map f = (l.map f).cons (f a) :=
ListVal.map_cons f l a

@[simp] theorem ListBlank.nth_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ']
  (f : PointedMap Γ Γ') (l : ListBlank Γ) (n : ℕ) : (l.map f).nth n = f (l.nth n) :=
ListVal.nth_map f l n

-- /-- The `i`-th projection as a pointed map. -/
-- def PointedMap_proj {ι : Type*} {Γ : ι → Type*} [∀ i, Inhabited (Γ i)] (i : ι) :
--   PointedMap (∀ i, Γ i) (Γ i) := ⟨λ a => a i, rfl⟩

-- theorem PointedMap_proj_map_nth {ι : Type*} {Γ : ι → Type*} [∀ i, Inhabited (Γ i)] (i : ι)
--   (L n) : (ListBlank.map (@proj ι Γ _ i) L).nth n = L.nth n i := by
--   rw [ListBlank.nth_map]; rfl

theorem ListBlank.map_modifyNth {Γ Γ'} [Inhabited Γ] [Inhabited Γ']
  (F : PointedMap Γ Γ') (f : Γ → Γ) (f' : Γ' → Γ')
  (H : ∀ x, F (f x) = f' (F x)) (n) (L : ListBlank Γ) :
  (L.modifyNth f n).map F = (L.map F).modifyNth f' n :=
ListVal.map_modifyNth F f f' H n L

/-- Append a List on the left side of a ListBlank. -/
@[simp] def ListBlank.append {Γ} [Inhabited Γ] : List Γ → ListBlank Γ → ListBlank Γ :=
ListVal.append

@[simp] theorem ListBlank.append_mk {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) :
  ListBlank.append l₁ (ListBlank.mk l₂) = ListBlank.mk (l₁ ++ l₂) :=
ListVal.append_mk l₁ l₂

theorem ListBlank.append_assoc {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) (l₃ : ListBlank Γ) :
  ListBlank.append (l₁ ++ l₂) l₃ = ListBlank.append l₁ (ListBlank.append l₂ l₃) :=
ListVal.append_assoc l₁ l₂ l₃

/-- The `bind` function on Lists is well defined on `ListBlank`s provided that the default element
is sent to a sequence of default elements. -/
def ListBlank.bind {Γ Γ'} [Inhabited Γ] [Inhabited Γ']
  (l : ListBlank Γ) (f : Γ → List Γ')
  (hf : ∃ n, f default = List.replicate n default) : ListBlank Γ' :=
ListVal.bind default l f hf

@[simp] lemma ListBlank.bind_mk {Γ Γ'} [Inhabited Γ] [Inhabited Γ']
  (l : List Γ) (f : Γ → List Γ') (hf) :
  (ListBlank.mk l).bind f hf = ListBlank.mk (l.bind f) := rfl

@[simp] lemma ListBlank.cons_bind {Γ Γ'} [Inhabited Γ] [Inhabited Γ']
  (a : Γ) (l : ListBlank Γ) (f : Γ → List Γ') (hf) :
  (l.cons a).bind f hf = (l.bind f hf).append (f a) :=
ListVal.cons_bind a l f hf

end ListBlank
