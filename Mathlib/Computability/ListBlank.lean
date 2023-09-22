/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Bolton Bailey
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

This file defines a quotient type for Lists which are equivalent up to extension by some specific
value. This is useful for Turing machine tapes, as well as a computable variant of
finitely-supported functions on ℕ.

## Main Definitions

The main definitions in this file are

* `List_val Γ val` - a quotient type over Lists of `Γ` which are equivalent up to extension by `val`
* `List_blank Γ` - A `List_val` instantiation for inhabited types, using the default as the value

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
or.inl (val_extends.refl val _)

@[symm] theorem val_rel.symm {Γ} (val : Γ) {l₁ l₂ : List Γ} :
  val_rel val l₁ l₂ → val_rel val l₂ l₁ := or.symm

@[trans] theorem val_rel.trans {Γ} (val : Γ) {l₁ l₂ l₃ : List Γ} :
  val_rel val l₁ l₂ → val_rel val l₂ l₃ → val_rel val l₁ l₃ :=
begin
  rintro (h₁|h₁) (h₂|h₂),
  { exact or.inl (h₁.trans val h₂) },
  { cases le_total l₁.length l₃.length with h h,
    { exact or.inl (h₁.above_of_le val h₂ h) },
    { exact or.inr (h₂.above_of_le val h₁ h) } },
  { cases le_total l₁.length l₃.length with h h,
    { exact or.inl (h₁.below_of_le val h₂ h) },
    { exact or.inr (h₂.below_of_le val h₁ h) } },
  { exact or.inr (h₂.trans val h₁) },
end

/-- Given two `val_rel` Lists, there exists (constructively) a common join. -/
def val_rel.above {Γ} (val : Γ) {l₁ l₂ : List Γ} (h : val_rel val l₁ l₂) :
  {l // val_extends val l₁ l ∧ val_extends val l₂ l} :=
begin
  refine if hl : l₁.length ≤ l₂.length
    then ⟨l₂, or.elim h id (λ h', _), val_extends.refl val _⟩
    else ⟨l₁, val_extends.refl val _, or.elim h (λ h', _) id⟩,
  exact (val_extends.refl val _).above_of_le val h' hl,
  exact (val_extends.refl val _).above_of_le val h' (le_of_not_ge hl)
end

/-- Given two `val_rel` Lists, there exists (constructively) a common meet. -/
def val_rel.below {Γ} (val : Γ) {l₁ l₂ : List Γ} (h : val_rel val l₁ l₂) :
  {l // val_extends val l l₁ ∧ val_extends val l l₂} :=
begin
  refine if hl : l₁.length ≤ l₂.length
    then ⟨l₁, val_extends.refl val _, or.elim h id (λ h', _)⟩
    else ⟨l₂, or.elim h (λ h', _) id, val_extends.refl val _⟩,
  exact (val_extends.refl val _).above_of_le val h' hl,
  exact (val_extends.refl val _).above_of_le val h' (le_of_not_ge hl)
end

theorem val_rel.equivalence (Γ) (val : Γ) : equivalence (@val_rel Γ val) :=
⟨val_rel.refl val, @val_rel.symm _ _, @val_rel.trans _ _⟩

/-- Construct a setoid instance for `val_rel`. -/
def val_rel.setoid (Γ) (val : Γ) : setoid (List Γ) := ⟨_, val_rel.equivalence _ val⟩

/-- A `List_val Γ` is a quotient of `List Γ` by extension by vals at the end. This is used to
represent half-tapes of a Turing machine, so that we can pretend that the List continues
infinitely with vals. -/
def List_val (Γ) (val : Γ) := quotient (val_rel.setoid Γ val)

instance List_val.inhabited {Γ} (val : Γ) : inhabited (List_val Γ val) := ⟨quotient.mk' []⟩
instance List_val.has_emptyc {Γ} (val : Γ) : has_emptyc (List_val Γ val) := ⟨quotient.mk' []⟩

/-- A modified version of `quotient.lift_on'` specialized for `List_val`, with the stronger
precondition `val_extends` instead of `val_rel`. -/
@[elab_as_eliminator, reducible]
protected def List_val.lift_on {Γ} {val : Γ} {α} (l : List_val Γ val) (f : List Γ → α)
  (H : ∀ a b, val_extends val a b → f a = f b) : α :=
l.lift_on' f $ by rintro a b (h|h); [exact H _ _ h, exact (H _ _ h).symm]

/-- The quotient map turning a `List` into a `List_val`. -/
def List_val.mk {Γ} (val : Γ) : List Γ → List_val Γ val := quotient.mk'

@[elab_as_eliminator]
protected lemma List_val.induction_on {Γ} {val : Γ}
  {p : List_val Γ val → Prop} (q : List_val Γ val)
  (h : ∀ a, p (List_val.mk val a)) : p q := quotient.induction_on' q h

/-- The head of a `List_val` is well defined. -/
def List_val.head {Γ} {val : Γ} (l : List_val Γ val) : Γ :=
l.lift_on (List.headd val) begin
  rintro _ _ ⟨i, rfl⟩,
  cases a, {cases i; refl}, refl
end

/-- The head of a `List_val` is the defaulted head of a List that constructs it. -/
@[simp] theorem List_val.head_mk {Γ} (val : Γ) (l : List Γ) :
  List_val.head (List_val.mk val l) = l.headd val := rfl

/-- The tail of a `List_val` is well defined (up to the tail of vals). -/
def List_val.tail {Γ} {val : Γ} (l : List_val Γ val) : List_val Γ val :=
l.lift_on (λ l, List_val.mk val l.tail) begin
  rintro _ _ ⟨i, rfl⟩,
  refine quotient.sound' (or.inl _),
  cases a; [{cases i; [exact ⟨0, rfl⟩, exact ⟨i, rfl⟩]}, exact ⟨i, rfl⟩]
end

@[simp] theorem List_val.tail_mk {Γ} (val : Γ) (l : List Γ) :
  List_val.tail (List_val.mk val l) = List_val.mk val l.tail := rfl

/-- We can cons an element onto a `List_val`. -/
def List_val.cons {Γ} {val : Γ} (a : Γ) (l : List_val Γ val) : List_val Γ val :=
l.lift_on (λ l, List_val.mk val (List.cons a l)) begin
  rintro _ _ ⟨i, rfl⟩,
  exact quotient.sound' (or.inl ⟨i, rfl⟩),
end

@[simp] theorem List_val.cons_mk {Γ} (val : Γ) (a : Γ) (l : List Γ) :
  List_val.cons a (List_val.mk val l) = List_val.mk val (a :: l) := rfl

@[simp] theorem List_val.head_cons {Γ} (val : Γ) (a : Γ) :
  ∀ (l : List_val Γ val), (l.cons a).head = a :=
quotient.ind' $ by exact λ l, rfl

@[simp] theorem List_val.tail_cons {Γ} (val : Γ) (a : Γ) :
  ∀ (l : List_val Γ val), (l.cons a).tail = l :=
quotient.ind' $ by exact λ l, rfl

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `List` where
this only holds for nonempty Lists. -/
@[simp] theorem List_val.cons_head_tail {Γ} {val : Γ} :
  ∀ (l : List_val Γ val), l.tail.cons l.head = l :=
quotient.ind' begin
  refine (λ l, quotient.sound' (or.inr _)),
  cases l, {exact ⟨1, rfl⟩}, {refl},
end

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `List` where
this only holds for nonempty Lists. -/
theorem List_val.exists_cons {Γ} {val : Γ} (l : List_val Γ val) :
  ∃ a l', l = List_val.cons a l' :=
⟨_, _, (List_val.cons_head_tail _).symm⟩

/-- The n-th element of a `List_val` is well defined for all `n : ℕ`, unlike in a `List`. -/
def List_val.nth {Γ} {val : Γ} (l : List_val Γ val) (n : ℕ) : Γ :=
l.lift_on (λ l, List.nthd val l n) begin
  rintro l _ ⟨i, rfl⟩,
  simp only,
  cases lt_or_le n l.length with h h, {rw List.nthd_append _ _ _ _ h, },
  rw List.nthd_eq_default _ _ h,
  cases le_or_lt _ _ with h₂ h₂, {rw List.nthd_eq_default _ _ h₂},
  rw [List.nthd_eq_nth_le _ _ h₂, List.nth_le_append_right h, List.nth_le_replicate],
end

@[simp] theorem List_val.nth_mk {Γ} (val : Γ) (l : List Γ) (n : ℕ) :
  (List_val.mk val l).nth n = l.nthd val n := rfl

@[simp] theorem List_val.nth_zero {Γ} {val : Γ} (l : List_val Γ val) : l.nth 0 = l.head :=
begin
  conv {to_lhs, rw [← List_val.cons_head_tail l]},
  exact quotient.induction_on' l.tail (λ l, rfl)
end

@[simp] theorem List_val.nth_succ {Γ} {val : Γ} (l : List_val Γ val) (n : ℕ) :
  l.nth (n + 1) = l.tail.nth n :=
begin
  conv {to_lhs, rw [← List_val.cons_head_tail l]},
  exact quotient.induction_on' l.tail (λ l, rfl)
end

@[ext] theorem List_val.ext {Γ} {val : Γ} {L₁ L₂ : List_val Γ val} :
  (∀ i, L₁.nth i = L₂.nth i) → L₁ = L₂ :=
List_val.induction_on L₁ $ λ l₁, List_val.induction_on L₂ $ λ l₂ H,
begin
  wlog h : l₁.length ≤ l₂.length using l₁ l₂,
  swap, { exact (this $ λ i, (H i).symm).symm },
  refine quotient.sound' (or.inl ⟨l₂.length - l₁.length, _⟩),
  refine List.ext_le _ (λ i h h₂, eq.symm _),
  { simp only [add_tsub_cancel_of_le h, List.length_append, List.length_replicate] },
  simp only [List_val.nth_mk] at H,
  cases lt_or_le i l₁.length with h' h',
  { simp only [List.nth_le_append _ h', List.nth_le_nth h, List.nth_le_nth h',
               ←List.nthd_eq_nth_le _ val h, ←List.nthd_eq_nth_le _ val h', H], },
  { simp only [List.nth_le_append_right h', List.nth_le_replicate, ←List.nthd_eq_nth_le _ val h,
               ←H, List.nthd_eq_default _ val h'], }
end

/-- Apply a function to a value stored at the nth position of the List. -/
@[simp] def List_val.modify_nth {Γ} {val : Γ} (f : Γ → Γ) : ℕ → List_val Γ val → List_val Γ val
| 0     L := L.tail.cons (f L.head)
| (n+1) L := (L.tail.modify_nth n).cons L.head

theorem List_val.nth_modify_nth {Γ} {val : Γ} (f : Γ → Γ) (n i) (L : List_val Γ val) :
  (L.modify_nth f n).nth i = if i = n then f (L.nth i) else L.nth i :=
begin
  induction n with n IH generalizing i L,
  { cases i; simp only [List_val.nth_zero, if_true,
      List_val.head_cons, List_val.modify_nth, eq_self_iff_true,
      List_val.nth_succ, if_false, List_val.tail_cons] },
  { cases i,
    { rw if_neg (nat.succ_ne_zero _).symm,
      simp only [List_val.nth_zero, List_val.head_cons, List_val.modify_nth] },
    { simp only [IH, List_val.modify_nth, List_val.nth_succ, List_val.tail_cons] } }
end

/-- A specified pointed map is a map that sends one specified value to the other. -/
structure {u v} specified_pointed_map (Γ : Type u) (Γ' : Type v)
  (val : Γ) (val' : Γ') : Type (max u v) :=
(f : Γ → Γ') (map_pt' : f val = val')

instance {Γ Γ'} (val : Γ) (val' : Γ') : inhabited (specified_pointed_map Γ Γ' val val') :=
⟨⟨λ _, val', rfl⟩⟩

instance {Γ Γ'} (val : Γ) (val' : Γ') :
  has_coe_to_fun (specified_pointed_map Γ Γ' val val') (λ _, Γ → Γ') :=
⟨specified_pointed_map.f⟩

@[simp] theorem specified_pointed_map.mk_val {Γ Γ'} (val : Γ) (val' : Γ')
  (f : Γ → Γ') (pt) : (@specified_pointed_map.mk _ _ val val' f pt : Γ → Γ') = f := rfl

@[simp] theorem specified_pointed_map.map_pt {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : specified_pointed_map Γ Γ' val val') : f val = val' := specified_pointed_map.map_pt' _

@[simp] theorem specified_pointed_map.head_map {Γ Γ'} (val : Γ) (val' : Γ')
  (f : specified_pointed_map Γ Γ' val val') (l : List Γ) : (l.map f).headd val' = f (l.headd val) :=
begin
  cases l; simp,
end

/-- The `map` function on Lists is well defined on `List_val`s provided that the map is
pointed. -/
def List_val.map {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : specified_pointed_map Γ Γ' val val') (l : List_val Γ val) : List_val Γ' val' :=
l.lift_on (λ l, List_val.mk val' (List.map f l)) begin
  rintro l _ ⟨i, rfl⟩, refine quotient.sound' (or.inl ⟨i, _⟩),
  simp only [specified_pointed_map.map_pt, List.map_append, List.map_replicate],
end

@[simp] theorem List_val.map_mk {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : specified_pointed_map Γ Γ' val val') (l : List Γ) :
  (List_val.mk val l).map f = List_val.mk val' (l.map f) := rfl

@[simp] theorem List_val.head_map {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : specified_pointed_map Γ Γ' val val') (l : List_val Γ val) : (l.map f).head = f l.head :=
begin
  conv {to_lhs, rw [← List_val.cons_head_tail l]},
  exact quotient.induction_on' l (λ a, rfl)
end

@[simp] theorem List_val.tail_map {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : specified_pointed_map Γ Γ' val val') (l : List_val Γ val) : (l.map f).tail = l.tail.map f :=
begin
  conv {to_lhs, rw [← List_val.cons_head_tail l]},
  exact quotient.induction_on' l (λ a, rfl)
end

@[simp] theorem List_val.map_cons {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : specified_pointed_map Γ Γ' val val') (l : List_val Γ val) (a : Γ) :
  (l.cons a).map f = (l.map f).cons (f a) :=
begin
  refine (List_val.cons_head_tail _).symm.trans _,
  simp only [List_val.head_map, List_val.head_cons, List_val.tail_map, List_val.tail_cons]
end

@[simp] theorem List_val.nth_map {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : specified_pointed_map Γ Γ' val val') (l : List_val Γ val) (n : ℕ) :
  (l.map f).nth n = f (l.nth n) :=
l.induction_on begin
  intro l,
  simp_rw [List_val.map_mk],
  simp_rw [List_val.nth_mk],
  rw [←List.nthd_map val (f : Γ -> Γ') l n],
  congr,
  exact f.2.symm,
end

/-- The `i`-th projection as a pointed map. -/
def proj {ι : Type*} {Γ : ι → Type*} (vals : Π i, Γ i) (i : ι) :
  specified_pointed_map (Π i, Γ i) (Γ i) vals (vals i) := ⟨λ a, a i, rfl⟩

theorem proj_map_nth {ι : Type*} {Γ : ι → Type*} (vals : Π i, Γ i) (i : ι)
  (L n) : (List_val.map (@proj ι Γ vals i) L).nth n = L.nth n i :=
by rw List_val.nth_map; refl

theorem List_val.map_modify_nth {Γ Γ'} {val : Γ} {val' : Γ'}
  (F : specified_pointed_map Γ Γ' val val') (f : Γ → Γ) (f' : Γ' → Γ')
  (H : ∀ x, F (f x) = f' (F x)) (n) (L : List_val Γ val) :
  (L.modify_nth f n).map F = (L.map F).modify_nth f' n :=
by induction n with n IH generalizing L; simp only [*,
  List_val.head_map, List_val.modify_nth, List_val.map_cons, List_val.tail_map]

/-- Append a List on the left side of a List_val. -/
@[simp] def List_val.append {Γ} {val : Γ} : List Γ → List_val Γ val → List_val Γ val
| [] L := L
| (a :: l) L := List_val.cons a (List_val.append l L)

@[simp] theorem List_val.append_mk {Γ} {val : Γ} (l₁ l₂ : List Γ) :
  List_val.append l₁ (List_val.mk val l₂) = List_val.mk val (l₁ ++ l₂) :=
by induction l₁; simp only [*,
     List_val.append, List.nil_append, List.cons_append, List_val.cons_mk]

theorem List_val.append_assoc {Γ} {val : Γ} (l₁ l₂ : List Γ) (l₃ : List_val Γ val) :
  List_val.append (l₁ ++ l₂) l₃ = List_val.append l₁ (List_val.append l₂ l₃) :=
l₃.induction_on $ by intro; simp only [List_val.append_mk, List.append_assoc]

/-- The `bind` function on Lists is well defined on `List_val`s provided that the default element
is sent to a sequence of default elements. -/
def List_val.bind {Γ Γ'} {val : Γ} (val' : Γ')
  (l : List_val Γ val) (f : Γ → List Γ')
  (hf : ∃ n, f val = List.replicate val' n) : List_val Γ' val' :=
l.lift_on (λ l, List_val.mk val' (List.bind l f)) begin
  rintro l _ ⟨i, rfl⟩, cases hf with n e, refine quotient.sound' (or.inl ⟨i * n, _⟩),
  rw [List.bind_append, mul_comm], congr,
  induction i with i IH, refl,
  simp only [IH, e, List.replicate_add, nat.mul_succ, add_comm, List.replicate_succ, List.cons_bind],
end

@[simp] lemma List_val.bind_mk {Γ Γ'} (val : Γ) (val' : Γ')
  (l : List Γ) (f : Γ → List Γ') (hf) :
  (List_val.mk val l).bind val' f hf = List_val.mk val' (l.bind f) := rfl

@[simp] lemma List_val.cons_bind {Γ Γ'} {val : Γ} {val' : Γ'}
  (a : Γ) (l : List_val Γ val) (f : Γ → List Γ') (hf) :
  (l.cons a).bind val' f hf = (l.bind val' f hf).append (f a) :=
l.induction_on $ by intro; simp only [List_val.append_mk,
  List_val.bind_mk, List_val.cons_mk, List.cons_bind]


section List_blank

/-- A `List_blank Γ` is a quotient of `List Γ` by extension by blanks at the end. This is used to
represent half-tapes of a Turing machine, so that we can pretend that the List continues
infinitely with blanks. -/
def List_blank (Γ) [inhabited Γ] := List_val Γ default

instance List_blank.inhabited {Γ} [inhabited Γ] : inhabited (List_blank Γ) := ⟨quotient.mk' []⟩
instance List_blank.has_emptyc {Γ} [inhabited Γ] : has_emptyc (List_blank Γ) := ⟨quotient.mk' []⟩

/-- The quotient map turning a `List` into a `List_blank`. -/
def List_blank.mk {Γ} [inhabited Γ] : List Γ → List_blank Γ := List_val.mk default

@[elab_as_eliminator]
protected lemma List_blank.induction_on {Γ} [inhabited Γ]
  {p : List_blank Γ → Prop} (q : List_blank Γ)
  (h : ∀ a, p (List_blank.mk a)) : p q := quotient.induction_on' q h

/-- The head of a `List_blank` is well defined. -/
def List_blank.head {Γ} [inhabited Γ] (l : List_blank Γ) : Γ := List_val.head l

@[simp] theorem List_blank.head_mk {Γ} [inhabited Γ] (l : List Γ) :
  List_blank.head (List_blank.mk l) = l.head :=
begin
  cases l,
  { simp only [List_blank.mk, List.head],
    refl, },
  { simp only [List.head_cons],
    refl, },
end

/-- The tail of a `List_blank` is well defined (up to the tail of blanks). -/
def List_blank.tail {Γ} [inhabited Γ] (l : List_blank Γ) : List_blank Γ := List_val.tail l

@[simp] theorem List_blank.tail_mk {Γ} [inhabited Γ] (l : List Γ) :
  List_blank.tail (List_blank.mk l) = List_blank.mk l.tail := rfl

/-- We can cons an element onto a `List_blank`. -/
def List_blank.cons {Γ} [inhabited Γ] (a : Γ) (l : List_blank Γ) : List_blank Γ := List_val.cons a l

@[simp] theorem List_blank.cons_mk {Γ} [inhabited Γ] (a : Γ) (l : List Γ) :
  List_blank.cons a (List_blank.mk l) = List_blank.mk (a :: l) := rfl

@[simp] theorem List_blank.head_cons {Γ} [inhabited Γ] (a : Γ) :
  ∀ (l : List_blank Γ), (l.cons a).head = a :=
quotient.ind' $ by exact λ l, rfl

@[simp] theorem List_blank.tail_cons {Γ} [inhabited Γ] (a : Γ) :
  ∀ (l : List_blank Γ), (l.cons a).tail = l :=
quotient.ind' $ by exact λ l, rfl

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `List` where
this only holds for nonempty Lists. -/
@[simp] theorem List_blank.cons_head_tail {Γ} [inhabited Γ] :
  ∀ (l : List_blank Γ), l.tail.cons l.head = l :=
quotient.ind' begin
  refine (λ l, quotient.sound' (or.inr _)),
  cases l, {exact ⟨1, rfl⟩}, {refl},
end

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `List` where
this only holds for nonempty Lists. -/
theorem List_blank.exists_cons {Γ} [inhabited Γ] (l : List_blank Γ) :
  ∃ a l', l = List_blank.cons a l' :=
⟨_, _, (List_blank.cons_head_tail _).symm⟩

/-- The n-th element of a `List_blank` is well defined for all `n : ℕ`, unlike in a `List`. -/
def List_blank.nth {Γ} [inhabited Γ] (l : List_blank Γ) (n : ℕ) : Γ := List_val.nth l n

@[simp] theorem List_blank.nth_mk {Γ} [inhabited Γ] (l : List Γ) (n : ℕ) :
  (List_blank.mk l).nth n = l.inth n := rfl

@[simp] theorem List_blank.nth_zero {Γ} [inhabited Γ] (l : List_blank Γ) : l.nth 0 = l.head :=
List_val.nth_zero l

@[simp] theorem List_blank.nth_succ {Γ} [inhabited Γ] (l : List_blank Γ) (n : ℕ) :
  l.nth (n + 1) = l.tail.nth n :=
List_val.nth_succ l n

@[ext] theorem List_blank.ext {Γ} [inhabited Γ] {L₁ L₂ : List_blank Γ} :
  (∀ i, L₁.nth i = L₂.nth i) → L₁ = L₂ :=
List_val.ext

/-- Apply a function to a value stored at the nth position of the List. -/
def List_blank.modify_nth {Γ} [inhabited Γ] (f : Γ → Γ) : ℕ → List_blank Γ → List_blank Γ :=
List_val.modify_nth f

@[simp] lemma List_blank.modify_nth_zero {Γ} [inhabited Γ] (f : Γ → Γ) (L : List_blank Γ) :
  L.modify_nth f 0 = L.tail.cons (f L.head) := rfl

@[simp] lemma List_blank.modify_nth_cons {Γ} [inhabited Γ] (f : Γ → Γ) (n : ℕ) (L : List_blank Γ) :
  L.modify_nth f (n+1) = (L.tail.modify_nth n).cons L.head := rfl

@[simp] lemma List_blank.modify_nth_zero {Γ} [inhabited Γ] (f : Γ → Γ) (L : List_blank Γ) :
  L.modify_nth f 0 = L.tail.cons (f L.head) := rfl

@[simp] lemma List_blank.modify_nth_cons {Γ} [inhabited Γ] (f : Γ → Γ) (n : ℕ) (L : List_blank Γ) :
  L.modify_nth f (n+1) = (L.tail.modify_nth f n).cons L.head := rfl

theorem List_blank.nth_modify_nth {Γ} [inhabited Γ] (f : Γ → Γ) (n i) (L : List_blank Γ) :
  (L.modify_nth f n).nth i = if i = n then f (L.nth i) else L.nth i :=
List_val.nth_modify_nth f n i L

/-- A pointed map of `inhabited` types is a map that sends one default value to the other. -/
def {u v} pointed_map (Γ : Type u) (Γ' : Type v)
  [inhabited Γ] [inhabited Γ'] : Type (max u v) :=
specified_pointed_map Γ Γ' default default

instance {Γ Γ'} [inhabited Γ] [inhabited Γ'] : inhabited (pointed_map Γ Γ') :=
⟨⟨default, rfl⟩⟩

instance {Γ Γ'} [inhabited Γ] [inhabited Γ'] : has_coe_to_fun (pointed_map Γ Γ') (λ _, Γ → Γ') :=
⟨specified_pointed_map.f⟩

-- @[simp] theorem pointed_map.mk_val {Γ Γ'} [inhabited Γ] [inhabited Γ']
--   (f : Γ → Γ') (pt) : (pointed_map.mk f pt : Γ → Γ') = f := rfl

@[simp] theorem pointed_map.map_pt {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') : f default = default := specified_pointed_map.map_pt f

@[simp] theorem pointed_map.head_map {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : List Γ) : (l.map f).head = f l.head :=
by cases l; [exact (pointed_map.map_pt f).symm, refl]

/-- The `map` function on Lists is well defined on `List_blank`s provided that the map is
pointed. -/
def List_blank.map {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : List_blank Γ) : List_blank Γ' := List_val.map f l

@[simp] theorem List_blank.map_mk {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : List Γ) : (List_blank.mk l).map f = List_blank.mk (l.map f) := rfl

@[simp] theorem List_blank.head_map {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : List_blank Γ) : (l.map f).head = f l.head := List_val.head_map f l

@[simp] theorem List_blank.tail_map {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : List_blank Γ) : (l.map f).tail = l.tail.map f := List_val.tail_map f l

@[simp] theorem List_blank.map_cons {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : List_blank Γ) (a : Γ) : (l.cons a).map f = (l.map f).cons (f a) :=
List_val.map_cons f l a

@[simp] theorem List_blank.nth_map {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : List_blank Γ) (n : ℕ) : (l.map f).nth n = f (l.nth n) :=
List_val.nth_map f l n

/-- The `i`-th projection as a pointed map. -/
def pointed_map_proj {ι : Type*} {Γ : ι → Type*} [∀ i, inhabited (Γ i)] (i : ι) :
  pointed_map (∀ i, Γ i) (Γ i) := ⟨λ a, a i, rfl⟩

theorem pointed_map_proj_map_nth {ι : Type*} {Γ : ι → Type*} [∀ i, inhabited (Γ i)] (i : ι)
  (L n) : (List_blank.map (@pointed_map_proj ι Γ _ i) L).nth n = L.nth n i :=
by rw List_blank.nth_map; refl

theorem List_blank.map_modify_nth {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (F : pointed_map Γ Γ') (f : Γ → Γ) (f' : Γ' → Γ')
  (H : ∀ x, F (f x) = f' (F x)) (n) (L : List_blank Γ) :
  (L.modify_nth f n).map F = (L.map F).modify_nth f' n :=
List_val.map_modify_nth F f f' H n L

/-- Append a List on the left side of a List_blank. -/
@[simp] def List_blank.append {Γ} [inhabited Γ] : List Γ → List_blank Γ → List_blank Γ :=
List_val.append

@[simp] theorem List_blank.append_mk {Γ} [inhabited Γ] (l₁ l₂ : List Γ) :
  List_blank.append l₁ (List_blank.mk l₂) = List_blank.mk (l₁ ++ l₂) :=
List_val.append_mk l₁ l₂

theorem List_blank.append_assoc {Γ} [inhabited Γ] (l₁ l₂ : List Γ) (l₃ : List_blank Γ) :
  List_blank.append (l₁ ++ l₂) l₃ = List_blank.append l₁ (List_blank.append l₂ l₃) :=
List_val.append_assoc l₁ l₂ l₃

/-- The `bind` function on Lists is well defined on `List_blank`s provided that the default element
is sent to a sequence of default elements. -/
def List_blank.bind {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (l : List_blank Γ) (f : Γ → List Γ')
  (hf : ∃ n, f default = List.replicate default n) : List_blank Γ' :=
List_val.bind default l f hf

@[simp] lemma List_blank.bind_mk {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (l : List Γ) (f : Γ → List Γ') (hf) :
  (List_blank.mk l).bind f hf = List_blank.mk (l.bind f) := rfl

@[simp] lemma List_blank.cons_bind {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (a : Γ) (l : List_blank Γ) (f : Γ → List Γ') (hf) :
  (l.cons a).bind f hf = (l.bind f hf).append (f a) :=
List_val.cons_bind a l f hf

end List_blank
