/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Bolton Bailey
-/
import data.fintype.basic
import data.pfun
import logic.function.iterate
import order.basic
import tactic.apply_fun

/-!
# Blanked Lists

This file defines a quotient type for lists which are equivalent up to extension by some specific
value. This is useful for Turing machine tapes, as well as a computable variant of
finitely-supported functions on ℕ.

## Main Definitions

The main definitions in this file are

* `list_val Γ val` - a quotient type over lists of `Γ` which are equivalent up to extension by `val`
* `list_blank Γ` - A `list_val` instantiation for inhabited types, using the default as the value

-/

/-- The `val_extends` partial order holds of `l₁` and `l₂` if `l₂` is obtained by adding
vals (`val : Γ`) to the end of `l₁`. -/
def val_extends {Γ} (val : Γ) (l₁ l₂ : list Γ) : Prop :=
∃ n, l₂ = l₁ ++ list.repeat val n

@[refl] theorem val_extends.refl {Γ} (val : Γ) (l : list Γ) : val_extends val l l :=
⟨0, by simp⟩

@[trans] theorem val_extends.trans {Γ} (val : Γ) {l₁ l₂ l₃ : list Γ} :
  val_extends val l₁ l₂ → val_extends val l₂ l₃ → val_extends val l₁ l₃ :=
by { rintro ⟨i, rfl⟩ ⟨j, rfl⟩, exact ⟨i+j, by simp [list.repeat_add]⟩ }

theorem val_extends.below_of_le {Γ} (val : Γ) {l l₁ l₂ : list Γ} :
  val_extends val l l₁ → val_extends val l l₂ →
  l₁.length ≤ l₂.length → val_extends val l₁ l₂ :=
begin
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩ h, use j - i,
  simp only [list.length_append, add_le_add_iff_left, list.length_repeat] at h,
  simp only [← list.repeat_add, add_tsub_cancel_of_le h, list.append_assoc],
end

/-- Any two extensions by val `l₁,l₂` of `l` have a common join (which can be taken to be the
longer of `l₁` and `l₂`). -/
def val_extends.above {Γ} (val : Γ) {l l₁ l₂ : list Γ}
  (h₁ : val_extends val l l₁) (h₂ : val_extends val l l₂) :
  {l' // val_extends val l₁ l' ∧ val_extends val l₂ l'} :=
if h : l₁.length ≤ l₂.length then
  ⟨l₂, h₁.below_of_le val h₂ h, val_extends.refl val _⟩
else
  ⟨l₁, val_extends.refl val _, h₂.below_of_le val h₁ (le_of_not_ge h)⟩

theorem val_extends.above_of_le {Γ} (val : Γ) {l l₁ l₂ : list Γ} :
  val_extends val l₁ l → val_extends val l₂ l →
  l₁.length ≤ l₂.length → val_extends val l₁ l₂ :=
begin
  rintro ⟨i, rfl⟩ ⟨j, e⟩ h, use i - j,
  refine list.append_right_cancel (e.symm.trans _),
  rw [list.append_assoc, ← list.repeat_add, tsub_add_cancel_of_le],
  apply_fun list.length at e,
  simp only [list.length_append, list.length_repeat] at e,
  rwa [← add_le_add_iff_left, e, add_le_add_iff_right]
end

/-- `val_rel` is the symmetric closure of `val_extends`, turning it into an equivalence
relation. Two lists are related by `val_rel` if one extends the other by vals. -/
def val_rel {Γ} (val : Γ) (l₁ l₂ : list Γ) : Prop :=
val_extends val l₁ l₂ ∨ val_extends val l₂ l₁

@[refl] theorem val_rel.refl {Γ} (val : Γ) (l : list Γ) : val_rel val l l :=
or.inl (val_extends.refl val _)

@[symm] theorem val_rel.symm {Γ} (val : Γ) {l₁ l₂ : list Γ} :
  val_rel val l₁ l₂ → val_rel val l₂ l₁ := or.symm

@[trans] theorem val_rel.trans {Γ} (val : Γ) {l₁ l₂ l₃ : list Γ} :
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

/-- Given two `val_rel` lists, there exists (constructively) a common join. -/
def val_rel.above {Γ} (val : Γ) {l₁ l₂ : list Γ} (h : val_rel val l₁ l₂) :
  {l // val_extends val l₁ l ∧ val_extends val l₂ l} :=
begin
  refine if hl : l₁.length ≤ l₂.length
    then ⟨l₂, or.elim h id (λ h', _), val_extends.refl val _⟩
    else ⟨l₁, val_extends.refl val _, or.elim h (λ h', _) id⟩,
  exact (val_extends.refl val _).above_of_le val h' hl,
  exact (val_extends.refl val _).above_of_le val h' (le_of_not_ge hl)
end

/-- Given two `val_rel` lists, there exists (constructively) a common meet. -/
def val_rel.below {Γ} (val : Γ) {l₁ l₂ : list Γ} (h : val_rel val l₁ l₂) :
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
def val_rel.setoid (Γ) (val : Γ) : setoid (list Γ) := ⟨_, val_rel.equivalence _ val⟩

/-- A `list_val Γ` is a quotient of `list Γ` by extension by vals at the end. This is used to
represent half-tapes of a Turing machine, so that we can pretend that the list continues
infinitely with vals. -/
def list_val (Γ) (val : Γ) := quotient (val_rel.setoid Γ val)

instance list_val.inhabited {Γ} (val : Γ) : inhabited (list_val Γ val) := ⟨quotient.mk' []⟩
instance list_val.has_emptyc {Γ} (val : Γ) : has_emptyc (list_val Γ val) := ⟨quotient.mk' []⟩

/-- A modified version of `quotient.lift_on'` specialized for `list_val`, with the stronger
precondition `val_extends` instead of `val_rel`. -/
@[elab_as_eliminator, reducible]
protected def list_val.lift_on {Γ} {val : Γ} {α} (l : list_val Γ val) (f : list Γ → α)
  (H : ∀ a b, val_extends val a b → f a = f b) : α :=
l.lift_on' f $ by rintro a b (h|h); [exact H _ _ h, exact (H _ _ h).symm]

/-- The quotient map turning a `list` into a `list_val`. -/
def list_val.mk {Γ} (val : Γ) : list Γ → list_val Γ val := quotient.mk'

@[elab_as_eliminator]
protected lemma list_val.induction_on {Γ} {val : Γ}
  {p : list_val Γ val → Prop} (q : list_val Γ val)
  (h : ∀ a, p (list_val.mk val a)) : p q := quotient.induction_on' q h

/-- The head of a `list_val` is well defined. -/
def list_val.head {Γ} {val : Γ} (l : list_val Γ val) : Γ :=
l.lift_on (list.headd val) begin
  rintro _ _ ⟨i, rfl⟩,
  cases a, {cases i; refl}, refl
end

/-- The head of a `list_val` is the defaulted head of a list that constructs it. -/
@[simp] theorem list_val.head_mk {Γ} (val : Γ) (l : list Γ) :
  list_val.head (list_val.mk val l) = l.headd val := rfl

/-- The tail of a `list_val` is well defined (up to the tail of vals). -/
def list_val.tail {Γ} {val : Γ} (l : list_val Γ val) : list_val Γ val :=
l.lift_on (λ l, list_val.mk val l.tail) begin
  rintro _ _ ⟨i, rfl⟩,
  refine quotient.sound' (or.inl _),
  cases a; [{cases i; [exact ⟨0, rfl⟩, exact ⟨i, rfl⟩]}, exact ⟨i, rfl⟩]
end

@[simp] theorem list_val.tail_mk {Γ} (val : Γ) (l : list Γ) :
  list_val.tail (list_val.mk val l) = list_val.mk val l.tail := rfl

/-- We can cons an element onto a `list_val`. -/
def list_val.cons {Γ} {val : Γ} (a : Γ) (l : list_val Γ val) : list_val Γ val :=
l.lift_on (λ l, list_val.mk val (list.cons a l)) begin
  rintro _ _ ⟨i, rfl⟩,
  exact quotient.sound' (or.inl ⟨i, rfl⟩),
end

@[simp] theorem list_val.cons_mk {Γ} (val : Γ) (a : Γ) (l : list Γ) :
  list_val.cons a (list_val.mk val l) = list_val.mk val (a :: l) := rfl

@[simp] theorem list_val.head_cons {Γ} (val : Γ) (a : Γ) :
  ∀ (l : list_val Γ val), (l.cons a).head = a :=
quotient.ind' $ by exact λ l, rfl

@[simp] theorem list_val.tail_cons {Γ} (val : Γ) (a : Γ) :
  ∀ (l : list_val Γ val), (l.cons a).tail = l :=
quotient.ind' $ by exact λ l, rfl

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `list` where
this only holds for nonempty lists. -/
@[simp] theorem list_val.cons_head_tail {Γ} {val : Γ} :
  ∀ (l : list_val Γ val), l.tail.cons l.head = l :=
quotient.ind' begin
  refine (λ l, quotient.sound' (or.inr _)),
  cases l, {exact ⟨1, rfl⟩}, {refl},
end

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `list` where
this only holds for nonempty lists. -/
theorem list_val.exists_cons {Γ} {val : Γ} (l : list_val Γ val) :
  ∃ a l', l = list_val.cons a l' :=
⟨_, _, (list_val.cons_head_tail _).symm⟩

/-- The n-th element of a `list_val` is well defined for all `n : ℕ`, unlike in a `list`. -/
def list_val.nth {Γ} {val : Γ} (l : list_val Γ val) (n : ℕ) : Γ :=
l.lift_on (λ l, list.nthd val l n) begin
  rintro l _ ⟨i, rfl⟩,
  simp only,
  cases lt_or_le n l.length with h h, {rw list.nthd_append _ _ _ _ h, },
  rw list.nthd_eq_default _ _ h,
  cases le_or_lt _ _ with h₂ h₂, {rw list.nthd_eq_default _ _ h₂},
  rw [list.nthd_eq_nth_le _ _ h₂, list.nth_le_append_right h, list.nth_le_repeat],
end

@[simp] theorem list_val.nth_mk {Γ} (val : Γ) (l : list Γ) (n : ℕ) :
  (list_val.mk val l).nth n = l.nthd val n := rfl

@[simp] theorem list_val.nth_zero {Γ} {val : Γ} (l : list_val Γ val) : l.nth 0 = l.head :=
begin
  conv {to_lhs, rw [← list_val.cons_head_tail l]},
  exact quotient.induction_on' l.tail (λ l, rfl)
end

@[simp] theorem list_val.nth_succ {Γ} {val : Γ} (l : list_val Γ val) (n : ℕ) :
  l.nth (n + 1) = l.tail.nth n :=
begin
  conv {to_lhs, rw [← list_val.cons_head_tail l]},
  exact quotient.induction_on' l.tail (λ l, rfl)
end

@[ext] theorem list_val.ext {Γ} {val : Γ} {L₁ L₂ : list_val Γ val} :
  (∀ i, L₁.nth i = L₂.nth i) → L₁ = L₂ :=
list_val.induction_on L₁ $ λ l₁, list_val.induction_on L₂ $ λ l₂ H,
begin
  wlog h : l₁.length ≤ l₂.length using l₁ l₂,
  swap, { exact (this $ λ i, (H i).symm).symm },
  refine quotient.sound' (or.inl ⟨l₂.length - l₁.length, _⟩),
  refine list.ext_le _ (λ i h h₂, eq.symm _),
  { simp only [add_tsub_cancel_of_le h, list.length_append, list.length_repeat] },
  simp only [list_val.nth_mk] at H,
  cases lt_or_le i l₁.length with h' h',
  { simp only [list.nth_le_append _ h', list.nth_le_nth h, list.nth_le_nth h',
               ←list.nthd_eq_nth_le _ val h, ←list.nthd_eq_nth_le _ val h', H], },
  { simp only [list.nth_le_append_right h', list.nth_le_repeat, ←list.nthd_eq_nth_le _ val h,
               ←H, list.nthd_eq_default _ val h'], }
end

/-- Apply a function to a value stored at the nth position of the list. -/
@[simp] def list_val.modify_nth {Γ} {val : Γ} (f : Γ → Γ) : ℕ → list_val Γ val → list_val Γ val
| 0     L := L.tail.cons (f L.head)
| (n+1) L := (L.tail.modify_nth n).cons L.head

theorem list_val.nth_modify_nth {Γ} {val : Γ} (f : Γ → Γ) (n i) (L : list_val Γ val) :
  (L.modify_nth f n).nth i = if i = n then f (L.nth i) else L.nth i :=
begin
  induction n with n IH generalizing i L,
  { cases i; simp only [list_val.nth_zero, if_true,
      list_val.head_cons, list_val.modify_nth, eq_self_iff_true,
      list_val.nth_succ, if_false, list_val.tail_cons] },
  { cases i,
    { rw if_neg (nat.succ_ne_zero _).symm,
      simp only [list_val.nth_zero, list_val.head_cons, list_val.modify_nth] },
    { simp only [IH, list_val.modify_nth, list_val.nth_succ, list_val.tail_cons] } }
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
  (f : specified_pointed_map Γ Γ' val val') (l : list Γ) : (l.map f).headd val' = f (l.headd val) :=
begin
  cases l; simp,
end

/-- The `map` function on lists is well defined on `list_val`s provided that the map is
pointed. -/
def list_val.map {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : specified_pointed_map Γ Γ' val val') (l : list_val Γ val) : list_val Γ' val' :=
l.lift_on (λ l, list_val.mk val' (list.map f l)) begin
  rintro l _ ⟨i, rfl⟩, refine quotient.sound' (or.inl ⟨i, _⟩),
  simp only [specified_pointed_map.map_pt, list.map_append, list.map_repeat],
end

@[simp] theorem list_val.map_mk {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : specified_pointed_map Γ Γ' val val') (l : list Γ) :
  (list_val.mk val l).map f = list_val.mk val' (l.map f) := rfl

@[simp] theorem list_val.head_map {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : specified_pointed_map Γ Γ' val val') (l : list_val Γ val) : (l.map f).head = f l.head :=
begin
  conv {to_lhs, rw [← list_val.cons_head_tail l]},
  exact quotient.induction_on' l (λ a, rfl)
end

@[simp] theorem list_val.tail_map {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : specified_pointed_map Γ Γ' val val') (l : list_val Γ val) : (l.map f).tail = l.tail.map f :=
begin
  conv {to_lhs, rw [← list_val.cons_head_tail l]},
  exact quotient.induction_on' l (λ a, rfl)
end

@[simp] theorem list_val.map_cons {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : specified_pointed_map Γ Γ' val val') (l : list_val Γ val) (a : Γ) :
  (l.cons a).map f = (l.map f).cons (f a) :=
begin
  refine (list_val.cons_head_tail _).symm.trans _,
  simp only [list_val.head_map, list_val.head_cons, list_val.tail_map, list_val.tail_cons]
end

@[simp] theorem list_val.nth_map {Γ Γ'} {val : Γ} {val' : Γ'}
  (f : specified_pointed_map Γ Γ' val val') (l : list_val Γ val) (n : ℕ) :
  (l.map f).nth n = f (l.nth n) :=
l.induction_on begin
  intro l,
  simp_rw [list_val.map_mk],
  simp_rw [list_val.nth_mk],
  rw [←list.nthd_map val (f : Γ -> Γ') l n],
  congr,
  exact f.2.symm,
end

/-- The `i`-th projection as a pointed map. -/
def proj {ι : Type*} {Γ : ι → Type*} (vals : Π i, Γ i) (i : ι) :
  specified_pointed_map (Π i, Γ i) (Γ i) vals (vals i) := ⟨λ a, a i, rfl⟩

theorem proj_map_nth {ι : Type*} {Γ : ι → Type*} (vals : Π i, Γ i) (i : ι)
  (L n) : (list_val.map (@proj ι Γ vals i) L).nth n = L.nth n i :=
by rw list_val.nth_map; refl

theorem list_val.map_modify_nth {Γ Γ'} {val : Γ} {val' : Γ'}
  (F : specified_pointed_map Γ Γ' val val') (f : Γ → Γ) (f' : Γ' → Γ')
  (H : ∀ x, F (f x) = f' (F x)) (n) (L : list_val Γ val) :
  (L.modify_nth f n).map F = (L.map F).modify_nth f' n :=
by induction n with n IH generalizing L; simp only [*,
  list_val.head_map, list_val.modify_nth, list_val.map_cons, list_val.tail_map]

/-- Append a list on the left side of a list_val. -/
@[simp] def list_val.append {Γ} {val : Γ} : list Γ → list_val Γ val → list_val Γ val
| [] L := L
| (a :: l) L := list_val.cons a (list_val.append l L)

@[simp] theorem list_val.append_mk {Γ} {val : Γ} (l₁ l₂ : list Γ) :
  list_val.append l₁ (list_val.mk val l₂) = list_val.mk val (l₁ ++ l₂) :=
by induction l₁; simp only [*,
     list_val.append, list.nil_append, list.cons_append, list_val.cons_mk]

theorem list_val.append_assoc {Γ} {val : Γ} (l₁ l₂ : list Γ) (l₃ : list_val Γ val) :
  list_val.append (l₁ ++ l₂) l₃ = list_val.append l₁ (list_val.append l₂ l₃) :=
l₃.induction_on $ by intro; simp only [list_val.append_mk, list.append_assoc]

/-- The `bind` function on lists is well defined on `list_val`s provided that the default element
is sent to a sequence of default elements. -/
def list_val.bind {Γ Γ'} {val : Γ} (val' : Γ')
  (l : list_val Γ val) (f : Γ → list Γ')
  (hf : ∃ n, f val = list.repeat val' n) : list_val Γ' val' :=
l.lift_on (λ l, list_val.mk val' (list.bind l f)) begin
  rintro l _ ⟨i, rfl⟩, cases hf with n e, refine quotient.sound' (or.inl ⟨i * n, _⟩),
  rw [list.bind_append, mul_comm], congr,
  induction i with i IH, refl,
  simp only [IH, e, list.repeat_add, nat.mul_succ, add_comm, list.repeat_succ, list.cons_bind],
end

@[simp] lemma list_val.bind_mk {Γ Γ'} (val : Γ) (val' : Γ')
  (l : list Γ) (f : Γ → list Γ') (hf) :
  (list_val.mk val l).bind val' f hf = list_val.mk val' (l.bind f) := rfl

@[simp] lemma list_val.cons_bind {Γ Γ'} {val : Γ} {val' : Γ'}
  (a : Γ) (l : list_val Γ val) (f : Γ → list Γ') (hf) :
  (l.cons a).bind val' f hf = (l.bind val' f hf).append (f a) :=
l.induction_on $ by intro; simp only [list_val.append_mk,
  list_val.bind_mk, list_val.cons_mk, list.cons_bind]


section list_blank

/-- A `list_blank Γ` is a quotient of `list Γ` by extension by blanks at the end. This is used to
represent half-tapes of a Turing machine, so that we can pretend that the list continues
infinitely with blanks. -/
def list_blank (Γ) [inhabited Γ] := list_val Γ default

instance list_blank.inhabited {Γ} [inhabited Γ] : inhabited (list_blank Γ) := ⟨quotient.mk' []⟩
instance list_blank.has_emptyc {Γ} [inhabited Γ] : has_emptyc (list_blank Γ) := ⟨quotient.mk' []⟩

/-- The quotient map turning a `list` into a `list_blank`. -/
def list_blank.mk {Γ} [inhabited Γ] : list Γ → list_blank Γ := list_val.mk default

@[elab_as_eliminator]
protected lemma list_blank.induction_on {Γ} [inhabited Γ]
  {p : list_blank Γ → Prop} (q : list_blank Γ)
  (h : ∀ a, p (list_blank.mk a)) : p q := quotient.induction_on' q h

/-- The head of a `list_blank` is well defined. -/
def list_blank.head {Γ} [inhabited Γ] (l : list_blank Γ) : Γ := list_val.head l

@[simp] theorem list_blank.head_mk {Γ} [inhabited Γ] (l : list Γ) :
  list_blank.head (list_blank.mk l) = l.head :=
begin
  cases l,
  { simp only [list_blank.mk, list.head],
    refl, },
  { simp only [list.head_cons],
    refl, },
end

/-- The tail of a `list_blank` is well defined (up to the tail of blanks). -/
def list_blank.tail {Γ} [inhabited Γ] (l : list_blank Γ) : list_blank Γ := list_val.tail l

@[simp] theorem list_blank.tail_mk {Γ} [inhabited Γ] (l : list Γ) :
  list_blank.tail (list_blank.mk l) = list_blank.mk l.tail := rfl

/-- We can cons an element onto a `list_blank`. -/
def list_blank.cons {Γ} [inhabited Γ] (a : Γ) (l : list_blank Γ) : list_blank Γ := list_val.cons a l

@[simp] theorem list_blank.cons_mk {Γ} [inhabited Γ] (a : Γ) (l : list Γ) :
  list_blank.cons a (list_blank.mk l) = list_blank.mk (a :: l) := rfl

@[simp] theorem list_blank.head_cons {Γ} [inhabited Γ] (a : Γ) :
  ∀ (l : list_blank Γ), (l.cons a).head = a :=
quotient.ind' $ by exact λ l, rfl

@[simp] theorem list_blank.tail_cons {Γ} [inhabited Γ] (a : Γ) :
  ∀ (l : list_blank Γ), (l.cons a).tail = l :=
quotient.ind' $ by exact λ l, rfl

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `list` where
this only holds for nonempty lists. -/
@[simp] theorem list_blank.cons_head_tail {Γ} [inhabited Γ] :
  ∀ (l : list_blank Γ), l.tail.cons l.head = l :=
quotient.ind' begin
  refine (λ l, quotient.sound' (or.inr _)),
  cases l, {exact ⟨1, rfl⟩}, {refl},
end

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `list` where
this only holds for nonempty lists. -/
theorem list_blank.exists_cons {Γ} [inhabited Γ] (l : list_blank Γ) :
  ∃ a l', l = list_blank.cons a l' :=
⟨_, _, (list_blank.cons_head_tail _).symm⟩

/-- The n-th element of a `list_blank` is well defined for all `n : ℕ`, unlike in a `list`. -/
def list_blank.nth {Γ} [inhabited Γ] (l : list_blank Γ) (n : ℕ) : Γ := list_val.nth l n

@[simp] theorem list_blank.nth_mk {Γ} [inhabited Γ] (l : list Γ) (n : ℕ) :
  (list_blank.mk l).nth n = l.inth n := rfl

@[simp] theorem list_blank.nth_zero {Γ} [inhabited Γ] (l : list_blank Γ) : l.nth 0 = l.head :=
list_val.nth_zero l

@[simp] theorem list_blank.nth_succ {Γ} [inhabited Γ] (l : list_blank Γ) (n : ℕ) :
  l.nth (n + 1) = l.tail.nth n :=
list_val.nth_succ l n

@[ext] theorem list_blank.ext {Γ} [inhabited Γ] {L₁ L₂ : list_blank Γ} :
  (∀ i, L₁.nth i = L₂.nth i) → L₁ = L₂ :=
list_val.ext

/-- Apply a function to a value stored at the nth position of the list. -/
def list_blank.modify_nth {Γ} [inhabited Γ] (f : Γ → Γ) : ℕ → list_blank Γ → list_blank Γ :=
list_val.modify_nth f

@[simp] lemma list_blank.modify_nth_zero {Γ} [inhabited Γ] (f : Γ → Γ) (L : list_blank Γ) :
  L.modify_nth f 0 = L.tail.cons (f L.head) := rfl

@[simp] lemma list_blank.modify_nth_cons {Γ} [inhabited Γ] (f : Γ → Γ) (n : ℕ) (L : list_blank Γ) :
  L.modify_nth f (n+1) = (L.tail.modify_nth n).cons L.head := rfl

@[simp] lemma list_blank.modify_nth_zero {Γ} [inhabited Γ] (f : Γ → Γ) (L : list_blank Γ) :
  L.modify_nth f 0 = L.tail.cons (f L.head) := rfl

@[simp] lemma list_blank.modify_nth_cons {Γ} [inhabited Γ] (f : Γ → Γ) (n : ℕ) (L : list_blank Γ) :
  L.modify_nth f (n+1) = (L.tail.modify_nth f n).cons L.head := rfl

theorem list_blank.nth_modify_nth {Γ} [inhabited Γ] (f : Γ → Γ) (n i) (L : list_blank Γ) :
  (L.modify_nth f n).nth i = if i = n then f (L.nth i) else L.nth i :=
list_val.nth_modify_nth f n i L

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
  (f : pointed_map Γ Γ') (l : list Γ) : (l.map f).head = f l.head :=
by cases l; [exact (pointed_map.map_pt f).symm, refl]

/-- The `map` function on lists is well defined on `list_blank`s provided that the map is
pointed. -/
def list_blank.map {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : list_blank Γ) : list_blank Γ' := list_val.map f l

@[simp] theorem list_blank.map_mk {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : list Γ) : (list_blank.mk l).map f = list_blank.mk (l.map f) := rfl

@[simp] theorem list_blank.head_map {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : list_blank Γ) : (l.map f).head = f l.head := list_val.head_map f l

@[simp] theorem list_blank.tail_map {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : list_blank Γ) : (l.map f).tail = l.tail.map f := list_val.tail_map f l

@[simp] theorem list_blank.map_cons {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : list_blank Γ) (a : Γ) : (l.cons a).map f = (l.map f).cons (f a) :=
list_val.map_cons f l a

@[simp] theorem list_blank.nth_map {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (f : pointed_map Γ Γ') (l : list_blank Γ) (n : ℕ) : (l.map f).nth n = f (l.nth n) :=
list_val.nth_map f l n

/-- The `i`-th projection as a pointed map. -/
def pointed_map_proj {ι : Type*} {Γ : ι → Type*} [∀ i, inhabited (Γ i)] (i : ι) :
  pointed_map (∀ i, Γ i) (Γ i) := ⟨λ a, a i, rfl⟩

theorem pointed_map_proj_map_nth {ι : Type*} {Γ : ι → Type*} [∀ i, inhabited (Γ i)] (i : ι)
  (L n) : (list_blank.map (@pointed_map_proj ι Γ _ i) L).nth n = L.nth n i :=
by rw list_blank.nth_map; refl

theorem list_blank.map_modify_nth {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (F : pointed_map Γ Γ') (f : Γ → Γ) (f' : Γ' → Γ')
  (H : ∀ x, F (f x) = f' (F x)) (n) (L : list_blank Γ) :
  (L.modify_nth f n).map F = (L.map F).modify_nth f' n :=
list_val.map_modify_nth F f f' H n L

/-- Append a list on the left side of a list_blank. -/
@[simp] def list_blank.append {Γ} [inhabited Γ] : list Γ → list_blank Γ → list_blank Γ :=
list_val.append

@[simp] theorem list_blank.append_mk {Γ} [inhabited Γ] (l₁ l₂ : list Γ) :
  list_blank.append l₁ (list_blank.mk l₂) = list_blank.mk (l₁ ++ l₂) :=
list_val.append_mk l₁ l₂

theorem list_blank.append_assoc {Γ} [inhabited Γ] (l₁ l₂ : list Γ) (l₃ : list_blank Γ) :
  list_blank.append (l₁ ++ l₂) l₃ = list_blank.append l₁ (list_blank.append l₂ l₃) :=
list_val.append_assoc l₁ l₂ l₃

/-- The `bind` function on lists is well defined on `list_blank`s provided that the default element
is sent to a sequence of default elements. -/
def list_blank.bind {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (l : list_blank Γ) (f : Γ → list Γ')
  (hf : ∃ n, f default = list.repeat default n) : list_blank Γ' :=
list_val.bind default l f hf

@[simp] lemma list_blank.bind_mk {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (l : list Γ) (f : Γ → list Γ') (hf) :
  (list_blank.mk l).bind f hf = list_blank.mk (l.bind f) := rfl

@[simp] lemma list_blank.cons_bind {Γ Γ'} [inhabited Γ] [inhabited Γ']
  (a : Γ) (l : list_blank Γ) (f : Γ → list Γ') (hf) :
  (l.cons a).bind f hf = (l.bind f hf).append (f a) :=
list_val.cons_bind a l f hf

end list_blank
