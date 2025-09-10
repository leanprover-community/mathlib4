/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Lists from functions

Theorems and lemmas for dealing with `List.ofFn`, which converts a function on `Fin n` to a list
of length `n`.

## Main Statements

The main statements pertain to lists generated using `List.ofFn`

- `List.get?_ofFn`, which tells us the nth element of such a list
- `List.equivSigmaTuple`, which is an `Equiv` between lists and the functions that generate them
  via `List.ofFn`.
-/

assert_not_exists Monoid

universe u

variable {α : Type u}

open Nat

namespace List

theorem get_ofFn {n} (f : Fin n → α) (i) : get (ofFn f) i = f (Fin.cast (by simp) i) := by
  simp; congr

@[simp]
theorem map_ofFn {β : Type*} {n : ℕ} (f : Fin n → α) (g : α → β) :
    map g (ofFn f) = ofFn (g ∘ f) :=
  ext_get (by simp) fun i h h' => by simp

/-- Useful if `rw [← map_ofFn]` complains that `g ∘ f` is not the same as `fun i => g (f i)`. -/
theorem ofFn_comp' {β : Type*} {n : ℕ} (f : Fin n → α) (g : α → β) :
    ofFn (fun i => g (f i)) = map g (ofFn f) :=
  (map_ofFn f g).symm

@[congr]
theorem ofFn_congr {m n : ℕ} (h : m = n) (f : Fin m → α) :
    ofFn f = ofFn fun i : Fin n => f (Fin.cast h.symm i) := by
  subst h
  simp_rw [Fin.cast_refl, id]

theorem ofFn_succ' {n} (f : Fin (succ n) → α) :
    ofFn f = (ofFn fun i => f (Fin.castSucc i)).concat (f (Fin.last _)) := by
  induction n with
  | zero => rw [ofFn_zero, concat_nil, ofFn_succ, ofFn_zero]; rfl
  | succ n IH => rw [ofFn_succ, IH, ofFn_succ, concat_cons, Fin.castSucc_zero]; congr

@[simp]
theorem ofFn_fin_append {m n} (a : Fin m → α) (b : Fin n → α) :
    List.ofFn (Fin.append a b) = List.ofFn a ++ List.ofFn b := by
  simp_rw [ofFn_add]
  simp [Fin.append_left', Fin.append_right]

/-- This breaks a list of `m*n` items into `m` groups each containing `n` elements. -/
theorem ofFn_mul {m n} (f : Fin (m * n) → α) :
    List.ofFn f = List.flatten (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => f ⟨i * n + j,
    calc
      ↑i * n + j < (i + 1) * n :=
        (Nat.add_lt_add_left j.prop _).trans_eq (by rw [Nat.add_mul, Nat.one_mul])
      _ ≤ _ := Nat.mul_le_mul_right _ i.prop⟩) := by
  induction m with
  | zero => simp [ofFn_zero, Nat.zero_mul, ofFn_zero]
  | succ m IH =>
    simp_rw [ofFn_succ', succ_mul]
    simp [ofFn_add, IH]
    rfl

/-- This breaks a list of `m*n` items into `n` groups each containing `m` elements. -/
theorem ofFn_mul' {m n} (f : Fin (m * n) → α) :
    List.ofFn f = List.flatten (List.ofFn fun i : Fin n => List.ofFn fun j : Fin m => f ⟨m * i + j,
    calc
      m * i + j < m * (i + 1) :=
        (Nat.add_lt_add_left j.prop _).trans_eq (by rw [Nat.mul_add, Nat.mul_one])
      _ ≤ _ := Nat.mul_le_mul_left _ i.prop⟩) := by simp_rw [m.mul_comm, ofFn_mul, Fin.cast_mk]

@[simp]
theorem ofFn_get : ∀ l : List α, (ofFn (get l)) = l
  | [] => by rw [ofFn_zero]
  | a :: l => by
    rw [ofFn_succ]
    congr
    exact ofFn_get l

@[simp]
theorem ofFn_getElem : ∀ l : List α, (ofFn (fun i : Fin l.length => l[(i : Nat)])) = l
  | [] => by rw [ofFn_zero]
  | a :: l => by
    rw [ofFn_succ]
    congr
    exact ofFn_get l

@[simp]
theorem ofFn_getElem_eq_map {β : Type*} (l : List α) (f : α → β) :
    ofFn (fun i : Fin l.length => f <| l[(i : Nat)]) = l.map f := by
  rw [← Function.comp_def, ← map_ofFn, ofFn_getElem]

-- Note there is a now another `mem_ofFn` defined in Lean, with an existential on the RHS,
-- which is marked as a simp lemma.
theorem mem_ofFn' {n} (f : Fin n → α) (a : α) : a ∈ ofFn f ↔ a ∈ Set.range f := by grind

theorem forall_mem_ofFn_iff {n : ℕ} {f : Fin n → α} {P : α → Prop} :
    (∀ i ∈ ofFn f, P i) ↔ ∀ j : Fin n, P (f j) := by simp

@[simp]
theorem ofFn_const : ∀ (n : ℕ) (c : α), (ofFn fun _ : Fin n => c) = replicate n c
  | 0, c => by rw [ofFn_zero, replicate_zero]
  | n + 1, c => by rw [replicate, ← ofFn_const n]; simp

@[simp]
theorem ofFn_fin_repeat {m} (a : Fin m → α) (n : ℕ) :
    List.ofFn (Fin.repeat n a) = (List.replicate n (List.ofFn a)).flatten := by
  simp_rw [ofFn_mul, ← ofFn_const, Fin.repeat, Fin.modNat, Nat.add_comm,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Fin.is_lt _)]

@[simp]
theorem pairwise_ofFn {R : α → α → Prop} {n} {f : Fin n → α} :
    (ofFn f).Pairwise R ↔ ∀ ⦃i j⦄, i < j → R (f i) (f j) := by
  simp only [pairwise_iff_getElem, length_ofFn, List.getElem_ofFn,
    Fin.forall_iff,
    Fin.mk_lt_mk, forall_comm (α := (_ : Prop)) (β := ℕ)]

lemma getLast_ofFn_succ {n : ℕ} (f : Fin n.succ → α) :
    (ofFn f).getLast (mt ofFn_eq_nil_iff.1 (Nat.succ_ne_zero _)) = f (Fin.last _) :=
  getLast_ofFn _

lemma ofFn_cons {n} (a : α) (f : Fin n → α) : ofFn (Fin.cons a f) = a :: ofFn f := by
  rw [ofFn_succ]
  rfl

lemma find?_ofFn_eq_some {n} {f : Fin n → α} {p : α → Bool} {b : α} :
    (ofFn f).find? p = some b ↔ p b = true ∧ ∃ i, f i = b ∧ ∀ j < i, ¬(p (f j) = true) := by
  rw [find?_eq_some_iff_getElem]
  exact ⟨fun ⟨hpb, i, hi, hfb, h⟩ ↦
      ⟨hpb, ⟨⟨i, length_ofFn (f := f) ▸ hi⟩, by simpa using hfb, fun j hj ↦ by simpa using h j hj⟩⟩,
    fun ⟨hpb, i, hfb, h⟩ ↦
      ⟨hpb, ⟨i, (length_ofFn (f := f)).symm ▸ i.isLt, by simpa using hfb,
        fun j hj ↦ by simpa using h ⟨j, by omega⟩ (by simpa using hj)⟩⟩⟩

lemma find?_ofFn_eq_some_of_injective {n} {f : Fin n → α} {p : α → Bool} {i : Fin n}
    (h : Function.Injective f) :
    (ofFn f).find? p = some (f i) ↔ p (f i) = true ∧ ∀ j < i, ¬(p (f j) = true) := by
  simp only [find?_ofFn_eq_some, h.eq_iff, Bool.not_eq_true, exists_eq_left]

/-- Lists are equivalent to the sigma type of tuples of a given length. -/
@[simps]
def equivSigmaTuple : List α ≃ Σ n, Fin n → α where
  toFun l := ⟨l.length, l.get⟩
  invFun f := List.ofFn f.2
  left_inv := List.ofFn_get
  right_inv := fun ⟨_, f⟩ =>
    Fin.sigma_eq_of_eq_comp_cast length_ofFn <| funext fun i => get_ofFn f i

/-- A recursor for lists that expands a list into a function mapping to its elements.

This can be used with `induction l using List.ofFnRec`. -/
@[elab_as_elim]
def ofFnRec {C : List α → Sort*} (h : ∀ (n) (f : Fin n → α), C (List.ofFn f)) (l : List α) : C l :=
  cast (congr_arg C l.ofFn_get) <|
    h l.length l.get

@[simp]
theorem ofFnRec_ofFn {C : List α → Sort*} (h : ∀ (n) (f : Fin n → α), C (List.ofFn f)) {n : ℕ}
    (f : Fin n → α) : @ofFnRec _ C h (List.ofFn f) = h _ f :=
  equivSigmaTuple.rightInverse_symm.cast_eq (fun s => h s.1 s.2) ⟨n, f⟩

theorem exists_iff_exists_tuple {P : List α → Prop} :
    (∃ l : List α, P l) ↔ ∃ (n : _) (f : Fin n → α), P (List.ofFn f) :=
  equivSigmaTuple.symm.surjective.exists.trans Sigma.exists

theorem forall_iff_forall_tuple {P : List α → Prop} :
    (∀ l : List α, P l) ↔ ∀ (n) (f : Fin n → α), P (List.ofFn f) :=
  equivSigmaTuple.symm.surjective.forall.trans Sigma.forall

/-- `Fin.sigma_eq_iff_eq_comp_cast` may be useful to work with the RHS of this expression. -/
theorem ofFn_inj' {m n : ℕ} {f : Fin m → α} {g : Fin n → α} :
    ofFn f = ofFn g ↔ (⟨m, f⟩ : Σ n, Fin n → α) = ⟨n, g⟩ :=
  Iff.symm <| equivSigmaTuple.symm.injective.eq_iff.symm

/-- Note we can only state this when the two functions are indexed by defeq `n`. -/
theorem ofFn_injective {n : ℕ} : Function.Injective (ofFn : (Fin n → α) → List α) := fun f g h =>
  eq_of_heq <| by rw [ofFn_inj'] at h; cases h; rfl

/-- A special case of `List.ofFn_inj` for when the two functions are indexed by defeq `n`. -/
@[simp]
theorem ofFn_inj {n : ℕ} {f g : Fin n → α} : ofFn f = ofFn g ↔ f = g :=
  ofFn_injective.eq_iff

end List
