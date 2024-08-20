/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Range

/-!
# Matrix and vector notation

This file defines notation for vectors and matrices. Given `a b c d : α`,
the notation allows us to write `![a, b, c, d] : Fin 4 → α`.
Nesting vectors gives coefficients of a matrix, so `![![a, b], ![c, d]] : Fin 2 → Fin 2 → α`.
In later files we introduce `!![a, b; c, d]` as notation for `Matrix.of ![![a, b], ![c, d]]`.

## Main definitions

* `vecEmpty` is the empty vector (or `0` by `n` matrix) `![]`
* `vecCons` prepends an entry to a vector, so `![a, b]` is `vecCons a (vecCons b vecEmpty)`

## Implementation notes

The `simp` lemmas require that one of the arguments is of the form `vecCons _ _`.
This ensures `simp` works with entries only when (some) entries are already given.
In other words, this notation will only appear in the output of `simp` if it
already appears in the input.

## Notations

The main new notation is `![a, b]`, which gets expanded to `vecCons a (vecCons b vecEmpty)`.

## Examples

Examples of usage can be found in the `test/matrix.lean` file.
-/


namespace Matrix

universe u

variable {α : Type u}

section MatrixNotation

/-- `![]` is the vector with no entries. -/
def vecEmpty : Fin 0 → α :=
  Fin.elim0

/-- `vecCons h t` prepends an entry `h` to a vector `t`.

The inverse functions are `vecHead` and `vecTail`.
The notation `![a, b, ...]` expands to `vecCons a (vecCons b ...)`.
-/
def vecCons {n : ℕ} (h : α) (t : Fin n → α) : Fin n.succ → α :=
  Fin.cons h t

/-- `![...]` notation is used to construct a vector `Fin n → α` using `Matrix.vecEmpty` and
`Matrix.vecCons`.

For instance, `![a, b, c] : Fin 3` is syntax for `vecCons a (vecCons b (vecCons c vecEmpty))`.

Note that this should not be used as syntax for `Matrix` as it generates a term with the wrong type.
The `!![a, b; c, d]` syntax (provided by `Matrix.matrixNotation`) should be used instead.
-/
syntax (name := vecNotation) "![" term,* "]" : term

macro_rules
  | `(![$term:term, $terms:term,*]) => `(vecCons $term ![$terms,*])
  | `(![$term:term]) => `(vecCons $term ![])
  | `(![]) => `(vecEmpty)

/-- Unexpander for the `![x, y, ...]` notation. -/
@[app_unexpander vecCons]
def vecConsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term ![$term2, $terms,*]) => `(![$term, $term2, $terms,*])
  | `($_ $term ![$term2]) => `(![$term, $term2])
  | `($_ $term ![]) => `(![$term])
  | _ => throw ()

/-- Unexpander for the `![]` notation. -/
@[app_unexpander vecEmpty]
def vecEmptyUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_:ident) => `(![])
  | _ => throw ()

/-- `vecHead v` gives the first entry of the vector `v` -/
def vecHead {n : ℕ} (v : Fin n.succ → α) : α :=
  v 0

/-- `vecTail v` gives a vector consisting of all entries of `v` except the first -/
def vecTail {n : ℕ} (v : Fin n.succ → α) : Fin n → α :=
  v ∘ Fin.succ

variable {m n : ℕ}

/-- Use `![...]` notation for displaying a vector `Fin n → α`, for example:

```
#eval ![1, 2] + ![3, 4] -- ![4, 6]
```
-/
instance _root_.PiFin.hasRepr [Repr α] : Repr (Fin n → α) where
  reprPrec f _ :=
    Std.Format.bracket "![" (Std.Format.joinSep
      ((List.finRange n).map fun n => repr (f n)) ("," ++ Std.Format.line)) "]"

end MatrixNotation

variable {m n o : ℕ} {m' n' o' : Type*}

theorem empty_eq (v : Fin 0 → α) : v = ![] :=
  Subsingleton.elim _ _

section Val

@[simp]
theorem head_fin_const (a : α) : (vecHead fun _ : Fin (n + 1) => a) = a :=
  rfl

@[simp]
theorem cons_val_zero (x : α) (u : Fin m → α) : vecCons x u 0 = x :=
  rfl

theorem cons_val_zero' (h : 0 < m.succ) (x : α) (u : Fin m → α) : vecCons x u ⟨0, h⟩ = x :=
  rfl

@[simp]
theorem cons_val_succ (x : α) (u : Fin m → α) (i : Fin m) : vecCons x u i.succ = u i := by
  simp [vecCons]

@[simp]
theorem cons_val_succ' {i : ℕ} (h : i.succ < m.succ) (x : α) (u : Fin m → α) :
    vecCons x u ⟨i.succ, h⟩ = u ⟨i, Nat.lt_of_succ_lt_succ h⟩ := by
  simp only [vecCons, Fin.cons, Fin.cases_succ']

@[simp]
theorem head_cons (x : α) (u : Fin m → α) : vecHead (vecCons x u) = x :=
  rfl

@[simp]
theorem tail_cons (x : α) (u : Fin m → α) : vecTail (vecCons x u) = u := by
  ext
  simp [vecTail]

@[simp]
theorem empty_val' {n' : Type*} (j : n') : (fun i => (![] : Fin 0 → n' → α) i j) = ![] :=
  empty_eq _

@[simp]
theorem cons_head_tail (u : Fin m.succ → α) : vecCons (vecHead u) (vecTail u) = u :=
  Fin.cons_self_tail _

@[simp]
theorem range_cons (x : α) (u : Fin n → α) : Set.range (vecCons x u) = {x} ∪ Set.range u :=
  Set.ext fun y => by simp [Fin.exists_fin_succ, eq_comm]

@[simp]
theorem range_empty (u : Fin 0 → α) : Set.range u = ∅ :=
  Set.range_eq_empty _

-- @[simp] -- Porting note (#10618): simp can prove this
theorem range_cons_empty (x : α) (u : Fin 0 → α) : Set.range (Matrix.vecCons x u) = {x} := by
  rw [range_cons, range_empty, Set.union_empty]

-- @[simp] -- Porting note (#10618): simp can prove this (up to commutativity)
theorem range_cons_cons_empty (x y : α) (u : Fin 0 → α) :
    Set.range (vecCons x <| vecCons y u) = {x, y} := by
  rw [range_cons, range_cons_empty, Set.singleton_union]

@[simp]
theorem vecCons_const (a : α) : (vecCons a fun _ : Fin n => a) = fun _ => a :=
  funext <| Fin.forall_fin_succ.2 ⟨rfl, cons_val_succ _ _⟩

theorem vec_single_eq_const (a : α) : ![a] = fun _ => a :=
  let _ : Unique (Fin 1) := inferInstance
  funext <| Unique.forall_iff.2 rfl

/-- `![a, b, ...] 1` is equal to `b`.

  The simplifier needs a special lemma for length `≥ 2`, in addition to
  `cons_val_succ`, because `1 : Fin 1 = 0 : Fin 1`.
-/
@[simp]
theorem cons_val_one (x : α) (u : Fin m.succ → α) : vecCons x u 1 = vecHead u :=
  rfl

@[simp]
theorem cons_val_two (x : α) (u : Fin m.succ.succ → α) : vecCons x u 2 = vecHead (vecTail u) :=
  rfl

@[simp]
lemma cons_val_three (x : α) (u : Fin m.succ.succ.succ → α) :
    vecCons x u 3 = vecHead (vecTail (vecTail u)) :=
  rfl

@[simp]
lemma cons_val_four (x : α) (u : Fin m.succ.succ.succ.succ → α) :
    vecCons x u 4 = vecHead (vecTail (vecTail (vecTail u))) :=
  rfl

@[simp]
theorem cons_val_fin_one (x : α) (u : Fin 0 → α) : ∀ (i : Fin 1), vecCons x u i = x := by
  rw [Fin.forall_fin_one]
  rfl

theorem cons_fin_one (x : α) (u : Fin 0 → α) : vecCons x u = fun _ => x :=
  funext (cons_val_fin_one x u)

open Lean Qq in
protected instance _root_.PiFin.toExpr [ToLevel.{u}] [ToExpr α] (n : ℕ) : ToExpr (Fin n → α) :=
  have lu := toLevel.{u}
  have eα : Q(Type $lu) := toTypeExpr α
  have toTypeExpr := q(Fin $n → $eα)
  match n with
  | 0 => { toTypeExpr, toExpr := fun _ => q(@vecEmpty $eα) }
  | n + 1 =>
    { toTypeExpr, toExpr := fun v =>
      have := PiFin.toExpr n
      have eh : Q($eα) := toExpr (vecHead v)
      have et : Q(Fin $n → $eα) := toExpr (vecTail v)
      q(vecCons $eh $et) }

-- Porting note: the next decl is commented out. TODO(eric-wieser)

-- /-- Convert a vector of pexprs to the pexpr constructing that vector. -/
-- unsafe def _root_.pi_fin.to_pexpr : ∀ {n}, (Fin n → pexpr) → pexpr
--   | 0, v => ``(![])
--   | n + 1, v => ``(vecCons $(v 0) $(_root_.pi_fin.to_pexpr <| vecTail v))

/-! ### `bit0` and `bit1` indices
The following definitions and `simp` lemmas are used to allow
numeral-indexed element of a vector given with matrix notation to
be extracted by `simp` in Lean 3 (even when the numeral is larger than the
number of elements in the vector, which is taken modulo that number
of elements by virtue of the semantics of `bit0` and `bit1` and of
addition on `Fin n`).
-/


/-- `vecAppend ho u v` appends two vectors of lengths `m` and `n` to produce
one of length `o = m + n`. This is a variant of `Fin.append` with an additional `ho` argument,
which provides control of definitional equality for the vector length.

This turns out to be helpful when providing simp lemmas to reduce `![a, b, c] n`, and also means
that `vecAppend ho u v 0` is valid. `Fin.append u v 0` is not valid in this case because there is
no `Zero (Fin (m + n))` instance. -/
def vecAppend {α : Type*} {o : ℕ} (ho : o = m + n) (u : Fin m → α) (v : Fin n → α) : Fin o → α :=
  Fin.append u v ∘ Fin.cast ho

theorem vecAppend_eq_ite {α : Type*} {o : ℕ} (ho : o = m + n) (u : Fin m → α) (v : Fin n → α) :
    vecAppend ho u v = fun i : Fin o =>
      if h : (i : ℕ) < m then u ⟨i, h⟩ else v ⟨(i : ℕ) - m, by omega⟩ := by
  ext i
  rw [vecAppend, Fin.append, Function.comp_apply, Fin.addCases]
  congr with hi
  simp only [eq_rec_constant]
  rfl

-- Porting note: proof was `rfl`, so this is no longer a `dsimp`-lemma
-- Could become one again with change to `Nat.ble`:
-- https://github.com/leanprover-community/mathlib4/pull/1741/files/#r1083902351
@[simp]
theorem vecAppend_apply_zero {α : Type*} {o : ℕ} (ho : o + 1 = m + 1 + n) (u : Fin (m + 1) → α)
    (v : Fin n → α) : vecAppend ho u v 0 = u 0 :=
  dif_pos _

@[simp]
theorem empty_vecAppend (v : Fin n → α) : vecAppend n.zero_add.symm ![] v = v := by
  ext
  simp [vecAppend_eq_ite]

@[simp]
theorem cons_vecAppend (ho : o + 1 = m + 1 + n) (x : α) (u : Fin m → α) (v : Fin n → α) :
    vecAppend ho (vecCons x u) v = vecCons x (vecAppend (by omega) u v) := by
  ext i
  simp_rw [vecAppend_eq_ite]
  split_ifs with h
  · rcases i with ⟨⟨⟩ | i, hi⟩
    · simp
    · simp only [Nat.add_lt_add_iff_right, Fin.val_mk] at h
      simp [h]
  · rcases i with ⟨⟨⟩ | i, hi⟩
    · simp at h
    · rw [not_lt, Fin.val_mk, Nat.add_le_add_iff_right] at h
      simp [h, not_lt.2 h]

/-- `vecAlt0 v` gives a vector with half the length of `v`, with
only alternate elements (even-numbered). -/
def vecAlt0 (hm : m = n + n) (v : Fin m → α) (k : Fin n) : α := v ⟨(k : ℕ) + k, by omega⟩

/-- `vecAlt1 v` gives a vector with half the length of `v`, with
only alternate elements (odd-numbered). -/
def vecAlt1 (hm : m = n + n) (v : Fin m → α) (k : Fin n) : α :=
  v ⟨(k : ℕ) + k + 1, hm.symm ▸ Nat.add_succ_lt_add k.2 k.2⟩

section bits

theorem vecAlt0_vecAppend (v : Fin n → α) :
    vecAlt0 rfl (vecAppend rfl v v) = v ∘ (fun n ↦ n + n) := by
  ext i
  simp_rw [Function.comp, vecAlt0, vecAppend_eq_ite]
  split_ifs with h <;> congr
  · rw [Fin.val_mk] at h
    exact (Nat.mod_eq_of_lt h).symm
  · rw [Fin.val_mk, not_lt] at h
    simp only [Fin.ext_iff, Fin.val_add, Fin.val_mk, Nat.mod_eq_sub_mod h]
    refine (Nat.mod_eq_of_lt ?_).symm
    omega

theorem vecAlt1_vecAppend (v : Fin (n + 1) → α) :
    vecAlt1 rfl (vecAppend rfl v v) = v ∘ (fun n ↦ (n + n) + 1) := by
  ext i
  simp_rw [Function.comp, vecAlt1, vecAppend_eq_ite]
  cases n with
  | zero =>
    cases' i with i hi
    simp only [Nat.zero_add, Nat.lt_one_iff] at hi; subst i; rfl
  | succ n =>
    split_ifs with h <;> congr
    · simp [Nat.mod_eq_of_lt, h]
    · rw [Fin.val_mk, not_lt] at h
      simp only [Fin.ext_iff, Fin.val_add, Fin.val_mk, Nat.mod_add_mod, Fin.val_one,
        Nat.mod_eq_sub_mod h, show 1 % (n + 2) = 1 from Nat.mod_eq_of_lt (by omega)]
      refine (Nat.mod_eq_of_lt ?_).symm
      omega

@[simp]
theorem vecHead_vecAlt0 (hm : m + 2 = n + 1 + (n + 1)) (v : Fin (m + 2) → α) :
    vecHead (vecAlt0 hm v) = v 0 :=
  rfl

@[simp]
theorem vecHead_vecAlt1 (hm : m + 2 = n + 1 + (n + 1)) (v : Fin (m + 2) → α) :
    vecHead (vecAlt1 hm v) = v 1 := by simp [vecHead, vecAlt1]

@[simp]
theorem cons_vec_bit0_eq_alt0 (x : α) (u : Fin n → α) (i : Fin (n + 1)) :
    vecCons x u (i + i) = vecAlt0 rfl (vecAppend rfl (vecCons x u) (vecCons x u)) i := by
  rw [vecAlt0_vecAppend]; rfl

@[simp]
theorem cons_vec_bit1_eq_alt1 (x : α) (u : Fin n → α) (i : Fin (n + 1)) :
    vecCons x u ((i + i) + 1) = vecAlt1 rfl (vecAppend rfl (vecCons x u) (vecCons x u)) i := by
  rw [vecAlt1_vecAppend]; rfl

end bits

@[simp]
theorem cons_vecAlt0 (h : m + 1 + 1 = n + 1 + (n + 1)) (x y : α) (u : Fin m → α) :
    vecAlt0 h (vecCons x (vecCons y u)) = vecCons x (vecAlt0 (by omega) u) := by
  ext i
  simp_rw [vecAlt0]
  rcases i with ⟨⟨⟩ | i, hi⟩
  · rfl
  · simp only [← Nat.add_assoc, Nat.add_right_comm, cons_val_succ',
      cons_vecAppend, Nat.add_eq, vecAlt0]

-- Although proved by simp, extracting element 8 of a five-element
-- vector does not work by simp unless this lemma is present.
@[simp]
theorem empty_vecAlt0 (α) {h} : vecAlt0 h (![] : Fin 0 → α) = ![] := by
  simp [eq_iff_true_of_subsingleton]

@[simp]
theorem cons_vecAlt1 (h : m + 1 + 1 = n + 1 + (n + 1)) (x y : α) (u : Fin m → α) :
    vecAlt1 h (vecCons x (vecCons y u)) = vecCons y (vecAlt1 (by omega) u) := by
  ext i
  simp_rw [vecAlt1]
  rcases i with ⟨⟨⟩ | i, hi⟩
  · rfl
  · simp [vecAlt1, Nat.add_right_comm, ← Nat.add_assoc]

-- Although proved by simp, extracting element 9 of a five-element
-- vector does not work by simp unless this lemma is present.
@[simp]
theorem empty_vecAlt1 (α) {h} : vecAlt1 h (![] : Fin 0 → α) = ![] := by
  simp [eq_iff_true_of_subsingleton]

end Val

lemma const_fin1_eq (x : α) : (fun _ : Fin 1 => x) = ![x] :=
  (cons_fin_one x _).symm

end Matrix
