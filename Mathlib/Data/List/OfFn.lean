/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Join
import Mathlib.Data.List.Pairwise

#align_import data.list.of_fn from "leanprover-community/mathlib"@"bf27744463e9620ca4e4ebe951fe83530ae6949b"

/-!
# Lists from functions

Theorems and lemmas for dealing with `List.ofFn`, which converts a function on `Fin n` to a list
of length `n`.

## Main Statements

The main statements pertain to lists generated using `List.ofFn`

- `List.length_ofFn`, which tells us the length of such a list
- `List.get?_ofFn`, which tells us the nth element of such a list
- `List.equivSigmaTuple`, which is an `Equiv` between lists and the functions that generate them
  via `List.ofFn`.
-/


universe u

variable {α : Type u}

open Nat

namespace List

#noalign list.length_of_fn_aux

/-- The length of a list converted from a function is the size of the domain. -/
@[simp]
theorem length_ofFn {n} (f : Fin n → α) : length (ofFn f) = n := by
  simp [ofFn]
  -- 🎉 no goals
#align list.length_of_fn List.length_ofFn

#noalign list.nth_of_fn_aux

--Porting note: new theorem
@[simp]
theorem get_ofFn {n} (f : Fin n → α) (i) : get (ofFn f) i = f (Fin.castIso (by simp) i) := by
                                                                               -- 🎉 no goals
  have := Array.getElem_ofFn f i (by simpa using i.2)
  -- ⊢ get (ofFn f) i = f (↑(Fin.castIso (_ : length (ofFn f) = n)) i)
  cases' i with i hi
  -- ⊢ get (ofFn f) { val := i, isLt := hi } = f (↑(Fin.castIso (_ : length (ofFn f …
  simp only [getElem, Array.get] at this
  -- ⊢ get (ofFn f) { val := i, isLt := hi } = f (↑(Fin.castIso (_ : length (ofFn f …
  simp only [Fin.castIso_mk]
  -- ⊢ get (ofFn f) { val := i, isLt := hi } = f { val := i, isLt := (_ : i < n) }
  rw [← this]
  -- ⊢ get (ofFn f) { val := i, isLt := hi } = get (Array.ofFn f).data { val := i,  …
  congr <;> simp [ofFn]
            -- 🎉 no goals
            -- 🎉 no goals
            -- 🎉 no goals

/-- The `n`th element of a list -/
@[simp]
theorem get?_ofFn {n} (f : Fin n → α) (i) : get? (ofFn f) i = ofFnNthVal f i :=
  if h : i < (ofFn f).length
  then by
    rw [get?_eq_get h, get_ofFn]
    -- ⊢ some (f (↑(Fin.castIso (_ : length (ofFn f) = n)) { val := i, isLt := h }))  …
    · simp at h; simp [ofFnNthVal, h]
      -- ⊢ some (f (↑(Fin.castIso (_ : length (ofFn f) = n)) { val := i, isLt := h✝ })) …
                 -- 🎉 no goals
  else by
    rw [ofFnNthVal, dif_neg] <;>
    -- ⊢ get? (ofFn f) i = none
    simpa using h
    -- 🎉 no goals
    -- 🎉 no goals
#align list.nth_of_fn List.get?_ofFn

set_option linter.deprecated false in
@[deprecated get_ofFn]
theorem nthLe_ofFn {n} (f : Fin n → α) (i : Fin n) :
    nthLe (ofFn f) i ((length_ofFn f).symm ▸ i.2) = f i := by
  simp [nthLe]
  -- 🎉 no goals
#align list.nth_le_of_fn List.nthLe_ofFn

set_option linter.deprecated false in
@[simp, deprecated get_ofFn]
theorem nthLe_ofFn' {n} (f : Fin n → α) {i : ℕ} (h : i < (ofFn f).length) :
    nthLe (ofFn f) i h = f ⟨i, length_ofFn f ▸ h⟩ :=
  nthLe_ofFn f ⟨i, length_ofFn f ▸ h⟩
#align list.nth_le_of_fn' List.nthLe_ofFn'

@[simp]
theorem map_ofFn {β : Type*} {n : ℕ} (f : Fin n → α) (g : α → β) :
    map g (ofFn f) = ofFn (g ∘ f) :=
  ext_get (by simp) fun i h h' => by simp
              -- 🎉 no goals
                                     -- 🎉 no goals
#align list.map_of_fn List.map_ofFn

--Porting note: we don't have Array' in mathlib4
-- /-- Arrays converted to lists are the same as `of_fn` on the indexing function of the array. -/
-- theorem array_eq_of_fn {n} (a : Array' n α) : a.toList = ofFn a.read :=
--   by
--   suffices ∀ {m h l}, DArray.revIterateAux a (fun i => cons) m h l =
--      ofFnAux (DArray.read a) m h l
--     from this
--   intros; induction' m with m IH generalizing l; · rfl
--   simp only [DArray.revIterateAux, of_fn_aux, IH]
-- #align list.array_eq_of_fn List.array_eq_of_fn

@[congr]
theorem ofFn_congr {m n : ℕ} (h : m = n) (f : Fin m → α) :
    ofFn f = ofFn fun i : Fin n => f (Fin.castIso h.symm i) := by
  subst h
  -- ⊢ ofFn f = ofFn fun i => f (↑(Fin.castIso (_ : m = m)) i)
  simp_rw [Fin.castIso_refl, OrderIso.refl_apply]
  -- 🎉 no goals
#align list.of_fn_congr List.ofFn_congr

/-- `ofFn` on an empty domain is the empty list. -/
@[simp]
theorem ofFn_zero (f : Fin 0 → α) : ofFn f = [] :=
  rfl
#align list.of_fn_zero List.ofFn_zero

@[simp]
theorem ofFn_succ {n} (f : Fin (succ n) → α) : ofFn f = f 0 :: ofFn fun i => f i.succ :=
  ext_get (by simp) (fun i hi₁ hi₂ => by
              -- 🎉 no goals
    cases i
    -- ⊢ get (ofFn f) { val := zero, isLt := hi₁ } = get (f 0 :: ofFn fun i => f (Fin …
    · simp
      -- 🎉 no goals
    · simp)
      -- 🎉 no goals
#align list.of_fn_succ List.ofFn_succ

theorem ofFn_succ' {n} (f : Fin (succ n) → α) :
    ofFn f = (ofFn fun i => f (Fin.castSucc i)).concat (f (Fin.last _)) := by
  induction' n with n IH
  -- ⊢ ofFn f = concat (ofFn fun i => f (Fin.castSucc i)) (f (Fin.last zero))
  · rw [ofFn_zero, concat_nil, ofFn_succ, ofFn_zero]
    -- ⊢ [f 0] = [f (Fin.last zero)]
    rfl
    -- 🎉 no goals
  · rw [ofFn_succ, IH, ofFn_succ, concat_cons, Fin.castSucc_zero]
    -- ⊢ f 0 :: concat (ofFn fun i => f (Fin.succ (Fin.castSucc i))) (f (Fin.succ (Fi …
    congr
    -- 🎉 no goals
#align list.of_fn_succ' List.ofFn_succ'

@[simp]
theorem ofFn_eq_nil_iff {n : ℕ} {f : Fin n → α} : ofFn f = [] ↔ n = 0 := by
  cases n <;> simp only [ofFn_zero, ofFn_succ, eq_self_iff_true, Nat.succ_ne_zero]
  -- ⊢ ofFn f = [] ↔ zero = 0
              -- 🎉 no goals
              -- 🎉 no goals
#align list.of_fn_eq_nil_iff List.ofFn_eq_nil_iff

theorem last_ofFn {n : ℕ} (f : Fin n → α) (h : ofFn f ≠ [])
    (hn : n - 1 < n := Nat.pred_lt <| ofFn_eq_nil_iff.not.mp h) :
    getLast (ofFn f) h = f ⟨n - 1, hn⟩ := by simp [getLast_eq_get]
                                             -- 🎉 no goals
#align list.last_of_fn List.last_ofFn

theorem last_ofFn_succ {n : ℕ} (f : Fin n.succ → α)
    (h : ofFn f ≠ [] := mt ofFn_eq_nil_iff.mp (Nat.succ_ne_zero _)) :
    getLast (ofFn f) h = f (Fin.last _) :=
  last_ofFn f h
#align list.last_of_fn_succ List.last_ofFn_succ

/-- Note this matches the convention of `List.ofFn_succ'`, putting the `Fin m` elements first. -/
theorem ofFn_add {m n} (f : Fin (m + n) → α) :
    List.ofFn f =
      (List.ofFn fun i => f (Fin.castAdd n i)) ++ List.ofFn fun j => f (Fin.natAdd m j) := by
  induction' n with n IH
  -- ⊢ ofFn f = (ofFn fun i => f (Fin.castAdd zero i)) ++ ofFn fun j => f (Fin.natA …
  · rw [ofFn_zero, append_nil, Fin.castAdd_zero]
    -- ⊢ ofFn f = ofFn fun i => f (Fin.cast (_ : m = m) i)
    rfl
    -- 🎉 no goals
  · rw [ofFn_succ', ofFn_succ', IH, append_concat]
    -- ⊢ concat ((ofFn fun i => f (Fin.castSucc (Fin.castAdd n i))) ++ ofFn fun j =>  …
    rfl
    -- 🎉 no goals
#align list.of_fn_add List.ofFn_add

@[simp]
theorem ofFn_fin_append {m n} (a : Fin m → α) (b : Fin n → α) :
    List.ofFn (Fin.append a b) = List.ofFn a ++ List.ofFn b := by
  simp_rw [ofFn_add, Fin.append_left, Fin.append_right]
  -- 🎉 no goals
#align list.of_fn_fin_append List.ofFn_fin_append

/-- This breaks a list of `m*n` items into `m` groups each containing `n` elements. -/
theorem ofFn_mul {m n} (f : Fin (m * n) → α) :
    List.ofFn f = List.join (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => f ⟨i * n + j,
    calc
      ↑i * n + j < (i + 1) * n := (add_lt_add_left j.prop _).trans_eq (add_one_mul (_ : ℕ) _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ i.prop⟩) := by
  induction' m with m IH
  -- ⊢ ofFn f = join (ofFn fun i => ofFn fun j => f { val := ↑i * n + ↑j, isLt := ( …
  · simp [ofFn_zero, zero_mul, ofFn_zero, join]
    -- 🎉 no goals
  · simp_rw [ofFn_succ', succ_mul, join_concat, ofFn_add, IH]
    -- ⊢ (join (ofFn fun i => ofFn fun j => f (↑(Fin.castIso (_ : m * n + n = succ m  …
    rfl
    -- 🎉 no goals
#align list.of_fn_mul List.ofFn_mul

/-- This breaks a list of `m*n` items into `n` groups each containing `m` elements. -/
theorem ofFn_mul' {m n} (f : Fin (m * n) → α) :
    List.ofFn f = List.join (List.ofFn fun i : Fin n => List.ofFn fun j : Fin m => f ⟨m * i + j,
    calc
      m * i + j < m * (i + 1) := (add_lt_add_left j.prop _).trans_eq (mul_add_one (_ : ℕ) _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ i.prop⟩) := by
  simp_rw [mul_comm m n, mul_comm m, ofFn_mul, Fin.castIso_mk]
  -- 🎉 no goals
#align list.of_fn_mul' List.ofFn_mul'

theorem ofFn_get : ∀ l : List α, (ofFn (get l)) = l
  | [] => rfl
  | a :: l => by
    rw [ofFn_succ]
    -- ⊢ (get (a :: l) 0 :: ofFn fun i => get (a :: l) (Fin.succ i)) = a :: l
    congr
    -- ⊢ (ofFn fun i => get (a :: l) (Fin.succ i)) = l
    exact ofFn_get l
    -- 🎉 no goals

set_option linter.deprecated false in
@[deprecated ofFn_get]
theorem ofFn_nthLe : ∀ l : List α, (ofFn fun i => nthLe l i i.2) = l :=
  ofFn_get
#align list.of_fn_nth_le List.ofFn_nthLe

-- not registered as a simp lemma, as otherwise it fires before `forall_mem_ofFn_iff` which
-- is much more useful
theorem mem_ofFn {n} (f : Fin n → α) (a : α) : a ∈ ofFn f ↔ a ∈ Set.range f := by
  simp only [mem_iff_get, Set.mem_range, get_ofFn]
  -- ⊢ (∃ n_1, f (↑(Fin.castIso (_ : length (ofFn f) = n)) n_1) = a) ↔ ∃ y, f y = a
  exact ⟨fun ⟨i, hi⟩ => ⟨Fin.castIso (by simp) i, hi⟩, fun ⟨i, hi⟩ => ⟨Fin.castIso (by simp) i, hi⟩⟩
  -- 🎉 no goals
#align list.mem_of_fn List.mem_ofFn

@[simp]
theorem forall_mem_ofFn_iff {n : ℕ} {f : Fin n → α} {P : α → Prop} :
    (∀ i ∈ ofFn f, P i) ↔ ∀ j : Fin n, P (f j) := by simp only [mem_ofFn, Set.forall_range_iff]
                                                     -- 🎉 no goals
#align list.forall_mem_of_fn_iff List.forall_mem_ofFn_iff

@[simp]
theorem ofFn_const : ∀ (n : ℕ) (c : α), (ofFn fun _ : Fin n => c) = replicate n c
  | 0, c => rfl
  | n+1, c => by rw [replicate, ← ofFn_const n]; simp
                 -- ⊢ (ofFn fun x => c) = c :: ofFn fun x => c
                                                 -- 🎉 no goals
#align list.of_fn_const List.ofFn_const

@[simp]
theorem ofFn_fin_repeat {m} (a : Fin m → α) (n : ℕ) :
    List.ofFn (Fin.repeat n a) = (List.replicate n (List.ofFn a)).join := by
  simp_rw [ofFn_mul, ← ofFn_const, Fin.repeat, Fin.modNat, add_comm,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Fin.is_lt _)]
#align list.of_fn_fin_repeat List.ofFn_fin_repeat

@[simp]
theorem pairwise_ofFn {R : α → α → Prop} {n} {f : Fin n → α} :
    (ofFn f).Pairwise R ↔ ∀ ⦃i j⦄, i < j → R (f i) (f j) := by
  simp only [pairwise_iff_get, (Fin.castIso (length_ofFn f)).surjective.forall, get_ofFn,
    OrderIso.lt_iff_lt]
#align list.pairwise_of_fn List.pairwise_ofFn

/-- Lists are equivalent to the sigma type of tuples of a given length. -/
@[simps]
def equivSigmaTuple : List α ≃ Σn, Fin n → α where
  toFun l := ⟨l.length, l.get⟩
  invFun f := List.ofFn f.2
  left_inv := List.ofFn_get
  right_inv := fun ⟨_, f⟩ =>
    Fin.sigma_eq_of_eq_comp_castIso (length_ofFn _) <| funext fun i => get_ofFn f i
#align list.equiv_sigma_tuple List.equivSigmaTuple
#align list.equiv_sigma_tuple_symm_apply List.equivSigmaTuple_symm_apply
#align list.equiv_sigma_tuple_apply_fst List.equivSigmaTuple_apply_fst
#align list.equiv_sigma_tuple_apply_snd List.equivSigmaTuple_apply_snd

/-- A recursor for lists that expands a list into a function mapping to its elements.

This can be used with `induction l using List.ofFnRec`. -/
@[elab_as_elim]
def ofFnRec {C : List α → Sort*} (h : ∀ (n) (f : Fin n → α), C (List.ofFn f)) (l : List α) : C l :=
  cast (congr_arg C l.ofFn_get) <|
    h l.length l.get
#align list.of_fn_rec List.ofFnRec

@[simp]
theorem ofFnRec_ofFn {C : List α → Sort*} (h : ∀ (n) (f : Fin n → α), C (List.ofFn f)) {n : ℕ}
    (f : Fin n → α) : @ofFnRec _ C h (List.ofFn f) = h _ f := by
  --Porting note: Old proof was
  -- equivSigmaTuple.rightInverse_symm.cast_eq (fun s => h s.1 s.2) ⟨n, f⟩
  have := (@equivSigmaTuple α).rightInverse_symm
  -- ⊢ ofFnRec h (ofFn f) = h n f
  dsimp [equivSigmaTuple] at this
  -- ⊢ ofFnRec h (ofFn f) = h n f
  have := this.cast_eq (fun s => h s.1 s.2) ⟨n, f⟩
  -- ⊢ ofFnRec h (ofFn f) = h n f
  dsimp only at this
  -- ⊢ ofFnRec h (ofFn f) = h n f
  rw [ofFnRec, ← this]
  -- 🎉 no goals
#align list.of_fn_rec_of_fn List.ofFnRec_ofFn

theorem exists_iff_exists_tuple {P : List α → Prop} :
    (∃ l : List α, P l) ↔ ∃ (n : _) (f : Fin n → α), P (List.ofFn f) :=
  equivSigmaTuple.symm.surjective.exists.trans Sigma.exists
#align list.exists_iff_exists_tuple List.exists_iff_exists_tuple

theorem forall_iff_forall_tuple {P : List α → Prop} :
    (∀ l : List α, P l) ↔ ∀ (n) (f : Fin n → α), P (List.ofFn f) :=
  equivSigmaTuple.symm.surjective.forall.trans Sigma.forall
#align list.forall_iff_forall_tuple List.forall_iff_forall_tuple

/-- `Fin.sigma_eq_iff_eq_comp_cast` may be useful to work with the RHS of this expression. -/
theorem ofFn_inj' {m n : ℕ} {f : Fin m → α} {g : Fin n → α} :
    ofFn f = ofFn g ↔ (⟨m, f⟩ : Σn, Fin n → α) = ⟨n, g⟩ :=
  Iff.symm <| equivSigmaTuple.symm.injective.eq_iff.symm
#align list.of_fn_inj' List.ofFn_inj'

/-- Note we can only state this when the two functions are indexed by defeq `n`. -/
theorem ofFn_injective {n : ℕ} : Function.Injective (ofFn : (Fin n → α) → List α) := fun f g h =>
  eq_of_heq $ by rw [ofFn_inj'] at h; cases h; rfl
                 -- ⊢ HEq f g
                                      -- ⊢ HEq f f
                                               -- 🎉 no goals
#align list.of_fn_injective List.ofFn_injective

/-- A special case of `List.ofFn_inj` for when the two functions are indexed by defeq `n`. -/
@[simp]
theorem ofFn_inj {n : ℕ} {f g : Fin n → α} : ofFn f = ofFn g ↔ f = g :=
  ofFn_injective.eq_iff
#align list.of_fn_inj List.ofFn_inj

end List
