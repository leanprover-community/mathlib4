/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Vector
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Control.Applicative
import Mathlib.Control.Traversable.Basic

#align_import data.vector.basic from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# Additional theorems and definitions about the `Vector` type

This file introduces the infix notation `::ᵥ` for `Vector.cons`.
-/

set_option autoImplicit true


universe u

variable {n : ℕ}

namespace Vector

variable {α : Type*}

@[inherit_doc]
infixr:67 " ::ᵥ " => Vector.cons

attribute [simp] head_cons tail_cons

instance [Inhabited α] : Inhabited (Vector α n) :=
  ⟨ofFn default⟩

theorem toList_injective : Function.Injective (@toList α n) :=
  Subtype.val_injective
#align vector.to_list_injective Vector.toList_injective

/-- Two `v w : Vector α n` are equal iff they are equal at every single index. -/
@[ext]
theorem ext : ∀ {v w : Vector α n} (_ : ∀ m : Fin n, Vector.get v m = Vector.get w m), v = w
  | ⟨v, hv⟩, ⟨w, hw⟩, h =>
    Subtype.eq (List.ext_get (by rw [hv, hw]) fun m hm _ => h ⟨m, hv ▸ hm⟩)
                                 -- 🎉 no goals
#align vector.ext Vector.ext

/-- The empty `Vector` is a `Subsingleton`. -/
instance zero_subsingleton : Subsingleton (Vector α 0) :=
  ⟨fun _ _ => Vector.ext fun m => Fin.elim0 m⟩
#align vector.zero_subsingleton Vector.zero_subsingleton

@[simp]
theorem cons_val (a : α) : ∀ v : Vector α n, (a ::ᵥ v).val = a :: v.val
  | ⟨_, _⟩ => rfl
#align vector.cons_val Vector.cons_val

#align vector.cons_head Vector.head_cons
#align vector.cons_tail Vector.tail_cons

theorem eq_cons_iff (a : α) (v : Vector α n.succ) (v' : Vector α n) :
    v = a ::ᵥ v' ↔ v.head = a ∧ v.tail = v' :=
  ⟨fun h => h.symm ▸ ⟨head_cons a v', tail_cons a v'⟩, fun h =>
    _root_.trans (cons_head_tail v).symm (by rw [h.1, h.2])⟩
                                             -- 🎉 no goals
#align vector.eq_cons_iff Vector.eq_cons_iff

theorem ne_cons_iff (a : α) (v : Vector α n.succ) (v' : Vector α n) :
    v ≠ a ::ᵥ v' ↔ v.head ≠ a ∨ v.tail ≠ v' := by rw [Ne.def, eq_cons_iff a v v', not_and_or]
                                                  -- 🎉 no goals
#align vector.ne_cons_iff Vector.ne_cons_iff

theorem exists_eq_cons (v : Vector α n.succ) : ∃ (a : α) (as : Vector α n), v = a ::ᵥ as :=
  ⟨v.head, v.tail, (eq_cons_iff v.head v v.tail).2 ⟨rfl, rfl⟩⟩
#align vector.exists_eq_cons Vector.exists_eq_cons

@[simp]
theorem toList_ofFn : ∀ {n} (f : Fin n → α), toList (ofFn f) = List.ofFn f
  | 0, f => rfl
  | n + 1, f => by rw [ofFn, List.ofFn_succ, toList_cons, toList_ofFn]
                   -- 🎉 no goals
#align vector.to_list_of_fn Vector.toList_ofFn

@[simp]
theorem mk_toList : ∀ (v : Vector α n) (h), (⟨toList v, h⟩ : Vector α n) = v
  | ⟨_, _⟩, _ => rfl
#align vector.mk_to_list Vector.mk_toList


@[simp] theorem length_val (v : Vector α n) : v.val.length = n := v.2

-- porting notes: not used in mathlib and coercions done differently in Lean 4
-- @[simp]
-- theorem length_coe (v : Vector α n) :
--     ((coe : { l : List α // l.length = n } → List α) v).length = n :=
--   v.2
#noalign vector.length_coe

@[simp]
theorem toList_map {β : Type*} (v : Vector α n) (f : α → β) : (v.map f).toList = v.toList.map f :=
  by cases v; rfl
     -- ⊢ toList (map f { val := val✝, property := property✝ }) = List.map f (toList { …
              -- 🎉 no goals
#align vector.to_list_map Vector.toList_map

@[simp]
theorem head_map {β : Type*} (v : Vector α (n + 1)) (f : α → β) : (v.map f).head = f v.head := by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  -- ⊢ head (map f v) = f (head v)
  rw [h, map_cons, head_cons, head_cons]
  -- 🎉 no goals
#align vector.head_map Vector.head_map

@[simp]
theorem tail_map {β : Type*} (v : Vector α (n + 1)) (f : α → β) :
    (v.map f).tail = v.tail.map f := by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  -- ⊢ tail (map f v) = map f (tail v)
  rw [h, map_cons, tail_cons, tail_cons]
  -- 🎉 no goals
#align vector.tail_map Vector.tail_map

theorem get_eq_get (v : Vector α n) (i : Fin n) :
    v.get i = v.toList.get (Fin.castIso v.toList_length.symm i) :=
  rfl
#align vector.nth_eq_nth_le Vector.get_eq_get

-- porting notes: `nthLe` deprecated for `get`
@[deprecated get_eq_get]
theorem nth_eq_nthLe :
    ∀ (v : Vector α n) (i), get v i = v.toList.nthLe i.1 (by rw [toList_length]; exact i.2)
                                                             -- ⊢ ↑i < n
                                                                                 -- 🎉 no goals
  | ⟨_, _⟩, _ => rfl

@[simp]
theorem get_replicate (a : α) (i : Fin n) : (Vector.replicate n a).get i = a := by
  apply List.get_replicate
  -- 🎉 no goals
#align vector.nth_repeat Vector.get_replicate

@[simp]
theorem get_map {β : Type*} (v : Vector α n) (f : α → β) (i : Fin n) :
    (v.map f).get i = f (v.get i) := by
  cases v; simp [Vector.map, get_eq_get]; rfl
  -- ⊢ get (map f { val := val✝, property := property✝ }) i = f (get { val := val✝, …
           -- ⊢ f (List.get val✝ { val := ↑i, isLt := (_ : ↑i < List.length val✝) }) = f (Li …
                                          -- 🎉 no goals
#align vector.nth_map Vector.get_map

@[simp]
theorem map₂_nil (f : α → β → γ) : Vector.map₂ f nil nil = nil :=
  rfl

@[simp]
theorem map₂_cons (hd₁ : α) (tl₁ : Vector α n) (hd₂ : β) (tl₂ : Vector β n) (f : α → β → γ) :
    Vector.map₂ f (hd₁ ::ᵥ tl₁) (hd₂ ::ᵥ tl₂) = f hd₁ hd₂ ::ᵥ (Vector.map₂ f tl₁ tl₂) :=
  rfl

@[simp]
theorem get_ofFn {n} (f : Fin n → α) (i) : get (ofFn f) i = f i := by
  conv_rhs => erw [← List.get_ofFn f ⟨i, by simp⟩]
  -- ⊢ get (ofFn f) i = List.get (List.ofFn f) { val := ↑i, isLt := (_ : ↑i < List. …
  simp only [get_eq_get]
  -- ⊢ List.get (toList (ofFn f)) (↑(Fin.castIso (_ : n = List.length (toList (ofFn …
  congr <;> simp [Fin.heq_ext_iff]
  -- ⊢ toList (ofFn f) = List.ofFn f
            -- 🎉 no goals
            -- 🎉 no goals
#align vector.nth_of_fn Vector.get_ofFn

@[simp]
theorem ofFn_get (v : Vector α n) : ofFn (get v) = v := by
  rcases v with ⟨l, rfl⟩
  -- ⊢ ofFn (get { val := l, property := (_ : List.length l = List.length l) }) = { …
  apply toList_injective
  -- ⊢ toList (ofFn (get { val := l, property := (_ : List.length l = List.length l …
  dsimp
  -- ⊢ toList (ofFn (get { val := l, property := (_ : List.length l = List.length l …
  simpa only [toList_ofFn] using List.ofFn_get _
  -- 🎉 no goals
#align vector.of_fn_nth Vector.ofFn_get

/-- The natural equivalence between length-`n` vectors and functions from `Fin n`. -/
def _root_.Equiv.vectorEquivFin (α : Type*) (n : ℕ) : Vector α n ≃ (Fin n → α) :=
  ⟨Vector.get, Vector.ofFn, Vector.ofFn_get, fun f => funext <| Vector.get_ofFn f⟩
#align equiv.vector_equiv_fin Equiv.vectorEquivFin

theorem get_tail (x : Vector α n) (i) :
    x.tail.get i = x.get ⟨i.1 + 1, lt_tsub_iff_right.mp i.2⟩ := by
  cases' i with i ih; dsimp
  -- ⊢ get (tail x) { val := i, isLt := ih } = get x { val := ↑{ val := i, isLt :=  …
                      -- ⊢ get (tail x) { val := i, isLt := ih } = get x { val := i + 1, isLt := (_ : i …
  rcases x with ⟨_ | _, h⟩ <;> try rfl
  -- ⊢ get (tail { val := [], property := h }) { val := i, isLt := ih } = get { val …
                               -- ⊢ get (tail { val := [], property := h }) { val := i, isLt := ih } = get { val …
                               -- 🎉 no goals
  rw [List.length] at h
  -- ⊢ get (tail { val := [], property := h✝ }) { val := i, isLt := ih } = get { va …
  rw [←h] at ih
  -- ⊢ get (tail { val := [], property := h✝ }) { val := i, isLt := ih✝ } = get { v …
  contradiction
  -- 🎉 no goals
#align vector.nth_tail Vector.get_tail

@[simp]
theorem get_tail_succ : ∀ (v : Vector α n.succ) (i : Fin n), get (tail v) i = get v i.succ
  | ⟨a :: l, e⟩, ⟨i, h⟩ => by simp [get_eq_get]; rfl
                              -- ⊢ List.get (toList (tail { val := a :: l, property := e })) { val := i, isLt : …
                                                 -- 🎉 no goals
#align vector.nth_tail_succ Vector.get_tail_succ

@[simp]
theorem tail_val : ∀ v : Vector α n.succ, v.tail.val = v.val.tail
  | ⟨_ :: _, _⟩ => rfl
#align vector.tail_val Vector.tail_val

/-- The `tail` of a `nil` vector is `nil`. -/
@[simp]
theorem tail_nil : (@nil α).tail = nil :=
  rfl
#align vector.tail_nil Vector.tail_nil

/-- The `tail` of a vector made up of one element is `nil`. -/
@[simp]
theorem singleton_tail : ∀ (v : Vector α 1), v.tail = Vector.nil
  | ⟨[_], _⟩ => rfl
#align vector.singleton_tail Vector.singleton_tail

@[simp]
theorem tail_ofFn {n : ℕ} (f : Fin n.succ → α) : tail (ofFn f) = ofFn fun i => f i.succ :=
  (ofFn_get _).symm.trans <| by
    congr
    -- ⊢ get (tail (ofFn f)) = fun i => f (Fin.succ i)
    funext i
    -- ⊢ get (tail (ofFn f)) i = f (Fin.succ i)
    rw [get_tail, get_ofFn]
    -- ⊢ f { val := ↑i + 1, isLt := (_ : ↑i + 1 < Nat.succ n) } = f (Fin.succ i)
    rfl
    -- 🎉 no goals
#align vector.tail_of_fn Vector.tail_ofFn

@[simp]
theorem toList_empty (v : Vector α 0) : v.toList = [] :=
  List.length_eq_zero.mp v.2
#align vector.to_list_empty Vector.toList_empty

/-- The list that makes up a `Vector` made up of a single element,
retrieved via `toList`, is equal to the list of that single element. -/
@[simp]
theorem toList_singleton (v : Vector α 1) : v.toList = [v.head] := by
  rw [← v.cons_head_tail]
  -- ⊢ toList (head v ::ᵥ tail v) = [head (head v ::ᵥ tail v)]
  simp only [toList_cons, toList_nil, head_cons, eq_self_iff_true, and_self_iff, singleton_tail]
  -- 🎉 no goals
#align vector.to_list_singleton Vector.toList_singleton

@[simp]
theorem empty_toList_eq_ff (v : Vector α (n + 1)) : v.toList.isEmpty = false :=
  match v with
  | ⟨_ :: _, _⟩ => rfl
#align vector.empty_to_list_eq_ff Vector.empty_toList_eq_ff

theorem not_empty_toList (v : Vector α (n + 1)) : ¬v.toList.isEmpty := by
  simp only [empty_toList_eq_ff, Bool.coe_sort_false, not_false_iff]
  -- 🎉 no goals
#align vector.not_empty_to_list Vector.not_empty_toList

/-- Mapping under `id` does not change a vector. -/
@[simp]
theorem map_id {n : ℕ} (v : Vector α n) : Vector.map id v = v :=
  Vector.eq _ _ (by simp only [List.map_id, Vector.toList_map])
                    -- 🎉 no goals
#align vector.map_id Vector.map_id

theorem nodup_iff_injective_get {v : Vector α n} : v.toList.Nodup ↔ Function.Injective v.get := by
  cases' v with l hl
  -- ⊢ List.Nodup (toList { val := l, property := hl }) ↔ Function.Injective (get { …
  subst hl
  -- ⊢ List.Nodup (toList { val := l, property := (_ : List.length l = List.length  …
  exact List.nodup_iff_injective_get
  -- 🎉 no goals
#align vector.nodup_iff_nth_inj Vector.nodup_iff_injective_get

theorem head?_toList : ∀ v : Vector α n.succ, (toList v).head? = some (head v)
  | ⟨_ :: _, _⟩ => rfl
#align vector.head'_to_list Vector.head?_toList

/-- Reverse a vector. -/
def reverse (v : Vector α n) : Vector α n :=
  ⟨v.toList.reverse, by simp⟩
                        -- 🎉 no goals
#align vector.reverse Vector.reverse

/-- The `List` of a vector after a `reverse`, retrieved by `toList` is equal
to the `List.reverse` after retrieving a vector's `toList`. -/
theorem toList_reverse {v : Vector α n} : v.reverse.toList = v.toList.reverse :=
  rfl
#align vector.to_list_reverse Vector.toList_reverse

@[simp]
theorem reverse_reverse {v : Vector α n} : v.reverse.reverse = v := by
  cases v
  -- ⊢ reverse (reverse { val := val✝, property := property✝ }) = { val := val✝, pr …
  simp [Vector.reverse]
  -- 🎉 no goals
#align vector.reverse_reverse Vector.reverse_reverse

@[simp]
theorem get_zero : ∀ v : Vector α n.succ, get v 0 = head v
  | ⟨_ :: _, _⟩ => rfl
#align vector.nth_zero Vector.get_zero

@[simp]
theorem head_ofFn {n : ℕ} (f : Fin n.succ → α) : head (ofFn f) = f 0 := by
  rw [← get_zero, get_ofFn]
  -- 🎉 no goals
#align vector.head_of_fn Vector.head_ofFn

--@[simp] Porting note: simp can prove it
theorem get_cons_zero (a : α) (v : Vector α n) : get (a ::ᵥ v) 0 = a := by simp [get_zero]
                                                                           -- 🎉 no goals
#align vector.nth_cons_zero Vector.get_cons_zero

/-- Accessing the nth element of a vector made up
of one element `x : α` is `x` itself. -/
@[simp]
theorem get_cons_nil : ∀ {ix : Fin 1} (x : α), get (x ::ᵥ nil) ix = x
  | ⟨0, _⟩, _ => rfl
#align vector.nth_cons_nil Vector.get_cons_nil

@[simp]
theorem get_cons_succ (a : α) (v : Vector α n) (i : Fin n) : get (a ::ᵥ v) i.succ = get v i := by
  rw [← get_tail_succ, tail_cons]
  -- 🎉 no goals
#align vector.nth_cons_succ Vector.get_cons_succ

/-- The last element of a `Vector`, given that the vector is at least one element. -/
def last (v : Vector α (n + 1)) : α :=
  v.get (Fin.last n)
#align vector.last Vector.last

/-- The last element of a `Vector`, given that the vector is at least one element. -/
theorem last_def {v : Vector α (n + 1)} : v.last = v.get (Fin.last n) :=
  rfl
#align vector.last_def Vector.last_def

/-- The `last` element of a vector is the `head` of the `reverse` vector. -/
theorem reverse_get_zero {v : Vector α (n + 1)} : v.reverse.head = v.last := by
  rw [← get_zero, last_def, get_eq_get, get_eq_get]
  -- ⊢ List.get (toList (reverse v)) (↑(Fin.castIso (_ : Nat.succ n = List.length ( …
  simp_rw [toList_reverse]
  -- ⊢ List.get (List.reverse (toList v)) (↑(Fin.castIso (_ : Nat.succ n = List.len …
  rw [← Option.some_inj, ← List.get?_eq_get, ← List.get?_eq_get, List.get?_reverse]
  -- ⊢ List.get? (toList v) (List.length (toList v) - 1 - ↑(↑(Fin.castIso (_ : Nat. …
  · congr
    -- ⊢ List.length (toList v) - 1 - ↑(↑(Fin.castIso (_ : Nat.succ n = List.length ( …
    simp
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align vector.reverse_nth_zero Vector.reverse_get_zero

section Scan

variable {β : Type*}

variable (f : β → α → β) (b : β)

variable (v : Vector α n)

/-- Construct a `Vector β (n + 1)` from a `Vector α n` by scanning `f : β → α → β`
from the "left", that is, from 0 to `Fin.last n`, using `b : β` as the starting value.
-/
def scanl : Vector β (n + 1) :=
  ⟨List.scanl f b v.toList, by rw [List.length_scanl, toList_length]⟩
                               -- 🎉 no goals
#align vector.scanl Vector.scanl

/-- Providing an empty vector to `scanl` gives the starting value `b : β`. -/
@[simp]
theorem scanl_nil : scanl f b nil = b ::ᵥ nil :=
  rfl
#align vector.scanl_nil Vector.scanl_nil

/-- The recursive step of `scanl` splits a vector `x ::ᵥ v : Vector α (n + 1)`
into the provided starting value `b : β` and the recursed `scanl`
`f b x : β` as the starting value.

This lemma is the `cons` version of `scanl_get`.
-/
@[simp]
theorem scanl_cons (x : α) : scanl f b (x ::ᵥ v) = b ::ᵥ scanl f (f b x) v := by
  simp only [scanl, toList_cons, List.scanl]; dsimp
  -- ⊢ { val := b :: List.scanl f (f b x) ↑v, property := (_ : (fun l => List.lengt …
                                              -- ⊢ { val := b :: List.scanl f (f b x) ↑v, property := (_ : List.length (List.sc …
  simp only [cons]; rfl
  -- ⊢ { val := b :: List.scanl f (f b x) ↑v, property := (_ : List.length (List.sc …
                    -- 🎉 no goals
#align vector.scanl_cons Vector.scanl_cons

/-- The underlying `List` of a `Vector` after a `scanl` is the `List.scanl`
of the underlying `List` of the original `Vector`.
-/
@[simp]
theorem scanl_val : ∀ {v : Vector α n}, (scanl f b v).val = List.scanl f b v.val
  | _ => rfl
#align vector.scanl_val Vector.scanl_val

/-- The `toList` of a `Vector` after a `scanl` is the `List.scanl`
of the `toList` of the original `Vector`.
-/
@[simp]
theorem toList_scanl : (scanl f b v).toList = List.scanl f b v.toList :=
  rfl
#align vector.to_list_scanl Vector.toList_scanl

/-- The recursive step of `scanl` splits a vector made up of a single element
`x ::ᵥ nil : Vector α 1` into a `Vector` of the provided starting value `b : β`
and the mapped `f b x : β` as the last value.
-/
@[simp]
theorem scanl_singleton (v : Vector α 1) : scanl f b v = b ::ᵥ f b v.head ::ᵥ nil := by
  rw [← cons_head_tail v]
  -- ⊢ scanl f b (head v ::ᵥ tail v) = b ::ᵥ f b (head (head v ::ᵥ tail v)) ::ᵥ nil
  simp only [scanl_cons, scanl_nil, head_cons, singleton_tail]
  -- 🎉 no goals
#align vector.scanl_singleton Vector.scanl_singleton

/-- The first element of `scanl` of a vector `v : Vector α n`,
retrieved via `head`, is the starting value `b : β`.
-/
@[simp]
theorem scanl_head : (scanl f b v).head = b := by
  cases n
  -- ⊢ head (scanl f b v) = b
  · have : v = nil := by simp only [Nat.zero_eq, eq_iff_true_of_subsingleton]
    -- ⊢ head (scanl f b v) = b
    simp only [this, scanl_nil, head_cons]
    -- 🎉 no goals
  · rw [← cons_head_tail v]
    -- ⊢ head (scanl f b (head v ::ᵥ tail v)) = b
    simp only [← get_zero, get_eq_get, toList_scanl, toList_cons, List.scanl, Fin.val_zero,
      List.get]
#align vector.scanl_head Vector.scanl_head

/-- For an index `i : Fin n`, the nth element of `scanl` of a
vector `v : Vector α n` at `i.succ`, is equal to the application
function `f : β → α → β` of the `castSucc i` element of
`scanl f b v` and `get v i`.

This lemma is the `get` version of `scanl_cons`.
-/
@[simp]
theorem scanl_get (i : Fin n) :
    (scanl f b v).get i.succ = f ((scanl f b v).get (Fin.castSucc i)) (v.get i) := by
  cases' n with n
  -- ⊢ get (scanl f b v) (Fin.succ i) = f (get (scanl f b v) (Fin.castSucc i)) (get …
  · exact i.elim0
    -- 🎉 no goals
  induction' n with n hn generalizing b
  -- ⊢ get (scanl f b v) (Fin.succ i) = f (get (scanl f b v) (Fin.castSucc i)) (get …
  · have i0 : i = 0 := Fin.eq_zero _
    -- ⊢ get (scanl f b v) (Fin.succ i) = f (get (scanl f b v) (Fin.castSucc i)) (get …
    simp [scanl_singleton, i0, get_zero]; simp [get_eq_get]
    -- ⊢ get (b ::ᵥ f b (head v) ::ᵥ nil) 1 = f b (head v)
                                          -- 🎉 no goals
  · rw [← cons_head_tail v, scanl_cons, get_cons_succ]
    -- ⊢ get (scanl f (f b (head v)) (tail v)) i = f (get (b ::ᵥ scanl f (f b (head v …
    refine' Fin.cases _ _ i
    -- ⊢ get (scanl f (f b (head v)) (tail v)) 0 = f (get (b ::ᵥ scanl f (f b (head v …
    · simp only [get_zero, scanl_head, Fin.castSucc_zero, head_cons]
      -- 🎉 no goals
    · intro i'
      -- ⊢ get (scanl f (f b (head v)) (tail v)) (Fin.succ i') = f (get (b ::ᵥ scanl f  …
      simp only [hn, Fin.castSucc_fin_succ, get_cons_succ]
      -- 🎉 no goals
#align vector.scanl_nth Vector.scanl_get

end Scan

/-- Monadic analog of `Vector.ofFn`.
Given a monadic function on `Fin n`, return a `Vector α n` inside the monad. -/
def mOfFn {m} [Monad m] {α : Type u} : ∀ {n}, (Fin n → m α) → m (Vector α n)
  | 0, _ => pure nil
  | _ + 1, f => do
    let a ← f 0
    let v ← mOfFn fun i => f i.succ
    pure (a ::ᵥ v)
#align vector.m_of_fn Vector.mOfFn

theorem mOfFn_pure {m} [Monad m] [LawfulMonad m] {α} :
    ∀ {n} (f : Fin n → α), (@mOfFn m _ _ _ fun i => pure (f i)) = pure (ofFn f)
  | 0, f => rfl
  | n + 1, f => by
    rw [mOfFn, @mOfFn_pure m _ _ _ n _, ofFn]
    -- ⊢ (do
    simp
    -- 🎉 no goals
#align vector.m_of_fn_pure Vector.mOfFn_pure

/-- Apply a monadic function to each component of a vector,
returning a vector inside the monad. -/
def mmap {m} [Monad m] {α} {β : Type u} (f : α → m β) : ∀ {n}, Vector α n → m (Vector β n)
  | 0, _ => pure nil
  | _ + 1, xs => do
    let h' ← f xs.head
    let t' ← mmap f xs.tail
    pure (h' ::ᵥ t')
#align vector.mmap Vector.mmap

@[simp]
theorem mmap_nil {m} [Monad m] {α β} (f : α → m β) : mmap f nil = pure nil :=
  rfl
#align vector.mmap_nil Vector.mmap_nil

@[simp]
theorem mmap_cons {m} [Monad m] {α β} (f : α → m β) (a) :
    ∀ {n} (v : Vector α n),
      mmap f (a ::ᵥ v) = do
        let h' ← f a
        let t' ← mmap f v
        pure (h' ::ᵥ t')
  | _, ⟨_, rfl⟩ => rfl
#align vector.mmap_cons Vector.mmap_cons

/-- Define `C v` by induction on `v : Vector α n`.

This function has two arguments: `h_nil` handles the base case on `C nil`,
and `h_cons` defines the inductive step using `∀ x : α, C w → C (x ::ᵥ w)`.

This can be used as `induction v using Vector.inductionOn`. -/
@[elab_as_elim]
def inductionOn {C : ∀ {n : ℕ}, Vector α n → Sort*} {n : ℕ} (v : Vector α n)
    (h_nil : C nil) (h_cons : ∀ {n : ℕ} {x : α} {w : Vector α n}, C w → C (x ::ᵥ w)) : C v := by
  -- porting notes: removed `generalizing`: already generalized
  induction' n with n ih
  -- ⊢ C v
  · rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    -- ⊢ C { val := [], property := (_ : List.length [] = List.length []) }
    exact h_nil
    -- 🎉 no goals
  · rcases v with ⟨_ | ⟨a, v⟩, v_property⟩
    -- ⊢ C { val := [], property := v_property }
    cases v_property
    -- ⊢ C { val := a :: v, property := v_property }
    apply @h_cons n _ ⟨v, (add_left_inj 1).mp v_property⟩
    -- ⊢ C { val := v, property := (_ : List.length v = n) }
    apply ih
    -- 🎉 no goals
#align vector.induction_on Vector.inductionOn

-- check that the above works with `induction ... using`
example (v : Vector α n) : True := by induction v using Vector.inductionOn <;> trivial
                                      -- ⊢ True
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals

variable {β γ : Type*}

/-- Define `C v w` by induction on a pair of vectors `v : Vector α n` and `w : Vector β n`. -/
@[elab_as_elim]
def inductionOn₂ {C : ∀ {n}, Vector α n → Vector β n → Sort*}
    (v : Vector α n) (w : Vector β n)
    (nil : C nil nil) (cons : ∀ {n a b} {x : Vector α n} {y}, C x y → C (a ::ᵥ x) (b ::ᵥ y)) :
    C v w := by
  -- porting notes: removed `generalizing`: already generalized
  induction' n with n ih
  -- ⊢ C v w
  · rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    -- ⊢ C { val := [], property := (_ : List.length [] = List.length []) } w
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    -- ⊢ C { val := [], property := (_ : List.length [] = List.length []) } { val :=  …
    exact nil
    -- 🎉 no goals
  · rcases v with ⟨_ | ⟨a, v⟩, v_property⟩
    -- ⊢ C { val := [], property := v_property } w
    cases v_property
    -- ⊢ C { val := a :: v, property := v_property } w
    rcases w with ⟨_ | ⟨b, w⟩, w_property⟩
    -- ⊢ C { val := a :: v, property := v_property } { val := [], property := w_prope …
    cases w_property
    -- ⊢ C { val := a :: v, property := v_property } { val := b :: w, property := w_p …
    apply @cons n _ _ ⟨v, (add_left_inj 1).mp v_property⟩ ⟨w, (add_left_inj 1).mp w_property⟩
    -- ⊢ C { val := v, property := (_ : List.length v = n) } { val := w, property :=  …
    apply ih
    -- 🎉 no goals
#align vector.induction_on₂ Vector.inductionOn₂

/-- Define `C u v w` by induction on a triplet of vectors
`u : Vector α n`, `v : Vector β n`, and `w : Vector γ b`. -/
@[elab_as_elim]
def inductionOn₃ {C : ∀ {n}, Vector α n → Vector β n → Vector γ n → Sort*}
    (u : Vector α n) (v : Vector β n) (w : Vector γ n) (nil : C nil nil nil)
    (cons : ∀ {n a b c} {x : Vector α n} {y z}, C x y z → C (a ::ᵥ x) (b ::ᵥ y) (c ::ᵥ z)) :
    C u v w := by
  -- porting notes: removed `generalizing`: already generalized
  induction' n with n ih
  -- ⊢ C u v w
  · rcases u with ⟨_ | ⟨-, -⟩, - | -⟩
    -- ⊢ C { val := [], property := (_ : List.length [] = List.length []) } v w
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    -- ⊢ C { val := [], property := (_ : List.length [] = List.length []) } { val :=  …
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    -- ⊢ C { val := [], property := (_ : List.length [] = List.length []) } { val :=  …
    exact nil
    -- 🎉 no goals
  · rcases u with ⟨_ | ⟨a, u⟩, u_property⟩
    -- ⊢ C { val := [], property := u_property } v w
    cases u_property
    -- ⊢ C { val := a :: u, property := u_property } v w
    rcases v with ⟨_ | ⟨b, v⟩, v_property⟩
    -- ⊢ C { val := a :: u, property := u_property } { val := [], property := v_prope …
    cases v_property
    -- ⊢ C { val := a :: u, property := u_property } { val := b :: v, property := v_p …
    rcases w with ⟨_ | ⟨c, w⟩, w_property⟩
    -- ⊢ C { val := a :: u, property := u_property } { val := b :: v, property := v_p …
    cases w_property
    -- ⊢ C { val := a :: u, property := u_property } { val := b :: v, property := v_p …
    apply
      @cons n _ _ _ ⟨u, (add_left_inj 1).mp u_property⟩ ⟨v, (add_left_inj 1).mp v_property⟩
        ⟨w, (add_left_inj 1).mp w_property⟩
    apply ih
    -- 🎉 no goals
#align vector.induction_on₃ Vector.inductionOn₃

/-- Define `motive v` by case-analysis on `v : Vector α n` -/
def casesOn {motive : ∀ {n}, Vector α n → Sort*} (v : Vector α m)
    (nil : motive nil) (cons : ∀ {n}, (hd : α) → (tl : Vector α n) → motive (Vector.cons hd tl)) :
    motive v :=
  inductionOn (C := motive) v nil @fun _ hd tl _ => cons hd tl

/-- Define `motive v₁ v₂` by case-analysis on `v₁ : Vector α n` and `v₂ : Vector β n` -/
def casesOn₂  {motive : ∀{n}, Vector α n → Vector β n → Sort*} (v₁ : Vector α m) (v₂ : Vector β m)
              (nil : motive nil nil)
              (cons : ∀{n}, (x : α) → (y : β) → (xs : Vector α n) → (ys : Vector β n)
                      → motive (x ::ᵥ xs) (y ::ᵥ ys)) :
              motive v₁ v₂ :=
    inductionOn₂ (C := motive) v₁ v₂ nil @fun _ x y xs ys _ => cons x y xs ys

/-- Define `motive v₁ v₂ v₃` by case-analysis on `v₁ : Vector α n`, `v₂ : Vector β n`, and
    `v₃ : Vector γ n` -/
def casesOn₃  {motive : ∀{n}, Vector α n → Vector β n → Vector γ n → Sort*} (v₁ : Vector α m)
              (v₂ : Vector β m) (v₃ : Vector γ m) (nil : motive nil nil nil)
              (cons : ∀{n}, (x : α) → (y : β) → (z : γ) → (xs : Vector α n) → (ys : Vector β n)
                        → (zs : Vector γ n) → motive (x ::ᵥ xs) (y ::ᵥ ys) (z ::ᵥ zs)) :
              motive v₁ v₂ v₃ :=
    inductionOn₃ (C := motive) v₁ v₂ v₃ nil @fun _ x y z xs ys zs _ => cons x y z xs ys zs

/-- Cast a vector to an array. -/
def toArray : Vector α n → Array α
  | ⟨xs, _⟩ => cast (by rfl) xs.toArray
                        -- 🎉 no goals
#align vector.to_array Vector.toArray

section InsertNth

variable {a : α}

/-- `v.insertNth a i` inserts `a` into the vector `v` at position `i`
(and shifting later components to the right). -/
def insertNth (a : α) (i : Fin (n + 1)) (v : Vector α n) : Vector α (n + 1) :=
  ⟨v.1.insertNth i a, by
    rw [List.length_insertNth, v.2]
    -- ⊢ ↑i ≤ List.length ↑v
    rw [v.2, ← Nat.succ_le_succ_iff]
    -- ⊢ Nat.succ ↑i ≤ Nat.succ n
    exact i.2⟩
    -- 🎉 no goals
#align vector.insert_nth Vector.insertNth

theorem insertNth_val {i : Fin (n + 1)} {v : Vector α n} :
    (v.insertNth a i).val = v.val.insertNth i.1 a :=
  rfl
#align vector.insert_nth_val Vector.insertNth_val

@[simp]
theorem removeNth_val {i : Fin n} : ∀ {v : Vector α n}, (removeNth i v).val = v.val.removeNth i
  | _ => rfl
#align vector.remove_nth_val Vector.removeNth_val

theorem removeNth_insertNth {v : Vector α n} {i : Fin (n + 1)} :
    removeNth i (insertNth a i v) = v :=
  Subtype.eq <| List.removeNth_insertNth i.1 v.1
#align vector.remove_nth_insert_nth Vector.removeNth_insertNth

theorem removeNth_insertNth' {v : Vector α (n + 1)} :
    ∀ {i : Fin (n + 1)} {j : Fin (n + 2)},
      removeNth (j.succAbove i) (insertNth a j v) = insertNth a (i.predAbove j) (removeNth i v)
  | ⟨i, hi⟩, ⟨j, hj⟩ => by
    dsimp [insertNth, removeNth, Fin.succAbove, Fin.predAbove]
    -- ⊢ { val := List.removeNth (List.insertNth j a ↑v) ↑(if i < j then { val := i,  …
    rw [Subtype.mk_eq_mk]
    -- ⊢ List.removeNth (List.insertNth j a ↑v) ↑(if i < j then { val := i, isLt := ( …
    simp only [Fin.lt_iff_val_lt_val]
    -- ⊢ List.removeNth (List.insertNth j a ↑v) ↑(if i < j then { val := i, isLt := ( …
    split_ifs with hij
    · rcases Nat.exists_eq_succ_of_ne_zero
        (Nat.pos_iff_ne_zero.1 (lt_of_le_of_lt (Nat.zero_le _) hij)) with ⟨j, rfl⟩
      rw [← List.insertNth_removeNth_of_ge]
      · simp; rfl
        -- ⊢ List.insertNth j a (List.removeNth (↑v) i) =
              -- 🎉 no goals
      · simpa
        -- 🎉 no goals
      · simpa [Nat.lt_succ_iff] using hij
        -- 🎉 no goals
    · dsimp
      -- ⊢ List.removeNth (List.insertNth j a ↑v) (i + 1) =
      rw [← List.insertNth_removeNth_of_le i j _ _ _]
      · rfl
        -- 🎉 no goals
      · simpa
        -- 🎉 no goals
      · simpa [not_lt] using hij
        -- 🎉 no goals
#align vector.remove_nth_insert_nth' Vector.removeNth_insertNth'

theorem insertNth_comm (a b : α) (i j : Fin (n + 1)) (h : i ≤ j) :
    ∀ v : Vector α n,
      (v.insertNth a i).insertNth b j.succ = (v.insertNth b j).insertNth a (Fin.castSucc i)
  | ⟨l, hl⟩ => by
    refine' Subtype.eq _
    -- ⊢ ↑(insertNth b (Fin.succ j) (insertNth a i { val := l, property := hl })) = ↑ …
    simp only [insertNth_val, Fin.val_succ, Fin.castSucc, Fin.coe_castAdd]
    -- ⊢ List.insertNth (↑j + 1) b (List.insertNth (↑i) a l) = List.insertNth (↑i) a  …
    apply List.insertNth_comm
    -- ⊢ ↑i ≤ ↑j
    · assumption
      -- 🎉 no goals
    · rw [hl]
      -- ⊢ ↑j ≤ n
      exact Nat.le_of_succ_le_succ j.2
      -- 🎉 no goals
#align vector.insert_nth_comm Vector.insertNth_comm

end InsertNth

-- porting notes: renamed to `set` from `updateNth` to align with `List`
section ModifyNth

/-- `set v n a` replaces the `n`th element of `v` with `a` -/
def set (v : Vector α n) (i : Fin n) (a : α) : Vector α n :=
  ⟨v.1.set i.1 a, by simp⟩
                     -- 🎉 no goals
#align vector.update_nth Vector.set

@[simp]
theorem toList_set (v : Vector α n) (i : Fin n) (a : α) :
    (v.set i a).toList = v.toList.set i a :=
  rfl
#align vector.to_list_update_nth Vector.toList_set

@[simp]
theorem get_set_same (v : Vector α n) (i : Fin n) (a : α) : (v.set i a).get i = a := by
  cases v; cases i; simp [Vector.set, get_eq_get]
  -- ⊢ get (set { val := val✝, property := property✝ } i a) i = a
           -- ⊢ get (set { val := val✝¹, property := property✝ } { val := val✝, isLt := isLt …
                    -- ⊢ List.get (List.set val✝¹ val✝ a) (↑(Fin.castIso (_ : n = List.length (toList …
  dsimp
  -- ⊢ List.get (List.set val✝¹ val✝ a) (↑(Fin.castIso (_ : n = List.length (List.s …
  exact List.get_set_eq _ _ _ _
  -- 🎉 no goals
#align vector.nth_update_nth_same Vector.get_set_same

theorem get_set_of_ne {v : Vector α n} {i j : Fin n} (h : i ≠ j) (a : α) :
    (v.set i a).get j = v.get j := by
  cases v; cases i; cases j
  -- ⊢ get (set { val := val✝, property := property✝ } i a) j = get { val := val✝,  …
           -- ⊢ get (set { val := val✝¹, property := property✝ } { val := val✝, isLt := isLt …
                    -- ⊢ get (set { val := val✝², property := property✝ } { val := val✝¹, isLt := isL …
  simp [Vector.set, Vector.get_eq_get, List.get_set_of_ne (Fin.vne_of_ne h)]
  -- ⊢ List.get (List.set val✝² val✝¹ a) (↑(Fin.castIso (_ : n = List.length (toLis …
  rw [List.get_set_of_ne]
  -- ⊢ List.get val✝² { val := ↑(↑(Fin.castIso (_ : n = List.length (toList { val : …
  · rfl
    -- 🎉 no goals
  · simpa using h
    -- 🎉 no goals
#align vector.nth_update_nth_of_ne Vector.get_set_of_ne

theorem get_set_eq_if {v : Vector α n} {i j : Fin n} (a : α) :
    (v.set i a).get j = if i = j then a else v.get j := by
  split_ifs <;> (try simp [*]); rwa [get_set_of_ne]
  -- ⊢ get (set v i a) j = a
                 -- 🎉 no goals
                 -- ⊢ get (set v i a) j = get v j
                                -- 🎉 no goals
#align vector.nth_update_nth_eq_if Vector.get_set_eq_if

@[to_additive]
theorem prod_set [Monoid α] (v : Vector α n) (i : Fin n) (a : α) :
    (v.set i a).toList.prod = (v.take i).toList.prod * a * (v.drop (i + 1)).toList.prod := by
  refine' (List.prod_set v.toList i a).trans _
  -- ⊢ (List.prod (List.take (↑i) (toList v)) * if ↑i < List.length (toList v) then …
  simp_all
  -- 🎉 no goals
#align vector.prod_update_nth Vector.prod_set

@[to_additive]
theorem prod_set' [CommGroup α] (v : Vector α n) (i : Fin n) (a : α) :
    (v.set i a).toList.prod = v.toList.prod * (v.get i)⁻¹ * a := by
  refine' (List.prod_set' v.toList i a).trans _
  -- ⊢ (List.prod (toList v) * if hn : ↑i < List.length (toList v) then (List.nthLe …
  simp [get_eq_get, mul_assoc]; rfl
  -- ⊢ List.nthLe (toList v) ↑i (_ : ↑i < List.length (toList v)) = List.get (toLis …
                                -- 🎉 no goals
#align vector.prod_update_nth' Vector.prod_set'

end ModifyNth

end Vector

namespace Vector

section Traverse

variable {F G : Type u → Type u}

variable [Applicative F] [Applicative G]

open Applicative Functor

open List (cons)

open Nat

private def traverseAux {α β : Type u} (f : α → F β) : ∀ x : List α, F (Vector β x.length)
  | [] => pure Vector.nil
  | x :: xs => Vector.cons <$> f x <*> traverseAux f xs

/-- Apply an applicative function to each component of a vector. -/
protected def traverse {α β : Type u} (f : α → F β) : Vector α n → F (Vector β n)
  | ⟨v, Hv⟩ => cast (by rw [Hv]) <| traverseAux f v
                        -- 🎉 no goals
#align vector.traverse Vector.traverse

section

variable {α β : Type u}

@[simp]
protected theorem traverse_def (f : α → F β) (x : α) :
    ∀ xs : Vector α n, (x ::ᵥ xs).traverse f = cons <$> f x <*> xs.traverse f := by
  rintro ⟨xs, rfl⟩; rfl
  -- ⊢ Vector.traverse f (x ::ᵥ { val := xs, property := (_ : List.length xs = List …
                    -- 🎉 no goals
#align vector.traverse_def Vector.traverse_def

protected theorem id_traverse : ∀ x : Vector α n, x.traverse (pure : _ → Id _) = x := by
  rintro ⟨x, rfl⟩; dsimp [Vector.traverse, cast]
  -- ⊢ Vector.traverse pure { val := x, property := (_ : List.length x = List.lengt …
                   -- ⊢ Vector.traverseAux pure x = { val := x, property := (_ : List.length x = Lis …
  induction' x with x xs IH; · rfl
  -- ⊢ Vector.traverseAux pure [] = { val := [], property := (_ : List.length [] =  …
                               -- 🎉 no goals
  simp! [IH]; rfl
  -- ⊢ (Seq.seq (cons x) fun x => { val := xs, property := (_ : List.length xs = Li …
              -- 🎉 no goals
#align vector.id_traverse Vector.id_traverse

end

open Function

variable [LawfulApplicative F] [LawfulApplicative G]

variable {α β γ : Type u}

-- We need to turn off the linter here as
-- the `LawfulTraversable` instance below expects a particular signature.
@[nolint unusedArguments]
protected theorem comp_traverse (f : β → F γ) (g : α → G β) (x : Vector α n) :
    Vector.traverse (Comp.mk ∘ Functor.map f ∘ g) x =
      Comp.mk (Vector.traverse f <$> Vector.traverse g x) := by
  induction' x using Vector.inductionOn with n x xs ih
  -- ⊢ Vector.traverse (Comp.mk ∘ Functor.map f ∘ g) nil = Comp.mk (Vector.traverse …
  simp! [cast, *, functor_norm]
  -- ⊢ pure nil = Comp.mk (pure (pure nil))
  · rfl
    -- 🎉 no goals
  · rw [Vector.traverse_def, ih]
    -- ⊢ (Seq.seq (cons <$> (Comp.mk ∘ Functor.map f ∘ g) x) fun x => Comp.mk (Vector …
    simp [functor_norm, (· ∘ ·)]
    -- 🎉 no goals
#align vector.comp_traverse Vector.comp_traverse

protected theorem traverse_eq_map_id {α β} (f : α → β) :
    ∀ x : Vector α n, x.traverse ((pure: _ → Id _) ∘ f) = (pure: _ → Id _) (map f x) := by
  rintro ⟨x, rfl⟩; simp!; induction x <;> simp! [*, functor_norm] <;> rfl
  -- ⊢ Vector.traverse (pure ∘ f) { val := x, property := (_ : List.length x = List …
                   -- ⊢ Vector.traverseAux (pure ∘ f) x = { val := List.map f x, property := (_ : Li …
                          -- ⊢ Vector.traverseAux (pure ∘ f) [] = { val := List.map f [], property := (_ :  …
                                          -- ⊢ nil = { val := [], property := (_ : (fun l => List.length l = List.length [] …
                                          -- ⊢ (Seq.seq (cons (f head✝)) fun x => { val := List.map f tail✝, property := (_ …
                                                                      -- 🎉 no goals
                                                                      -- 🎉 no goals
#align vector.traverse_eq_map_id Vector.traverse_eq_map_id

variable (η : ApplicativeTransformation F G)

protected theorem naturality {α β : Type _} (f : α → F β) (x : Vector α n) :
    η (x.traverse f) = x.traverse (@η _ ∘ f) := by
  induction' x using Vector.inductionOn with n x xs ih
  -- ⊢ (fun {α} => ApplicativeTransformation.app η α) (Vector.traverse f nil) = Vec …
  · simp! [functor_norm, cast, η.preserves_pure]
    -- 🎉 no goals
  · rw [Vector.traverse_def, Vector.traverse_def, ← ih, η.preserves_seq, η.preserves_map]
    -- ⊢ (Seq.seq (cons <$> (fun {α} => ApplicativeTransformation.app η α) (f x)) fun …
    rfl
    -- 🎉 no goals
#align vector.naturality Vector.naturality

end Traverse

instance : Traversable.{u} (flip Vector n) where
  traverse := @Vector.traverse n
  map {α β} := @Vector.map.{u, u} α β n

instance : LawfulTraversable.{u} (flip Vector n) where
  id_traverse := @Vector.id_traverse n
  comp_traverse := Vector.comp_traverse
  traverse_eq_map_id := @Vector.traverse_eq_map_id n
  naturality := Vector.naturality
  id_map := by intro _ x; cases x; simp! [(· <$> ·)]
               -- ⊢ id <$> x = x
                          -- ⊢ id <$> { val := val✝, property := property✝ } = { val := val✝, property := p …
                                   -- 🎉 no goals
  comp_map := by intro _ _ _ _ _ x; cases x; simp! [(· <$> ·)]
                 -- ⊢ (h✝ ∘ g✝) <$> x = h✝ <$> g✝ <$> x
                                    -- ⊢ (h✝ ∘ g✝) <$> { val := val✝, property := property✝ } = h✝ <$> g✝ <$> { val : …
                                             -- 🎉 no goals
  map_const := rfl

--Porting note: not porting meta instances
-- unsafe instance reflect [reflected_univ.{u}] {α : Type u} [has_reflect α]
--     [reflected _ α] {n : ℕ} : has_reflect (Vector α n) := fun v =>
--   @Vector.inductionOn α (fun n => reflected _) n v
--     ((by
--           trace
--             "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14:
--              unsupported tactic `reflect_name #[]" :
--           reflected _ @Vector.nil.{u}).subst
--       q(α))
--     fun n x xs ih =>
--     (by
--           trace
--             "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14:
--              unsupported tactic `reflect_name #[]" :
--           reflected _ @Vector.cons.{u}).subst₄
--       q(α) q(n) q(x) ih
-- #align vector.reflect vector.reflect


section Simp

variable (xs : Vector α n)

@[simp]
theorem replicate_succ (val : α) :
    replicate (n+1) val = val ::ᵥ (replicate n val) :=
  rfl

section Append
variable (ys : Vector α m)

@[simp]
theorem get_append_cons_zero : get (append (x ::ᵥ xs) ys) ⟨0, by simp⟩ = x :=
                                                                 -- 🎉 no goals
  rfl

@[simp]
theorem get_append_cons_succ {i : Fin (n + m)} {h} :
    get (append (x ::ᵥ xs) ys) ⟨i+1, h⟩ = get (append xs ys) i :=
  rfl

@[simp]
theorem append_nil : append xs nil = xs := by
  cases xs; simp [append]
  -- ⊢ append { val := val✝, property := property✝ } nil = { val := val✝, property  …
            -- 🎉 no goals

end Append

variable (ys : Vector β n)

@[simp]
theorem get_map₂ (v₁ : Vector α n) (v₂ : Vector β n) (f : α → β → γ) (i : Fin n) :
    get (map₂ f v₁ v₂) i = f (get v₁ i) (get v₂ i) := by
  clear * - v₁ v₂
  -- ⊢ get (map₂ f v₁ v₂) i = f (get v₁ i) (get v₂ i)
  induction v₁, v₂ using inductionOn₂
  -- ⊢ get (map₂ f nil nil) i = f (get nil i) (get nil i)
  case nil =>
    exact Fin.elim0 i
  case cons x xs y ys ih =>
    rw [map₂_cons]
    cases i using Fin.cases
    · simp only [get_zero, head_cons]
    · simp only [get_cons_succ, ih]

@[simp]
theorem mapAccumr_cons :
    mapAccumr f (x ::ᵥ xs) s
    = let r := mapAccumr f xs s
      let q := f x r.1
      (q.1, q.2 ::ᵥ r.2) :=
  rfl

@[simp]
theorem mapAccumr₂_cons :
    mapAccumr₂ f (x ::ᵥ xs) (y ::ᵥ ys) s
    = let r := mapAccumr₂ f xs ys s
      let q := f x y r.1
      (q.1, q.2 ::ᵥ r.2) :=
  rfl

end Simp

end Vector
