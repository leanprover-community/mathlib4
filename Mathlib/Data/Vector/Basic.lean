/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.vector.basic
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Vector
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Control.Applicative

/-!
# Additional theorems and definitions about the `Vector` type

This file introduces the infix notation `::ᵥ` for `Vector.cons`.
-/


universe u

variable {n : ℕ}

namespace Vector

variable {α : Type _}

-- mathport name: «expr ::ᵥ »
infixr:67 " ::ᵥ " => Vector.cons

attribute [simp] head_cons tail_cons

instance [Inhabited α] : Inhabited (Vector α n) :=
  ⟨ofFn default⟩

theorem to_list_injective : Function.Injective (@toList α n) :=
  Subtype.val_injective
#align vector.to_list_injective Vector.to_list_injective

/-- Two `v w : Vector α n` are equal iff they are equal at every single index. -/
@[ext]
theorem ext : ∀ {v w : Vector α n} (_ : ∀ m : Fin n, Vector.get v m = Vector.get w m), v = w
  | ⟨v, hv⟩, ⟨w, hw⟩, h =>
    Subtype.eq (List.ext_get (by rw [hv, hw]) fun m hm _ => h ⟨m, hv ▸ hm⟩)
#align vector.ext Vector.ext

/-- The empty `Vector` is a `Subsingleton`. -/
instance zero_subsingleton : Subsingleton (Vector α 0) :=
  ⟨fun _ _ => Vector.ext fun m => Fin.elim0 m⟩
#align vector.zero_subsingleton Vector.zero_subsingleton

@[simp]
theorem cons_val (a : α) : ∀ v : Vector α n, (a ::ᵥ v).val = a :: v.val
  | ⟨_, _⟩ => rfl
#align vector.cons_val Vector.cons_val

@[simp]
theorem cons_head (a : α) : ∀ v : Vector α n, (a ::ᵥ v).head = a
  | ⟨_, _⟩ => rfl
#align vector.cons_head Vector.cons_head

@[simp]
theorem cons_tail (a : α) : ∀ v : Vector α n, (a ::ᵥ v).tail = v
  | ⟨_, _⟩ => rfl
#align vector.cons_tail Vector.cons_tail

theorem eq_cons_iff (a : α) (v : Vector α n.succ) (v' : Vector α n) :
    v = a ::ᵥ v' ↔ v.head = a ∧ v.tail = v' :=
  ⟨fun h => h.symm ▸ ⟨head_cons a v', tail_cons a v'⟩, fun h =>
    _root_.trans (cons_head_tail v).symm (by rw [h.1, h.2])⟩
#align vector.eq_cons_iff Vector.eq_cons_iff

theorem ne_cons_iff (a : α) (v : Vector α n.succ) (v' : Vector α n) :
    v ≠ a ::ᵥ v' ↔ v.head ≠ a ∨ v.tail ≠ v' := by rw [Ne.def, eq_cons_iff a v v', not_and_or]
#align vector.ne_cons_iff Vector.ne_cons_iff

theorem exists_eq_cons (v : Vector α n.succ) : ∃ (a : α)(as : Vector α n), v = a ::ᵥ as :=
  ⟨v.head, v.tail, (eq_cons_iff v.head v v.tail).2 ⟨rfl, rfl⟩⟩
#align vector.exists_eq_cons Vector.exists_eq_cons

@[simp]
theorem toList_of_fn : ∀ {n} (f : Fin n → α), toList (ofFn f) = List.ofFn f
  | 0, f => rfl
  | n + 1, f => by rw [ofFn, List.ofFn_succ, toList_cons, toList_of_fn]
#align vector.to_list_of_fn Vector.toList_of_fn

@[simp]
theorem mk_to_list : ∀ (v : Vector α n) (h), (⟨toList v, h⟩ : Vector α n) = v
  | ⟨_, _⟩, _ => rfl
#align vector.mk_to_list Vector.mk_to_list


@[simp] theorem length_val (v : Vector α n) : v.val.length = n := v.2

@[simp] theorem length_toList (v : Vector α n) : v.toList.length = n := v.2

-- porting notes: not used in mathlib and coercions done differently in Lean 4
-- @[simp]
-- theorem length_coe (v : Vector α n) :
--     ((coe : { l : List α // l.length = n } → List α) v).length = n :=
--   v.2
#noalign vector.length_coe

@[simp]
theorem to_list_map {β : Type _} (v : Vector α n) (f : α → β) : (v.map f).toList = v.toList.map f :=
  by cases v ; rfl
#align vector.to_list_map Vector.to_list_map

@[simp]
theorem head_map {β : Type _} (v : Vector α (n + 1)) (f : α → β) : (v.map f).head = f v.head :=
  by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  rw [h, map_cons, head_cons, head_cons]
#align vector.head_map Vector.head_map

@[simp]
theorem tail_map {β : Type _} (v : Vector α (n + 1)) (f : α → β) : (v.map f).tail = v.tail.map f :=
  by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  rw [h, map_cons, tail_cons, tail_cons]
#align vector.tail_map Vector.tail_map

@[simp] theorem get_eq_get (v : Vector α n) (i : Fin n) :
    v.get i = v.toList.get (Fin.cast v.length_toList.symm i) :=
  rfl
#align vector.nth_eq_nth_le Vector.get_eq_get

-- porting notes: `nthLe` deprecated for `get`
@[deprecated get_eq_get]
theorem nth_eq_nth_le :
    ∀ (v : Vector α n) (i), get v i = v.toList.nthLe i.1 (by rw [toList_length] ; exact i.2)
  | ⟨_, _⟩, _ => rfl

@[simp]
theorem get_replicate (a : α) (i : Fin n) : (Vector.replicate n a).get i = a := by
  apply List.get_replicate
#align vector.nth_repeat Vector.get_replicate

@[simp]
theorem get_map {β : Type _} (v : Vector α n) (f : α → β) (i : Fin n) :
    (v.map f).get i = f (v.get i) := by simp [get_eq_get]
#align vector.nth_map Vector.get_map

@[simp]
theorem get_ofFn {n} (f : Fin n → α) (i) : get (ofFn f) i = f i := by
  rw [get_eq_get, ← List.get_ofFn f] <;> congr <;> apply toList_ofFn
#align vector.nth_of_fn Vector.get_ofFn

@[simp]
theorem ofFn_get (v : Vector α n) : ofFn (get v) = v :=
  by
  rcases v with ⟨l, rfl⟩
  apply to_list_injective
  change get ⟨l, Eq.refl _⟩ with fun i => get ⟨l, rfl⟩ i
  simpa only [toList_of_fn] using List.ofFn_get _
#align vector.of_fn_nth Vector.ofFn_get

/-- The natural equivalence between length-`n` vectors and functions from `Fin n`. -/
def _root_.Equiv.vectorEquivFin (α : Type _) (n : ℕ) : Vector α n ≃ (Fin n → α) :=
  ⟨Vector.get, Vector.ofFn, Vector.ofFn_get, fun f => funext <| Vector.get_ofFn f⟩
#align equiv.vector_equiv_fin Equiv.vectorEquivFin

theorem get_tail (x : Vector α n) (i) : x.tail.get i = x.get ⟨i.1 + 1, lt_tsub_iff_right.mp i.2⟩ :=
  by rcases x with ⟨_ | _, h⟩ <;> rfl
#align vector.nth_tail Vector.get_tail

@[simp]
theorem get_tail_succ : ∀ (v : Vector α n.succ) (i : Fin n), get (tail v) i = get v i.succ
  | ⟨a :: l, e⟩, ⟨i, h⟩ => by simp [get_eq_get] ; rfl
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
theorem singleton_tail (v : Vector α 1) : v.tail = Vector.nil := by
  simp only [← cons_head_tail, eq_iff_true_of_subsingleton]
#align vector.singleton_tail Vector.singleton_tail

@[simp]
theorem tail_ofFn {n : ℕ} (f : Fin n.succ → α) : tail (ofFn f) = ofFn fun i => f i.succ :=
  (ofFn_get _).symm.trans <| by
    congr
    funext i
    cases i
    simp
#align vector.tail_of_fn Vector.tail_ofFn

@[simp]
theorem toList_empty (v : Vector α 0) : v.toList = [] :=
  List.length_eq_zero.mp v.2
#align vector.to_list_empty Vector.toList_empty

/-- The list that makes up a `Vector` made up of a single element,
retrieved via `toList`, is equal to the list of that single element. -/
@[simp]
theorem toList_singleton (v : Vector α 1) : v.toList = [v.head] :=
  by
  rw [← v.cons_head_tail]
  simp only [toList_cons, toList_nil, cons_head, eq_self_iff_true, and_self_iff, singleton_tail]
#align vector.to_list_singleton Vector.toList_singleton

@[simp]
theorem empty_toList_eq_ff (v : Vector α (n + 1)) : v.toList.isEmpty = false :=
  match v with
  | ⟨_ :: _, _⟩ => rfl
#align vector.empty_to_list_eq_ff Vector.empty_toList_eq_ff

theorem not_empty_toList (v : Vector α (n + 1)) : ¬v.toList.isEmpty := by
  simp only [empty_toList_eq_ff, Bool.coe_sort_false, not_false_iff]
#align vector.not_empty_to_list Vector.not_empty_toList

/-- Mapping under `id` does not change a vector. -/
@[simp]
theorem map_id {n : ℕ} (v : Vector α n) : Vector.map id v = v :=
  Vector.eq _ _ (by simp only [List.map_id, Vector.to_list_map])
#align vector.map_id Vector.map_id

theorem nodup_iff_injective_get {v : Vector α n} : v.toList.Nodup ↔ Function.Injective v.get :=
  by
  cases' v with l hl
  subst hl
  simp only [List.nodup_iff_injective_get]
  constructor
  · intro h i j hij
    cases i
    cases j
    ext
    apply h
    simpa
  · intro h i j hi hj hij
    have := @h ⟨i, hi⟩ ⟨j, hj⟩
    simp [nth_eq_nth_le] at *
    tauto
#align vector.nodup_iff_nth_inj Vector.nodup_iff_injective_get

theorem head?_toList : ∀ v : Vector α n.succ, (toList v).head? = some (head v)
  | ⟨_ :: _, _⟩ => rfl
#align vector.head'_to_list Vector.head?_toList

/-- Reverse a vector. -/
def reverse (v : Vector α n) : Vector α n :=
  ⟨v.toList.reverse, by simp⟩
#align vector.reverse Vector.reverse

/-- The `List` of a vector after a `reverse`, retrieved by `toList` is equal
to the `List.reverse` after retrieving a vector's `toList`. -/
theorem to_list_reverse {v : Vector α n} : v.reverse.toList = v.toList.reverse :=
  rfl
#align vector.to_list_reverse Vector.to_list_reverse

@[simp]
theorem reverse_reverse {v : Vector α n} : v.reverse.reverse = v :=
  by
  cases v
  simp [Vector.reverse]
#align vector.reverse_reverse Vector.reverse_reverse

@[simp]
theorem get_zero : ∀ v : Vector α n.succ, get v 0 = head v
  | ⟨_ :: _, _⟩ => rfl
#align vector.nth_zero Vector.get_zero

@[simp]
theorem head_of_fn {n : ℕ} (f : Fin n.succ → α) : head (ofFn f) = f 0 := by
  rw [← get_zero, get_ofFn]
#align vector.head_of_fn Vector.head_of_fn

@[simp]
theorem get_cons_zero (a : α) (v : Vector α n) : get (a ::ᵥ v) 0 = a := by simp [get_zero]
#align vector.nth_cons_zero Vector.get_cons_zero

/-- Accessing the nth element of a vector made up
of one element `x : α` is `x` itself. -/
@[simp]
theorem get_cons_nil {ix : Fin 1} (x : α) : get (x ::ᵥ nil) ix = x := by convert get_cons_zero x nil
#align vector.nth_cons_nil Vector.get_cons_nil

@[simp]
theorem get_cons_succ (a : α) (v : Vector α n) (i : Fin n) : get (a ::ᵥ v) i.succ = get v i := by
  rw [← get_tail_succ, tail_cons]
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
theorem reverse_get_zero {v : Vector α (n + 1)} : v.reverse.head = v.last :=
  by
  have : 0 = v.toList.length - 1 - n := by
    simp only [Nat.add_succ_sub_one, add_zero, toList_length, tsub_self, List.length_reverse]
  rw [← get_zero, last_def, get_eq_get, get_eq_get]
  simp_rw [to_list_reverse, Fin.val_last, Fin.val_zero, this]
  rw [List.get_reverse]
#align vector.reverse_nth_zero Vector.reverse_get_zero

section Scan

variable {β : Type _}

variable (f : β → α → β) (b : β)

variable (v : Vector α n)

/-- Construct a `Vector β (n + 1)` from a `Vector α n` by scanning `f : β → α → β`
from the "left", that is, from 0 to `Fin.last n`, using `b : β` as the starting value.
-/
def scanl : Vector β (n + 1) :=
  ⟨List.scanl f b v.toList, by rw [List.length_scanl, toList_length]⟩
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
  simpa only [scanl, toList_cons]
#align vector.scanl_cons Vector.scanl_cons

/-- The underlying `list` of a `Vector` after a `scanl` is the `List.scanl`
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
theorem scanl_singleton (v : Vector α 1) : scanl f b v = b ::ᵥ f b v.head ::ᵥ nil :=
  by
  rw [← cons_head_tail v]
  simp only [scanl_cons, scanl_nil, cons_head, singleton_tail]
#align vector.scanl_singleton Vector.scanl_singleton

/-- The first element of `scanl` of a vector `v : Vector α n`,
retrieved via `head`, is the starting value `b : β`.
-/
@[simp]
theorem scanl_head : (scanl f b v).head = b :=
  by
  cases n
  · have : v = nil := by simp only [Nat.zero_eq, eq_iff_true_of_subsingleton]
    simp only [this, scanl_nil, cons_head]
  · rw [← cons_head_tail v]
    simp only [← get_zero, nth_eq_get, toList_scanl, toList_cons, List.scanl, Fin.val_zero,
      List.get]
#align vector.scanl_head Vector.scanl_head

/-- For an index `i : Fin n`, the nth element of `scanl` of a
vector `v : Vector α n` at `i.succ`, is equal to the application
function `f : β → α → β` of the `i.cast_succ` element of
`scanl f b v` and `get v i`.

This lemma is the `get` version of `scanl_cons`.
-/
@[simp]
theorem scanl_get (i : Fin n) :
    (scanl f b v).get i.succ = f ((scanl f b v).get i.cast_succ) (v.get i) :=
  by
  cases' n with n
  · exact finZeroElim i
  induction' n with n hn generalizing b
  · have i0 : i = 0 := by simp only [eq_iff_true_of_subsingleton]
    simpa only [scanl_singleton, i0, get_zero]
  · rw [← cons_head_tail v, scanl_cons, get_cons_succ]
    refine' Fin.cases _ _ i
    · simp only [get_zero, scanl_head, Fin.castSucc_zero, cons_head]
    · intro i'
      simp only [hn, Fin.castSucc_fin_succ, get_cons_succ]
#align vector.scanl_nth Vector.scanl_get

end Scan

/- warning: vector.m_of_fn -> Vector.mOfFn is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] {α : Type.{u1}} {n : Nat}, ((Fin n) -> (m α)) -> (m (Vector.{u1} α n))
but is expected to have type
  forall {m : Type.{u2} -> Type.{u1}} [_inst_1 : Monad.{u2, u1} m] {α : Type.{u2}} {n : Nat}, ((Fin n) -> (m α)) -> (m (Vector.{u2} α n))
Case conversion may be inaccurate. Consider using '#align vector.m_of_fn Vector.mOfFnₓ'. -/
/-- Monadic analog of `Vector.ofFn`.
Given a monadic function on `fin n`, return a `Vector α n` inside the monad. -/
def mOfFn {m} [Monad m] {α : Type u} : ∀ {n}, (Fin n → m α) → m (Vector α n)
  | 0, f => pure nil
  | n + 1, f => do
    let a ← f 0
    let v ← m_of_fn fun i => f i.succ
    pure (a ::ᵥ v)
#align vector.m_of_fn Vector.mOfFn

theorem m_of_fn_pure {m} [Monad m] [LawfulMonad m] {α} :
    ∀ {n} (f : Fin n → α), (@mOfFn m _ _ _ fun i => pure (f i)) = pure (ofFn f)
  | 0, f => rfl
  | n + 1, f => by simp [m_of_fn, @m_of_fn_pure n, of_fn]
#align vector.m_of_fn_pure Vector.m_of_fn_pure

/- warning: vector.mmap -> Vector.mmap is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] {α : Type.{u3}} {β : Type.{u1}}, (α -> (m β)) -> (forall {n : Nat}, (Vector.{u3} α n) -> (m (Vector.{u1} β n)))
but is expected to have type
  forall {m : Type.{u3} -> Type.{u2}} [_inst_1 : Monad.{u3, u2} m] {α : Type.{u1}} {β : Type.{u3}}, (α -> (m β)) -> (forall {n : Nat}, (Vector.{u1} α n) -> (m (Vector.{u3} β n)))
Case conversion may be inaccurate. Consider using '#align vector.mmap Vector.mmapₓ'. -/
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
-- porting notes: requires noncomputable
@[elab_as_elim]
noncomputable def inductionOn {C : ∀ {n : ℕ}, Vector α n → Sort _} {n : ℕ} (v : Vector α n) (h_nil : C nil)
    (h_cons : ∀ {n : ℕ} {x : α} {w : Vector α n}, C w → C (x ::ᵥ w)) : C v :=
  by
  -- porting notes: removed `generalizing`: already generalized
  induction' n with n ih
  · rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    exact h_nil
  · rcases v with ⟨_ | ⟨a, v⟩, v_property⟩
    cases v_property
    apply @h_cons n _ ⟨v, (add_left_inj 1).mp v_property⟩
    apply ih
#align vector.induction_on Vector.inductionOn

-- check that the above works with `induction ... using`
example (v : Vector α n) : True := by induction v using Vector.inductionOn <;> trivial

variable {β γ : Type _}

/-- Define `C v w` by induction on a pair of vectors `v : Vector α n` and `w : Vector β n`. -/
-- porting notes: requires noncomputable
@[elab_as_elim]
noncomputable def inductionOn₂ {C : ∀ {n}, Vector α n → Vector β n → Sort _} (v : Vector α n) (w : Vector β n)
    (h_nil : C nil nil) (h_cons : ∀ {n a b} {x : Vector α n} {y}, C x y → C (a ::ᵥ x) (b ::ᵥ y)) :
    C v w := by
  -- porting notes: removed `generalizing`: already generalized
  induction' n with n ih
  · rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact h_nil
  · rcases v with ⟨_ | ⟨a, v⟩, v_property⟩
    cases v_property
    rcases w with ⟨_ | ⟨b, w⟩, w_property⟩
    cases w_property
    apply @h_cons n _ _ ⟨v, (add_left_inj 1).mp v_property⟩ ⟨w, (add_left_inj 1).mp w_property⟩
    apply ih
#align vector.induction_on₂ Vector.inductionOn₂

/-- Define `C u v w` by induction on a triplet of vectors
`u : Vector α n`, `v : Vector β n`, and `w : Vector γ b`. -/
-- porting notes: requires noncomputable
@[elab_as_elim]
noncomputable def inductionOn₃ {C : ∀ {n}, Vector α n → Vector β n → Vector γ n → Sort _} (u : Vector α n)
    (v : Vector β n) (w : Vector γ n) (h_nil : C nil nil nil)
    (h_cons : ∀ {n a b c} {x : Vector α n} {y z}, C x y z → C (a ::ᵥ x) (b ::ᵥ y) (c ::ᵥ z)) :
    C u v w := by
  -- porting notes: removed `generalizing`: already generalized
  induction' n with n ih
  · rcases u with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact h_nil
  · rcases u with ⟨_ | ⟨a, u⟩, u_property⟩
    cases u_property
    rcases v with ⟨_ | ⟨b, v⟩, v_property⟩
    cases v_property
    rcases w with ⟨_ | ⟨c, w⟩, w_property⟩
    cases w_property
    apply
      @h_cons n _ _ _ ⟨u, (add_left_inj 1).mp u_property⟩ ⟨v, (add_left_inj 1).mp v_property⟩
        ⟨w, (add_left_inj 1).mp w_property⟩
    apply ih
#align vector.induction_on₃ Vector.inductionOn₃

/-- Cast a vector to an array. -/
def toArray : Vector α n → Array n α
  | ⟨xs, h⟩ => cast (by rw [h]) xs.toArray
#align vector.to_array Vector.toArray

section InsertNth

variable {a : α}

/-- `v.insertNth a i` inserts `a` into the vector `v` at position `i`
(and shifting later components to the right). -/
def insertNth (a : α) (i : Fin (n + 1)) (v : Vector α n) : Vector α (n + 1) :=
  ⟨v.1.insertNth i a, by
    rw [List.length_insertNth, v.2]
    rw [v.2, ← Nat.succ_le_succ_iff]
    exact i.2⟩
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
  | ⟨i, hi⟩, ⟨j, hj⟩ =>
    by
    dsimp [insertNth, removeNth, Fin.succAbove, Fin.predAbove]
    simp only [Subtype.mk_eq_mk]
    split_ifs
    · convert (List.insertNth_removeNth_of_ge i (j - 1) _ _ _).symm
      · convert (Nat.succ_pred_eq_of_pos _).symm
        exact lt_of_le_of_lt (zero_le _) h
      · apply removeNth_val
      · convert hi
        exact v.2
      · exact Nat.le_pred_of_lt h
    · convert (List.insertNth_removeNth_of_le i j _ _ _).symm
      · apply removeNth_val
      · convert hi
        exact v.2
      · simpa using h
#align vector.remove_nth_insert_nth' Vector.removeNth_insertNth'

theorem insertNth_comm (a b : α) (i j : Fin (n + 1)) (h : i ≤ j) :
    ∀ v : Vector α n,
      (v.insertNth a i).insertNth b j.succ = (v.insertNth b j).insertNth a i.cast_succ
  | ⟨l, hl⟩ => by
    refine' Subtype.eq _
    simp only [insertNth_val, Fin.val_succ, Fin.castSucc, Fin.coe_castAdd]
    apply List.insertNth_comm
    · assumption
    · rw [hl]
      exact Nat.le_of_succ_le_succ j.2
#align vector.insert_nth_comm Vector.insertNth_comm

end InsertNth

-- porting notes: renamed to `modifyNth` from `updateNth` to align with `List`
section ModifyNth

/-- `modifyNth v n a` replaces the `n`th element of `v` with `a` -/
def modifyNth (v : Vector α n) (i : Fin n) (a : α) : Vector α n :=
  ⟨v.1.modifyNth i.1 a, by rw [List.length_set, v.2]⟩
#align vector.update_nth Vector.modifyNth

@[simp]
theorem toList_modifyNth (v : Vector α n) (i : Fin n) (a : α) :
    (v.modifyNth i a).toList = v.toList.modifyNth i a :=
  rfl
#align vector.to_list_update_nth Vector.toList_modifyNth

@[simp]
theorem get_modifyNth_same (v : Vector α n) (i : Fin n) (a : α) : (v.updateNth i a).get i = a := by
  cases v <;> cases i <;> simp [Vector.modifyNth, Vector.get_eq_get]
#align vector.nth_update_nth_same Vector.get_modifyNth_same

theorem get_modifyNth_of_ne {v : Vector α n} {i j : Fin n} (h : i ≠ j) (a : α) :
    (v.modifyNth i a).get j = v.get j := by
  cases v <;> cases i <;> cases j <;>
    simp [Vector.modifyNth, Vector.get_eq_get, List.get_set_of_ne (Fin.vne_of_ne h)]
#align vector.nth_update_nth_of_ne Vector.get_modifyNth_of_ne

theorem get_modifyNth_eq_if {v : Vector α n} {i j : Fin n} (a : α) :
    (v.modifyNth i a).get j = if i = j then a else v.get j := by
  split_ifs <;> try simp [*] <;> try rw [get_updateNth_of_ne] ; assumption
#align vector.nth_update_nth_eq_if Vector.get_modifyNth_eq_if

@[to_additive]
theorem prod_modifyNth [Monoid α] (v : Vector α n) (i : Fin n) (a : α) :
    (v.modifyNth i a).toList.prod = (v.take i).toList.prod * a * (v.drop (i + 1)).toList.prod :=
  by
  refine' (List.prod_set v.toList i a).trans _
  have : ↑i < v.to_list.length := lt_of_lt_of_le i.2 (le_of_eq v.2.symm)
  simp_all
#align vector.prod_update_nth Vector.prod_modifyNth

@[to_additive]
theorem prod_modifyNth' [CommGroup α] (v : Vector α n) (i : Fin n) (a : α) :
    (v.modifyNth i a).toList.prod = v.toList.prod * (v.get i)⁻¹ * a :=
  by
  refine' (List.prod_set' v.toList i a).trans _
  have : ↑i < v.to_list.length := lt_of_lt_of_le i.2 (le_of_eq v.2.symm)
  simp [this, get_eq_get, mul_assoc]
#align vector.prod_update_nth' Vector.prod_modifyNth'

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
#align vector.traverse Vector.traverse

section

variable {α β : Type u}

@[simp]
protected theorem traverse_def (f : α → F β) (x : α) :
    ∀ xs : Vector α n, (x ::ᵥ xs).traverse f = cons <$> f x <*> xs.traverse f := by
  rintro ⟨xs, rfl⟩ ; rfl
#align vector.traverse_def Vector.traverse_def

protected theorem id_traverse : ∀ x : Vector α n, x.traverse (pure: _ → Id _)= x :=
  by
  rintro ⟨x, rfl⟩; dsimp [Vector.traverse, cast]
  induction' x with x xs IH; · rfl
  simp! [IH]; rfl
#align vector.id_traverse Vector.id_traverse

end

open Function

variable [LawfulApplicative F] [LawfulApplicative G]

variable {α β γ : Type u}

-- We need to turn off the linter here as
-- the `IsLawfulTraversable` instance below expects a particular signature.
@[nolint unusedArguments]
protected theorem comp_traverse (f : β → F γ) (g : α → G β) :
    ∀ x : Vector α n,
      Vector.traverse (Comp.mk ∘ Functor.map f ∘ g) x =
        Comp.mk (Vector.traverse f <$> Vector.traverse g x) :=
  by
  rintro ⟨x, rfl⟩ <;> dsimp [Vector.traverse, cast] <;> induction' x with x xs <;>
      simp! [cast, *, functor_norm] <;>
    [rfl, simp [(· ∘ ·)]]
#align vector.comp_traverse Vector.comp_traverse

protected theorem traverse_eq_map_id {α β} (f : α → β) :
    ∀ x : Vector α n, x.traverse ((pure: _ → Id _) ∘ f) = (pure: _ → Id _) (map f x) := by
  rintro ⟨x, rfl⟩ ; simp! ; induction x <;> simp! [*, functor_norm] <;> rfl
#align vector.traverse_eq_map_id Vector.traverse_eq_map_id

variable (η : ApplicativeTransformation F G)

protected theorem naturality {α β : Type _} (f : α → F β) :
    ∀ x : Vector α n, η (x.traverse f) = x.traverse (@η _ ∘ f) := by
  rintro ⟨x, rfl⟩ <;> simp! [cast] <;> induction' x with x xs IH <;> simp! [*, functor_norm]
#align vector.naturality Vector.naturality

end Traverse

instance : Traversable.{u} (flip Vector n)
    where
  traverse := @Vector.traverse n
  map α β := @Vector.map.{u, u} α β n

instance : IsLawfulTraversable.{u} (flip Vector n)
    where
  id_traverse := @Vector.id_traverse n
  comp_traverse := @Vector.comp_traverse n
  traverse_eq_map_id := @Vector.traverse_eq_map_id n
  naturality := @Vector.naturality n
  id_map := by intros <;> cases x <;> simp! [(· <$> ·)]
  comp_map := by intros <;> cases x <;> simp! [(· <$> ·)]

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `reflect_name #[] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `reflect_name #[] -/
unsafe instance reflect [reflected_univ.{u}] {α : Type u} [has_reflect α] [reflected _ α] {n : ℕ} :
    has_reflect (Vector α n) := fun v =>
  @Vector.inductionOn α (fun n => reflected _) n v
    ((by
          trace
            "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `reflect_name #[]" :
          reflected _ @Vector.nil.{u}).subst
      q(α))
    fun n x xs ih =>
    (by
          trace
            "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `reflect_name #[]" :
          reflected _ @Vector.cons.{u}).subst₄
      q(α) q(n) q(x) ih
#align vector.reflect vector.reflect

end Vector
