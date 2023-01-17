/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.vector.basic
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Leanbin.Data.Vector
import Mathbin.Data.List.Nodup
import Mathbin.Data.List.OfFn
import Mathbin.Control.Applicative
import Mathbin.Meta.Univs

/-!
# Additional theorems and definitions about the `vector` type

This file introduces the infix notation `::ᵥ` for `vector.cons`.
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

/-- Two `v w : vector α n` are equal iff they are equal at every single index. -/
@[ext]
theorem ext : ∀ {v w : Vector α n} (h : ∀ m : Fin n, Vector.nth v m = Vector.nth w m), v = w
  | ⟨v, hv⟩, ⟨w, hw⟩, h =>
    Subtype.eq (List.ext_nthLe (by rw [hv, hw]) fun m hm hn => h ⟨m, hv ▸ hm⟩)
#align vector.ext Vector.ext

/-- The empty `vector` is a `subsingleton`. -/
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
    trans (cons_head_tail v).symm (by rw [h.1, h.2])⟩
#align vector.eq_cons_iff Vector.eq_cons_iff

theorem ne_cons_iff (a : α) (v : Vector α n.succ) (v' : Vector α n) :
    v ≠ a ::ᵥ v' ↔ v.head ≠ a ∨ v.tail ≠ v' := by rw [Ne.def, eq_cons_iff a v v', not_and_or]
#align vector.ne_cons_iff Vector.ne_cons_iff

theorem exists_eq_cons (v : Vector α n.succ) : ∃ (a : α)(as : Vector α n), v = a ::ᵥ as :=
  ⟨v.head, v.tail, (eq_cons_iff v.head v v.tail).2 ⟨rfl, rfl⟩⟩
#align vector.exists_eq_cons Vector.exists_eq_cons

@[simp]
theorem to_list_of_fn : ∀ {n} (f : Fin n → α), toList (ofFn f) = List.ofFn f
  | 0, f => rfl
  | n + 1, f => by rw [of_fn, List.of_fn_succ, to_list_cons, to_list_of_fn]
#align vector.to_list_of_fn Vector.to_list_of_fn

@[simp]
theorem mk_to_list : ∀ (v : Vector α n) (h), (⟨toList v, h⟩ : Vector α n) = v
  | ⟨l, h₁⟩, h₂ => rfl
#align vector.mk_to_list Vector.mk_to_list

@[simp]
theorem length_coe (v : Vector α n) :
    ((coe : { l : List α // l.length = n } → List α) v).length = n :=
  v.2
#align vector.length_coe Vector.length_coe

@[simp]
theorem to_list_map {β : Type _} (v : Vector α n) (f : α → β) : (v.map f).toList = v.toList.map f :=
  by cases v <;> rfl
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

theorem nth_eq_nth_le :
    ∀ (v : Vector α n) (i), nth v i = v.toList.nthLe i.1 (by rw [to_list_length] <;> exact i.2)
  | ⟨l, h⟩, i => rfl
#align vector.nth_eq_nth_le Vector.nth_eq_nth_le

@[simp]
theorem nth_repeat (a : α) (i : Fin n) : (Vector.repeat a n).nth i = a := by apply List.nthLe_repeat
#align vector.nth_repeat Vector.nth_repeat

@[simp]
theorem nth_map {β : Type _} (v : Vector α n) (f : α → β) (i : Fin n) :
    (v.map f).nth i = f (v.nth i) := by simp [nth_eq_nth_le]
#align vector.nth_map Vector.nth_map

@[simp]
theorem nth_of_fn {n} (f : Fin n → α) (i) : nth (ofFn f) i = f i := by
  rw [nth_eq_nth_le, ← List.nth_le_of_fn f] <;> congr <;> apply to_list_of_fn
#align vector.nth_of_fn Vector.nth_of_fn

@[simp]
theorem of_fn_nth (v : Vector α n) : ofFn (nth v) = v :=
  by
  rcases v with ⟨l, rfl⟩
  apply to_list_injective
  change nth ⟨l, Eq.refl _⟩ with fun i => nth ⟨l, rfl⟩ i
  simpa only [to_list_of_fn] using List.of_fn_nth_le _
#align vector.of_fn_nth Vector.of_fn_nth

/-- The natural equivalence between length-`n` vectors and functions from `fin n`. -/
def Equiv.vectorEquivFin (α : Type _) (n : ℕ) : Vector α n ≃ (Fin n → α) :=
  ⟨Vector.nth, Vector.ofFn, Vector.of_fn_nth, fun f => funext <| Vector.nth_of_fn f⟩
#align equiv.vector_equiv_fin Equiv.vectorEquivFin

theorem nth_tail (x : Vector α n) (i) : x.tail.nth i = x.nth ⟨i.1 + 1, lt_tsub_iff_right.mp i.2⟩ :=
  by rcases x with ⟨_ | _, h⟩ <;> rfl
#align vector.nth_tail Vector.nth_tail

@[simp]
theorem nth_tail_succ : ∀ (v : Vector α n.succ) (i : Fin n), nth (tail v) i = nth v i.succ
  | ⟨a :: l, e⟩, ⟨i, h⟩ => by simp [nth_eq_nth_le] <;> rfl
#align vector.nth_tail_succ Vector.nth_tail_succ

@[simp]
theorem tail_val : ∀ v : Vector α n.succ, v.tail.val = v.val.tail
  | ⟨a :: l, e⟩ => rfl
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
theorem tail_of_fn {n : ℕ} (f : Fin n.succ → α) : tail (ofFn f) = ofFn fun i => f i.succ :=
  (of_fn_nth _).symm.trans <| by
    congr
    funext i
    cases i
    simp
#align vector.tail_of_fn Vector.tail_of_fn

@[simp]
theorem to_list_empty (v : Vector α 0) : v.toList = [] :=
  List.length_eq_zero.mp v.2
#align vector.to_list_empty Vector.to_list_empty

/-- The list that makes up a `vector` made up of a single element,
retrieved via `to_list`, is equal to the list of that single element. -/
@[simp]
theorem to_list_singleton (v : Vector α 1) : v.toList = [v.head] :=
  by
  rw [← v.cons_head_tail]
  simp only [to_list_cons, to_list_nil, cons_head, eq_self_iff_true, and_self_iff, singleton_tail]
#align vector.to_list_singleton Vector.to_list_singleton

@[simp]
theorem empty_to_list_eq_ff (v : Vector α (n + 1)) : v.toList.Empty = ff :=
  match v with
  | ⟨a :: as, _⟩ => rfl
#align vector.empty_to_list_eq_ff Vector.empty_to_list_eq_ff

theorem not_empty_to_list (v : Vector α (n + 1)) : ¬v.toList.Empty := by
  simp only [empty_to_list_eq_ff, Bool.coe_sort_false, not_false_iff]
#align vector.not_empty_to_list Vector.not_empty_to_list

/-- Mapping under `id` does not change a vector. -/
@[simp]
theorem map_id {n : ℕ} (v : Vector α n) : Vector.map id v = v :=
  Vector.eq _ _ (by simp only [List.map_id, Vector.to_list_map])
#align vector.map_id Vector.map_id

theorem nodup_iff_nth_inj {v : Vector α n} : v.toList.Nodup ↔ Function.Injective v.nth :=
  by
  cases' v with l hl
  subst hl
  simp only [List.nodup_iff_nthLe_inj]
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
#align vector.nodup_iff_nth_inj Vector.nodup_iff_nth_inj

theorem head'_to_list : ∀ v : Vector α n.succ, (toList v).head' = some (head v)
  | ⟨a :: l, e⟩ => rfl
#align vector.head'_to_list Vector.head'_to_list

/-- Reverse a vector. -/
def reverse (v : Vector α n) : Vector α n :=
  ⟨v.toList.reverse, by simp⟩
#align vector.reverse Vector.reverse

/-- The `list` of a vector after a `reverse`, retrieved by `to_list` is equal
to the `list.reverse` after retrieving a vector's `to_list`. -/
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
theorem nth_zero : ∀ v : Vector α n.succ, nth v 0 = head v
  | ⟨a :: l, e⟩ => rfl
#align vector.nth_zero Vector.nth_zero

@[simp]
theorem head_of_fn {n : ℕ} (f : Fin n.succ → α) : head (ofFn f) = f 0 := by
  rw [← nth_zero, nth_of_fn]
#align vector.head_of_fn Vector.head_of_fn

@[simp]
theorem nth_cons_zero (a : α) (v : Vector α n) : nth (a ::ᵥ v) 0 = a := by simp [nth_zero]
#align vector.nth_cons_zero Vector.nth_cons_zero

/-- Accessing the `nth` element of a vector made up
of one element `x : α` is `x` itself. -/
@[simp]
theorem nth_cons_nil {ix : Fin 1} (x : α) : nth (x ::ᵥ nil) ix = x := by convert nth_cons_zero x nil
#align vector.nth_cons_nil Vector.nth_cons_nil

@[simp]
theorem nth_cons_succ (a : α) (v : Vector α n) (i : Fin n) : nth (a ::ᵥ v) i.succ = nth v i := by
  rw [← nth_tail_succ, tail_cons]
#align vector.nth_cons_succ Vector.nth_cons_succ

/-- The last element of a `vector`, given that the vector is at least one element. -/
def last (v : Vector α (n + 1)) : α :=
  v.nth (Fin.last n)
#align vector.last Vector.last

/-- The last element of a `vector`, given that the vector is at least one element. -/
theorem last_def {v : Vector α (n + 1)} : v.last = v.nth (Fin.last n) :=
  rfl
#align vector.last_def Vector.last_def

/-- The `last` element of a vector is the `head` of the `reverse` vector. -/
theorem reverse_nth_zero {v : Vector α (n + 1)} : v.reverse.head = v.last :=
  by
  have : 0 = v.to_list.length - 1 - n := by
    simp only [Nat.add_succ_sub_one, add_zero, to_list_length, tsub_self, List.length_reverse]
  rw [← nth_zero, last_def, nth_eq_nth_le, nth_eq_nth_le]
  simp_rw [to_list_reverse, [anonymous], Fin.val_last, Fin.val_zero, this]
  rw [List.nthLe_reverse]
#align vector.reverse_nth_zero Vector.reverse_nth_zero

section Scan

variable {β : Type _}

variable (f : β → α → β) (b : β)

variable (v : Vector α n)

/-- Construct a `vector β (n + 1)` from a `vector α n` by scanning `f : β → α → β`
from the "left", that is, from 0 to `fin.last n`, using `b : β` as the starting value.
-/
def scanl : Vector β (n + 1) :=
  ⟨List.scanl f b v.toList, by rw [List.length_scanl, to_list_length]⟩
#align vector.scanl Vector.scanl

/-- Providing an empty vector to `scanl` gives the starting value `b : β`. -/
@[simp]
theorem scanl_nil : scanl f b nil = b ::ᵥ nil :=
  rfl
#align vector.scanl_nil Vector.scanl_nil

/-- The recursive step of `scanl` splits a vector `x ::ᵥ v : vector α (n + 1)`
into the provided starting value `b : β` and the recursed `scanl`
`f b x : β` as the starting value.

This lemma is the `cons` version of `scanl_nth`.
-/
@[simp]
theorem scanl_cons (x : α) : scanl f b (x ::ᵥ v) = b ::ᵥ scanl f (f b x) v := by
  simpa only [scanl, to_list_cons]
#align vector.scanl_cons Vector.scanl_cons

/-- The underlying `list` of a `vector` after a `scanl` is the `list.scanl`
of the underlying `list` of the original `vector`.
-/
@[simp]
theorem scanl_val : ∀ {v : Vector α n}, (scanl f b v).val = List.scanl f b v.val
  | ⟨l, hl⟩ => rfl
#align vector.scanl_val Vector.scanl_val

/-- The `to_list` of a `vector` after a `scanl` is the `list.scanl`
of the `to_list` of the original `vector`.
-/
@[simp]
theorem to_list_scanl : (scanl f b v).toList = List.scanl f b v.toList :=
  rfl
#align vector.to_list_scanl Vector.to_list_scanl

/-- The recursive step of `scanl` splits a vector made up of a single element
`x ::ᵥ nil : vector α 1` into a `vector` of the provided starting value `b : β`
and the mapped `f b x : β` as the last value.
-/
@[simp]
theorem scanl_singleton (v : Vector α 1) : scanl f b v = b ::ᵥ f b v.head ::ᵥ nil :=
  by
  rw [← cons_head_tail v]
  simp only [scanl_cons, scanl_nil, cons_head, singleton_tail]
#align vector.scanl_singleton Vector.scanl_singleton

/-- The first element of `scanl` of a vector `v : vector α n`,
retrieved via `head`, is the starting value `b : β`.
-/
@[simp]
theorem scanl_head : (scanl f b v).head = b :=
  by
  cases n
  · have : v = nil := by simp only [eq_iff_true_of_subsingleton]
    simp only [this, scanl_nil, cons_head]
  · rw [← cons_head_tail v]
    simp only [← nth_zero, nth_eq_nth_le, to_list_scanl, to_list_cons, List.scanl, Fin.val_zero,
      List.nthLe]
#align vector.scanl_head Vector.scanl_head

/-- For an index `i : fin n`, the `nth` element of `scanl` of a
vector `v : vector α n` at `i.succ`, is equal to the application
function `f : β → α → β` of the `i.cast_succ` element of
`scanl f b v` and `nth v i`.

This lemma is the `nth` version of `scanl_cons`.
-/
@[simp]
theorem scanl_nth (i : Fin n) :
    (scanl f b v).nth i.succ = f ((scanl f b v).nth i.cast_succ) (v.nth i) :=
  by
  cases n
  · exact finZeroElim i
  induction' n with n hn generalizing b
  · have i0 : i = 0 := by simp only [eq_iff_true_of_subsingleton]
    simpa only [scanl_singleton, i0, nth_zero]
  · rw [← cons_head_tail v, scanl_cons, nth_cons_succ]
    refine' Fin.cases _ _ i
    · simp only [nth_zero, scanl_head, Fin.castSucc_zero, cons_head]
    · intro i'
      simp only [hn, Fin.castSucc_fin_succ, nth_cons_succ]
#align vector.scanl_nth Vector.scanl_nth

end Scan

/- warning: vector.m_of_fn -> Vector.mOfFn is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] {α : Type.{u1}} {n : Nat}, ((Fin n) -> (m α)) -> (m (Vector.{u1} α n))
but is expected to have type
  forall {m : Type.{u2} -> Type.{u1}} [_inst_1 : Monad.{u2, u1} m] {α : Type.{u2}} {n : Nat}, ((Fin n) -> (m α)) -> (m (Vector.{u2} α n))
Case conversion may be inaccurate. Consider using '#align vector.m_of_fn Vector.mOfFnₓ'. -/
/-- Monadic analog of `vector.of_fn`.
Given a monadic function on `fin n`, return a `vector α n` inside the monad. -/
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
  | 0, xs => pure nil
  | n + 1, xs => do
    let h' ← f xs.head
    let t' ← @mmap n xs.tail
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
  | _, ⟨l, rfl⟩ => rfl
#align vector.mmap_cons Vector.mmap_cons

/-- Define `C v` by induction on `v : vector α n`.

This function has two arguments: `h_nil` handles the base case on `C nil`,
and `h_cons` defines the inductive step using `∀ x : α, C w → C (x ::ᵥ w)`.

This can be used as `induction v using vector.induction_on`. -/
@[elab_as_elim]
def inductionOn {C : ∀ {n : ℕ}, Vector α n → Sort _} {n : ℕ} (v : Vector α n) (h_nil : C nil)
    (h_cons : ∀ {n : ℕ} {x : α} {w : Vector α n}, C w → C (x ::ᵥ w)) : C v :=
  by
  induction' n with n ih generalizing v
  · rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    exact h_nil
  · rcases v with ⟨_ | ⟨a, v⟩, _⟩
    cases v_property
    apply @h_cons n _ ⟨v, (add_left_inj 1).mp v_property⟩
    apply ih
#align vector.induction_on Vector.inductionOn

-- check that the above works with `induction ... using`
example (v : Vector α n) : True := by induction v using Vector.inductionOn <;> trivial

variable {β γ : Type _}

/-- Define `C v w` by induction on a pair of vectors `v : vector α n` and `w : vector β n`. -/
@[elab_as_elim]
def inductionOn₂ {C : ∀ {n}, Vector α n → Vector β n → Sort _} (v : Vector α n) (w : Vector β n)
    (h_nil : C nil nil) (h_cons : ∀ {n a b} {x : Vector α n} {y}, C x y → C (a ::ᵥ x) (b ::ᵥ y)) :
    C v w := by
  induction' n with n ih generalizing v w
  · rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact h_nil
  · rcases v with ⟨_ | ⟨a, v⟩, _⟩
    cases v_property
    rcases w with ⟨_ | ⟨b, w⟩, _⟩
    cases w_property
    apply @h_cons n _ _ ⟨v, (add_left_inj 1).mp v_property⟩ ⟨w, (add_left_inj 1).mp w_property⟩
    apply ih
#align vector.induction_on₂ Vector.inductionOn₂

/-- Define `C u v w` by induction on a triplet of vectors
`u : vector α n`, `v : vector β n`, and `w : vector γ b`. -/
@[elab_as_elim]
def inductionOn₃ {C : ∀ {n}, Vector α n → Vector β n → Vector γ n → Sort _} (u : Vector α n)
    (v : Vector β n) (w : Vector γ n) (h_nil : C nil nil nil)
    (h_cons : ∀ {n a b c} {x : Vector α n} {y z}, C x y z → C (a ::ᵥ x) (b ::ᵥ y) (c ::ᵥ z)) :
    C u v w := by
  induction' n with n ih generalizing u v w
  · rcases u with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact h_nil
  · rcases u with ⟨_ | ⟨a, u⟩, _⟩
    cases u_property
    rcases v with ⟨_ | ⟨b, v⟩, _⟩
    cases v_property
    rcases w with ⟨_ | ⟨c, w⟩, _⟩
    cases w_property
    apply
      @h_cons n _ _ _ ⟨u, (add_left_inj 1).mp u_property⟩ ⟨v, (add_left_inj 1).mp v_property⟩
        ⟨w, (add_left_inj 1).mp w_property⟩
    apply ih
#align vector.induction_on₃ Vector.inductionOn₃

/-- Cast a vector to an array. -/
def toArray : Vector α n → Array' n α
  | ⟨xs, h⟩ => cast (by rw [h]) xs.toArray
#align vector.to_array Vector.toArray

section InsertNth

variable {a : α}

/-- `v.insert_nth a i` inserts `a` into the vector `v` at position `i`
(and shifting later components to the right). -/
def insertNth (a : α) (i : Fin (n + 1)) (v : Vector α n) : Vector α (n + 1) :=
  ⟨v.1.insertNth i a, by
    rw [List.length_insertNth, v.2]
    rw [v.2, ← Nat.succ_le_succ_iff]
    exact i.2⟩
#align vector.insert_nth Vector.insertNth

theorem insert_nth_val {i : Fin (n + 1)} {v : Vector α n} :
    (v.insertNth a i).val = v.val.insertNth i.1 a :=
  rfl
#align vector.insert_nth_val Vector.insert_nth_val

@[simp]
theorem remove_nth_val {i : Fin n} : ∀ {v : Vector α n}, (removeNth i v).val = v.val.removeNth i
  | ⟨l, hl⟩ => rfl
#align vector.remove_nth_val Vector.remove_nth_val

theorem remove_nth_insert_nth {v : Vector α n} {i : Fin (n + 1)} :
    removeNth i (insertNth a i v) = v :=
  Subtype.eq <| List.removeNth_insertNth i.1 v.1
#align vector.remove_nth_insert_nth Vector.remove_nth_insert_nth

theorem remove_nth_insert_nth' {v : Vector α (n + 1)} :
    ∀ {i : Fin (n + 1)} {j : Fin (n + 2)},
      removeNth (j.succAbove i) (insertNth a j v) = insertNth a (i.predAbove j) (removeNth i v)
  | ⟨i, hi⟩, ⟨j, hj⟩ =>
    by
    dsimp [insert_nth, remove_nth, Fin.succAbove, Fin.predAbove]
    simp only [Subtype.mk_eq_mk]
    split_ifs
    · convert (List.insertNth_removeNth_of_ge i (j - 1) _ _ _).symm
      · convert (Nat.succ_pred_eq_of_pos _).symm
        exact lt_of_le_of_lt (zero_le _) h
      · apply remove_nth_val
      · convert hi
        exact v.2
      · exact Nat.le_pred_of_lt h
    · convert (List.insertNth_removeNth_of_le i j _ _ _).symm
      · apply remove_nth_val
      · convert hi
        exact v.2
      · simpa using h
#align vector.remove_nth_insert_nth' Vector.remove_nth_insert_nth'

theorem insert_nth_comm (a b : α) (i j : Fin (n + 1)) (h : i ≤ j) :
    ∀ v : Vector α n,
      (v.insertNth a i).insertNth b j.succ = (v.insertNth b j).insertNth a i.cast_succ
  | ⟨l, hl⟩ => by
    refine' Subtype.eq _
    simp only [insert_nth_val, Fin.val_succ, Fin.castSucc, [anonymous], Fin.coe_castAdd]
    apply List.insertNth_comm
    · assumption
    · rw [hl]
      exact Nat.le_of_succ_le_succ j.2
#align vector.insert_nth_comm Vector.insert_nth_comm

end InsertNth

section UpdateNth

/-- `update_nth v n a` replaces the `n`th element of `v` with `a` -/
def updateNth (v : Vector α n) (i : Fin n) (a : α) : Vector α n :=
  ⟨v.1.updateNth i.1 a, by rw [List.length_set, v.2]⟩
#align vector.update_nth Vector.updateNth

@[simp]
theorem to_list_update_nth (v : Vector α n) (i : Fin n) (a : α) :
    (v.updateNth i a).toList = v.toList.updateNth i a :=
  rfl
#align vector.to_list_update_nth Vector.to_list_update_nth

@[simp]
theorem nth_update_nth_same (v : Vector α n) (i : Fin n) (a : α) : (v.updateNth i a).nth i = a := by
  cases v <;> cases i <;> simp [Vector.updateNth, Vector.nth_eq_nth_le]
#align vector.nth_update_nth_same Vector.nth_update_nth_same

theorem nth_update_nth_of_ne {v : Vector α n} {i j : Fin n} (h : i ≠ j) (a : α) :
    (v.updateNth i a).nth j = v.nth j := by
  cases v <;> cases i <;> cases j <;>
    simp [Vector.updateNth, Vector.nth_eq_nth_le, List.nthLe_set_of_ne (Fin.vne_of_ne h)]
#align vector.nth_update_nth_of_ne Vector.nth_update_nth_of_ne

theorem nth_update_nth_eq_if {v : Vector α n} {i j : Fin n} (a : α) :
    (v.updateNth i a).nth j = if i = j then a else v.nth j := by
  split_ifs <;> try simp [*] <;> try rw [nth_update_nth_of_ne] <;> assumption
#align vector.nth_update_nth_eq_if Vector.nth_update_nth_eq_if

@[to_additive]
theorem prod_update_nth [Monoid α] (v : Vector α n) (i : Fin n) (a : α) :
    (v.updateNth i a).toList.Prod = (v.take i).toList.Prod * a * (v.drop (i + 1)).toList.Prod :=
  by
  refine' (List.prod_set v.to_list i a).trans _
  have : ↑i < v.to_list.length := lt_of_lt_of_le i.2 (le_of_eq v.2.symm)
  simp_all
#align vector.prod_update_nth Vector.prod_update_nth

@[to_additive]
theorem prod_update_nth' [CommGroup α] (v : Vector α n) (i : Fin n) (a : α) :
    (v.updateNth i a).toList.Prod = v.toList.Prod * (v.nth i)⁻¹ * a :=
  by
  refine' (List.prod_set' v.to_list i a).trans _
  have : ↑i < v.to_list.length := lt_of_lt_of_le i.2 (le_of_eq v.2.symm)
  simp [this, nth_eq_nth_le, mul_assoc]
#align vector.prod_update_nth' Vector.prod_update_nth'

end UpdateNth

end Vector

namespace Vector

section Traverse

variable {F G : Type u → Type u}

variable [Applicative F] [Applicative G]

open Applicative Functor

open List (cons)

open Nat

private def traverse_aux {α β : Type u} (f : α → F β) : ∀ x : List α, F (Vector β x.length)
  | [] => pure Vector.nil
  | x :: xs => Vector.cons <$> f x <*> traverse_aux xs
#align vector.traverse_aux vector.traverse_aux

/-- Apply an applicative function to each component of a vector. -/
protected def traverse {α β : Type u} (f : α → F β) : Vector α n → F (Vector β n)
  | ⟨v, Hv⟩ => cast (by rw [Hv]) <| traverseAux f v
#align vector.traverse Vector.traverse

section

variable {α β : Type u}

@[simp]
protected theorem traverse_def (f : α → F β) (x : α) :
    ∀ xs : Vector α n, (x ::ᵥ xs).traverse f = cons <$> f x <*> xs.traverse f := by
  rintro ⟨xs, rfl⟩ <;> rfl
#align vector.traverse_def Vector.traverse_def

protected theorem id_traverse : ∀ x : Vector α n, x.traverse id.mk = x :=
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
-- the `is_lawful_traversable` instance below expects a particular signature.
@[nolint unused_arguments]
protected theorem comp_traverse (f : β → F γ) (g : α → G β) :
    ∀ x : Vector α n,
      Vector.traverse (comp.mk ∘ Functor.map f ∘ g) x =
        Comp.mk (Vector.traverse f <$> Vector.traverse g x) :=
  by
  rintro ⟨x, rfl⟩ <;> dsimp [Vector.traverse, cast] <;> induction' x with x xs <;>
      simp! [cast, *, functor_norm] <;>
    [rfl, simp [(· ∘ ·)]]
#align vector.comp_traverse Vector.comp_traverse

protected theorem traverse_eq_map_id {α β} (f : α → β) :
    ∀ x : Vector α n, x.traverse (id.mk ∘ f) = id.mk (map f x) := by
  rintro ⟨x, rfl⟩ <;> simp! <;> induction x <;> simp! [*, functor_norm] <;> rfl
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

