/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Data.Multiset.Pi

/-!
# The cartesian product of lists

## Main definitions

* `List.pi`: Cartesian product of lists indexed by a list.
-/

namespace List

namespace Pi
variable {ι : Type*} [DecidableEq ι] {α : ι → Sort*}

/-- Given `α : ι → Sort*`, `Pi.nil α` is the trivial dependent function out of the empty list. -/
def nil (α : ι → Sort*) : (∀ i ∈ ([] : List ι), α i) :=
  nofun

variable {i : ι} {l : List ι}

/-- Given `f` a function whose domain is `i :: l`, get its value at `i`. -/
def head (f : ∀ j ∈ i :: l, α j) : α i :=
  f i mem_cons_self

/-- Given `f` a function whose domain is `i :: l`, produce a function whose domain
is restricted to `l`. -/
def tail (f : ∀ j ∈ i :: l, α j) : ∀ j ∈ l, α j :=
  fun j hj ↦ f j (mem_cons_of_mem _ hj)

variable (i l)

/-- Given `α : ι → Sort*`, a list `l` and a term `i`, as well as a term `a : α i` and a
function `f` such that `f j : α j` for all `j` in `l`, `Pi.cons a f` is a function `g` such
that `g k : α k` for all `k` in `i :: l`. -/
def cons (a : α i) (f : ∀ j ∈ l, α j) : ∀ j ∈ i :: l, α j :=
  Multiset.Pi.cons (α := ι) l _ a f

variable {i l}

lemma cons_def (a : α i) (f : ∀ j ∈ l, α j) : cons _ _ a f =
    fun j hj ↦ if h : j = i then h.symm.rec a else f j <| (mem_cons.1 hj).resolve_left h :=
  rfl

@[simp] lemma _root_.Multiset.Pi.cons_coe {l : List ι} (a : α i) (f : ∀ j ∈ l, α j) :
    Multiset.Pi.cons l _ a f = cons _ _ a f :=
  rfl

@[simp] lemma cons_eta (f : ∀ j ∈ i :: l, α j) :
    cons _ _ (head f) (tail f) = f :=
  Multiset.Pi.cons_eta (α := ι) (m := l) f

lemma cons_map (a : α i) (f : ∀ j ∈ l, α j)
    {α' : ι → Sort*} (φ : ∀ ⦃j⦄, α j → α' j) :
    cons _ _ (φ a) (fun j hj ↦ φ (f j hj)) = (fun j hj ↦ φ ((cons _ _ a f) j hj)) :=
  Multiset.Pi.cons_map _ _ _

lemma forall_rel_cons_ext {r : ∀ ⦃i⦄, α i → α i → Prop} {a₁ a₂ : α i} {f₁ f₂ : ∀ j ∈ l, α j}
    (ha : r a₁ a₂) (hf : ∀ (i : ι) (hi : i ∈ l), r (f₁ i hi) (f₂ i hi)) :
    ∀ j hj, r (cons _ _ a₁ f₁ j hj) (cons _ _ a₂ f₂ j hj) :=
  Multiset.Pi.forall_rel_cons_ext (α := ι) (m := l) ha hf

end Pi

variable {ι : Type*} [DecidableEq ι] {α : ι → Type*}

/-- `pi xs f` creates the list of functions `g` such that, for `x ∈ xs`, `g x ∈ f x` -/
def pi : ∀ l : List ι, (∀ i, List (α i)) → List (∀ i, i ∈ l → α i)
  |     [],  _ => [List.Pi.nil α]
  | i :: l, fs => (fs i).flatMap (fun b ↦ (pi l fs).map (List.Pi.cons _ _ b))

@[simp] lemma pi_nil (t : ∀ i, List (α i)) :
    pi [] t = [Pi.nil α] :=
  rfl

@[simp] lemma pi_cons (i : ι) (l : List ι) (t : ∀ j, List (α j)) :
    pi (i :: l) t = ((t i).flatMap fun b ↦ (pi l t).map <| Pi.cons _ _ b) :=
  rfl

lemma _root_.Multiset.pi_coe (l : List ι) (fs : ∀ i, List (α i)) :
    (l : Multiset ι).pi (fs ·) = (↑(pi l fs) : Multiset (∀ i ∈ l, α i)) := by
  induction' l with i l ih
  · change Multiset.pi 0 _ = _
    simp only [Multiset.coe_singleton, Multiset.pi_zero, pi_nil, Multiset.singleton_inj]
    ext i hi
    simp at hi
  · change Multiset.pi (i ::ₘ ↑l) _ = _
    simp [ih, Multiset.coe_bind, - Multiset.cons_coe]

lemma mem_pi {l : List ι} (fs : ∀ i, List (α i)) :
    ∀ f : ∀ i ∈ l, α i, (f ∈ pi l fs) ↔ (∀ i (hi : i ∈ l), f i hi ∈ fs i) := by
  intros f
  convert @Multiset.mem_pi ι _ α ↑l (fs ·) f using 1
  rw [Multiset.pi_coe]
  rfl

end List
