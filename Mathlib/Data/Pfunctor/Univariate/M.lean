/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module data.pfunctor.univariate.M
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Pfunctor.Univariate.Basic

/-!
# M-types

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.
-/


universe u v w

open Nat Function

open List hiding head'

variable (F : Pfunctor.{u})

-- mathport name: «expr♯ »
local prefix:0 "♯" => cast (by first |simp [*]|cc|solve_by_elim)

namespace Pfunctor

namespace Approx

/-- `cofix_a F n` is an `n` level approximation of a M-type -/
inductive CofixA : ℕ → Type u
  | continue : cofix_a 0
  | intro {n} : ∀ a, (F.B a → cofix_a n) → cofix_a (succ n)
#align pfunctor.approx.cofix_a Pfunctor.Approx.CofixA

/-- default inhabitant of `cofix_a` -/
protected def CofixA.default [Inhabited F.A] : ∀ n, CofixA F n
  | 0 => CofixA.continue
  | succ n => CofixA.intro default fun _ => cofix_a.default n
#align pfunctor.approx.cofix_a.default Pfunctor.Approx.CofixA.default

instance [Inhabited F.A] {n} : Inhabited (CofixA F n) :=
  ⟨CofixA.default F n⟩

theorem cofixA_eq_zero : ∀ x y : CofixA F 0, x = y
  | cofix_a.continue, cofix_a.continue => rfl
#align pfunctor.approx.cofix_a_eq_zero Pfunctor.Approx.cofixA_eq_zero

variable {F}

/-- The label of the root of the tree for a non-trivial
approximation of the cofix of a pfunctor.
-/
def head' : ∀ {n}, CofixA F (succ n) → F.A
  | n, cofix_a.intro i _ => i
#align pfunctor.approx.head' Pfunctor.Approx.head'

/-- for a non-trivial approximation, return all the subtrees of the root -/
def children' : ∀ {n} (x : CofixA F (succ n)), F.B (head' x) → CofixA F n
  | n, cofix_a.intro a f => f
#align pfunctor.approx.children' Pfunctor.Approx.children'

theorem approx_eta {n : ℕ} (x : CofixA F (n + 1)) : x = CofixA.intro (head' x) (children' x) := by
  cases x <;> rfl
#align pfunctor.approx.approx_eta Pfunctor.Approx.approx_eta

/-- Relation between two approximations of the cofix of a pfunctor
that state they both contain the same data until one of them is truncated -/
inductive Agree : ∀ {n : ℕ}, CofixA F n → CofixA F (n + 1) → Prop
  | continue (x : CofixA F 0) (y : CofixA F 1) : agree x y
  |
  intro {n} {a} (x : F.B a → CofixA F n) (x' : F.B a → CofixA F (n + 1)) :
    (∀ i : F.B a, agree (x i) (x' i)) → agree (CofixA.intro a x) (CofixA.intro a x')
#align pfunctor.approx.agree Pfunctor.Approx.Agree

/-- Given an infinite series of approximations `approx`,
`all_agree approx` states that they are all consistent with each other.
-/
def AllAgree (x : ∀ n, CofixA F n) :=
  ∀ n, Agree (x n) (x (succ n))
#align pfunctor.approx.all_agree Pfunctor.Approx.AllAgree

@[simp]
theorem agree_trival {x : CofixA F 0} {y : CofixA F 1} : Agree x y := by constructor
#align pfunctor.approx.agree_trival Pfunctor.Approx.agree_trival

theorem agree_children {n : ℕ} (x : CofixA F (succ n)) (y : CofixA F (succ n + 1)) {i j}
    (h₀ : HEq i j) (h₁ : Agree x y) : Agree (children' x i) (children' y j) :=
  by
  cases' h₁ with _ _ _ _ _ _ hagree; cases h₀
  apply hagree
#align pfunctor.approx.agree_children Pfunctor.Approx.agree_children

/-- `truncate a` turns `a` into a more limited approximation -/
def truncate : ∀ {n : ℕ}, CofixA F (n + 1) → CofixA F n
  | 0, cofix_a.intro _ _ => CofixA.continue
  | succ n, cofix_a.intro i f => CofixA.intro i <| truncate ∘ f
#align pfunctor.approx.truncate Pfunctor.Approx.truncate

theorem truncate_eq_of_agree {n : ℕ} (x : CofixA F n) (y : CofixA F (succ n)) (h : Agree x y) :
    truncate y = x := by
  induction n generalizing x y <;> cases x <;> cases y
  · rfl
  · cases' h with _ _ _ _ _ h₀ h₁
    cases h
    simp only [truncate, Function.comp, true_and_iff, eq_self_iff_true, hEq_iff_eq]
    ext y
    apply n_ih
    apply h₁
#align pfunctor.approx.truncate_eq_of_agree Pfunctor.Approx.truncate_eq_of_agree

variable {X : Type w}

variable (f : X → F.Obj X)

/-- `s_corec f i n` creates an approximation of height `n`
of the final coalgebra of `f` -/
def sCorec : ∀ (i : X) (n), CofixA F n
  | _, 0 => CofixA.continue
  | j, succ n => CofixA.intro (f j).1 fun i => s_corec ((f j).2 i) _
#align pfunctor.approx.s_corec Pfunctor.Approx.sCorec

theorem P_corec (i : X) (n : ℕ) : Agree (sCorec f i n) (sCorec f i (succ n)) :=
  by
  induction' n with n generalizing i
  constructor
  cases' h : f i with y g
  constructor
  introv
  apply n_ih
#align pfunctor.approx.P_corec Pfunctor.Approx.P_corec

/-- `path F` provides indices to access internal nodes in `corec F` -/
def Path (F : Pfunctor.{u}) :=
  List F.IdxCat
#align pfunctor.approx.path Pfunctor.Approx.Path

instance Path.inhabited : Inhabited (Path F) :=
  ⟨[]⟩
#align pfunctor.approx.path.inhabited Pfunctor.Approx.Path.inhabited

open List Nat

instance : Subsingleton (CofixA F 0) :=
  ⟨by
    intros
    casesm*cofix_a F 0
    rfl⟩

theorem head_succ' (n m : ℕ) (x : ∀ n, CofixA F n) (Hconsistent : AllAgree x) :
    head' (x (succ n)) = head' (x (succ m)) :=
  by
  suffices ∀ n, head' (x (succ n)) = head' (x 1) by simp [this]
  clear m n
  intro
  cases' h₀ : x (succ n) with _ i₀ f₀
  cases' h₁ : x 1 with _ i₁ f₁
  dsimp only [head']
  induction' n with n
  · rw [h₁] at h₀
    cases h₀
    trivial
  · have H := Hconsistent (succ n)
    cases' h₂ : x (succ n) with _ i₂ f₂
    rw [h₀, h₂] at H
    apply n_ih (truncate ∘ f₀)
    rw [h₂]
    cases' H with _ _ _ _ _ _ hagree
    congr
    funext j
    dsimp only [comp_app]
    rw [truncate_eq_of_agree]
    apply hagree
#align pfunctor.approx.head_succ' Pfunctor.Approx.head_succ'

end Approx

open Approx

/-- Internal definition for `M`. It is needed to avoid name clashes
between `M.mk` and `M.cases_on` and the declarations generated for
the structure -/
structure MIntl where
  approx : ∀ n, CofixA F n
  consistent : AllAgree approx
#align pfunctor.M_intl Pfunctor.MIntl

/-- For polynomial functor `F`, `M F` is its final coalgebra -/
def M :=
  MIntl F
#align pfunctor.M Pfunctor.M

theorem M.default_consistent [Inhabited F.A] : ∀ n, Agree (default : CofixA F n) default
  | 0 => Agree.continue _ _
  | succ n => Agree.intro _ _ fun _ => M.default_consistent n
#align pfunctor.M.default_consistent Pfunctor.M.default_consistent

instance M.inhabited [Inhabited F.A] : Inhabited (M F) :=
  ⟨{  approx := default
      consistent := M.default_consistent _ }⟩
#align pfunctor.M.inhabited Pfunctor.M.inhabited

instance MIntl.inhabited [Inhabited F.A] : Inhabited (MIntl F) :=
  show Inhabited (M F) by infer_instance
#align pfunctor.M_intl.inhabited Pfunctor.MIntl.inhabited

namespace M

theorem ext' (x y : M F) (H : ∀ i : ℕ, x.approx i = y.approx i) : x = y :=
  by
  cases x
  cases y
  congr with n
  apply H
#align pfunctor.M.ext' Pfunctor.M.ext'

variable {X : Type _}

variable (f : X → F.Obj X)

variable {F}

/-- Corecursor for the M-type defined by `F`. -/
protected def corec (i : X) : M F where
  approx := sCorec f i
  consistent := P_corec _ _
#align pfunctor.M.corec Pfunctor.M.corec

variable {F}

/-- given a tree generated by `F`, `head` gives us the first piece of data
it contains -/
def head (x : M F) :=
  head' (x.1 1)
#align pfunctor.M.head Pfunctor.M.head

/-- return all the subtrees of the root of a tree `x : M F` -/
def children (x : M F) (i : F.B (head x)) : M F :=
  let H := fun n : ℕ => @head_succ' _ n 0 x.1 x.2
  { approx := fun n => children' (x.1 _) (cast (congr_arg _ <| by simp only [head, H] <;> rfl) i)
    consistent := by
      intro
      have P' := x.2 (succ n)
      apply agree_children _ _ _ P'
      trans i
      apply cast_hEq
      symm
      apply cast_hEq }
#align pfunctor.M.children Pfunctor.M.children

/-- select a subtree using a `i : F.Idx` or return an arbitrary tree if
`i` designates no subtree of `x` -/
def ichildren [Inhabited (M F)] [DecidableEq F.A] (i : F.IdxCat) (x : M F) : M F :=
  if H' : i.1 = head x then children x (cast (congr_arg _ <| by simp only [head, H'] <;> rfl) i.2)
  else default
#align pfunctor.M.ichildren Pfunctor.M.ichildren

theorem head_succ (n m : ℕ) (x : M F) : head' (x.approx (succ n)) = head' (x.approx (succ m)) :=
  head_succ' n m _ x.consistent
#align pfunctor.M.head_succ Pfunctor.M.head_succ

theorem head_eq_head' : ∀ (x : M F) (n : ℕ), head x = head' (x.approx <| n + 1)
  | ⟨x, h⟩, n => head_succ' _ _ _ h
#align pfunctor.M.head_eq_head' Pfunctor.M.head_eq_head'

theorem head'_eq_head : ∀ (x : M F) (n : ℕ), head' (x.approx <| n + 1) = head x
  | ⟨x, h⟩, n => head_succ' _ _ _ h
#align pfunctor.M.head'_eq_head Pfunctor.M.head'_eq_head

theorem truncate_approx (x : M F) (n : ℕ) : truncate (x.approx <| n + 1) = x.approx n :=
  truncate_eq_of_agree _ _ (x.consistent _)
#align pfunctor.M.truncate_approx Pfunctor.M.truncate_approx

/-- unfold an M-type -/
def dest : M F → F.Obj (M F)
  | x => ⟨head x, fun i => children x i⟩
#align pfunctor.M.dest Pfunctor.M.dest

namespace Approx

/-- generates the approximations needed for `M.mk` -/
protected def sMk (x : F.Obj <| M F) : ∀ n, CofixA F n
  | 0 => CofixA.continue
  | succ n => CofixA.intro x.1 fun i => (x.2 i).approx n
#align pfunctor.M.approx.s_mk Pfunctor.M.Approx.sMk

protected theorem P_mk (x : F.Obj <| M F) : AllAgree (Approx.sMk x)
  | 0 => by constructor
  | succ n => by
    constructor
    introv
    apply (x.2 i).consistent
#align pfunctor.M.approx.P_mk Pfunctor.M.Approx.P_mk

end Approx

/-- constructor for M-types -/
protected def mk (x : F.Obj <| M F) : M F
    where
  approx := Approx.sMk x
  consistent := Approx.P_mk x
#align pfunctor.M.mk Pfunctor.M.mk

/-- `agree' n` relates two trees of type `M F` that
are the same up to dept `n` -/
inductive Agree' : ℕ → M F → M F → Prop
  | trivial (x y : M F) : agree' 0 x y
  |
  step {n : ℕ} {a} (x y : F.B a → M F) {x' y'} :
    x' = M.mk ⟨a, x⟩ → y' = M.mk ⟨a, y⟩ → (∀ i, agree' n (x i) (y i)) → agree' (succ n) x' y'
#align pfunctor.M.agree' Pfunctor.M.Agree'

@[simp]
theorem dest_mk (x : F.Obj <| M F) : dest (M.mk x) = x :=
  by
  funext i
  dsimp only [M.mk, dest]
  cases' x with x ch; congr with i
  cases h : ch i
  simp only [children, M.approx.s_mk, children', cast_eq]
  dsimp only [M.approx.s_mk, children']
  congr ; rw [h]
#align pfunctor.M.dest_mk Pfunctor.M.dest_mk

@[simp]
theorem mk_dest (x : M F) : M.mk (dest x) = x :=
  by
  apply ext'
  intro n
  dsimp only [M.mk]
  induction' n with n
  · apply Subsingleton.elim
  dsimp only [approx.s_mk, dest, head]
  cases' h : x.approx (succ n) with _ hd ch
  have h' : hd = head' (x.approx 1) :=
    by
    rw [← head_succ' n, h, head']
    apply x.consistent
  revert ch
  rw [h']
  intros
  congr
  · ext a
    dsimp only [children]
    generalize hh : cast _ a = a''
    rw [cast_eq_iff_hEq] at hh
    revert a''
    rw [h]
    intros
    cases hh
    rfl
#align pfunctor.M.mk_dest Pfunctor.M.mk_dest

theorem mk_inj {x y : F.Obj <| M F} (h : M.mk x = M.mk y) : x = y := by rw [← dest_mk x, h, dest_mk]
#align pfunctor.M.mk_inj Pfunctor.M.mk_inj

/-- destructor for M-types -/
protected def cases {r : M F → Sort w} (f : ∀ x : F.Obj <| M F, r (M.mk x)) (x : M F) : r x :=
  suffices r (M.mk (dest x)) by
    haveI := Classical.propDecidable
    haveI := Inhabited.mk x
    rw [← mk_dest x]
    exact this
  f _
#align pfunctor.M.cases Pfunctor.M.cases

/-- destructor for M-types -/
protected def casesOn {r : M F → Sort w} (x : M F) (f : ∀ x : F.Obj <| M F, r (M.mk x)) : r x :=
  M.cases f x
#align pfunctor.M.cases_on Pfunctor.M.casesOn

/-- destructor for M-types, similar to `cases_on` but also
gives access directly to the root and subtrees on an M-type -/
protected def casesOn' {r : M F → Sort w} (x : M F) (f : ∀ a f, r (M.mk ⟨a, f⟩)) : r x :=
  M.casesOn x fun ⟨a, g⟩ => f a _
#align pfunctor.M.cases_on' Pfunctor.M.casesOn'

theorem approx_mk (a : F.A) (f : F.B a → M F) (i : ℕ) :
    (M.mk ⟨a, f⟩).approx (succ i) = CofixA.intro a fun j => (f j).approx i :=
  rfl
#align pfunctor.M.approx_mk Pfunctor.M.approx_mk

@[simp]
theorem agree'_refl {n : ℕ} (x : M F) : Agree' n x x :=
  by
  induction n generalizing x <;> induction x using Pfunctor.M.casesOn' <;> constructor <;> try rfl
  intros
  apply n_ih
#align pfunctor.M.agree'_refl Pfunctor.M.agree'_refl

theorem agree_iff_agree' {n : ℕ} (x y : M F) :
    Agree (x.approx n) (y.approx <| n + 1) ↔ Agree' n x y :=
  by
  constructor <;> intro h
  · induction n generalizing x y
    constructor
    · induction x using Pfunctor.M.casesOn'
      induction y using Pfunctor.M.casesOn'
      simp only [approx_mk] at h
      cases' h with _ _ _ _ _ _ hagree
      constructor <;> try rfl
      intro i
      apply n_ih
      apply hagree
  · induction n generalizing x y
    constructor
    · cases h
      induction x using Pfunctor.M.casesOn'
      induction y using Pfunctor.M.casesOn'
      simp only [approx_mk]
      have h_a_1 := mk_inj ‹M.mk ⟨x_a, x_f⟩ = M.mk ⟨h_a, h_x⟩›
      cases h_a_1
      replace h_a_2 := mk_inj ‹M.mk ⟨y_a, y_f⟩ = M.mk ⟨h_a, h_y⟩›
      cases h_a_2
      constructor
      intro i
      apply n_ih
      simp [*]
#align pfunctor.M.agree_iff_agree' Pfunctor.M.agree_iff_agree'

@[simp]
theorem cases_mk {r : M F → Sort _} (x : F.Obj <| M F) (f : ∀ x : F.Obj <| M F, r (M.mk x)) :
    Pfunctor.M.cases f (M.mk x) = f x :=
  by
  dsimp only [M.mk, Pfunctor.M.cases, dest, head, approx.s_mk, head']
  cases x; dsimp only [approx.s_mk]
  apply eq_of_hEq
  apply ndrec_hEq_of_hEq; congr with x
  dsimp only [children, approx.s_mk, children']
  cases h : x_snd x; dsimp only [head]
  congr with n; change (x_snd x).approx n = _; rw [h]
#align pfunctor.M.cases_mk Pfunctor.M.cases_mk

@[simp]
theorem casesOn_mk {r : M F → Sort _} (x : F.Obj <| M F) (f : ∀ x : F.Obj <| M F, r (M.mk x)) :
    Pfunctor.M.casesOn (M.mk x) f = f x :=
  cases_mk x f
#align pfunctor.M.cases_on_mk Pfunctor.M.casesOn_mk

@[simp]
theorem cases_on_mk' {r : M F → Sort _} {a} (x : F.B a → M F)
    (f : ∀ (a) (f : F.B a → M F), r (M.mk ⟨a, f⟩)) : Pfunctor.M.casesOn' (M.mk ⟨a, x⟩) f = f a x :=
  cases_mk ⟨_, x⟩ _
#align pfunctor.M.cases_on_mk' Pfunctor.M.cases_on_mk'

/-- `is_path p x` tells us if `p` is a valid path through `x` -/
inductive IsPath : Path F → M F → Prop
  | nil (x : M F) : is_path [] x
  |
  cons (xs : Path F) {a} (x : M F) (f : F.B a → M F) (i : F.B a) :
    x = M.mk ⟨a, f⟩ → is_path xs (f i) → is_path (⟨a, i⟩ :: xs) x
#align pfunctor.M.is_path Pfunctor.M.IsPath

theorem isPath_cons {xs : Path F} {a a'} {f : F.B a → M F} {i : F.B a'} :
    IsPath (⟨a', i⟩ :: xs) (M.mk ⟨a, f⟩) → a = a' :=
  by
  generalize h : M.mk ⟨a, f⟩ = x
  rintro (_ | ⟨_, _, _, _, rfl, _⟩)
  cases mk_inj h
  rfl
#align pfunctor.M.is_path_cons Pfunctor.M.isPath_cons

theorem isPath_cons' {xs : Path F} {a} {f : F.B a → M F} {i : F.B a} :
    IsPath (⟨a, i⟩ :: xs) (M.mk ⟨a, f⟩) → IsPath xs (f i) :=
  by
  generalize h : M.mk ⟨a, f⟩ = x
  rintro (_ | ⟨_, _, _, _, rfl, hp⟩)
  cases mk_inj h
  exact hp
#align pfunctor.M.is_path_cons' Pfunctor.M.isPath_cons'

/-- follow a path through a value of `M F` and return the subtree
found at the end of the path if it is a valid path for that value and
return a default tree -/
def isubtree [DecidableEq F.A] [Inhabited (M F)] : Path F → M F → M F
  | [], x => x
  | ⟨a, i⟩ :: ps, x =>
    Pfunctor.M.casesOn' x fun a' f =>
      (if h : a = a' then isubtree ps (f <| cast (by rw [h]) i) else default :
        (fun x => M F) (M.mk ⟨a', f⟩))
#align pfunctor.M.isubtree Pfunctor.M.isubtree

/-- similar to `isubtree` but returns the data at the end of the path instead
of the whole subtree -/
def iselect [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) : M F → F.A := fun x : M F =>
  head <| isubtree ps x
#align pfunctor.M.iselect Pfunctor.M.iselect

theorem iselect_eq_default [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) (x : M F)
    (h : ¬IsPath ps x) : iselect ps x = head default :=
  by
  induction ps generalizing x
  · exfalso
    apply h
    constructor
  · cases' ps_hd with a i
    induction x using Pfunctor.M.casesOn'
    simp only [iselect, isubtree] at ps_ih⊢
    by_cases h'' : a = x_a
    subst x_a
    · simp only [dif_pos, eq_self_iff_true, cases_on_mk']
      rw [ps_ih]
      intro h'
      apply h
      constructor <;> try rfl
      apply h'
    · simp [*]
#align pfunctor.M.iselect_eq_default Pfunctor.M.iselect_eq_default

@[simp]
theorem head_mk (x : F.Obj (M F)) : head (M.mk x) = x.1 :=
  Eq.symm <|
    calc
      x.1 = (dest (M.mk x)).1 := by rw [dest_mk]
      _ = head (M.mk x) := by rfl
      
#align pfunctor.M.head_mk Pfunctor.M.head_mk

theorem children_mk {a} (x : F.B a → M F) (i : F.B (head (M.mk ⟨a, x⟩))) :
    children (M.mk ⟨a, x⟩) i = x (cast (by rw [head_mk]) i) := by apply ext' <;> intro n <;> rfl
#align pfunctor.M.children_mk Pfunctor.M.children_mk

@[simp]
theorem ichildren_mk [DecidableEq F.A] [Inhabited (M F)] (x : F.Obj (M F)) (i : F.IdxCat) :
    ichildren i (M.mk x) = x.iget i :=
  by
  dsimp only [ichildren, Pfunctor.Obj.iget]
  congr with h
  apply ext'
  dsimp only [children', M.mk, approx.s_mk]
  intros
  rfl
#align pfunctor.M.ichildren_mk Pfunctor.M.ichildren_mk

@[simp]
theorem isubtree_cons [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) {a} (f : F.B a → M F)
    {i : F.B a} : isubtree (⟨_, i⟩ :: ps) (M.mk ⟨a, f⟩) = isubtree ps (f i) := by
  simp only [isubtree, ichildren_mk, Pfunctor.Obj.iget, dif_pos, isubtree, M.cases_on_mk'] <;> rfl
#align pfunctor.M.isubtree_cons Pfunctor.M.isubtree_cons

@[simp]
theorem iselect_nil [DecidableEq F.A] [Inhabited (M F)] {a} (f : F.B a → M F) :
    iselect nil (M.mk ⟨a, f⟩) = a := by rfl
#align pfunctor.M.iselect_nil Pfunctor.M.iselect_nil

@[simp]
theorem iselect_cons [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) {a} (f : F.B a → M F) {i} :
    iselect (⟨a, i⟩ :: ps) (M.mk ⟨a, f⟩) = iselect ps (f i) := by simp only [iselect, isubtree_cons]
#align pfunctor.M.iselect_cons Pfunctor.M.iselect_cons

theorem corec_def {X} (f : X → F.Obj X) (x₀ : X) : M.corec f x₀ = M.mk (M.corec f <$> f x₀) :=
  by
  dsimp only [M.corec, M.mk]
  congr with n
  cases' n with n
  · dsimp only [s_corec, approx.s_mk]
    rfl
  · dsimp only [s_corec, approx.s_mk]
    cases h : f x₀
    dsimp only [(· <$> ·), Pfunctor.map]
    congr
#align pfunctor.M.corec_def Pfunctor.M.corec_def

theorem ext_aux [Inhabited (M F)] [DecidableEq F.A] {n : ℕ} (x y z : M F) (hx : Agree' n z x)
    (hy : Agree' n z y) (hrec : ∀ ps : Path F, n = ps.length → iselect ps x = iselect ps y) :
    x.approx (n + 1) = y.approx (n + 1) :=
  by
  induction' n with n generalizing x y z
  · specialize hrec [] rfl
    induction x using Pfunctor.M.casesOn'
    induction y using Pfunctor.M.casesOn'
    simp only [iselect_nil] at hrec
    subst hrec
    simp only [approx_mk, true_and_iff, eq_self_iff_true, hEq_iff_eq]
    apply Subsingleton.elim
  · cases hx
    cases hy
    induction x using Pfunctor.M.casesOn'
    induction y using Pfunctor.M.casesOn'
    subst z
    iterate 3 have := mk_inj ‹_›; repeat' cases this
    simp only [approx_mk, true_and_iff, eq_self_iff_true, hEq_iff_eq]
    ext i
    apply n_ih
    · solve_by_elim
    · solve_by_elim
    introv h
    specialize hrec (⟨_, i⟩ :: ps) (congr_arg _ h)
    simp only [iselect_cons] at hrec
    exact hrec
#align pfunctor.M.ext_aux Pfunctor.M.ext_aux

open Pfunctor.Approx

variable {F}

attribute [local instance] Classical.propDecidable

theorem ext [Inhabited (M F)] (x y : M F) (H : ∀ ps : Path F, iselect ps x = iselect ps y) :
    x = y := by
  apply ext'; intro i
  induction' i with i
  · cases x.approx 0
    cases y.approx 0
    constructor
  · apply ext_aux x y x
    · rw [← agree_iff_agree']
      apply x.consistent
    · rw [← agree_iff_agree', i_ih]
      apply y.consistent
    introv H'
    dsimp only [iselect] at H
    cases H'
    apply H ps
#align pfunctor.M.ext Pfunctor.M.ext

section Bisim

variable (R : M F → M F → Prop)

-- mathport name: «expr ~ »
local infixl:50 " ~ " => R

/-- Bisimulation is the standard proof technique for equality between
infinite tree-like structures -/
structure IsBisimulation : Prop where
  head : ∀ {a a'} {f f'}, M.mk ⟨a, f⟩ ~ M.mk ⟨a', f'⟩ → a = a'
  tail : ∀ {a} {f f' : F.B a → M F}, M.mk ⟨a, f⟩ ~ M.mk ⟨a, f'⟩ → ∀ i : F.B a, f i ~ f' i
#align pfunctor.M.is_bisimulation Pfunctor.M.IsBisimulation

theorem nth_of_bisim [Inhabited (M F)] (bisim : IsBisimulation R) (s₁ s₂) (ps : Path F) :
    s₁ ~ s₂ →
      IsPath ps s₁ ∨ IsPath ps s₂ →
        iselect ps s₁ = iselect ps s₂ ∧
          ∃ (a : _)(f f' : F.B a → M F),
            isubtree ps s₁ = M.mk ⟨a, f⟩ ∧
              isubtree ps s₂ = M.mk ⟨a, f'⟩ ∧ ∀ i : F.B a, f i ~ f' i :=
  by
  intro h₀ hh
  induction' s₁ using Pfunctor.M.casesOn' with a f
  induction' s₂ using Pfunctor.M.casesOn' with a' f'
  obtain rfl : a = a' := bisim.head h₀
  induction' ps with i ps generalizing a f f'
  · exists rfl, a, f, f', rfl, rfl
    apply bisim.tail h₀
  cases' i with a' i
  obtain rfl : a = a' := by cases hh <;> cases is_path_cons hh <;> rfl
  dsimp only [iselect] at ps_ih⊢
  have h₁ := bisim.tail h₀ i
  induction' h : f i using Pfunctor.M.casesOn' with a₀ f₀
  induction' h' : f' i using Pfunctor.M.casesOn' with a₁ f₁
  simp only [h, h', isubtree_cons] at ps_ih⊢
  rw [h, h'] at h₁
  obtain rfl : a₀ = a₁ := bisim.head h₁
  apply ps_ih _ _ _ h₁
  rw [← h, ← h']
  apply or_of_or_of_imp_of_imp hh is_path_cons' is_path_cons'
#align pfunctor.M.nth_of_bisim Pfunctor.M.nth_of_bisim

theorem eq_of_bisim [Nonempty (M F)] (bisim : IsBisimulation R) : ∀ s₁ s₂, s₁ ~ s₂ → s₁ = s₂ :=
  by
  inhabit M F
  introv Hr; apply ext
  introv
  by_cases h : is_path ps s₁ ∨ is_path ps s₂
  · have H := nth_of_bisim R bisim _ _ ps Hr h
    exact H.left
  · rw [not_or] at h
    cases' h with h₀ h₁
    simp only [iselect_eq_default, *, not_false_iff]
#align pfunctor.M.eq_of_bisim Pfunctor.M.eq_of_bisim

end Bisim

universe u' v'

/-- corecursor for `M F` with swapped arguments -/
def corecOn {X : Type _} (x₀ : X) (f : X → F.Obj X) : M F :=
  M.corec f x₀
#align pfunctor.M.corec_on Pfunctor.M.corecOn

variable {P : Pfunctor.{u}} {α : Type u}

theorem dest_corec (g : α → P.Obj α) (x : α) : M.dest (M.corec g x) = M.corec g <$> g x := by
  rw [corec_def, dest_mk]
#align pfunctor.M.dest_corec Pfunctor.M.dest_corec

theorem bisim (R : M P → M P → Prop)
    (h : ∀ x y, R x y → ∃ a f f', M.dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ ∀ i, R (f i) (f' i)) :
    ∀ x y, R x y → x = y := by
  introv h'
  haveI := Inhabited.mk x.head
  apply eq_of_bisim R _ _ _ h'; clear h' x y
  constructor <;> introv ih <;> rcases h _ _ ih with ⟨a'', g, g', h₀, h₁, h₂⟩ <;> clear h
  · replace h₀ := congr_arg Sigma.fst h₀
    replace h₁ := congr_arg Sigma.fst h₁
    simp only [dest_mk] at h₀ h₁
    rw [h₀, h₁]
  · simp only [dest_mk] at h₀ h₁
    cases h₀
    cases h₁
    apply h₂
#align pfunctor.M.bisim Pfunctor.M.bisim

theorem bisim' {α : Type _} (Q : α → Prop) (u v : α → M P)
    (h :
      ∀ x,
        Q x →
          ∃ a f f',
            M.dest (u x) = ⟨a, f⟩ ∧
              M.dest (v x) = ⟨a, f'⟩ ∧ ∀ i, ∃ x', Q x' ∧ f i = u x' ∧ f' i = v x') :
    ∀ x, Q x → u x = v x := fun x Qx =>
  let R := fun w z : M P => ∃ x', Q x' ∧ w = u x' ∧ z = v x'
  @M.bisim P R
    (fun x y ⟨x', Qx', xeq, yeq⟩ =>
      let ⟨a, f, f', ux'eq, vx'eq, h'⟩ := h x' Qx'
      ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
    _ _ ⟨x, Qx, rfl, rfl⟩
#align pfunctor.M.bisim' Pfunctor.M.bisim'

-- for the record, show M_bisim follows from _bisim'
theorem bisim_equiv (R : M P → M P → Prop)
    (h : ∀ x y, R x y → ∃ a f f', M.dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ ∀ i, R (f i) (f' i)) :
    ∀ x y, R x y → x = y := fun x y Rxy =>
  let Q : M P × M P → Prop := fun p => R p.fst p.snd
  bisim' Q Prod.fst Prod.snd
    (fun p Qp =>
      let ⟨a, f, f', hx, hy, h'⟩ := h p.fst p.snd Qp
      ⟨a, f, f', hx, hy, fun i => ⟨⟨f i, f' i⟩, h' i, rfl, rfl⟩⟩)
    ⟨x, y⟩ Rxy
#align pfunctor.M.bisim_equiv Pfunctor.M.bisim_equiv

theorem corec_unique (g : α → P.Obj α) (f : α → M P) (hyp : ∀ x, M.dest (f x) = f <$> g x) :
    f = M.corec g := by
  ext x
  apply bisim' (fun x => True) _ _ _ _ trivial
  clear x
  intro x _
  cases' gxeq : g x with a f'
  have h₀ : M.dest (f x) = ⟨a, f ∘ f'⟩ := by rw [hyp, gxeq, Pfunctor.map_eq]
  have h₁ : M.dest (M.corec g x) = ⟨a, M.corec g ∘ f'⟩ := by rw [dest_corec, gxeq, Pfunctor.map_eq]
  refine' ⟨_, _, _, h₀, h₁, _⟩
  intro i
  exact ⟨f' i, trivial, rfl, rfl⟩
#align pfunctor.M.corec_unique Pfunctor.M.corec_unique

/-- corecursor where the state of the computation can be sent downstream
in the form of a recursive call -/
def corec₁ {α : Type u} (F : ∀ X, (α → X) → α → P.Obj X) : α → M P :=
  M.corec (F _ id)
#align pfunctor.M.corec₁ Pfunctor.M.corec₁

/-- corecursor where it is possible to return a fully formed value at any point
of the computation -/
def corec' {α : Type u} (F : ∀ {X : Type u}, (α → X) → α → Sum (M P) (P.Obj X)) (x : α) : M P :=
  corec₁
    (fun X rec (a : Sum (M P) α) =>
      let y := a >>= F (rec ∘ Sum.inr)
      match y with
      | Sum.inr y => y
      | Sum.inl y => (rec ∘ Sum.inl) <$> M.dest y)
    (@Sum.inr (M P) _ x)
#align pfunctor.M.corec' Pfunctor.M.corec'

end M

end Pfunctor

