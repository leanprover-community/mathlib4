/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Data.PFunctor.Univariate.Basic

#align_import data.pfunctor.univariate.M from "leanprover-community/mathlib"@"8631e2d5ea77f6c13054d9151d82b83069680cb1"

/-!
# M-types

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.

Unfortunately, the data structure of the model of M types is inefficient, so we override the data
structure of M types.
-/


universe u v w

open Nat Function

open List

variable (F : PFunctor.{u})

-- porting note: the ♯ tactic is never used
-- local prefix:0 "♯" => cast (by first |simp [*]|cc|solve_by_elim)

namespace PFunctor

namespace Approx

/-- `CofixA F n` is an `n` level approximation of an M-type -/
inductive CofixA : ℕ → Type u
  | continue : CofixA 0
  | intro {n} : ∀ a, (F.B a → CofixA n) → CofixA (succ n)
#align pfunctor.approx.cofix_a PFunctor.Approx.CofixA

/-- default inhabitant of `CofixA` -/
protected def CofixA.default [Inhabited F.A] : ∀ n, CofixA F n
  | 0 => CofixA.continue
  | succ n => CofixA.intro default fun _ => CofixA.default n
#align pfunctor.approx.cofix_a.default PFunctor.Approx.CofixA.default

instance [Inhabited F.A] {n} : Inhabited (CofixA F n) :=
  ⟨CofixA.default F n⟩

theorem cofixA_eq_zero : ∀ x y : CofixA F 0, x = y
  | CofixA.continue, CofixA.continue => rfl
#align pfunctor.approx.cofix_a_eq_zero PFunctor.Approx.cofixA_eq_zero

variable {F}

/-- The label of the root of the tree for a non-trivial
approximation of the cofix of a pfunctor.
-/
def head' : ∀ {n}, CofixA F (succ n) → F.A
  | _, CofixA.intro i _ => i
#align pfunctor.approx.head' PFunctor.Approx.head'

/-- for a non-trivial approximation, return all the subtrees of the root -/
def children' : ∀ {n} (x : CofixA F (succ n)), F.B (head' x) → CofixA F n
  | _, CofixA.intro _ f => f
#align pfunctor.approx.children' PFunctor.Approx.children'

theorem approx_eta {n : ℕ} (x : CofixA F (n + 1)) : x = CofixA.intro (head' x) (children' x) := by
  cases x; rfl
#align pfunctor.approx.approx_eta PFunctor.Approx.approx_eta

/-- Relation between two approximations of the cofix of a pfunctor
that state they both contain the same data until one of them is truncated -/
inductive Agree : ∀ {n : ℕ}, CofixA F n → CofixA F (n + 1) → Prop
  | continu (x : CofixA F 0) (y : CofixA F 1) : Agree x y
  | intro {n} {a} (x : F.B a → CofixA F n) (x' : F.B a → CofixA F (n + 1)) :
    (∀ i : F.B a, Agree (x i) (x' i)) → Agree (CofixA.intro a x) (CofixA.intro a x')
#align pfunctor.approx.agree PFunctor.Approx.Agree

/-- Given an infinite series of approximations `approx`,
`AllAgree approx` states that they are all consistent with each other.
-/
def AllAgree (x : ∀ n, CofixA F n) :=
  ∀ n, Agree (x n) (x (succ n))
#align pfunctor.approx.all_agree PFunctor.Approx.AllAgree

@[simp]
theorem agree_trival {x : CofixA F 0} {y : CofixA F 1} : Agree x y := by constructor
#align pfunctor.approx.agree_trival PFunctor.Approx.agree_trival

theorem agree_children {n : ℕ} (x : CofixA F (succ n)) (y : CofixA F (succ n + 1)) {i j}
    (h₀ : HEq i j) (h₁ : Agree x y) : Agree (children' x i) (children' y j) := by
  cases' h₁ with _ _ _ _ _ _ hagree; cases h₀
  apply hagree
#align pfunctor.approx.agree_children PFunctor.Approx.agree_children

/-- `truncate a` turns `a` into a more limited approximation -/
def truncate : ∀ {n : ℕ}, CofixA F (n + 1) → CofixA F n
  | 0, CofixA.intro _ _ => CofixA.continue
  | succ _, CofixA.intro i f => CofixA.intro i <| truncate ∘ f
#align pfunctor.approx.truncate PFunctor.Approx.truncate

theorem truncate_eq_of_agree {n : ℕ} (x : CofixA F n) (y : CofixA F (succ n)) (h : Agree x y) :
    truncate y = x := by
  induction n <;> cases x <;> cases y
  · rfl
  · -- cases' h with _ _ _ _ _ h₀ h₁
    cases h
    simp only [truncate, Function.comp, true_and_iff, eq_self_iff_true, heq_iff_eq]
    -- porting note: used to be `ext y`
    rename_i n_ih a f y h₁
    suffices (fun x => truncate (y x)) = f
      by simp [this]; try (exact HEq.rfl;)
    funext y

    apply n_ih
    apply h₁
#align pfunctor.approx.truncate_eq_of_agree PFunctor.Approx.truncate_eq_of_agree

variable {X : Type w}

variable (f : X → F X)

/-- `sCorec f i n` creates an approximation of height `n`
of the final coalgebra of `f` -/
def sCorec : X → ∀ n, CofixA F n
  | _, 0 => CofixA.continue
  | j, succ _ => CofixA.intro (f j).1 fun i => sCorec ((f j).2 i) _
#align pfunctor.approx.s_corec PFunctor.Approx.sCorec

theorem P_corec (i : X) (n : ℕ) : Agree (sCorec f i n) (sCorec f i (succ n)) := by
  induction' n with n n_ih generalizing i
  constructor
  cases' h : f i with y g
  constructor
  introv
  apply n_ih
set_option linter.uppercaseLean3 false in
#align pfunctor.approx.P_corec PFunctor.Approx.P_corec

/-- `Path F` provides indices to access internal nodes in `Corec F` -/
def Path (F : PFunctor.{u}) :=
  List F.Idx
#align pfunctor.approx.path PFunctor.Approx.Path

instance Path.inhabited : Inhabited (Path F) :=
  ⟨[]⟩
#align pfunctor.approx.path.inhabited PFunctor.Approx.Path.inhabited

open List Nat

instance CofixA.instSubsingleton : Subsingleton (CofixA F 0) :=
  ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩

theorem head_succ' (n m : ℕ) (x : ∀ n, CofixA F n) (Hconsistent : AllAgree x) :
    head' (x (succ n)) = head' (x (succ m)) := by
  suffices ∀ n, head' (x (succ n)) = head' (x 1) by simp [this]
  clear m n
  intro n
  cases' h₀ : x (succ n) with _ i₀ f₀
  cases' h₁ : x 1 with _ i₁ f₁
  dsimp only [head']
  induction' n with n n_ih
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
    dsimp only [comp_apply]
    rw [truncate_eq_of_agree]
    apply hagree
#align pfunctor.approx.head_succ' PFunctor.Approx.head_succ'

end Approx

open Approx

/-- Internal definition for `M`. This data structure is inefficient so we override the data
structure. -/
structure MIntl where
  /-- constructor for `MIntl` as a structure of the internal definition. -/
  mk' ::
  /-- An `n`-th level approximation, for each depth `n` -/
  approx : ∀ n, CofixA F n
  /-- Each approximation agrees with the next -/
  consistent : AllAgree approx
set_option linter.uppercaseLean3 false in
#align pfunctor.M_intl PFunctor.MIntl

namespace MIntl

variable {F}

theorem default_consistent [Inhabited F.A] : ∀ n, Agree (default : CofixA F n) default
  | 0 => Agree.continu _ _
  | succ n => Agree.intro _ _ fun _ => default_consistent n
set_option linter.uppercaseLean3 false in
#align pfunctor.M.default_consistent PFunctor.MIntl.default_consistent

instance inhabited [Inhabited F.A] : Inhabited (MIntl F) :=
  ⟨{  approx := default
      consistent := default_consistent }⟩
set_option linter.uppercaseLean3 false in
#align pfunctor.M_intl.inhabited PFunctor.MIntl.inhabited

theorem ext' (x y : MIntl F) (H : ∀ i : ℕ, x.approx i = y.approx i) : x = y := by
  cases x
  cases y
  congr with n
  apply H
set_option linter.uppercaseLean3 false in
#align pfunctor.M.ext' PFunctor.MIntl.ext'

variable {X : Type*}

variable (f : X → F X)

/-- Corecursor for the M-type defined by `F`. -/
protected def corec (i : X) : MIntl F where
  approx := sCorec f i
  consistent := P_corec _ _

/-- given a tree generated by `F`, `head` gives us the first piece of data
it contains -/
def head (x : MIntl F) :=
  head' (x.1 1)
set_option linter.uppercaseLean3 false in
#align pfunctor.M.head PFunctor.MIntl.head

/-- return all the subtrees of the root of a tree `x : MIntl F` -/
def children (x : MIntl F) (i : F.B (head x)) : MIntl F :=
  let H := fun n : ℕ => @head_succ' _ n 0 x.1 x.2
  { approx := fun n => children' (x.1 _) (cast (congr_arg _ <| by simp only [head, H]) i)
    consistent := by
      intro n
      have P' := x.2 (succ n)
      apply agree_children _ _ _ P'
      trans i
      apply cast_heq
      symm
      apply cast_heq }
set_option linter.uppercaseLean3 false in
#align pfunctor.M.children PFunctor.MIntl.children

theorem head_succ (n m : ℕ) (x : MIntl F) : head' (x.approx (succ n)) = head' (x.approx (succ m)) :=
  head_succ' n m _ x.consistent
set_option linter.uppercaseLean3 false in
#align pfunctor.M.head_succ PFunctor.MIntl.head_succ

theorem head_eq_head' (x : MIntl F) (n : ℕ) : head x = head' (x.approx <| n + 1) :=
  head_succ' _ _ _ x.consistent
set_option linter.uppercaseLean3 false in
#align pfunctor.M.head_eq_head' PFunctor.MIntl.head_eq_head'

theorem head'_eq_head (x : MIntl F) (n : ℕ) : head' (x.approx <| n + 1) = head x :=
  head_succ' _ _ _ x.consistent
set_option linter.uppercaseLean3 false in
#align pfunctor.M.head'_eq_head PFunctor.MIntl.head'_eq_head

theorem truncate_approx (x : MIntl F) (n : ℕ) : truncate (x.approx <| n + 1) = x.approx n :=
  truncate_eq_of_agree _ _ (x.consistent _)
set_option linter.uppercaseLean3 false in
#align pfunctor.M.truncate_approx PFunctor.MIntl.truncate_approx

/-- This unfolds an M-type. -/
def dest (x : MIntl F) : F (MIntl F) :=
  ⟨head x, fun i => children x i⟩

/-- select a subtree using an `i : F.Idx` or return an arbitrary tree if
`i` designates no subtree of `x` -/
def ichildren [Inhabited (MIntl F)] [DecidableEq F.A] (i : F.Idx) (x : MIntl F) : MIntl F :=
  if H' : i.1 = head x then children x (cast (congr_arg _ <| by simp only [head, H']) i.2)
  else default
set_option linter.uppercaseLean3 false in
#align pfunctor.M.ichildren PFunctor.MIntl.ichildren

namespace Approx

/-- generates the approximations needed for `MIntl.mk` -/
protected def sMk (x : F (MIntl F)) : ∀ n, CofixA F n
  | 0 => CofixA.continue
  | succ n => CofixA.intro x.1 fun i => (x.2 i).approx n
set_option linter.uppercaseLean3 false in
#align pfunctor.M.approx.s_mk PFunctor.MIntl.Approx.sMk

protected theorem P_mk (x : F (MIntl F)) : AllAgree (Approx.sMk x)
  | 0 => by constructor
  | succ n => by
    constructor
    introv
    apply (x.2 i).consistent
set_option linter.uppercaseLean3 false in
#align pfunctor.M.approx.P_mk PFunctor.MIntl.Approx.P_mk

end Approx

/-- constructor for M-types -/
protected def mk (x : F (MIntl F)) : MIntl F where
  approx := Approx.sMk x
  consistent := Approx.P_mk x

/-- `Agree' n` relates two trees of type `MIntl F` that
are the same up to depth `n` -/
inductive Agree' : ℕ → MIntl F → MIntl F → Prop
  | trivial (x y : MIntl F) : Agree' 0 x y
  | step {n : ℕ} {a} (x y : F.B a → MIntl F) {x' y'} :
    x' = MIntl.mk ⟨a, x⟩ → y' = MIntl.mk ⟨a, y⟩ →
      (∀ i, Agree' n (x i) (y i)) → Agree' (succ n) x' y'
set_option linter.uppercaseLean3 false in
#align pfunctor.M.agree' PFunctor.MIntl.Agree'

@[simp]
theorem dest_mk (x : F (MIntl F)) : dest (MIntl.mk x) = x :=
  rfl

@[simp]
theorem mk_dest (x : MIntl F) : MIntl.mk (dest x) = x := by
  apply ext'
  intro n
  dsimp only [MIntl.mk]
  induction' n with n
  · apply @Subsingleton.elim _ CofixA.instSubsingleton
  dsimp only [Approx.sMk, dest, head]
  cases' h : x.approx (succ n) with _ hd ch
  have h' : hd = head' (x.approx 1) := by
    rw [← head_succ' n, h, head']
    apply x.consistent
  revert ch
  rw [h']
  intros ch h
  congr
  · ext a
    dsimp only [children]
    generalize hh : cast _ a = a''
    rw [cast_eq_iff_heq] at hh
    revert a''
    rw [h]
    intros _ hh
    cases hh
    rfl

theorem mk_inj {x y : F (MIntl F)} (h : MIntl.mk x = MIntl.mk y) : x = y := by
  rw [← dest_mk x, h, dest_mk]

/-- destructor for M-types -/
protected def cCases {r : MIntl F → Sort w} (f : ∀ x : F (MIntl F), r (MIntl.mk x))
    (x : MIntl F) : r x :=
  suffices r (MIntl.mk (dest x)) by
    rw [← mk_dest x]
    exact this
  f _

/-- destructor for M-types -/
protected def cCasesOn {r : MIntl F → Sort w} (x : MIntl F)
    (f : ∀ x : F (MIntl F), r (MIntl.mk x)) : r x :=
  MIntl.cCases f x

/-- destructor for M-types, similar to `cCasesOn` but also
gives access directly to the root and subtrees on an M-type -/
protected def cCasesOn' {r : MIntl F → Sort w} (x : MIntl F) (f : ∀ a f, r (MIntl.mk ⟨a, f⟩)) :
    r x :=
  MIntl.cCasesOn x (fun ⟨a, g⟩ => f a g)

theorem approx_mk (a : F.A) (f : F.B a → MIntl F) (i : ℕ) :
    (MIntl.mk ⟨a, f⟩).approx (succ i) = CofixA.intro a fun j => (f j).approx i :=
  rfl
set_option linter.uppercaseLean3 false in
#align pfunctor.M.approx_mk PFunctor.MIntl.approx_mk

@[simp]
theorem agree'_refl {n : ℕ} (x : MIntl F) : Agree' n x x := by
  induction' n with _ n_ih generalizing x <;>
  induction x using PFunctor.MIntl.cCasesOn' <;> constructor <;> try rfl
  intros
  apply n_ih
set_option linter.uppercaseLean3 false in
#align pfunctor.M.agree'_refl PFunctor.MIntl.agree'_refl

theorem agree_iff_agree' {n : ℕ} (x y : MIntl F) :
    Agree (x.approx n) (y.approx <| n + 1) ↔ Agree' n x y := by
  constructor <;> intro h
  · induction' n with _ n_ih generalizing x y
    constructor
    · induction x using PFunctor.MIntl.cCasesOn'
      induction y using PFunctor.MIntl.cCasesOn'
      simp only [approx_mk] at h
      cases' h with _ _ _ _ _ _ hagree
      constructor <;> try rfl
      intro i
      apply n_ih
      apply hagree
  · induction' n with _ n_ih generalizing x y
    constructor
    · cases' h with _ _ _ a x' y'
      induction' x using PFunctor.MIntl.cCasesOn' with x_a x_f
      induction' y using PFunctor.MIntl.cCasesOn' with y_a y_f
      simp only [approx_mk]
      have h_a_1 := mk_inj ‹MIntl.mk ⟨x_a, x_f⟩ = MIntl.mk ⟨a, x'⟩›
      cases h_a_1
      replace h_a_2 := mk_inj ‹MIntl.mk ⟨y_a, y_f⟩ = MIntl.mk ⟨a, y'⟩›
      cases h_a_2
      constructor
      intro i
      apply n_ih
      simp [*]
set_option linter.uppercaseLean3 false in
#align pfunctor.M.agree_iff_agree' PFunctor.MIntl.agree_iff_agree'

@[simp]
theorem cCases_mk {r : MIntl F → Sort*} (x : F (MIntl F)) (f : ∀ x : F (MIntl F), r (MIntl.mk x)) :
    PFunctor.MIntl.cCases f (MIntl.mk x) = f x := by
  dsimp only [MIntl.mk, PFunctor.MIntl.cCases, dest, head, Approx.sMk, head']
  cases x; dsimp only [Approx.sMk]
  simp only [Eq.mpr]
  apply congrFun
  rfl

@[simp]
theorem cCasesOn_mk {r : MIntl F → Sort*} (x : F (MIntl F))
    (f : ∀ x : F (MIntl F), r (MIntl.mk x)) :
    PFunctor.MIntl.cCasesOn (MIntl.mk x) f = f x :=
  cCases_mk x f

@[simp]
theorem cCasesOn_mk' {r : MIntl F → Sort*} {a} (x : F.B a → MIntl F)
    (f : ∀ (a) (f : F.B a → MIntl F), r (MIntl.mk ⟨a, f⟩)) :
    PFunctor.MIntl.cCasesOn' (MIntl.mk ⟨a, x⟩) f = f a x :=
  @cCases_mk F r ⟨a, x⟩ (fun ⟨a, g⟩ => f a g)

/-- `IsPath p x` tells us if `p` is a valid path through `x` -/
inductive IsPath : Path F → MIntl F → Prop
  | nil (x : MIntl F) : IsPath [] x
  | cons (xs : Path F) {a} (x : MIntl F) (f : F.B a → MIntl F) (i : F.B a) :
    x = MIntl.mk ⟨a, f⟩ → IsPath xs (f i) → IsPath (⟨a, i⟩ :: xs) x
set_option linter.uppercaseLean3 false in
#align pfunctor.M.is_path PFunctor.MIntl.IsPath

theorem isPath_cons {xs : Path F} {a a'} {f : F.B a → MIntl F} {i : F.B a'} :
    IsPath (⟨a', i⟩ :: xs) (MIntl.mk ⟨a, f⟩) → a = a' := by
  generalize h : MIntl.mk ⟨a, f⟩ = x
  rintro (_ | ⟨_, _, _, _, rfl, _⟩)
  cases mk_inj h
  rfl
set_option linter.uppercaseLean3 false in
#align pfunctor.M.is_path_cons PFunctor.MIntl.isPath_cons

theorem isPath_cons' {xs : Path F} {a} {f : F.B a → MIntl F} {i : F.B a} :
    IsPath (⟨a, i⟩ :: xs) (MIntl.mk ⟨a, f⟩) → IsPath xs (f i) := by
  generalize h : MIntl.mk ⟨a, f⟩ = x
  rintro (_ | ⟨_, _, _, _, rfl, hp⟩)
  cases mk_inj h
  exact hp
set_option linter.uppercaseLean3 false in
#align pfunctor.M.is_path_cons' PFunctor.MIntl.isPath_cons'

/-- follow a path through a value of `MIntl F` and return the subtree
found at the end of the path if it is a valid path for that value and
return a default tree -/
def isubtree [DecidableEq F.A] [Inhabited (MIntl F)] : Path F → MIntl F → MIntl F
  | [], x => x
  | ⟨a, i⟩ :: ps, x =>
    PFunctor.MIntl.cCasesOn' (r := fun _ => MIntl F) x (fun a' f =>
      if h : a = a' then
        isubtree ps (f <| cast (by rw [h]) i)
      else
        default (α := MIntl F)
    )

set_option linter.uppercaseLean3 false in
#align pfunctor.M.isubtree PFunctor.MIntl.isubtree

/-- similar to `isubtree` but returns the data at the end of the path instead
of the whole subtree -/
def iselect [DecidableEq F.A] [Inhabited (MIntl F)] (ps : Path F) : MIntl F → F.A :=
  fun x : MIntl F => head <| isubtree ps x
set_option linter.uppercaseLean3 false in
#align pfunctor.M.iselect PFunctor.MIntl.iselect

theorem iselect_eq_default [DecidableEq F.A] [Inhabited (MIntl F)] (ps : Path F) (x : MIntl F)
    (h : ¬IsPath ps x) : iselect ps x = head default := by
  induction' ps with ps_hd ps_tail ps_ih generalizing x
  · exfalso
    apply h
    constructor
  · cases' ps_hd with a i
    induction' x using PFunctor.MIntl.cCasesOn' with x_a x_f
    simp only [iselect, isubtree] at ps_ih ⊢
    by_cases h'' : a = x_a
    subst x_a
    · simp only [dif_pos, eq_self_iff_true, cCasesOn_mk']
      rw [ps_ih]
      intro h'
      apply h
      constructor <;> try rfl
      apply h'
    · simp [*]
set_option linter.uppercaseLean3 false in
#align pfunctor.M.iselect_eq_default PFunctor.MIntl.iselect_eq_default

@[simp]
theorem head_mk (x : F (MIntl F)) : head (MIntl.mk x) = x.1 :=
  Eq.symm <|
    calc
      x.1 = (dest (MIntl.mk x)).1 := by rw [dest_mk]
      _ = head (MIntl.mk x) := rfl
set_option linter.uppercaseLean3 false in
#align pfunctor.M.head_mk PFunctor.MIntl.head_mk

theorem children_mk {a} (x : F.B a → MIntl F) (i : F.B (head (MIntl.mk ⟨a, x⟩))) :
    children (MIntl.mk ⟨a, x⟩) i = x (cast (by rw [head_mk]) i) := by apply ext'; intro n; rfl
set_option linter.uppercaseLean3 false in
#align pfunctor.M.children_mk PFunctor.MIntl.children_mk

@[simp]
theorem ichildren_mk [DecidableEq F.A] [Inhabited (MIntl F)] (x : F (MIntl F)) (i : F.Idx) :
    ichildren i (MIntl.mk x) = x.iget i := by
  dsimp only [ichildren, PFunctor.Obj.iget]
  congr with h
set_option linter.uppercaseLean3 false in
#align pfunctor.M.ichildren_mk PFunctor.MIntl.ichildren_mk

@[simp]
theorem isubtree_cons [DecidableEq F.A] [Inhabited (MIntl F)] (ps : Path F) {a}
    (f : F.B a → MIntl F) {i : F.B a} :
    isubtree (⟨_, i⟩ :: ps) (MIntl.mk ⟨a, f⟩) = isubtree ps (f i) := by
  simp only [isubtree, ichildren_mk, PFunctor.Obj.iget, dif_pos, isubtree, cCasesOn_mk']; rfl
set_option linter.uppercaseLean3 false in
#align pfunctor.M.isubtree_cons PFunctor.MIntl.isubtree_cons

@[simp]
theorem iselect_nil [DecidableEq F.A] [Inhabited (MIntl F)] {a} (f : F.B a → MIntl F) :
    iselect nil (MIntl.mk ⟨a, f⟩) = a := rfl
set_option linter.uppercaseLean3 false in
#align pfunctor.M.iselect_nil PFunctor.MIntl.iselect_nil

@[simp]
theorem iselect_cons [DecidableEq F.A] [Inhabited (MIntl F)]
    (ps : Path F) {a} (f : F.B a → MIntl F) {i} :
    iselect (⟨a, i⟩ :: ps) (MIntl.mk ⟨a, f⟩) = iselect ps (f i) := by
  simp only [iselect, isubtree_cons]
set_option linter.uppercaseLean3 false in
#align pfunctor.M.iselect_cons PFunctor.MIntl.iselect_cons

theorem corec_def {X} (f : X → F X) (x₀ : X) :
    MIntl.corec f x₀ = MIntl.mk (MIntl.corec f <$> f x₀) := by
  dsimp only [MIntl.corec, MIntl.mk]
  congr with n
  cases' n with n
  · dsimp only [sCorec, Approx.sMk]
  · dsimp only [sCorec, Approx.sMk]
    cases h : f x₀
    dsimp only [(· <$> ·), PFunctor.map]
    congr

theorem ext_aux [Inhabited (MIntl F)] [DecidableEq F.A] {n : ℕ}
    (x y z : MIntl F) (hx : Agree' n z x)
    (hy : Agree' n z y) (hrec : ∀ ps : Path F, n = ps.length → iselect ps x = iselect ps y) :
    x.approx (n + 1) = y.approx (n + 1) := by
  induction' n with n n_ih generalizing x y z
  · specialize hrec [] rfl
    induction x using PFunctor.MIntl.cCasesOn'
    induction y using PFunctor.MIntl.cCasesOn'
    simp only [iselect_nil] at hrec
    subst hrec
    simp only [approx_mk, true_and_iff, eq_self_iff_true, heq_iff_eq, zero_eq, CofixA.intro.injEq,
                heq_eq_eq, eq_iff_true_of_subsingleton, and_self]
  · cases hx
    cases hy
    induction x using PFunctor.MIntl.cCasesOn'
    induction y using PFunctor.MIntl.cCasesOn'
    subst z
    iterate 3 (have := mk_inj ‹_›; cases this)
    rename_i n_ih a f₃ f₂ hAgree₂ _ _ h₂ _ _ f₁ h₁ hAgree₁ clr
    simp only [approx_mk, true_and_iff, eq_self_iff_true, heq_iff_eq]

    have := mk_inj h₁
    cases this; clear h₁
    have := mk_inj h₂
    cases this; clear h₂

    congr
    ext i
    apply n_ih
    · solve_by_elim
    · solve_by_elim
    introv h
    specialize hrec (⟨_, i⟩ :: ps) (congr_arg _ h)
    simp only [iselect_cons] at hrec
    exact hrec
set_option linter.uppercaseLean3 false in
#align pfunctor.M.ext_aux PFunctor.MIntl.ext_aux

open PFunctor.Approx

attribute [local instance] Classical.propDecidable

theorem ext [Inhabited (MIntl F)] (x y : MIntl F) (H : ∀ ps : Path F, iselect ps x = iselect ps y) :
    x = y := by
  apply ext'; intro i
  induction' i with i i_ih
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
set_option linter.uppercaseLean3 false in
#align pfunctor.M.ext PFunctor.MIntl.ext

section Bisim

variable (R : MIntl F → MIntl F → Prop)

local infixl:50 " ~ " => R

/-- Bisimulation is the standard proof technique for equality between
infinite tree-like structures -/
structure IsBisimulation : Prop where
  /-- The head of the trees are equal -/
  head : ∀ {a a'} {f f'}, MIntl.mk ⟨a, f⟩ ~ MIntl.mk ⟨a', f'⟩ → a = a'
  /-- The tails are equal -/
  tail : ∀ {a} {f f' : F.B a → MIntl F},
    MIntl.mk ⟨a, f⟩ ~ MIntl.mk ⟨a, f'⟩ → ∀ i : F.B a, f i ~ f' i
set_option linter.uppercaseLean3 false in
#align pfunctor.M.is_bisimulation PFunctor.MIntl.IsBisimulation

theorem nth_of_bisim [Inhabited (MIntl F)] (bisim : IsBisimulation R) (s₁ s₂) (ps : Path F) :
    (R s₁ s₂) →
      IsPath ps s₁ ∨ IsPath ps s₂ →
        iselect ps s₁ = iselect ps s₂ ∧
          ∃ (a : _) (f f' : F.B a → MIntl F),
            isubtree ps s₁ = MIntl.mk ⟨a, f⟩ ∧
              isubtree ps s₂ = MIntl.mk ⟨a, f'⟩ ∧ ∀ i : F.B a, f i ~ f' i := by
  intro h₀ hh
  induction' s₁ using PFunctor.MIntl.cCasesOn' with a f
  rename_i h₁ hh₁
  induction' s₂ using PFunctor.MIntl.cCasesOn' with a' f'
  rename_i h₁' hh₁' h₂ hh₂
  clear h₁ hh₁ h₂ hh₂ hh₁'
  obtain rfl : a = a' := bisim.head h₀
  induction' ps with i ps ps_ih generalizing a f f'
  · exists rfl, a, f, f', rfl, rfl
    apply bisim.tail h₀
  cases' i with a' i
  obtain rfl : a = a' := by rcases hh with hh|hh <;> cases isPath_cons hh <;> rfl
  dsimp only [iselect] at ps_ih ⊢
  have h₁ := bisim.tail h₀ i
  induction' h : f i using PFunctor.MIntl.cCasesOn' with a₀ f₀
  induction' h' : f' i using PFunctor.MIntl.cCasesOn' with a₁ f₁
  simp only [h, h', isubtree_cons] at ps_ih ⊢
  rw [h, h'] at h₁
  obtain rfl : a₀ = a₁ := bisim.head h₁
  apply ps_ih _ _ _ h₁
  rw [← h, ← h']
  apply Or.imp isPath_cons' isPath_cons' hh
set_option linter.uppercaseLean3 false in
#align pfunctor.M.nth_of_bisim PFunctor.MIntl.nth_of_bisim

theorem eq_of_bisim [Nonempty (MIntl F)] (bisim : IsBisimulation R) :
    ∀ s₁ s₂, R s₁ s₂ → s₁ = s₂ := by
  inhabit MIntl F
  introv Hr; apply ext
  introv
  by_cases h : IsPath ps s₁ ∨ IsPath ps s₂
  · have H := nth_of_bisim R bisim _ _ ps Hr h
    exact H.left
  · rw [not_or] at h
    cases' h with h₀ h₁
    simp only [iselect_eq_default, *, not_false_iff]
set_option linter.uppercaseLean3 false in
#align pfunctor.M.eq_of_bisim PFunctor.MIntl.eq_of_bisim

end Bisim

universe u' v'

variable {P : PFunctor.{u}} {α : Type u}

theorem bisim (R : MIntl P → MIntl P → Prop)
    (h : ∀ x y, R x y → ∃ a f f',
      MIntl.dest x = ⟨a, f⟩ ∧ MIntl.dest y = ⟨a, f'⟩ ∧ ∀ i, R (f i) (f' i)) :
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

end MIntl

/-! ## Override the data structure of M-types

The structure of `MIntl` is the closure which returns the approximation of the tree with the given
depth. However, if we want the sequence of data with increasing depth, we can't reuse computational
resource which is used for previous datas. So we override the structure of `M` to lazy evaluated
infinite trees.
-/

-- TODO(Miyahara): Use `opaque_repr` attribute after lean4#2292
/-- Wrap `MIntl`. This is used to implement `M`. -/
opaque MSpec : (T : Type u) × (T ≃ MIntl F) :=
  ⟨MIntl F, Equiv.refl _⟩

/-- For polynomial functor `F`, `M F` is its final coalgebra -/
def M :=
  (MSpec F).1
set_option linter.uppercaseLean3 false in
#align pfunctor.MIntl PFunctor.M

/-- This is the meta type of `CofixA F ∞`. This is theorically equivalent to `W`, but
this can be an infinite structure. -/
unsafe inductive CofixI (F : PFunctor.{u})
  /-- Construct `CofixI` from an infinite structure. -/
  | mk (t : F (CofixI F)) : CofixI F

namespace M

variable {F}

/-- Construct the internal model from M-type. This is useful to get the finite approximation. -/
noncomputable def toIntl (x : M F) : MIntl F :=
  (MSpec F).2 x

/-- Construct M-type from the internal model. Not optimized.
Consider using `corec` before use this. -/
noncomputable def ofIntl (x : MIntl F) : M F :=
  (MSpec F).2.symm x

theorem leftInv_ofIntl_toIntl : LeftInverse (ofIntl : MIntl F → M F) toIntl :=
  (MSpec F).2.left_inv'

@[simp]
theorem toIntl_comp_ofIntl : (toIntl : M F → MIntl F) ∘ ofIntl = id :=
  (MSpec F).2.self_comp_symm

@[simp]
theorem toIntl_ofIntl (x : MIntl F) : toIntl (ofIntl x) = x :=
  (MSpec F).2.apply_symm_apply x

theorem rightInv_ofIntl_toIntl : RightInverse (ofIntl : MIntl F → M F) toIntl :=
  (MSpec F).2.right_inv'

@[simp]
theorem ofIntl_comp_toIntl : (ofIntl : MIntl F → M F) ∘ toIntl = id :=
  (MSpec F).2.symm_comp_self

@[simp]
theorem eta (x : M F) : ofIntl (toIntl x) = x :=
  (MSpec F).2.symm_apply_apply x

@[simp]
theorem ofIntl.injEq (x y : MIntl F) : (ofIntl x = ofIntl y) = (x = y) :=
  propext ((MSpec F).2.symm.injective.eq_iff)

/-- Get the finite approximation of the given tree. -/
noncomputable def approx (x : M F) (n : ℕ) : CofixA F n :=
  x.toIntl.approx n

theorem consistent (x : M F) : AllAgree x.approx :=
  x.toIntl.consistent

@[simp]
theorem approx_ofIntl (x : MIntl F) (n : ℕ) : approx (ofIntl x) n = x.approx n := by
  rw [approx, toIntl_ofIntl]

@[elab_as_elim]
theorem ind {motive : M F → Prop}
    (ofIntl : (x : MIntl F) → motive (ofIntl x)) (y : M F) : motive y :=
  eta y ▸ ofIntl (toIntl y)

/-- Convert `M` to `CofixI`. -/
@[inline]
unsafe def ofI : CofixI F → M F :=
  unsafeCast

/-- Convert `CofixI` to `M`. -/
@[inline]
unsafe def toI : M F → CofixI F :=
  unsafeCast

variable {X : Type*}

variable (f : X → F X)

/-- The implemention of `corec`. This generates data trees lazily. -/
@[inline]
unsafe def corecUnsafe (i : X) : M F :=
  let rec
    /-- The main loop of `corecUnsafe`. -/
    @[specialize] loop (i : X) : CofixI F :=
      CofixI.mk <|
        match f i with
        | ⟨a, o⟩ => ⟨a, fun b => loop (o b)⟩
  ofI (loop i)

/-- Corecursor for the M-type defined by `F`. -/
@[implemented_by corecUnsafe]
protected def corec (i : X) : M F :=
  ofIntl (MIntl.corec f i)
set_option linter.uppercaseLean3 false in
#align pfunctor.M.corec PFunctor.M.corec

instance inhabited [Inhabited F.A] : Inhabited (M F) where
  default := M.corec (fun a : F.A => ⟨a, fun _ => default⟩) default
set_option linter.uppercaseLean3 false in
#align pfunctor.M.inhabited PFunctor.M.inhabited

/-- The implemention of `dest`. This unfolds an M-type. -/
unsafe def destUnsafe (x : M F) : F (M F) :=
  match toI x with
  | ⟨⟨a, o⟩⟩ => ⟨a, fun b => ofI (o b)⟩

/-- This unfolds an M-type. -/
@[implemented_by destUnsafe]
def dest (x : M F) : F (M F) :=
  ofIntl <$> x.toIntl.dest
set_option linter.uppercaseLean3 false in
#align pfunctor.M.dest PFunctor.M.dest

@[simp]
theorem dest_ofIntl (x : MIntl F) : dest (ofIntl x) = ofIntl <$> x.dest := by
  rw [dest, toIntl_ofIntl]

/-- The implemention of `approx`. -/
def approxComputable (x : M F) : (n : ℕ) → CofixA F n
  | 0      => CofixA.continue
  | succ n =>
    match dest x with
    | ⟨a, o⟩ => CofixA.intro a fun b => approxComputable (o b) n

@[csimp]
theorem approx_eq_approxComputable : @approx.{u} = @approxComputable.{u} := by
  funext F x n; cases' x using ind with x
  induction n generalizing x with
  | zero      => apply cofixA_eq_zero
  | succ n hn =>
    simp [approxComputable, MIntl.dest, PFunctor.map_eq, ← hn]
    conv_lhs => rw [← MIntl.mk_dest x, MIntl.dest, MIntl.approx_mk]

/-- The implemention of `toIntl`. -/
def toIntlComputable (x : M F) : MIntl F where
  approx := approx x
  consistent := consistent x

@[csimp]
theorem toIntl_eq_toIntlComputable : @toIntl.{u} = @toIntlComputable.{u} :=
  rfl

/-- The implemention of `mk`. -/
@[inline]
unsafe def mkUnsafe (x : F (M F)) : M F :=
  match x with
  | ⟨a, o⟩ => ofI <| CofixI.mk <| ⟨a, fun b => toI (o b)⟩

/-- constructor for M-types -/
@[implemented_by mkUnsafe]
protected def mk (x : F (M F)) : M F :=
  ofIntl (MIntl.mk (toIntl <$> x))
set_option linter.uppercaseLean3 false in
#align pfunctor.M.mk PFunctor.MIntl.mk

@[simp]
theorem mk_ofIntl_map (x : F (MIntl F)) : M.mk (ofIntl <$> x) = ofIntl (MIntl.mk x) := by
  simp [M.mk, Functor.map_map]

@[simp]
theorem dest_mk (x : F (M F)) : dest (M.mk x) = x := by
  simp [dest, M.mk, Functor.map_map]
set_option linter.uppercaseLean3 false in
#align pfunctor.M.dest_mk PFunctor.M.dest_mk

@[simp]
theorem mk_dest (x : M F) : M.mk (dest x) = x := by
  cases x using ind; simp
set_option linter.uppercaseLean3 false in
#align pfunctor.M.mk_dest PFunctor.M.mk_dest

theorem mk_inj {x y : F (M F)} (h : M.mk x = M.mk y) : x = y := by
  rw [← dest_mk x, h, dest_mk]
set_option linter.uppercaseLean3 false in
#align pfunctor.M.mk_inj PFunctor.M.mk_inj

/-- destructor for M-types -/
@[inline]
protected def cCases {r : M F → Sort w} (f : ∀ x : F (M F), r (M.mk x))
    (x : M F) : r x :=
  suffices r (M.mk (dest x)) by
    rw [← mk_dest x]
    exact this
  f _
set_option linter.uppercaseLean3 false in
#align pfunctor.M.cases PFunctor.M.cCases

/-- destructor for M-types -/
@[inline]
protected def cCasesOn {r : M F → Sort w} (x : M F)
    (f : ∀ x : F (M F), r (M.mk x)) : r x :=
  M.cCases f x
set_option linter.uppercaseLean3 false in
#align pfunctor.M.cases_on PFunctor.M.cCasesOn

/-- destructor for M-types, similar to `cCasesOn` but also
gives access directly to the root and subtrees on an M-type -/
@[inline]
protected def cCasesOn' {r : M F → Sort w} (x : M F) (f : ∀ a f, r (M.mk ⟨a, f⟩)) :
    r x :=
  M.cCasesOn x (fun ⟨a, g⟩ => f a g)
set_option linter.uppercaseLean3 false in
#align pfunctor.M.cases_on' PFunctor.M.cCasesOn'

@[simp]
theorem cCases_mk {r : M F → Sort*} (x : F (M F))
    (f : ∀ x : F (M F), r (M.mk x)) :
    PFunctor.M.cCases f (M.mk x) = f x := by
  dsimp only [M.cCases]
  rw [eq_mpr_eq_cast, cast_eq_iff_heq, dest_mk]
set_option linter.uppercaseLean3 false in
#align pfunctor.M.cases_mk PFunctor.M.cCases_mk

@[simp]
theorem cCasesOn_mk {r : M F → Sort*} (x : F (M F))
    (f : ∀ x : F (M F), r (M.mk x)) :
    PFunctor.M.cCasesOn (M.mk x) f = f x :=
  cCases_mk x f
set_option linter.uppercaseLean3 false in
#align pfunctor.M.cases_on_mk PFunctor.M.cCasesOn_mk

@[simp]
theorem cCasesOn_mk' {r : M F → Sort*} {a} (x : F.B a → M F)
    (f : ∀ (a) (f : F.B a → M F), r (M.mk ⟨a, f⟩)) :
    PFunctor.M.cCasesOn' (M.mk ⟨a, x⟩) f = f a x :=
  @cCases_mk F r ⟨a, x⟩ (fun ⟨a, g⟩ => f a g)
set_option linter.uppercaseLean3 false in
#align pfunctor.M.cases_on_mk' PFunctor.M.cCasesOn_mk'

theorem corec_def {X} (f : X → F X) (x₀ : X) :
    M.corec f x₀ = M.mk (M.corec f <$> f x₀) := by
  simpa [M.corec, M.mk, Functor.map_map, Function.comp] using MIntl.corec_def f x₀

/-- corecursor for `M F` with swapped arguments -/
abbrev corecOn {X : Type*} (x₀ : X) (f : X → F X) : M F :=
  M.corec f x₀
set_option linter.uppercaseLean3 false in
#align pfunctor.M.corec_on PFunctor.M.corecOn

variable {P : PFunctor.{u}} {α : Type u}

@[simp]
theorem dest_corec (g : α → P α) (x : α) :
    M.dest (M.corec g x) = M.corec g <$> g x := by
  rw [corec_def, dest_mk]
set_option linter.uppercaseLean3 false in
#align pfunctor.M.dest_corec PFunctor.M.dest_corec

theorem bisim (R : M P → M P → Prop)
    (h : ∀ x y, R x y → ∃ a f f',
      M.dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ ∀ i, R (f i) (f' i)) :
    ∀ x y, R x y → x = y := by
  have hm :
    Function.RightInverse (Functor.map ofIntl : P (MIntl P) → P (M P)) (Functor.map toIntl)
  · simp [Function.RightInverse, LeftInverse, Functor.map_map]
  simp only [leftInv_ofIntl_toIntl.surjective.forall,
    leftInv_ofIntl_toIntl.surjective.comp_left.exists,
    comp_apply, ← PFunctor.map_eq, dest_ofIntl, hm.injective.eq_iff] at h
  intro x₁ x₂ hx; cases x₁ using ind; cases x₂ using ind; rw [ofIntl.injEq]
  exact MIntl.bisim _ h _ _ hx
set_option linter.uppercaseLean3 false in
#align pfunctor.M.bisim PFunctor.M.bisim

theorem bisim' {α : Type*} (Q : α → Prop) (u v : α → M P)
    (h : ∀ x, Q x → ∃ a f f',
          M.dest (u x) = ⟨a, f⟩
          ∧ M.dest (v x) = ⟨a, f'⟩
          ∧ ∀ i, ∃ x', Q x' ∧ f i = u x' ∧ f' i = v x'
      ) :
    ∀ x, Q x → u x = v x := fun x Qx =>
  let R := fun w z : M P => ∃ x', Q x' ∧ w = u x' ∧ z = v x'
  @M.bisim P R
    (fun _ _ ⟨x', Qx', xeq, yeq⟩ =>
      let ⟨a, f, f', ux'eq, vx'eq, h'⟩ := h x' Qx'
      ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
    _ _ ⟨x, Qx, rfl, rfl⟩
set_option linter.uppercaseLean3 false in
#align pfunctor.M.bisim' PFunctor.M.bisim'

-- for the record, show M_bisim follows from _bisim'
theorem bisim_equiv (R : M P → M P → Prop)
    (h : ∀ x y, R x y → ∃ a f f',
      M.dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ ∀ i, R (f i) (f' i)) :
    ∀ x y, R x y → x = y := fun x y Rxy =>
  let Q : M P × M P → Prop := fun p => R p.fst p.snd
  bisim' Q Prod.fst Prod.snd
    (fun p Qp =>
      let ⟨a, f, f', hx, hy, h'⟩ := h p.fst p.snd Qp
      ⟨a, f, f', hx, hy, fun i => ⟨⟨f i, f' i⟩, h' i, rfl, rfl⟩⟩)
    ⟨x, y⟩ Rxy
set_option linter.uppercaseLean3 false in
#align pfunctor.M.bisim_equiv PFunctor.M.bisim_equiv

theorem corec_unique (g : α → P α) (f : α → M P) (hyp : ∀ x, M.dest (f x) = f <$> g x) :
    f = M.corec g := by
  ext x
  apply bisim' (fun _ => True) _ _ _ _ trivial
  clear x
  intro x _
  cases' gxeq : g x with a f'
  have h₀ : M.dest (f x) = ⟨a, f ∘ f'⟩ := by rw [hyp, gxeq, PFunctor.map_eq]
  have h₁ : M.dest (M.corec g x) = ⟨a, M.corec g ∘ f'⟩ := by
    rw [dest_corec, gxeq, PFunctor.map_eq]
  refine' ⟨_, _, _, h₀, h₁, _⟩
  intro i
  exact ⟨f' i, trivial, rfl, rfl⟩
set_option linter.uppercaseLean3 false in
#align pfunctor.M.corec_unique PFunctor.M.corec_unique

/-- The implemention of `ofIntl`. Not optimized. -/
def ofIntlComputable (x : MIntl F) : M F :=
  M.corec MIntl.dest x

@[csimp]
theorem ofIntl_eq_ofIntlComputable : @ofIntl.{u} = @ofIntlComputable.{u} := by
  funext F x; unfold ofIntlComputable; revert x; rw [← Function.funext_iff]
  apply corec_unique; intro x; simp

/-- corecursor where the state of the computation can be sent downstream
in the form of a recursive call -/
@[inline]
def corec₁ {α : Type u} (F : ∀ X, (α → X) → α → P X) : α → M P :=
  M.corec (F _ id)
set_option linter.uppercaseLean3 false in
#align pfunctor.M.corec₁ PFunctor.M.corec₁

/-- The more efficient implemention of `corec'`. -/
@[inline]
unsafe def corec'Unsafe {α : Type u} (F : α → M P ⊕ P α) (x : α) : M P :=
  let rec
    /-- The main loop of `corec'Unsafe`. -/
    @[specialize] loop (x : α) : CofixI P :=
      CofixI.mk <|
        match F x with
        | Sum.inr ⟨a, o⟩ => ⟨a, fun b => loop (o b)⟩
        | Sum.inl y =>
          match toI y with
          | ⟨t⟩ => t
  ofI (loop x)

/-- corecursor where it is possible to return a fully formed value at any point
of the computation -/
@[implemented_by corec'Unsafe]
def corec' {α : Type u} (F : α → M P ⊕ P α) (x : α) : M P :=
  M.corec
    (fun (s : M P ⊕ α) =>
      match Sum.bind s F with
      | Sum.inr a => Sum.inr <$> a
      | Sum.inl y => Sum.inl <$> M.dest y)
    (Sum.inr x)
set_option linter.uppercaseLean3 false in
#align pfunctor.M.corec' PFunctor.M.corec'

end M

end PFunctor
