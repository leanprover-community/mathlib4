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
  -- ⊢ CofixA.intro a✝¹ a✝ = CofixA.intro (head' (CofixA.intro a✝¹ a✝)) (children'  …
           -- 🎉 no goals
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
                                                                         -- 🎉 no goals
#align pfunctor.approx.agree_trival PFunctor.Approx.agree_trival

theorem agree_children {n : ℕ} (x : CofixA F (succ n)) (y : CofixA F (succ n + 1)) {i j}
    (h₀ : HEq i j) (h₁ : Agree x y) : Agree (children' x i) (children' y j) := by
  cases' h₁ with _ _ _ _ _ _ hagree; cases h₀
  -- ⊢ Agree (children' (CofixA.intro a✝ x✝) i) (children' (CofixA.intro a✝ x'✝) j)
                                     -- ⊢ Agree (children' (CofixA.intro a✝ x✝) i) (children' (CofixA.intro a✝ x'✝) i)
  apply hagree
  -- 🎉 no goals
#align pfunctor.approx.agree_children PFunctor.Approx.agree_children

/-- `truncate a` turns `a` into a more limited approximation -/
def truncate : ∀ {n : ℕ}, CofixA F (n + 1) → CofixA F n
  | 0, CofixA.intro _ _ => CofixA.continue
  | succ _, CofixA.intro i f => CofixA.intro i <| truncate ∘ f
#align pfunctor.approx.truncate PFunctor.Approx.truncate

theorem truncate_eq_of_agree {n : ℕ} (x : CofixA F n) (y : CofixA F (succ n)) (h : Agree x y) :
    truncate y = x := by
  induction n <;> cases x <;> cases y
  -- ⊢ truncate y = x
                  -- ⊢ truncate y = CofixA.continue
                  -- ⊢ truncate y = CofixA.intro a✝¹ a✝
                              -- ⊢ truncate (CofixA.intro a✝¹ a✝) = CofixA.continue
                              -- ⊢ truncate (CofixA.intro a✝¹ a✝) = CofixA.intro a✝³ a✝²
  · rfl
    -- 🎉 no goals
  · -- cases' h with _ _ _ _ _ h₀ h₁
    cases h
    -- ⊢ truncate (CofixA.intro a✝² x'✝) = CofixA.intro a✝² a✝¹
    simp only [truncate, Function.comp, true_and_iff, eq_self_iff_true, heq_iff_eq]
    -- ⊢ (CofixA.intro a✝² fun x => truncate (x'✝ x)) = CofixA.intro a✝² a✝¹
    -- porting note: used to be `ext y`
    rename_i n_ih a f y h₁
    -- ⊢ (CofixA.intro a fun x => truncate (y x)) = CofixA.intro a f
    suffices (fun x => truncate (y x)) = f
      by simp [this]; try (exact HEq.rfl;)
    funext y
    -- ⊢ truncate (y✝ y) = f y

    apply n_ih
    -- ⊢ Agree (f y) (y✝ y)
    apply h₁
    -- 🎉 no goals
#align pfunctor.approx.truncate_eq_of_agree PFunctor.Approx.truncate_eq_of_agree

variable {X : Type w}

variable (f : X → F.Obj X)

/-- `sCorec f i n` creates an approximation of height `n`
of the final coalgebra of `f` -/
def sCorec : X → ∀ n, CofixA F n
  | _, 0 => CofixA.continue
  | j, succ _ => CofixA.intro (f j).1 fun i => sCorec ((f j).2 i) _
#align pfunctor.approx.s_corec PFunctor.Approx.sCorec

theorem P_corec (i : X) (n : ℕ) : Agree (sCorec f i n) (sCorec f i (succ n)) := by
  induction' n with n n_ih generalizing i
  -- ⊢ Agree (sCorec f i zero) (sCorec f i (succ zero))
  constructor
  -- ⊢ Agree (sCorec f i (succ n)) (sCorec f i (succ (succ n)))
  cases' h : f i with y g
  -- ⊢ Agree (sCorec f i (succ n)) (sCorec f i (succ (succ n)))
  constructor
  -- ⊢ ∀ (i_1 : B F (f i).fst), Agree (sCorec f (Sigma.snd (f i) i_1) n) (sCorec f  …
  introv
  -- ⊢ Agree (sCorec f (Sigma.snd (f i✝) i) n) (sCorec f (Sigma.snd (f i✝) i) (succ …
  apply n_ih
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.approx.P_corec PFunctor.Approx.P_corec

/-- `Path F` provides indices to access internal nodes in `Corec F` -/
def Path (F : PFunctor.{u}) :=
  List F.IdxCat
#align pfunctor.approx.path PFunctor.Approx.Path

instance Path.inhabited : Inhabited (Path F) :=
  ⟨[]⟩
#align pfunctor.approx.path.inhabited PFunctor.Approx.Path.inhabited

open List Nat

instance CofixA.instSubsingleton : Subsingleton (CofixA F 0) :=
  ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩
      -- ⊢ continue = continue
                    -- 🎉 no goals

theorem head_succ' (n m : ℕ) (x : ∀ n, CofixA F n) (Hconsistent : AllAgree x) :
    head' (x (succ n)) = head' (x (succ m)) := by
  suffices ∀ n, head' (x (succ n)) = head' (x 1) by simp [this]
  -- ⊢ ∀ (n : ℕ), head' (x (succ n)) = head' (x 1)
  clear m n
  -- ⊢ ∀ (n : ℕ), head' (x (succ n)) = head' (x 1)
  intro n
  -- ⊢ head' (x (succ n)) = head' (x 1)
  cases' h₀ : x (succ n) with _ i₀ f₀
  -- ⊢ head' (CofixA.intro i₀ f₀) = head' (x 1)
  cases' h₁ : x 1 with _ i₁ f₁
  -- ⊢ head' (CofixA.intro i₀ f₀) = head' (CofixA.intro i₁ f₁)
  dsimp only [head']
  -- ⊢ i₀ = i₁
  induction' n with n n_ih
  -- ⊢ i₀ = i₁
  · rw [h₁] at h₀
    -- ⊢ i₀ = i₁
    cases h₀
    -- ⊢ i₀ = i₀
    trivial
    -- 🎉 no goals
  · have H := Hconsistent (succ n)
    -- ⊢ i₀ = i₁
    cases' h₂ : x (succ n) with _ i₂ f₂
    -- ⊢ i₀ = i₁
    rw [h₀, h₂] at H
    -- ⊢ i₀ = i₁
    apply n_ih (truncate ∘ f₀)
    -- ⊢ x (succ n) = CofixA.intro i₀ (truncate ∘ f₀)
    rw [h₂]
    -- ⊢ CofixA.intro i₂ f₂ = CofixA.intro i₀ (truncate ∘ f₀)
    cases' H with _ _ _ _ _ _ hagree
    -- ⊢ CofixA.intro i₀ f₂ = CofixA.intro i₀ (truncate ∘ f₀)
    congr
    -- ⊢ f₂ = truncate ∘ f₀
    funext j
    -- ⊢ f₂ j = (truncate ∘ f₀) j
    dsimp only [comp_apply]
    -- ⊢ f₂ j = truncate (f₀ j)
    rw [truncate_eq_of_agree]
    -- ⊢ Agree (f₂ j) (f₀ j)
    apply hagree
    -- 🎉 no goals
#align pfunctor.approx.head_succ' PFunctor.Approx.head_succ'

end Approx

open Approx

/-- Internal definition for `M`. It is needed to avoid name clashes
between `M.mk` and `M.cases_on` and the declarations generated for
the structure -/
structure MIntl where
  /-- An `n`-th level approximation, for each depth `n` -/
  approx : ∀ n, CofixA F n
  /-- Each approximation agrees with the next -/
  consistent : AllAgree approx
set_option linter.uppercaseLean3 false in
#align pfunctor.M_intl PFunctor.MIntl

/-- For polynomial functor `F`, `M F` is its final coalgebra -/
def M :=
  MIntl F
set_option linter.uppercaseLean3 false in
#align pfunctor.M PFunctor.M

theorem M.default_consistent [Inhabited F.A] : ∀ n, Agree (default : CofixA F n) default
  | 0 => Agree.continu _ _
  | succ n => Agree.intro _ _ fun _ => M.default_consistent n
set_option linter.uppercaseLean3 false in
#align pfunctor.M.default_consistent PFunctor.M.default_consistent

instance M.inhabited [Inhabited F.A] : Inhabited (M F) :=
  ⟨{  approx := default
      consistent := M.default_consistent _ }⟩
set_option linter.uppercaseLean3 false in
#align pfunctor.M.inhabited PFunctor.M.inhabited

instance MIntl.inhabited [Inhabited F.A] : Inhabited (MIntl F) :=
  show Inhabited (M F) by infer_instance
                          -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M_intl.inhabited PFunctor.MIntl.inhabited

namespace M

theorem ext' (x y : M F) (H : ∀ i : ℕ, x.approx i = y.approx i) : x = y := by
  cases x
  -- ⊢ { approx := approx✝, consistent := consistent✝ } = y
  cases y
  -- ⊢ { approx := approx✝¹, consistent := consistent✝¹ } = { approx := approx✝, co …
  congr with n
  -- ⊢ approx✝¹ n = approx✝ n
  apply H
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.ext' PFunctor.M.ext'

variable {X : Type*}

variable (f : X → F.Obj X)

variable {F}

/-- Corecursor for the M-type defined by `F`. -/
protected def corec (i : X) : M F where
  approx := sCorec f i
  consistent := P_corec _ _
set_option linter.uppercaseLean3 false in
#align pfunctor.M.corec PFunctor.M.corec

/-- given a tree generated by `F`, `head` gives us the first piece of data
it contains -/
def head (x : M F) :=
  head' (x.1 1)
set_option linter.uppercaseLean3 false in
#align pfunctor.M.head PFunctor.M.head

/-- return all the subtrees of the root of a tree `x : M F` -/
def children (x : M F) (i : F.B (head x)) : M F :=
  let H := fun n : ℕ => @head_succ' _ n 0 x.1 x.2
  { approx := fun n => children' (x.1 _) (cast (congr_arg _ <| by simp only [head, H]) i)
                                                                  -- 🎉 no goals
    consistent := by
      intro n
      -- ⊢ Agree ((fun n => children' (MIntl.approx x (succ n)) (cast (_ : B F (head x) …
      have P' := x.2 (succ n)
      -- ⊢ Agree ((fun n => children' (MIntl.approx x (succ n)) (cast (_ : B F (head x) …
      apply agree_children _ _ _ P'
      -- ⊢ HEq (cast (_ : B F (head x) = B F (head' (MIntl.approx x (succ n)))) i) (cas …
      trans i
      -- ⊢ HEq (cast (_ : B F (head x) = B F (head' (MIntl.approx x (succ n)))) i) i
      apply cast_heq
      -- ⊢ HEq i (cast (_ : B F (head x) = B F (head' (MIntl.approx x (succ (succ n)))) …
      symm
      -- ⊢ HEq (cast (_ : B F (head x) = B F (head' (MIntl.approx x (succ (succ n)))))  …
      apply cast_heq }
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.children PFunctor.M.children

/-- select a subtree using an `i : F.Idx` or return an arbitrary tree if
`i` designates no subtree of `x` -/
def ichildren [Inhabited (M F)] [DecidableEq F.A] (i : F.IdxCat) (x : M F) : M F :=
  if H' : i.1 = head x then children x (cast (congr_arg _ <| by simp only [head, H']) i.2)
                                                                -- 🎉 no goals
  else default
set_option linter.uppercaseLean3 false in
#align pfunctor.M.ichildren PFunctor.M.ichildren

theorem head_succ (n m : ℕ) (x : M F) : head' (x.approx (succ n)) = head' (x.approx (succ m)) :=
  head_succ' n m _ x.consistent
set_option linter.uppercaseLean3 false in
#align pfunctor.M.head_succ PFunctor.M.head_succ

theorem head_eq_head' : ∀ (x : M F) (n : ℕ), head x = head' (x.approx <| n + 1)
  | ⟨_, h⟩, _ => head_succ' _ _ _ h
set_option linter.uppercaseLean3 false in
#align pfunctor.M.head_eq_head' PFunctor.M.head_eq_head'

theorem head'_eq_head : ∀ (x : M F) (n : ℕ), head' (x.approx <| n + 1) = head x
  | ⟨_, h⟩, _ => head_succ' _ _ _ h
set_option linter.uppercaseLean3 false in
#align pfunctor.M.head'_eq_head PFunctor.M.head'_eq_head

theorem truncate_approx (x : M F) (n : ℕ) : truncate (x.approx <| n + 1) = x.approx n :=
  truncate_eq_of_agree _ _ (x.consistent _)
set_option linter.uppercaseLean3 false in
#align pfunctor.M.truncate_approx PFunctor.M.truncate_approx

/-- unfold an M-type -/
def dest : M F → F.Obj (M F)
  | x => ⟨head x, fun i => children x i⟩
set_option linter.uppercaseLean3 false in
#align pfunctor.M.dest PFunctor.M.dest

namespace Approx

/-- generates the approximations needed for `M.mk` -/
protected def sMk (x : F.Obj <| M F) : ∀ n, CofixA F n
  | 0 => CofixA.continue
  | succ n => CofixA.intro x.1 fun i => (x.2 i).approx n
set_option linter.uppercaseLean3 false in
#align pfunctor.M.approx.s_mk PFunctor.M.Approx.sMk

protected theorem P_mk (x : F.Obj <| M F) : AllAgree (Approx.sMk x)
  | 0 => by constructor
            -- 🎉 no goals
  | succ n => by
    constructor
    -- ⊢ ∀ (i : B F x.fst), Agree (MIntl.approx (Sigma.snd x i) n) (MIntl.approx (Sig …
    introv
    -- ⊢ Agree (MIntl.approx (Sigma.snd x i) n) (MIntl.approx (Sigma.snd x i) (succ n))
    apply (x.2 i).consistent
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.approx.P_mk PFunctor.M.Approx.P_mk

end Approx

/-- constructor for M-types -/
protected def mk (x : F.Obj <| M F) : M F
    where
  approx := Approx.sMk x
  consistent := Approx.P_mk x
set_option linter.uppercaseLean3 false in
#align pfunctor.M.mk PFunctor.M.mk

/-- `Agree' n` relates two trees of type `M F` that
are the same up to depth `n` -/
inductive Agree' : ℕ → M F → M F → Prop
  | trivial (x y : M F) : Agree' 0 x y
  | step {n : ℕ} {a} (x y : F.B a → M F) {x' y'} :
      x' = M.mk ⟨a, x⟩ → y' = M.mk ⟨a, y⟩ → (∀ i, Agree' n (x i) (y i)) → Agree' (succ n) x' y'
set_option linter.uppercaseLean3 false in
#align pfunctor.M.agree' PFunctor.M.Agree'

@[simp]
theorem dest_mk (x : F.Obj <| M F) : dest (M.mk x) = x := by rfl
                                                             -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.dest_mk PFunctor.M.dest_mk

@[simp]
theorem mk_dest (x : M F) : M.mk (dest x) = x := by
  apply ext'
  -- ⊢ ∀ (i : ℕ), MIntl.approx (M.mk (dest x)) i = MIntl.approx x i
  intro n
  -- ⊢ MIntl.approx (M.mk (dest x)) n = MIntl.approx x n
  dsimp only [M.mk]
  -- ⊢ Approx.sMk (dest x) n = MIntl.approx x n
  induction' n with n
  -- ⊢ Approx.sMk (dest x) zero = MIntl.approx x zero
  · apply @Subsingleton.elim _ CofixA.instSubsingleton
    -- 🎉 no goals
  dsimp only [Approx.sMk, dest, head]
  -- ⊢ (CofixA.intro (head' (MIntl.approx x 1)) fun i => MIntl.approx (children x i …
  cases' h : x.approx (succ n) with _ hd ch
  -- ⊢ (CofixA.intro (head' (MIntl.approx x 1)) fun i => MIntl.approx (children x i …
  have h' : hd = head' (x.approx 1) := by
    rw [← head_succ' n, h, head']
    apply x.consistent
  revert ch
  -- ⊢ ∀ (ch : B F hd → CofixA F n), MIntl.approx x (succ n) = CofixA.intro hd ch → …
  rw [h']
  -- ⊢ ∀ (ch : B F (head' (MIntl.approx x 1)) → CofixA F n), MIntl.approx x (succ n …
  intros ch h
  -- ⊢ (CofixA.intro (head' (MIntl.approx x 1)) fun i => MIntl.approx (children x i …
  congr
  -- ⊢ (fun i => MIntl.approx (children x i) n) = ch
  · ext a
    -- ⊢ MIntl.approx (children x a) n = ch a
    dsimp only [children]
    -- ⊢ children' (MIntl.approx x (succ n)) (cast (_ : B F (head x) = B F (head' (MI …
    generalize hh : cast _ a = a''
    -- ⊢ children' (MIntl.approx x (succ n)) a'' = ch a
    rw [cast_eq_iff_heq] at hh
    -- ⊢ children' (MIntl.approx x (succ n)) a'' = ch a
    revert a''
    -- ⊢ ∀ (a'' : B F (head' (MIntl.approx x (succ n)))), HEq a a'' → children' (MInt …
    rw [h]
    -- ⊢ ∀ (a'' : B F (head' (CofixA.intro (head' (MIntl.approx x 1)) ch))), HEq a a' …
    intros _ hh
    -- ⊢ children' (CofixA.intro (head' (MIntl.approx x 1)) ch) a''✝ = ch a
    cases hh
    -- ⊢ children' (CofixA.intro (head' (MIntl.approx x 1)) ch) a = ch a
    rfl
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.mk_dest PFunctor.M.mk_dest

theorem mk_inj {x y : F.Obj <| M F} (h : M.mk x = M.mk y) : x = y := by rw [← dest_mk x, h, dest_mk]
                                                                        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.mk_inj PFunctor.M.mk_inj

/-- destructor for M-types -/
protected def cases {r : M F → Sort w} (f : ∀ x : F.Obj <| M F, r (M.mk x)) (x : M F) : r x :=
  suffices r (M.mk (dest x)) by
    rw [← mk_dest x]
    -- ⊢ r (M.mk (dest x))
    exact this
    -- 🎉 no goals
  f _
set_option linter.uppercaseLean3 false in
#align pfunctor.M.cases PFunctor.M.cases

/-- destructor for M-types -/
protected def casesOn {r : M F → Sort w} (x : M F) (f : ∀ x : F.Obj <| M F, r (M.mk x)) : r x :=
  M.cases f x
set_option linter.uppercaseLean3 false in
#align pfunctor.M.cases_on PFunctor.M.casesOn

/-- destructor for M-types, similar to `casesOn` but also
gives access directly to the root and subtrees on an M-type -/
protected def casesOn' {r : M F → Sort w} (x : M F) (f : ∀ a f, r (M.mk ⟨a, f⟩)) : r x :=
  M.casesOn x (fun ⟨a, g⟩ => f a g)
set_option linter.uppercaseLean3 false in
#align pfunctor.M.cases_on' PFunctor.M.casesOn'

theorem approx_mk (a : F.A) (f : F.B a → M F) (i : ℕ) :
    (M.mk ⟨a, f⟩).approx (succ i) = CofixA.intro a fun j => (f j).approx i :=
  rfl
set_option linter.uppercaseLean3 false in
#align pfunctor.M.approx_mk PFunctor.M.approx_mk

@[simp]
theorem agree'_refl {n : ℕ} (x : M F) : Agree' n x x := by
  induction' n with _ n_ih generalizing x <;>
  -- ⊢ Agree' zero x x
  induction x using PFunctor.M.casesOn' <;> constructor <;> try rfl
  -- ⊢ Agree' zero (M.mk { fst := a✝, snd := f✝ }) (M.mk { fst := a✝, snd := f✝ })
  -- ⊢ Agree' (succ n✝) (M.mk { fst := a✝, snd := f✝ }) (M.mk { fst := a✝, snd := f …
                                            -- 🎉 no goals
                                                            -- 🎉 no goals
                                                            -- 🎉 no goals
                                                            -- ⊢ ∀ (i : B F a✝), Agree' n✝ (f✝ i) (f✝ i)
  intros
  -- ⊢ Agree' n✝ (f✝ i✝) (f✝ i✝)
  apply n_ih
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.agree'_refl PFunctor.M.agree'_refl

theorem agree_iff_agree' {n : ℕ} (x y : M F) :
    Agree (x.approx n) (y.approx <| n + 1) ↔ Agree' n x y := by
  constructor <;> intro h
  -- ⊢ Agree (MIntl.approx x n) (MIntl.approx y (n + 1)) → Agree' n x y
                  -- ⊢ Agree' n x y
                  -- ⊢ Agree (MIntl.approx x n) (MIntl.approx y (n + 1))
  · induction' n with _ n_ih generalizing x y
    -- ⊢ Agree' zero x y
    constructor
    -- ⊢ Agree' (succ n✝) x y
    · induction x using PFunctor.M.casesOn'
      -- ⊢ Agree' (succ n✝) (M.mk { fst := a✝, snd := f✝ }) y
      induction y using PFunctor.M.casesOn'
      -- ⊢ Agree' (succ n✝) (M.mk { fst := a✝¹, snd := f✝¹ }) (M.mk { fst := a✝, snd := …
      simp only [approx_mk] at h
      -- ⊢ Agree' (succ n✝) (M.mk { fst := a✝¹, snd := f✝¹ }) (M.mk { fst := a✝, snd := …
      cases' h with _ _ _ _ _ _ hagree
      -- ⊢ Agree' (succ n✝) (M.mk { fst := a✝, snd := f✝¹ }) (M.mk { fst := a✝, snd :=  …
      constructor <;> try rfl
                      -- 🎉 no goals
                      -- 🎉 no goals
                      -- ⊢ ∀ (i : B F a✝), Agree' n✝ (f✝¹ i) (f✝ i)
      intro i
      -- ⊢ Agree' n✝ (f✝¹ i) (f✝ i)
      apply n_ih
      -- ⊢ Agree (MIntl.approx (f✝¹ i) n✝) (MIntl.approx (f✝ i) (n✝ + 1))
      apply hagree
      -- 🎉 no goals
  · induction' n with _ n_ih generalizing x y
    -- ⊢ Agree (MIntl.approx x zero) (MIntl.approx y (zero + 1))
    constructor
    -- ⊢ Agree (MIntl.approx x (succ n✝)) (MIntl.approx y (succ n✝ + 1))
    · cases' h with _ _ _ a x' y'
      -- ⊢ Agree (MIntl.approx x (succ n✝)) (MIntl.approx y (succ n✝ + 1))
      induction' x using PFunctor.M.casesOn' with x_a x_f
      -- ⊢ Agree (MIntl.approx (M.mk { fst := x_a, snd := x_f }) (succ n✝)) (MIntl.appr …
      induction' y using PFunctor.M.casesOn' with y_a y_f
      -- ⊢ Agree (MIntl.approx (M.mk { fst := x_a, snd := x_f }) (succ n✝)) (MIntl.appr …
      simp only [approx_mk]
      -- ⊢ Agree (CofixA.intro x_a fun j => MIntl.approx (x_f j) n✝) (CofixA.intro y_a  …
      have h_a_1 := mk_inj ‹M.mk ⟨x_a, x_f⟩ = M.mk ⟨a, x'⟩›
      -- ⊢ Agree (CofixA.intro x_a fun j => MIntl.approx (x_f j) n✝) (CofixA.intro y_a  …
      cases h_a_1
      -- ⊢ Agree (CofixA.intro a fun j => MIntl.approx (x' j) n✝) (CofixA.intro y_a fun …
      replace h_a_2 := mk_inj ‹M.mk ⟨y_a, y_f⟩ = M.mk ⟨a, y'⟩›
      -- ⊢ Agree (CofixA.intro a fun j => MIntl.approx (x' j) n✝) (CofixA.intro y_a fun …
      cases h_a_2
      -- ⊢ Agree (CofixA.intro a fun j => MIntl.approx (x' j) n✝) (CofixA.intro a fun j …
      constructor
      -- ⊢ ∀ (i : B F a), Agree (MIntl.approx (x' i) n✝) (MIntl.approx (y' i) (n✝ + 1))
      intro i
      -- ⊢ Agree (MIntl.approx (x' i) n✝) (MIntl.approx (y' i) (n✝ + 1))
      apply n_ih
      -- ⊢ Agree' n✝ (x' i) (y' i)
      simp [*]
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.agree_iff_agree' PFunctor.M.agree_iff_agree'

@[simp]
theorem cases_mk {r : M F → Sort*} (x : F.Obj <| M F) (f : ∀ x : F.Obj <| M F, r (M.mk x)) :
    PFunctor.M.cases f (M.mk x) = f x := by
  dsimp only [M.mk, PFunctor.M.cases, dest, head, Approx.sMk, head']
  -- ⊢ Eq.mpr
  cases x; dsimp only [Approx.sMk]
  -- ⊢ Eq.mpr
           -- ⊢ Eq.mpr
  simp only [Eq.mpr]
  -- ⊢ f
  apply congrFun
  -- ⊢ f = f
  rfl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.cases_mk PFunctor.M.cases_mk

@[simp]
theorem casesOn_mk {r : M F → Sort*} (x : F.Obj <| M F) (f : ∀ x : F.Obj <| M F, r (M.mk x)) :
    PFunctor.M.casesOn (M.mk x) f = f x :=
  cases_mk x f
set_option linter.uppercaseLean3 false in
#align pfunctor.M.cases_on_mk PFunctor.M.casesOn_mk

@[simp]
theorem casesOn_mk' {r : M F → Sort*} {a} (x : F.B a → M F)
                    (f : ∀ (a) (f : F.B a → M F), r (M.mk ⟨a, f⟩)) :
    PFunctor.M.casesOn' (M.mk ⟨a, x⟩) f = f a x :=
  @cases_mk F r ⟨a, x⟩ (fun ⟨a, g⟩ => f a g)
set_option linter.uppercaseLean3 false in
#align pfunctor.M.cases_on_mk' PFunctor.M.casesOn_mk'

/-- `IsPath p x` tells us if `p` is a valid path through `x` -/
inductive IsPath : Path F → M F → Prop
  | nil (x : M F) : IsPath [] x
  |
  cons (xs : Path F) {a} (x : M F) (f : F.B a → M F) (i : F.B a) :
    x = M.mk ⟨a, f⟩ → IsPath xs (f i) → IsPath (⟨a, i⟩ :: xs) x
set_option linter.uppercaseLean3 false in
#align pfunctor.M.is_path PFunctor.M.IsPath

theorem isPath_cons {xs : Path F} {a a'} {f : F.B a → M F} {i : F.B a'} :
    IsPath (⟨a', i⟩ :: xs) (M.mk ⟨a, f⟩) → a = a' := by
  generalize h : M.mk ⟨a, f⟩ = x
  -- ⊢ IsPath ({ fst := a', snd := i } :: xs) x → a = a'
  rintro (_ | ⟨_, _, _, _, rfl, _⟩)
  -- ⊢ a = a'
  cases mk_inj h
  -- ⊢ a = a
  rfl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.is_path_cons PFunctor.M.isPath_cons

theorem isPath_cons' {xs : Path F} {a} {f : F.B a → M F} {i : F.B a} :
    IsPath (⟨a, i⟩ :: xs) (M.mk ⟨a, f⟩) → IsPath xs (f i) := by
  generalize h : M.mk ⟨a, f⟩ = x
  -- ⊢ IsPath ({ fst := a, snd := i } :: xs) x → IsPath xs (f i)
  rintro (_ | ⟨_, _, _, _, rfl, hp⟩)
  -- ⊢ IsPath xs (f i)
  cases mk_inj h
  -- ⊢ IsPath xs (f i)
  exact hp
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.is_path_cons' PFunctor.M.isPath_cons'

/-- follow a path through a value of `M F` and return the subtree
found at the end of the path if it is a valid path for that value and
return a default tree -/
def isubtree [DecidableEq F.A] [Inhabited (M F)] : Path F → M F → M F
  | [], x => x
  | ⟨a, i⟩ :: ps, x =>
    PFunctor.M.casesOn' (r := fun _ => M F) x (fun a' f =>
      if h : a = a' then
        isubtree ps (f <| cast (by rw [h]) i)
                                   -- 🎉 no goals
      else
        default (α := M F)
    )

set_option linter.uppercaseLean3 false in
#align pfunctor.M.isubtree PFunctor.M.isubtree

/-- similar to `isubtree` but returns the data at the end of the path instead
of the whole subtree -/
def iselect [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) : M F → F.A := fun x : M F =>
  head <| isubtree ps x
set_option linter.uppercaseLean3 false in
#align pfunctor.M.iselect PFunctor.M.iselect

theorem iselect_eq_default [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) (x : M F)
    (h : ¬IsPath ps x) : iselect ps x = head default := by
  induction' ps with ps_hd ps_tail ps_ih generalizing x
  -- ⊢ iselect [] x = head default
  · exfalso
    -- ⊢ False
    apply h
    -- ⊢ IsPath [] x
    constructor
    -- 🎉 no goals
  · cases' ps_hd with a i
    -- ⊢ iselect ({ fst := a, snd := i } :: ps_tail) x = head default
    induction' x using PFunctor.M.casesOn' with x_a x_f
    -- ⊢ iselect ({ fst := a, snd := i } :: ps_tail) (M.mk { fst := x_a, snd := x_f } …
    simp only [iselect, isubtree] at ps_ih ⊢
    -- ⊢ head (M.casesOn' (M.mk { fst := x_a, snd := x_f }) fun a' f => if h : a = a' …
    by_cases h'' : a = x_a
    -- ⊢ head (M.casesOn' (M.mk { fst := x_a, snd := x_f }) fun a' f => if h : a = a' …
    subst x_a
    -- ⊢ head (M.casesOn' (M.mk { fst := a, snd := x_f }) fun a' f => if h : a = a' t …
    · simp only [dif_pos, eq_self_iff_true, casesOn_mk']
      -- ⊢ head (isubtree ps_tail (x_f (cast (_ : B F a = B F a) i))) = head default
      rw [ps_ih]
      -- ⊢ ¬IsPath ps_tail (x_f (cast (_ : B F a = B F a) i))
      intro h'
      -- ⊢ False
      apply h
      -- ⊢ IsPath ({ fst := a, snd := i } :: ps_tail) (M.mk { fst := a, snd := x_f })
      constructor <;> try rfl
                      -- 🎉 no goals
                      -- ⊢ IsPath ps_tail (x_f i)
      apply h'
      -- 🎉 no goals
    · simp [*]
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.iselect_eq_default PFunctor.M.iselect_eq_default

@[simp]
theorem head_mk (x : F.Obj (M F)) : head (M.mk x) = x.1 :=
  Eq.symm <|
    calc
      x.1 = (dest (M.mk x)).1 := by rw [dest_mk]
                                    -- 🎉 no goals
      _ = head (M.mk x) := by rfl
                              -- 🎉 no goals

set_option linter.uppercaseLean3 false in
#align pfunctor.M.head_mk PFunctor.M.head_mk

theorem children_mk {a} (x : F.B a → M F) (i : F.B (head (M.mk ⟨a, x⟩))) :
    children (M.mk ⟨a, x⟩) i = x (cast (by rw [head_mk]) i) := by apply ext'; intro n; rfl
                                           -- 🎉 no goals
                                                                  -- ⊢ ∀ (i_1 : ℕ), MIntl.approx (children (M.mk { fst := a, snd := x }) i) i_1 = M …
                                                                              -- ⊢ MIntl.approx (children (M.mk { fst := a, snd := x }) i) n = MIntl.approx (x  …
                                                                                       -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.children_mk PFunctor.M.children_mk

@[simp]
theorem ichildren_mk [DecidableEq F.A] [Inhabited (M F)] (x : F.Obj (M F)) (i : F.IdxCat) :
    ichildren i (M.mk x) = x.iget i := by
  dsimp only [ichildren, PFunctor.Obj.iget]
  -- ⊢ (if H' : i.fst = head (M.mk x) then children (M.mk x) (cast (_ : B F i.fst = …
  congr with h
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.ichildren_mk PFunctor.M.ichildren_mk

@[simp]
theorem isubtree_cons [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) {a} (f : F.B a → M F)
    {i : F.B a} : isubtree (⟨_, i⟩ :: ps) (M.mk ⟨a, f⟩) = isubtree ps (f i) := by
  simp only [isubtree, ichildren_mk, PFunctor.Obj.iget, dif_pos, isubtree, M.casesOn_mk']; rfl
  -- ⊢ isubtree ps (f (cast (_ : B F a = B F a) i)) = isubtree ps (f i)
                                                                                           -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.isubtree_cons PFunctor.M.isubtree_cons

@[simp]
theorem iselect_nil [DecidableEq F.A] [Inhabited (M F)] {a} (f : F.B a → M F) :
    iselect nil (M.mk ⟨a, f⟩) = a := by rfl
                                        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.iselect_nil PFunctor.M.iselect_nil

@[simp]
theorem iselect_cons [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) {a} (f : F.B a → M F) {i} :
    iselect (⟨a, i⟩ :: ps) (M.mk ⟨a, f⟩) = iselect ps (f i) := by simp only [iselect, isubtree_cons]
                                                                  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.iselect_cons PFunctor.M.iselect_cons

theorem corec_def {X} (f : X → F.Obj X) (x₀ : X) : M.corec f x₀ = M.mk (M.corec f <$> f x₀) := by
  dsimp only [M.corec, M.mk]
  -- ⊢ { approx := sCorec f x₀, consistent := (_ : ∀ (n : ℕ), Agree (sCorec f x₀ n) …
  congr with n
  -- ⊢ sCorec f x₀ n = Approx.sMk ((fun i => { approx := sCorec f i, consistent :=  …
  cases' n with n
  -- ⊢ sCorec f x₀ zero = Approx.sMk ((fun i => { approx := sCorec f i, consistent  …
  · dsimp only [sCorec, Approx.sMk]
    -- 🎉 no goals
  · dsimp only [sCorec, Approx.sMk]
    -- ⊢ (CofixA.intro (f x₀).fst fun i => sCorec f (Sigma.snd (f x₀) i) n) = CofixA. …
    cases h : f x₀
    -- ⊢ (CofixA.intro { fst := fst✝, snd := snd✝ }.fst fun i => sCorec f (Sigma.snd  …
    dsimp only [(· <$> ·), PFunctor.map]
    -- ⊢ (CofixA.intro fst✝ fun i => sCorec f (snd✝ i) n) = CofixA.intro fst✝ fun i = …
    congr
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.corec_def PFunctor.M.corec_def

theorem ext_aux [Inhabited (M F)] [DecidableEq F.A] {n : ℕ} (x y z : M F) (hx : Agree' n z x)
    (hy : Agree' n z y) (hrec : ∀ ps : Path F, n = ps.length → iselect ps x = iselect ps y) :
    x.approx (n + 1) = y.approx (n + 1) := by
  induction' n with n n_ih generalizing x y z
  -- ⊢ MIntl.approx x (zero + 1) = MIntl.approx y (zero + 1)
  · specialize hrec [] rfl
    -- ⊢ MIntl.approx x (zero + 1) = MIntl.approx y (zero + 1)
    induction x using PFunctor.M.casesOn'
    -- ⊢ MIntl.approx (M.mk { fst := a✝, snd := f✝ }) (zero + 1) = MIntl.approx y (ze …
    induction y using PFunctor.M.casesOn'
    -- ⊢ MIntl.approx (M.mk { fst := a✝¹, snd := f✝¹ }) (zero + 1) = MIntl.approx (M. …
    simp only [iselect_nil] at hrec
    -- ⊢ MIntl.approx (M.mk { fst := a✝¹, snd := f✝¹ }) (zero + 1) = MIntl.approx (M. …
    subst hrec
    -- ⊢ MIntl.approx (M.mk { fst := a✝, snd := f✝¹ }) (zero + 1) = MIntl.approx (M.m …
    simp only [approx_mk, true_and_iff, eq_self_iff_true, heq_iff_eq, zero_eq, CofixA.intro.injEq,
                heq_eq_eq, eq_iff_true_of_subsingleton, and_self]
  · cases hx
    -- ⊢ MIntl.approx x (succ n + 1) = MIntl.approx y (succ n + 1)
    cases hy
    -- ⊢ MIntl.approx x (succ n + 1) = MIntl.approx y (succ n + 1)
    induction x using PFunctor.M.casesOn'
    -- ⊢ MIntl.approx (M.mk { fst := a✝¹, snd := f✝ }) (succ n + 1) = MIntl.approx y  …
    induction y using PFunctor.M.casesOn'
    -- ⊢ MIntl.approx (M.mk { fst := a✝³, snd := f✝¹ }) (succ n + 1) = MIntl.approx ( …
    subst z
    -- ⊢ MIntl.approx (M.mk { fst := a✝⁴, snd := f✝¹ }) (succ n + 1) = MIntl.approx ( …
    iterate 3 (have := mk_inj ‹_›; cases this)
    -- ⊢ MIntl.approx (M.mk { fst := a✝⁵, snd := f✝¹ }) (succ n + 1) = MIntl.approx ( …
    rename_i n_ih a f₃ f₂ hAgree₂ _ _ h₂ _ _ f₁ h₁ hAgree₁ clr
    -- ⊢ MIntl.approx (M.mk { fst := a✝¹, snd := f✝¹ }) (succ n + 1) = MIntl.approx ( …
    simp only [approx_mk, true_and_iff, eq_self_iff_true, heq_iff_eq]
    -- ⊢ (CofixA.intro a✝¹ fun j => MIntl.approx (f✝¹ j) (n + 1)) = CofixA.intro a✝ f …

    have := mk_inj h₁
    -- ⊢ (CofixA.intro a✝¹ fun j => MIntl.approx (f✝¹ j) (n + 1)) = CofixA.intro a✝ f …
    cases this; clear h₁
    -- ⊢ (CofixA.intro a✝ fun j => MIntl.approx (f✝ j) (n + 1)) = CofixA.intro a fun  …
                -- ⊢ (CofixA.intro a✝ fun j => MIntl.approx (f✝ j) (n + 1)) = CofixA.intro a fun  …
    have := mk_inj h₂
    -- ⊢ (CofixA.intro a✝ fun j => MIntl.approx (f✝ j) (n + 1)) = CofixA.intro a fun  …
    cases this; clear h₂
    -- ⊢ (CofixA.intro a fun j => MIntl.approx (f₂ j) (n + 1)) = CofixA.intro a fun j …
                -- ⊢ (CofixA.intro a fun j => MIntl.approx (f₂ j) (n + 1)) = CofixA.intro a fun j …

    congr
    -- ⊢ (fun j => MIntl.approx (f₂ j) (n + 1)) = fun j => MIntl.approx (f₁ j) (n + 1)
    ext i
    -- ⊢ MIntl.approx (f₂ i) (n + 1) = MIntl.approx (f₁ i) (n + 1)
    apply n_ih
    · solve_by_elim
      -- 🎉 no goals
    · solve_by_elim
      -- 🎉 no goals
    introv h
    -- ⊢ iselect ps (f₂ i) = iselect ps (f₁ i)
    specialize hrec (⟨_, i⟩ :: ps) (congr_arg _ h)
    -- ⊢ iselect ps (f₂ i) = iselect ps (f₁ i)
    simp only [iselect_cons] at hrec
    -- ⊢ iselect ps (f₂ i) = iselect ps (f₁ i)
    exact hrec
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.ext_aux PFunctor.M.ext_aux

open PFunctor.Approx

attribute [local instance] Classical.propDecidable

theorem ext [Inhabited (M F)] (x y : M F) (H : ∀ ps : Path F, iselect ps x = iselect ps y) :
    x = y := by
  apply ext'; intro i
  -- ⊢ ∀ (i : ℕ), MIntl.approx x i = MIntl.approx y i
              -- ⊢ MIntl.approx x i = MIntl.approx y i
  induction' i with i i_ih
  -- ⊢ MIntl.approx x zero = MIntl.approx y zero
  · cases x.approx 0
    -- ⊢ CofixA.continue = MIntl.approx y zero
    cases y.approx 0
    -- ⊢ CofixA.continue = CofixA.continue
    constructor
    -- 🎉 no goals
  · apply ext_aux x y x
    · rw [← agree_iff_agree']
      -- ⊢ Agree (MIntl.approx x i) (MIntl.approx x (i + 1))
      apply x.consistent
      -- 🎉 no goals
    · rw [← agree_iff_agree', i_ih]
      -- ⊢ Agree (MIntl.approx y i) (MIntl.approx y (i + 1))
      apply y.consistent
      -- 🎉 no goals
    introv H'
    -- ⊢ iselect ps x = iselect ps y
    dsimp only [iselect] at H
    -- ⊢ iselect ps x = iselect ps y
    cases H'
    -- ⊢ iselect ps x = iselect ps y
    apply H ps
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.ext PFunctor.M.ext

section Bisim

variable (R : M F → M F → Prop)

local infixl:50 " ~ " => R

/-- Bisimulation is the standard proof technique for equality between
infinite tree-like structures -/
structure IsBisimulation : Prop where
  /-- The head of the trees are equal -/
  head : ∀ {a a'} {f f'}, M.mk ⟨a, f⟩ ~ M.mk ⟨a', f'⟩ → a = a'
  /-- The tails are equal -/
  tail : ∀ {a} {f f' : F.B a → M F}, M.mk ⟨a, f⟩ ~ M.mk ⟨a, f'⟩ → ∀ i : F.B a, f i ~ f' i
set_option linter.uppercaseLean3 false in
#align pfunctor.M.is_bisimulation PFunctor.M.IsBisimulation

theorem nth_of_bisim [Inhabited (M F)] (bisim : IsBisimulation R) (s₁ s₂) (ps : Path F) :
    (R s₁ s₂) →
      IsPath ps s₁ ∨ IsPath ps s₂ →
        iselect ps s₁ = iselect ps s₂ ∧
          ∃ (a : _) (f f' : F.B a → M F),
            isubtree ps s₁ = M.mk ⟨a, f⟩ ∧
              isubtree ps s₂ = M.mk ⟨a, f'⟩ ∧ ∀ i : F.B a, f i ~ f' i := by
  intro h₀ hh
  -- ⊢ iselect ps s₁ = iselect ps s₂ ∧ ∃ a f f', isubtree ps s₁ = M.mk { fst := a,  …
  induction' s₁ using PFunctor.M.casesOn' with a f
  -- ⊢ iselect ps (M.mk { fst := a, snd := f }) = iselect ps s₂ ∧ ∃ a_1 f_1 f', isu …
  rename_i h₁ hh₁
  -- ⊢ iselect ps (M.mk { fst := a, snd := f }) = iselect ps s₂ ∧ ∃ a_1 f_1 f', isu …
  induction' s₂ using PFunctor.M.casesOn' with a' f'
  -- ⊢ iselect ps (M.mk { fst := a, snd := f }) = iselect ps (M.mk { fst := a', snd …
  rename_i h₁' hh₁' h₂ hh₂
  -- ⊢ iselect ps (M.mk { fst := a, snd := f }) = iselect ps (M.mk { fst := a', snd …
  clear h₁ hh₁ h₂ hh₂ hh₁'
  -- ⊢ iselect ps (M.mk { fst := a, snd := f }) = iselect ps (M.mk { fst := a', snd …
  obtain rfl : a = a' := bisim.head h₀
  -- ⊢ iselect ps (M.mk { fst := a, snd := f }) = iselect ps (M.mk { fst := a, snd  …
  induction' ps with i ps ps_ih generalizing a f f'
  -- ⊢ iselect [] (M.mk { fst := a, snd := f }) = iselect [] (M.mk { fst := a, snd  …
  · exists rfl, a, f, f', rfl, rfl
    -- ⊢ ∀ (i : B F a), R (f i) (f' i)
    apply bisim.tail h₀
    -- 🎉 no goals
  cases' i with a' i
  -- ⊢ iselect ({ fst := a', snd := i } :: ps) (M.mk { fst := a, snd := f }) = isel …
  obtain rfl : a = a' := by rcases hh with hh|hh <;> cases isPath_cons hh <;> rfl
  -- ⊢ iselect ({ fst := a, snd := i } :: ps) (M.mk { fst := a, snd := f }) = isele …
  dsimp only [iselect] at ps_ih ⊢
  -- ⊢ head (isubtree ({ fst := a, snd := i } :: ps) (M.mk { fst := a, snd := f })) …
  have h₁ := bisim.tail h₀ i
  -- ⊢ head (isubtree ({ fst := a, snd := i } :: ps) (M.mk { fst := a, snd := f })) …
  induction' h : f i using PFunctor.M.casesOn' with a₀ f₀
  -- ⊢ head (isubtree ({ fst := a, snd := i } :: ps) (M.mk { fst := a, snd := f })) …
  induction' h' : f' i using PFunctor.M.casesOn' with a₁ f₁
  -- ⊢ head (isubtree ({ fst := a, snd := i } :: ps) (M.mk { fst := a, snd := f })) …
  simp only [h, h', isubtree_cons] at ps_ih ⊢
  -- ⊢ head (isubtree ps (M.mk { fst := a₀, snd := f₀ })) = head (isubtree ps (M.mk …
  rw [h, h'] at h₁
  -- ⊢ head (isubtree ps (M.mk { fst := a₀, snd := f₀ })) = head (isubtree ps (M.mk …
  obtain rfl : a₀ = a₁ := bisim.head h₁
  -- ⊢ head (isubtree ps (M.mk { fst := a₀, snd := f₀ })) = head (isubtree ps (M.mk …
  apply ps_ih _ _ _ h₁
  -- ⊢ IsPath ps (M.mk { fst := a₀, snd := f₀ }) ∨ IsPath ps (M.mk { fst := a₀, snd …
  rw [← h, ← h']
  -- ⊢ IsPath ps (f i) ∨ IsPath ps (f' i)
  apply Or.imp isPath_cons' isPath_cons' hh
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.nth_of_bisim PFunctor.M.nth_of_bisim

theorem eq_of_bisim [Nonempty (M F)] (bisim : IsBisimulation R) : ∀ s₁ s₂, R s₁ s₂ → s₁ = s₂ := by
  inhabit M F
  -- ⊢ ∀ (s₁ s₂ : M F), R s₁ s₂ → s₁ = s₂
  introv Hr; apply ext
  -- ⊢ s₁ = s₂
             -- ⊢ ∀ (ps : Path F), iselect ps s₁ = iselect ps s₂
  introv
  -- ⊢ iselect ps s₁ = iselect ps s₂
  by_cases h : IsPath ps s₁ ∨ IsPath ps s₂
  -- ⊢ iselect ps s₁ = iselect ps s₂
  · have H := nth_of_bisim R bisim _ _ ps Hr h
    -- ⊢ iselect ps s₁ = iselect ps s₂
    exact H.left
    -- 🎉 no goals
  · rw [not_or] at h
    -- ⊢ iselect ps s₁ = iselect ps s₂
    cases' h with h₀ h₁
    -- ⊢ iselect ps s₁ = iselect ps s₂
    simp only [iselect_eq_default, *, not_false_iff]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.eq_of_bisim PFunctor.M.eq_of_bisim

end Bisim

universe u' v'

/-- corecursor for `M F` with swapped arguments -/
def corecOn {X : Type*} (x₀ : X) (f : X → F.Obj X) : M F :=
  M.corec f x₀
set_option linter.uppercaseLean3 false in
#align pfunctor.M.corec_on PFunctor.M.corecOn

variable {P : PFunctor.{u}} {α : Type u}

theorem dest_corec (g : α → P.Obj α) (x : α) : M.dest (M.corec g x) = M.corec g <$> g x := by
  rw [corec_def, dest_mk]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.dest_corec PFunctor.M.dest_corec

theorem bisim (R : M P → M P → Prop)
    (h : ∀ x y, R x y → ∃ a f f', M.dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ ∀ i, R (f i) (f' i)) :
    ∀ x y, R x y → x = y := by
  introv h'
  -- ⊢ x = y
  haveI := Inhabited.mk x.head
  -- ⊢ x = y
  apply eq_of_bisim R _ _ _ h'; clear h' x y
  -- ⊢ IsBisimulation R
                                -- ⊢ IsBisimulation R
  constructor <;> introv ih <;> rcases h _ _ ih with ⟨a'', g, g', h₀, h₁, h₂⟩ <;> clear h
  -- ⊢ ∀ {a a' : P.A} {f : B P a → M P} {f' : B P a' → M P}, R (M.mk { fst := a, sn …
                  -- ⊢ a = a'
                  -- ⊢ R (f i) (f' i)
                                -- ⊢ a = a'
                                -- ⊢ R (f i) (f' i)
                                                                                  -- ⊢ a = a'
                                                                                  -- ⊢ R (f i) (f' i)
  · replace h₀ := congr_arg Sigma.fst h₀
    -- ⊢ a = a'
    replace h₁ := congr_arg Sigma.fst h₁
    -- ⊢ a = a'
    simp only [dest_mk] at h₀ h₁
    -- ⊢ a = a'
    rw [h₀, h₁]
    -- 🎉 no goals
  · simp only [dest_mk] at h₀ h₁
    -- ⊢ R (f i) (f' i)
    cases h₀
    -- ⊢ R (f i) (f' i)
    cases h₁
    -- ⊢ R (f i) (f' i)
    apply h₂
    -- 🎉 no goals
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
    (h : ∀ x y, R x y → ∃ a f f', M.dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ ∀ i, R (f i) (f' i)) :
    ∀ x y, R x y → x = y := fun x y Rxy =>
  let Q : M P × M P → Prop := fun p => R p.fst p.snd
  bisim' Q Prod.fst Prod.snd
    (fun p Qp =>
      let ⟨a, f, f', hx, hy, h'⟩ := h p.fst p.snd Qp
      ⟨a, f, f', hx, hy, fun i => ⟨⟨f i, f' i⟩, h' i, rfl, rfl⟩⟩)
    ⟨x, y⟩ Rxy
set_option linter.uppercaseLean3 false in
#align pfunctor.M.bisim_equiv PFunctor.M.bisim_equiv

theorem corec_unique (g : α → P.Obj α) (f : α → M P) (hyp : ∀ x, M.dest (f x) = f <$> g x) :
    f = M.corec g := by
  ext x
  -- ⊢ f x = M.corec g x
  apply bisim' (fun _ => True) _ _ _ _ trivial
  -- ⊢ ∀ (x : α), (fun x => True) x → ∃ a f_1 f', dest (f x) = { fst := a, snd := f …
  clear x
  -- ⊢ ∀ (x : α), (fun x => True) x → ∃ a f_1 f', dest (f x) = { fst := a, snd := f …
  intro x _
  -- ⊢ ∃ a f_1 f', dest (f x) = { fst := a, snd := f_1 } ∧ dest (M.corec g x) = { f …
  cases' gxeq : g x with a f'
  -- ⊢ ∃ a f_1 f', dest (f x) = { fst := a, snd := f_1 } ∧ dest (M.corec g x) = { f …
  have h₀ : M.dest (f x) = ⟨a, f ∘ f'⟩ := by rw [hyp, gxeq, PFunctor.map_eq]
  -- ⊢ ∃ a f_1 f', dest (f x) = { fst := a, snd := f_1 } ∧ dest (M.corec g x) = { f …
  have h₁ : M.dest (M.corec g x) = ⟨a, M.corec g ∘ f'⟩ := by rw [dest_corec, gxeq, PFunctor.map_eq]
  -- ⊢ ∃ a f_1 f', dest (f x) = { fst := a, snd := f_1 } ∧ dest (M.corec g x) = { f …
  refine' ⟨_, _, _, h₀, h₁, _⟩
  -- ⊢ ∀ (i : B P a), ∃ x', (fun x => True) x' ∧ (f ∘ f') i = f x' ∧ (M.corec g ∘ f …
  intro i
  -- ⊢ ∃ x', (fun x => True) x' ∧ (f ∘ f') i = f x' ∧ (M.corec g ∘ f') i = M.corec  …
  exact ⟨f' i, trivial, rfl, rfl⟩
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align pfunctor.M.corec_unique PFunctor.M.corec_unique

/-- corecursor where the state of the computation can be sent downstream
in the form of a recursive call -/
def corec₁ {α : Type u} (F : ∀ X, (α → X) → α → P.Obj X) : α → M P :=
  M.corec (F _ id)
set_option linter.uppercaseLean3 false in
#align pfunctor.M.corec₁ PFunctor.M.corec₁

/-- corecursor where it is possible to return a fully formed value at any point
of the computation -/
def corec' {α : Type u} (F : ∀ {X : Type u}, (α → X) → α → Sum (M P) (P.Obj X)) (x : α) : M P :=
  corec₁
    (fun _ rec (a : Sum (M P) α) =>
      let y := a >>= F (rec ∘ Sum.inr)
      match y with
      | Sum.inr y => y
      | Sum.inl y => (rec ∘ Sum.inl) <$> M.dest y)
    (@Sum.inr (M P) _ x)
set_option linter.uppercaseLean3 false in
#align pfunctor.M.corec' PFunctor.M.corec'

end M

end PFunctor
