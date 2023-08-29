/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
import Mathlib.Data.PFunctor.Multivariate.Basic

#align_import data.pfunctor.multivariate.W from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# The W construction as a multivariate polynomial functor.

W types are well-founded tree-like structures. They are defined
as the least fixpoint of a polynomial functor.

## Main definitions

 * `W_mk`     - constructor
 * `W_dest    - destructor
 * `W_rec`    - recursor: basis for defining functions by structural recursion on `P.W α`
 * `W_rec_eq` - defining equation for `W_rec`
 * `W_ind`    - induction principle for `P.W α`

## Implementation notes

Three views of M-types:

 * `wp`: polynomial functor
 * `W`: data type inductively defined by a triple:
     shape of the root, data in the root and children of the root
 * `W`: least fixed point of a polynomial functor

Specifically, we define the polynomial functor `wp` as:

 * A := a tree-like structure without information in the nodes
 * B := given the tree-like structure `t`, `B t` is a valid path
   (specified inductively by `W_path`) from the root of `t` to any given node.

As a result `wp.Obj α` is made of a dataless tree and a function from
its valid paths to values of `α`

## Reference

 * Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
   [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/


universe u v

namespace MvPFunctor

open TypeVec

open MvFunctor

variable {n : ℕ} (P : MvPFunctor.{u} (n + 1))

/-- A path from the root of a tree to one of its node -/
inductive WPath : P.last.W → Fin2 n → Type u
  | root (a : P.A) (f : P.last.B a → P.last.W) (i : Fin2 n) (c : P.drop.B a i) : WPath ⟨a, f⟩ i
  | child (a : P.A) (f : P.last.B a → P.last.W) (i : Fin2 n) (j : P.last.B a)
    (c : WPath (f j) i) : WPath ⟨a, f⟩ i
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_path MvPFunctor.WPath

instance WPath.inhabited (x : P.last.W) {i} [I : Inhabited (P.drop.B x.head i)] :
    Inhabited (WPath P x i) :=
  ⟨match x, I with
    | ⟨a, f⟩, I => WPath.root a f i (@default _ I)⟩
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_path.inhabited MvPFunctor.WPath.inhabited

/-- Specialized destructor on `WPath` -/
def wPathCasesOn {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W} (g' : P.drop.B a ⟹ α)
    (g : ∀ j : P.last.B a, P.WPath (f j) ⟹ α) : P.WPath ⟨a, f⟩ ⟹ α := by
  intro i x;
  -- ⊢ α i
  match x with
  | WPath.root _ _ i c => exact g' i c
  | WPath.child _ _ i j c => exact g j i c
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_path_cases_on MvPFunctor.wPathCasesOn

/-- Specialized destructor on `WPath` -/
def wPathDestLeft {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (h : P.WPath ⟨a, f⟩ ⟹ α) : P.drop.B a ⟹ α := fun i c => h i (WPath.root a f i c)
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_path_dest_left MvPFunctor.wPathDestLeft

/-- Specialized destructor on `WPath` -/
def wPathDestRight {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (h : P.WPath ⟨a, f⟩ ⟹ α) : ∀ j : P.last.B a, P.WPath (f j) ⟹ α := fun j i c =>
  h i (WPath.child a f i j c)
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_path_dest_right MvPFunctor.wPathDestRight

theorem wPathDestLeft_wPathCasesOn {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (g' : P.drop.B a ⟹ α) (g : ∀ j : P.last.B a, P.WPath (f j) ⟹ α) :
    P.wPathDestLeft (P.wPathCasesOn g' g) = g' := rfl
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_path_dest_left_W_path_cases_on MvPFunctor.wPathDestLeft_wPathCasesOn

theorem wPathDestRight_wPathCasesOn {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (g' : P.drop.B a ⟹ α) (g : ∀ j : P.last.B a, P.WPath (f j) ⟹ α) :
    P.wPathDestRight (P.wPathCasesOn g' g) = g := rfl
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_path_dest_right_W_path_cases_on MvPFunctor.wPathDestRight_wPathCasesOn

theorem wPathCasesOn_eta {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (h : P.WPath ⟨a, f⟩ ⟹ α) : P.wPathCasesOn (P.wPathDestLeft h) (P.wPathDestRight h) = h := by
  ext i x; cases x <;> rfl
  -- ⊢ wPathCasesOn P (wPathDestLeft P h) (wPathDestRight P h) i x = h i x
           -- ⊢ wPathCasesOn P (wPathDestLeft P h) (wPathDestRight P h) i (WPath.root a (fun …
                       -- 🎉 no goals
                       -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_path_cases_on_eta MvPFunctor.wPathCasesOn_eta

theorem comp_wPathCasesOn {α β : TypeVec n} (h : α ⟹ β) {a : P.A} {f : P.last.B a → P.last.W}
    (g' : P.drop.B a ⟹ α) (g : ∀ j : P.last.B a, P.WPath (f j) ⟹ α) :
    h ⊚ P.wPathCasesOn g' g = P.wPathCasesOn (h ⊚ g') fun i => h ⊚ g i := by
  ext i x; cases x <;> rfl
  -- ⊢ (h ⊚ wPathCasesOn P g' g) i x = wPathCasesOn P (h ⊚ g') (fun i => h ⊚ g i) i x
           -- ⊢ (h ⊚ wPathCasesOn P g' g) i (WPath.root a (fun j => f j) i c✝) = wPathCasesO …
                       -- 🎉 no goals
                       -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mvpfunctor.comp_W_path_cases_on MvPFunctor.comp_wPathCasesOn

/-- Polynomial functor for the W-type of `P`. `A` is a data-less well-founded
tree whereas, for a given `a : A`, `B a` is a valid path in tree `a` so
that `Wp.obj α` is made of a tree and a function from its valid paths to
the values it contains  -/
def wp : MvPFunctor n where
  A := P.last.W
  B := P.WPath
set_option linter.uppercaseLean3 false in
#align mvpfunctor.Wp MvPFunctor.wp

/-- W-type of `P` -/
-- Porting note: used to have @[nolint has_nonempty_instance]
def W (α : TypeVec n) : Type _ :=
  P.wp.Obj α
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W MvPFunctor.W

instance mvfunctorW : MvFunctor P.W := by delta MvPFunctor.W; infer_instance
                                          -- ⊢ MvFunctor fun α => Obj (wp P) α
                                                              -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mvpfunctor.mvfunctor_W MvPFunctor.mvfunctorW

/-!
First, describe operations on `W` as a polynomial functor.
-/


/-- Constructor for `wp` -/
def wpMk {α : TypeVec n} (a : P.A) (f : P.last.B a → P.last.W) (f' : P.WPath ⟨a, f⟩ ⟹ α) :
    P.W α :=
  ⟨⟨a, f⟩, f'⟩
set_option linter.uppercaseLean3 false in
#align mvpfunctor.Wp_mk MvPFunctor.wpMk

def wpRec {α : TypeVec n} {C : Type*}
    (g : ∀ (a : P.A) (f : P.last.B a → P.last.W), P.WPath ⟨a, f⟩ ⟹ α → (P.last.B a → C) → C) :
    ∀ (x : P.last.W) (_ : P.WPath x ⟹ α), C
  | ⟨a, f⟩, f' => g a f f' fun i => wpRec g (f i) (P.wPathDestRight f' i)
set_option linter.uppercaseLean3 false in
#align mvpfunctor.Wp_rec MvPFunctor.wpRec

theorem wpRec_eq {α : TypeVec n} {C : Type*}
    (g : ∀ (a : P.A) (f : P.last.B a → P.last.W), P.WPath ⟨a, f⟩ ⟹ α → (P.last.B a → C) → C)
    (a : P.A) (f : P.last.B a → P.last.W) (f' : P.WPath ⟨a, f⟩ ⟹ α) :
    P.wpRec g ⟨a, f⟩ f' = g a f f' fun i => P.wpRec g (f i) (P.wPathDestRight f' i) := rfl
set_option linter.uppercaseLean3 false in
#align mvpfunctor.Wp_rec_eq MvPFunctor.wpRec_eq

-- Note: we could replace Prop by Type* and obtain a dependent recursor
theorem wp_ind {α : TypeVec n} {C : ∀ x : P.last.W, P.WPath x ⟹ α → Prop}
    (ih : ∀ (a : P.A) (f : P.last.B a → P.last.W) (f' : P.WPath ⟨a, f⟩ ⟹ α),
        (∀ i : P.last.B a, C (f i) (P.wPathDestRight f' i)) → C ⟨a, f⟩ f') :
    ∀ (x : P.last.W) (f' : P.WPath x ⟹ α), C x f'
  | ⟨a, f⟩, f' => ih a f f' fun _i => wp_ind ih _ _
set_option linter.uppercaseLean3 false in
#align mvpfunctor.Wp_ind MvPFunctor.wp_ind

/-!
Now think of W as defined inductively by the data ⟨a, f', f⟩ where
- `a  : P.A` is the shape of the top node
- `f' : P.drop.B a ⟹ α` is the contents of the top node
- `f  : P.last.B a → P.last.W` are the subtrees
 -/


/-- Constructor for `W` -/
def wMk {α : TypeVec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) : P.W α :=
  let g : P.last.B a → P.last.W := fun i => (f i).fst
  let g' : P.WPath ⟨a, g⟩ ⟹ α := P.wPathCasesOn f' fun i => (f i).snd
  ⟨⟨a, g⟩, g'⟩
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_mk MvPFunctor.wMk

/-- Recursor for `W` -/
def wRec {α : TypeVec n} {C : Type*}
    (g : ∀ a : P.A, P.drop.B a ⟹ α → (P.last.B a → P.W α) → (P.last.B a → C) → C) : P.W α → C
  | ⟨a, f'⟩ =>
    let g' (a : P.A) (f : P.last.B a → P.last.W) (h : P.WPath ⟨a, f⟩ ⟹ α)
      (h' : P.last.B a → C) : C :=
      g a (P.wPathDestLeft h) (fun i => ⟨f i, P.wPathDestRight h i⟩) h'
    P.wpRec g' a f'
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_rec MvPFunctor.wRec

/-- Defining equation for the recursor of `W` -/
theorem wRec_eq {α : TypeVec n} {C : Type*}
    (g : ∀ a : P.A, P.drop.B a ⟹ α → (P.last.B a → P.W α) → (P.last.B a → C) → C) (a : P.A)
    (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
    P.wRec g (P.wMk a f' f) = g a f' f fun i => P.wRec g (f i) := by
  rw [wMk, wRec]; dsimp; rw [wpRec_eq]
  -- ⊢ (match
                  -- ⊢ wpRec P (fun a f h h' => g a (wPathDestLeft P h) (fun i => { fst := f i, snd …
                         -- ⊢ (g a (wPathDestLeft P (wPathCasesOn P f' fun i => (f i).snd)) (fun i => { fs …
  dsimp only [wPathDestLeft_wPathCasesOn, wPathDestRight_wPathCasesOn]
  -- ⊢ (g a f' (fun i => { fst := (f i).fst, snd := (f i).snd }) fun i => wpRec P ( …
  congr
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_rec_eq MvPFunctor.wRec_eq

/-- Induction principle for `W` -/
theorem w_ind {α : TypeVec n} {C : P.W α → Prop}
    (ih : ∀ (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α),
        (∀ i, C (f i)) → C (P.wMk a f' f)) :
    ∀ x, C x := by
  intro x; cases' x with a f
  -- ⊢ C x
           -- ⊢ C { fst := a, snd := f }
  apply @wp_ind n P α fun a f => C ⟨a, f⟩
  -- ⊢ ∀ (a : P.A) (f : PFunctor.B (last P) a → PFunctor.W (last P)) (f' : WPath P  …
  intro a f f' ih'
  -- ⊢ C { fst := WType.mk a f, snd := f' }
  dsimp [wMk] at ih
  -- ⊢ C { fst := WType.mk a f, snd := f' }
  let ih'' := ih a (P.wPathDestLeft f') fun i => ⟨f i, P.wPathDestRight f' i⟩
  -- ⊢ C { fst := WType.mk a f, snd := f' }
  dsimp at ih''; rw [wPathCasesOn_eta] at ih''
  -- ⊢ C { fst := WType.mk a f, snd := f' }
                 -- ⊢ C { fst := WType.mk a f, snd := f' }
  apply ih''
  -- ⊢ ∀ (i : PFunctor.B (last P) a), C { fst := f i, snd := wPathDestRight P f' i }
  apply ih'
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_ind MvPFunctor.w_ind

theorem w_cases {α : TypeVec n} {C : P.W α → Prop}
    (ih : ∀ (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α), C (P.wMk a f' f)) :
    ∀ x, C x := P.w_ind fun a f' f _ih' => ih a f' f
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_cases MvPFunctor.w_cases

/-- W-types are functorial -/
def wMap {α β : TypeVec n} (g : α ⟹ β) : P.W α → P.W β := fun x => g <$$> x
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_map MvPFunctor.wMap

theorem wMk_eq {α : TypeVec n} (a : P.A) (f : P.last.B a → P.last.W) (g' : P.drop.B a ⟹ α)
    (g : ∀ j : P.last.B a, P.WPath (f j) ⟹ α) :
    (P.wMk a g' fun i => ⟨f i, g i⟩) = ⟨⟨a, f⟩, P.wPathCasesOn g' g⟩ := rfl
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_mk_eq MvPFunctor.wMk_eq

theorem w_map_wMk {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f' : P.drop.B a ⟹ α)
    (f : P.last.B a → P.W α) : g <$$> P.wMk a f' f = P.wMk a (g ⊚ f') fun i => g <$$> f i := by
  show _ = P.wMk a (g ⊚ f') (MvFunctor.map g ∘ f)
  -- ⊢ g <$$> wMk P a f' f = wMk P a (g ⊚ f') (MvFunctor.map g ∘ f)
  have : MvFunctor.map g ∘ f = fun i => ⟨(f i).fst, g ⊚ (f i).snd⟩ := by
    ext i : 1
    dsimp [Function.comp]
    cases f i
    rfl
  rw [this]
  -- ⊢ g <$$> wMk P a f' f = wMk P a (g ⊚ f') fun i => { fst := (f i).fst, snd := g …
  have : f = fun i => ⟨(f i).fst, (f i).snd⟩ := by
    ext1 x
    cases f x
    rfl
  rw [this]
  -- ⊢ (g <$$> wMk P a f' fun i => { fst := (f i).fst, snd := (f i).snd }) = wMk P  …
  dsimp
  -- ⊢ (g <$$> wMk P a f' fun i => { fst := (f i).fst, snd := (f i).snd }) = wMk P  …
  rw [wMk_eq, wMk_eq]
  -- ⊢ g <$$> { fst := WType.mk a fun i => (f i).fst, snd := wPathCasesOn P f' fun  …
  have h := MvPFunctor.map_eq P.wp g
  -- ⊢ g <$$> { fst := WType.mk a fun i => (f i).fst, snd := wPathCasesOn P f' fun  …
  rw [h, comp_wPathCasesOn]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_map_W_mk MvPFunctor.w_map_wMk

-- TODO: this technical theorem is used in one place in constructing the initial algebra.
-- Can it be avoided?
/-- Constructor of a value of `P.obj (α ::: β)` from components.
Useful to avoid complicated type annotation -/
@[reducible]
def objAppend1 {α : TypeVec n} {β : Type _} (a : P.A) (f' : P.drop.B a ⟹ α)
    (f : P.last.B a → β) : P.Obj (α ::: β) :=
  ⟨a, splitFun f' f⟩
#align mvpfunctor.obj_append1 MvPFunctor.objAppend1

theorem map_objAppend1 {α γ : TypeVec n} (g : α ⟹ γ) (a : P.A) (f' : P.drop.B a ⟹ α)
    (f : P.last.B a → P.W α) :
    appendFun g (P.wMap g) <$$> P.objAppend1 a f' f =
      P.objAppend1 a (g ⊚ f') fun x => P.wMap g (f x) :=
  by rw [objAppend1, objAppend1, map_eq, appendFun, ← splitFun_comp]; rfl
     -- ⊢ { fst := a, snd := splitFun (g ⊚ f') (wMap P g ∘ f) } = { fst := a, snd := s …
                                                                      -- 🎉 no goals
#align mvpfunctor.map_obj_append1 MvPFunctor.map_objAppend1

/-!
Yet another view of the W type: as a fixed point for a multivariate polynomial functor.
These are needed to use the W-construction to construct a fixed point of a qpf, since
the qpf axioms are expressed in terms of `map` on `P`.
-/


/-- Constructor for the W-type of `P` -/
def wMk' {α : TypeVec n} : P.Obj (α ::: P.W α) → P.W α
  | ⟨a, f⟩ => P.wMk a (dropFun f) (lastFun f)
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_mk' MvPFunctor.wMk'

/-- Destructor for the W-type of `P` -/
def wDest' {α : TypeVec.{u} n} : P.W α → P.Obj (α.append1 (P.W α)) :=
  P.wRec fun a f' f _ => ⟨a, splitFun f' f⟩
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_dest' MvPFunctor.wDest'

theorem wDest'_wMk {α : TypeVec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
    P.wDest' (P.wMk a f' f) = ⟨a, splitFun f' f⟩ := by rw [wDest', wRec_eq]
                                                       -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_dest'_W_mk MvPFunctor.wDest'_wMk

theorem wDest'_wMk' {α : TypeVec n} (x : P.Obj (α.append1 (P.W α))) : P.wDest' (P.wMk' x) = x := by
  cases' x with a f; rw [wMk', wDest'_wMk, split_dropFun_lastFun]
  -- ⊢ wDest' P (wMk' P { fst := a, snd := f }) = { fst := a, snd := f }
                     -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mvpfunctor.W_dest'_W_mk' MvPFunctor.wDest'_wMk'

end MvPFunctor
