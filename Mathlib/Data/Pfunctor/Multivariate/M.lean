/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon

! This file was ported from Lean 3 source module data.pfunctor.multivariate.M
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Pfunctor.Multivariate.Basic
import Mathbin.Data.Pfunctor.Univariate.M

/-!
# The M construction as a multivariate polynomial functor.

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.

## Main definitions

 * `M.mk`     - constructor
 * `M.dest`   - destructor
 * `M.corec`  - corecursor: useful for formulating infinite, productive computations
 * `M.bisim`  - bisimulation: proof technique to show the equality of infinite objects

## Implementation notes

Dual view of M-types:

 * `Mp`: polynomial functor
 * `M`: greatest fixed point of a polynomial functor

Specifically, we define the polynomial functor `Mp` as:

 * A := a possibly infinite tree-like structure without information in the nodes
 * B := given the tree-like structure `t`, `B t` is a valid path
   from the root of `t` to any given node.

As a result `Mp.obj α` is made of a dataless tree and a function from
its valid paths to values of `α`

The difference with the polynomial functor of an initial algebra is
that `A` is a possibly infinite tree.

## Reference

 * Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
   [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/


universe u

open MvFunctor

namespace MvPFunctor

open TypeVec

variable {n : ℕ} (P : MvPFunctor.{u} (n + 1))

/-- A path from the root of a tree to one of its node -/
inductive M.Path : P.getLast.M → Fin2 n → Type u
  |
  root (x : P.getLast.M) (a : P.A) (f : P.getLast.B a → P.getLast.M)
    (h : PFunctor.M.dest x = ⟨a, f⟩) (i : Fin2 n) (c : P.drop.B a i) : M.path x i
  |
  child (x : P.getLast.M) (a : P.A) (f : P.getLast.B a → P.getLast.M)
    (h : PFunctor.M.dest x = ⟨a, f⟩) (j : P.getLast.B a) (i : Fin2 n) (c : M.path (f j) i) :
    M.path x i
#align mvpfunctor.M.path MvPFunctor.M.Path

instance M.Path.inhabited (x : P.getLast.M) {i} [Inhabited (P.drop.B x.headI i)] :
    Inhabited (M.Path P x i) :=
  ⟨M.Path.root _ (PFunctor.M.head x) (PFunctor.M.children x)
      (PFunctor.M.casesOn' x <| by
        intros <;> simp [PFunctor.M.dest_mk] <;> ext <;> rw [PFunctor.M.children_mk] <;> rfl)
      _ default⟩
#align mvpfunctor.M.path.inhabited MvPFunctor.M.Path.inhabited

/-- Polynomial functor of the M-type of `P`. `A` is a data-less
possibly infinite tree whereas, for a given `a : A`, `B a` is a valid
path in tree `a` so that `Wp.obj α` is made of a tree and a function
from its valid paths to the values it contains -/
def mp : MvPFunctor n where
  A := P.getLast.M
  B := M.Path P
#align mvpfunctor.Mp MvPFunctor.mp

/-- `n`-ary M-type for `P` -/
def M (α : TypeVec n) : Type _ :=
  P.mp.Obj α
#align mvpfunctor.M MvPFunctor.M

instance mvfunctorM : MvFunctor P.M := by delta M <;> infer_instance
#align mvpfunctor.mvfunctor_M MvPFunctor.mvfunctorM

instance inhabitedM {α : TypeVec _} [I : Inhabited P.A] [∀ i : Fin2 n, Inhabited (α i)] :
    Inhabited (P.M α) :=
  @Obj.inhabited _ (mp P) _ (@PFunctor.M.inhabited P.getLast I) _
#align mvpfunctor.inhabited_M MvPFunctor.inhabitedM

/-- construct through corecursion the shape of an M-type
without its contents -/
def M.corecShape {β : Type u} (g₀ : β → P.A) (g₂ : ∀ b : β, P.getLast.B (g₀ b) → β) :
    β → P.getLast.M :=
  PFunctor.M.corec fun b => ⟨g₀ b, g₂ b⟩
#align mvpfunctor.M.corec_shape MvPFunctor.M.corecShape

/-- Proof of type equality as an arrow -/
def castDropB {a a' : P.A} (h : a = a') : P.drop.B a ⟹ P.drop.B a' := fun i b => Eq.recOn h b
#align mvpfunctor.cast_dropB MvPFunctor.castDropB

/-- Proof of type equality as a function -/
def castLastB {a a' : P.A} (h : a = a') : P.getLast.B a → P.getLast.B a' := fun b => Eq.recOn h b
#align mvpfunctor.cast_lastB MvPFunctor.castLastB

/-- Using corecursion, construct the contents of an M-type -/
def M.corecContents {α : TypeVec.{u} n} {β : Type u} (g₀ : β → P.A)
    (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α) (g₂ : ∀ b : β, P.getLast.B (g₀ b) → β) :
    ∀ x b, x = M.corecShape P g₀ g₂ b → M.Path P x ⟹ α
  | _, b, h, _, M.path.root x a f h' i c =>
    have : a = g₀ b := by
      rw [h, M.corec_shape, PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    g₁ b i (P.castDropB this i c)
  | _, b, h, _, M.path.child x a f h' j i c =>
    have h₀ : a = g₀ b := by
      rw [h, M.corec_shape, PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    have h₁ : f j = M.corecShape P g₀ g₂ (g₂ b (castLastB P h₀ j)) :=
      by
      rw [h, M.corec_shape, PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    M.corec_contents (f j) (g₂ b (P.castLastB h₀ j)) h₁ i c
#align mvpfunctor.M.corec_contents MvPFunctor.M.corecContents

/-- Corecursor for M-type of `P` -/
def M.corec' {α : TypeVec n} {β : Type u} (g₀ : β → P.A) (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : ∀ b : β, P.getLast.B (g₀ b) → β) : β → P.M α := fun b =>
  ⟨M.corecShape P g₀ g₂ b, M.corecContents P g₀ g₁ g₂ _ _ rfl⟩
#align mvpfunctor.M.corec' MvPFunctor.M.corec'

/-- Corecursor for M-type of `P` -/
def M.corec {α : TypeVec n} {β : Type u} (g : β → P.Obj (α.append1 β)) : β → P.M α :=
  M.corec' P (fun b => (g b).fst) (fun b => dropFun (g b).snd) fun b => lastFun (g b).snd
#align mvpfunctor.M.corec MvPFunctor.M.corec

/-- Implementation of destructor for M-type of `P` -/
def M.pathDestLeft {α : TypeVec n} {x : P.getLast.M} {a : P.A} {f : P.getLast.B a → P.getLast.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) : P.drop.B a ⟹ α := fun i c =>
  f' i (M.Path.root x a f h i c)
#align mvpfunctor.M.path_dest_left MvPFunctor.M.pathDestLeft

/-- Implementation of destructor for M-type of `P` -/
def M.pathDestRight {α : TypeVec n} {x : P.getLast.M} {a : P.A} {f : P.getLast.B a → P.getLast.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) :
    ∀ j : P.getLast.B a, M.Path P (f j) ⟹ α := fun j i c => f' i (M.Path.child x a f h j i c)
#align mvpfunctor.M.path_dest_right MvPFunctor.M.pathDestRight

/-- Destructor for M-type of `P` -/
def M.dest' {α : TypeVec n} {x : P.getLast.M} {a : P.A} {f : P.getLast.B a → P.getLast.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) : P.Obj (α.append1 (P.M α)) :=
  ⟨a, splitFun (M.pathDestLeft P h f') fun x => ⟨f x, M.pathDestRight P h f' x⟩⟩
#align mvpfunctor.M.dest' MvPFunctor.M.dest'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Destructor for M-types -/
def M.dest {α : TypeVec n} (x : P.M α) : P.Obj (α ::: P.M α) :=
  M.dest' P (Sigma.eta <| PFunctor.M.dest x.fst).symm x.snd
#align mvpfunctor.M.dest MvPFunctor.M.dest

/-- Constructor for M-types -/
def M.mk {α : TypeVec n} : P.Obj (α.append1 (P.M α)) → P.M α :=
  M.corec _ fun i => appendFun id (M.dest P) <$$> i
#align mvpfunctor.M.mk MvPFunctor.M.mk

theorem M.dest'_eq_dest' {α : TypeVec n} {x : P.getLast.M} {a₁ : P.A}
    {f₁ : P.getLast.B a₁ → P.getLast.M} (h₁ : PFunctor.M.dest x = ⟨a₁, f₁⟩) {a₂ : P.A}
    {f₂ : P.getLast.B a₂ → P.getLast.M} (h₂ : PFunctor.M.dest x = ⟨a₂, f₂⟩) (f' : M.Path P x ⟹ α) :
    M.dest' P h₁ f' = M.dest' P h₂ f' := by cases h₁.symm.trans h₂ <;> rfl
#align mvpfunctor.M.dest'_eq_dest' MvPFunctor.M.dest'_eq_dest'

theorem M.dest_eq_dest' {α : TypeVec n} {x : P.getLast.M} {a : P.A}
    {f : P.getLast.B a → P.getLast.M} (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) :
    M.dest P ⟨x, f'⟩ = M.dest' P h f' :=
  M.dest'_eq_dest' _ _ _ _
#align mvpfunctor.M.dest_eq_dest' MvPFunctor.M.dest_eq_dest'

theorem M.dest_corec' {α : TypeVec.{u} n} {β : Type u} (g₀ : β → P.A)
    (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α) (g₂ : ∀ b : β, P.getLast.B (g₀ b) → β) (x : β) :
    M.dest P (M.corec' P g₀ g₁ g₂ x) = ⟨g₀ x, splitFun (g₁ x) (M.corec' P g₀ g₁ g₂ ∘ g₂ x)⟩ :=
  rfl
#align mvpfunctor.M.dest_corec' MvPFunctor.M.dest_corec'

theorem M.dest_corec {α : TypeVec n} {β : Type u} (g : β → P.Obj (α.append1 β)) (x : β) :
    M.dest P (M.corec P g x) = appendFun id (M.corec P g) <$$> g x :=
  by
  trans; apply M.dest_corec'
  cases' g x with a f; dsimp
  rw [MvPFunctor.map_eq]; congr
  conv =>
    rhs
    rw [← split_drop_fun_last_fun f, append_fun_comp_split_fun]
  rfl
#align mvpfunctor.M.dest_corec MvPFunctor.M.dest_corec

theorem M.bisim_lemma {α : TypeVec n} {a₁ : (mp P).A} {f₁ : (mp P).B a₁ ⟹ α} {a' : P.A}
    {f' : (P.B a').drop ⟹ α} {f₁' : (P.B a').getLast → M P α}
    (e₁ : M.dest P ⟨a₁, f₁⟩ = ⟨a', splitFun f' f₁'⟩) :
    ∃ (g₁' : _)(e₁' : PFunctor.M.dest a₁ = ⟨a', g₁'⟩),
      f' = M.pathDestLeft P e₁' f₁ ∧
        f₁' = fun x : (last P).B a' => ⟨g₁' x, M.pathDestRight P e₁' f₁ x⟩ :=
  by
  generalize ef : @split_fun n _ (append1 α (M P α)) f' f₁' = ff at e₁
  cases' e₁' : PFunctor.M.dest a₁ with a₁' g₁'
  rw [M.dest_eq_dest' _ e₁'] at e₁
  cases e₁; exact ⟨_, e₁', split_fun_inj ef⟩
#align mvpfunctor.M.bisim_lemma MvPFunctor.M.bisim_lemma

theorem M.bisim {α : TypeVec n} (R : P.M α → P.M α → Prop)
    (h :
      ∀ x y,
        R x y →
          ∃ a f f₁ f₂,
            M.dest P x = ⟨a, splitFun f f₁⟩ ∧
              M.dest P y = ⟨a, splitFun f f₂⟩ ∧ ∀ i, R (f₁ i) (f₂ i))
    (x y) (r : R x y) : x = y := by
  cases' x with a₁ f₁
  cases' y with a₂ f₂
  dsimp [Mp] at *
  have : a₁ = a₂ :=
    by
    refine'
      PFunctor.M.bisim (fun a₁ a₂ => ∃ x y, R x y ∧ x.1 = a₁ ∧ y.1 = a₂) _ _ _
        ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩
    rintro _ _ ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩
    rcases h _ _ r with ⟨a', f', f₁', f₂', e₁, e₂, h'⟩
    rcases M.bisim_lemma P e₁ with ⟨g₁', e₁', rfl, rfl⟩
    rcases M.bisim_lemma P e₂ with ⟨g₂', e₂', _, rfl⟩
    rw [e₁', e₂']
    exact ⟨_, _, _, rfl, rfl, fun b => ⟨_, _, h' b, rfl, rfl⟩⟩
  subst this
  congr with (i p)
  induction' p with x a f h' i c x a f h' i c p IH generalizing f₁ f₂ <;>
    try
      rcases h _ _ r with ⟨a', f', f₁', f₂', e₁, e₂, h''⟩
      rcases M.bisim_lemma P e₁ with ⟨g₁', e₁', rfl, rfl⟩
      rcases M.bisim_lemma P e₂ with ⟨g₂', e₂', e₃, rfl⟩
      cases h'.symm.trans e₁'
      cases h'.symm.trans e₂'
  · exact (congr_fun (congr_fun e₃ i) c : _)
  · exact IH _ _ (h'' _)
#align mvpfunctor.M.bisim MvPFunctor.M.bisim

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem M.bisim₀ {α : TypeVec n} (R : P.M α → P.M α → Prop) (h₀ : Equivalence R)
    (h : ∀ x y, R x y → (id ::: Quot.mk R) <$$> M.dest _ x = (id ::: Quot.mk R) <$$> M.dest _ y)
    (x y) (r : R x y) : x = y := by
  apply M.bisim P R _ _ _ r
  clear r x y
  introv Hr
  specialize h _ _ Hr
  clear Hr
  rcases M.dest P x with ⟨ax, fx⟩
  rcases M.dest P y with ⟨ay, fy⟩
  intro h
  rw [map_eq, map_eq] at h
  injection h with h₀ h₁
  subst ay
  simp at h₁
  clear h
  have Hdrop : drop_fun fx = drop_fun fy :=
    by
    replace h₁ := congr_arg drop_fun h₁
    simpa using h₁
  exists ax, drop_fun fx, last_fun fx, last_fun fy
  rw [split_drop_fun_last_fun, Hdrop, split_drop_fun_last_fun]
  simp
  intro i
  replace h₁ := congr_fun (congr_fun h₁ Fin2.fz) i
  simp [(· ⊚ ·), append_fun, split_fun] at h₁
  replace h₁ := Quot.exact _ h₁
  rw [h₀.eqv_gen_iff] at h₁
  exact h₁
#align mvpfunctor.M.bisim₀ MvPFunctor.M.bisim₀

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem M.bisim' {α : TypeVec n} (R : P.M α → P.M α → Prop)
    (h : ∀ x y, R x y → (id ::: Quot.mk R) <$$> M.dest _ x = (id ::: Quot.mk R) <$$> M.dest _ y)
    (x y) (r : R x y) : x = y := by
  have := M.bisim₀ P (EqvGen R) _ _
  · solve_by_elim [EqvGen.rel]
  · apply EqvGen.is_equivalence
  · clear r x y
    introv Hr
    have : ∀ x y, R x y → EqvGen R x y := @EqvGen.rel _ R
    induction Hr
    · rw [← Quot.factor_mk_eq R (EqvGen R) this]
      rwa [append_fun_comp_id, ← MvFunctor.map_map, ← MvFunctor.map_map, h]
    all_goals cc
#align mvpfunctor.M.bisim' MvPFunctor.M.bisim'

theorem M.dest_map {α β : TypeVec n} (g : α ⟹ β) (x : P.M α) :
    M.dest P (g <$$> x) = (appendFun g fun x => g <$$> x) <$$> M.dest P x :=
  by
  cases' x with a f
  rw [map_eq]
  conv =>
    rhs
    rw [M.dest, M.dest', map_eq, append_fun_comp_split_fun]
  rfl
#align mvpfunctor.M.dest_map MvPFunctor.M.dest_map

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem M.map_dest {α β : TypeVec n} (g : (α ::: P.M α) ⟹ (β ::: P.M β)) (x : P.M α)
    (h : ∀ x : P.M α, lastFun g x = (dropFun g <$$> x : P.M β)) :
    g <$$> M.dest P x = M.dest P (dropFun g <$$> x) :=
  by
  rw [M.dest_map]; congr
  apply eq_of_drop_last_eq <;> simp
  ext1; apply h
#align mvpfunctor.M.map_dest MvPFunctor.M.map_dest

end MvPFunctor

