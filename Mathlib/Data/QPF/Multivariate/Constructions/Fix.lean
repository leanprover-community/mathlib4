/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon

! This file was ported from Lean 3 source module data.qpf.multivariate.constructions.fix
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.PFunctor.Multivariate.W
import Mathlib.Data.QPF.Multivariate.Basic

/-!
# The initial algebra of a multivariate qpf is again a qpf.

For a `(n+1)`-ary QPF `F (α₀,..,αₙ)`, we take the least fixed point of `F` with
regards to its last argument `αₙ`. The result is a `n`-ary functor: `Fix F (α₀,..,αₙ₋₁)`.
Making `Fix F` into a functor allows us to take the fixed point, compose with other functors
and take a fixed point again.

## Main definitions

 * `Fix.mk`     - constructor
 * `Fix.dest`    - destructor
 * `Fix.rec`    - recursor: basis for defining functions by structural recursion on `Fix F α`
 * `Fix.drec`   - dependent recursor: generalization of `Fix.rec` where
                  the result type of the function is allowed to depend on the `Fix F α` value
 * `Fix.rec_eq` - defining equation for `recursor`
 * `Fix.ind`    - induction principle for `Fix F α`

## Implementation notes

For `F` a `QPF`, we define `Fix F α` in terms of the W-type of the polynomial functor `P` of `F`.
We define the relation `WEquiv` and take its quotient as the definition of `Fix F α`.

See [avigad-carneiro-hudon2019] for more details.

## Reference

 * Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
   [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/


universe u v

namespace MvQPF

open TypeVec

open MvFunctor (LiftP LiftR)

open MvFunctor

variable {n : ℕ} {F : TypeVec.{u} (n + 1) → Type u} [MvFunctor F] [q : MvQPF F]


/-- `recF` is used as a basis for defining the recursor on `Fix F α`. `recF`
traverses recursively the W-type generated by `q.P` using a function on `F`
as a recursive step -/
def recF {α : TypeVec n} {β : Type _} (g : F (α.append1 β) → β) : q.P.W α → β :=
  q.P.wRec fun a f' _f rec => g (abs ⟨a, splitFun f' rec⟩)
set_option linter.uppercaseLean3 false in
#align mvqpf.recF MvQPF.recF

theorem recF_eq {α : TypeVec n} {β : Type _} (g : F (α.append1 β) → β) (a : q.P.A)
    (f' : q.P.drop.B a ⟹ α) (f : q.P.last.B a → q.P.W α) :
    recF g (q.P.wMk a f' f) = g (abs ⟨a, splitFun f' (recF g ∘ f)⟩) := by
  rw [recF, MvPFunctor.wRec_eq]; rfl
set_option linter.uppercaseLean3 false in
#align mvqpf.recF_eq MvQPF.recF_eq

theorem recF_eq' {α : TypeVec n} {β : Type _} (g : F (α.append1 β) → β) (x : q.P.W α) :
    recF g x = g (abs (appendFun id (recF g) <$$> q.P.wDest' x)) := by
  apply q.P.w_cases _ x
  intro a f' f
  rw [recF_eq, q.P.wDest'_wMk, MvPFunctor.map_eq, appendFun_comp_splitFun, TypeVec.id_comp]
set_option linter.uppercaseLean3 false in
#align mvqpf.recF_eq' MvQPF.recF_eq'

/-- Equivalence relation on W-types that represent the same `Fix F`
value -/
inductive WEquiv {α : TypeVec n} : q.P.W α → q.P.W α → Prop
  | ind (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f₀ f₁ : q.P.last.B a → q.P.W α) :
    (∀ x, WEquiv (f₀ x) (f₁ x)) → WEquiv (q.P.wMk a f' f₀) (q.P.wMk a f' f₁)
  | abs (a₀ : q.P.A) (f'₀ : q.P.drop.B a₀ ⟹ α) (f₀ : q.P.last.B a₀ → q.P.W α) (a₁ : q.P.A)
    (f'₁ : q.P.drop.B a₁ ⟹ α) (f₁ : q.P.last.B a₁ → q.P.W α) :
    abs ⟨a₀, q.P.appendContents f'₀ f₀⟩ = abs ⟨a₁, q.P.appendContents f'₁ f₁⟩ →
      WEquiv (q.P.wMk a₀ f'₀ f₀) (q.P.wMk a₁ f'₁ f₁)
  | trans (u v w : q.P.W α) : WEquiv u v → WEquiv v w → WEquiv u w
set_option linter.uppercaseLean3 false in
#align mvqpf.Wequiv MvQPF.WEquiv

theorem recF_eq_of_WEquiv (α : TypeVec n) {β : Type _} (u : F (α.append1 β) → β) (x y : q.P.W α) :
    WEquiv x y → recF u x = recF u y := by
  apply q.P.w_cases _ x
  intro a₀ f'₀ f₀
  apply q.P.w_cases _ y
  intro a₁ f'₁ f₁
  intro h
  -- porting note: induction on h doesn't work.
  refine' @WEquiv.recOn _ _ _ _ _ (λ a a' _ => recF u a = recF u a') _ _ h _ _ _
  · intros a f' f₀ f₁ _h ih; simp only [recF_eq, Function.comp]
    congr; funext; congr; funext; apply ih
  · intros a₀ f'₀ f₀ a₁ f'₁ f₁ h; simp only [recF_eq', abs_map, MvPFunctor.wDest'_wMk, h]
  · intros x y z _e₁ _e₂ ih₁ ih₂; exact Eq.trans ih₁ ih₂
set_option linter.uppercaseLean3 false in
#align mvqpf.recF_eq_of_Wequiv MvQPF.recF_eq_of_WEquiv

theorem WEquiv.abs' {α : TypeVec n} (x y : q.P.W α)
                    (h : MvQPF.abs (q.P.wDest' x ) = MvQPF.abs (q.P.wDest' y)) :
    WEquiv x y := by
  revert h
  apply q.P.w_cases _ x
  intro a₀ f'₀ f₀
  apply q.P.w_cases _ y
  intro a₁ f'₁ f₁
  apply WEquiv.abs
set_option linter.uppercaseLean3 false in
#align mvqpf.Wequiv.abs' MvQPF.WEquiv.abs'

theorem WEquiv.refl {α : TypeVec n} (x : q.P.W α) : WEquiv x x := by
  apply q.P.w_cases _ x; intro a f' f; exact WEquiv.abs a f' f a f' f rfl
set_option linter.uppercaseLean3 false in
#align mvqpf.Wequiv.refl MvQPF.WEquiv.refl

theorem WEquiv.symm {α : TypeVec n} (x y : q.P.W α) : WEquiv x y → WEquiv y x := by
  intro h; induction h
  case ind a f' f₀ f₁ _h ih => exact WEquiv.ind _ _ _ _ ih
  case abs a₀ f'₀ f₀ a₁ f'₁ f₁ h => exact WEquiv.abs _ _ _ _ _ _ h.symm
  case trans x y z _e₁ _e₂ ih₁ ih₂ => exact MvQPF.WEquiv.trans _ _ _ ih₂ ih₁
set_option linter.uppercaseLean3 false in
#align mvqpf.Wequiv.symm MvQPF.WEquiv.symm

/-- maps every element of the W type to a canonical representative -/
def wrepr {α : TypeVec n} : q.P.W α → q.P.W α :=
  recF (q.P.wMk' ∘ repr)
set_option linter.uppercaseLean3 false in
#align mvqpf.Wrepr MvQPF.wrepr

theorem wrepr_wMk {α : TypeVec n} (a : q.P.A) (f' : q.P.drop.B a ⟹ α)
    (f : q.P.last.B a → q.P.W α) :
    wrepr (q.P.wMk a f' f) =
      q.P.wMk' (repr (abs (appendFun id wrepr <$$> ⟨a, q.P.appendContents f' f⟩))) :=
  by rw [wrepr, recF_eq', q.P.wDest'_wMk]; rfl
set_option linter.uppercaseLean3 false in
#align mvqpf.Wrepr_W_mk MvQPF.wrepr_wMk

theorem wrepr_equiv {α : TypeVec n} (x : q.P.W α) : WEquiv (wrepr x) x := by
  apply q.P.w_ind _ x; intro a f' f ih
  apply WEquiv.trans _ (q.P.wMk' (appendFun id wrepr <$$> ⟨a, q.P.appendContents f' f⟩))
  · apply WEquiv.abs'
    rw [wrepr_wMk, q.P.wDest'_wMk', q.P.wDest'_wMk', abs_repr]
  rw [q.P.map_eq, MvPFunctor.wMk', appendFun_comp_splitFun, id_comp]
  apply WEquiv.ind; exact ih
set_option linter.uppercaseLean3 false in
#align mvqpf.Wrepr_equiv MvQPF.wrepr_equiv

theorem WEquiv_map {α β : TypeVec n} (g : α ⟹ β) (x y : q.P.W α) :
    WEquiv x y → WEquiv (g <$$> x) (g <$$> y) := by
  intro h; induction h
  case ind a f' f₀ f₁ h ih => rw [q.P.w_map_wMk, q.P.w_map_wMk]; apply WEquiv.ind; exact ih
  case
    abs a₀ f'₀ f₀ a₁ f'₁ f₁ h =>
    rw [q.P.w_map_wMk, q.P.w_map_wMk]; apply WEquiv.abs
    show
      abs (q.P.objAppend1 a₀ (g ⊚ f'₀) fun x => q.P.wMap g (f₀ x)) =
        abs (q.P.objAppend1 a₁ (g ⊚ f'₁) fun x => q.P.wMap g (f₁ x))
    rw [← q.P.map_objAppend1, ← q.P.map_objAppend1, abs_map, abs_map, h]
  case trans x y z _ _ ih₁ ih₂ => apply MvQPF.WEquiv.trans; apply ih₁; apply ih₂
set_option linter.uppercaseLean3 false in
#align mvqpf.Wequiv_map MvQPF.WEquiv_map

/-- Define the fixed point as the quotient of trees under the equivalence relation.
-/
def wSetoid (α : TypeVec n) : Setoid (q.P.W α) :=
  ⟨WEquiv, @WEquiv.refl _ _ _ _ _, @WEquiv.symm _ _ _ _ _, @WEquiv.trans _ _ _ _ _⟩
set_option linter.uppercaseLean3 false in
#align mvqpf.W_setoid MvQPF.wSetoid

attribute [local instance] wSetoid

/-- Least fixed point of functor F. The result is a functor with one fewer parameters
than the input. For `F a b c` a ternary functor, `Fix F` is a binary functor such that

```lean
Fix F a b = F a b (Fix F a b)
```
-/
def Fix {n : ℕ} (F : TypeVec (n + 1) → Type _) [MvFunctor F] [q : MvQPF F] (α : TypeVec n) :=
  Quotient (wSetoid α : Setoid (q.P.W α))
#align mvqpf.fix MvQPF.Fix

--attribute [nolint has_nonempty_instance] Fix

/-- `Fix F` is a functor -/
def Fix.map {α β : TypeVec n} (g : α ⟹ β) : Fix F α → Fix F β :=
  Quotient.lift (fun x : q.P.W α => ⟦q.P.wMap g x⟧) fun _a _b h => Quot.sound (WEquiv_map _ _ _ h)
#align mvqpf.fix.map MvQPF.Fix.map

instance Fix.mvfunctor : MvFunctor (Fix F) where map := @Fix.map _ _ _ _
#align mvqpf.fix.mvfunctor MvQPF.Fix.mvfunctor

variable {α : TypeVec.{u} n}

/-- Recursor for `Fix F` -/
def Fix.rec {β : Type u} (g : F (α ::: β) → β) : Fix F α → β :=
  Quot.lift (recF g) (recF_eq_of_WEquiv α g)
#align mvqpf.fix.rec MvQPF.Fix.rec

/-- Access W-type underlying `Fix F`  -/
def fixToW : Fix F α → q.P.W α :=
  Quotient.lift wrepr (recF_eq_of_WEquiv α fun x => q.P.wMk' (repr x))
set_option linter.uppercaseLean3 false in
#align mvqpf.fix_to_W MvQPF.fixToW

/-- Constructor for `Fix F` -/
def Fix.mk (x : F (append1 α (Fix F α))) : Fix F α :=
  Quot.mk _ (q.P.wMk' (appendFun id fixToW <$$> repr x))
#align mvqpf.fix.mk MvQPF.Fix.mk

/-- Destructor for `Fix F` -/
def Fix.dest : Fix F α → F (append1 α (Fix F α)) :=
  Fix.rec (MvFunctor.map (appendFun id Fix.mk))
#align mvqpf.fix.dest MvQPF.Fix.dest

theorem Fix.rec_eq {β : Type u} (g : F (append1 α β) → β) (x : F (append1 α (Fix F α))) :
    Fix.rec g (Fix.mk x) = g (appendFun id (Fix.rec g) <$$> x) := by
  have : recF g ∘ fixToW = Fix.rec g := by
    apply funext
    apply Quotient.ind
    intro x
    apply recF_eq_of_WEquiv
    apply wrepr_equiv
  conv =>
    lhs
    rw [Fix.rec, Fix.mk]
    dsimp
  cases' h : repr x with a f
  rw [MvPFunctor.map_eq, recF_eq', ← MvPFunctor.map_eq, MvPFunctor.wDest'_wMk']
  rw [← MvPFunctor.comp_map, abs_map, ← h, abs_repr, ← appendFun_comp, id_comp, this]
#align mvqpf.fix.rec_eq MvQPF.Fix.rec_eq

theorem Fix.ind_aux (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f : q.P.last.B a → q.P.W α) :
    Fix.mk (abs ⟨a, q.P.appendContents f' fun x => ⟦f x⟧⟩) = ⟦q.P.wMk a f' f⟧ := by
  have : Fix.mk (abs ⟨a, q.P.appendContents f' fun x => ⟦f x⟧⟩) = ⟦wrepr (q.P.wMk a f' f)⟧ :=
    by
    apply Quot.sound; apply WEquiv.abs'
    rw [MvPFunctor.wDest'_wMk', abs_map, abs_repr, ← abs_map, MvPFunctor.map_eq]
    conv =>
      rhs
      rw [wrepr_wMk, q.P.wDest'_wMk', abs_repr, MvPFunctor.map_eq]
    congr 2; rw [MvPFunctor.appendContents, MvPFunctor.appendContents]
    rw [appendFun, appendFun, ← splitFun_comp, ← splitFun_comp]
    rfl
  rw [this]
  apply Quot.sound
  apply wrepr_equiv
#align mvqpf.fix.ind_aux MvQPF.Fix.ind_aux

theorem Fix.ind_rec {β : Type _} (g₁ g₂ : Fix F α → β)
    (h :
      ∀ x : F (append1 α (Fix F α)),
        appendFun id g₁ <$$> x = appendFun id g₂ <$$> x → g₁ (Fix.mk x) = g₂ (Fix.mk x)) :
    ∀ x, g₁ x = g₂ x := by
  apply Quot.ind
  intro x
  apply q.P.w_ind _ x
  intro a f' f ih
  show g₁ ⟦q.P.wMk a f' f⟧ = g₂ ⟦q.P.wMk a f' f⟧
  rw [← Fix.ind_aux a f' f]
  apply h
  rw [← abs_map, ← abs_map, MvPFunctor.map_eq, MvPFunctor.map_eq]
  congr 2
  rw [MvPFunctor.appendContents, appendFun, appendFun, ← splitFun_comp, ← splitFun_comp]
  have : (g₁ ∘ fun x => ⟦f x⟧) = g₂ ∘ fun x => ⟦f x⟧ :=
    by
    ext x
    exact ih x
  rw [this]
#align mvqpf.fix.ind_rec MvQPF.Fix.ind_rec

theorem Fix.rec_unique {β : Type _} (g : F (append1 α β) → β) (h : Fix F α → β)
    (hyp : ∀ x, h (Fix.mk x) = g (appendFun id h <$$> x)) : Fix.rec g = h := by
  ext x
  apply Fix.ind_rec
  intro x hyp'
  rw [hyp, ← hyp', Fix.rec_eq]
#align mvqpf.fix.rec_unique MvQPF.Fix.rec_unique

theorem Fix.mk_dest (x : Fix F α) : Fix.mk (Fix.dest x) = x := by
  change (Fix.mk ∘ Fix.dest) x = x
  apply Fix.ind_rec
  intro x; dsimp
  rw [Fix.dest, Fix.rec_eq, ← comp_map, ← appendFun_comp, id_comp]
  intro h; rw [h]
  show Fix.mk (appendFun id id <$$> x) = Fix.mk x
  rw [appendFun_id_id, MvFunctor.id_map]
#align mvqpf.fix.mk_dest MvQPF.Fix.mk_dest

theorem Fix.dest_mk (x : F (append1 α (Fix F α))) : Fix.dest (Fix.mk x) = x := by
  unfold Fix.dest
  rw [Fix.rec_eq, ← Fix.dest, ← comp_map]
  conv =>
    rhs
    rw [← MvFunctor.id_map x]
  rw [← appendFun_comp, id_comp]
  have : Fix.mk ∘ Fix.dest = _root_.id := by
    ext (x: Fix F α)
    apply Fix.mk_dest
  rw [this, appendFun_id_id]
#align mvqpf.fix.dest_mk MvQPF.Fix.dest_mk

theorem Fix.ind {α : TypeVec n} (p : Fix F α → Prop)
    (h : ∀ x : F (α.append1 (Fix F α)), LiftP (PredLast α p) x → p (Fix.mk x)) : ∀ x, p x := by
  apply Quot.ind
  intro x
  apply q.P.w_ind _ x; intro a f' f ih
  change p ⟦q.P.wMk a f' f⟧
  rw [← Fix.ind_aux a f' f]
  apply h
  rw [MvQPF.liftP_iff]
  refine' ⟨_, _, rfl, _⟩
  intro i j
  cases i
  · apply ih
  · trivial
#align mvqpf.fix.ind MvQPF.Fix.ind

instance mvqpfFix : MvQPF (Fix F) where
  P := q.P.wp
  abs α := Quot.mk WEquiv α
  repr α := fixToW α
  abs_repr := by
    intro α
    apply Quot.ind
    intro a
    apply Quot.sound
    apply wrepr_equiv
  abs_map := by
    intro α β g x;
    conv =>
      rhs
      dsimp [MvFunctor.map]
#align mvqpf.mvqpf_fix MvQPF.mvqpfFix

/-- Dependent recursor for `fix F` -/
def Fix.drec {β : Fix F α → Type u}
    (g : ∀ x : F (α ::: Sigma β), β (Fix.mk <| (id ::: Sigma.fst) <$$> x)) (x : Fix F α) : β x :=
  let y := @Fix.rec _ F _ _ α (Sigma β) (fun i => ⟨_, g i⟩) x
  have : x = y.1 := by
    symm
    dsimp
    apply Fix.ind_rec _ id _ x
    intro x' ih
    rw [Fix.rec_eq]
    dsimp
    simp [appendFun_id_id] at ih
    congr
    conv =>
      rhs
      rw [← ih]
    rw [MvFunctor.map_map, ← appendFun_comp, id_comp]
    simp only [Function.comp]
  cast (by rw [this]) y.2

#align mvqpf.fix.drec MvQPF.Fix.drec

end MvQPF
