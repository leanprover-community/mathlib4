/-
Copyright (c) 2021 Roberto Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roberto Alvarez

! This file was ported from Lean 3 source module topology.homotopy.homotopy_group
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# `n`th homotopy group

We define the `n`th homotopy group at `x`, `π n x`, as the equivalence classes
of functions from the nth dimensional cube to the topological space `X`
that send the boundary to the base point `x`, up to homotopic equivalence.
Note that such functions are generalized loops `gen_loop n x`, in particular
`gen_loop 1 x ≃ path x x`

We show that `π 0 x` is equivalent to the path-conected components, and
that `π 1 x` is equivalent to the fundamental group at `x`.

## definitions

* `gen_loop n x` is the type of continous fuctions `I^n → X` that send the boundary to `x`
* `homotopy_group n x` denoted `π n x` is the quotient of `gen_loop n x` by homotopy relative
  to the boundary

TODO: show that `π n x` is a group when `n > 0` and abelian when `n > 1`. Show that
`pi1_equiv_fundamental_group` is an isomorphism of groups.

-/


open scoped unitInterval Topology

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X]

variable {n : ℕ} {x : X}

/-- The `n`-dimensional cube.
-/
def Cube (n : ℕ) : Type :=
  Fin n → I deriving Zero, One, TopologicalSpace
#align cube Cube

-- mathport name: «exprI^»
local notation "I^" => Cube

namespace Cube

@[continuity]
theorem proj_continuous (i : Fin n) : Continuous fun f : I^ n => f i :=
  continuous_apply i
#align cube.proj_continuous Cube.proj_continuous

/-- The points of the `n`-dimensional cube with at least one projection equal to 0 or 1.
-/
def boundary (n : ℕ) : Set (I^ n) :=
  { y | ∃ i, y i = 0 ∨ y i = 1 }
#align cube.boundary Cube.boundary

/-- The first projection of a positive-dimensional cube.
-/
@[simp]
def head {n} : I^ (n + 1) → I := fun c => c 0
#align cube.head Cube.head

@[continuity]
theorem head.continuous {n} : Continuous (@head n) :=
  proj_continuous 0
#align cube.head.continuous Cube.head.continuous

/-- The projection to the last `n` coordinates from an `n+1` dimensional cube.
-/
@[simp]
def tail {n} : I^ (n + 1) → I^ n := fun c => Fin.tail c
#align cube.tail Cube.tail

instance uniqueCube0 : Unique (I^ 0) :=
  Pi.uniqueOfIsEmpty _
#align cube.unique_cube0 Cube.uniqueCube0

theorem one_char (f : I^ 1) : f = fun _ => f 0 := by convert eq_const_of_unique f
#align cube.one_char Cube.one_char

end Cube

/--
The `n`-dimensional generalized loops; functions `I^n → X` that send the boundary to the base point.
-/
structure GenLoop (n : ℕ) (x : X) extends C(I^ n, X) where
  boundary : ∀ y ∈ Cube.boundary n, to_fun y = x
#align gen_loop GenLoop

namespace GenLoop

instance funLike : FunLike (GenLoop n x) (I^ n) fun _ => X
    where
  coe f := f.1
  coe_injective' := fun ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ h => by congr ; exact h
#align gen_loop.fun_like GenLoop.funLike

@[ext]
theorem ext (f g : GenLoop n x) (H : ∀ y, f y = g y) : f = g :=
  FunLike.ext f g H
#align gen_loop.ext GenLoop.ext

@[simp]
theorem mk_apply (f : C(I^ n, X)) (H y) : (⟨f, H⟩ : GenLoop n x) y = f y :=
  rfl
#align gen_loop.mk_apply GenLoop.mk_apply

/-- The constant `gen_loop` at `x`.
-/
def const : GenLoop n x :=
  ⟨ContinuousMap.const _ x, fun _ _ => rfl⟩
#align gen_loop.const GenLoop.const

instance inhabited : Inhabited (GenLoop n x) where default := const
#align gen_loop.inhabited GenLoop.inhabited

/-- The "homotopy relative to boundary" relation between `gen_loop`s.
-/
def Homotopic (f g : GenLoop n x) : Prop :=
  f.toContinuousMap.HomotopicRel g.toContinuousMap (Cube.boundary n)
#align gen_loop.homotopic GenLoop.Homotopic

namespace homotopic

section

variable {f g h : GenLoop n x}

@[refl]
theorem refl (f : GenLoop n x) : Homotopic f f :=
  ContinuousMap.HomotopicRel.refl _
#align gen_loop.homotopic.refl GenLoop.Homotopic.refl

@[symm]
theorem symm (H : f.Homotopic g) : g.Homotopic f :=
  H.symm
#align gen_loop.homotopic.symm GenLoop.Homotopic.symm

@[trans]
theorem trans (H0 : f.Homotopic g) (H1 : g.Homotopic h) : f.Homotopic h :=
  H0.trans H1
#align gen_loop.homotopic.trans GenLoop.Homotopic.trans

theorem equiv : Equivalence (@Homotopic X _ n x) :=
  ⟨Homotopic.refl, fun _ _ => Homotopic.symm, fun _ _ _ => Homotopic.trans⟩
#align gen_loop.homotopic.equiv GenLoop.Homotopic.equiv

instance setoid (n : ℕ) (x : X) : Setoid (GenLoop n x) :=
  ⟨Homotopic, equiv⟩
#align gen_loop.homotopic.setoid GenLoop.Homotopic.setoid

end

end homotopic

end GenLoop

/-- The `n`th homotopy group at `x` defined as the quotient of `gen_loop n x` by the
`homotopic` relation.
-/
def HomotopyGroup (n : ℕ) (x : X) : Type _ :=
  Quotient (GenLoop.Homotopic.setoid n x)deriving Inhabited
#align homotopy_group HomotopyGroup

-- mathport name: exprπ
local notation "π" => HomotopyGroup

/-- The 0-dimensional generalized loops based at `x` are in 1-1 correspondence with `X`. -/
def genLoopZeroEquiv : GenLoop 0 x ≃ X where
  toFun f := f 0
  invFun x := ⟨ContinuousMap.const _ x, fun _ ⟨f0, _⟩ => f0.elim0ₓ⟩
  left_inv f := by ext1; exact congr_arg f (Subsingleton.elim _ _)
  right_inv _ := rfl
#align gen_loop_zero_equiv genLoopZeroEquiv

/-- The 0th homotopy "group" is equivalent to the path components of `X`, aka the `zeroth_homotopy`.
-/
def pi0EquivPathComponents : π 0 x ≃ ZerothHomotopy X :=
  Quotient.congr genLoopZeroEquiv
    (by
      -- joined iff homotopic
      intros ;
      constructor <;> rintro ⟨H⟩
      exacts[⟨{
            toFun := fun t => H ⟨t, Fin.elim0⟩
            source' := (H.apply_zero _).trans (congr_arg a₁ matrix.zero_empty.symm)
            target' := (H.apply_one _).trans (congr_arg a₂ matrix.zero_empty.symm) }⟩,
        ⟨{  toFun := fun t0 => H t0.fst
            map_zero_left' := fun _ => by convert H.source
            map_one_left' := fun _ => by convert H.target
            prop' := fun _ _ ⟨i, _⟩ => i.elim0ₓ }⟩])
#align pi0_equiv_path_components pi0EquivPathComponents

/-- The 1-dimensional generalized loops based at `x` are in 1-1 correspondence with
  paths from `x` to itself. -/
@[simps]
def genLoopOneEquivPathSelf : GenLoop 1 x ≃ Path x x
    where
  toFun p :=
    Path.mk ⟨fun t => p fun _ => t, by continuity; exact p.1.2⟩
      (p.boundary (fun _ => 0) ⟨0, Or.inl rfl⟩) (p.boundary (fun _ => 1) ⟨1, Or.inr rfl⟩)
  invFun p :=
    { toFun := fun c => p c.headI
      boundary :=
        by
        rintro y ⟨i, iH | iH⟩ <;> cases Unique.eq_default i <;> apply (congr_arg p iH).trans
        exacts[p.source, p.target] }
  left_inv p := by ext1; exact congr_arg p y.one_char.symm
  right_inv p := by ext; rfl
#align gen_loop_one_equiv_path_self genLoopOneEquivPathSelf

/-- The first homotopy group at `x` is equivalent to the fundamental group,
i.e. the loops based at `x` up to homotopy.
-/
def pi1EquivFundamentalGroup : π 1 x ≃ FundamentalGroup X x :=
  by
  refine' Equiv.trans _ (CategoryTheory.Groupoid.isoEquivHom _ _).symm
  refine' Quotient.congr genLoopOneEquivPathSelf _
  -- homotopic iff homotopic
  intros ;
  constructor <;> rintro ⟨H⟩
  exacts[⟨{
        toFun := fun tx => H (tx.fst, fun _ => tx.snd)
        map_zero_left' := fun _ => by convert H.apply_zero _
        map_one_left' := fun _ => by convert H.apply_one _
        prop' := fun t y iH => H.prop' _ _ ⟨0, iH⟩ }⟩,
    ⟨{  toFun := fun tx => H (tx.fst, tx.snd.head)
        map_zero_left' := fun y => by convert H.apply_zero _; exact y.one_char
        map_one_left' := fun y => by convert H.apply_one _; exact y.one_char
        prop' := fun t y ⟨i, iH⟩ => by
          cases Unique.eq_default i; constructor
          · convert H.eq_fst _ _; exacts[y.one_char, iH]
          · convert H.eq_snd _ _; exacts[y.one_char, iH] }⟩]
#align pi1_equiv_fundamental_group pi1EquivFundamentalGroup

