/-
Copyright (c) 2021 Roberto Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roberto Alvarez

! This file was ported from Lean 3 source module topology.homotopy.homotopy_group
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# `n`th homotopy group

We define the `n`th homotopy group at `x`, `π n x`, as the equivalence classes
of functions from the nth dimensional cube to the topological space `X`
that send the boundary to the base point `x`, up to homotopic equivalence.
Note that such functions are generalized loops `GenLoop n x`, in particular
`GenLoop 1 x ≃ Path x x`

We show that `π 0 x` is equivalent to the path-connected components, and
that `π 1 x` is equivalent to the fundamental group at `x`.

## definitions

* `GenLoop n x` is the type of continuous functions `I^n → X` that send the boundary to `x`
* `HomotopyGroup n x` denoted `π n x` is the quotient of `GenLoop n x` by homotopy relative
  to the boundary

TODO: show that `π n x` is a group when `n > 0` and abelian when `n > 1`. Show that
`pi1EquivFundamentalGroup` is an isomorphism of groups.

-/


open scoped unitInterval Topology

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X]

variable {n : ℕ} {x : X}

/-- The `n`-dimensional cube.
-/
def Cube (n : ℕ) : Type :=
  Fin n → I
#align cube Cube

local notation "I^" => Cube

-- porting note: the next 3 instances were derived in Lean 3
instance : Zero (I^ n) := inferInstanceAs (Zero (Fin n → I))
instance : One (I^ n) := inferInstanceAs (One (Fin n → I))
instance : TopologicalSpace (I^ n) := inferInstanceAs (TopologicalSpace (Fin n → I))

namespace Cube

@[continuity]
theorem proj_continuous (i : Fin n) : Continuous fun f : I^ n => f i :=
  continuous_apply i
#align cube.proj_continuous Cube.proj_continuous

/-- The points of the `n`-dimensional cube with at least one projection equal to 0 or 1.
-/
def boundary (n : ℕ) : Set (I^ n) :=
  { y | ∃ i : Fin n, y i = 0 ∨ y i = 1 }
#align cube.boundary Cube.boundary

theorem mem_boundary {y : I^ n} : y ∈ boundary n ↔ ∃ i, y i = 0 ∨ y i = 1 := Iff.rfl

theorem zero_mem_boundary [NeZero n] : 0 ∈ boundary n := ⟨0, .inl rfl⟩
theorem one_mem_boundary [NeZero n] : 1 ∈ boundary n := ⟨0, .inr rfl⟩

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

theorem one_char (f : I^ 1) : f = fun _ => f 0 := eq_const_of_unique f
#align cube.one_char Cube.one_char

open Set

@[simp] -- porting note: new lemma
theorem boundary_zero : boundary 0 = ∅ :=
  eq_empty_of_forall_not_mem <| fun _ ⟨i, _⟩ ↦ i.elim0

@[simp] -- porting note: new lemma
theorem boundary_one : boundary 1 = {0, 1} := by
  ext x
  rw [mem_boundary, Fin.exists_fin_one, mem_insert_iff, mem_singleton_iff,
    Function.funext_iff, Function.funext_iff, Fin.forall_fin_one, Fin.forall_fin_one]
  rfl

end Cube

/--
The `n`-dimensional generalized loops; functions `I^n → X` that send the boundary to the base point.
-/
structure GenLoop (n : ℕ) (x : X) extends C(I^ n, X) where
  boundary : ∀ y ∈ Cube.boundary n, toFun y = x
#align gen_loop GenLoop

namespace GenLoop

instance funLike : FunLike (GenLoop n x) (I^ n) fun _ => X where
  coe f := f.1
  coe_injective' := fun ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ _ => by congr
#align gen_loop.fun_like GenLoop.funLike

@[ext]
theorem ext (f g : GenLoop n x) (H : ∀ y, f y = g y) : f = g :=
  FunLike.ext f g H
#align gen_loop.ext GenLoop.ext

@[simp]
theorem mk_apply (f : C(I^ n, X)) (H y) : (⟨f, H⟩ : GenLoop n x) y = f y :=
  rfl
#align gen_loop.mk_apply GenLoop.mk_apply

@[simp] -- porting note: new lemma
theorem toContinuousMap_apply (f : GenLoop n x) (y) : f.toContinuousMap y = f y := rfl

initialize_simps_projections GenLoop (toFun → apply)

/-- The constant `GenLoop` at `x`.
-/
@[simps!] -- porting note: new attr
def const : GenLoop n x :=
  ⟨ContinuousMap.const _ x, fun _ _ => rfl⟩
#align gen_loop.const GenLoop.const

instance inhabited : Inhabited (GenLoop n x) where default := const
#align gen_loop.inhabited GenLoop.inhabited

/-- Restrict a `GenLoop n x` with `n ≠ 0` to the diagonal of the cube. -/
@[simps!]
def diagonal [NeZero n] (f : GenLoop n x) : Path x x where
  toContinuousMap := f.comp <| .constPi _
  source' := f.boundary _ Cube.zero_mem_boundary
  target' := f.boundary _ Cube.one_mem_boundary

/-- The "homotopy relative to boundary" relation between `GenLoop`s.
-/
def Homotopic (f g : GenLoop n x) : Prop :=
  f.toContinuousMap.HomotopicRel g.toContinuousMap (Cube.boundary n)
#align gen_loop.homotopic GenLoop.Homotopic

namespace Homotopic

variable {f g h : GenLoop n x}

@[refl]
theorem refl (f : GenLoop n x) : Homotopic f f :=
  ContinuousMap.HomotopicRel.refl _
#align gen_loop.homotopic.refl GenLoop.Homotopic.refl

@[symm]
nonrec theorem symm (H : f.Homotopic g) : g.Homotopic f :=
  H.symm
#align gen_loop.homotopic.symm GenLoop.Homotopic.symm

@[trans]
nonrec theorem trans (H0 : f.Homotopic g) (H1 : g.Homotopic h) : f.Homotopic h :=
  H0.trans H1
#align gen_loop.homotopic.trans GenLoop.Homotopic.trans

theorem equiv : Equivalence (@Homotopic X _ n x) :=
  ⟨Homotopic.refl, Homotopic.symm, Homotopic.trans⟩
#align gen_loop.homotopic.equiv GenLoop.Homotopic.equiv

instance setoid (n : ℕ) (x : X) : Setoid (GenLoop n x) :=
  ⟨Homotopic, equiv⟩
#align gen_loop.homotopic.setoid GenLoop.Homotopic.setoid

protected theorem diagonal [NeZero n] (H : f.Homotopic g) :
    f.diagonal.Homotopic g.diagonal := by
  rcases H with ⟨H⟩
  refine ⟨H.compContinuousMap _, ?_⟩
  rintro t _ (rfl | rfl)
  · exact H.prop' _ _ Cube.zero_mem_boundary
  · exact H.prop' _ _ Cube.one_mem_boundary

end Homotopic

end GenLoop

/-- The `n`th homotopy group at `x` defined as the quotient of `GenLoop n x` by the
`homotopic` relation.
-/
def HomotopyGroup (n : ℕ) (x : X) : Type _ :=
  Quotient (GenLoop.Homotopic.setoid n x)
#align homotopy_group HomotopyGroup

local notation "π" => HomotopyGroup

-- porting note: in Lean 3 this instance was derived
instance : Inhabited (π n x) :=
  inferInstanceAs <| Inhabited <| Quotient (GenLoop.Homotopic.setoid n x)

/-- The 0-dimensional generalized loops based at `x` are in 1-1 correspondence with `X`. -/
@[simps!]
def genLoopZeroEquiv : GenLoop 0 x ≃ X where
  toFun f := f 0
  invFun x := ⟨ContinuousMap.const _ x, fun _ ⟨f0, _⟩ => f0.elim0⟩
  left_inv f := by ext1; exact congr_arg f (Subsingleton.elim _ _)
  right_inv _ := rfl
#align gen_loop_zero_equiv genLoopZeroEquiv

open ContinuousMap in
@[simp] -- porting note: new lemma
theorem homotopic_genLoopZeroEquiv_symm_iff {a b : X} :
    (genLoopZeroEquiv.symm a : GenLoop 0 x).Homotopic (genLoopZeroEquiv.symm b) ↔ Joined a b := by
  rw [GenLoop.Homotopic, Cube.boundary_zero, homotopicRel_empty]
  exact homotopic_const_iff

-- porting note: new lemma    
theorem joined_genLoopZeroEquiv_iff {f g : GenLoop 0 x} :
    Joined (genLoopZeroEquiv f) (genLoopZeroEquiv g) ↔ f.Homotopic g := by
  rw [← homotopic_genLoopZeroEquiv_symm_iff, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The 0th homotopy "group" is equivalent to the path components of `X`, aka the `ZerothHomotopy`.
-/
def pi0EquivPathComponents : π 0 x ≃ ZerothHomotopy X :=
  Quotient.congr (genLoopZeroEquiv (x := x)) <| fun _ _ ↦ joined_genLoopZeroEquiv_iff.symm
#align pi0_equiv_path_components pi0EquivPathComponents

/-- The 1-dimensional generalized loops based at `x` are in 1-1 correspondence with
  paths from `x` to itself. -/
@[simps!] -- porting note: TODO: `symm_apply_apply` doesn't unfold `↑(ContinuousMap.eval 0)`
def genLoopOneEquivPathSelf : GenLoop 1 x ≃ Path x x where
  toFun p := p.diagonal
  invFun p :=
    { toContinuousMap := p.comp <| .eval 0
      boundary := by
        rw [Cube.boundary_one]
        rintro _ (rfl | rfl)
        exacts [p.source, p.target] }
  left_inv p := by ext1 y; exact congr_arg p y.one_char.symm
  right_inv p := rfl
#align gen_loop_one_equiv_path_self genLoopOneEquivPathSelf

-- porting note: new theorem
theorem genLoopOneEquivPathSelf_symm_homotopic_iff {f g : Path x x} :
    (genLoopOneEquivPathSelf.symm f).Homotopic (genLoopOneEquivPathSelf.symm g) ↔
      f.Homotopic g := by
  refine ⟨GenLoop.Homotopic.diagonal, ?_⟩
  rintro ⟨H⟩
  refine ⟨H.1.compContinuousMap _, ?_⟩
  rw [Cube.boundary_one]
  rintro t _ (rfl | rfl)
  · exact H.prop' _ _ (.inl rfl)
  · exact H.prop' _ _ (.inr rfl)

-- porting note: new theorem
theorem genLoopOneEquivPathSelf_homotopic_iff {f g : GenLoop 1 x} :
    (genLoopOneEquivPathSelf f).Homotopic (genLoopOneEquivPathSelf g) ↔ f.Homotopic g := by
  rw [← genLoopOneEquivPathSelf_symm_homotopic_iff, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The first homotopy group at `x` is equivalent to the fundamental group,
i.e. the loops based at `x` up to homotopy.
-/
def pi1EquivFundamentalGroup : π 1 x ≃ FundamentalGroup X x := by
  refine Equiv.trans ?_ (CategoryTheory.Groupoid.isoEquivHom _ _).symm
  exact Quotient.congr genLoopOneEquivPathSelf fun _ _ ↦ genLoopOneEquivPathSelf_homotopic_iff.symm
#align pi1_equiv_fundamental_group pi1EquivFundamentalGroup
