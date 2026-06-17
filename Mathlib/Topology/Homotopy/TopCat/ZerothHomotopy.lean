/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Homotopy.TopCat.Path

/-!
# `ZerothHomotopy` and connected components of `TopCat.toSSet.obj X`

In this file, given `X : TopCat`, we define a bijection
`TopCat.zerothHomotopyEquiv` between `ZerothHomotopy X` and
`(TopCat.toSSet.obj X).π₀`.

-/

@[expose] public section

universe u

open Simplicial

namespace TopCat

variable {X : TopCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Given `X : TopCat`, this is the bijection between `1`-simplices of the
singular simplicial set of `X` and the type of morphisms `I ⟶ X`. -/
noncomputable def toSSetObj₁Equiv :
    toSSet.obj X _⦋1⦌ ≃ (I ⟶ X) :=
  (toSSetObjEquiv _ _).trans
    { toFun f := ofHom (f.comp (toContinuousMap TopCat.stdSimplexHomeomorphI.symm))
      invFun f := f.hom.comp TopCat.stdSimplexHomeomorphI
      left_inv _ := by simp
      right_inv _ := by simp }

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma toSSetObj₁Equiv_apply_zero (s : toSSet.obj X _⦋1⦌) :
    X.toSSetObj₁Equiv s 0 = toSSetObj₀Equiv ((toSSet.obj X).δ 1 s) := by
  simp [toSSetObj₀Equiv, toSSetObj₁Equiv,
    Subsingleton.elim (default : stdSimplex ℝ (Fin 1)) (stdSimplex.vertex 0)]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma toSSetObj₁Equiv_apply_one (s : toSSet.obj X _⦋1⦌) :
    X.toSSetObj₁Equiv s 1 = toSSetObj₀Equiv ((toSSet.obj X).δ 0 s) := by
  simp [toSSetObj₀Equiv, toSSetObj₁Equiv,
    Subsingleton.elim (default : stdSimplex ℝ (Fin 1)) (stdSimplex.vertex 0)]

@[simp]
lemma δ_one_toSSetObj₁Equiv.symm (f : I ⟶ X) :
    (toSSet.obj X).δ 1 (toSSetObj₁Equiv.symm f) =
      toSSetObj₀Equiv.symm (f 0) :=
  toSSetObj₀Equiv.injective (by simp [← toSSetObj₁Equiv_apply_zero])

@[simp]
lemma δ_zero_toSSetObj₁Equiv.symm (f : I ⟶ X) :
    (toSSet.obj X).δ 0 (toSSetObj₁Equiv.symm f) =
      toSSetObj₀Equiv.symm (f 1) :=
  toSSetObj₀Equiv.injective (by simp [← toSSetObj₁Equiv_apply_one])

/-- Given two points `x` and `y` of `X : TopCat`, this is the bijection between
edges in the simplicial set `toSSet.obj X` connecting the vertices corresponding
to `x` and `y`, and paths from `x` to `y`. -/
@[simps]
noncomputable def toSSetObjEdgeEquiv {x y : X} :
    SSet.Edge (toSSetObj₀Equiv.symm x) (toSSetObj₀Equiv.symm y) ≃ X.Path x y where
  toFun e := { hom := toSSetObj₁Equiv e.edge }
  invFun p := SSet.Edge.mk (toSSetObj₁Equiv.symm p.hom)
  left_inv _ := by aesop
  right_inv _ := by aesop

/-- Given `X : TopCat`, this is the bijection between `ZerothHomotopy X` and the
type of connected components of the simplicial set `toSSet.obj X`. -/
noncomputable def zerothHomotopyEquiv : ZerothHomotopy X ≃ (toSSet.obj X).π₀ where
  toFun :=
    ZerothHomotopy.lift (SSet.π₀.mk ∘ toSSetObj₀Equiv.symm)
      (fun _ _ p ↦ SSet.π₀.sound (toSSetObjEdgeEquiv.symm (pathEquiv.symm p)))
  invFun := SSet.π₀.lift (ZerothHomotopy.mk ∘ toSSetObj₀Equiv) (fun x y e ↦ by
    obtain ⟨x, rfl⟩ := toSSetObj₀Equiv.symm.surjective x
    obtain ⟨y, rfl⟩ := toSSetObj₀Equiv.symm.surjective y
    exact ZerothHomotopy.sound (pathEquiv (toSSetObjEdgeEquiv e)))
  left_inv x := by induction x; simp
  right_inv x := by induction x; simp

@[simp]
lemma zerothHomotopyEquiv_mk (x : X) :
    zerothHomotopyEquiv (.mk x) = .mk (toSSetObj₀Equiv.symm x) := rfl

@[simp]
lemma zerothHomotopyEquiv_symm_mk (x : (toSSet.obj X) _⦋0⦌) :
    zerothHomotopyEquiv.symm (.mk x) = .mk (toSSetObj₀Equiv x) := rfl

instance [PathConnectedSpace X] : (toSSet.obj X).IsConnected := by
  letI : Unique (ZerothHomotopy X) := Nonempty.some (by
    rw [unique_iff_subsingleton_and_nonempty]
    constructor <;> infer_instance)
  rw [SSet.isConnected_iff_nonempty_unique]
  exact ⟨zerothHomotopyEquiv.symm.unique⟩

end TopCat
