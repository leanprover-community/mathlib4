/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Homotopy.TopCat.Path

/-!
# Singular homology in degree 0


-/

@[expose] public section

universe w v v' u u'

open CategoryTheory Limits AlgebraicTopology Simplicial

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C]

namespace TopCat

variable (X : TopCat.{w}) (R : C)

section

variable {X}

set_option backward.isDefEq.respectTransparency false in
noncomputable def toSSetObj₁Equiv :
    toSSet.obj X _⦋1⦌ ≃ (I ⟶ X) :=
  (toSSetObjEquiv _ _).trans
    { toFun f := ofHom (f.comp (toContinuousMap TopCat.stdSimplexHomeomorphI.symm))
      invFun f := f.hom.comp TopCat.stdSimplexHomeomorphI
      left_inv _ := by aesop
      right_inv _ := by aesop }

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma toSSetObj₁Equiv_apply_zero (s : toSSet.obj X _⦋1⦌) :
    X.toSSetObj₁Equiv s 0 = toSSetObj₀Equiv ((toSSet.obj X).δ 1 s) := by
  dsimp [toSSetObj₀Equiv, toSSetObj₁Equiv]
  congr 1
  rw [Subsingleton.elim default (stdSimplex.vertex 0)]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma toSSetObj₁Equiv_apply_one (s : toSSet.obj X _⦋1⦌) :
    X.toSSetObj₁Equiv s 1 = toSSetObj₀Equiv ((toSSet.obj X).δ 0 s) := by
  dsimp [toSSetObj₀Equiv, toSSetObj₁Equiv]
  congr 1
  rw [Subsingleton.elim default (stdSimplex.vertex 0)]
  simp

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

noncomputable def toSSetObjEdgeEquiv {x y : X} :
    SSet.Edge (toSSetObj₀Equiv.symm x) (toSSetObj₀Equiv.symm y) ≃ X.Path x y where
  toFun e := { hom := toSSetObj₁Equiv e.edge }
  invFun p := SSet.Edge.mk (toSSetObj₁Equiv.symm p.hom)
  left_inv _ := by aesop
  right_inv _ := by aesop

end

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

noncomputable def singularHomology₀Iso :
    ((singularHomologyFunctor C 0).obj R).obj X ≅ ∐ (fun (_ : ZerothHomotopy X) ↦ R) :=
  SSet.homology₀Iso _ _ ≪≫
    (sigmaConst.obj R).mapIso (zerothHomotopyEquiv X).toIso.symm

noncomputable def singularHomology₀ε :
    ((singularHomologyFunctor C 0).obj R).obj X ⟶ R :=
  SSet.homology₀ε _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma singularHomology₀Iso_sigma_desc_id :
    (singularHomology₀Iso X R).hom ≫ Sigma.desc (fun _ ↦ 𝟙 R) = singularHomology₀ε X R := by
  dsimp only [singularHomology₀Iso, singularHomology₀ε, SSet.homology₀ε]
  cat_disch

instance [PathConnectedSpace X] : Subsingleton (ZerothHomotopy X) :=
  (pathConnectedSpace_iff_zerothHomotopy.1 inferInstance).2

instance [PathConnectedSpace X] : Nonempty (ZerothHomotopy X) :=
  (pathConnectedSpace_iff_zerothHomotopy.1 inferInstance).1

instance [PathConnectedSpace X] : (toSSet.obj X).IsConnected := by
  letI : Unique (ZerothHomotopy X) := Nonempty.some (by
    rw [unique_iff_subsingleton_and_nonempty]
    constructor <;> infer_instance)
  rw [SSet.isConnected_iff_nonempty_unique]
  exact ⟨(zerothHomotopyEquiv X).symm.unique⟩

instance [PathConnectedSpace X] : IsIso (X.singularHomology₀ε R) :=
  inferInstanceAs (IsIso ((toSSet.obj X).homology₀ε R))

end TopCat
