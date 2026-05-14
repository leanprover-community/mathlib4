/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Transport rigid structures over a monoidal equivalence.
-/

@[expose] public section


namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- Given candidate data for an exact pairing,
which is sent by a faithful monoidal functor to an exact pairing,
the equations holds automatically. -/
@[implicit_reducible]
def ExactPairing.ofFaithful [F.Faithful] {X Y : C} (eval : Y ⊗ X ⟶ 𝟙_ C)
    (coeval : 𝟙_ C ⟶ X ⊗ Y) [ExactPairing (F.obj X) (F.obj Y)]
    (map_eval : F.map eval = (δ F _ _) ≫ ε_ _ _ ≫ ε F)
    (map_coeval : F.map coeval = (η F) ≫ η_ _ _ ≫ μ F _ _) : ExactPairing X Y where
  evaluation' := eval
  coevaluation' := coeval
  evaluation_coevaluation' :=
    F.map_injective <| by
      simp [map_eval, map_coeval, Functor.Monoidal.map_whiskerLeft,
        Functor.Monoidal.map_whiskerRight]
  coevaluation_evaluation' :=
    F.map_injective <| by
      simp [map_eval, map_coeval, Functor.Monoidal.map_whiskerLeft,
        Functor.Monoidal.map_whiskerRight]

/-- Given a pair of objects which are sent by a fully faithful functor to a pair of objects
with an exact pairing, we get an exact pairing.
-/
@[implicit_reducible]
noncomputable def ExactPairing.ofFullyFaithful [F.Full] [F.Faithful] (X Y : C)
    [ExactPairing (F.obj X) (F.obj Y)] : ExactPairing X Y :=
  .ofFaithful F (F.preimage (δ F _ _ ≫ ε_ _ _ ≫ (ε F)))
    (F.preimage (η F ≫ η_ _ _ ≫ μ F _ _)) (by simp) (by simp)

@[deprecated (since := "2025-10-17")] alias exactPairingOfFaithful := ExactPairing.ofFaithful

@[deprecated (since := "2025-10-17")]
alias exactPairingOfFullyFaithful := ExactPairing.ofFullyFaithful

variable {F}
variable {G : D ⥤ C} (adj : F ⊣ G) [F.IsEquivalence]

noncomputable section

/-- Pull back a left dual along an equivalence. -/
@[implicit_reducible]
def hasLeftDualOfEquivalence (X : C) [HasLeftDual (F.obj X)] :
    HasLeftDual X where
  leftDual := G.obj (ᘁ(F.obj X))
  exact := by
    letI := exactPairingCongrLeft (X := F.obj (G.obj ᘁ(F.obj X)))
      (X' := ᘁ(F.obj X)) (Y := F.obj X) (adj.toEquivalence.counitIso.app ᘁ(F.obj X))
    apply ExactPairing.ofFullyFaithful F

/-- Pull back a right dual along an equivalence. -/
@[implicit_reducible]
def hasRightDualOfEquivalence (X : C) [HasRightDual (F.obj X)] :
    HasRightDual X where
  rightDual := G.obj ((F.obj X)ᘁ)
  exact := by
    letI := exactPairingCongrRight (X := F.obj X) (Y := F.obj (G.obj (F.obj X)ᘁ))
      (Y' := (F.obj X)ᘁ) (adj.toEquivalence.counitIso.app (F.obj X)ᘁ)
    apply ExactPairing.ofFullyFaithful F

/-- Pull back a left rigid structure along an equivalence. -/
@[implicit_reducible]
def leftRigidCategoryOfEquivalence [LeftRigidCategory D] :
    LeftRigidCategory C where leftDual X := hasLeftDualOfEquivalence adj X

/-- Pull back a right rigid structure along an equivalence. -/
@[implicit_reducible]
def rightRigidCategoryOfEquivalence [RightRigidCategory D] :
    RightRigidCategory C where rightDual X := hasRightDualOfEquivalence adj X

/-- Pull back a rigid structure along an equivalence. -/
@[implicit_reducible]
def rigidCategoryOfEquivalence [RigidCategory D] : RigidCategory C where
  leftDual X := hasLeftDualOfEquivalence adj X
  rightDual X := hasRightDualOfEquivalence adj X

end

end CategoryTheory
