/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!

# Residue fields of points

Any point `x` of a locally ringed space `X` comes with a natural residue field, namely the residue
field of the stalk at `x`. Moreover, for every open subset of `X` containing `x`, we have a canonical
evaluation map from `Γ(X, U)` to the residue field of `X` at `x`.

## Main definitions

The following are in the `AlgebraicGeometry.LocallyRingedSpace` namespace:

- `residueField`: the residue field of the stalk at `x`.
- `evaluation`: for open subsets `U` of `X` containing `x`, the evaluation map from sections over
  `U` to the residue field at `x`.
- `evaluationMap`: a morphism of locally ringed spaces induces a morphism, i.e. extension, of
  residue fields.

-/

universe u

open CategoryTheory TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

variable (X : LocallyRingedSpace.{u}) {U : Opens X}

/-- The residue field of `X` at a point `x` is the residue field of the stalk of `X`
at `x`. -/
def residueField (x : X) : CommRingCat :=
  CommRingCat.of <| LocalRing.ResidueField (X.stalk x)

lemma residueField_isField (x : X) : IsField (X.residueField x) :=
  Field.toIsField (LocalRing.ResidueField (X.stalk x))

/--
If `U` is an open of `X` containing `x`, we have a canonical ring map from the sections
over `U` to the residue field of `x`.

If we interpret sections over `U` as functions of `X` defined on `U`, then this ring map
corresponds to evaluation at `x`.
-/
def evaluation (x : U) :
    X.presheaf.obj (op U) ⟶ X.residueField x :=
  X.presheaf.germ x ≫ LocalRing.residue _

lemma evaluation_eq_zero_iff_mem_maximalIdeal (x : U) (f : X.presheaf.obj (op U)) :
    X.evaluation x f = 0 ↔ (X.presheaf.germ x) f ∈ LocalRing.maximalIdeal (X.stalk x) :=
  LocalRing.residue_eq_zero_iff _

lemma evaluation_ne_zero_iff_isUnit {U : Opens X} (x : U) (f : X.presheaf.obj (op U)) :
    X.evaluation x f ≠ 0 ↔ IsUnit ((X.presheaf.germ x) f) :=
  LocalRing.residue_ne_zero_iff_isUnit _

/-- The global evaluation map from `Γ(X, ⊤)` to the residue field at `x`. -/
def Γevaluation (x : X) : LocallyRingedSpace.Γ.obj (op X) ⟶ X.residueField x :=
  X.evaluation ⟨x, show x ∈ ⊤ from trivial⟩

lemma Γevaluation_eq_zero_iff_mem_maximalIdeal (x : X) (f : LocallyRingedSpace.Γ.obj (op X)) :
    X.Γevaluation x f = 0 ↔
      (X.presheaf.germ ⟨x, show x ∈ ⊤ by trivial⟩) f ∈ LocalRing.maximalIdeal (X.stalk x) :=
  LocalRing.residue_eq_zero_iff _

lemma Γevaluation_ne_zero_iff_isUnit (x : U) (f : X.presheaf.obj (op U)) :
    X.evaluation x f ≠ 0 ↔ IsUnit ((X.presheaf.germ x) f) :=
  LocalRing.residue_ne_zero_iff_isUnit _

lemma mem_basicOpen_iff_evaluation_ne_zero (f : X.presheaf.obj (op U)) (x : U) :
    x.val ∈ X.toRingedSpace.basicOpen f ↔ X.evaluation x f ≠ 0 := by
  rw [X.toRingedSpace.mem_basicOpen f x]
  exact (X.evaluation_ne_zero_iff_isUnit x f).symm

lemma mem_basicOpen_iff_Γevaluation_ne_zero (f : X.presheaf.obj (op ⊤)) (x : X) :
    x ∈ X.toRingedSpace.basicOpen f ↔ X.Γevaluation x f ≠ 0 :=
  mem_basicOpen_iff_evaluation_ne_zero X f ⟨x, trivial⟩

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)

/-- If `X ⟶ Y` is a morphism of locally ringed spaces and `x` a point of `X`, we obtain
a morphism of residue fields in the other direction. -/
def evaluationMap (x : X) : Y.residueField (f.val.base x) ⟶ X.residueField x :=
  LocalRing.ResidueField.map (LocallyRingedSpace.stalkMap f x)

lemma evaluation_naturality {V : Opens Y} (x : f ⁻¹ᵁ V) :
    Y.evaluation ⟨f.val.base x, x.property⟩ ≫ evaluationMap f x.val =
      f.val.c.app (op V) ≫ X.evaluation x := by
  dsimp only [LocallyRingedSpace.evaluation,
    LocallyRingedSpace.evaluationMap]
  rw [Category.assoc]
  ext a
  simp only [comp_apply]
  erw [LocalRing.ResidueField.map_residue, PresheafedSpace.stalkMap_germ'_apply]
  rfl

lemma evaluation_naturality_apply {V : Opens Y} (x :  f⁻¹ᵁ V) (a : Y.presheaf.obj (op V)) :
    evaluationMap f x.val (Y.evaluation ⟨f.val.base x, x.property⟩ a) =
      X.evaluation x (f.val.c.app (op V) a) := by
  simpa using congrFun (congrArg DFunLike.coe <| evaluation_naturality f x) a

lemma Γevaluation_naturality (x : X) :
    Y.Γevaluation (f.val.base x) ≫ evaluationMap f x =
      f.val.c.app (op ⊤) ≫ X.Γevaluation x :=
  evaluation_naturality f ⟨x, show x ∈ f ⁻¹ᵁ ⊤ by simp only [Opens.map_top]; trivial⟩

lemma Γevaluation_naturality_apply (x : X) (a : Y.presheaf.obj (op ⊤)) :
    LocallyRingedSpace.evaluationMap f x (Y.Γevaluation (f.val.base x) a) =
      X.Γevaluation x (f.val.c.app (op ⊤) a) :=
  evaluation_naturality_apply f ⟨x, show x ∈ f ⁻¹ᵁ ⊤ by simp only [Opens.map_top]; trivial⟩ a
