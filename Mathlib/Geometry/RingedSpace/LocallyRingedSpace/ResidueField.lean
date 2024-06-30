/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!

# Residue fields of points

Any point `x` of a locally ringed space `X` comes with a natural residue field, namely the residue
field of the stalk at `x`. Moreover, for every open subset of `X` containing `x`, we have a
canonical evaluation map from `Γ(X, U)` to the residue field of `X` at `x`.

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

instance (x : X) : Field (X.residueField x) :=
  inferInstanceAs <| Field (LocalRing.ResidueField (X.stalk x))

/--
If `U` is an open of `X` containing `x`, we have a canonical ring map from the sections
over `U` to the residue field of `x`.

If we interpret sections over `U` as functions of `X` defined on `U`, then this ring map
corresponds to evaluation at `x`.
-/
def evaluation (x : U) : X.presheaf.obj (op U) ⟶ X.residueField x :=
  X.presheaf.germ x ≫ LocalRing.residue _

/-- The global evaluation map from `Γ(X, ⊤)` to the residue field at `x`. -/
def Γevaluation (x : X) : X.presheaf.obj (op ⊤) ⟶ X.residueField x :=
  X.evaluation ⟨x, show x ∈ ⊤ from trivial⟩

@[simp]
lemma evaluation_eq_zero_iff_not_mem_basicOpen (x : U) (f : X.presheaf.obj (op U)) :
    X.evaluation x f = 0 ↔ x.val ∉ X.toRingedSpace.basicOpen f := by
  rw [X.toRingedSpace.mem_basicOpen f x, ← not_iff_not, not_not]
  exact (LocalRing.residue_ne_zero_iff_isUnit _)

lemma evaluation_ne_zero_iff_mem_basicOpen (x : U) (f : X.presheaf.obj (op U)) :
    X.evaluation x f ≠ 0 ↔ x.val ∈ X.toRingedSpace.basicOpen f := by
  simp

@[simp]
lemma Γevaluation_eq_zero_iff_not_mem_basicOpen (x : X) (f : X.presheaf.obj (op ⊤)) :
    X.Γevaluation x f = 0 ↔ x ∉ X.toRingedSpace.basicOpen f :=
  evaluation_eq_zero_iff_not_mem_basicOpen X ⟨x, show x ∈ ⊤ by trivial⟩ f

lemma Γevaluation_ne_zero_iff_mem_basicOpen (x : X) (f : X.presheaf.obj (op ⊤)) :
    X.Γevaluation x f ≠ 0 ↔ x ∈ X.toRingedSpace.basicOpen f :=
  evaluation_ne_zero_iff_mem_basicOpen X ⟨x, show x ∈ ⊤ by trivial⟩ f

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)

/-- If `X ⟶ Y` is a morphism of locally ringed spaces and `x` a point of `X`, we obtain
a morphism of residue fields in the other direction. -/
def evaluationMap (x : X) : Y.residueField (f.val.base x) ⟶ X.residueField x :=
  LocalRing.ResidueField.map (LocallyRingedSpace.stalkMap f x)

@[reassoc]
lemma evaluation_naturality {V : Opens Y} (x : (Opens.map f.1.base).obj V) :
    Y.evaluation ⟨f.val.base x, x.property⟩ ≫ evaluationMap f x.val =
      f.val.c.app (op V) ≫ X.evaluation x := by
  dsimp only [LocallyRingedSpace.evaluation,
    LocallyRingedSpace.evaluationMap]
  rw [Category.assoc]
  ext a
  simp only [comp_apply]
  erw [LocalRing.ResidueField.map_residue, PresheafedSpace.stalkMap_germ'_apply]
  rfl

lemma evaluation_naturality_apply {V : Opens Y} (x : (Opens.map f.1.base).obj V)
    (a : Y.presheaf.obj (op V)) :
    evaluationMap f x.val (Y.evaluation ⟨f.val.base x, x.property⟩ a) =
      X.evaluation x (f.val.c.app (op V) a) := by
  simpa using congrFun (congrArg DFunLike.coe <| evaluation_naturality f x) a

@[reassoc]
lemma Γevaluation_naturality (x : X) :
    Y.Γevaluation (f.val.base x) ≫ evaluationMap f x =
      f.val.c.app (op ⊤) ≫ X.Γevaluation x :=
  evaluation_naturality f ⟨x, by simp only [Opens.map_top]; trivial⟩

lemma Γevaluation_naturality_apply (x : X) (a : Y.presheaf.obj (op ⊤)) :
    LocallyRingedSpace.evaluationMap f x (Y.Γevaluation (f.val.base x) a) =
      X.Γevaluation x (f.val.c.app (op ⊤) a) :=
  evaluation_naturality_apply f ⟨x, by simp only [Opens.map_top]; trivial⟩ a
