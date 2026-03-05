/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

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

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

variable (X : LocallyRingedSpace.{u}) {U : Opens X}

/-- The residue field of `X` at a point `x` is the residue field of the stalk of `X`
at `x`. -/
def residueField (x : X) : CommRingCat :=
  CommRingCat.of <| IsLocalRing.ResidueField (X.presheaf.stalk x)

instance (x : X) : Field (X.residueField x) :=
  inferInstaceAs% (Field (IsLocalRing.ResidueField (X.presheaf.stalk x)))

/--
If `U` is an open of `X` containing `x`, we have a canonical ring map from the sections
over `U` to the residue field of `x`.

If we interpret sections over `U` as functions of `X` defined on `U`, then this ring map
corresponds to evaluation at `x`.
-/
def evaluation (x : U) : X.presheaf.obj (op U) ⟶ X.residueField x :=
  -- TODO: make a new definition wrapping
  -- `CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk _))`?
  X.presheaf.germ U x.1 x.2 ≫ CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk _))

/-- The global evaluation map from `Γ(X, ⊤)` to the residue field at `x`. -/
def Γevaluation (x : X) : X.presheaf.obj (op ⊤) ⟶ X.residueField x :=
  X.evaluation ⟨x, show x ∈ ⊤ from trivial⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma evaluation_eq_zero_iff_notMem_basicOpen (x : U) (f : X.presheaf.obj (op U)) :
    X.evaluation x f = 0 ↔ x.val ∉ X.toRingedSpace.basicOpen f := by
  rw [X.toRingedSpace.mem_basicOpen f x.1 x.2, ← not_iff_not, not_not]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _)

lemma evaluation_ne_zero_iff_mem_basicOpen (x : U) (f : X.presheaf.obj (op U)) :
    X.evaluation x f ≠ 0 ↔ x.val ∈ X.toRingedSpace.basicOpen f := by
  simp

set_option backward.isDefEq.respectTransparency false in
lemma basicOpen_eq_bot_iff_forall_evaluation_eq_zero (f : X.presheaf.obj (op U)) :
    X.toRingedSpace.basicOpen f = ⊥ ↔ ∀ (x : U), X.evaluation x f = 0 := by
  simp only [evaluation_eq_zero_iff_notMem_basicOpen, Subtype.forall]
  exact ⟨fun h ↦ h ▸ fun a _ hc ↦ hc,
    fun h ↦ eq_bot_iff.mpr <| fun a ha ↦ h a (X.toRingedSpace.basicOpen_le f ha) ha⟩

@[simp]
lemma Γevaluation_eq_zero_iff_notMem_basicOpen (x : X) (f : X.presheaf.obj (op ⊤)) :
    X.Γevaluation x f = 0 ↔ x ∉ X.toRingedSpace.basicOpen f :=
  evaluation_eq_zero_iff_notMem_basicOpen X ⟨x, show x ∈ ⊤ by trivial⟩ f

lemma Γevaluation_ne_zero_iff_mem_basicOpen (x : X) (f : X.presheaf.obj (op ⊤)) :
    X.Γevaluation x f ≠ 0 ↔ x ∈ X.toRingedSpace.basicOpen f :=
  evaluation_ne_zero_iff_mem_basicOpen X ⟨x, show x ∈ ⊤ by trivial⟩ f

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X)

/-- If `X ⟶ Y` is a morphism of locally ringed spaces and `x` a point of `X`, we obtain
a morphism of residue fields in the other direction. -/
def residueFieldMap (x : X) : Y.residueField (f.base x) ⟶ X.residueField x :=
  CommRingCat.ofHom (IsLocalRing.ResidueField.map (f.stalkMap x).hom)

lemma residue_comp_residueFieldMap_eq_stalkMap_comp_residue (x : X) :
    CommRingCat.ofHom (IsLocalRing.residue (Y.presheaf.stalk (f.base x))) ≫
      residueFieldMap f x = f.stalkMap x ≫
      CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk x)) := by
  simp [residueFieldMap]
  rfl

@[simp]
lemma residueFieldMap_id (x : X) :
    residueFieldMap (𝟙 X) x = 𝟙 (X.residueField x) := by
  ext : 1
  simp only [residueFieldMap, stalkMap_id]
  apply IsLocalRing.ResidueField.map_id

@[simp]
lemma residueFieldMap_comp {Z : LocallyRingedSpace.{u}} (g : Y ⟶ Z) (x : X) :
    residueFieldMap (f ≫ g) x = residueFieldMap g (f.base x) ≫ residueFieldMap f x := by
  ext : 1
  simp only [residueFieldMap, stalkMap_comp]
  apply IsLocalRing.ResidueField.map_comp (Hom.stalkMap g (f.base x)).hom (Hom.stalkMap f x).hom

@[reassoc]
lemma evaluation_naturality {V : Opens Y} (x : (Opens.map f.base).obj V) :
    Y.evaluation ⟨f.base x, x.property⟩ ≫ residueFieldMap f x.val =
      f.c.app (op V) ≫ X.evaluation x := by
  dsimp only [LocallyRingedSpace.evaluation,
    LocallyRingedSpace.residueFieldMap]
  rw [Category.assoc]
  ext a
  simp only [CommRingCat.comp_apply]
  erw [IsLocalRing.ResidueField.map_residue]
  rw [LocallyRingedSpace.stalkMap_germ_apply]
  rfl

lemma evaluation_naturality_apply {V : Opens Y} (x : (Opens.map f.base).obj V)
    (a : Y.presheaf.obj (op V)) :
    residueFieldMap f x.val (Y.evaluation ⟨f.base x, x.property⟩ a) =
      X.evaluation x (f.c.app (op V) a) := by
  simpa using congrFun (congrArg (DFunLike.coe ∘ CommRingCat.Hom.hom) <|
    evaluation_naturality f x) a

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma Γevaluation_naturality (x : X) :
    Y.Γevaluation (f.base x) ≫ residueFieldMap f x =
      f.c.app (op ⊤) ≫ X.Γevaluation x :=
  evaluation_naturality f ⟨x, by simp only [Opens.map_top]; trivial⟩

lemma Γevaluation_naturality_apply (x : X) (a : Y.presheaf.obj (op ⊤)) :
    residueFieldMap f x (Y.Γevaluation (f.base x) a) =
      X.Γevaluation x (f.c.app (op ⊤) a) :=
  evaluation_naturality_apply f ⟨x, by simp only [Opens.map_top]; trivial⟩ a

end LocallyRingedSpace

end AlgebraicGeometry
