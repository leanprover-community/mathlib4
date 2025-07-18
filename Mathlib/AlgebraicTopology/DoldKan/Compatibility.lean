/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Equivalence

/-! Tools for compatibilities between Dold-Kan equivalences

The purpose of this file is to introduce tools which will enable the
construction of the Dold-Kan equivalence `SimplicialObject C ≌ ChainComplex C ℕ`
for a pseudoabelian category `C` from the equivalence
`Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C ℕ)` and the two
equivalences `simplicial_object C ≅ Karoubi (SimplicialObject C)` and
`ChainComplex C ℕ ≅ Karoubi (ChainComplex C ℕ)`.

It is certainly possible to get an equivalence `SimplicialObject C ≌ ChainComplex C ℕ`
using a compositions of the three equivalences above, but then neither the functor
nor the inverse would have good definitional properties. For example, it would be better
if the inverse functor of the equivalence was exactly the functor
`Γ₀ : SimplicialObject C ⥤ ChainComplex C ℕ` which was constructed in `FunctorGamma.lean`.

In this file, given four categories `A`, `A'`, `B`, `B'`, equivalences `eA : A ≅ A'`,
`eB : B ≅ B'`, `e' : A' ≅ B'`, functors `F : A ⥤ B'`, `G : B ⥤ A` equipped with certain
compatibilities, we construct successive equivalences:
- `equivalence₀` from `A` to `B'`, which is the composition of `eA` and `e'`.
- `equivalence₁` from `A` to `B'`, with the same inverse functor as `equivalence₀`,
but whose functor is `F`.
- `equivalence₂` from `A` to `B`, which is the composition of `equivalence₁` and the
inverse of `eB`:
- `equivalence` from `A` to `B`, which has the same functor `F ⋙ eB.inverse` as `equivalence₂`,
but whose inverse functor is `G`.

When extra assumptions are given, we shall also provide simplification lemmas for the
unit and counit isomorphisms of `equivalence`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/


open CategoryTheory CategoryTheory.Category Functor

namespace AlgebraicTopology

namespace DoldKan

namespace Compatibility

variable {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B'] (eA : A ≌ A')
  (eB : B ≌ B') (e' : A' ≌ B') {F : A ⥤ B'} (hF : eA.functor ⋙ e'.functor ≅ F) {G : B ⥤ A}
  (hG : eB.functor ⋙ e'.inverse ≅ G ⋙ eA.functor)

/-- A basic equivalence `A ≅ B'` obtained by composing `eA : A ≅ A'` and `e' : A' ≅ B'`. -/
@[simps! functor inverse unitIso_hom_app]
def equivalence₀ : A ≌ B' :=
  eA.trans e'

variable {eA} {e'}

/-- An intermediate equivalence `A ≅ B'` whose functor is `F` and whose inverse is
`e'.inverse ⋙ eA.inverse`. -/
@[simps! functor]
def equivalence₁ : A ≌ B' := (equivalence₀ eA e').changeFunctor hF

theorem equivalence₁_inverse : (equivalence₁ hF).inverse = e'.inverse ⋙ eA.inverse :=
  rfl

/-- The counit isomorphism of the equivalence `equivalence₁` between `A` and `B'`. -/
@[simps!]
def equivalence₁CounitIso : (e'.inverse ⋙ eA.inverse) ⋙ F ≅ 𝟭 B' :=
  calc
    (e'.inverse ⋙ eA.inverse) ⋙ F ≅ (e'.inverse ⋙ eA.inverse) ⋙ eA.functor ⋙ e'.functor :=
      isoWhiskerLeft _ hF.symm
    _ ≅ e'.inverse ⋙ (eA.inverse ⋙ eA.functor ⋙ e'.functor) := associator _ _ _
    _ ≅ e'.inverse ⋙ (eA.inverse ⋙ eA.functor) ⋙ e'.functor :=
      isoWhiskerLeft _ (associator _ _ _).symm
    _ ≅ e'.inverse ⋙ 𝟭 _ ⋙ e'.functor := isoWhiskerLeft _ (isoWhiskerRight eA.counitIso _)
    _ ≅ e'.inverse ⋙ e'.functor := isoWhiskerLeft _ (leftUnitor _)
    _ ≅ 𝟭 B' := e'.counitIso

theorem equivalence₁CounitIso_eq : (equivalence₁ hF).counitIso = equivalence₁CounitIso hF := by
  ext Y
  simp [equivalence₁, equivalence₀]

/-- The unit isomorphism of the equivalence `equivalence₁` between `A` and `B'`. -/
@[simps!]
def equivalence₁UnitIso : 𝟭 A ≅ F ⋙ e'.inverse ⋙ eA.inverse :=
  calc
    𝟭 A ≅ eA.functor ⋙ eA.inverse := eA.unitIso
    _ ≅ eA.functor ⋙ 𝟭 A' ⋙ eA.inverse := isoWhiskerLeft _ (leftUnitor _).symm
    _ ≅ eA.functor ⋙ (e'.functor ⋙ e'.inverse) ⋙ eA.inverse :=
      isoWhiskerLeft _ (isoWhiskerRight e'.unitIso _)
    _ ≅ eA.functor ⋙ (e'.functor ⋙ e'.inverse ⋙ eA.inverse) :=
      isoWhiskerLeft _ (associator _ _ _)
    _ ≅ (eA.functor ⋙ e'.functor) ⋙ e'.inverse ⋙ eA.inverse := (associator _ _ _).symm
    _ ≅ F ⋙ e'.inverse ⋙ eA.inverse := isoWhiskerRight hF _

theorem equivalence₁UnitIso_eq : (equivalence₁ hF).unitIso = equivalence₁UnitIso hF := by
  ext X
  simp [equivalence₁]

/-- An intermediate equivalence `A ≅ B` obtained as the composition of `equivalence₁` and
the inverse of `eB : B ≌ B'`. -/
@[simps! functor]
def equivalence₂ : A ≌ B :=
  (equivalence₁ hF).trans eB.symm

theorem equivalence₂_inverse :
    (equivalence₂ eB hF).inverse = eB.functor ⋙ e'.inverse ⋙ eA.inverse :=
  rfl

/-- The counit isomorphism of the equivalence `equivalence₂` between `A` and `B`. -/
@[simps!]
def equivalence₂CounitIso : (eB.functor ⋙ e'.inverse ⋙ eA.inverse) ⋙ F ⋙ eB.inverse ≅ 𝟭 B :=
  calc
    (eB.functor ⋙ e'.inverse ⋙ eA.inverse) ⋙ F ⋙ eB.inverse
      ≅ eB.functor ⋙ (e'.inverse ⋙ eA.inverse) ⋙ F ⋙ eB.inverse := associator _ _ _
    _ ≅ eB.functor ⋙ ((e'.inverse ⋙ eA.inverse) ⋙ F) ⋙ eB.inverse :=
      isoWhiskerLeft _ (associator _ _ _).symm
    _ ≅ eB.functor ⋙ 𝟭 _ ⋙ eB.inverse :=
      isoWhiskerLeft _ (isoWhiskerRight (equivalence₁CounitIso hF) _)
    _ ≅ eB.functor ⋙ eB.inverse := isoWhiskerLeft _ (leftUnitor _)
    _ ≅ 𝟭 B := eB.unitIso.symm

theorem equivalence₂CounitIso_eq :
    (equivalence₂ eB hF).counitIso = equivalence₂CounitIso eB hF := by
  ext Y'
  simp [equivalence₂, equivalence₁CounitIso_eq]

/-- The unit isomorphism of the equivalence `equivalence₂` between `A` and `B`. -/
@[simps!]
def equivalence₂UnitIso : 𝟭 A ≅ (F ⋙ eB.inverse) ⋙ eB.functor ⋙ e'.inverse ⋙ eA.inverse :=
  calc
    𝟭 A ≅ F ⋙ e'.inverse ⋙ eA.inverse := equivalence₁UnitIso hF
    _ ≅ F ⋙ 𝟭 B' ⋙ e'.inverse ⋙ eA.inverse :=
      isoWhiskerLeft _ (leftUnitor _).symm
    _ ≅ F ⋙ (eB.inverse ⋙ eB.functor) ⋙ e'.inverse ⋙ eA.inverse :=
      isoWhiskerLeft _ (isoWhiskerRight eB.counitIso.symm _)
    _ ≅ (F ⋙ eB.inverse ⋙ eB.functor) ⋙ e'.inverse ⋙ eA.inverse :=
      (associator _ _ _).symm
    _ ≅ ((F ⋙ eB.inverse) ⋙ eB.functor) ⋙ e'.inverse ⋙ eA.inverse :=
      isoWhiskerRight (associator _ _ _).symm _
    _ ≅ (F ⋙ eB.inverse) ⋙ eB.functor ⋙ e'.inverse ⋙ eA.inverse :=
      associator _ _ _

theorem equivalence₂UnitIso_eq : (equivalence₂ eB hF).unitIso = equivalence₂UnitIso eB hF := by
  ext X
  simp [equivalence₂, equivalence₁]

variable {eB}

/-- The equivalence `A ≅ B` whose functor is `F ⋙ eB.inverse` and
whose inverse is `G : B ≅ A`. -/
@[simps! inverse]
def equivalence : A ≌ B :=
  ((equivalence₂ eB hF).changeInverse
    (calc eB.functor ⋙ e'.inverse ⋙ eA.inverse ≅
        (eB.functor ⋙ e'.inverse) ⋙ eA.inverse := (associator _ _ _).symm
    _ ≅ (G ⋙ eA.functor) ⋙ eA.inverse := isoWhiskerRight hG _
    _ ≅ G ⋙ eA.functor ⋙ eA.inverse := associator _ _ _
    _ ≅ G ⋙ 𝟭 A := isoWhiskerLeft _ eA.unitIso.symm
    _ ≅ G := G.rightUnitor))

theorem equivalence_functor : (equivalence hF hG).functor = F ⋙ eB.inverse :=
  rfl

/-- The isomorphism `eB.functor ⋙ e'.inverse ⋙ e'.functor ≅ eB.functor` deduced
from the counit isomorphism of `e'`. -/
@[simps! hom_app]
def τ₀ : eB.functor ⋙ e'.inverse ⋙ e'.functor ≅ eB.functor :=
  calc
    eB.functor ⋙ e'.inverse ⋙ e'.functor ≅ eB.functor ⋙ 𝟭 _ := isoWhiskerLeft _ e'.counitIso
    _ ≅ eB.functor := Functor.rightUnitor _

/-- The isomorphism `eB.functor ⋙ e'.inverse ⋙ e'.functor ≅ eB.functor` deduced
from the isomorphisms `hF : eA.functor ⋙ e'.functor ≅ F`,
`hG : eB.functor ⋙ e'.inverse ≅ G ⋙ eA.functor` and the datum of
an isomorphism `η : G ⋙ F ≅ eB.functor`. -/
@[simps! hom_app]
def τ₁ (η : G ⋙ F ≅ eB.functor) : eB.functor ⋙ e'.inverse ⋙ e'.functor ≅ eB.functor :=
  calc
    eB.functor ⋙ e'.inverse ⋙ e'.functor ≅ (eB.functor ⋙ e'.inverse) ⋙ e'.functor :=
        (associator _ _ _).symm
    _ ≅ (G ⋙ eA.functor) ⋙ e'.functor := isoWhiskerRight hG _
    _ ≅ G ⋙ eA.functor ⋙ e'.functor := associator _ _ _
    _ ≅ G ⋙ F := isoWhiskerLeft _ hF
    _ ≅ eB.functor := η

variable (η : G ⋙ F ≅ eB.functor)

/-- The counit isomorphism of `equivalence`. -/
@[simps!]
def equivalenceCounitIso : G ⋙ F ⋙ eB.inverse ≅ 𝟭 B :=
  calc
    G ⋙ F ⋙ eB.inverse ≅ (G ⋙ F) ⋙ eB.inverse := (associator _ _ _).symm
    _ ≅ eB.functor ⋙ eB.inverse := isoWhiskerRight η _
    _ ≅ 𝟭 B := eB.unitIso.symm

variable {η hF hG}

theorem equivalenceCounitIso_eq (hη : τ₀ = τ₁ hF hG η) :
    (equivalence hF hG).counitIso = equivalenceCounitIso η := by
  ext1; apply NatTrans.ext; ext Y
  dsimp [equivalence]
  simp only [comp_id, id_comp, Functor.map_comp, equivalence₂CounitIso_eq,
    equivalence₂CounitIso_hom_app, assoc, equivalenceCounitIso_hom_app]
  simp only [equivalence₂_inverse, comp_obj, ← τ₀_hom_app, hη, τ₁_hom_app, ←
    eB.inverse.map_comp_assoc]
  rw [hF.inv.naturality_assoc, hF.inv.naturality_assoc]
  congr 2
  simp only [← e'.functor.map_comp_assoc]
  simp only [Functor.comp_map, Equivalence.fun_inv_map, comp_obj, id_obj, map_comp, assoc]
  simp only [← e'.functor.map_comp_assoc]
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, comp_obj, comp_id,
    Equivalence.functor_unit_comp, map_id, id_comp]

variable (hF)

/-- The isomorphism `eA.functor ≅ F ⋙ e'.inverse` deduced from the
unit isomorphism of `e'` and the isomorphism `hF : eA.functor ⋙ e'.functor ≅ F`. -/
@[simps!]
def υ : eA.functor ≅ F ⋙ e'.inverse :=
  calc
    eA.functor ≅ eA.functor ⋙ 𝟭 A' := (rightUnitor _).symm
    _ ≅ eA.functor ⋙ e'.functor ⋙ e'.inverse := isoWhiskerLeft _ e'.unitIso
    _ ≅ (eA.functor ⋙ e'.functor) ⋙ e'.inverse := (associator _ _ _).symm
    _ ≅ F ⋙ e'.inverse := isoWhiskerRight hF _

variable (ε : eA.functor ≅ F ⋙ e'.inverse) (hG)

/-- The unit isomorphism of `equivalence`. -/
@[simps!]
def equivalenceUnitIso : 𝟭 A ≅ (F ⋙ eB.inverse) ⋙ G :=
  calc
    𝟭 A ≅ eA.functor ⋙ eA.inverse := eA.unitIso
    _ ≅ (F ⋙ e'.inverse) ⋙ eA.inverse := isoWhiskerRight ε _
    _ ≅ F ⋙ e'.inverse ⋙ eA.inverse := associator _ _ _
    _ ≅ F ⋙ 𝟭 B' ⋙ e'.inverse ⋙ eA.inverse := isoWhiskerLeft _ (leftUnitor _).symm
    _ ≅ F ⋙ (eB.inverse ⋙ eB.functor) ⋙ e'.inverse ⋙ eA.inverse :=
      isoWhiskerLeft _ (isoWhiskerRight eB.counitIso.symm _)
    _ ≅ (F ⋙ eB.inverse ⋙ eB.functor) ⋙ e'.inverse ⋙ eA.inverse := (associator _ _ _).symm
    _ ≅ ((F ⋙ eB.inverse) ⋙ eB.functor) ⋙ e'.inverse ⋙ eA.inverse :=
      isoWhiskerRight (associator _ _ _).symm _
    _ ≅ (F ⋙ eB.inverse) ⋙ eB.functor ⋙ e'.inverse ⋙ eA.inverse := associator _ _ _
    _ ≅ (F ⋙ eB.inverse) ⋙ (eB.functor ⋙ e'.inverse) ⋙ eA.inverse :=
      isoWhiskerLeft _ (associator _ _ _).symm
    _ ≅ (F ⋙ eB.inverse) ⋙ (G ⋙ eA.functor) ⋙ eA.inverse :=
      isoWhiskerLeft _ (isoWhiskerRight hG _)
    _ ≅ ((F ⋙ eB.inverse) ⋙ G ⋙ eA.functor) ⋙ eA.inverse := (associator _ _ _).symm
    _ ≅ (((F ⋙ eB.inverse) ⋙ G) ⋙ eA.functor) ⋙ eA.inverse :=
      isoWhiskerRight (associator _ _ _).symm _
    _ ≅ ((F ⋙ eB.inverse) ⋙ G) ⋙ eA.functor ⋙ eA.inverse := associator _ _ _
    _ ≅ ((F ⋙ eB.inverse) ⋙ G) ⋙ 𝟭 A := isoWhiskerLeft _ eA.unitIso.symm
    _ ≅ (F ⋙ eB.inverse) ⋙ G := rightUnitor _

variable {ε hF hG}

theorem equivalenceUnitIso_eq (hε : υ hF = ε) :
    (equivalence hF hG).unitIso = equivalenceUnitIso hG ε := by
  ext1; apply NatTrans.ext; ext X
  dsimp [equivalence]
  simp only [assoc, comp_id, equivalenceUnitIso_hom_app, equivalence₂_inverse, Functor.comp_obj,
    id_comp, equivalence₂UnitIso_eq eB hF, equivalence₂UnitIso_hom_app,
    ← eA.inverse.map_comp_assoc, assoc, ← hε, υ_hom_app]

end Compatibility

end DoldKan

end AlgebraicTopology
