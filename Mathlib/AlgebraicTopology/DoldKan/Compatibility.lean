/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.compatibility
! leanprover-community/mathlib commit 160f568dcf772b2477791c844fc605f2f91f73d1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Equivalence

/-! Tools for compatibilities between Dold-Kan equivalences

The purpose of this file is to introduce tools which will enable the
construction of the Dold-Kan equivalence `simplicial_object C ≌ chain_complex C ℕ`
for a pseudoabelian category `C` from the equivalence
`karoubi (simplicial_object C) ≌ karoubi (chain_complex C ℕ)` and the two
equivalences `simplicial_object C ≅ karoubi (simplicial_object C)` and
`chain_complex C ℕ ≅ karoubi (chain_complex C ℕ)`.

It is certainly possible to get an equivalence `simplicial_object C ≌ chain_complex C ℕ`
using a compositions of the three equivalences above, but then neither the functor
nor the inverse would have good definitional properties. For example, it would be better
if the inverse functor of the equivalence was exactly the functor
`Γ₀ : simplicial_object C ⥤ chain_complex C ℕ` which was constructed in `functor_gamma.lean`.

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
unit and counit isomorphisms of `equivalence`. (TODO)

-/


open CategoryTheory CategoryTheory.Category

namespace AlgebraicTopology

namespace DoldKan

namespace Compatibility

variable {A A' B B' : Type _} [Category A] [Category A'] [Category B] [Category B'] (eA : A ≌ A')
  (eB : B ≌ B') (e' : A' ≌ B') {F : A ⥤ B'} (hF : eA.Functor ⋙ e'.Functor ≅ F) {G : B ⥤ A}
  (hG : eB.Functor ⋙ e'.inverse ≅ G ⋙ eA.Functor)

/-- A basic equivalence `A ≅ B'` obtained by composing `eA : A ≅ A'` and `e' : A' ≅ B'`. -/
@[simps Functor inverse unit_iso_hom_app]
def equivalence₀ : A ≌ B' :=
  eA.trans e'
#align algebraic_topology.dold_kan.compatibility.equivalence₀ AlgebraicTopology.DoldKan.Compatibility.equivalence₀

include hF

variable {eA} {e'}

/-- An intermediate equivalence `A ≅ B'` whose functor is `F` and whose inverse is
`e'.inverse ⋙ eA.inverse`. -/
@[simps Functor]
def equivalence₁ : A ≌ B' :=
  letI : is_equivalence F :=
    is_equivalence.of_iso hF (is_equivalence.of_equivalence (equivalence₀ eA e'))
  F.as_equivalence
#align algebraic_topology.dold_kan.compatibility.equivalence₁ AlgebraicTopology.DoldKan.Compatibility.equivalence₁

theorem equivalence₁_inverse : (equivalence₁ hF).inverse = e'.inverse ⋙ eA.inverse :=
  rfl
#align algebraic_topology.dold_kan.compatibility.equivalence₁_inverse AlgebraicTopology.DoldKan.Compatibility.equivalence₁_inverse

/-- The counit isomorphism of the equivalence `equivalence₁` between `A` and `B'`. -/
@[simps]
def equivalence₁CounitIso : (e'.inverse ⋙ eA.inverse) ⋙ F ≅ 𝟭 B' :=
  calc
    (e'.inverse ⋙ eA.inverse) ⋙ F ≅ (e'.inverse ⋙ eA.inverse) ⋙ eA.Functor ⋙ e'.Functor :=
      isoWhiskerLeft _ hF.symm
    _ ≅ e'.inverse ⋙ (eA.inverse ⋙ eA.Functor) ⋙ e'.Functor := (Iso.refl _)
    _ ≅ e'.inverse ⋙ 𝟭 _ ⋙ e'.Functor := (isoWhiskerLeft _ (isoWhiskerRight eA.counitIso _))
    _ ≅ e'.inverse ⋙ e'.Functor := (Iso.refl _)
    _ ≅ 𝟭 B' := e'.counitIso
    
#align algebraic_topology.dold_kan.compatibility.equivalence₁_counit_iso AlgebraicTopology.DoldKan.Compatibility.equivalence₁CounitIso

theorem equivalence₁CounitIso_eq : (equivalence₁ hF).counitIso = equivalence₁CounitIso hF :=
  by
  ext Y
  dsimp [equivalence₀, equivalence₁, is_equivalence.inverse, is_equivalence.of_equivalence]
  simp only [equivalence₁_counit_iso_hom_app, CategoryTheory.Functor.map_id, comp_id]
#align algebraic_topology.dold_kan.compatibility.equivalence₁_counit_iso_eq AlgebraicTopology.DoldKan.Compatibility.equivalence₁CounitIso_eq

/-- The unit isomorphism of the equivalence `equivalence₁` between `A` and `B'`. -/
@[simps]
def equivalence₁UnitIso : 𝟭 A ≅ F ⋙ e'.inverse ⋙ eA.inverse :=
  calc
    𝟭 A ≅ eA.Functor ⋙ eA.inverse := eA.unitIso
    _ ≅ eA.Functor ⋙ 𝟭 A' ⋙ eA.inverse := (Iso.refl _)
    _ ≅ eA.Functor ⋙ (e'.Functor ⋙ e'.inverse) ⋙ eA.inverse :=
      (isoWhiskerLeft _ (isoWhiskerRight e'.unitIso _))
    _ ≅ (eA.Functor ⋙ e'.Functor) ⋙ e'.inverse ⋙ eA.inverse := (Iso.refl _)
    _ ≅ F ⋙ e'.inverse ⋙ eA.inverse := isoWhiskerRight hF _
    
#align algebraic_topology.dold_kan.compatibility.equivalence₁_unit_iso AlgebraicTopology.DoldKan.Compatibility.equivalence₁UnitIso

theorem equivalence₁UnitIso_eq : (equivalence₁ hF).unitIso = equivalence₁UnitIso hF :=
  by
  ext X
  dsimp [equivalence₀, equivalence₁, nat_iso.hcomp, is_equivalence.of_equivalence]
  simp only [id_comp, assoc, equivalence₁_unit_iso_hom_app]
#align algebraic_topology.dold_kan.compatibility.equivalence₁_unit_iso_eq AlgebraicTopology.DoldKan.Compatibility.equivalence₁UnitIso_eq

include eB

/-- An intermediate equivalence `A ≅ B` obtained as the composition of `equivalence₁` and
the inverse of `eB : B ≌ B'`. -/
@[simps Functor]
def equivalence₂ : A ≌ B :=
  (equivalence₁ hF).trans eB.symm
#align algebraic_topology.dold_kan.compatibility.equivalence₂ AlgebraicTopology.DoldKan.Compatibility.equivalence₂

theorem equivalence₂_inverse :
    (equivalence₂ eB hF).inverse = eB.Functor ⋙ e'.inverse ⋙ eA.inverse :=
  rfl
#align algebraic_topology.dold_kan.compatibility.equivalence₂_inverse AlgebraicTopology.DoldKan.Compatibility.equivalence₂_inverse

/-- The counit isomorphism of the equivalence `equivalence₂` between `A` and `B`. -/
@[simps]
def equivalence₂CounitIso : (eB.Functor ⋙ e'.inverse ⋙ eA.inverse) ⋙ F ⋙ eB.inverse ≅ 𝟭 B :=
  calc
    (eB.Functor ⋙ e'.inverse ⋙ eA.inverse) ⋙ F ⋙ eB.inverse ≅
        eB.Functor ⋙ (e'.inverse ⋙ eA.inverse ⋙ F) ⋙ eB.inverse :=
      Iso.refl _
    _ ≅ eB.Functor ⋙ 𝟭 _ ⋙ eB.inverse :=
      (isoWhiskerLeft _ (isoWhiskerRight (equivalence₁CounitIso hF) _))
    _ ≅ eB.Functor ⋙ eB.inverse := (Iso.refl _)
    _ ≅ 𝟭 B := eB.unitIso.symm
    
#align algebraic_topology.dold_kan.compatibility.equivalence₂_counit_iso AlgebraicTopology.DoldKan.Compatibility.equivalence₂CounitIso

theorem equivalence₂CounitIso_eq : (equivalence₂ eB hF).counitIso = equivalence₂CounitIso eB hF :=
  by
  ext Y'
  dsimp [equivalence₂, iso.refl]
  simp only [equivalence₁_counit_iso_eq, equivalence₂_counit_iso_hom_app,
    equivalence₁_counit_iso_hom_app, functor.map_comp, assoc]
#align algebraic_topology.dold_kan.compatibility.equivalence₂_counit_iso_eq AlgebraicTopology.DoldKan.Compatibility.equivalence₂CounitIso_eq

/-- The unit isomorphism of the equivalence `equivalence₂` between `A` and `B`. -/
@[simps]
def equivalence₂UnitIso : 𝟭 A ≅ (F ⋙ eB.inverse) ⋙ eB.Functor ⋙ e'.inverse ⋙ eA.inverse :=
  calc
    𝟭 A ≅ F ⋙ e'.inverse ⋙ eA.inverse := equivalence₁UnitIso hF
    _ ≅ F ⋙ 𝟭 B' ⋙ e'.inverse ⋙ eA.inverse := (Iso.refl _)
    _ ≅ F ⋙ (eB.inverse ⋙ eB.Functor) ⋙ e'.inverse ⋙ eA.inverse :=
      (isoWhiskerLeft _ (isoWhiskerRight eB.counitIso.symm _))
    _ ≅ (F ⋙ eB.inverse) ⋙ eB.Functor ⋙ e'.inverse ⋙ eA.inverse := Iso.refl _
    
#align algebraic_topology.dold_kan.compatibility.equivalence₂_unit_iso AlgebraicTopology.DoldKan.Compatibility.equivalence₂UnitIso

theorem equivalence₂UnitIso_eq : (equivalence₂ eB hF).unitIso = equivalence₂UnitIso eB hF :=
  by
  ext X
  dsimp [equivalence₂]
  simpa only [equivalence₂_unit_iso_hom_app, equivalence₁_unit_iso_eq,
    equivalence₁_unit_iso_hom_app, assoc, nat_iso.cancel_nat_iso_hom_left]
#align algebraic_topology.dold_kan.compatibility.equivalence₂_unit_iso_eq AlgebraicTopology.DoldKan.Compatibility.equivalence₂UnitIso_eq

variable {eB}

include hG

/-- The equivalence `A ≅ B` whose functor is `F ⋙ eB.inverse` and
whose inverse is `G : B ≅ A`. -/
@[simps inverse]
def equivalence : A ≌ B :=
  letI : is_equivalence G :=
    by
    refine' is_equivalence.of_iso _ (is_equivalence.of_equivalence (equivalence₂ eB hF).symm)
    calc
      eB.functor ⋙ e'.inverse ⋙ eA.inverse ≅ (eB.functor ⋙ e'.inverse) ⋙ eA.inverse := iso.refl _
      _ ≅ (G ⋙ eA.functor) ⋙ eA.inverse := (iso_whisker_right hG _)
      _ ≅ G ⋙ 𝟭 A := (iso_whisker_left _ eA.unit_iso.symm)
      _ ≅ G := functor.right_unitor G
      
  G.as_equivalence.symm
#align algebraic_topology.dold_kan.compatibility.equivalence AlgebraicTopology.DoldKan.Compatibility.equivalence

theorem equivalence_functor : (equivalence hF hG).Functor = F ⋙ eB.inverse :=
  rfl
#align algebraic_topology.dold_kan.compatibility.equivalence_functor AlgebraicTopology.DoldKan.Compatibility.equivalence_functor

end Compatibility

end DoldKan

end AlgebraicTopology

