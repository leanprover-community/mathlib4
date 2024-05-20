/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.DoldKan.EquivalenceAdditive
import Mathlib.AlgebraicTopology.DoldKan.Compatibility
import Mathlib.CategoryTheory.Idempotents.SimplicialObject

#align_import algebraic_topology.dold_kan.equivalence_pseudoabelian from "leanprover-community/mathlib"@"32a7e535287f9c73f2e4d2aef306a39190f0b504"

/-!

# The Dold-Kan correspondence for pseudoabelian categories

In this file, for any idempotent complete additive category `C`,
the Dold-Kan equivalence
`Idempotents.DoldKan.Equivalence C : SimplicialObject C ≌ ChainComplex C ℕ`
is obtained. It is deduced from the equivalence
`Preadditive.DoldKan.Equivalence` between the respective idempotent
completions of these categories using the fact that when `C` is idempotent complete,
then both `SimplicialObject C` and `ChainComplex C ℕ` are idempotent complete.

The construction of `Idempotents.DoldKan.Equivalence` uses the tools
introduced in the file `Compatibility.lean`. Doing so, the functor
`Idempotents.DoldKan.N` of the equivalence is
the composition of `N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ)`
(defined in `FunctorN.lean`) and the inverse of the equivalence
`ChainComplex C ℕ ≌ Karoubi (ChainComplex C ℕ)`. The functor
`Idempotents.DoldKan.Γ` of the equivalence is by definition the functor
`Γ₀` introduced in `FunctorGamma.lean`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Idempotents

variable {C : Type*} [Category C] [Preadditive C]

namespace CategoryTheory

namespace Idempotents

namespace DoldKan

open AlgebraicTopology.DoldKan

/-- The functor `N` for the equivalence is obtained by composing
`N' : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ)` and the inverse
of the equivalence `ChainComplex C ℕ ≌ Karoubi (ChainComplex C ℕ)`. -/
@[simps!, nolint unusedArguments]
def N [IsIdempotentComplete C] [HasFiniteCoproducts C] : SimplicialObject C ⥤ ChainComplex C ℕ :=
  N₁ ⋙ (toKaroubiEquivalence _).inverse
set_option linter.uppercaseLean3 false in
#align category_theory.idempotents.dold_kan.N CategoryTheory.Idempotents.DoldKan.N

/-- The functor `Γ` for the equivalence is `Γ'`. -/
@[simps!, nolint unusedArguments]
def Γ [IsIdempotentComplete C] [HasFiniteCoproducts C] : ChainComplex C ℕ ⥤ SimplicialObject C :=
  Γ₀
#align category_theory.idempotents.dold_kan.Γ CategoryTheory.Idempotents.DoldKan.Γ

variable [IsIdempotentComplete C] [HasFiniteCoproducts C]

/-- A reformulation of the isomorphism `toKaroubi (SimplicialObject C) ⋙ N₂ ≅ N₁` -/
def isoN₁ :
    (toKaroubiEquivalence (SimplicialObject C)).functor ⋙
      Preadditive.DoldKan.equivalence.functor ≅ N₁ := toKaroubiCompN₂IsoN₁

@[simp]
lemma isoN₁_hom_app_f (X : SimplicialObject C) :
    (isoN₁.hom.app X).f = PInfty := rfl

/-- A reformulation of the canonical isomorphism
`toKaroubi (ChainComplex C ℕ) ⋙ Γ₂ ≅ Γ ⋙ toKaroubi (SimplicialObject C)`. -/
def isoΓ₀ :
    (toKaroubiEquivalence (ChainComplex C ℕ)).functor ⋙ Preadditive.DoldKan.equivalence.inverse ≅
      Γ ⋙ (toKaroubiEquivalence _).functor :=
  (functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app Γ₀

@[simp]
lemma N₂_map_isoΓ₀_hom_app_f (X : ChainComplex C ℕ) :
    (N₂.map (isoΓ₀.hom.app X)).f = PInfty := by
  ext
  apply comp_id

/-- The Dold-Kan equivalence for pseudoabelian categories given
by the functors `N` and `Γ`. It is obtained by applying the results in
`Compatibility.lean` to the equivalence `Preadditive.DoldKan.Equivalence`. -/
def equivalence : SimplicialObject C ≌ ChainComplex C ℕ :=
  Compatibility.equivalence isoN₁ isoΓ₀
#align category_theory.idempotents.dold_kan.equivalence CategoryTheory.Idempotents.DoldKan.equivalence

theorem equivalence_functor : (equivalence : SimplicialObject C ≌ _).functor = N :=
  rfl
#align category_theory.idempotents.dold_kan.equivalence_functor CategoryTheory.Idempotents.DoldKan.equivalence_functor

theorem equivalence_inverse : (equivalence : SimplicialObject C ≌ _).inverse = Γ :=
  rfl
#align category_theory.idempotents.dold_kan.equivalence_inverse CategoryTheory.Idempotents.DoldKan.equivalence_inverse

/-- The natural isomorphism `NΓ' satisfies the compatibility that is needed
for the construction of our counit isomorphism `η` -/
theorem hη :
    Compatibility.τ₀ =
      Compatibility.τ₁ isoN₁ isoΓ₀
        (N₁Γ₀ : Γ ⋙ N₁ ≅ (toKaroubiEquivalence (ChainComplex C ℕ)).functor) := by
  ext K : 3
  simp only [Compatibility.τ₀_hom_app, Compatibility.τ₁_hom_app]
  exact (N₂Γ₂_compatible_with_N₁Γ₀ K).trans (by simp )
#align category_theory.idempotents.dold_kan.hη CategoryTheory.Idempotents.DoldKan.hη

/-- The counit isomorphism induced by `N₁Γ₀` -/
@[simps!]
def η : Γ ⋙ N ≅ 𝟭 (ChainComplex C ℕ) :=
  Compatibility.equivalenceCounitIso
    (N₁Γ₀ : (Γ : ChainComplex C ℕ ⥤ _) ⋙ N₁ ≅ (toKaroubiEquivalence _).functor)
#align category_theory.idempotents.dold_kan.η CategoryTheory.Idempotents.DoldKan.η

theorem equivalence_counitIso :
    DoldKan.equivalence.counitIso = (η : Γ ⋙ N ≅ 𝟭 (ChainComplex C ℕ)) :=
  Compatibility.equivalenceCounitIso_eq hη
#align category_theory.idempotents.dold_kan.equivalence_counit_iso CategoryTheory.Idempotents.DoldKan.equivalence_counitIso

theorem hε :
    Compatibility.υ (isoN₁) =
      (Γ₂N₁ : (toKaroubiEquivalence _).functor ≅
          (N₁ : SimplicialObject C ⥤ _) ⋙ Preadditive.DoldKan.equivalence.inverse) := by
  dsimp only [isoN₁]
  ext1
  rw [← cancel_epi Γ₂N₁.inv, Iso.inv_hom_id]
  ext X : 2
  rw [NatTrans.comp_app]
  erw [compatibility_Γ₂N₁_Γ₂N₂_natTrans X]
  rw [Compatibility.υ_hom_app, Preadditive.DoldKan.equivalence_unitIso, Iso.app_inv, assoc]
  erw [← NatTrans.comp_app_assoc, IsIso.hom_inv_id]
  rw [NatTrans.id_app, id_comp, NatTrans.id_app, Γ₂N₂ToKaroubiIso_inv_app]
  dsimp only [Preadditive.DoldKan.equivalence_inverse, Preadditive.DoldKan.Γ]
  rw [← Γ₂.map_comp, Iso.inv_hom_id_app, Γ₂.map_id]
  rfl
#align category_theory.idempotents.dold_kan.hε CategoryTheory.Idempotents.DoldKan.hε

/-- The unit isomorphism induced by `Γ₂N₁`. -/
def ε : 𝟭 (SimplicialObject C) ≅ N ⋙ Γ :=
  Compatibility.equivalenceUnitIso isoΓ₀ Γ₂N₁
#align category_theory.idempotents.dold_kan.ε CategoryTheory.Idempotents.DoldKan.ε

theorem equivalence_unitIso :
    DoldKan.equivalence.unitIso = (ε : 𝟭 (SimplicialObject C) ≅ N ⋙ Γ) :=
  Compatibility.equivalenceUnitIso_eq hε
#align category_theory.idempotents.dold_kan.equivalence_unit_iso CategoryTheory.Idempotents.DoldKan.equivalence_unitIso

end DoldKan

end Idempotents

end CategoryTheory
