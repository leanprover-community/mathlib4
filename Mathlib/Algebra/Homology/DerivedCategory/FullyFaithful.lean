/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.SingleHomology

/-! # The fully faithful embedding of the abelian category in its derived category

In this file, we show that for any `n : ℤ`, the functor
`singleFunctor C n : C ⥤ DerivedCategory C` is fully faithful.

-/

@[expose] public section

universe w v u

open CategoryTheory

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The canonical isomorphism
`DerivedCategory.singleFunctor C n ⋙ DerivedCategory.homologyFunctor C n ≅ 𝟭 C` -/
noncomputable def singleFunctorCompHomologyFunctorIso (n : ℤ) :
    singleFunctor C n ⋙ homologyFunctor C n ≅ 𝟭 C :=
  Functor.isoWhiskerRight ((SingleFunctors.evaluation _ _ n).mapIso
    (singleFunctorsPostcompQIso C)) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (homologyFunctorFactors C n) ≪≫
      (HomologicalComplex.homologyFunctorSingleIso _ _ _)

instance (n : ℤ) : (singleFunctor C n).Faithful where
  map_injective {_ _ f₁ f₂} h := by
    have eq₁ := NatIso.naturality_1 (singleFunctorCompHomologyFunctorIso C n) f₁
    have eq₂ := NatIso.naturality_1 (singleFunctorCompHomologyFunctorIso C n) f₂
    dsimp at eq₁ eq₂
    rw [← eq₁, ← eq₂, h]

set_option backward.isDefEq.respectTransparency false in
instance (n : ℤ) : (singleFunctor C n).Full where
  map_surjective {A B} f := by
    change Q.obj ((CochainComplex.singleFunctor C n).obj A) ⟶
      Q.obj ((CochainComplex.singleFunctor C n).obj B) at f
    suffices ∃ f', f = Q.map f' by
      obtain ⟨f', rfl⟩ := this
      obtain ⟨g, rfl⟩ := (CochainComplex.singleFunctor C n).map_surjective f'
      exact ⟨g, rfl⟩
    obtain ⟨X, _, _, s, _, g, rfl⟩ := right_fac_of_isStrictlyLE_of_isStrictlyGE n n f
    obtain ⟨A₀, ⟨e⟩⟩ := X.exists_iso_single n
    have ⟨φ, hφ⟩ := (CochainComplex.singleFunctor C n).map_surjective (e.inv ≫ s)
    have : IsIso ((singleFunctor C n).map φ) := by
      change IsIso (Q.map ((CochainComplex.singleFunctor C n).map φ))
      rw [hφ, Functor.map_comp]
      infer_instance
    have : IsIso φ := (NatIso.isIso_map_iff (singleFunctorCompHomologyFunctorIso C n) φ).1
        (by dsimp; infer_instance)
    have : IsIso (e.inv ≫ s) := by rw [← hφ]; infer_instance
    have : IsIso s := IsIso.of_isIso_comp_left e.inv s
    exact ⟨inv s ≫ g, by simp⟩

noncomputable instance (n : ℤ) : (CochainComplex.singleFunctor C n ⋙ Q).Full :=
  inferInstanceAs (singleFunctor C n).Full

noncomputable instance (n : ℤ) : (CochainComplex.singleFunctor C n ⋙ Q).Faithful :=
  inferInstanceAs (singleFunctor C n).Faithful

end DerivedCategory
