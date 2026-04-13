/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.ForgetCorepresentable
public import Mathlib.CategoryTheory.Generator.Preadditive
public import Mathlib.CategoryTheory.Presentable.StrongGenerator

/-!
# The category of modules is locally finitely presentable

For any commutative ring `R`, the category `ModuleCat R` of `R`-modules is locally
finitely presentable. The proof uses the Gabriel-Ulmer characterization
(Adamek-Rosicky Theorem 1.11): the free rank-1 module `R` is a small strong
generator of `ℵ₀`-presentable objects.

## Main results

- `ModuleCat.isStrongGenerator_singleton_self`: the singleton `{R}` is a strong
  generator of `ModuleCat R`.
- `ModuleCat.isCardinalPresentable_self`: the free rank-1 module `R` is `ℵ₀`-presentable.
- `ModuleCat.isLocallyFinitelyPresentable`: `ModuleCat R` is locally finitely
  presentable.

## References

* [Adamek, J. and Rosicky, J., *Locally presentable and accessible
  categories*][Adamek_Rosicky_1994]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

attribute [local instance] fact_isRegular_aleph0

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- For `m : M`, the `R`-linear map `R → M` sending `r` to `r • m`.
Maps from the free rank-1 module biject with elements via
`LinearMap.ringLmapEquivSelf`. -/
noncomputable abbrev elementMap (M : ModuleCat.{u} R) (m : M) :
    ModuleCat.of R R ⟶ M :=
  ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf R R M).symm m)

/-- The forgetful functor `ModuleCat R → Type` preserves filtered colimits,
hence is `ℵ₀`-accessible. -/
instance :
    (forget (ModuleCat.{u} R)).IsCardinalAccessible (ℵ₀ : Cardinal.{u}) where
  preservesColimitOfShape J _ _ :=
    haveI : IsFiltered J := isFiltered_of_isCardinalFiltered J ℵ₀
    inferInstance

/-- The free rank-1 module `R` is `ℵ₀`-presentable: `Hom(R, -)` preserves
filtered colimits because it identifies with the forgetful functor. -/
instance isCardinalPresentable_self :
    IsCardinalPresentable (ModuleCat.of R R) (ℵ₀ : Cardinal.{u}) :=
  Functor.isCardinalAccessible_of_natIso (coyonedaObjIsoForget R).symm ℵ₀

/-- The singleton property `{R}` (the free rank-1 module) is a strong generator
of `ModuleCat R`: maps `R → M` detect morphism equality (separating) and
suffice to upgrade a mono to an iso (strong). -/
lemma isStrongGenerator_singleton_self :
    (ObjectProperty.singleton (ModuleCat.of R R)).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨?_, ?_⟩
  · -- Separating: maps R → M detect morphism equality
    rw [Preadditive.isSeparating_iff]
    intro X Y f hf; ext x; change f.hom x = 0
    have h := hf (ModuleCat.of R R) (by simp) (elementMap R X x)
    have h1 :
        (elementMap R X x ≫ f).hom (1 : R) = f.hom x := by
      simp [elementMap, LinearMap.ringLmapEquivSelf_symm_apply, one_smul]
    rw [h] at h1; simpa using h1.symm
  · -- Strong: mono + all R-maps lift => iso
    intro X Y i _ hsurj
    have : Epi i := by
      rw [ModuleCat.epi_iff_surjective]; intro y
      obtain ⟨g, hg⟩ := hsurj (ModuleCat.of R R) (by simp) (elementMap R Y y)
      exact ⟨(ConcreteCategory.hom g) 1, by
        have := congr_arg
          (fun f => (ConcreteCategory.hom f) (1 : R)) hg
        simp only [ConcreteCategory.comp_apply] at this
        rw [this]; simp [elementMap,
          LinearMap.ringLmapEquivSelf_symm_apply, one_smul]⟩
    exact isIso_of_mono_of_epi i

/-- **`ModuleCat R` is locally finitely presentable**
(Gabriel-Ulmer, Adamek-Rosicky 1.11).

The free rank-1 module `R` is a small, strong generator of
`ℵ₀`-presentable objects. -/
instance isLocallyFinitelyPresentable :
    IsLocallyFinitelyPresentable.{u} (ModuleCat.{u} R) := by
  change IsCardinalLocallyPresentable (ModuleCat.{u} R) ℵ₀
  rw [IsCardinalLocallyPresentable.iff_exists_isStrongGenerator]
  refine ⟨ObjectProperty.singleton (ModuleCat.of R R), inferInstance,
    isStrongGenerator_singleton_self R, ?_⟩
  exact ObjectProperty.singleton_le_iff.mpr (isCardinalPresentable_self R)

end ModuleCat
