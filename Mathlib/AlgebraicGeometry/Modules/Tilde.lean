/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel, Jujian Zhang, Weihong Xu,
  Andrew Yang
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.AlgebraicGeometry.StructureSheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures

/-!

# Construction of M^~

Given any commutative ring `R` and `R`-module `M`, we construct the sheaf `M^~` of `𝒪_SpecR`-modules
such that `M^~(U)` is the set of dependent functions that are locally fractions.

## Main definitions
* `ModuleCat.tilde` : `M^~` as a sheaf of `𝒪_{Spec R}`-modules.
-/

@[expose] public section

universe u

open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

namespace ModuleCat

/--
`M^~` as a sheaf of `𝒪_{Spec R}`-modules
-/
noncomputable def tilde : (Spec <| .of R).Modules where
  val := moduleStructurePresheaf R M
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    (structureSheafInType R M).2

/--
This is `M^~` as a sheaf of `R`-modules.
-/
noncomputable def tildeInModuleCat :
    TopCat.Presheaf (ModuleCat R) (PrimeSpectrum.Top R) :=
  structurePresheafInModuleCat R M

namespace Tilde

@[simp]
theorem res_apply (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U)
    (s : (tildeInModuleCat M).obj (op U)) (x : V) :
    ((tildeInModuleCat M).map i.op s).1 x = (s.1 (i x) :) :=
  rfl

lemma smul_section_apply (r : R) (U : Opens (PrimeSpectrum.Top R))
    (s : (tildeInModuleCat M).obj (op U)) (x : U) :
    (r • s).1 x = r • (s.1 x) := rfl

lemma smul_stalk_no_nonzero_divisor {x : PrimeSpectrum R}
    (r : x.asIdeal.primeCompl) (st : (tildeInModuleCat M).stalk x) (hst : r.1 • st = 0) :
    st = 0 :=
  Limits.Concrete.colimit_no_zero_smul_divisor _ _ _
    ⟨op ⟨PrimeSpectrum.basicOpen r.1, r.2⟩, fun U i s hs ↦ Subtype.ext <| funext fun pt ↦
    LocalizedModule.eq_zero_of_smul_eq_zero _ (i.unop pt).2 _
    (by simpa [← smul_section_apply] using congr(($hs).1 pt))⟩ _ hst

/--
If `U` is an open subset of `Spec R`, this is the morphism of `R`-modules from `M` to
`M^~(U)`.
-/
noncomputable def toOpen (U : Opens (PrimeSpectrum.Top R)) :
    ModuleCat.of R M ⟶ (tildeInModuleCat M).obj (op U) :=
  ModuleCat.ofHom (StructureSheaf.toOpenₗ R M U)


@[simp]
theorem toOpen_res (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U) :
    toOpen M U ≫ (tildeInModuleCat M).map i.op = toOpen M V :=
  rfl

noncomputable
instance (x : PrimeSpectrum.Top R) : Module R ↑(TopCat.Presheaf.stalk M.tilde.presheaf x) :=
  inferInstanceAs (Module R ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x))

/--
If `x` is a point of `Spec R`, this is the morphism of `R`-modules from `M` to the stalk of
`M^~` at `x`.
-/
noncomputable def toStalk (x : PrimeSpectrum.Top R) :
    ModuleCat.of R M ⟶ ModuleCat.of R ↑(TopCat.Presheaf.stalk M.tilde.presheaf x) :=
  ModuleCat.ofHom (StructureSheaf.toStalkₗ ..)

instance (x : PrimeSpectrum.Top R) :
    IsLocalizedModule x.asIdeal.primeCompl (toStalk M x).hom :=
  inferInstanceAs (IsLocalizedModule x.asIdeal.primeCompl (StructureSheaf.toStalkₗ ..))

end Tilde

end ModuleCat
