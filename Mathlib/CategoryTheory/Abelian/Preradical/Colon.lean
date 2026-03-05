/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.Abelian.Preradical.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square

/-!
# The colon construction on preradicals

Given preradicals `Φ` and `Ψ` on an abelian category `C`, this file defines their **colon** `Φ : Ψ`
in the sense of Stenström.  Following Stenström, one can realize the colon object `r : s` as the
pullback of `X ⟶ X / r X` along `s (X / r X) ⟶ X / r X`. We encode this categorically by
constructing `Φ : Ψ` as a pullback of the canonical projection
`Φ.π : 𝟭 C ⟶ Φ.quotient` along
`Φ.quotient.whiskerLeft Ψ.ι ≫ Φ.quotient.rightUnitor.hom : Φ.quotient ⋙ Ψ.r ⟶ Φ.quotient`.

## Main definitions

* `Preradical.colon Φ Ψ : Preradical C` : The colon preradical `Φ : Ψ` of Stenström.
* `toColon Φ Ψ : Φ ⟶ Φ.colon Ψ` : The canonical inclusion of the left preradical into the colon.

## Main results

* `isIso_toColon_iff` : The morphism `toColon Φ Ψ` is an isomorphism if and only if `Ψ` kills
quotients in the sense that `Φ.quotient ⋙ Ψ.r` is the zero object.

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

category_theory, preradical, colon, pullback, torsion theory
-/

@[expose] public section

namespace CategoryTheory.Abelian

open CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C]

namespace Preradical

variable (Φ Ψ : Preradical C)

/-- The cokernel of `Φ.ι : Φ.r ⟶ 𝟭 C`. -/
noncomputable abbrev quotient : C ⥤ C := cokernel Φ.ι

/-- The canonical projection `𝟭 C ⥤ Φ.quotient` where `Φ.quotient` is the cokernel of
`Φ.ι : Φ.r ⟶ 𝟭 C`. -/
noncomputable def π : 𝟭 C ⟶ Φ.quotient := cokernel.π Φ.ι
  deriving Epi

@[reassoc (attr := simp)]
lemma ι_π : Φ.ι ≫ Φ.π = 0 := cokernel.condition _

/-- The canonical cofork `CokernelCofork.ofπ Φ.π Φ.ι_π` exhibits `Φ.π : 𝟭 C ⟶ Φ.quotient` as the
cokernel of `Φ.ι : Φ.r ⟶ 𝟭 C`. -/
noncomputable def isColimitCokernelCofork : IsColimit (CokernelCofork.ofπ _ Φ.ι_π) :=
  cokernelIsCokernel _

/-- The short complex `Φ.r ⟶ 𝟭 C ⟶ Φ.quotient` in the functor category associated to a preradical
`Φ`. -/
@[simps]
noncomputable def shortComplex : ShortComplex (C ⥤ C) where
  f := Φ.ι
  g := Φ.π

instance : Mono Φ.shortComplex.f := by dsimp; infer_instance
instance : Epi Φ.shortComplex.g := by dsimp; infer_instance

lemma shortExact_shortComplex : Φ.shortComplex.ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

/-- The kernel fork `KernelFork.ofι Φ.ι Φ.ι_π` exhibits `Φ.ι : Φ.r ⟶ 𝟭 C` as the kernel
of the canonical projection `Φ.π : 𝟭 C ⟶ Φ.quotient`. -/
noncomputable def isLimitKernelFork : IsLimit (KernelFork.ofι _ Φ.ι_π) :=
  Φ.shortExact_shortComplex.fIsKernel

@[reassoc (attr := simp)]
lemma ι_π_app (X : C) : Φ.ι.app X ≫ Φ.π.app X = 0 := by
  simp [← NatTrans.comp_app]

/-- For `X : C`, the short complex `Φ.r.obj X ⟶ X ⟶ Φ.quotient.obj X` obtained by evaluating
`Φ.shortComplex` at `X`. -/
@[simps]
noncomputable def shortComplexObj (X : C) : ShortComplex C where
  f := Φ.ι.app X
  g := Φ.π.app X

instance (X : C) : Mono (Φ.shortComplexObj X).f := by dsimp; infer_instance
instance (X : C) : Epi (Φ.shortComplexObj X).g := by dsimp; infer_instance

lemma shortExact_shortComplex_obj (X : C) : (Φ.shortComplexObj X).ShortExact where
  exact :=
    (ShortComplex.ShortExact.map_of_exact Φ.shortExact_shortComplex ((evaluation C C).obj X)).exact

/-- For `X : C`, the kernel fork `KernelFork.ofι (Φ.ι.app X) (Φ.ι_π_app X)` exhibits
`Φ.ι.app X : Φ.r.obj X ⟶ X` as the kernel of the projection `Φ.π.app X : X ⟶ Φ.quotient.obj X`. -/
noncomputable def isLimitKernelForkObj (X : C) : IsLimit (KernelFork.ofι _ (Φ.ι_π_app X)) :=
  (Φ.shortExact_shortComplex_obj X).fIsKernel

/-- For `X : C`, the cokernel cofork `CokernelCofork.ofπ (Φ.π.app X) (Φ.ι_π_app X)` exhibits
`Φ.π.app X : X ⟶ Φ.quotient.obj X` as the cokernel of `Φ.ι.app X : Φ.r.obj X ⟶ X`. -/
noncomputable def isColimitCokernelCoforkObj (X : C) :
    IsColimit (CokernelCofork.ofπ _ (Φ.ι_π_app X)) :=
  (Φ.shortExact_shortComplex_obj X).gIsCokernel

open Functor

/-- The colon preradical from Stenström, defined as the pullback of `Φ.π : 𝟭 C ⟶ Φ.quotient` along
`Φ.quotient.whiskerLeft Ψ.ι ≫ Φ.quotient.rightUnitor.hom : Φ.quotient ⋙ Ψ.r ⟶ Φ.quotient` -/
noncomputable def colon : Preradical C :=
  MonoOver.mk
    (pullback.fst Φ.π (whiskerLeft Φ.quotient Ψ.ι ≫ (rightUnitor _).hom))

/-- The second projection of the pullback defining the colon preradical. -/
noncomputable def colonπ : (colon Φ Ψ).r ⟶ Φ.quotient ⋙ Ψ.r := pullback.snd _ _

instance : Epi (colonπ Φ Ψ) := by dsimp [colonπ]; infer_instance

instance (X : C) : Epi ((colonπ Φ Ψ).app X) := instEpiAppOfFunctor (Φ.colonπ Ψ) X

lemma isPullback_colon :
    IsPullback (colon Φ Ψ).ι (colonπ Φ Ψ) Φ.π
      (whiskerLeft Φ.quotient Ψ.ι ≫ (rightUnitor _).hom) :=
  .of_hasPullback _ _

lemma isPullback_colon_obj (Φ Ψ : Preradical C) (X : C) :
    IsPullback ((Φ.colon Ψ).ι.app X) ((Φ.colonπ Ψ).app X)
      (Φ.π.app X) (Ψ.ι.app (Φ.quotient.obj X)) := by
  simpa using (isPullback_colon Φ Ψ).map ((evaluation _ _).obj X)

@[reassoc]
lemma colon_ι_app_π_app (Φ Ψ : Preradical C) (X : C) :
    (Φ.colon Ψ).ι.app X ≫ Φ.π.app X = (Φ.colonπ Ψ).app X ≫ Ψ.ι.app (Φ.quotient.obj X) :=
  (isPullback_colon_obj Φ Ψ X).w

/-- There is a morphism `Φ ⟶ (Φ.colon Ψ)` induced by the universal property for the pullback
via `Φ.ι : Φ.r X ⟶ 𝟭 C` and the zero morphism `Φ.r ⟶  Φ.quotient ⋙ Ψ.r`. -/
noncomputable def toColon : Φ ⟶ Φ.colon Ψ :=
  MonoOver.homMk ((isPullback_colon Φ Ψ).lift Φ.ι 0 (by simp))

@[reassoc (attr := simp)]
lemma toColon_hom_left_colonπ :
    (toColon Φ Ψ).hom.left ≫ colonπ Φ Ψ = 0 := by
  simp [toColon]

@[reassoc (attr := simp)]
lemma toColon_hom_left_app_colonπ_app (X : C) :
    (toColon Φ Ψ).hom.left.app X ≫ (colonπ Φ Ψ).app X = 0 :=
  NatTrans.congr_app (toColon_hom_left_colonπ Φ Ψ) X

@[reassoc (attr := simp)]
lemma toColon_hom_left_app_colon_ι_app (X : C) :
    (Φ.toColon Ψ).hom.left.app X ≫ (Φ.colon Ψ).ι.app X = Φ.ι.app X := by
  rw [← NatTrans.comp_app, Over.w]

/-- For `X : C`, the morphism `(toColon Φ Ψ)` is an isomorphism if and only if
`(Ψ.r.obj (Φ.quotient.obj X))` is the zero object. -/
theorem isIso_toColon_hom_left_app_iff {Φ Ψ : Preradical C} {X : C} :
    IsIso ((toColon Φ Ψ).hom.left.app X) ↔ IsZero (Ψ.r.obj (Φ.quotient.obj X)) := by
  constructor <;> intro h
  · exact IsZero.of_epi_eq_zero ((colonπ Φ Ψ).app X)
      (zero_of_epi_comp ((toColon Φ Ψ).hom.left.app X) (by simp))
  · obtain ⟨inv, hinv⟩ :=
      KernelFork.IsLimit.lift' (Φ.isLimitKernelForkObj X) ((colon Φ Ψ).ι.app X) (by
        rw [colon_ι_app_π_app, h.eq_zero_of_tgt ((colonπ Φ Ψ).app X), zero_comp])
    dsimp at hinv
    refine ⟨inv, ?_, ?_⟩
    · simp [← cancel_mono (Φ.ι.app X), hinv]
    · simp [← cancel_mono ((Φ.colon Ψ).ι.app X), hinv]

/-- The morphism `(toColon Φ Ψ)` is an isomorphism if and only if `Φ.quotient ⋙ Ψ.r` is the zero
object. -/
theorem isIso_toColon_iff {Φ Ψ : Preradical C} :
    IsIso (toColon Φ Ψ) ↔ IsZero (Φ.quotient ⋙ Ψ.r) := by
  simpa [MonoOver.isIso_iff_isIso_hom_left, isZero_iff (Φ.quotient ⋙ Ψ.r),
    NatTrans.isIso_iff_isIso_app] using forall_congr' fun x ↦ isIso_toColon_hom_left_app_iff

end Preradical

end CategoryTheory.Abelian
