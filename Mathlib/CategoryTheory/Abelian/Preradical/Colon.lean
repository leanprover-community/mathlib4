/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.Abelian.Preradical.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

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

/-- The canonical kernel fork `KernelFork.ofι Φ.ι Φ.ι_π` exhibits `Φ.ι : Φ.r ⟶ 𝟭 C` as the kernel
of the canonical projection `Φ.π : 𝟭 C ⟶ Φ.quotient`. -/
noncomputable def isLimitKernelFork : IsLimit (KernelFork.ofι _ Φ.ι_π) :=
  Φ.shortExact_shortComplex.fIsKernel

open Functor

/-- The colon preradical from Stenström, defined as the pullback of `Φ.π : 𝟭 C ⟶ Φ.quotient` along
`Φ.quotient.whiskerLeft Ψ.ι ≫ Φ.quotient.rightUnitor.hom : Φ.quotient ⋙ Ψ.r ⟶ Φ.quotient` -/
noncomputable def colon : Preradical C :=
  MonoOver.mk
    (pullback.fst Φ.π (whiskerLeft Φ.quotient Ψ.ι ≫ (rightUnitor _).hom))

/-- The second projection of the pullback defining the colon preradical. -/
noncomputable def colonπ : (colon Φ Ψ).r ⟶ Φ.quotient ⋙ Ψ.r := pullback.snd _ _

lemma isPullback_colon :
    IsPullback (colon Φ Ψ).ι (colonπ Φ Ψ) Φ.π
      (whiskerLeft Φ.quotient Ψ.ι ≫ (rightUnitor _).hom) :=
  .of_hasPullback _ _

/-- There is a morphism `Φ ⟶ (Φ.colon Ψ)` induced by the universal property for the pullback
via `Φ.ι : Φ.r X ⟶ 𝟭 C` and the zero morphism `Φ.r ⟶  Φ.quotient ⋙ Ψ.r`. -/
noncomputable def toColon : Φ ⟶ Φ.colon Ψ :=
  MonoOver.homMk ((isPullback_colon Φ Ψ).lift Φ.ι 0 (by simp))

/-- The morphism `(toColon Φ Ψ)` is an isomorphism if and only if `Φ.quotient ⋙ Ψ.r` is the zero
object. -/
theorem isIso_toColon_iff : IsIso (toColon Φ Ψ) ↔ IsZero (Φ.quotient ⋙ Ψ.r) := by
  haveI : Epi (colonπ Φ Ψ) := by dsimp [colonπ]; infer_instance
  let g := (Φ.quotient.whiskerLeft Ψ.ι ≫ (rightUnitor _).hom)
  constructor <;> intro h
  · exact IsZero.of_epi_eq_zero
      (pullback.snd Φ.π g)
      (zero_of_epi_comp (toColon Φ Ψ).hom.left ((isPullback_colon Φ Ψ).lift_snd Φ.ι 0 (by simp)))
  · refine (MonoOver.isIso_iff_isIso_hom_left (Φ.toColon Ψ)).mpr ?_
    have hsnd : pullback.snd Φ.π g = 0 := IsZero.eq_zero_of_tgt h _
    have hfst : (pullback.fst Φ.π g) ≫ Φ.π = 0 := by
      rw [pullback.condition, hsnd, zero_comp]
    let s : KernelFork Φ.π := (KernelFork.ofι (colon Φ Ψ).ι hfst)
    let inv : (colon Φ Ψ).r ⟶ Φ.r := Φ.isLimitKernelFork.lift s
    have hfac : inv ≫ Φ.ι = (colon Φ Ψ).ι := by
      simpa using Φ.isLimitKernelFork.fac s WalkingParallelPair.zero
    refine ⟨inv, ?_, ?_⟩
    · apply (cancel_mono Φ.ι).mp
      simp [hfac]
    · apply (cancel_mono (Φ.colon Ψ).ι).mp
      simp [hfac]

end Preradical

end CategoryTheory.Abelian
