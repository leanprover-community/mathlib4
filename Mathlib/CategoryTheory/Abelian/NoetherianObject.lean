/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.NoetherianObject
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.Order.OrderIsoNat

/-!
# Noetherian objects in an abelian category form a Serre class

-/

universe v u

open CategoryTheory ZeroObject

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace Abelian

variable [Abelian C] {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (p : X ⟶ X') (q : Y ⟶ Y') (fac : f ≫ q = p ≫ f')

noncomputable def image.map : Abelian.image f ⟶ Abelian.image f' :=
  kernel.map _ _ q (cokernel.map _ _ p q fac) (by simp)

@[reassoc (attr := simp)]
lemma image.map_ι :
    image.map f f' p q fac ≫ Abelian.image.ι f' = Abelian.image.ι f ≫ q := by
  simp [image.map]

end Abelian

variable {X Y : C}

@[simps (config := .lemmasOnly)]
noncomputable def MonoOver.abelianImage [Abelian C] (f : X ⟶ Y) :
    MonoOver X ⥤ MonoOver Y where
  obj A := MonoOver.mk' (Abelian.image.ι (A.1.hom ≫ f))
  map {A B} g := MonoOver.homMk (Abelian.image.map _ _ g.left (𝟙 _) (by simp))

noncomputable def Subobject.abelianImage [Abelian C] (f : X ⟶ Y) :
    Subobject X ⥤ Subobject Y :=
  lower (MonoOver.abelianImage f)

lemma Subobject.mk_abelianImageι_eq [Abelian C]
    (f : X ⟶ Y) {Z : C} (π : X ⟶ Z) [Epi π] (ι : Z ⟶ Y) [Mono ι] (fac : π ≫ ι = f):
    mk (Abelian.image.ι f) = mk ι := by
  let g : Z ⟶ Abelian.image f := kernel.lift _ ι (by
    rw [← cancel_epi π, reassoc_of% fac, cokernel.condition, comp_zero])
  have fac₁ : g ≫ Abelian.image.ι f = ι := by simp [g]
  have fac₂ : π ≫ g = Abelian.factorThruImage f := by
    rw [← cancel_mono (Abelian.image.ι f), Category.assoc, fac₁, kernel.lift_ι, fac]
  have := mono_of_mono_fac fac₁
  have := epi_of_epi_fac fac₂
  have := isIso_of_mono_of_epi g
  exact (mk_eq_mk_of_comm _ _ (asIso g) fac₁).symm

lemma Subobject.abelianImage_obj_mk [Abelian C] (f : X ⟶ Y)
    {A B : C} (i : A ⟶ X) [Mono i] (π : A ⟶ B) [Epi π] (ι : B ⟶ Y) [Mono ι]
    (fac : i ≫ f = π ≫ ι) :
    (abelianImage f).obj (.mk i) = .mk ι := by
  exact Subobject.mk_abelianImageι_eq (i ≫ f) π ι fac.symm

lemma Subobject.abelianImage_obj_pullback_obj_of_epi [Abelian C] (p : X ⟶ Y) [Epi p]
    (A : Subobject Y) : (abelianImage p).obj ((pullback p).obj A) = A := by
  revert A
  apply Subobject.ind
  intro A f _
  exact Subobject.abelianImage_obj_mk p (pullback.snd f p) (pullback.fst f p) f
    pullback.condition.symm

lemma Subobject.pullback_obj_injective [Abelian C] (p : X ⟶ Y) [Epi p] :
    Function.Injective (Subobject.pullback p).obj := by
  intro A B h
  rw [← abelianImage_obj_pullback_obj_of_epi p A, h, abelianImage_obj_pullback_obj_of_epi]

namespace Abelian

variable [Abelian C]

lemma isNoetherianObject_of_epi (p : X ⟶ Y) [Epi p] [IsNoetherianObject X] :
    IsNoetherianObject Y := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject
    ⟨_, (Subobject.pullback p).monotone.comp f.2⟩
  exact ⟨n, fun m hm ↦ Subobject.pullback_obj_injective p (hn m hm)⟩

instance : (isNoetherianObject (C := C)).IsClosedUnderQuotients where
  prop_of_epi f _ hX := by
    rw [← isNoetherianObject.is_iff] at hX ⊢
    exact isNoetherianObject_of_epi f

section

variable (S : ShortComplex C)

@[simps]
noncomputable def fromMonoOverOfShortComplex :
    MonoOver S.X₂ ⥤ ShortComplex C where
  obj A :=
    { X₁ := pullback A.1.hom S.f
      X₂ := A.1.left
      X₃ := Abelian.image (A.1.hom ≫ S.g)
      f := pullback.fst _ _
      g := Abelian.factorThruImage _
      zero := by ext; simp [pullback.condition_assoc] }
  map {A B} φ :=
    { τ₁ := ((MonoOver.pullback S.f).map φ).left
      τ₂ := φ.left
      τ₃ := ((MonoOver.abelianImage S.g).map φ).left
      comm₁₂ := by simp [MonoOver.pullback, MonoOver.forget]
      comm₂₃ := by ext; simp [MonoOver.abelianImage] }

variable {S}

lemma shortExact_fromMonoOverOfShortComplex_obj
    (hS : S.ShortExact) (A : MonoOver S.X₂) :
    ((fromMonoOverOfShortComplex S).obj A).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  dsimp [fromMonoOverOfShortComplex]
  exact
    { exact := by
        rw [ShortComplex.exact_iff_exact_up_to_refinements]
        intro Y x₂ hx₂
        dsimp at x₂ hx₂ ⊢
        rw [← cancel_mono (Abelian.image.ι _), Category.assoc,
          kernel.lift_ι, zero_comp] at hx₂
        obtain ⟨A', π, _, x₁, hx₁⟩  :=
          hS.exact.exact_up_to_refinements (x₂ ≫ A.obj.hom) (by simpa using hx₂)
        exact ⟨A', π, inferInstance, pullback.lift (π ≫ x₂) x₁ (by simpa),
          by simp⟩}

end

lemma isIso_monoOver_iff_of_shortExact
    {S : ShortComplex C} (hS : S.ShortExact)
    {A B : MonoOver S.X₂} (φ : A ⟶ B) :
    IsIso φ ↔ IsIso ((MonoOver.pullback S.f).map φ) ∧
      IsIso ((MonoOver.abelianImage S.g).map φ):= by
  constructor
  · intro
    constructor <;> infer_instance
  · rintro ⟨h₁, h₃⟩
    rw [MonoOver.isIso_iff_isIso_left] at h₁ h₃ ⊢
    let ψ := ((fromMonoOverOfShortComplex S).map φ)
    have : IsIso ψ.τ₁ := h₁
    have : IsIso ψ.τ₃ := h₃
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ ψ
      (shortExact_fromMonoOverOfShortComplex_obj hS _)
      (shortExact_fromMonoOverOfShortComplex_obj hS _)

lemma isNoetherianObject_of_shortExact {S : ShortComplex C}
    (hS : S.ShortExact) (h₁ : IsNoetherianObject S.X₁)
    (h₃ : IsNoetherianObject S.X₃) :
    IsNoetherianObject S.X₂ := by
  rw [isNoetherianObject_iff_isEventuallyConstant]
  intro F₂
  obtain ⟨n₁, hn₁⟩ := isEventuallyConstant_of_isNoetherianObject
    (F₂ ⋙ MonoOver.pullback S.f)
  obtain ⟨n₃, hn₃⟩ := isEventuallyConstant_of_isNoetherianObject
    (F₂ ⋙ MonoOver.abelianImage S.g)
  refine ⟨max n₁ n₃, fun m hm ↦ ?_⟩
  rw [isIso_monoOver_iff_of_shortExact hS]
  exact ⟨hn₁.isIso_map _ (homOfLE (le_max_left n₁ n₃)),
    hn₃.isIso_map _ (homOfLE (le_max_right n₁ n₃))⟩

instance : (isNoetherianObject (C := C)).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := by
    rw [← isNoetherianObject.is_iff] at h₁ h₃ ⊢
    exact isNoetherianObject_of_shortExact hS h₁ h₃

instance : (isNoetherianObject (C := C)).IsSerreClass where

end Abelian

end CategoryTheory
