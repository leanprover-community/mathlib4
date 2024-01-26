/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.LeftExact
/-!
# Locally injective and locally surjective morphisms of presheaves


-/

universe w v' v u' u

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D] [ConcreteCategory.{w} D]
  (J : GrothendieckTopology C)

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

@[simp]
lemma NatTrans.naturality_apply {F G : C ⥤ D} (φ : F ⟶ G) {X Y : C}
    (f : X ⟶ Y) (x : F.obj X) :
    φ.app Y (F.map f x) = G.map f (φ.app X x) := by
  simpa only [Functor.map_comp] using congr_fun ((forget D).congr_map (φ.naturality f)) x

namespace Presheaf

variable {F₁ F₂ F₃ : Cᵒᵖ ⥤ D} (φ : F₁ ⟶ F₂) (ψ : F₂ ⟶ F₃)

class LocallyInjective : Prop where
  locally_injective {X : Cᵒᵖ} (x y : F₁.obj X) (h : φ.app X x = φ.app X y) :
    ∃ (S : Sieve X.unop) (_ : S ∈ J X.unop),
      ∀ {Y : C} (f : Y ⟶ X.unop) (_ : S f), F₁.map f.op x = F₁.map f.op y

lemma locallyInjective_of_injective (hφ : ∀ (X : Cᵒᵖ), Function.Injective (φ.app X)) :
    LocallyInjective J φ where
  locally_injective {X} x y h := ⟨⊤, J.top_mem _, fun f _ => hφ _ (by simp [h])⟩

instance [IsIso φ] :
    LocallyInjective J φ := locallyInjective_of_injective J φ (fun X => by
  apply Function.Bijective.injective
  rw [← isIso_iff_bijective]
  change IsIso ((forget D).map (φ.app X))
  infer_instance)

section

variable [hφ : LocallyInjective J φ]
  {X : Cᵒᵖ} (x y : F₁.obj X) (h : φ.app X x = φ.app X y)

noncomputable def sieveOfLocallyInjective : Sieve X.unop :=
  (hφ.locally_injective x y h).choose

lemma sieveOfLocallyInjective_mem :
    sieveOfLocallyInjective J φ x y h ∈ J X.unop :=
  (hφ.locally_injective x y h).choose_spec.choose

lemma map_apply_eq_of_locallyInjective
    {Y : C} (f : Y ⟶ X.unop) (hf : sieveOfLocallyInjective J φ x y h f) :
    F₁.map f.op x = F₁.map f.op y :=
  (hφ.locally_injective x y h).choose_spec.choose_spec f hf

end

class LocallySurjective : Prop where
  locally_surjective {X : Cᵒᵖ} (x : F₂.obj X) :
    ∃ (S : Sieve X.unop) (_ : S ∈ J X.unop),
      ∀ {Y : C} (f : Y ⟶ X.unop) (_ : S f), ∃ (y : F₁.obj (op Y)),
        φ.app (op Y) y = F₂.map f.op x

lemma locallySurjective_of_surjective (hφ : ∀ (X : Cᵒᵖ), Function.Surjective (φ.app X)) :
    LocallySurjective J φ where
  locally_surjective _ := ⟨⊤, J.top_mem _, fun _ _ => hφ _ _⟩

instance [IsIso φ] : LocallySurjective J φ := locallySurjective_of_surjective J φ (fun X => by
  apply Function.Bijective.surjective
  rw [← isIso_iff_bijective]
  change IsIso ((forget D).map (φ.app X))
  infer_instance)

section

variable [hφ : LocallySurjective J φ]
  {X : Cᵒᵖ} (x : F₂.obj X)

noncomputable def sieveOfLocallySurjective : Sieve X.unop :=
  (hφ.locally_surjective x).choose

lemma sieveOfLocallySurjective_mem : sieveOfLocallySurjective J φ x ∈ J X.unop :=
  (hφ.locally_surjective x).choose_spec.choose

variable {Y : C} (f : Y ⟶ X.unop) (hf : sieveOfLocallySurjective J φ x f)

noncomputable def localPreimage : F₁.obj (op Y) :=
  ((hφ.locally_surjective x).choose_spec.choose_spec f hf).choose

@[simp]
lemma app_apply_localPreimage :
    φ.app _ (localPreimage J φ x f hf) = F₂.map f.op x :=
  ((hφ.locally_surjective x).choose_spec.choose_spec f hf).choose_spec

end

instance locallyInjective_forget [LocallyInjective J φ] :
    LocallyInjective J (whiskerRight φ (forget D)) where
  locally_injective x y h :=
    ⟨_, sieveOfLocallyInjective_mem J φ x y h, map_apply_eq_of_locallyInjective J φ x y h⟩

instance locallySurjective_forget [LocallySurjective J φ] :
    LocallySurjective J (whiskerRight φ (forget D)) where
  locally_surjective x :=
    ⟨_, sieveOfLocallySurjective_mem J φ x,
      fun f hf => ⟨localPreimage J φ x f hf, app_apply_localPreimage J φ x f hf⟩⟩

instance locallyInjective_comp [LocallyInjective J φ] [LocallyInjective J ψ] :
    LocallyInjective J (φ ≫ ψ) where
  locally_injective {X} x y h := by
    let S := sieveOfLocallyInjective J ψ (φ.app _ x) (φ.app _ y) (by simpa using h)
    have hS : S ∈ J X.unop := sieveOfLocallyInjective_mem J ψ (φ.app _ x) (φ.app _ y) (by simpa using h)
    have hS' : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X.unop⦄ (_ : S f),
      φ.app _ (F₁.map f.op x) = φ.app _ (F₁.map f.op y) := fun Y f hf => by
        simpa using map_apply_eq_of_locallyInjective J ψ (φ.app _ x) (φ.app _ y) _ f hf
    let T : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X.unop⦄ (_ : S f), Sieve Y := fun Y f hf =>
      sieveOfLocallyInjective J φ (F₁.map f.op x) (F₁.map f.op y) (hS' hf)
    refine ⟨_, J.transitive hS (Sieve.bind S.1 T) ?_, ?_⟩
    · intro Y f hf
      exact J.superset_covering (Sieve.le_pullback_bind S.1 T _ hf)
        (sieveOfLocallyInjective_mem J φ (F₁.map f.op x) (F₁.map f.op y) (hS' hf))
    · intro Y f hf
      obtain ⟨Z, a, g, hg, ha, rfl⟩ := hf
      simpa using map_apply_eq_of_locallyInjective J φ _ _ (hS' hg) _ ha

lemma locallyInjective_of_locallyInjective [LocallyInjective J (φ ≫ ψ)] :
    LocallyInjective J φ where
  locally_injective {X} x y h :=
      ⟨_, sieveOfLocallyInjective_mem J (φ ≫ ψ) x y
        (by simpa using congr_arg (ψ.app X) h),
        map_apply_eq_of_locallyInjective J (φ ≫ ψ) x y _⟩

variable {φ ψ}

lemma locallyInjective_of_locallyInjective_fac {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ)
    [LocallyInjective J φψ] : LocallyInjective J φ := by
  subst fac
  exact locallyInjective_of_locallyInjective J φ ψ

lemma locallyInjective_iff_fac {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ) [LocallyInjective J ψ] :
    LocallyInjective J φψ ↔ LocallyInjective J φ := by
  constructor
  · intro
    exact locallyInjective_of_locallyInjective_fac J fac
  · intro
    rw [← fac]
    infer_instance

variable (φ ψ)

lemma locallyInjective_comp_iff [LocallyInjective J ψ] :
    LocallyInjective J (φ ≫ ψ) ↔ LocallyInjective J φ :=
  locallyInjective_iff_fac J rfl

instance locallySurjective_comp [LocallySurjective J φ] [LocallySurjective J ψ] :
    LocallySurjective J (φ ≫ ψ) where
  locally_surjective {X} x := by
    let S := sieveOfLocallySurjective J ψ x
    let hS : S ∈ J X.unop := sieveOfLocallySurjective_mem J ψ x
    let T : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X.unop⦄ (_ : S f), Sieve Y :=
      fun Y f hf => sieveOfLocallySurjective J φ (localPreimage J ψ x f hf)
    refine ⟨_, J.transitive hS (Sieve.bind S.1 T) ?_, ?_⟩
    · intro Y f hf
      exact J.superset_covering (Sieve.le_pullback_bind _ _ _ hf)
        (by apply sieveOfLocallySurjective_mem)
    · intro Y f hf
      obtain ⟨Z, a, g, hg, ha, rfl⟩ := hf
      exact ⟨localPreimage J φ (localPreimage J ψ x g hg) a ha, by simp⟩

lemma locallySurjective_of_locallySurjective [LocallySurjective J (φ ≫ ψ)] :
    LocallySurjective J ψ where
  locally_surjective {X} x :=
    ⟨_, sieveOfLocallySurjective_mem J (φ ≫ ψ) x, fun f hf =>
      ⟨φ.app _ (localPreimage J (φ ≫ ψ) x f hf),
        by simpa using app_apply_localPreimage J (φ ≫ ψ) x f hf⟩⟩

variable {φ ψ}

lemma locallySurjective_of_locallySurjective_fac {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ)
    [LocallySurjective J φψ] : LocallySurjective J ψ := by
  subst fac
  exact locallySurjective_of_locallySurjective J φ ψ

lemma locallySurjective_iff_fac {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ) [LocallySurjective J φ] :
    LocallySurjective J φψ ↔ LocallySurjective J ψ := by
  constructor
  · intro
    exact locallySurjective_of_locallySurjective_fac J fac
  · intro
    rw [← fac]
    infer_instance

variable (φ ψ)

lemma locallySurjective_comp_iff [LocallySurjective J φ] :
    LocallySurjective J (φ ≫ ψ) ↔ LocallySurjective J ψ :=
  locallySurjective_iff_fac J rfl

section

variable {E : Type u'} [Category.{max u v} E] [ConcreteCategory E]
  [PreservesLimits (forget E)]
  [∀ (P : Cᵒᵖ ⥤ E) (X : C) (S : J.Cover X),
    HasMultiequalizer (GrothendieckTopology.Cover.index S P)]
  [∀ (X : C), HasColimitsOfShape (GrothendieckTopology.Cover J X)ᵒᵖ E]
  [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget E)] [ReflectsIsomorphisms (forget E)]

variable (P : Cᵒᵖ ⥤ E)

section

open GrothendieckTopology Plus

instance locallyInjective_toPlus : LocallyInjective J (J.toPlus P) where
  locally_injective {X} x y h := by
    erw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
    obtain ⟨W, h₁, h₂, eq⟩ := h
    exact ⟨W.1, W.2, fun {Y} f hf => congr_fun (congr_arg Subtype.val eq) ⟨Y, f, hf⟩⟩

instance locallySurjective_toPlus : LocallySurjective J (J.toPlus P) where
  locally_surjective {X} x := by
    obtain ⟨S, x, rfl⟩ := exists_rep x
    refine' ⟨S.1, S.2, fun {Y} f hf => ⟨x.1 ⟨Y, f, hf⟩, _⟩⟩
    dsimp
    erw [toPlus_eq_mk, res_mk_eq_mk_pullback, eq_mk_iff_exists]
    refine' ⟨S.pullback f, homOfLE le_top, 𝟙 _, _⟩
    ext ⟨Z, g, hg⟩
    simpa using x.2 (Cover.Relation.mk _ _ _ g (𝟙 Z) f (g ≫ f) hf
      (S.1.downward_closed hf g) (by simp))

end

instance locallyInjective_toSheafify : LocallyInjective J (J.toSheafify P) := by
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

instance locallySurjective_toSheafify : LocallySurjective J (J.toSheafify P) := by
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

@[reassoc (attr := simp)]
lemma toSheafify_plusPlusIsoSheafify_hom :
    J.toSheafify P ≫ (plusPlusIsoSheafify J E P).hom = toSheafify J P := by
  convert Adjunction.unit_leftAdjointUniq_hom_app
    (plusPlusAdjunction J E) (sheafificationAdjunction J E) P
  ext1 P
  dsimp [GrothendieckTopology.toSheafify, plusPlusAdjunction]
  rw [Category.comp_id]

instance locallyInjective_toSheafify' : LocallyInjective J (toSheafify J P) := by
  rw [← toSheafify_plusPlusIsoSheafify_hom]
  infer_instance

instance locallySurjective_toSheafify' : LocallySurjective J (toSheafify J P) := by
  rw [← toSheafify_plusPlusIsoSheafify_hom]
  infer_instance

end

end Presheaf

namespace Sheaf

variable {J}
variable {F₁ F₂ F₃ : Sheaf J D} (φ : F₁ ⟶ F₂) (ψ : F₂ ⟶ F₃)

abbrev LocallyInjective := Presheaf.LocallyInjective J φ.1

abbrev LocallySurjective := Presheaf.LocallySurjective J φ.1

instance locallyInjective_comp [LocallyInjective φ] [LocallyInjective ψ] :
    LocallyInjective (φ ≫ ψ) :=
  Presheaf.locallyInjective_comp J φ.1 ψ.1

instance locallySurjective_comp [LocallySurjective φ] [LocallySurjective ψ] :
    LocallySurjective (φ ≫ ψ) :=
  Presheaf.locallySurjective_comp J φ.1 ψ.1

lemma locallyInjective_of_locallyInjective [LocallyInjective (φ ≫ ψ)] :
    LocallyInjective φ :=
  Presheaf.locallyInjective_of_locallyInjective J φ.1 ψ.1

lemma locallySurjective_of_locallySurjective [LocallySurjective (φ ≫ ψ)] :
    LocallySurjective ψ :=
  Presheaf.locallySurjective_of_locallySurjective J φ.1 ψ.1

variable {φ ψ}

lemma locallyInjective_of_locallyInjective_fac {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ)
    [LocallyInjective φψ] : LocallyInjective φ := by
  subst fac
  exact locallyInjective_of_locallyInjective φ ψ

lemma locallySurjective_of_locallySurjective_fac {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ)
    [LocallySurjective φψ] : LocallySurjective ψ := by
  subst fac
  exact locallySurjective_of_locallySurjective φ ψ

section

variable (φ)
variable [J.HasSheafCompose (forget D)]

instance locallyInjective_forget [LocallyInjective φ] :
    LocallyInjective ((sheafCompose J (forget D)).map φ) :=
  Presheaf.locallyInjective_forget J φ.1

instance locallySurjective_forget [LocallySurjective φ] :
    LocallySurjective ((sheafCompose J (forget D)).map φ) :=
  Presheaf.locallySurjective_forget J φ.1

lemma mono_of_locallyInjective' {F G : Sheaf J (Type w)} (φ : F ⟶ G) [LocallyInjective φ] :
    Mono φ where
  right_cancellation {Z} f₁ f₂ h := by
    ext X x
    apply ((Presieve.isSeparated_of_isSheaf _ _ ((isSheaf_iff_isSheaf_of_type _ _).1 F.2)) _
      (Presheaf.sieveOfLocallyInjective_mem J φ.1 (f₁.1.app _ x) (f₂.1.app _ x)
      (congr_fun (congr_app (congr_arg Sheaf.Hom.val h) X) x))).ext
    intro Y f hf
    exact Presheaf.map_apply_eq_of_locallyInjective J φ.1 _ _ _ f hf

lemma epi_of_locallySurjective' {F G : Sheaf J (Type w)} (φ : F ⟶ G) [LocallySurjective φ] :
    Epi φ where
  left_cancellation := by
    intro H f₁ f₂ h₁₂
    ext X x
    apply ((Presieve.isSeparated_of_isSheaf _ _ ((isSheaf_iff_isSheaf_of_type _ _).1 H.2)) _
      (Presheaf.sieveOfLocallySurjective_mem J φ.1 x)).ext
    intro Y f hf
    have h₁ := congr_fun (f₁.1.naturality f.op) x
    have h₂ := congr_fun (f₂.1.naturality f.op) x
    dsimp at h₁ h₂
    simp only [← h₁, ← h₂]
    erw [congr_arg (f₁.val.app (op Y)) (Presheaf.app_apply_localPreimage J φ.1 x f hf).symm,
      congr_arg (f₂.val.app (op Y)) (Presheaf.app_apply_localPreimage J φ.1 x f hf).symm]
    exact congr_fun (congr_app (congr_arg Sheaf.Hom.val h₁₂) (op Y)) _

instance : Faithful (sheafCompose J (forget D)) where
  map_injective {F G f₁ f₂} h := by
    ext X x
    exact congr_fun (congr_app ((sheafToPresheaf _ _).congr_map h) X) x

lemma mono_of_locallySurjective [LocallyInjective φ] : Mono φ :=
  (sheafCompose J (forget D)).mono_of_mono_map (mono_of_locallyInjective' _)

lemma epi_of_locallySurjective [LocallySurjective φ] : Epi φ :=
  (sheafCompose J (forget D)).epi_of_epi_map (epi_of_locallySurjective' _)

end

end Sheaf

namespace Presheaf

variable [HasWeakSheafify J D]
  [∀ (P : Cᵒᵖ ⥤ D), Presheaf.LocallyInjective J (toSheafify J P)]
  [∀ (P : Cᵒᵖ ⥤ D), Presheaf.LocallySurjective J (toSheafify J P)]
  {F G : Cᵒᵖ ⥤ D} (φ : F ⟶ G)

/-lemma sheafifyMap_locallyInjective_iff :
    LocallyInjective J (sheafifyMap J φ) ↔
      LocallyInjective J φ := by
  rw [← locallyInjective_comp_iff J _ (toSheafify J G), toSheafify_naturality J φ]
  constructor
  · intro
    infer_instance
  · sorry

lemma presheafToSheaf_map_locallyInjective_iff :
    Sheaf.LocallyInjective ((presheafToSheaf J D).map φ) ↔
      LocallyInjective J φ :=
  sheafifyMap_locallyInjective_iff J φ-/

end Presheaf

end CategoryTheory
