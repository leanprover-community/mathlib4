/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.EpiMono
import Mathlib.CategoryTheory.MorphismProperty
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Whiskering
/-!
# Locally injective or locally surjective morphisms of presheaves


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

lemma app_apply_localPreimage :
    φ.app _ (localPreimage J φ x f hf) = F₂.map f.op x :=
  ((hφ.locally_surjective x).choose_spec.choose_spec f hf).choose_spec

end

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

variable (φ ψ)

/-instance locallySurjective_comp [LocallySurjective J φ] [LocallySurjective J ψ] :
    LocallySurjective J (φ ≫ ψ) where
  locally_surjective {X} x := by
    sorry-/

end Presheaf

namespace Sheaf

variable {J}
variable {F₁ F₂ F₃ : Sheaf J D} (φ : F₁ ⟶ F₂) (ψ : F₂ ⟶ F₃)

abbrev LocallyInjective := Presheaf.LocallyInjective J φ.1

abbrev LocallySurjective := Presheaf.LocallySurjective J φ.1

instance locallyInjective_comp [LocallyInjective φ] [LocallyInjective ψ] :
    LocallyInjective (φ ≫ ψ) :=
  Presheaf.locallyInjective_comp J φ.1 ψ.1

lemma locallyInjective_of_locallyInjective [LocallyInjective (φ ≫ ψ)] :
    LocallyInjective φ :=
  Presheaf.locallyInjective_of_locallyInjective J φ.1 ψ.1

variable {φ ψ}

lemma locallyInjective_of_locallyInjective_fac {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ)
    [LocallyInjective φψ] : LocallyInjective φ := by
  subst fac
  exact locallyInjective_of_locallyInjective φ ψ

end Sheaf

end CategoryTheory
