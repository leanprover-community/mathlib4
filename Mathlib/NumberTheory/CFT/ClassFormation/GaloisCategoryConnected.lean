/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Galois.Decomposition
public import Mathlib.CategoryTheory.Galois.Prorepresentability
public import Mathlib.CategoryTheory.Galois.GaloisObjects

/-!
# Connected objects in Galois categories

-/

-- to be moved to `CategoryTheory/Galois`

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open GaloisCategory PreGaloisCategory Limits

namespace PreGaloisCategory

lemma isConnected_iff_pretransitive_and_nonempty
    [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (X : C) :
    PreGaloisCategory.IsConnected X ↔ MulAction.IsPretransitive (Aut F) (F.obj X).obj ∧
      Nonempty (F.obj X).obj :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦
    { notInitial := not_initial_of_inhabited F (Classical.arbitrary (F.obj X).obj)
      noTrivialComponent Y i _ hY := by
        rw [← isIso_iff_of_reflects_iso _ F,
          ConcreteCategory.isIso_iff_bijective]
        refine ⟨injective_of_mono ((forget _).map (F.map i)), fun x ↦ ?_⟩
        rw [not_initial_iff_fiber_nonempty F] at hY
        let y : (F.obj Y).obj := Classical.arbitrary _
        obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq  (Aut F) (F.map i y) x
        exact ⟨g • y, by simp [mulAction_naturality]⟩}⟩

lemma IsConnected.of_iso
    {X Y : C} [PreGaloisCategory.IsConnected X] (e : X ≅ Y) :
    IsConnected Y where
  notInitial h := notInitial (h.ofIso e.symm)
  noTrivialComponent Z i _ hZ := by
    rw [← isIso_comp_right_iff _ e.inv]
    exact noTrivialComponent _ _ hZ

lemma IsConnected.of_epi [GaloisCategory C]
    {X Y : C} [PreGaloisCategory.IsConnected X] (p : X ⟶ Y) [Epi p] :
    PreGaloisCategory.IsConnected Y := by
  let F := getFiberFunctor C
  rw [isConnected_iff_pretransitive_and_nonempty F]
  have hp : Function.Surjective (F.map p) :=
    surjective_of_epi ((forget _).map (F.map p))
  refine ⟨⟨fun y₁ y₂ ↦ ?_⟩, ⟨F.map p (Classical.arbitrary (F.obj X).obj)⟩⟩
  obtain ⟨x₁, rfl⟩ := hp y₁
  obtain ⟨x₂, rfl⟩ := hp y₂
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (Aut F) x₁ x₂
  exact ⟨g, by simp [mulAction_naturality]⟩

variable (C) in
/-- The property of objects satisfied by conencted objects (in a pre-Galois
category). -/
abbrev isConnected : ObjectProperty C := PreGaloisCategory.IsConnected

instance (X : (isConnected C).FullSubcategory) :
    PreGaloisCategory.IsConnected X.obj := X.property

instance : (PreGaloisCategory.isConnected C).IsClosedUnderIsomorphisms where
  of_iso e _ := PreGaloisCategory.IsConnected.of_iso e

instance (X : (PreGaloisCategory.isConnected C).FullSubcategory) :
    PreGaloisCategory.IsConnected X.obj :=
  X.property

/-- Constructor for objects in the full subcategory of connected objects in a Galois category. -/
abbrev isConnectedMk (X : C) [PreGaloisCategory.IsConnected X] :
    (isConnected C).FullSubcategory := ⟨X, inferInstance⟩

/-- Constructor for morphisms in the full subcategory of connected objects
in a Galois category. -/
abbrev isConnectedHomMk {X Y : C} (f : X ⟶ Y) [PreGaloisCategory.IsConnected X]
    [PreGaloisCategory.IsConnected Y] :
    isConnectedMk X ⟶ isConnectedMk Y :=
  ObjectProperty.homMk f

open ConcreteCategory in
lemma IsGalois.of_iso [GaloisCategory C]
    {X Y : C} [hX : PreGaloisCategory.IsGalois X] (e : X ≅ Y) :
    IsGalois Y := by
  have := IsConnected.of_iso e
  let F := getFiberFunctor C
  rw [isGalois_iff_pretransitive F, MulAction.isPretransitive_iff] at hX ⊢
  intro x y
  obtain ⟨x, rfl⟩ := (bijective_of_isIso (F.map e.hom)).surjective x
  obtain ⟨y, rfl⟩ := (bijective_of_isIso (F.map e.hom)).surjective y
  obtain ⟨g, rfl⟩ := hX x y
  refine ⟨Aut.autMulEquivOfIso e g, ?_⟩
  simp only [autMulFiber_def, Aut.autMulEquivOfIso_apply_hom,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp, Iso.hom_inv_id_assoc]

lemma IsGalois.iff_of_iso [GaloisCategory C]
    {X Y : C} (e : X ≅ Y) :
    PreGaloisCategory.IsGalois X ↔ PreGaloisCategory.IsGalois Y :=
  ⟨fun _ ↦ .of_iso e, fun _ ↦ .of_iso e.symm⟩

instance [GaloisCategory C] {X Y : C} [PreGaloisCategory.IsConnected X]
    [PreGaloisCategory.IsConnected Y] (f : X ⟶ Y) :
    Epi f :=
  epi_of_nonempty_of_isConnected (getFiberFunctor C) _

instance [GaloisCategory C] {X Y : (isConnected C).FullSubcategory} (f : X ⟶ Y) :
    Epi f where
  left_cancellation {Z} g₁ g₂ h := by
    ext
    simp only [← cancel_epi f.hom, ← InducedCategory.comp_hom, h]

end PreGaloisCategory

namespace GaloisCategory

lemma has_connected_component [GaloisCategory C] (X : C) (hX : IsInitial X → False) :
    ∃ (X₀ : C) (f : X₀ ⟶ X), Mono f ∧ PreGaloisCategory.IsConnected X₀ := by
  obtain ⟨ι, W, a, ha, _, _⟩ := has_decomp_connected_components X
  have : Nonempty ι := by
    by_contra!
    exact hX (IsInitial.ofUniqueHom
      (fun _ ↦ Cofan.IsColimit.desc ha (fun i ↦ (IsEmpty.false i).elim))
      (fun _ _ ↦ Cofan.IsColimit.hom_ext ha _ _ (fun i ↦ (IsEmpty.false i).elim)))
  exact ⟨W (Classical.arbitrary _), a _, MonoCoprod.mono_inj _ _ ha _, inferInstance⟩

end GaloisCategory

end CategoryTheory
