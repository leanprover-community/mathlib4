/-
Copyright (c) 2027 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-!

-/

@[expose] public section

universe w v v₁ u₁ v₂ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {A : Type*} [Category.{v} A] {B : Type*} [Category.{v} B]

variable {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D)

variable {P : ObjectProperty C}

def ObjectProperty.isHomInjective (P : ObjectProperty C) : MorphismProperty C := fun _ _ f ↦
  ∀ Z, P Z → Function.Injective fun (g : _ ⟶ Z) ↦ f ≫ g

lemma ObjectProperty.isLocal_le_isHomInjective (P : ObjectProperty C) :
    P.isLocal ≤ P.isHomInjective :=
  fun _ _ _ hf Z hZ ↦ (hf Z hZ).injective

instance (P : ObjectProperty C) : P.isHomInjective.IsMultiplicative where
  id_mem X Z _ := by simpa [Category.id_comp] using Function.injective_id
  comp_mem f g hf hg Z hZ := by
    simpa using Function.Injective.comp (hf Z hZ) (hg Z hZ)

instance (P : ObjectProperty C) : P.isHomInjective.HasOfPrecompProperty P.isHomInjective where
  of_precomp f g hf hfg Z hZ := by
    rw [← Function.Injective.of_comp_iff (hf Z hZ)]
    simpa using hfg Z hZ

instance (P : ObjectProperty C) : P.isHomInjective.HasOfPrecompProperty P.isLocal :=
  .of_le _ P.isHomInjective P.isLocal_le_isHomInjective

instance (P : ObjectProperty C) : P.isHomInjective.HasOfPostcompProperty P.isLocal where
  of_postcomp f g hg hfg Z hZ := by
    rw [← Function.Injective.of_comp_iff' _ (hg Z hZ)]
    simpa using hfg Z hZ

instance (P : ObjectProperty C) : P.isHomInjective.RespectsRight P.isLocal where
  postcomp f hf g hg Z hZ := by
    simpa using Function.Injective.comp (hg Z hZ) (hf Z hZ).injective

instance (P : ObjectProperty C) : P.isHomInjective.RespectsLeft P.isLocal where
  precomp f hf g hg Z hZ := by
    simpa using Function.Injective.comp (hf Z hZ).injective (hg Z hZ)

def Presieve.leftComp {X : C} (R : Presieve X) (Y : C) :
    (X ⟶ Y) → ∀ (T : C) (u : T ⟶ X) (_ : R u), T ⟶ Y :=
  fun g _ u _ ↦ u ≫ g

def ObjectProperty.IsJointlyHomInjective (P : ObjectProperty C) {X : C} (R : Presieve X) : Prop :=
  ∀ Z, P Z → Function.Injective fun (g : X ⟶ Z) (T : C) (u : T ⟶ X) (_ : R u) ↦ u ≫ g

def ObjectProperty.IsJointlyHomSurjective (P : ObjectProperty C) {X : C} (R : Presieve X) : Prop :=
  ∀ Z, P Z → Function.Surjective fun (g : X ⟶ Z) (T : C) (u : T ⟶ X) (_ : R u) ↦ u ≫ g

def ObjectProperty.IsJointlyLocal (P : ObjectProperty C) {X : C} (R : Presieve X) : Prop :=
  ∀ Z, P Z → Function.Bijective fun (g : X ⟶ Z) (T : C) (u : T ⟶ X) (_ : R u) ↦ u ≫ g

lemma ObjectProperty.IsJointlyLocal.isJointlyHomInjective {X : C} {R : Presieve X}
    (h : P.IsJointlyLocal R) :
    P.IsJointlyHomInjective R :=
  fun Z hZ ↦ (h Z hZ).injective

lemma ObjectProperty.IsJointlyLocal.isJointlyHomSurjective {X : C} {R : Presieve X}
    (h : P.IsJointlyLocal R) :
    P.IsJointlyHomSurjective R :=
  fun Z hZ ↦ (h Z hZ).surjective

lemma ObjectProperty.isJointlyHomInjective_ofArrows_iff {X : C} {ι : Type*}
    {Y : ι → C} {f : ∀ i, Y i ⟶ X} :
    P.IsJointlyHomInjective (.ofArrows _ f) ↔
      ∀ Z, P Z → Function.Injective (fun (g : X ⟶ Z) (i : ι) ↦ f i ≫ g) := by
  refine ⟨fun h Z hZ a b hab ↦ h Z hZ ?_, fun h Z hZ a b hab ↦ h Z hZ ?_⟩
  · ext _ _ ⟨i⟩
    exact congr($(hab) i)
  · ext i
    exact congr($(hab) _ _ ⟨i⟩)

lemma ObjectProperty.isJointlyLocal_singleton (P : ObjectProperty C) {X Y : C} (f : X ⟶ Y) :
    P.IsJointlyLocal (.singleton f) ↔ P.isLocal f := by
  refine ⟨fun h Z hZ ↦ ⟨?_, ?_⟩, fun h Z hZ ↦ ⟨?_, ?_⟩⟩
  · intro a b hab
    apply (h Z hZ).injective
    ext _ _ ⟨⟩
    simpa
  · intro a
    obtain ⟨u, hu⟩ := (h Z hZ).surjective fun T v hv ↦ eqToHom (by cases hv; rfl) ≫ a
    exact ⟨u, by simp [dsimp% congr($(hu) _ _ ⟨⟩)]⟩
  · intro a b hab
    exact (h Z hZ).injective congr($(hab) _ _ ⟨⟩)
  · intro a
    obtain ⟨u, hu⟩ := (h Z hZ).surjective (a _ _ ⟨⟩)
    exact ⟨u, by ext _ _ ⟨⟩; simpa⟩

set_option backward.isDefEq.respectTransparency false in
lemma Adjunction.bijective_map_comp_iff {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) {X Y : C} (f : X ⟶ Y)
    (Z : D) :
    Function.Bijective (fun (g : F.obj Y ⟶ Z) ↦ F.map f ≫ g) ↔
      Function.Bijective (fun (g : Y ⟶ G.obj Z) ↦ f ≫ g) := by
  rw [← Function.Bijective.of_comp_iff' (adj.homEquiv _ _).bijective,
    ← Function.Bijective.of_comp_iff _ (adj.homEquiv _ _).symm.bijective]
  congr!
  ext g
  simp [Adjunction.homEquiv_apply, Adjunction.homEquiv_symm_apply, ]

section

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

set_option backward.isDefEq.respectTransparency false in
lemma ObjectProperty.isHomInjective_iff_epi_map {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X Y : C} (f : X ⟶ Y) :
    isHomInjective G.essImage f ↔ Epi (F.map f) := by
  refine ⟨fun h ↦ ⟨fun {Z} a b hab ↦ ?_⟩, ?_⟩
  · apply (adj.homEquiv _ _).injective (h _ (G.obj_mem_essImage Z) ?_)
    apply (adj.homEquiv _ _).symm.injective
    simp [adj.homEquiv_naturality_left_symm, hab]
  · intro h Z ⟨U, ⟨e⟩⟩ a b hab
    rw [← cancel_mono e.inv]
    apply (adj.homEquiv _ _).symm.injective
    simp_rw [adj.homEquiv_naturality_left_symm,
      ← cancel_epi (F.map f), ← Functor.map_comp_assoc, dsimp% hab]

end
open Limits

def Sieve.equivSubfunctorYoneda (X : C) : Sieve X ≃ Subfunctor (yoneda.obj X) where
  toFun S := ⟨fun Y ↦ { f | S f }, fun {Y Z} g f hf ↦ S.downward_closed hf _⟩
  invFun F := ⟨fun Y f ↦ f ∈ F.obj (.op Y), fun {Y Z} f hf g ↦ F.map g.op hf⟩

@[simps, pp_with_univ]
def Sieve.shrinkFunctor [LocallySmall.{w} C] {X : C} (S : Sieve X) :
    Subfunctor (shrinkYoneda.{w}.obj X) where
  obj Y := { f | S (shrinkYonedaObjObjEquiv f) }
  map {Y Z} g f hf := by
    simpa [shrinkYonedaObjObjEquiv_map] using S.downward_closed hf _

set_option backward.isDefEq.respectTransparency false in
noncomputable
def Sieve.shrinkFunctorUliftFunctorIso [LocallySmall.{w} C] [LocallySmall.{max v w, v₁, u₁} C]
    {X : C} (S : Sieve X) :
    (Sieve.shrinkFunctor.{w} S).toFunctor ⋙ CategoryTheory.uliftFunctor.{v, w} ≅
      (Sieve.shrinkFunctor.{max v w} S).toFunctor :=
  NatIso.ofComponents
    (fun X ↦ Equiv.toIso
      (.trans Equiv.ulift
        (Equiv.subtypeEquiv (shrinkYonedaObjObjEquiv.trans shrinkYonedaObjObjEquiv.symm)
        fun a ↦ by simp)))
    fun {U V} f ↦ by
      ext
      dsimp
      ext
      dsimp [Equiv.subtypeEquiv]
      rw [shrinkYonedaObjObjEquiv_map, shrinkYonedaObjObjEquiv_symm_comp]
      simp

@[reassoc]
lemma Sieve.shrinkFunctorUliftFunctorIso_inv_ι [LocallySmall.{w} C]
    [LocallySmall.{max v w, v₁, u₁} C]
    {X : C} (S : Sieve X) :
    (Sieve.shrinkFunctorUliftFunctorIso.{w, v} S).inv ≫
      Functor.whiskerRight (Sieve.shrinkFunctor.{w} _).ι CategoryTheory.uliftFunctor.{v, w} =
    (Sieve.shrinkFunctor.{max v w} S).ι ≫
      shrinkYonedaUliftFunctorIso.{w, v}.inv.app X :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simps]
noncomputable
def Sieve.shrinkFunctorHomEquiv [LocallySmall.{w} C] {F : Cᵒᵖ ⥤ Type w} {X : C} {S : Sieve X} :
    (S.shrinkFunctor.toFunctor ⟶ F) ≃ { x : S.arrows.FamilyOfElements F // x.Compatible } where
  toFun t := ⟨fun Y f hf ↦ t.app _ ⟨shrinkYonedaObjObjEquiv.symm f, by simpa⟩, by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y Z f g hf
    simp only [shrinkFunctor_obj, ← FunctorToTypes.naturality]
    rw! [shrinkYonedaObjObjEquiv_symm_comp]
    rfl⟩
  invFun t :=
    { app X f := t.1 _ f.mem
      naturality Y Z g := by
        ext ⟨f, hf⟩
        dsimp
        convert t.2.to_sieveCompatible _ _ _
        simp only [Opposite.op_unop, shrinkYonedaObjObjEquiv_map]
        rfl }
  left_inv t := by cat_disch
  right_inv x := by
    ext
    dsimp
    rw! [Equiv.apply_symm_apply]
    simp

set_option backward.isDefEq.respectTransparency false in
lemma Sieve.shrinkFunctor_ι_comp_eq_iff_isAmalgamation [LocallySmall.{w} C] (F : Cᵒᵖ ⥤ Type w)
    {X : C} {S : Sieve X} (f : S.shrinkFunctor.toFunctor ⟶ F) (g : shrinkYoneda.{w}.obj X ⟶ F) :
    S.shrinkFunctor.ι ≫ g = f ↔
      (Sieve.shrinkFunctorHomEquiv f).1.IsAmalgamation (shrinkYonedaEquiv g) := by
  simp only [Presieve.FamilyOfElements.IsAmalgamation]
  dsimp
  refine ⟨?_, ?_⟩
  · rintro rfl Y f hf
    simp [shrinkYonedaEquiv_naturality, shrinkYonedaEquiv_comp, shrinkYonedaEquiv_shrinkYoneda_map]
  · intro h
    ext Y ⟨u, hu⟩
    convert h (shrinkYonedaObjObjEquiv u) hu
    · rw [shrinkYonedaEquiv_naturality, shrinkYonedaEquiv_comp, shrinkYonedaEquiv_shrinkYoneda_map]
      simp
    · rw! [Equiv.symm_apply_apply]
      rfl

lemma Sieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp [LocallySmall.{w} C] {X : C}
    (S : Sieve X) (F : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSheafFor F S.arrows ↔
      Function.Bijective (fun g : _ ⟶ F ↦ S.shrinkFunctor.ι ≫ g) := by
  simp only [Presieve.IsSheafFor, Function.bijective_iff_existsUnique,
    Sieve.shrinkFunctor_ι_comp_eq_iff_isAmalgamation,
    Equiv.forall_congr_left Sieve.shrinkFunctorHomEquiv, Subtype.forall]
  exact forall₂_congr fun x hx ↦ by simp [Equiv.existsUnique_congr_right]

set_option backward.isDefEq.respectTransparency false in
def Sieve.equivSubfunctorShrinkYoneda [LocallySmall.{w} C] {X : C} :
    Sieve X ≃ Subfunctor (shrinkYoneda.{w}.obj X) where
  invFun F :=
    ⟨fun Y f ↦ shrinkYonedaObjObjEquiv.symm f ∈ F.obj (.op Y),
      fun {Y Z} f hf g ↦ by
        dsimp
        rw [shrinkYonedaObjObjEquiv_symm_comp]
        exact F.map g.op hf⟩
  toFun S := S.shrinkFunctor
  left_inv S := by simp
  right_inv F := by ext; simp

@[simp]
lemma ObjectProperty.essImage_ι (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] :
    P.ι.essImage = P :=
  le_antisymm (fun _ ⟨Y, ⟨e⟩⟩ ↦ P.prop_of_iso e Y.property) fun X h ↦ ⟨⟨X, h⟩, ⟨.refl _⟩⟩

lemma epi_iff_isIso_of_mono {C : Type*} [Category* C] [Balanced C] {X Y : C} (f : X ⟶ Y) [Mono f] :
    Epi f ↔ IsIso f := by
  simp [isIso_iff_mono_and_epi, ‹Mono f›]

lemma mono_iff_isIso_of_epi {C : Type*} [Category* C] [Balanced C] {X Y : C} (f : X ⟶ Y) [Epi f] :
    Mono f ↔ IsIso f := by
  simp [isIso_iff_mono_and_epi, ‹Epi f›]

namespace Presheaf

/--
A morphism of presheafs `f : H ⟶ K` is `J`-covering if for any `J`-sheaf `F` the induced
map `(K ⟶ F) → (H ⟶ F)` is injective.
(cf. SGA4 II 5.2 (morphisme couvrant))
-/
def covering : MorphismProperty (Cᵒᵖ ⥤ A) :=
  ObjectProperty.isHomInjective (Presheaf.IsSheaf J)

instance : ObjectProperty.IsClosedUnderIsomorphisms (Presheaf.IsSheaf J (A := A)) := by
  constructor
  intro F G e hF
  rwa [isSheaf_of_iso_iff e.symm]

@[simp]
lemma essImage_sheafToPresheaf : (sheafToPresheaf J A).essImage = Presheaf.IsSheaf J := by
  simp [sheafToPresheaf]

lemma covering_eq_isHomInjective_essImage :
    covering J = (sheafToPresheaf J A).essImage.isHomInjective := by
  simp [covering]

def IsCoveringFamily {X : Cᵒᵖ ⥤ A} (R : Presieve X) : Prop :=
  ObjectProperty.IsJointlyHomInjective (Presheaf.IsSheaf J) R

def IsBicoveringFamily {X : Cᵒᵖ ⥤ A} (R : Presieve X) : Prop :=
  ObjectProperty.IsJointlyLocal (Presheaf.IsSheaf J) R

variable {J}

lemma covering_of_W {H K : Cᵒᵖ ⥤ A} {f : H ⟶ K} (hf : J.W f) : covering J f :=
  fun F hF ↦ (hf F hF).injective

lemma covering_iff_epi [HasWeakSheafify J A] {H K : Cᵒᵖ ⥤ A} {f : H ⟶ K} :
    covering J f ↔ Epi ((presheafToSheaf J A).map f) := by
  rw [covering_eq_isHomInjective_essImage,
    ObjectProperty.isHomInjective_iff_epi_map (sheafificationAdjunction _ _)]

lemma Functor.W_map_of_adjunction_of_isContinuous (F : C ⥤ D)
    (H : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)) (adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op)
    [Functor.IsContinuous.{v} F J K] {G G' : Cᵒᵖ ⥤ A} (f : G ⟶ G') (hf : J.W f) :
    K.W (H.map f) := by
  intro U hU
  rw [adj.bijective_map_comp_iff]
  exact hf _ (F.op_comp_isSheaf_of_isSheaf _ _ _ hU)

lemma Functor.IsContinuous.of_W_map_of_adjunction [LocallySmall.{w} C] {F : C ⥤ D}
    {H : (Cᵒᵖ ⥤ Type w) ⥤ (Dᵒᵖ ⥤ Type w)} (adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op)
    (h : ∀ ⦃X : C⦄ ⦃S : Sieve X⦄, S ∈ J X → K.W (H.map <| S.shrinkFunctor.ι)) :
    Functor.IsContinuous.{w} F J K := by
  refine ⟨fun G X S hS ↦ ?_⟩
  rw [Sieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp, ← Functor.whiskeringLeft_obj_obj,
    ← adj.bijective_map_comp_iff]
  exact h hS _ G.property

/-- The assumptions are in particular satisfied for `A = Type w` for large enough `w`. -/
lemma W_iff_covering_and_covering_diagonal [HasPullbacks A] [HasSheafify J A]
    [Balanced (Sheaf J A)] {H K : Cᵒᵖ ⥤ A} (f : H ⟶ K) :
    J.W f ↔
      covering J f ∧ covering J (pullback.diagonal f) := by
  rw [covering_iff_epi, covering_iff_epi, J.W_iff, isIso_iff_mono_and_epi, and_comm]
  dsimp [pullback.diagonalObj, pullback.diagonal]
  rw [and_congr_right_iff]
  intro h
  rw [← epi_comp_iff_of_isIso _ (PreservesPullback.iso (presheafToSheaf J _) f f).hom]
  simp only [PreservesPullback.iso_hom, map_lift_pullbackComparison, Functor.map_id]
  rw [← pullback.diagonal, epi_iff_isIso_of_mono, pullback.isIso_diagonal_iff]

/-- `Functor.IsContinuous` is preserved under enlarging the universe if the starting
universe is large enough. -/
lemma isContinuous_max_of_isContinuous (F : C ⥤ D) [Functor.IsContinuous.{max u₁ v₁ u₂ v₂} F J K] :
    Functor.IsContinuous.{max w u₁ v₁ u₂ v₂} F J K := by
  let H : (Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂) ⥤ Dᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂ := F.op.lan
  let adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op := F.op.lanAdjunction _
  let H' : (Cᵒᵖ ⥤ Type max w u₁ v₁ u₂ v₂) ⥤ Dᵒᵖ ⥤ Type max w u₁ v₁ u₂ v₂ := F.op.lan
  let adj' : H' ⊣ (Functor.whiskeringLeft _ _ _).obj F.op := F.op.lanAdjunction _
  apply Functor.IsContinuous.of_W_map_of_adjunction _ adj'
  intro X S hS
  have hWS : J.W (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι := by
    -- TODO: extract this into a separate lemma
    intro Z hZ
    rw [isSheaf_iff_isSheaf_of_type] at hZ
    rw [← Sieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp]
    exact hZ _ hS
  have : K.W _ := Functor.W_map_of_adjunction_of_isContinuous (J := J) K F H adj
    (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι hWS
  let e : H ⋙ (Functor.whiskeringRight _ _ _).obj uliftFunctor.{w} ≅
      (Functor.whiskeringRight _ _ _).obj uliftFunctor.{w} ⋙ H' :=
    uliftFunctor.{w, max (max (max u₁ u₂) v₁) v₂}.lanCompIsoOfPreserves F.op
  have := e.app
  dsimp at this
  let e' := Sieve.shrinkFunctorUliftFunctorIso.{max u₁ v₁ u₂ v₂, w} S
  let iso : Arrow.mk (H'.map (Sieve.shrinkFunctor.{max w u₁ v₁ u₂ v₂} S).ι) ≅
      .mk
        (Functor.whiskerRight
          (H.map (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι) uliftFunctor.{w}) :=
    Arrow.isoMk' _ _ (H'.mapIso e'.symm ≪≫ (e.app _).symm)
      (H'.mapIso (shrinkYonedaUliftFunctorIso.{max u₁ v₁ u₂ v₂}.app _).symm ≪≫ (e.app _).symm) <| by
      simp only [Functor.mapIso_symm, Functor.comp_obj, Functor.whiskeringRight_obj_obj,
        Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv, Category.assoc, e']
      rw [← Functor.map_comp_assoc]
      rw [← dsimp% e.inv.naturality, ← Functor.map_comp_assoc]
      rw [Sieve.shrinkFunctorUliftFunctorIso_inv_ι]
      rfl
  rw [K.W.arrow_mk_iso_iff iso]
  apply GrothendieckTopology.W_of_preservesSheafification
  apply Functor.W_map_of_adjunction_of_isContinuous (J := J) K F H adj
    (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι hWS

lemma isContinuous_of_isContinuous_max (F : C ⥤ D) [Functor.IsContinuous.{max w v} F J K] :
    Functor.IsContinuous.{w} F J K := by
  refine ⟨fun G ↦ ?_⟩
  rw [← Presieve.isSheaf_comp_uliftFunctor_iff.{w, v}, ← isSheaf_iff_isSheaf_of_type,
    Presheaf.isSheaf_of_iso_iff (Functor.associator _ _ _)]
  refine F.op_comp_isSheaf_of_isSheaf J K _ ?_
  rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff.{w, v},
    ← isSheaf_iff_isSheaf_of_type]
  exact G.property

end Presheaf

namespace Functor

variable {F : C ⥤ D}

lemma functorPushforward_mem [IsContinuous.{max u₂ v₂} F J K] {X : C} (S : Sieve X) (hS : S ∈ J X) :
    S.functorPushforward F ∈ K _ := by
  rw [K.mem_iff_isSheafFor_closedSieves]
  obtain ⟨S, h⟩ := S
  obtain ⟨ι, Y, f, rfl⟩ := S.exists_eq_ofArrows
  dsimp
  sorry

lemma adsfasdf' [IsContinuous.{max u₂ v₂} F J K] :
    PreservesOneHypercovers.{w} F J K := by
  have H {X : C} (R : Presieve X) (hS : Sieve.generate R ∈ J X) :
      Presieve.IsSheafFor (F.op ⋙ closedSieves K) R := by
    rw [Presieve.isSheafFor_iff_generate]
    apply IsContinuous.op_comp_isSheaf_of_types (J := J) (K := K) ⟨closedSieves K, _⟩ _ hS
    rw [isSheaf_iff_isSheaf_of_type]
    exact classifier_isSheaf _
  --let auxSieve (Y : D) : Sieve Y :=
  --  { arrows Z f := ∃ (X : C), Nonempty (Z ⟶ F.obj X)
  --    downward_closed := sorry }
  intro X E
  refine ⟨?_, ?_⟩
  · rw [K.mem_iff_isSheafFor_closedSieves]
    rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate]
    rw [Presieve.isSheafFor_arrows_iff]
    intro x hx
    have := H E.presieve₀ E.mem₀
    rw [Presieve.isSheafFor_arrows_iff] at this
    refine this x ?_
    intro i j Z gi gj hgij
    apply hx
    simp [← Functor.map_comp, hgij]
  · intro i j W p₁ p₂ h
    --rw [K.mem_iff_isSheafFor_closedSieves]
    --intro x hx
    --let S : Sieve W :=
    --  ⟨fun T g ↦ ∃ (X : C), Nonempty (T ⟶ F.obj X), by
    --    intro Y Z f ⟨X, ⟨p⟩⟩ g
    --    use X, g ≫ p⟩
    --have hS : S ∈ K W := sorry
    let S : Sieve W :=
      ⟨fun T g ↦ ∃ (B : C) (u : B ⟶ E.X i) (u' : B ⟶ E.X j) (b : T ⟶ F.obj B),
          b ≫ F.map u = g ≫ p₁ ∧ b ≫ F.map u' = g ≫ p₂, by
        intro Y Z f ⟨B, u, u', b, hb₁, hb₂⟩ g
        use B, u, u', g ≫ b
        simp [hb₁, hb₂]⟩
    have hS : S ∈ K W :=
      sorry
    refine GrothendieckTopology.transitive _ hS _ ?_
    intro Y f ⟨B, u, u', b, hb₁, hb₂⟩
    --intro Y f ⟨X, ⟨p⟩⟩
    have := E.sieve₁ u u'
    have := E.mem₁ _ _ u u' <| by
      sorry
    have hmem : ((E.sieve₁ u u').functorPushforward F).pullback b ∈ K Y :=
      sorry
    refine K.superset_covering ?_ hmem
    intro Z p ⟨T, w, v, ⟨k, a, ha, ha'⟩, heq⟩
    use k, v ≫ F.map a
    refine ⟨?_, ?_⟩
    · simp [← hb₁, ← Functor.map_comp, ← ha, reassoc_of% heq]
    · simp [← hb₂, ← Functor.map_comp, ← ha', reassoc_of% heq]
  --rw [K.mem_iff_isSheafFor_closedSieves]
  --have : Presieve.IsSheafFor (F.op ⋙ closedSieves K) S.arrows := by
  --  apply IsContinuous.op_comp_isSheaf_of_types (J := J) (K := K) ⟨closedSieves K, _⟩ _ hS
  --  rw [isSheaf_iff_isSheaf_of_type]
  --  exact classifier_isSheaf _

lemma adsfasdf [IsContinuous.{max u₂ v₂} F J K] {X : C} {S : Sieve X} (hS : S ∈ J X) :
    S.functorPushforward F ∈ K (F.obj X) := by
  rw [K.mem_iff_isSheafFor_closedSieves]
  have : Presieve.IsSheafFor (F.op ⋙ closedSieves K) S.arrows := by
    apply IsContinuous.op_comp_isSheaf_of_types (J := J) (K := K) ⟨closedSieves K, _⟩ _ hS
    rw [isSheaf_iff_isSheaf_of_type]
    exact classifier_isSheaf _
  sorry

end Functor

end CategoryTheory
