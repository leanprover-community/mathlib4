/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.Hypercover.IsSheaf
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-!
# Continuous functors between sites.

We define the notion of continuous functor between sites: these are functors `F` such that
the precomposition with `F.op` preserves sheaves of types (and actually sheaves in any
category).

## Main definitions

* `Functor.IsContinuous`: a functor between sites is continuous if the
  precomposition with this functor preserves sheaves with values in
  the category `Type t` for a certain auxiliary universe `t`.
* `Functor.sheafPushforwardContinuous`: the induced functor
  `Sheaf K A ⥤ Sheaf J A` for a continuous functor `G : (C, J) ⥤ (D, K)`. In case this is
  part of a morphism of sites, this would be understood as the pushforward functor
  even though it goes in the opposite direction as the functor `G`. (Here, the auxiliary
  universe `t` in the assumption that `G` is continuous is the one such that morphisms
  in the category `A` are in `Type t`.)
* `Functor.PreservesOneHypercovers`: a type-class expressing that a functor preserves
  1-hypercovers of a certain size

## Main result

- `Functor.isContinuous_of_preservesOneHypercovers`: if the topology on `C` is generated
  by 1-hypercovers of size `w` and that `F : C ⥤ D` preserves 1-hypercovers of size `w`,
  then `F` is continuous (for any auxiliary universe parameter `t`).
  This is an instance for `w = max u₁ v₁` when `C : Type u₁` and `[Category.{v₁} C]`

## References
* https://stacks.math.columbia.edu/tag/00WU

-/

@[expose] public section

universe w t v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

namespace PreOneHypercover

variable {X : C} (E : PreOneHypercover X) (F : C ⥤ D)

/-- The image of a 1-pre-hypercover by a functor. -/
@[simps]
def map : PreOneHypercover (F.obj X) where
  I₀ := E.I₀
  X i := F.obj (E.X i)
  f i := F.map (E.f i)
  I₁ := E.I₁
  Y _ _ j := F.obj (E.Y j)
  p₁ _ _ j := F.map (E.p₁ j)
  p₂ _ _ j := F.map (E.p₂ j)
  w _ _ j := by simpa using F.congr_map (E.w j)

/-- If `F : C ⥤ D`, `P : Dᵒᵖ ⥤ A` and `E` is a 1-pre-hypercover of an object of `X`,
then `(E.map F).multifork P` is a limit iff `E.multifork (F.op ⋙ P)` is a limit. -/
def isLimitMapMultiforkEquiv {A : Type u} [Category.{t} A] (P : Dᵒᵖ ⥤ A) :
    IsLimit ((E.map F).multifork P) ≃ IsLimit (E.multifork (F.op ⋙ P)) := by rfl

end PreOneHypercover

namespace GrothendieckTopology

namespace OneHypercover

variable {J : GrothendieckTopology C} {X : C} (E : J.OneHypercover X)

/-- A 1-hypercover in `C` is preserved by a functor `F : C ⥤ D` if the mapped 1-pre-hypercover
in `D` is a 1-hypercover for the given topology on `D`. -/
class IsPreservedBy (F : C ⥤ D) (K : GrothendieckTopology D) : Prop where
  mem₀ : (E.toPreOneHypercover.map F).sieve₀ ∈ K (F.obj X)
  mem₁ (i₁ i₂ : E.I₀) ⦃W : D⦄ (p₁ : W ⟶ F.obj (E.X i₁)) (p₂ : W ⟶ F.obj (E.X i₂))
    (w : p₁ ≫ F.map (E.f i₁) = p₂ ≫ F.map (E.f i₂)) :
      (E.toPreOneHypercover.map F).sieve₁ p₁ p₂ ∈ K W

/-- Given a 1-hypercover `E : J.OneHypercover X` of an object of `C`, a functor `F : C ⥤ D`
such that `E.IsPreservedBy F K` for a Grothendieck topology `K` on `D`, this is
the image of `E` by `F`, as a 1-hypercover of `F.obj X` for `K`. -/
@[simps! toPreOneHypercover]
def map (F : C ⥤ D) (K : GrothendieckTopology D) [E.IsPreservedBy F K] :
    K.OneHypercover (F.obj X) where
  toPreOneHypercover := E.toPreOneHypercover.map F
  mem₀ := IsPreservedBy.mem₀
  mem₁ _ _ _ _ _ h := IsPreservedBy.mem₁ _ _ _ _ h

instance : E.IsPreservedBy (𝟭 C) J where
  mem₀ := E.mem₀
  mem₁ := E.mem₁

end OneHypercover

end GrothendieckTopology

/-- If `C` is `w`-locally small, any sieve induces a subfunctor of `shrinkYoneda.{w}.obj X`. -/
@[simps, pp_with_univ]
def Sieve.shrinkFunctor [LocallySmall.{w} C] {X : C} (S : Sieve X) :
    Subfunctor (shrinkYoneda.{w}.obj X) where
  obj Y := { f | S (shrinkYonedaObjObjEquiv f) }
  map {Y Z} g f hf := by
    simpa [shrinkYonedaObjObjEquiv_map] using S.downward_closed hf _

set_option backward.isDefEq.respectTransparency false in
/-- `Sieve.shrinkFunctor` is compatible with universe lifting. -/
noncomputable
def Sieve.shrinkFunctorUliftFunctorIso [LocallySmall.{w} C] [LocallySmall.{max t w, v₁, u₁} C]
    {X : C} (S : Sieve X) :
    (Sieve.shrinkFunctor.{w} S).toFunctor ⋙ CategoryTheory.uliftFunctor.{t, w} ≅
      (Sieve.shrinkFunctor.{max t w} S).toFunctor :=
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
    [LocallySmall.{max t w, v₁, u₁} C]
    {X : C} (S : Sieve X) :
    (Sieve.shrinkFunctorUliftFunctorIso.{w, t} S).inv ≫
      Functor.whiskerRight (Sieve.shrinkFunctor.{w} _).ι CategoryTheory.uliftFunctor.{t, w} =
    (Sieve.shrinkFunctor.{max t w} S).ι ≫
      shrinkYonedaUliftFunctorIso.{w, t}.inv.app X :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation): Auxiliary equivalence for showing
`Sieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp`. -/
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
lemma Adjunction.bijective_map_comp_iff {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) {X Y : C} (f : X ⟶ Y)
    (Z : D) :
    Function.Bijective (fun (g : F.obj Y ⟶ Z) ↦ F.map f ≫ g) ↔
      Function.Bijective (fun (g : Y ⟶ G.obj Z) ↦ f ≫ g) := by
  rw [← Function.Bijective.of_comp_iff' (adj.homEquiv _ _).bijective,
    ← Function.Bijective.of_comp_iff _ (adj.homEquiv _ _).symm.bijective]
  congr!
  ext g
  simp [Adjunction.homEquiv_apply, Adjunction.homEquiv_symm_apply, ]

lemma Presieve.IsSheaf.comp_of_W_map_of_adjunction
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [LocallySmall.{w} C] {F : C ⥤ D} {H : (Cᵒᵖ ⥤ Type w) ⥤ (Dᵒᵖ ⥤ Type w)}
    (adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op)
    (h : ∀ ⦃X : C⦄ ⦃S : Sieve X⦄, S ∈ J X →
      K.W (H.map <| (Sieve.shrinkFunctor.{w} S).ι))
    (G : Dᵒᵖ ⥤ Type w) (hG : Presieve.IsSheaf K G) :
    Presieve.IsSheaf J (F.op ⋙ G) := by
  intro X S hS
  rw [Sieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp, ← Functor.whiskeringLeft_obj_obj,
    ← adj.bijective_map_comp_iff]
  refine h hS _ ?_
  rwa [isSheaf_iff_isSheaf_of_type]

lemma Sieve.W_shrinkFunctor_ι_of_mem [LocallySmall.{w} C] {J : GrothendieckTopology C} {X : C}
    (S : Sieve X) (hS : S ∈ J X) :
    J.W (Sieve.shrinkFunctor.{w} S).ι := by
  intro Z hZ
  rw [isSheaf_iff_isSheaf_of_type] at hZ
  rw [← Sieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp]
  exact hZ _ hS

namespace Functor

variable (F F' : C ⥤ D) (τ : F ⟶ F') (e : F ≅ F') (G : D ⥤ E)
  {F'' : C ⥤ C} (eF'' : F'' ≅ 𝟭 C) {FG : C ⥤ E} (eFG : F ⋙ G ≅ FG)
  {A : Type u} [Category.{t} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)

/-- The condition that a functor `F : C ⥤ D` sends 1-hypercovers for
`J : GrothendieckTopology C` to 1-hypercovers for `K : GrothendieckTopology D`. -/
abbrev PreservesOneHypercovers :=
  ∀ {X : C} (E : GrothendieckTopology.OneHypercover.{w} J X), E.IsPreservedBy F K

/-- A functor `F` is continuous if the precomposition with `F.op` sends sheaves of
`Type (max u₁ v₁ u₂ v₂)` to sheaves. This implies that this holds for an arbitrary
universe (see `Functor.op_comp_isSheaf_of_types`). -/
class IsContinuous : Prop where
  op_comp_isSheaf_of_types (G : Sheaf K (Type max u₁ v₁ u₂ v₂)) : Presieve.IsSheaf J (F.op ⋙ G.obj)

/-- (Implementation) Use the more general `Functor.W_map_of_adjunction_of_isContinuous`. -/
private lemma W_map_of_adjunction_of_isContinuous_aux (F : C ⥤ D)
    (H : (Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂) ⥤ (Dᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂))
    (adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op)
    [Functor.IsContinuous F J K] {G G' : Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂} (f : G ⟶ G') (hf : J.W f) :
    K.W (H.map f) := by
  intro U hU
  rw [adj.bijective_map_comp_iff]
  apply hf
  rw [isSheaf_iff_isSheaf_of_type]
  exact IsContinuous.op_comp_isSheaf_of_types (F := F) ⟨U, hU⟩

/-- `Functor.IsContinuous` is preserved under enlarging the universe if the starting
universe is large enough. -/
private lemma isSheaf_of_isContinuous_aux (F : C ⥤ D) [Functor.IsContinuous F J K]
    (G : Dᵒᵖ ⥤ Type max w u₁ v₁ u₂ v₂) (hG : Presieve.IsSheaf K G) :
    Presieve.IsSheaf J (F.op ⋙ G) := by
  let H : (Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂) ⥤ Dᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂ := F.op.lan
  let adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op := F.op.lanAdjunction _
  let H' : (Cᵒᵖ ⥤ Type max w u₁ v₁ u₂ v₂) ⥤ Dᵒᵖ ⥤ Type max w u₁ v₁ u₂ v₂ := F.op.lan
  let adj' : H' ⊣ (Functor.whiskeringLeft _ _ _).obj F.op := F.op.lanAdjunction _
  refine Presieve.IsSheaf.comp_of_W_map_of_adjunction adj' ?_ _ hG
  intro X S hS
  have hWS : J.W (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι :=
    Sieve.W_shrinkFunctor_ι_of_mem.{max u₁ v₁ u₂ v₂} S hS
  have : K.W _ := Functor.W_map_of_adjunction_of_isContinuous_aux (J := J) K F H adj
    (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι hWS
  let e : H ⋙ (Functor.whiskeringRight _ _ _).obj uliftFunctor.{w} ≅
      (Functor.whiskeringRight _ _ _).obj uliftFunctor.{w} ⋙ H' :=
    uliftFunctor.{w, max (max (max u₁ u₂) v₁) v₂}.lanCompIsoOfPreserves F.op
  let iso : Arrow.mk (H'.map (Sieve.shrinkFunctor.{max w u₁ v₁ u₂ v₂} S).ι) ≅
      .mk (Functor.whiskerRight
        (H.map (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι) uliftFunctor.{w}) :=
    Arrow.isoMk' _ _
      (H'.mapIso (Sieve.shrinkFunctorUliftFunctorIso.{max u₁ v₁ u₂ v₂, w} S).symm ≪≫ (e.app _).symm)
      (H'.mapIso (shrinkYonedaUliftFunctorIso.{max u₁ v₁ u₂ v₂}.app _).symm ≪≫ (e.app _).symm) <| by
        simp only [Functor.mapIso_symm, Functor.comp_obj, Functor.whiskeringRight_obj_obj,
          Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
        rw [← Functor.map_comp_assoc, ← dsimp% e.inv.naturality, ← Functor.map_comp_assoc,
          Sieve.shrinkFunctorUliftFunctorIso_inv_ι]
        rfl
  rw [K.W.arrow_mk_iso_iff iso]
  apply GrothendieckTopology.W_of_preservesSheafification
  exact F.W_map_of_adjunction_of_isContinuous_aux J K H adj
    (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} S).ι hWS

lemma op_comp_isSheaf_of_types [Functor.IsContinuous F J K] (G : Sheaf K (Type t)) :
    Presieve.IsSheaf J (F.op ⋙ G.obj) := by
  rw [← Presieve.isSheaf_comp_uliftFunctor_iff.{t, max u₁ v₁ u₂ v₂}, ← isSheaf_iff_isSheaf_of_type,
    Presheaf.isSheaf_of_iso_iff (Functor.associator _ _ _), isSheaf_iff_isSheaf_of_type]
  apply isSheaf_of_isContinuous_aux.{t} J K
  rw [Presieve.isSheaf_comp_uliftFunctor_iff, ← isSheaf_iff_isSheaf_of_type]
  exact G.property

lemma op_comp_isSheaf [Functor.IsContinuous F J K] (G : Sheaf K A) :
    Presheaf.IsSheaf J (F.op ⋙ G.obj) :=
  fun T => F.op_comp_isSheaf_of_types J K ⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 (G.property T)⟩

lemma op_comp_isSheaf_of_isSheaf [IsContinuous F J K] (P : Dᵒᵖ ⥤ A) (h : Presheaf.IsSheaf K P) :
    Presheaf.IsSheaf J (F.op ⋙ P) :=
  F.op_comp_isSheaf J K ⟨P, h⟩

lemma W_map_of_adjunction_of_isContinuous (F : C ⥤ D) (H : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A))
    (adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op)
    [Functor.IsContinuous F J K] {G G' : Cᵒᵖ ⥤ A} (f : G ⟶ G') (hf : J.W f) :
    K.W (H.map f) := by
  intro U hU
  rw [adj.bijective_map_comp_iff]
  exact hf _ (F.op_comp_isSheaf_of_isSheaf _ _ _ hU)

lemma isContinuous_of_iso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Functor.IsContinuous F₁ J K] : Functor.IsContinuous F₂ J K where
  op_comp_isSheaf_of_types G :=
    Presieve.isSheaf_iso J (isoWhiskerRight (NatIso.op e.symm) _)
      (F₁.op_comp_isSheaf_of_types J K G)

instance isContinuous_id : Functor.IsContinuous (𝟭 C) J J where
  op_comp_isSheaf_of_types G := (isSheaf_iff_isSheaf_of_type _ _).1 G.2

lemma isContinuous_comp (F₁ : C ⥤ D) (F₂ : D ⥤ E) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (L : GrothendieckTopology E)
    [Functor.IsContinuous F₁ J K] [Functor.IsContinuous F₂ K L] :
    Functor.IsContinuous (F₁ ⋙ F₂) J L where
  op_comp_isSheaf_of_types G :=
    F₁.op_comp_isSheaf_of_types J K
      ⟨_,(isSheaf_iff_isSheaf_of_type _ _).2 (F₂.op_comp_isSheaf_of_types K L G)⟩

lemma isContinuous_comp' {F₁ : C ⥤ D} {F₂ : D ⥤ E} {F₁₂ : C ⥤ E}
    (e : F₁ ⋙ F₂ ≅ F₁₂) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (L : GrothendieckTopology E)
    [Functor.IsContinuous F₁ J K] [Functor.IsContinuous F₂ K L] :
    Functor.IsContinuous F₁₂ J L := by
  have := Functor.isContinuous_comp F₁ F₂ J K L
  apply Functor.isContinuous_of_iso e

instance [Functor.IsContinuous F J K] :
    Functor.IsContinuous (F ⋙ 𝟭 D) J K := by
  assumption

instance [Functor.IsContinuous F J K] :
    Functor.IsContinuous (𝟭 C ⋙ F) J K := by
  assumption

/-- To show a functor `F : C ⥤ D` is continuous for the topologies generated by
  precoverage `J` and `K`, it suffices to show that the image of every `J`-covering
  is a `K`-covering, if `F` preserves pairwise pullbacks of `J`-coverings. -/
lemma isContinuous_toGrothendieck_of_pullbacksPreservedBy (J : Precoverage C)
    (K : Precoverage D) [J.IsStableUnderBaseChange] [J.HasPullbacks] [K.IsStableUnderBaseChange]
    [K.HasPullbacks] [J.PullbacksPreservedBy F] (h : J ≤ K.comap F) :
    Functor.IsContinuous F J.toGrothendieck K.toGrothendieck where
  op_comp_isSheaf_of_types := fun ⟨G, H⟩ ↦ by
    rw [isSheaf_iff_isSheaf_of_type] at H
    rw [← Precoverage.toGrothendieck_toCoverage, Presieve.isSheaf_coverage] at H ⊢
    intro X R hR
    have : F.PreservesPairwisePullbacks R := J.preservesPairwisePullbacks_of_mem hR
    have : R.HasPairwisePullbacks := J.hasPairwisePullbacks_of_mem hR
    rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks]
    exact H _ (h _ hR)

section

lemma op_comp_isSheaf_of_preservesOneHypercovers
    [PreservesOneHypercovers.{w} F J K] [GrothendieckTopology.IsGeneratedByOneHypercovers.{w} J]
    (P : Dᵒᵖ ⥤ A) (hP : Presheaf.IsSheaf K P) :
    Presheaf.IsSheaf J (F.op ⋙ P) := by
  rw [Presheaf.isSheaf_iff_of_isGeneratedByOneHypercovers.{w}]
  intro X E
  exact ⟨(E.toPreOneHypercover.isLimitMapMultiforkEquiv F P)
    ((E.map F K).isLimitMultifork ⟨P, hP⟩)⟩

lemma isContinuous_of_preservesOneHypercovers
    [PreservesOneHypercovers.{w} F J K] [GrothendieckTopology.IsGeneratedByOneHypercovers.{w} J] :
    IsContinuous F J K where
  op_comp_isSheaf_of_types := by
    rintro ⟨P, hP⟩
    rw [← isSheaf_iff_isSheaf_of_type]
    exact F.op_comp_isSheaf_of_preservesOneHypercovers J K P hP

end

instance [PreservesOneHypercovers.{max u₁ v₁} F J K] :
    IsContinuous F J K :=
  isContinuous_of_preservesOneHypercovers.{max u₁ v₁} F J K

variable (A)
variable [Functor.IsContinuous F J K]

/-- The induced functor `Sheaf K A ⥤ Sheaf J A` given by `F.op ⋙ _`
if `F` is a continuous functor.
-/
@[simps!]
def sheafPushforwardContinuous : Sheaf K A ⥤ Sheaf J A :=
  ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (whiskeringLeft _ _ _).obj F.op)
    (F.op_comp_isSheaf J K)

/-- The functor `F.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A`
is induced by the precomposition with `F.op`. -/
@[simps!]
def sheafPushforwardContinuousCompSheafToPresheafIso :
    F.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A ≅
      sheafToPresheaf K A ⋙ (whiskeringLeft _ _ _).obj F.op := Iso.refl _

/-- The functor `sheafPushforwardContinuous` corresponding to the identity functor
identifies to the identity functor. -/
@[simps!]
def sheafPushforwardContinuousId :
    sheafPushforwardContinuous (𝟭 C) A J J ≅ 𝟭 _ := Iso.refl _

/-- The composition of two pushforward functors on sheaves identifies to
the pushforward for the composition of the two functors. -/
@[simps!]
def sheafPushforwardContinuousComp [IsContinuous G K L] :
    letI := isContinuous_comp F G J K L
    sheafPushforwardContinuous G A K L ⋙ sheafPushforwardContinuous F A J K ≅
    sheafPushforwardContinuous (F ⋙ G) A J L := Iso.refl _

variable {F F'} in
/-- The action of a natural transformation on pushforward functors of sheaves. -/
@[simps]
def sheafPushforwardContinuousNatTrans [IsContinuous F' J K] :
    sheafPushforwardContinuous F' A J K ⟶ sheafPushforwardContinuous F A J K where
  app M := ⟨whiskerRight (NatTrans.op τ) _⟩

variable {F F'} in
/-- The action of a natural isomorphism on pushforward functors of sheaves. -/
@[simps]
def sheafPushforwardContinuousIso [IsContinuous F' J K] :
    sheafPushforwardContinuous F A J K ≅ sheafPushforwardContinuous F' A J K where
  hom := sheafPushforwardContinuousNatTrans e.inv _ _ _
  inv := sheafPushforwardContinuousNatTrans e.hom _ _ _
  hom_inv_id := by ext; simp [← Functor.map_comp, ← op_comp]
  inv_hom_id := by ext; simp [← Functor.map_comp, ← op_comp]

/-- If a continuous functor between sites is isomorphic to the identity functor,
then the corresponding pushforward functor on sheaves identifies to the
identity functor. -/
@[simps!]
def sheafPushforwardContinuousId' [IsContinuous F'' J J] :
    sheafPushforwardContinuous F'' A J J ≅ 𝟭 _ :=
  sheafPushforwardContinuousIso eF'' _ _ _ ≪≫ sheafPushforwardContinuousId _ _

variable {F G} in
/-- When we have an isomorphism `F ⋙ G ≅ FG` between continuous functors
between sites, the composition of the pushforward functors for
`G` and `F` identifies to the pushforward functor for `FG`. -/
@[simps!]
def sheafPushforwardContinuousComp'
    [IsContinuous G K L] [IsContinuous FG J L] :
    sheafPushforwardContinuous G A K L ⋙ sheafPushforwardContinuous F A J K ≅
    sheafPushforwardContinuous FG A J L :=
  letI := isContinuous_comp F G J K L
  sheafPushforwardContinuousComp _ _ _ _ _ _ ≪≫ sheafPushforwardContinuousIso eFG _ _ _

end Functor

/-- If `F ⊣ G` is an adjunction between continuous functors, the associated
pushforwards on sheaves are adjoint. -/
@[simps!]
def Adjunction.sheafPushforwardContinuous {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]
    [G.IsContinuous K J] :
    F.sheafPushforwardContinuous E J K ⊣ G.sheafPushforwardContinuous E K J where
  unit.app P := { hom := (adj.op.whiskerLeft _).unit.app P.obj }
  counit.app P := { hom := (adj.op.whiskerLeft _).counit.app P.obj }
  left_triangle_components P := by
    ext : 1
    exact (adj.op.whiskerLeft _).left_triangle_components P.obj
  right_triangle_components P := by
    ext : 1
    exact (adj.op.whiskerLeft _).right_triangle_components P.obj

end CategoryTheory
