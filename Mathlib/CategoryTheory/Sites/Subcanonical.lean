/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
/-!

# Subcanonical Grothendieck topologies

This file provides some API for the Yoneda embedding into the category of sheaves for a
subcanonical Grothendieck topology.
-/

@[expose] public section

universe v' v u

namespace CategoryTheory.GrothendieckTopology

open Opposite Functor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [Subcanonical J]

/--
The equivalence between natural transformations from the yoneda embedding (to the sheaf category)
and elements of `F.obj.obj X`.
-/
def yonedaEquiv {X : C} {F : Sheaf J (Type v)} : (J.yoneda.obj X ⟶ F) ≃ F.obj.obj (op X) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.yonedaEquiv

theorem yonedaEquiv_apply {X : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F) :
    yonedaEquiv J f = f.hom.app (op X) (𝟙 X) :=
  rfl

@[simp]
theorem yonedaEquiv_symm_app_apply {X : C} {F : Sheaf J (Type v)} (x : F.obj.obj (op X)) (Y : Cᵒᵖ)
    (f : Y.unop ⟶ X) : (J.yonedaEquiv.symm x).hom.app Y f = F.obj.map f.op x :=
  rfl

/-- See also `yonedaEquiv_naturality'` for a more general version. -/
lemma yonedaEquiv_naturality {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.obj.map g.op (J.yonedaEquiv f) = J.yonedaEquiv (J.yoneda.map g ≫ f) := by
  simp [yonedaEquiv, CategoryTheory.yonedaEquiv_naturality]
  rfl

/--
Variant of `yonedaEquiv_naturality` with general `g`. This is technically strictly more general
than `yonedaEquiv_naturality`, but `yonedaEquiv_naturality` is sometimes preferable because it
can avoid the "motive is not type correct" error.
-/
lemma yonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.obj.map g (J.yonedaEquiv f) = J.yonedaEquiv (J.yoneda.map g.unop ≫ f) :=
  J.yonedaEquiv_naturality _ _

lemma yonedaEquiv_comp {X : C} {F G : Sheaf J (Type v)} (α : J.yoneda.obj X ⟶ F) (β : F ⟶ G) :
    J.yonedaEquiv (α ≫ β) = β.hom.app _ (J.yonedaEquiv α) :=
  rfl

lemma yonedaEquiv_yoneda_map {X Y : C} (f : X ⟶ Y) : J.yonedaEquiv (J.yoneda.map f) = f := by
  rw [yonedaEquiv_apply]
  simp

lemma yonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Sheaf J (Type v))
    (x : F.obj.obj ⟨X⟩) : J.yoneda.map f ≫ J.yonedaEquiv.symm x = J.yonedaEquiv.symm
      ((F.obj.map f.op) x) := by
  apply J.yonedaEquiv.injective
  simp only [yonedaEquiv_comp, yonedaEquiv_symm_app_apply, Equiv.apply_symm_apply]
  rw [yonedaEquiv_yoneda_map]

lemma yonedaEquiv_symm_naturality_right (X : C) {F F' : Sheaf J (Type v)} (f : F ⟶ F')
    (x : F.obj.obj ⟨X⟩) : J.yonedaEquiv.symm x ≫ f = J.yonedaEquiv.symm (f.hom.app ⟨X⟩ x) := by
  apply J.yonedaEquiv.injective
  simp [yonedaEquiv_comp]

/-- See also `map_yonedaEquiv'` for a more general version. -/
lemma map_yonedaEquiv {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.obj.map g.op (J.yonedaEquiv f) = f.hom.app (op Y) g := by
  rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/--
Variant of `map_yonedaEquiv` with general `g`. This is technically strictly more general
than `map_yonedaEquiv`, but `map_yonedaEquiv` is sometimes preferable because it
can avoid the "motive is not type correct" error.
-/
lemma map_yonedaEquiv' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.obj.map g (J.yonedaEquiv f) = f.hom.app Y g.unop := by
  rw [yonedaEquiv_naturality', yonedaEquiv_comp, yonedaEquiv_yoneda_map]

lemma yonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type v)} (t : F.obj.obj X) :
    J.yonedaEquiv.symm (F.obj.map f t) = J.yoneda.map f.unop ≫ J.yonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := J.yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/--
Two morphisms of sheaves of types `P ⟶ Q` coincide if the precompositions with morphisms
`yoneda.obj X ⟶ P` agree.
-/
lemma hom_ext_yoneda {P Q : Sheaf J (Type v)} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : J.yoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using congr_arg (J.yonedaEquiv) (h _ (J.yonedaEquiv.symm x))

/-- The Yoneda lemma for sheaves. -/
@[simps! hom_app_app_down inv_app_app]
def yonedaOpCompCoyoneda :
    J.yoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type v) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u} ⋙
      (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _) :=
  ((isoWhiskerLeft _ sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm).trans
    (isoWhiskerRight (NatIso.op J.yonedaCompSheafToPresheaf.symm)
    (_ ⋙ (whiskeringLeft _ _ _).obj _))).trans
    (isoWhiskerRight CategoryTheory.largeCurriedYonedaLemma ((whiskeringLeft _ _ _).obj _))

/-- A version of `yonedaEquiv` for `uliftYoneda`. -/
def uliftYonedaEquiv {X : C} {F : Sheaf J (Type (max v v'))} :
    ((uliftYoneda.{v'} J).obj X ⟶ F) ≃ F.obj.obj (op X) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.uliftYonedaEquiv

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv := uliftYonedaEquiv

theorem uliftYonedaEquiv_apply {X : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) : uliftYonedaEquiv.{v'} J f = f.hom.app (op X) ⟨𝟙 X⟩ :=
  rfl

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_apply := uliftYonedaEquiv_apply

@[simp]
theorem uliftYonedaEquiv_symm_app_apply {X : C} {F : Sheaf J (Type (max v v'))}
    (x : F.obj.obj (op X)) (Y : Cᵒᵖ) (f : Y.unop ⟶ X) :
    (J.uliftYonedaEquiv.symm x).hom.app Y ⟨f⟩ = F.obj.map f.op x :=
  rfl

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_symm_app_apply :=
  uliftYonedaEquiv_symm_app_apply

/-- See also `uliftYonedaEquiv_naturality'` for a more general version. -/
lemma uliftYonedaEquiv_naturality {X Y : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) (g : Y ⟶ X) :
      F.obj.map g.op (J.uliftYonedaEquiv f) = J.uliftYonedaEquiv (J.uliftYoneda.map g ≫ f) := by
  change (f.hom.app (op X) ≫ F.obj.map g.op) ⟨𝟙 X⟩ = f.hom.app (op Y) ⟨𝟙 Y ≫ g⟩
  rw [← f.hom.naturality]
  simp [uliftYoneda]

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_naturality :=
  uliftYonedaEquiv_naturality

/-- Variant of `uliftYonedaEquiv_naturality` with general `g`. This is technically strictly more
general than `uliftYonedaEquiv_naturality`, but `uliftYonedaEquiv_naturality` is sometimes
preferable because it can avoid the "motive is not type correct" error. -/
lemma uliftYonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) :
    F.obj.map g (J.uliftYonedaEquiv f) = J.uliftYonedaEquiv (J.uliftYoneda.map g.unop ≫ f) :=
  J.uliftYonedaEquiv_naturality _ _

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_naturality' :=
  uliftYonedaEquiv_naturality'

lemma uliftYonedaEquiv_comp {X : C} {F G : Sheaf J (Type (max v v'))} (α : J.uliftYoneda.obj X ⟶ F)
    (β : F ⟶ G) : J.uliftYonedaEquiv (α ≫ β) = β.hom.app _ (J.uliftYonedaEquiv α) :=
  rfl

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_comp := uliftYonedaEquiv_comp

lemma uliftYonedaEquiv_uliftYoneda_map {X Y : C} (f : X ⟶ Y) :
    (uliftYonedaEquiv.{v'} J) (J.uliftYoneda.map f) = ⟨f⟩ := by
  rw [uliftYonedaEquiv_apply]
  simp [uliftYoneda]

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_yonedaULift_map :=
  uliftYonedaEquiv_uliftYoneda_map

lemma uliftYonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Sheaf J (Type (max v v')))
    (x : F.obj.obj ⟨X⟩) :
    J.uliftYoneda.map f ≫ J.uliftYonedaEquiv.symm x =
      J.uliftYonedaEquiv.symm ((F.obj.map f.op) x) := by
  apply J.uliftYonedaEquiv.injective
  simp only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [uliftYonedaEquiv_uliftYoneda_map]
  rfl

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_symm_naturality_left :=
  uliftYonedaEquiv_symm_naturality_left

lemma uliftYonedaEquiv_symm_naturality_right (X : C) {F F' : Sheaf J (Type (max v v'))}
    (f : F ⟶ F') (x : F.obj.obj ⟨X⟩) :
    J.uliftYonedaEquiv.symm x ≫ f = J.uliftYonedaEquiv.symm (f.hom.app ⟨X⟩ x) := by
  apply J.uliftYonedaEquiv.injective
  simp [uliftYonedaEquiv_comp]

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_symm_naturality_right :=
  uliftYonedaEquiv_symm_naturality_right

/-- See also `map_yonedaEquiv'` for a more general version. -/
lemma map_uliftYonedaEquiv {X Y : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) (g : Y ⟶ X) :
    F.obj.map g.op (J.uliftYonedaEquiv f) = f.hom.app (op Y) ⟨g⟩ := by
  rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]

@[deprecated (since := "2025-11-10")] alias map_yonedaULiftEquiv := map_uliftYonedaEquiv

/-- Variant of `map_uliftYonedaEquiv` with general `g`. This is technically strictly more general
than `map_uliftYonedaEquiv`, but `map_uliftYonedaEquiv` is sometimes preferable because it
can avoid the "motive is not type correct" error. -/
lemma map_uliftYonedaEquiv' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) :
    F.obj.map g (J.uliftYonedaEquiv f) = f.hom.app Y ⟨g.unop⟩ := by
  rw [uliftYonedaEquiv_naturality', uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]

@[deprecated (since := "2025-11-10")] alias map_yonedaULiftEquiv' := map_uliftYonedaEquiv'

lemma uliftYonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type (max v v'))}
    (t : F.obj.obj X) : J.uliftYonedaEquiv.symm (F.obj.map f t) =
      J.uliftYoneda.map f.unop ≫ J.uliftYonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := J.uliftYonedaEquiv.surjective t
  rw [uliftYonedaEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_symm_map := uliftYonedaEquiv_symm_map

/-- Two morphisms of sheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `uliftYoneda.obj X ⟶ P` agree. -/
lemma hom_ext_uliftYoneda {P Q : Sheaf J (Type (max v v'))} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : J.uliftYoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    using congr_arg (J.uliftYonedaEquiv) (h _ (J.uliftYonedaEquiv.symm x))

@[deprecated (since := "2025-11-10")] alias hom_ext_yonedaULift := hom_ext_uliftYoneda

/-- A variant of the Yoneda lemma for sheaves with a raise in the universe level. -/
@[simps! -isSimp]
def uliftYonedaOpCompCoyoneda :
    J.uliftYoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type max v v') ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u} ⋙
      (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _) :=
  ((isoWhiskerLeft (J.yoneda.op ⋙ (sheafCompose J _).op)
    sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm).trans
    (isoWhiskerRight (NatIso.op (J.uliftYonedaCompSheafToPresheaf.symm))
    (_ ⋙ (whiskeringLeft _ _ _).obj _))).trans
    (isoWhiskerRight CategoryTheory.uliftYonedaOpCompCoyoneda
    ((whiskeringLeft _ _ _).obj _))

attribute [simp] uliftYonedaOpCompCoyoneda_hom_app_app_down

@[simp]
lemma uliftYonedaOpCompCoyoneda_inv_app_app (X : Cᵒᵖ) (F : Sheaf J (Type max v v'))
    (s : ULift.{u} (F.obj.obj X)) :
    (J.uliftYonedaOpCompCoyoneda.inv.app X).app F s = J.uliftYonedaEquiv.symm s.down :=
  rfl

lemma uliftYonedaOpCompCoyoneda_app_app (X : Cᵒᵖ) (F : Sheaf J (Type (max v v'))) :
    (J.uliftYonedaOpCompCoyoneda.app X).app F = (J.uliftYonedaEquiv.trans Equiv.ulift.symm).toIso :=
  rfl

open Limits

instance preservesLimitsOfSize_yoneda : PreservesLimitsOfSize J.yoneda := by
  refine ⟨fun {I} _ ↦ ?_⟩
  have : PreservesLimitsOfShape I (J.yoneda ⋙ sheafToPresheaf J _) :=
    inferInstanceAs <| PreservesLimitsOfShape I CategoryTheory.yoneda
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J _)

/--
Let `{ Xᵢ ⟶ Y }` be a family of pairwise disjoint maps that form a cover in `J`. Then its
image under the yoneda embedding to `J`-sheaves is a coproduct.
-/
noncomputable def isColimitCofanMkYoneda {ι : Type*} (X : ι → C) {c : Cofan X}
    (H : (Sieve.ofArrows _ c.inj) ∈ J c.pt) [∀ (i : ι), Mono (c.inj i)]
    (hempty : (Y : C) → IsInitial Y → ⊥ ∈ J Y)
    (hdisj : ∀ {i j : ι} (_ : i ≠ j) {Y : C} (a : Y ⟶ X i)
      (b : Y ⟶ X j), a ≫ c.inj i = b ≫ c.inj j → Nonempty (IsInitial Y)) :
    IsColimit (Cofan.mk _ fun i ↦ J.yoneda.map (c.inj i)) := by
  have heq (s : Cofan fun i ↦ J.yoneda.obj (X i))
      {Y : C} {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j) (hab : a ≫ c.inj i = b ≫ c.inj j) :
      (s.inj i).hom.app (op Y) a = (s.inj j).hom.app (op Y) b := by
    by_cases h : i = j
    · subst h
      rw [(cancel_mono _).mp hab]
    · obtain ⟨h⟩ := hdisj h a b hab
      have := Types.isTerminalEquivUnique _ (Sheaf.isTerminalOfBotCover s.pt _ (hempty Y h))
      exact Subsingleton.elim _ _
  refine mkCofanColimit _ (fun s ↦ ObjectProperty.homMk ?_) (fun s j ↦ ?_) fun s m hm ↦ ?_
  · refine (s.pt.property.isSheafFor _ H).extend ?_
    refine ⟨fun Y g ↦ ((s.inj (Sieve.ofArrows.i g.2)).hom.app Y) (Sieve.ofArrows.h g.2), ?_⟩
    intro ⟨Y⟩ ⟨Z⟩ ⟨(g : Z ⟶ Y)⟩
    ext u
    dsimp
    rw [← heq s (g ≫ Sieve.ofArrows.h u.2)
      (Sieve.ofArrows.h <| Sieve.downward_closed _ u.2 g) (by simp)]
    exact congrFun ((s.inj _).hom.naturality g.op) _
  · ext : 1
    let u (j : ι) : CategoryTheory.yoneda.obj (X j) ⟶ (Sieve.ofArrows _ c.inj).functor :=
      (Sieve.ofArrows _ c.inj).toFunctor (c.inj j) (Sieve.ofArrows_mk _ _ j)
    have (j : ι) : u j ≫ (Sieve.ofArrows _ c.inj).functorInclusion =
      CategoryTheory.yoneda.map (c.inj j) := rfl
    dsimp
    simp only [← this, Category.assoc, Presieve.IsSheafFor.functorInclusion_comp_extend]
    ext Z (g : Z.unop ⟶ X j)
    have h : Sieve.ofArrows X c.inj (g ≫ c.inj j) :=
      Sieve.downward_closed _ (Sieve.ofArrows_mk _ _ j) _
    exact heq s (Sieve.ofArrows.h h) g (by simp)
  · ext : 1
    dsimp
    apply Presieve.IsSheafFor.unique_extend
    ext Y ⟨g, hg⟩
    simp [← hm (Sieve.ofArrows.i hg)]

/-- If the coproduct inclusions form a covering of `J` and coproducts are disjoint,
the yoneda embedding to `J`-sheaves preserves coproducts. -/
lemma preservesColimitsOfShape_yoneda_of_ofArrows_inj_mem {ι : Type*}
    [CoproductsOfShapeDisjoint C ι] [HasPullbacks C] [HasStrictInitialObjects C]
    (hcov : ∀ {X : ι → C} {c : Cofan X} (_ : IsColimit c), Sieve.ofArrows X c.inj ∈ J c.pt)
    (htriv : ∀ (Y : C), IsInitial Y → ⊥ ∈ J Y) :
    PreservesColimitsOfShape (Discrete ι) J.yoneda := by
  apply (config := { allowSynthFailures := true }) preservesColimitsOfShape_of_discrete
  refine fun X ↦ ⟨fun {c : Cofan X} hc ↦ ⟨(Limits.Cofan.isColimitMapCoconeEquiv _ _ _).symm ?_⟩⟩
  have (i : ι) : Mono (c.inj i) := .of_coproductDisjoint hc _
  refine isColimitCofanMkYoneda _ _ (hcov hc) htriv fun hij Y a b hab ↦ ⟨?_⟩
  exact .ofCoproductDisjointOfCommSq hij hc _ _ hab

end CategoryTheory.GrothendieckTopology
