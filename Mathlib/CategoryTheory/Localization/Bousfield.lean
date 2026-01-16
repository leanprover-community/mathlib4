/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Local
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# Bousfield localization

Given a predicate `P : ObjectProperty C` on the objects of a category `C`,
we define `W.isLocal : MorphismProperty C` as the class of morphisms `f : X ⟶ Y`
such that for any `Z : C` such that `P Z`, the precomposition with `f`
induces a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`.

(This construction is part of the left Bousfield localization
in the context of model categories.)

When `G ⊣ F` is an adjunction with `F : C ⥤ D` fully faithful, then
`G : D ⥤ C` is a localization functor for the class `isLocal (· ∈ Set.range F.obj)`,
which then identifies to the inverse image by `G` of the class of
isomorphisms in `C`.

The dual results are also obtained.

## References

* https://ncatlab.org/nlab/show/left+Bousfield+localization+of+model+categories

-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C D : Type*} [Category* C] [Category* D]

namespace ObjectProperty

/-! ### Left Bousfield localization -/

section

variable (P : ObjectProperty C)

/-- Given `P : ObjectProperty C`, this is the class of morphisms `f : X ⟶ Y`
such that for all `Z : C` such that `P Z`, the precomposition with `f` induces
a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`. (One of the applications of this notion
is the left Bousfield localization of model categories.) -/
def isLocal : MorphismProperty C := fun _ _ f =>
  ∀ Z, P Z → Function.Bijective (fun (g : _ ⟶ Z) => f ≫ g)

variable {P} in
/-- The bijection `(Y ⟶ Z) ≃ (X ⟶ Z)` induced by `f : X ⟶ Y` when `P.isLocal f`
and `P Z`. -/
@[simps! apply]
noncomputable def isLocal.homEquiv {X Y : C} {f : X ⟶ Y} (hf : P.isLocal f) (Z : C) (hZ : P Z) :
    (Y ⟶ Z) ≃ (X ⟶ Z) :=
  Equiv.ofBijective _ (hf Z hZ)

lemma isoClosure_isLocal : P.isoClosure.isLocal = P.isLocal := by
  ext X Y f
  constructor
  · intro hf Z hZ
    exact hf _ (P.le_isoClosure _ hZ)
  · rintro hf Z ⟨Z', hZ', ⟨e⟩⟩
    constructor
    · intro g₁ g₂ eq
      rw [← cancel_mono e.hom]
      apply (hf _ hZ').1
      simp only [reassoc_of% eq]
    · intro g
      obtain ⟨a, h⟩ := (hf _ hZ').2 (g ≫ e.hom)
      exact ⟨a ≫ e.inv, by simp only [reassoc_of% h, e.hom_inv_id, comp_id]⟩

instance : P.isLocal.IsMultiplicative where
  id_mem X Z _ := by simpa [id_comp] using Function.bijective_id
  comp_mem f g hf hg Z hZ := by
    simpa using Function.Bijective.comp (hf Z hZ) (hg Z hZ)

instance : P.isLocal.HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg Z hZ := by
    rw [← Function.Bijective.of_comp_iff _ (hg Z hZ)]
    simpa using hfg Z hZ
  of_precomp f g hf hfg Z hZ := by
    rw [← Function.Bijective.of_comp_iff' (hf Z hZ)]
    simpa using hfg Z hZ

lemma isLocal_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : P.isLocal f := fun Z _ => by
  constructor
  · intro g₁ g₂ _
    simpa only [← cancel_epi f]
  · intro g
    exact ⟨inv f ≫ g, by simp⟩

lemma isLocal_iff_isIso {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y) :
    P.isLocal f ↔ IsIso f := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (hf _ hX).2 (𝟙 X)
    exact ⟨g, hg, (hf _ hY).1 (by simp only [reassoc_of% hg, comp_id])⟩
  · apply isLocal_of_isIso

instance : P.isLocal.RespectsIso where
  precomp f (_ : IsIso f) g hg := P.isLocal.comp_mem f g (isLocal_of_isIso _ f) hg
  postcomp f (_ : IsIso f) g hg := P.isLocal.comp_mem g f hg (isLocal_of_isIso _ f)

lemma le_isLocal_iff (P : ObjectProperty C) (W : MorphismProperty C) :
    W ≤ P.isLocal ↔ P ≤ W.isLocal :=
  ⟨fun h _ hZ _ _ _ hf ↦ h _ hf _ hZ,
    fun h _ _ _ hf _ hZ ↦ h _ hZ _ hf⟩

lemma galoisConnection_isLocal :
    GaloisConnection (OrderDual.toDual ∘ isLocal (C := C))
      (MorphismProperty.isLocal ∘ OrderDual.ofDual) :=
  le_isLocal_iff

end

/-! ### Right Bousfield localization -/

section

variable (P : ObjectProperty C)

/-- Given `P : ObjectProperty C`, this is the class of morphisms `g : Y ⟶ Z`
such that for all `X : C` such that `P X`, the postcomposition with `g` induces
a bijection `(X ⟶ Y) ≃ (X ⟶ Z)`. (One of the applications of this notion
is the right Bousfield localization of model categories.) -/
def isColocal : MorphismProperty C := fun _ _ g =>
  ∀ X, P X → Function.Bijective (fun (f : X ⟶ _) => f ≫ g)

variable {P} in
/-- The bijection `(X ⟶ Y) ≃ (X ⟶ Z)` induced by `g : Y ⟶ Z` when `P.isColocal g`
and `P X`. -/
@[simps! apply]
noncomputable def isColocal.homEquiv {Y Z : C} {g : Y ⟶ Z} (hg : P.isColocal g) (X : C) (hX : P X) :
    (X ⟶ Y) ≃ (X ⟶ Z) :=
  Equiv.ofBijective _ (hg X hX)

lemma isoClosure_isColocal : P.isoClosure.isColocal = P.isColocal := by
  ext Y Z g
  constructor
  · intro hg X hX
    exact hg _ (P.le_isoClosure _ hX)
  · rintro hg X ⟨X', hX', ⟨e⟩⟩
    constructor
    · intro f₁ f₂ eq
      rw [← cancel_epi e.inv]
      apply (hg _ hX').1
      simp [eq]
    · intro f
      obtain ⟨a, h⟩ := (hg _ hX').2 (e.inv ≫ f)
      exact ⟨e.hom ≫ a, by simp [h]⟩

instance : P.isColocal.IsMultiplicative where
  id_mem _ _ _ := by simpa [id_comp] using Function.bijective_id
  comp_mem f g hf hg X hX := by
    convert Function.Bijective.comp (hg X hX) (hf X hX)
    cat_disch

instance : P.isColocal.HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg X hX := by
    rw [← Function.Bijective.of_comp_iff' (hg X hX)]
    convert hfg X hX
    cat_disch
  of_precomp f g hf hfg X hX := by
    rw [← Function.Bijective.of_comp_iff _ (hf X hX)]
    convert hfg X hX
    cat_disch

lemma isColocal_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : P.isColocal f := fun Z _ => by
  constructor
  · intro g₁ g₂ _
    simpa only [← cancel_mono f]
  · intro g
    exact ⟨g ≫ inv f, by simp⟩

lemma isColocal_iff_isIso {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y) :
    P.isColocal f ↔ IsIso f := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (hf _ hY).2 (𝟙 Y)
    exact ⟨g, (hf _ hX).1 (by cat_disch), hg⟩
  · apply isColocal_of_isIso

instance : P.isColocal.RespectsIso where
  precomp f (_ : IsIso f) g hg := P.isColocal.comp_mem f g (isColocal_of_isIso _ f) hg
  postcomp f (_ : IsIso f) g hg := P.isColocal.comp_mem g f hg (isColocal_of_isIso _ f)

lemma le_isColocal_iff (P : ObjectProperty C) (W : MorphismProperty C) :
    W ≤ P.isColocal ↔ P ≤ W.isColocal :=
  ⟨fun h _ hZ _ _ _ hf ↦ h _ hf _ hZ,
    fun h _ _ _ hf _ hZ ↦ h _ hZ _ hf⟩

lemma galoisConnection_isColocal :
    GaloisConnection (OrderDual.toDual ∘ isColocal (C := C))
      (MorphismProperty.isColocal ∘ OrderDual.ofDual) :=
  le_isColocal_iff

end

/-! ### Bousfield localization and adjunctions -/

section

variable {F : C ⥤ D} {G : D ⥤ C} (adj : G ⊣ F) [F.Full] [F.Faithful]
include adj

lemma isLocal_adj_unit_app (X : D) : isLocal (· ∈ Set.range F.obj) (adj.unit.app X) := by
  rintro _ ⟨Y, rfl⟩
  convert ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.symm.trans
    (adj.homEquiv X Y)).bijective using 1
  dsimp [Adjunction.homEquiv]
  aesop

lemma isLocal_iff_isIso_map {X Y : D} (f : X ⟶ Y) :
    isLocal (· ∈ Set.range F.obj) f ↔ IsIso (G.map f) := by
  have := adj.unit.naturality f
  dsimp at this
  rw [← (isLocal (· ∈ Set.range F.obj)).postcomp_iff _ _ (isLocal_adj_unit_app adj Y),
    this, (isLocal (· ∈ Set.range F.obj)).precomp_iff _ _ (isLocal_adj_unit_app adj X),
    isLocal_iff_isIso _ _ ⟨_, rfl⟩ ⟨_, rfl⟩]
  exact ⟨fun _ ↦ isIso_of_fully_faithful F (G.map f), fun _ ↦ inferInstance⟩

lemma isLocal_eq_inverseImage_isomorphisms :
    isLocal (· ∈ Set.range F.obj) = (MorphismProperty.isomorphisms _).inverseImage G := by
  ext P₁ P₂ f
  rw [isLocal_iff_isIso_map adj]
  rfl

lemma isLocalization_isLocal : G.IsLocalization (isLocal (· ∈ Set.range F.obj)) := by
  rw [isLocal_eq_inverseImage_isomorphisms adj]
  exact adj.isLocalization

end

section

variable {F : C ⥤ D} {G : D ⥤ C} (adj : G ⊣ F) [G.Full] [G.Faithful]
include adj

lemma isColocal_adj_counit_app (X : C) : isColocal (· ∈ Set.range G.obj) (adj.counit.app X) := by
  rintro _ ⟨Y, rfl⟩
  convert ((Functor.FullyFaithful.ofFullyFaithful G).homEquiv.symm.trans
    (adj.homEquiv Y X).symm).bijective using 1
  dsimp [Adjunction.homEquiv]
  cat_disch

lemma isColocal_iff_isIso_map {X Y : C} (f : X ⟶ Y) :
    isColocal (· ∈ Set.range G.obj) f ↔ IsIso (F.map f) := by
  have := adj.counit.naturality f
  dsimp at this
  rw [← (isColocal _).precomp_iff _ _ (isColocal_adj_counit_app adj X),
    ← this, (isColocal _).postcomp_iff _ _ (isColocal_adj_counit_app adj Y),
    isColocal_iff_isIso _ _ ⟨_, rfl⟩ ⟨_, rfl⟩]
  exact ⟨fun _ ↦ isIso_of_fully_faithful G (F.map f), fun _ ↦ inferInstance⟩

lemma isColocal_eq_inverseImage_isomorphisms :
    isColocal (· ∈ Set.range G.obj) = (MorphismProperty.isomorphisms _).inverseImage F := by
  ext P₁ P₂ f
  rw [isColocal_iff_isIso_map adj]
  rfl

lemma isLocalization_isColocal : F.IsLocalization (isColocal (· ∈ Set.range G.obj)) := by
  rw [isColocal_eq_inverseImage_isomorphisms adj]
  exact adj.isLocalization'

end

end ObjectProperty

open Localization

lemma ObjectProperty.le_isLocal_isLocal (P : ObjectProperty C) :
    P ≤ P.isLocal.isLocal := by
  rw [← le_isLocal_iff]

lemma MorphismProperty.le_isLocal_isLocal (W : MorphismProperty C) :
    W ≤ W.isLocal.isLocal := by
  rw [ObjectProperty.le_isLocal_iff]

lemma ObjectProperty.le_isColocal_isColocal (P : ObjectProperty C) :
    P ≤ P.isColocal.isColocal := by
  rw [← le_isColocal_iff]

lemma MorphismProperty.le_isColocal_isColocal (W : MorphismProperty C) :
    W ≤ W.isColocal.isColocal := by
  rw [ObjectProperty.le_isColocal_iff]

@[deprecated (since := "2025-11-20")] alias ObjectProperty.le_isLocal_W :=
  ObjectProperty.le_isLocal_isLocal
@[deprecated (since := "2025-11-20")] alias MorphismProperty.le_leftBousfieldW_isLocal :=
  MorphismProperty.le_isLocal_isLocal

namespace Localization.LeftBousfield

open ObjectProperty

@[deprecated (since := "2025-11-20")] alias W := isLocal
@[deprecated (since := "2025-11-20")] alias W.homEquiv := isLocal.homEquiv
@[deprecated (since := "2025-11-20")] alias W_isoClosure := isoClosure_isLocal
@[deprecated (since := "2025-11-20")] alias W_of_isIso := isLocal_of_isIso
@[deprecated (since := "2025-11-20")] alias W_iff_isIso := isLocal_iff_isIso
@[deprecated (since := "2025-11-20")] alias le_W_iff := le_isLocal_iff
@[deprecated (since := "2025-11-20")] alias galoisConnection := galoisConnection_isLocal
@[deprecated (since := "2025-11-20")] alias W_adj_unit_app := isLocal_adj_unit_app
@[deprecated (since := "2025-11-20")] alias W_iff_isIso_map := isLocal_iff_isIso_map
@[deprecated (since := "2025-11-20")] alias W_eq_inverseImage_isomorphisms :=
  isLocal_eq_inverseImage_isomorphisms
@[deprecated (since := "2025-11-20")] alias isLocalization := isLocalization_isLocal

end Localization.LeftBousfield

end CategoryTheory
