/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Enriched.Ordinary
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.Shapes.End

/-!
# Functor categories are enriched

If `C` is a `V`-enriched ordinary category, then `J ⥤ C` is also
a `V`-enriched ordinary category, provided `C` has suitable limits.

-/

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Enriched.FunctorCategory

open Category MonoidalCategory Limits

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V]
  {C : Type u₂} [Category.{v₂} C]
  {J : Type u₃} [Category.{v₃} J]
  {K : Type u₄} [Category.{v₄} K]
  [EnrichedOrdinaryCategory V C]

variable (F₁ F₂ F₃ F₄ : J ⥤ C)

/-- Given two functors `F₁` and `F₂` from a category `J` to a `V`-enriched
ordinary category `C`, this is the diagram `Jᵒᵖ ⥤ J ⥤ V` whose end shall be
the `V`-morphisms in `J ⥤ V` from `F₁` to `F₂`. -/
@[simps!]
def diagram : Jᵒᵖ ⥤ J ⥤ V := F₁.op ⋙ eHomFunctor V C ⋙ (whiskeringLeft J C V).obj F₂

/-- The condition that the end `diagram V F₁ F₂` exists, see `enrichedHom`. -/
abbrev HasEnrichedHom := HasEnd (diagram V F₁ F₂)

section

variable [HasEnrichedHom V F₁ F₂]

/-- The `V`-enriched hom from `F₁` to `F₂` when `F₁` and `F₂` are functors `J ⥤ C`
and `C` is a `V`-enriched category. -/
noncomputable abbrev enrichedHom : V := end_ (diagram V F₁ F₂)

/-- The projection `enrichedHom V F₁ F₂ ⟶ F₁.obj j ⟶[V] F₂.obj j` in the category `V`
for any `j : J` when `F₁` and `F₂` are functors `J ⥤ C` and `C` is a `V`-enriched category. -/
noncomputable abbrev enrichedHomπ (j : J) : enrichedHom V F₁ F₂ ⟶ F₁.obj j ⟶[V] F₂.obj j :=
  end_.π _ j

@[reassoc]
lemma enrichedHom_condition {i j : J} (f : i ⟶ j) :
    enrichedHomπ V F₁ F₂ i ≫ (ρ_ _).inv ≫
      _ ◁ (eHomEquiv V) (F₂.map f) ≫ eComp V _ _ _  =
    enrichedHomπ V F₁ F₂ j ≫ (λ_ _).inv ≫
      (eHomEquiv V) (F₁.map f) ▷ _ ≫ eComp V _ _ _ :=
  end_.condition (diagram V F₁ F₂) f

variable {F₁ F₂}

/-- Given functors `F₁` and `F₂` in `J ⥤ C`, where `C` is a `V`-enriched ordinary category,
this is the isomorphism `(F₁ ⟶ F₂) ≃ (𝟙_ V ⟶ enrichedHom V F₁ F₂)` in the category `V`. -/
noncomputable def homEquiv : (F₁ ⟶ F₂) ≃ (𝟙_ V ⟶ enrichedHom V F₁ F₂) where
  toFun τ := end_.lift (fun j ↦ eHomEquiv V (τ.app j)) (fun i j f ↦ by
    trans eHomEquiv V (τ.app i ≫ F₂.map f)
    · dsimp
      simp only [eHomEquiv_comp, tensorHom_def_assoc, MonoidalCategory.whiskerRight_id,
        ← unitors_equal, assoc, Iso.inv_hom_id_assoc, eHomWhiskerLeft]
    · dsimp
      simp only [← NatTrans.naturality, eHomEquiv_comp, tensorHom_def', id_whiskerLeft,
        assoc, Iso.inv_hom_id_assoc, eHomWhiskerRight])
  invFun g :=
    { app := fun j ↦ (eHomEquiv V).symm (g ≫ end_.π _ j)
      naturality := fun i j f ↦ (eHomEquiv V).injective (by
        dsimp
        simp only [eHomEquiv_comp, Equiv.apply_symm_apply, Iso.cancel_iso_inv_left]
        conv_rhs =>
          rw [tensorHom_def_assoc, MonoidalCategory.whiskerRight_id_assoc, assoc,
            enrichedHom_condition V F₁ F₂ f]
        conv_lhs =>
          rw [tensorHom_def'_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
            id_whiskerLeft_assoc, id_whiskerLeft_assoc, Iso.inv_hom_id_assoc, unitors_equal]) }
  left_inv τ := by aesop
  right_inv g := by aesop

@[reassoc (attr := simp)]
lemma homEquiv_apply_π (τ : F₁ ⟶ F₂) (j : J) :
    homEquiv V τ ≫ enrichedHomπ V _ _ j = eHomEquiv V (τ.app j) := by
  simp [homEquiv]

end

section

variable [HasEnrichedHom V F₁ F₁]

/-- The identity for the `V`-enrichment of the category `J ⥤ C` over `V`. -/
noncomputable def enrichedId : 𝟙_ V ⟶ enrichedHom V F₁ F₁ := homEquiv _ (𝟙 F₁)

@[reassoc (attr := simp)]
lemma enrichedId_π (j : J) : enrichedId V F₁ ≫ end_.π _ j = eId V (F₁.obj j) := by
  simp [enrichedId]

@[simp]
lemma homEquiv_id : homEquiv V (𝟙 F₁) = enrichedId V F₁ := rfl

end

section

variable [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₂ F₃] [HasEnrichedHom V F₁ F₃]

/-- The composition for the `V`-enrichment of the category `J ⥤ C` over `V`. -/
noncomputable def enrichedComp : enrichedHom V F₁ F₂ ⊗ enrichedHom V F₂ F₃ ⟶ enrichedHom V F₁ F₃ :=
  end_.lift (fun j ↦ (end_.π _ j ⊗ end_.π _ j) ≫ eComp V _ _ _) (fun i j f ↦ by
    dsimp
    trans (end_.π (diagram V F₁ F₂) i ⊗ end_.π (diagram V F₂ F₃) j) ≫
      (ρ_ _).inv ▷ _ ≫ (_ ◁ (eHomEquiv V (F₂.map f))) ▷ _ ≫ eComp V _ (F₂.obj i) _ ▷ _ ≫
        eComp V _ (F₂.obj j) _
    · have := end_.condition (diagram V F₂ F₃) f
      dsimp [eHomWhiskerLeft, eHomWhiskerRight] at this ⊢
      conv_lhs => rw [assoc, tensorHom_def_assoc]
      conv_rhs =>
        rw [tensorHom_def_assoc, whisker_assoc_assoc, e_assoc,
          triangle_assoc_comp_right_inv_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
          assoc, assoc, ← this, MonoidalCategory.whiskerLeft_comp_assoc,
          MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
          ← e_assoc, whiskerLeft_rightUnitor_inv_assoc, associator_inv_naturality_right_assoc,
          Iso.hom_inv_id_assoc, whisker_exchange_assoc, MonoidalCategory.whiskerRight_id_assoc,
          Iso.inv_hom_id_assoc]
    · have := end_.condition (diagram V F₁ F₂) f
      dsimp [eHomWhiskerLeft, eHomWhiskerRight] at this ⊢
      conv_lhs =>
        rw [tensorHom_def'_assoc, ← comp_whiskerRight_assoc,
          ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc,
          assoc, assoc, this, comp_whiskerRight_assoc, comp_whiskerRight_assoc,
          comp_whiskerRight_assoc, leftUnitor_inv_whiskerRight_assoc,
          ← associator_inv_naturality_left_assoc, ← e_assoc',
          Iso.inv_hom_id_assoc, ← whisker_exchange_assoc, id_whiskerLeft_assoc,
          Iso.inv_hom_id_assoc]
      conv_rhs => rw [assoc, tensorHom_def'_assoc])

@[reassoc (attr := simp)]
lemma enrichedComp_π (j : J) :
    enrichedComp V F₁ F₂ F₃ ≫ end_.π _ j =
      (end_.π (diagram V F₁ F₂) j ⊗ end_.π (diagram V F₂ F₃) j) ≫ eComp V _ _ _ := by
  simp [enrichedComp]

variable {F₁ F₂ F₃}

@[reassoc]
lemma homEquiv_comp (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) :
    (homEquiv V) (f ≫ g) = (λ_ (𝟙_ V)).inv ≫ ((homEquiv V) f ⊗ (homEquiv V) g) ≫
    enrichedComp V F₁ F₂ F₃ := by
  ext j
  simp only [homEquiv_apply_π, NatTrans.comp_app, eHomEquiv_comp, assoc,
    enrichedComp_π, Functor.op_obj, ← tensor_comp_assoc]

end

@[reassoc (attr := simp)]
lemma enriched_id_comp [HasEnrichedHom V F₁ F₁] [HasEnrichedHom V F₁ F₂] :
    (λ_ (enrichedHom V F₁ F₂)).inv ≫ enrichedId V F₁ ▷ enrichedHom V F₁ F₂ ≫
      enrichedComp V F₁ F₁ F₂ = 𝟙 _ := by
  ext j
  rw [assoc, assoc, enrichedComp_π, id_comp, tensorHom_def, assoc,
    ← comp_whiskerRight_assoc, enrichedId_π, ← whisker_exchange_assoc,
    id_whiskerLeft, assoc, assoc, Iso.inv_hom_id_assoc]
  dsimp
  rw [e_id_comp, comp_id]

@[reassoc (attr := simp)]
lemma enriched_comp_id [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₂ F₂] :
    (ρ_ (enrichedHom V F₁ F₂)).inv ≫ enrichedHom V F₁ F₂ ◁ enrichedId V F₂ ≫
      enrichedComp V F₁ F₂ F₂ = 𝟙 _ := by
  ext j
  rw [assoc, assoc, enrichedComp_π, id_comp, tensorHom_def', assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, enrichedId_π,
    whisker_exchange_assoc, MonoidalCategory.whiskerRight_id, assoc, assoc,
    Iso.inv_hom_id_assoc]
  dsimp
  rw [e_comp_id, comp_id]

@[reassoc]
lemma enriched_assoc [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ F₃] [HasEnrichedHom V F₁ F₄]
    [HasEnrichedHom V F₂ F₃] [HasEnrichedHom V F₂ F₄] [HasEnrichedHom V F₃ F₄] :
    (α_ (enrichedHom V F₁ F₂) (enrichedHom V F₂ F₃) (enrichedHom V F₃ F₄)).inv ≫
      enrichedComp V F₁ F₂ F₃ ▷ enrichedHom V F₃ F₄ ≫ enrichedComp V F₁ F₃ F₄ =
      enrichedHom V F₁ F₂ ◁ enrichedComp V F₂ F₃ F₄ ≫ enrichedComp V F₁ F₂ F₄ := by
  ext j
  conv_lhs =>
    rw [assoc, assoc, enrichedComp_π,
      tensorHom_def_assoc, ← comp_whiskerRight_assoc, enrichedComp_π,
      comp_whiskerRight_assoc, ← whisker_exchange_assoc,
      ← whisker_exchange_assoc, ← tensorHom_def'_assoc, ← associator_inv_naturality_assoc]
  conv_rhs =>
    rw [assoc, enrichedComp_π, tensorHom_def'_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      enrichedComp_π, MonoidalCategory.whiskerLeft_comp_assoc, whisker_exchange_assoc,
      whisker_exchange_assoc, ← tensorHom_def_assoc]
  dsimp
  rw [e_assoc]

variable (J C)

/-- If `C` is a `V`-enriched ordinary category, and `C` has suitable limits,
then `J ⥤ C` is also a `V`-enriched ordinary category. -/
noncomputable def enrichedOrdinaryCategory [∀ (F₁ F₂ : J ⥤ C), HasEnrichedHom V F₁ F₂] :
    EnrichedOrdinaryCategory V (J ⥤ C) where
  Hom F₁ F₂ := enrichedHom V F₁ F₂
  id F := enrichedId V F
  comp F₁ F₂ F₃ := enrichedComp V F₁ F₂ F₃
  assoc _ _ _ _ := enriched_assoc _ _ _ _ _
  homEquiv := homEquiv V
  homEquiv_id _ := homEquiv_id V _
  homEquiv_comp f g := homEquiv_comp V f g

variable {J C}

section

variable (G : K ⥤ J) [HasEnrichedHom V F₁ F₂]
  [HasEnrichedHom V (G ⋙ F₁) (G ⋙ F₂)]

noncomputable def precompEnrichedHom :
    enrichedHom V F₁ F₂ ⟶ enrichedHom V (G ⋙ F₁) (G ⋙ F₂) :=
  end_.lift (fun _ ↦ enrichedHomπ _ _ _ _)
    (fun _ _ f ↦ enrichedHom_condition V F₁ F₂ (G.map f))

@[reassoc (attr := simp)]
lemma precompEnrichedHom_π (k : K) :
    precompEnrichedHom V F₁ F₂ G ≫ enrichedHomπ _ _ _ k = enrichedHomπ _ _ _ (G.obj k) := by
  apply end_.lift_π

end

section

abbrev HasPresheafEnrichedHom :=
  ∀ (j : J), HasEnrichedHom V (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₂)

variable [HasPresheafEnrichedHom V F₁ F₂]

instance {j j' : J} (f : j ⟶ j') :
    HasEnrichedHom V (Under.map f ⋙ Under.forget j ⋙ F₁)
      (Under.map f ⋙ Under.forget j ⋙ F₂) :=
  inferInstanceAs (HasEnrichedHom V (Under.forget j' ⋙ F₁) (Under.forget j' ⋙ F₂))

@[simps!]
noncomputable def presheafEnrichedHom : J ⥤ V where
  obj j := enrichedHom V (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₂)
  map f := precompEnrichedHom V (Under.forget _ ⋙ F₁) (Under.forget _ ⋙ F₂) (Under.map f)
  map_id X := by
    dsimp
    ext j
    rw [precompEnrichedHom_π, id_comp]
    congr 1
    simp [Under.map, Comma.mapLeft]
    rfl
  map_comp f g := by
    dsimp
    ext j
    rw [assoc, precompEnrichedHom_π]
    erw [precompEnrichedHom_π, precompEnrichedHom_π]
    congr 1
    simp [Under.map, Comma.mapLeft]

variable [HasEnrichedHom V F₁ F₂]

@[simps pt]
noncomputable def conePresheafEnrichedHom : Cone (presheafEnrichedHom V F₁ F₂) where
  pt := enrichedHom V F₁ F₂
  π :=
    { app := fun j ↦ precompEnrichedHom V F₁ F₂ (Under.forget j)
      naturality := fun j j' f ↦ by
        dsimp
        rw [id_comp]
        ext k
        rw [assoc, precompEnrichedHom_π]
        erw [precompEnrichedHom_π]
        rw [precompEnrichedHom_π]
        rfl }

namespace isLimitConePresheafEnrichedHom

variable {V F₁ F₂} (s : Cone (presheafEnrichedHom V F₁ F₂))

noncomputable def lift : s.pt ⟶ enrichedHom V F₁ F₂ :=
  end_.lift (fun j ↦ s.π.app j ≫ enrichedHomπ V _ _ (Under.mk (𝟙 j))) (fun j j' f ↦ by
    dsimp
    rw [← s.w f, assoc, assoc, assoc]
    dsimp [presheafEnrichedHom]
    erw [precompEnrichedHom_π_assoc,
      enrichedHom_condition V (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₂)
      (Under.homMk f : Under.mk (𝟙 j) ⟶ Under.mk f)]
    congr 3
    simp [Under.map, Comma.mapLeft]
    rfl)

lemma fac (j : J) : lift s ≫ (conePresheafEnrichedHom V F₁ F₂).π.app j = s.π.app j := by
  dsimp [conePresheafEnrichedHom]
  ext k
  rw [assoc]
  erw [end_.lift_π, end_.lift_π, ← s.w k.hom]
  rw [assoc]
  erw [precompEnrichedHom_π]
  congr
  simp [Under.map, Comma.mapLeft]
  rfl

end isLimitConePresheafEnrichedHom

open isLimitConePresheafEnrichedHom in
noncomputable def isLimitConePresheafEnrichedHom :
    IsLimit (conePresheafEnrichedHom V F₁ F₂) where
  lift := lift
  fac := fac
  uniq s m hm := by
    dsimp
    ext j
    have := ((hm j).trans (fac s j).symm) =≫ enrichedHomπ V _ _ (Under.mk (𝟙 j))
    dsimp [conePresheafEnrichedHom] at this
    rw [assoc, assoc, precompEnrichedHom_π] at this
    exact this

end

end CategoryTheory.Enriched.FunctorCategory
