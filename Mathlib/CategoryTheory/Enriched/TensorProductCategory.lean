/-
Copyright (c) 2026 Daniel Carranza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Carranza
-/
module

public import Mathlib.CategoryTheory.Enriched.Basic

/-!

# The monoidal product of enriched categories

When a monoidal category `V` is braided, we may define the monoidal product of
`V`-categories `C` and `D`, which is a `V`-category structure on the product type `C × D`.
The "middle-four exchange" map (known as `tensorμ`) is required to define the composition morphism.

-/

@[expose] public section

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

namespace CategoryTheory

open MonoidalCategory

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V]
variable (C : Type u₂) [EnrichedCategory V C]
variable (D : Type u₃) [EnrichedCategory V D]

lemma comp_tensor_comp_eq_comp_mid_left_right {a b c d e : C} :
    ((eComp V a b c) ⊗ₘ (eComp V c d e)) ≫ eComp V a c e =
      (α_ _ _ _).hom ≫ _ ◁ (α_ _ _ _).inv ≫ _ ◁ ((eComp V b c d) ▷ _) ≫ _ ◁ (eComp V b d e) ≫
        eComp V a b e := by
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Category.assoc, e_assoc, MonoidalCategory.whiskerLeft_comp]
  rw [← associator_naturality_right_assoc, e_assoc', ← tensorHom_def'_assoc]

variable [BraidedCategory V]

/-- For a braided monoidal category `V`, the tensor product of `V`-categories `C` and `D` is
canonically a `V`-category whose underlying type of objects is `C × D`. -/
instance enrichedTensorProduct : EnrichedCategory V (C × D) where
  Hom := fun ⟨c, d⟩ ⟨c', d'⟩ => EnrichedCategory.Hom c c' ⊗ EnrichedCategory.Hom d d'
  id := fun ⟨c, d⟩ => (λ_ (𝟙_ V)).inv ≫ (EnrichedCategory.id c ⊗ₘ EnrichedCategory.id d)
  comp := fun ⟨c, d⟩ ⟨c', d'⟩ ⟨c'', d''⟩ => tensorμ _ _ _ _ ≫
    (EnrichedCategory.comp _ _ _ ⊗ₘ EnrichedCategory.comp _ _ _)
  id_comp := fun ⟨c, d⟩ ⟨c', d'⟩ => by
    simp only [comp_whiskerRight_assoc, tensorμ_natural_left_assoc]
    have := tensor_left_unitality (EnrichedCategory.Hom c c' : V) (EnrichedCategory.Hom d d')
    rw [← Category.assoc] at this
    have := (Iso.comp_inv_eq
      (tensorIso (λ_ (EnrichedCategory.Hom c c')) (λ_ (EnrichedCategory.Hom d d')))).mpr this
    slice_lhs 2 3 => rw [← this]
    simp only [tensorIso_inv, Category.assoc, Iso.inv_hom_id_assoc]
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, EnrichedCategory.id_comp,
      EnrichedCategory.id_comp, id_tensorHom_id]
  comp_id := fun ⟨c, d⟩ ⟨c', d'⟩ => by
    simp only [MonoidalCategory.whiskerLeft_comp_assoc, tensorμ_natural_right_assoc]
    have := tensor_right_unitality (EnrichedCategory.Hom c c' : V) (EnrichedCategory.Hom d d')
    rw [← Category.assoc] at this
    have := (Iso.comp_inv_eq
      (tensorIso (ρ_ (EnrichedCategory.Hom c c')) (ρ_ (EnrichedCategory.Hom d d')))).mpr this
    slice_lhs 2 3 => rw [← this]
    simp only [tensorIso_inv, Category.assoc, Iso.inv_hom_id_assoc]
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, EnrichedCategory.comp_id,
      EnrichedCategory.comp_id, id_tensorHom_id]
  assoc := fun ⟨c₁, d₁⟩ ⟨c₂, d₂⟩ ⟨c₃, d₃⟩ ⟨c₄, d₄⟩ => by
    simp only [comp_whiskerRight_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
      tensorμ_natural_left_assoc, tensorμ_natural_right_assoc]
    apply (Iso.inv_comp_eq _).mpr
    rw [← tensor_associativity_assoc]
    repeat rw [tensorHom_comp_tensorHom]
    apply whisker_eq; apply whisker_eq
    rw [(Iso.inv_comp_eq _).mp (@EnrichedCategory.assoc V _ _ C _ c₁ c₂ c₃ c₄),
      (Iso.inv_comp_eq _).mp (@EnrichedCategory.assoc V _ _ D _ d₁ d₂ d₃ d₄)]

@[reassoc]
lemma tensor_eComp_eq (c c' c'' : C) (d d' d'' : D) :
    eComp V (C := C × D) ⟨c, d⟩ ⟨c', d'⟩ ⟨c'', d''⟩ = tensorμ _ _ _ _ ≫
    ((eComp V _ _ _) ⊗ₘ (eComp V _ _ _)) :=
  rfl

@[reassoc]
lemma tensor_eId_eq (c : C) (d : D) : eId V (C := C × D) ⟨c, d⟩ =
    (λ_ _).inv ≫ ((eId V c) ⊗ₘ (eId V d)) :=
  rfl

section Bifunctor

variable (E : Type u₄) [EnrichedCategory V E]

/-- An auxiliary type for constructing a `V`-functor out of the tensor product `C × D` by specifying
an assignment on objects `C → D → E` which is `V`-functorial in each variable separately, and whose
action on morphisms satisfies an additional "naturality" condition. -/
@[ext]
structure EnrichedBifunctor where
  obj : C → D → E
  map_left : (c c' : C) → (d : D) → (c ⟶[V] c') ⟶ EnrichedCategory.Hom (obj c d) (obj c' d)
  map_right : (c : C) → (d d' : D) → (d ⟶[V] d') ⟶ EnrichedCategory.Hom (obj c d) (obj c d')
  id_left : (c : C) → (d : D) → eId V c ≫ map_left c c d = eId V _
  id_right : (c : C) → (d : D) → eId V d ≫ map_right c d d = eId V _
  comp_left : (c c' c'' : C) → (d : D) → eComp V c c' c'' ≫ map_left c c'' d =
    ((map_left c c' d) ⊗ₘ (map_left c' c'' d)) ≫ eComp V _ _ _
  comp_right : (c : C) → (d d' d'' : D) → eComp V d d' d'' ≫ map_right c d d'' =
    ((map_right c d d') ⊗ₘ (map_right c d' d'')) ≫ eComp V _ _ _
  left_right_naturality : (c c' : C) → (d d' : D) → ((map_left c c' d) ⊗ₘ (map_right c' d d')) ≫
    eComp V _ _ _ = ((map_left c c' d') ⊗ₘ (map_right c d d')) ≫ (β_ _ _).inv ≫ eComp V _ _ _

/-- Construct a `V`-functor from `C × D` to `E` using the auxuliary data in `EnrichedBifunctor`. -/
def enrichedBifunctorEquiv.to (F : EnrichedBifunctor V C D E) : EnrichedFunctor V (C × D) E where
  obj p := F.obj p.1 p.2
  map p q := ((F.map_left p.1 q.1 p.2) ⊗ₘ (F.map_right q.1 p.2 q.2)) ≫ eComp V _ _ _
  map_id p := by
    rw [tensor_eId_eq, Category.assoc, tensorHom_comp_tensorHom_assoc, F.id_left, F.id_right,
      tensorHom_def', Category.assoc, ← leftUnitor_inv_naturality_assoc, e_id_comp,
      Category.comp_id]
  map_comp p q r := by
    have F_left_id : F.map_left p.1 q.1 p.2 ≫ 𝟙 _ = 𝟙 _ ≫ F.map_left p.1 q.1 p.2 := by aesop_cat
    have F_right_id : F.map_right r.1 q.2 r.2 ≫ 𝟙 _ = 𝟙 _ ≫ F.map_right r.1 q.2 r.2 := by aesop_cat
    rw [tensor_eComp_eq V, Category.assoc, tensorHom_comp_tensorHom_assoc, F.comp_left,
      F.comp_right]
    simp only [← tensorHom_comp_tensorHom_assoc]
    rw [comp_tensor_comp_eq_comp_mid_left_right, associator_naturality_assoc, ← id_tensorHom,
      tensorHom_comp_tensorHom_assoc, associator_inv_naturality, F_left_id,
      ← tensorHom_comp_tensorHom_assoc, ← tensorHom_id, ← id_tensorHom]
    nth_rw 2 [tensorHom_comp_tensorHom_assoc]
    rw [tensorHom_comp_tensorHom]
    simp only [F.left_right_naturality]
    rw [BraidedCategory.braiding_inv_naturality_assoc, F_right_id, ← tensorHom_comp_tensorHom,
      F_left_id, ← tensorHom_comp_tensorHom]
    simp only [id_tensorHom, tensorHom_id]
    unfold tensorμ
    simp only [Category.assoc, Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc]
    nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← MonoidalCategory.comp_whiskerRight, Iso.hom_inv_id]
    simp only [id_whiskerRight, MonoidalCategory.whiskerLeft_id, Category.id_comp]
    rw [tensorHom_def, tensorHom_def']
    simp only [comp_whiskerRight]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    nth_rw 3 [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← e_assoc', MonoidalCategory.whiskerLeft_comp_assoc,
      MonoidalCategory.whiskerLeft_comp_assoc]
    nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc,
      ← tensorHom_id]
    rw [associator_naturality, MonoidalCategory.whiskerLeft_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, associator_naturality_right,
      MonoidalCategory.whiskerLeft_comp_assoc, ← whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc]
    simp only [Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
    rw [← e_assoc, associator_inv_naturality_right_assoc]
    nth_rw 4 [← id_tensorHom]
    rw [associator_inv_naturality_assoc, associator_inv_naturality_right_assoc,
      associator_inv_naturality_left_assoc, Iso.hom_inv_id_assoc, ← tensorHom_id, ← tensorHom_id,
      ← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
      tensorHom_comp_tensorHom_assoc]
    simp only [Category.comp_id, Category.id_comp, id_tensorHom, tensorHom_id]
    rw [← tensorHom_def, ← tensorHom_def', ← tensorHom_def'_assoc]

/-- Given a `V`-functor from `C × D` to `E`, this constructs the data contained in
`EnrichedBifunctor` (i.e. `V`-functoriality in each variable separately, as well as the
compatibility between the two actions on morphisms). -/
def enrichedBifunctorEquiv.from (F : EnrichedFunctor V (C × D) E) : EnrichedBifunctor V C D E where
  obj c d := F.obj ⟨c, d⟩
  map_left c c' d := (ρ_ _).inv ≫ (_ ◁ eId V d) ≫ F.map ⟨c, d⟩ ⟨c', d⟩
  map_right c d d' := (λ_ _).inv ≫ (eId V c ▷ _) ≫ F.map ⟨c, d⟩ ⟨c, d'⟩
  id_left c d := by
    have : ((λ_ (𝟙_ V)).inv ≫ (eId V c ⊗ₘ eId V d)) = eId V (C := C × D) ⟨c, d⟩ := rfl
    rw [rightUnitor_inv_naturality_assoc, ← tensorHom_def_assoc, ← unitors_inv_equal,
      ← Category.assoc, this, F.map_id ⟨c, d⟩]
  id_right c d := by
    have : ((λ_ (𝟙_ V)).inv ≫ (eId V c ⊗ₘ eId V d)) = eId V (C := C × D) ⟨c, d⟩ := rfl
    rw [leftUnitor_inv_naturality_assoc, ← tensorHom_def'_assoc, ← Category.assoc, this,
      F.map_id ⟨c, d⟩]
  comp_left c c' c'' d := by
    repeat rw [← tensorHom_comp_tensorHom_assoc]
    rw [← F.map_comp]
    simp only [tensor_eComp_eq, Category.assoc]
    nth_rw 2 [← id_tensorHom, ← id_tensorHom]
    rw [tensorμ_natural_assoc, tensorHom_comp_tensorHom_assoc, tensorHom_id,
      tensorHom_def (eId V d), id_whiskerRight, MonoidalCategory.whiskerRight_id, Category.id_comp]
    simp only [Category.assoc]
    rw [e_comp_id, Category.comp_id, ← Category.comp_id (eComp V c c' c''),
      ← tensorHom_comp_tensorHom_assoc]
    simp only [Category.comp_id, id_tensorHom]
    rw [tensorHom_def'_assoc (eComp V c c' c''), rightUnitor_inv_naturality_assoc, tensorμ,
      tensorHom_def_assoc]
    simp
  comp_right c d d' d'' := by
    repeat rw [← tensorHom_comp_tensorHom_assoc]
    rw [← F.map_comp]
    simp only [tensor_eComp_eq, Category.assoc]
    nth_rw 2 [← tensorHom_id, ← tensorHom_id]
    rw [tensorμ_natural_assoc, tensorHom_comp_tensorHom_assoc, tensorHom_id,
      tensorHom_def (eId V c), id_whiskerRight, MonoidalCategory.whiskerRight_id, Category.id_comp]
    simp only [Category.assoc]
    rw [e_comp_id, Category.comp_id, ← Category.comp_id (eComp V d d' d''),
      ← tensorHom_comp_tensorHom_assoc, Category.comp_id, tensorHom_def'_assoc (ρ_ _).hom, tensorμ,
      tensorHom_def_assoc]
    simp
  left_right_naturality c c' d d' := by
    repeat rw [← tensorHom_comp_tensorHom_assoc]
    rw [BraidedCategory.braiding_inv_naturality_assoc]
    repeat rw [← F.map_comp, tensor_eComp_eq_assoc]
    rw [BraidedCategory.braiding_inv_naturality_assoc]
    repeat rw [← tensorHom_id, ← id_tensorHom, tensorμ_natural_assoc,
      tensorHom_comp_tensorHom_assoc]
    simp only [tensorHom_id, id_tensorHom, (Iso.inv_comp_eq_id (λ_ _)).mp (e_id_comp ..),
      (Iso.inv_comp_eq_id (ρ_ _)).mp (e_comp_id ..), braiding_inv_tensorμ_assoc,
      braiding_inv_tensorUnit_left, braiding_inv_tensorUnit_right, tensorHom_comp_tensorHom_assoc,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, tensorμ_unit_unit_tensorδ]

/-- The equivalence between `V`-functors out of the enriched tensor product `C × D` and the type of
enriched bifunctors `EnrichedBifunctor V C D`. -/
def enrichedBifunctorEquiv : (EnrichedBifunctor V C D E) ≃ (EnrichedFunctor V (C × D) E) where
  toFun := enrichedBifunctorEquiv.to V C D E
  invFun := enrichedBifunctorEquiv.from V C D E
  left_inv := fun F => by
    refine EnrichedBifunctor.ext rfl ?_ ?_
    · refine heq_of_eq (funext₃ (fun c c' d => ?_))
      have h : (enrichedBifunctorEquiv.from V C D E
          (enrichedBifunctorEquiv.to V C D E F)).map_left c c' d =
          (ρ_ _).inv ≫ (_ ◁ eId V d) ≫ (enrichedBifunctorEquiv.to V C D E F).map ⟨c, d⟩ ⟨c', d⟩ :=
        rfl
      have h' : (enrichedBifunctorEquiv.to V C D E F).map ⟨c, d⟩ ⟨c', d⟩
        = ((F.map_left c c' d) ⊗ₘ (F.map_right c' d d)) ≫ eComp V _ _ _ := rfl
      rw [h, h', ← id_tensorHom, tensorHom_comp_tensorHom_assoc, F.id_right, Category.id_comp,
        tensorHom_def_assoc, ← rightUnitor_inv_naturality_assoc, e_comp_id, Category.comp_id]
    refine heq_of_eq (funext₃ (fun c d d' => ?_))
    have h : (enrichedBifunctorEquiv.from V C D E
      (enrichedBifunctorEquiv.to V C D E F)).map_right c d d' =
      (λ_ _).inv ≫ (eId V c ▷ _) ≫ (enrichedBifunctorEquiv.to V C D E F).map ⟨c, d⟩ ⟨c, d'⟩ := rfl
    have h' : (enrichedBifunctorEquiv.to V C D E F).map ⟨c, d⟩ ⟨c, d'⟩ =
      ((F.map_left c c d) ⊗ₘ (F.map_right c d d')) ≫ eComp V _ _ _ := rfl
    rw [h, h', ← tensorHom_id, tensorHom_comp_tensorHom_assoc, F.id_left, Category.id_comp,
      tensorHom_def'_assoc, ← leftUnitor_inv_naturality_assoc, e_id_comp, Category.comp_id]
  right_inv := fun F => by
    fapply EnrichedFunctor.ext
    · intro p
      exact rfl
    intro p q
    let F' := enrichedBifunctorEquiv.from V C D E F
    have h₁ : (enrichedBifunctorEquiv.to V C D E F').map p q =
      ((F'.map_left p.1 q.1 p.2) ⊗ₘ (F'.map_right q.1 p.2 q.2)) ≫ eComp V _ _ _ := rfl
    have h₂ : F'.map_left p.1 q.1 p.2 =
      (ρ_ _).inv ≫ (_ ◁ eId V p.2) ≫ F.map ⟨p.1, p.2⟩ ⟨q.1, p.2⟩ := rfl
    have h₃ : F'.map_right q.1 p.2 q.2 =
      (λ_ _).inv ≫ (eId V q.1 ▷ _) ≫ F.map ⟨q.1, p.2⟩ ⟨q.1, q.2⟩ := rfl
    have h₄ : eComp V (F'.obj p.1 p.2) (F'.obj q.1 p.2) (F'.obj q.1 q.2) =
      eComp V (F.obj ⟨p.1, p.2⟩) (F.obj ⟨q.1, p.2⟩) (F.obj ⟨q.1, q.2⟩) := rfl
    have h₅ : EnrichedCategory.Hom p.1 q.1 ◁ eId V q.1 ≫ eComp V p.1 q.1 q.1 = (ρ_ _).hom
      := (Iso.inv_comp_eq_id _).mp (e_comp_id V _ _)
    have h₆ : eId V p.2 ▷ EnrichedCategory.Hom p.2 q.2 ≫ eComp V p.2 p.2 q.2 = (λ_ _).hom
      := (Iso.inv_comp_eq_id _).mp (e_id_comp V _ _)
    rw [h₁, h₂, h₃, h₄]
    simp only [← tensorHom_comp_tensorHom, Category.assoc]
    rw [eqToHom_refl, Category.comp_id, ← F.map_comp, tensor_eComp_eq, Category.assoc,
      ← tensorHom_id, ← id_tensorHom, tensorμ_natural_assoc, tensorHom_id, id_tensorHom,
      tensorHom_comp_tensorHom_assoc, h₅,h₆]
    unfold tensorμ
    simp only [Category.assoc]
    rw [braiding_unit_unit_eq_id]
    simp

end Bifunctor

end CategoryTheory
