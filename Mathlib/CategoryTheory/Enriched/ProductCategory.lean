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

-- Helper lemma for Bifunc.mk
lemma comp_tensor_comp_eq_comp_mid_left_right {a b c d e : C} :
    ((eComp V a b c) ⊗ₘ (eComp V c d e)) ≫ eComp V a c e =
      (α_ _ _ _).hom ≫ _ ◁ (α_ _ _ _).inv ≫ _ ◁ ((eComp V b c d) ▷ _) ≫ _ ◁ (eComp V b d e) ≫
        eComp V a b e := by
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Category.assoc, e_assoc, MonoidalCategory.whiskerLeft_comp]
  rw [← associator_naturality_right_assoc, e_assoc', ← tensorHom_def'_assoc]

variable [BraidedCategory V]

instance : EnrichedCategory V (C × D) where
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
      EnrichedCategory.id_comp]
    exact id_tensorHom_id (EnrichedCategory.Hom c c') (EnrichedCategory.Hom d d')
  comp_id := fun ⟨c, d⟩ ⟨c', d'⟩ => by
    simp only [MonoidalCategory.whiskerLeft_comp_assoc, tensorμ_natural_right_assoc]
    have := tensor_right_unitality (EnrichedCategory.Hom c c' : V) (EnrichedCategory.Hom d d')
    rw [← Category.assoc] at this
    have := (Iso.comp_inv_eq
      (tensorIso (ρ_ (EnrichedCategory.Hom c c')) (ρ_ (EnrichedCategory.Hom d d')))).mpr this
    slice_lhs 2 3 => rw [← this]
    simp only [tensorIso_inv, Category.assoc, Iso.inv_hom_id_assoc]
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, EnrichedCategory.comp_id,
      EnrichedCategory.comp_id]
    exact id_tensorHom_id (EnrichedCategory.Hom c c') (EnrichedCategory.Hom d d')
  assoc := fun ⟨c₁, d₁⟩ ⟨c₂, d₂⟩ ⟨c₃, d₃⟩ ⟨c₄, d₄⟩ => by
    simp only [comp_whiskerRight_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
      tensorμ_natural_left_assoc, tensorμ_natural_right_assoc]
    apply (Iso.inv_comp_eq _).mpr
    rw [← tensor_associativity_assoc]
    repeat rw [tensorHom_comp_tensorHom]
    apply whisker_eq; apply whisker_eq
    rw [(Iso.inv_comp_eq _).mp (@EnrichedCategory.assoc V _ _ C _ c₁ c₂ c₃ c₄),
      (Iso.inv_comp_eq _).mp (@EnrichedCategory.assoc V _ _ D _ d₁ d₂ d₃ d₄)]

def tensor_eComp_eq (c c' c'' : C) (d d' d'' : D) :
    eComp V (C := C × D) ⟨c, d⟩ ⟨c', d'⟩ ⟨c'', d''⟩ = tensorμ _ _ _ _ ≫
    (tensorHom (eComp V _ _ _) (eComp V _ _ _)) :=
  rfl

-- Look up if there is an analogous lemma for the unenriched setting
def enrichedBifunctor.mk {E : Type u₄} [EnrichedCategory V E]
    (F_obj : C → D → E)
    -- make c c' d implicit?
    (F_map_left : (c c' : C) → (d : D) →
      (c ⟶[V] c') ⟶ EnrichedCategory.Hom (F_obj c d) (F_obj c' d))
     -- make c d d' implicit?
    (F_map_right : (c : C) → (d d' : D) →
      (d ⟶[V] d') ⟶ EnrichedCategory.Hom (F_obj c d) (F_obj c d'))
    (F_id_left : (c : C) → (d : D) →
      eId V c ≫ F_map_left c c d = eId V _)
    (F_id_right : (c : C) → (d : D) →
      eId V d ≫ F_map_right c d d = eId V _)
    (F_comp_left : (c c' c'' : C) → (d : D) →
      eComp V c c' c'' ≫ F_map_left c c'' d =
      ((F_map_left c c' d) ⊗ₘ (F_map_left c' c'' d)) ≫ eComp V _ _ _)
    (F_comp_right : (c : C) → (d d' d'' : D) →
      eComp V d d' d'' ≫ F_map_right c d d'' =
      ((F_map_right c d d') ⊗ₘ (F_map_right c d' d'')) ≫ eComp V _ _ _)
    (F_left_right_naturality : (c c' : C) → (d d' : D) →
      ((F_map_left c c' d) ⊗ₘ (F_map_right c' d d')) ≫ eComp V _ _ _ =
      ((F_map_left c c' d') ⊗ₘ (F_map_right c d d')) ≫ (β_ _ _).inv ≫ eComp V _ _ _)
    : EnrichedFunctor V (C × D) E where
  obj p := F_obj p.1 p.2
  map p q := ((F_map_left p.1 q.1 p.2) ⊗ₘ (F_map_right q.1 p.2 q.2)) ≫ eComp V _ _ _
  map_id p := by
    have : eId V p = (λ_ _).inv ≫ ((eId V p.1) ⊗ₘ (eId V p.2)) := rfl
    simp only [this, Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    simp only [F_id_left, F_id_right, tensorHom_def', Category.assoc]
    rw [← leftUnitor_inv_naturality_assoc, e_id_comp]
    exact Category.comp_id _
  map_comp p q r := by
    have : eComp V p q r = tensorμ _ _ _ _ ≫ ((eComp V p.1 q.1 r.1) ⊗ₘ (eComp V p.2 q.2 r.2)) := rfl
    simp only [this, Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc, F_comp_left, F_comp_right]
    simp only [← tensorHom_comp_tensorHom_assoc]
    rw [comp_tensor_comp_eq_comp_mid_left_right]
    simp only [associator_naturality_assoc]
    rw [← id_tensorHom]
    rw [tensorHom_comp_tensorHom_assoc]
    rw [associator_inv_naturality]
    have F_left_id : F_map_left p.1 q.1 p.2 ≫ 𝟙 _ = 𝟙 _ ≫ F_map_left p.1 q.1 p.2 := by aesop_cat
    rw [F_left_id, ← tensorHom_comp_tensorHom_assoc]
    rw [← tensorHom_id, ← id_tensorHom]
    nth_rw 2 [tensorHom_comp_tensorHom_assoc]
    rw [tensorHom_comp_tensorHom]
    simp only [F_left_right_naturality]
    rw [BraidedCategory.braiding_inv_naturality_assoc]
    have F_right_id : F_map_right r.1 q.2 r.2 ≫ 𝟙 _ = 𝟙 _ ≫ F_map_right r.1 q.2 r.2 := by aesop_cat
    rw [F_right_id]
    rw [← tensorHom_comp_tensorHom]
    rw [F_left_id]
    rw [← tensorHom_comp_tensorHom]
    -- --
    simp only [id_tensorHom, tensorHom_id]
    unfold tensorμ
    simp only [Category.assoc]
    simp only [Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc]
    nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← MonoidalCategory.comp_whiskerRight]
    --
    rw [Iso.hom_inv_id]
    simp only [id_whiskerRight, MonoidalCategory.whiskerLeft_id, Category.id_comp]
    --
    rw [tensorHom_def]
    rw [tensorHom_def']
    simp only [comp_whiskerRight]
    -- simp only [Category.assoc]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    nth_rw 3 [← MonoidalCategory.whiskerLeft_comp_assoc]
    --
    rw [← e_assoc']
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    nth_rw 2 [← MonoidalCategory.whiskerLeft_comp_assoc]
    nth_rw 2 [← tensorHom_id]
    rw [associator_naturality]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [associator_naturality_right]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← whisker_exchange_assoc]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    simp only [Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
    --
    rw [← e_assoc]
    rw [associator_inv_naturality_right_assoc]
    nth_rw 4 [← id_tensorHom]
    rw [associator_inv_naturality_assoc]
    rw [associator_inv_naturality_right_assoc]
    rw [associator_inv_naturality_left_assoc]
    simp only [Iso.hom_inv_id_assoc]
    --
    rw [← tensorHom_id, ← tensorHom_id, ← id_tensorHom, ← id_tensorHom]
    rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
    simp only [Category.comp_id, Category.id_comp, id_tensorHom, tensorHom_id]
    rw [← tensorHom_def, ← tensorHom_def', ← tensorHom_def'_assoc]

variable (E : Type u₄) [EnrichedCategory V E]

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

def enrichedBifunctorEquiv.to (F : EnrichedBifunctor V C D E) : EnrichedFunctor V (C × D) E :=
  enrichedBifunctor.mk V C D F.obj F.map_left F.map_right F.id_left F.id_right F.comp_left
    F.comp_right F.left_right_naturality

@[reassoc]
lemma braiding_tensorμ (a b c d : V) : (β_ (c ⊗ d) (a ⊗ b)).inv ≫ tensorμ c d a b =
    tensorδ a c b d ≫ (tensorHom (β_ c a).inv (β_ d b).inv) := by
  -- have : ∀(v : V), (β_ v (𝟙_ V)).hom = (β_ (𝟙_ V) v).inv := by exact?
  unfold tensorμ tensorδ
  rw [tensorHom_def]
  simp only [BraidedCategory.braiding_tensor_right_inv, BraidedCategory.braiding_tensor_left_inv,
    MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, whisker_assoc, Category.assoc,
    pentagon_inv_inv_hom_hom_inv, pentagon_inv_assoc, Iso.inv_hom_id_assoc,
    whiskerLeft_hom_inv_assoc, whiskerRight_tensor, tensor_whiskerLeft,
    pentagon_hom_inv_inv_inv_inv_assoc, Iso.cancel_iso_hom_left]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc c (_ ▷ _)]
  simp only [inv_hom_whiskerRight, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  refine a ◁ (α_ b c d).inv ≫= ?_
  refine a ◁ (β_ c b).inv ▷ d ≫= ?_
  rw [← associator_naturality_right_assoc]
  rw [associator_naturality_left_assoc]
  rw [associator_inv_naturality_right_assoc]
  rw [← associator_inv_naturality_left_assoc]
  rw [whisker_exchange_assoc]
  simp only [whiskerRight_tensor, tensor_whiskerLeft, pentagon_hom_hom_inv_inv_hom,
    hom_inv_whiskerRight_assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    pentagon_hom_inv_inv_inv_inv_assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc]

lemma braiding_unit_unit_inv_eq : (β_ (𝟙_ V) (𝟙_ V)).hom = (β_ (𝟙_ V) (𝟙_ V)).inv := by
  simp only [braiding_tensorUnit_right, braiding_inv_tensorUnit_right]
  rw [MonoidalCategory.unitors_equal, MonoidalCategory.unitors_inv_equal]

lemma tensorμ_unit_unit (a d : V) : tensorμ a (𝟙_ V) (𝟙_ V) d = tensorδ a (𝟙_ V) (𝟙_ V) d := by
  unfold tensorμ tensorδ
  rw [braiding_unit_unit_inv_eq]

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
    -- simp only [← tensorHom_comp_tensorHom_assoc]
    rw [← F.map_comp]
    simp only [tensor_eComp_eq, Category.assoc]
    nth_rw 2 [← id_tensorHom, ← id_tensorHom]
    rw [tensorμ_natural_assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    rw [tensorHom_id, tensorHom_def (eId V d)]
    rw [id_whiskerRight, MonoidalCategory.whiskerRight_id, Category.id_comp]
    simp only [Category.assoc]
    rw [e_comp_id, Category.comp_id]
    rw [← Category.comp_id (eComp V c c' c'')]
    rw [← tensorHom_comp_tensorHom_assoc]
    simp only [Category.comp_id, id_tensorHom]
    rw [tensorHom_def'_assoc (eComp V c c' c'')]
    --
    rw [tensorμ]
    rw [rightUnitor_inv_naturality_assoc]
    repeat rw [← Category.assoc]
    repeat apply eq_whisker
    rw [tensorHom_def_assoc]
    aesop_cat
  comp_right c d d' d'' := by
    repeat rw [← tensorHom_comp_tensorHom_assoc]
    rw [← F.map_comp]
    simp only [tensor_eComp_eq, Category.assoc]
    nth_rw 2 [← tensorHom_id, ← tensorHom_id]
    rw [tensorμ_natural_assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    rw [tensorHom_id, tensorHom_def (eId V c)]
    rw [id_whiskerRight, MonoidalCategory.whiskerRight_id, Category.id_comp]
    simp only [Category.assoc]
    rw [e_comp_id, Category.comp_id]
    rw [← Category.comp_id (eComp V d d' d'')]
    rw [← tensorHom_comp_tensorHom_assoc]
    simp only [Category.comp_id]
    rw [tensorHom_def'_assoc (ρ_ _).hom]
    --
    rw [tensorμ]
    rw [leftUnitor_inv_naturality_assoc]
    repeat rw [← Category.assoc]
    repeat apply eq_whisker
    rw [tensorHom_def_assoc]
    aesop_cat
  left_right_naturality c c' d d' := by
    repeat rw [← tensorHom_comp_tensorHom_assoc]
    apply whisker_eq
    rw [BraidedCategory.braiding_inv_naturality_assoc]
    simp only [← F.map_comp]
    repeat rw [← Category.assoc]
    apply eq_whisker
    simp only [Category.assoc]
    simp only [tensor_eComp_eq]
    rw [BraidedCategory.braiding_inv_naturality_assoc]
    simp only [← tensorHom_id, ← id_tensorHom]
    simp only [tensorμ_natural_assoc]
    --
    simp only [tensorHom_comp_tensorHom]
    simp only [tensorHom_id, id_tensorHom]
    simp only [(Iso.inv_comp_eq_id (λ_ _)).mp (e_id_comp ..)]
    simp only [(Iso.inv_comp_eq_id (ρ_ _)).mp (e_comp_id ..)]
    --
    rw [braiding_tensorμ_assoc]
    simp only [braiding_inv_tensorUnit_left, braiding_inv_tensorUnit_right,
      tensorHom_comp_tensorHom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [tensorμ_unit_unit]

-- lemma enrichedFunctorEq (F G : EnrichedFunctor V C D) (obj_eq : F.obj = G.obj)
--     (map_eq : HEq F.map G.map) : F = G := by
--   induction F with
--     | mk F_obj F_map F_map_id F_map_comp =>
--     induction G with
--     | mk G_obj G_map G_map_id G_map_comp =>
--       simp only [EnrichedFunctor.mk.injEq]
--       exact And.intro obj_eq map_eq

def enrichedBifunctorEquiv : (EnrichedBifunctor V C D E) ≃ (EnrichedFunctor V (C × D) E) where
  toFun := enrichedBifunctorEquiv.to V C D E
  invFun := enrichedBifunctorEquiv.from V C D E
  left_inv := fun F => by
    refine EnrichedBifunctor.ext rfl ?_ ?_
    case refine_1 =>
      refine heq_of_eq (funext₃ (fun c c' d => ?_))
      have : (enrichedBifunctorEquiv.from V C D E
          (enrichedBifunctorEquiv.to V C D E F)).map_left c c' d =
          (ρ_ _).inv ≫ (_ ◁ eId V d) ≫ (enrichedBifunctorEquiv.to V C D E F).map ⟨c, d⟩ ⟨c', d⟩ :=
        rfl
      rw [this]
      have : (enrichedBifunctorEquiv.to V C D E F).map ⟨c, d⟩ ⟨c', d⟩
        = ((F.map_left c c' d) ⊗ₘ (F.map_right c' d d)) ≫ eComp V _ _ _ := rfl
      rw [this]
      rw [← id_tensorHom]
      rw [tensorHom_comp_tensorHom_assoc]
      rw [F.id_right]
      rw [Category.id_comp]
      rw [tensorHom_def_assoc]
      rw [← rightUnitor_inv_naturality_assoc]
      rw [e_comp_id]
      exact Category.comp_id _
    refine heq_of_eq (funext₃ (fun c d d' => ?_))
    have : (enrichedBifunctorEquiv.from V C D E
      (enrichedBifunctorEquiv.to V C D E F)).map_right c d d' =
      (λ_ _).inv ≫ (eId V c ▷ _) ≫ (enrichedBifunctorEquiv.to V C D E F).map ⟨c, d⟩ ⟨c, d'⟩ := rfl
    rw [this]
    have : (enrichedBifunctorEquiv.to V C D E F).map ⟨c, d⟩ ⟨c, d'⟩ =
      ((F.map_left c c d) ⊗ₘ (F.map_right c d d')) ≫ eComp V _ _ _ := rfl
    rw [this]
    rw [← tensorHom_id]
    rw [tensorHom_comp_tensorHom_assoc]
    rw [F.id_left]
    rw [Category.id_comp]
    rw [tensorHom_def'_assoc]
    rw [← leftUnitor_inv_naturality_assoc]
    rw [e_id_comp]
    exact Category.comp_id _
  right_inv := fun F => by
    fapply EnrichedFunctor.ext
    · intro p
      exact rfl
    intro p q
    rw [eqToHom_refl, Category.comp_id]
    -- refine heq_of_eq (funext₂ (fun p q => ?_))
    let F' := enrichedBifunctorEquiv.from V C D E F
    have : (enrichedBifunctorEquiv.to V C D E F').map p q =
      ((F'.map_left p.1 q.1 p.2) ⊗ₘ (F'.map_right q.1 p.2 q.2)) ≫ eComp V _ _ _ := rfl
    rw [this]
    have : F'.map_left p.1 q.1 p.2 =
      (ρ_ _).inv ≫ (_ ◁ eId V p.2) ≫ F.map ⟨p.1, p.2⟩ ⟨q.1, p.2⟩ := rfl
    rw [this]
    have : F'.map_right q.1 p.2 q.2 =
      (λ_ _).inv ≫ (eId V q.1 ▷ _) ≫ F.map ⟨q.1, p.2⟩ ⟨q.1, q.2⟩ := rfl
    rw [this]
    have : eComp V (F'.obj p.1 p.2) (F'.obj q.1 p.2) (F'.obj q.1 q.2) =
      eComp V (F.obj ⟨p.1, p.2⟩) (F.obj ⟨q.1, p.2⟩) (F.obj ⟨q.1, q.2⟩) := rfl
    rw [this]
    simp only [← tensorHom_comp_tensorHom, Category.assoc]
    rw [← F.map_comp]
    rw [tensor_eComp_eq, Category.assoc]
    rw [← tensorHom_id, ← id_tensorHom]
    rw [tensorμ_natural_assoc]
    rw [tensorHom_id, id_tensorHom, tensorHom_comp_tensorHom_assoc]
    have : EnrichedCategory.Hom p.1 q.1 ◁ eId V q.1 ≫ eComp V p.1 q.1 q.1 = (ρ_ _).hom
      := (Iso.inv_comp_eq_id _).mp (e_comp_id V _ _)
    rw [this]
    have : eId V p.2 ▷ EnrichedCategory.Hom p.2 q.2 ≫ eComp V p.2 p.2 q.2 = (λ_ _).hom
      := (Iso.inv_comp_eq_id _).mp (e_id_comp V _ _)
    rw [this]
    -- Candidate for its own lemma
    unfold tensorμ
    simp only [Category.assoc]
    have : (β_ (𝟙_ V) (𝟙_ V)).hom = 𝟙 _ := by
      simp only [braiding_tensorUnit_right]
      rw [← unitors_equal]
      exact (λ_ _).hom_inv_id
    rw [this]
    simp only [id_whiskerRight, MonoidalCategory.whiskerLeft_id, Category.id_comp,
      whiskerLeft_inv_hom_assoc, Iso.hom_inv_id_assoc, tensor_inv_hom_id_assoc, tensorHom_id,
      inv_hom_whiskerRight_assoc]

end CategoryTheory
