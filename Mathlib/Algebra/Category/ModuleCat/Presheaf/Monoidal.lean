import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

noncomputable section

open CategoryTheory MonoidalCategory

universe u v₁ u₁

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace PresheafOfModules

abbrev obj' (F : PresheafOfModules (R ⋙ forget₂ _ _)) (X : Cᵒᵖ) := (evaluation _ X).obj F

namespace Monoidal

#synth MonoidalCategory (ModuleCat ℤ)


def tensorObj' (F G : PresheafOfModules (R ⋙ forget₂ _ _)) :
    BundledCorePresheafOfModules (R ⋙ forget₂ _ _) where
  obj X := F.obj' X ⊗ G.obj' X
  map {X Y} f := by
    apply TensorProduct.lift (R := R.obj X)
    fapply LinearMap.mk₂
    · refine fun x y ↦ ?_
      let _ : CommSemiring ((R ⋙ forget₂ CommRingCat RingCat).obj Y) :=
        inferInstanceAs (CommSemiring (R.obj Y))
      exact (F.map f x) ⊗ₜ (G.map f y)
    all_goals sorry
  map_id := sorry
  map_comp := sorry

def tensorObj (F G : PresheafOfModules (R ⋙ forget₂ _ _)) : PresheafOfModules (R ⋙ forget₂ _ _) :=
  (tensorObj' F G).toPresheafOfModules

@[simp]
lemma tensorObj_map_tmul {F G : PresheafOfModules (R ⋙ forget₂ _ _)} {X Y : Cᵒᵖ}
    (x : F.obj' X) (y : G.obj' X) (f : X ⟶ Y) :
    letI : CommSemiring ((R ⋙ forget₂ CommRingCat RingCat).obj X) :=
        inferInstanceAs (CommSemiring (R.obj X))
    letI : CommSemiring ((R ⋙ forget₂ CommRingCat RingCat).obj Y) :=
        inferInstanceAs (CommSemiring (R.obj Y))
    (tensorObj F G).map f (x ⊗ₜ y) = (F.map f x) ⊗ₜ (G.map f y) := rfl

def tensorHom {F G H K : PresheafOfModules (R ⋙ forget₂ _ _)} (f : F ⟶ H) (g : G ⟶ K) :
    tensorObj F G ⟶ tensorObj H K := by
  refine Hom.mk''
    (fun X ↦ ((evaluation (R ⋙ forget₂ _ _) X).map f) ⊗ ((evaluation (R ⋙ forget₂ _ _) X).map g))
    ?_
  intro X Y h
  apply TensorProduct.ext (R := R.obj X)
  ext a b
  dsimp
  simp only [ModuleCat.restrictScalars, ModuleCat.RestrictScalars.map']
  sorry
  -- change ((Hom.app f Y ⊗ Hom.app g Y) (restrictionApp _ _)) = _
  -- erw [comp_apply]
  -- erw [restrictionApp_apply, restrictionApp_apply]


def whiskerLeft (F : PresheafOfModules (R ⋙ forget₂ _ _))
    {G H : PresheafOfModules (R ⋙ forget₂ _ _)} (g : G ⟶ H) : tensorObj F G ⟶ tensorObj F H := by
  fapply Hom.mk''
  · intro X
    let F' := (evaluation (R ⋙ forget₂ _ _) X).obj F
    exact F' ◁ ((evaluation (R ⋙ forget₂ _ _) X).map g)
  · sorry

def whiskerRight {F G : PresheafOfModules (R ⋙ forget₂ _ _)}
    (f : F ⟶ G) (H : PresheafOfModules (R ⋙ forget₂ _ _))  : tensorObj F H ⟶ tensorObj G H := by
  fapply Hom.mk''
  · intro X
    exact ((evaluation (R ⋙ forget₂ _ _) X).map f) ▷ (evaluation (R ⋙ forget₂ _ _) X).obj H
  · sorry

def associator (F G H : PresheafOfModules (R ⋙ forget₂ _ _)) :
    tensorObj (tensorObj F G) H ≅ tensorObj F (tensorObj G H) := by
  fapply isoMk''
  · intro X
    exact α_ (F.obj' X) (G.obj' X) (H.obj' X)
  · sorry

def leftUnitor (F : PresheafOfModules (R ⋙ forget₂ _ _)) : tensorObj (unit _) F ≅ F := by
  fapply isoMk''
  · intro X
    exact λ_ (F.obj' X)
  · sorry

def rightUnitor (F : PresheafOfModules (R ⋙ forget₂ _ _)) : tensorObj F (unit _) ≅ F := by
  fapply isoMk''
  · intro X
    exact ρ_ (F.obj' X)
  · sorry

instance monoidalCategoryStructPresheafOfModules :
    MonoidalCategoryStruct (PresheafOfModules (R ⋙ forget₂ _ _)) where
  tensorObj F G := tensorObj F G
  whiskerLeft F _ _ g := whiskerLeft F g
  whiskerRight f H := whiskerRight f H
  tensorHom f g := tensorHom f g
  tensorUnit := unit _
  associator F G H := associator F G H
  leftUnitor F := leftUnitor F
  rightUnitor F := rightUnitor F

@[simp]
lemma evaluation_map_tensorHom {F G H K : PresheafOfModules (R ⋙ forget₂ _ _)}
    (f : F ⟶ H) (g : G ⟶ K) (X : Cᵒᵖ) : ((evaluation _ X).map (f ⊗ g)) =
      ((evaluation _ X).map f) ⊗ ((evaluation _ X).map g) := rfl

@[simp]
lemma evaluation_map_whiskerLeft (F : PresheafOfModules (R ⋙ forget₂ _ _))
    {G H : PresheafOfModules (R ⋙ forget₂ _ _)} (g : G ⟶ H)
    (X : Cᵒᵖ) : ((evaluation _ X).map (F ◁ g)) =
      ((evaluation _ X).obj F) ◁ ((evaluation _ X).map g) := rfl

@[simp]
lemma evaluation_map_whiskerRight {F G : PresheafOfModules (R ⋙ forget₂ _ _)}
    (f : F ⟶ G) (H : PresheafOfModules (R ⋙ forget₂ _ _))
    (X : Cᵒᵖ) : ((evaluation _ X).map (f ▷ H)) =
      ((evaluation _ X).map f) ▷ ((evaluation _ X).obj H) := rfl

lemma evaluation_jointly_faithful {F G : PresheafOfModules (R ⋙ forget₂ _ _)} (f g : F ⟶ G)
    (h : ∀ (X : Cᵒᵖ), (evaluation _ X).map f = (evaluation _ X).map g) : f = g := by
  ext1 X
  exact h _

attribute [local ext] evaluation_jointly_faithful
attribute [-ext] Hom.ext
attribute [-simp] evaluation_map

@[simp]
lemma evaluation_map_associator_hom {F G H : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (X : Cᵒᵖ) :
    (evaluation (R ⋙ forget₂ _ _) X).map (α_ F G H).hom =
      (α_ (F.obj' X) (G.obj' X) (H.obj' X)).hom ≫ (by exact (𝟙 _)) := by
  rfl

lemma pentagon (F G H K : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)) :
    (α_ F G H).hom ▷ K ≫ (α_ F (G ⊗ H) K).hom ≫ F ◁ (α_ G H K).hom =
      (α_ (F ⊗ G) H K).hom ≫ (α_ F G (H ⊗ K)).hom := by
  ext1 X
  simp only [Functor.comp_obj, Functor.map_comp, evaluation_map_whiskerRight,
    evaluation_map_associator_hom, Category.comp_id, evaluation_map_whiskerLeft]
  apply MonoidalCategory.pentagon (F.obj' X) (G.obj' X) (H.obj' X) (K.obj' X)

set_option maxHeartbeats 400000 in
instance : MonoidalCategory (PresheafOfModules (R ⋙ forget₂ _ _)) where
  tensorHom_def _ _ := by ext1; simp [tensorHom_def]
  tensor_id _ _ := by
    ext1
    simp only [Functor.comp_obj, evaluation_obj, evaluation_map_tensorHom,
      CategoryTheory.Functor.map_id, tensorHom_id, id_whiskerRight]
    rfl
  tensor_comp f₁ f₂ g₁ g₂ := by ext1; simp
  whiskerLeft_id _ _ := by ext1; simp; rfl
  id_whiskerRight _ _ := by ext1; simp; rfl
  associator_naturality := sorry
  leftUnitor_naturality := sorry
  rightUnitor_naturality := sorry
  pentagon F G H K := pentagon F G H K
  triangle := sorry
