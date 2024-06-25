import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

noncomputable section

open CategoryTheory MonoidalCategory Category

universe v u v₁ u₁

namespace ModuleCat

variable {R : Type u} [CommRing R] {M N P : ModuleCat.{u} R}

section

variable (f : M → N → P) (h₁ : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  (h₂ : ∀ (a : R) m n, f (a • m) n = a • f m n)
  (h₃ : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
  (h₄ : ∀ (a : R) m n, f m (a • n) = a • f m n)

def tensorLift : M ⊗ N ⟶ P := TensorProduct.lift (LinearMap.mk₂ R f h₁ h₂ h₃ h₄)

@[simp]
lemma tensorLift_apply (m : M) (n : N) :
  tensorLift f h₁ h₂ h₃ h₄ (m ⊗ₜ n) = f m n := rfl

end

end ModuleCat

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  -- the next variable is more the missing API
  {S : Cᵒᵖ ⥤ RingCat.{u}}

instance (X : Cᵒᵖ) : CommRing ((R ⋙ forget₂ _ RingCat).obj X) :=
  inferInstanceAs (CommRing (R.obj X))

namespace PresheafOfModules

abbrev obj' (F : PresheafOfModules.{v} S) (X : Cᵒᵖ) := (evaluation _ X).obj F

abbrev Hom.app' {F G : PresheafOfModules.{v} S} (f : F ⟶ G) (X : Cᵒᵖ) :
    F.obj' X ⟶ G.obj' X := (evaluation _ X).map f

namespace Monoidal

variable (F G H K : PresheafOfModules (R ⋙ forget₂ _ _))

def tensorObj' :
    BundledCorePresheafOfModules (R ⋙ forget₂ _ _) where
  obj X := F.obj' X ⊗ G.obj' X
  map {X Y} f := ModuleCat.tensorLift (fun x y ↦ (F.map f x) ⊗ₜ (G.map f y))
    sorry sorry sorry sorry
  map_id := sorry
  map_comp := sorry

def tensorObj : PresheafOfModules (R ⋙ forget₂ _ _) :=
  (tensorObj' F G).toPresheafOfModules

variable {F G H K}

@[simp]
lemma tensorObj_map_tmul {X Y : Cᵒᵖ}
    (x : F.obj' X) (y : G.obj' X) (f : X ⟶ Y) :
    letI : CommSemiring ((R ⋙ forget₂ CommRingCat RingCat).obj X) :=
        inferInstanceAs (CommSemiring (R.obj X))
    letI : CommSemiring ((R ⋙ forget₂ CommRingCat RingCat).obj Y) :=
        inferInstanceAs (CommSemiring (R.obj Y))
    (tensorObj F G).map f (x ⊗ₜ y) = (F.map f x) ⊗ₜ (G.map f y) := rfl

def tensorHom (f : F ⟶ H) (g : G ⟶ K) :
    tensorObj F G ⟶ tensorObj H K :=
  Hom.mk'' (fun X ↦ Hom.app' f X ⊗ Hom.app' g X) (by
    intro X Y h
    apply TensorProduct.ext (R := R.obj X)
    ext a b
    dsimp
    simp only [ModuleCat.restrictScalars, ModuleCat.RestrictScalars.map']
    sorry)
    -- change ((Hom.app f Y ⊗ Hom.app g Y) (restrictionApp _ _)) = _
    -- erw [comp_apply]
    -- erw [restrictionApp_apply, restrictionApp_apply]


variable (F)

def whiskerLeft (g : G ⟶ H) : tensorObj F G ⟶ tensorObj F H :=
  Hom.mk'' (fun X ↦ F.obj' X ◁ Hom.app' g X) sorry

variable {F}

def whiskerRight (f : F ⟶ G) (H : PresheafOfModules (R ⋙ forget₂ _ _)) :
    tensorObj F H ⟶ tensorObj G H :=
  Hom.mk'' (fun X ↦ Hom.app' f X ▷ H.obj' X ) sorry

variable (F G H)

def associator :
    tensorObj (tensorObj F G) H ≅ tensorObj F (tensorObj G H) :=
  isoMk'' (fun X ↦ α_ (F.obj' X) (G.obj' X) (H.obj' X)) sorry

def leftUnitor : tensorObj (unit _) F ≅ F :=
  isoMk'' (fun X ↦ λ_ (F.obj' X)) sorry

def rightUnitor : tensorObj F (unit _) ≅ F :=
  isoMk'' (fun X ↦ ρ_ (F.obj' X)) sorry

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

variable {F G H}

@[simp]
lemma evaluation_map_tensorHom (f : F ⟶ H) (g : G ⟶ K) (X : Cᵒᵖ) :
    Hom.app' (f ⊗ g) X = Hom.app' f X ⊗ Hom.app' g X:= rfl

variable (F)

@[simp]
lemma evaluation_map_whiskerLeft (g : G ⟶ H) (X : Cᵒᵖ) :
    Hom.app' (F ◁ g) X = F.obj' X ◁ Hom.app' g X := rfl

variable {F}

@[simp]
lemma evaluation_map_whiskerRight
    (f : F ⟶ G) (H : PresheafOfModules (R ⋙ forget₂ _ _)) (X : Cᵒᵖ) :
    Hom.app' (f ▷ H) X = Hom.app' f X ▷ H.obj' X := rfl

lemma evaluation_jointly_faithful (f g : F ⟶ G)
    (h : ∀ (X : Cᵒᵖ), Hom.app' f X = Hom.app' g X) : f = g := by
  ext1 X
  exact h _

attribute [local ext] evaluation_jointly_faithful
attribute [-ext] Hom.ext
attribute [-simp] evaluation_map

@[simp]
lemma evaluation_map_associator_hom (X : Cᵒᵖ) :
    Hom.app' (α_ F G H).hom X =
      by exact (α_ (F.obj' X) (G.obj' X) (H.obj' X)).hom := by
  rfl

lemma pentagon (F G H K : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)) :
    (α_ F G H).hom ▷ K ≫ (α_ F (G ⊗ H) K).hom ≫ F ◁ (α_ G H K).hom =
      (α_ (F ⊗ G) H K).hom ≫ (α_ F G (H ⊗ K)).hom := by
  ext1 X
  simp only [Functor.comp_obj, Functor.map_comp, evaluation_map_whiskerRight,
    evaluation_map_associator_hom, evaluation_map_whiskerLeft]
  apply MonoidalCategory.pentagon (F.obj' X) (G.obj' X) (H.obj' X) (K.obj' X)

lemma associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃):
    ((f₁ ⊗ f₂) ⊗ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom =
      (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ f₂ ⊗ f₃) := by
  ext1 X
  simp only [Functor.map_comp, evaluation_map_tensorHom,
    evaluation_map_associator_hom]
  exact MonoidalCategory.associator_naturality (Hom.app' f₁ X) (Hom.app' f₂ X) (Hom.app' f₃ X)

set_option maxHeartbeats 400000 in
instance : MonoidalCategory (PresheafOfModules (R ⋙ forget₂ _ _)) where
  tensorHom_def _ _ := by ext1; simp [tensorHom_def]
  tensor_id _ _ := by ext1;simp; rfl
  tensor_comp f₁ f₂ g₁ g₂ := by ext1; simp
  whiskerLeft_id _ _ := by ext1; simp; rfl
  id_whiskerRight _ _ := by ext1; simp; rfl
  associator_naturality := associator_naturality
  leftUnitor_naturality := sorry
  rightUnitor_naturality := sorry
  pentagon F G H K := pentagon F G H K
  triangle := sorry
