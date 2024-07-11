import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Closed.Monoidal

universe v' v u' u

namespace CategoryTheory

open Category MonoidalCategory MonoidalClosed

variable {V : Type (u' + 1)} [Category.{u'} V] [MonoidalCategory V] [MonoidalClosed V]

variable [SymmetricCategory V]

namespace MonoidalClosed

@[simp]
def comp (X Y Z : V) : ((ihom X).obj Y) ⊗ ((ihom Y).obj Z) ⟶ ((ihom X).obj Z) :=
  curry ((α_ X _ _).inv ≫ (ihom.ev X).app Y ▷ (ihom Y).obj Z ≫ (ihom.ev Y).app Z)
--uncurry_pre
-- uncurry ((pre ((ihom.ev X).app Y)).app Z))


-- MonoidalClosed category is enriched over itself
-- need more api for proofs
instance : EnrichedCategory V V where
  Hom X Y := (ihom X).obj Y
  id X := curry (ρ_ X).hom
  comp := comp
  id_comp X Y := sorry
  comp_id X Y := sorry
  assoc W X Y Z := sorry

def homEquiv (X Y : V) : (X ⟶ Y) ≃ (𝟙_ V ⟶ (ihom X).obj Y) :=
  ((ρ_ X).homCongr (Iso.refl Y)).symm.trans ((ihom.adjunction X).homEquiv (𝟙_ V) Y)

def homEquiv_id (A : V) : homEquiv A A (𝟙 A) = eId V A := by
  change _ = curry (ρ_ A).hom
  simp [homEquiv, curry]

def homEquiv_comp {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homEquiv X Z (f ≫ g) = (λ_ _).inv ≫ (homEquiv X Y f ⊗ homEquiv Y Z g) ≫
      eComp V X Y Z := by
  change _ = _ ≫ _ ≫ comp X Y Z
  simp [homEquiv, curry]
  sorry

end MonoidalClosed

section

variable {C : Type u} [Category.{v} C]

-- when an enriched category is already a category, we should have more data
variable (V C) in
class EnrichedCategoryCategory extends EnrichedCategory V C where
  homEquiv (X Y : C) : (X ⟶ Y) ≃ (𝟙_ V ⟶ EnrichedCategory.Hom X Y)
  homEquiv_id (X : C) : homEquiv X X (𝟙 X) = eId V X := by aesop_cat
  homEquiv_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homEquiv X Z (f ≫ g) = (λ_ _).inv ≫ (homEquiv X Y f ⊗ homEquiv Y Z g) ≫
      eComp V X Y Z := by aesop_cat

namespace EnrichedCategoryCategory

instance : EnrichedCategoryCategory V V where
  homEquiv := MonoidalClosed.homEquiv
  homEquiv_id := MonoidalClosed.homEquiv_id
  homEquiv_comp := MonoidalClosed.homEquiv_comp

variable [h : EnrichedCategoryCategory V C]

noncomputable
def temp : CategoryTheory.Equivalence (ForgetEnrichment V C) C where
  functor := {
    obj := fun X ↦ ForgetEnrichment.to V X
    map := fun f ↦ (homEquiv _ _).symm (ForgetEnrichment.homTo V f)
    map_id := fun A ↦ by
      simp only [forgetEnrichment_id, ← homEquiv_id, Equiv.symm_apply_apply]
    map_comp := fun f g ↦ by
      apply_fun (fun f ↦ (h.homEquiv _ _) f)
      simp [homEquiv_comp] }
  inverse := {
    obj := fun A ↦ ForgetEnrichment.of V A
    map := fun f ↦ (ForgetEnrichment.homOf V (homEquiv _ _ f))
    map_id := fun A ↦ by simp [homEquiv_id]
    map_comp := by
      dsimp
      intro A B C f g
      dsimp [ForgetEnrichment.homOf]
      simp [homEquiv_comp]
      sorry
  }
  unitIso := {
    hom := { app := fun X ↦ 𝟙 X }
    inv := { app := fun X ↦ 𝟙 X } }
  counitIso := {
    hom := { app := fun X ↦ 𝟙 X }
    inv := { app := fun X ↦ 𝟙 X } }

section Tensor

noncomputable def whiskerRight {X X' : C} (f : X ⟶ X') (Y : C) :
    (X' ⟶[V] Y) ⟶ (X ⟶[V] Y) :=
  (λ_ _).inv ≫ homEquiv _ _ f ▷ _ ≫ eComp V X X' Y

@[simp]
lemma whiskerRight_id (X Y : C) : whiskerRight (𝟙 X) Y = 𝟙 (X ⟶[V] Y) := by
  simp [whiskerRight, homEquiv_id]

@[simp, reassoc]
lemma whiskerRight_comp {X X' X'' : C} (f : X ⟶ X') (f' : X' ⟶ X'') (Y : C) :
    whiskerRight (f ≫ f') Y = (whiskerRight (V := V) f' Y) ≫ whiskerRight f Y := by
  dsimp [whiskerRight]
  simp [assoc, homEquiv_comp, comp_whiskerRight, leftUnitor_inv_whiskerRight, ← e_assoc']
  sorry --rfl

noncomputable def whiskerLeft (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    (X ⟶[V] Y) ⟶ (X ⟶[V] Y') :=
  (ρ_ _).inv ≫ _ ◁ homEquiv _ _ g ≫ eComp V X Y Y'

@[simp]
lemma whiskerLeft_id (X Y : C) : whiskerLeft X (𝟙 Y) = 𝟙 (X ⟶[V] Y) := by
  simp [whiskerLeft, homEquiv_id]

@[simp, reassoc]
lemma whiskerLeft_comp (X : C) {Y Y' Y'' : C} (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    whiskerLeft X (g ≫ g') = whiskerLeft X g ≫ whiskerLeft (V := V) X g' := by
  dsimp [whiskerLeft]
  simp only [assoc, homEquiv_comp, comp_whiskerRight, leftUnitor_inv_whiskerRight, ← e_assoc']
  sorry --rfl

@[reassoc]
lemma whisker_exchange {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    whiskerLeft (V := V) X' g ≫ whiskerRight f Y' =
      whiskerRight f Y ≫ whiskerLeft X g := by
  have := ((ρ_ _).inv ≫ _ ◁ homEquiv _ _ g ≫ (λ_ _).inv ≫ homEquiv _ _ f ▷ _) ≫= (e_assoc V X X' Y Y').symm
  sorry

attribute [local simp] whisker_exchange

variable (V C) in
/-- The bifunctor `Cᵒᵖ ⥤ C ⥤ V` which sends `X : Cᵒᵖ` and `Y : C` to `X.unop ⟶[V] Y`. -/
@[simps]
noncomputable def eHomFunctor : Cᵒᵖ ⥤ C ⥤ V where
  obj X :=
    { obj := fun Y => X.unop ⟶[V] Y
      map := fun φ => whiskerLeft X.unop φ }
  map φ :=
    { app := fun Y => whiskerRight φ.unop Y }

class copower (A : V) (X : C) where
  obj : C
  -- C(A ⊗ᵥ X, -) ≅ V(A, C(X, -))
  iso : (eHomFunctor V C).obj (Opposite.op obj) ≅
    (eHomFunctor V C).obj (Opposite.op X) ⋙ (eHomFunctor V V).obj (Opposite.op A)
  α' : A ⟶ (X ⟶[V] obj) -- A ⟶ C(X, A ⊗ᵥ X)
  fac (Y : C) : (iso.hom.app Y) =
    curry (α' ▷ _ ≫ eComp V X obj Y)

-- iso.hom.app Y : C(A ⊗ᵥ X, Y) ⟶ V(A, C(X, Y))

-- eComp V X obj Y : C(X, A ⊗ᵥ X) ⊗ C(A ⊗ᵥ X, Y)  ⟶ C(X, Y)
-- α' ▷ _ : A ⊗ C(X, A ⊗ᵥ X) ⟶ C(X, A ⊗ᵥ X) ⊗ C(A ⊗ᵥ X, Y)
-- α' ▷ _ ≫ eComp V X obj Y : A ⊗ C(X, A ⊗ᵥ X) ⟶ C(X, Y)
-- curry (α' ▷ _ ≫ eComp V X obj Y) : C(X, A ⊗ᵥ X) ⟶ V(A, C(X, Y))

variable (C) in
class Copowered where
  copower (A : V) (X : C) : copower A X

variable (A : V) (X Y : C) [copower A X]

scoped infixr:70 " ⊗ᵥ " => copower.obj

def copowerα : A ⟶ (X ⟶[V] (A ⊗ᵥ X)) := copower.α'

-- C(A ⊗ᵥ X, Y) ≅ V(A, C(X, Y))
noncomputable def copowerIso : ((A ⊗ᵥ X) ⟶[V] Y) ≅ (ihom A).obj (X ⟶[V] Y) :=
  copower.iso.app Y

noncomputable def copowerEquiv : (A ⊗ᵥ X ⟶ Y) ≃ (A ⟶ (X ⟶[V] Y)) where
  toFun f := (homEquiv _ _).symm ((homEquiv _ _ f) ≫ (copowerIso A X Y).hom)
  invFun f := (homEquiv _ _).symm ((homEquiv _ _ f) ≫ (copowerIso A X Y).inv)
  left_inv _ := by aesop
  right_inv _ := by aesop

variable {A X Y} in
noncomputable abbrev copowerDesc (f : A ⟶ (X ⟶[V] Y)) : A ⊗ᵥ X ⟶ Y :=
  (copowerEquiv _ _ _).symm f

section

variable {A B : V} (f : A ⟶ B) {X Y : C} (g : X ⟶ Y)
  [copower A X] [copower B Y]

noncomputable def copowerMap :
    A ⊗ᵥ X ⟶ B ⊗ᵥ Y := copowerDesc (f ≫ copowerα B Y ≫ whiskerRight g _)

scoped infixr:70 " ⊗ₛ " => copowerMap

end
