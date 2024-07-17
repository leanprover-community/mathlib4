import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Closed.Monoidal

universe v' v u' u

namespace CategoryTheory

open Category MonoidalCategory MonoidalClosed

variable {V : Type (u' + 1)} [Category.{u'} V] [MonoidalCategory V] [MonoidalClosed V]

variable [SymmetricCategory V]

namespace MonoidalClosed

def homEquiv (X Y : V) : (X ⟶ Y) ≃ (𝟙_ V ⟶ (ihom X).obj Y) :=
  ((ρ_ X).homCongr (Iso.refl Y)).symm.trans ((ihom.adjunction X).homEquiv (𝟙_ V) Y)

@[simp]
def comp (X Y Z : V) : ((ihom X).obj Y) ⊗ ((ihom Y).obj Z) ⟶ ((ihom X).obj Z) :=
  curry ((α_ X _ _).inv ≫ (ihom.ev X).app Y ▷ (ihom Y).obj Z ≫ (ihom.ev Y).app Z)

def homEquiv_id (A : V) : homEquiv A A (𝟙 A) = curry (ρ_ A).hom := by
  simp [homEquiv, curry]

def homEquiv_comp {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homEquiv X Z (f ≫ g) = (λ_ _).inv ≫ (homEquiv X Y f ⊗ homEquiv Y Z g) ≫
      comp X Y Z := by
  simp
  sorry

variable [SymmetricCategory V]

-- Symmetric MonoidalClosed category is enriched over itself
instance : EnrichedCategory V V where
  Hom X Y := (ihom X).obj Y
  id X := curry (ρ_ X).hom
  comp := comp
  id_comp := sorry
  comp_id X Y := sorry
  assoc W X Y Z := sorry

def homEquiv' (A X : V) : (ihom (A ⊗ X)) ≅ (ihom X) ⋙ (ihom A) := sorry

end MonoidalClosed

section

variable {C : Type u} [Category.{v} C]

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

variable [EnrichedCategoryCategory V C]

open ForgetEnrichment in
noncomputable
def temp : CategoryTheory.Equivalence (ForgetEnrichment V C) C where
  functor := {
    obj := fun X ↦ ForgetEnrichment.to V X
    map := fun f ↦ (homEquiv _ _).symm (ForgetEnrichment.homTo V f)
    map_id := fun A ↦ by
      simp only [forgetEnrichment_id, ← homEquiv_id, Equiv.symm_apply_apply]
    map_comp := fun f g ↦ by
      apply_fun (fun f ↦ (homEquiv (V := V) _ _) f)
      simp only [forgetEnrichment_comp, assoc, Equiv.apply_symm_apply, homEquiv_comp] }
  inverse := {
    obj := fun A ↦ ForgetEnrichment.of V A
    map := fun f ↦ (ForgetEnrichment.homOf V (homEquiv _ _ f))
    map_id := fun A ↦ by simp [homEquiv_id]
    map_comp := fun {X Y Z} f g ↦ sorry
  }
  unitIso := {
    hom := { app := fun X ↦ 𝟙 X }
    inv := { app := fun X ↦ 𝟙 X } }
  counitIso := {
    hom := { app := fun X ↦ 𝟙 X }
    inv := { app := fun X ↦ 𝟙 X } }

/-
open ForgetEnrichment in
noncomputable
def temp' : CategoryTheory.Equivalence (ForgetEnrichment V V) V where
  functor := {
    obj := fun X ↦ ForgetEnrichment.to V X
    map := fun f ↦ (MonoidalClosed.homEquiv _ _).symm (ForgetEnrichment.homTo V f)
    map_id := fun A ↦ by
      apply_fun (fun f ↦ MonoidalClosed.homEquiv _ _ f)
      simp [MonoidalClosed.homEquiv_id]; rfl
    map_comp := fun f g ↦ by
      apply_fun (fun f ↦ (MonoidalClosed.homEquiv (V := V) _ _) f)
      simp [MonoidalClosed.homEquiv_comp]; rfl }
  inverse := {
    obj := fun A ↦ ForgetEnrichment.of V A
    map := fun f ↦ ForgetEnrichment.homOf V (MonoidalClosed.homEquiv _ _ f)
    map_id := fun A ↦ by simp [MonoidalClosed.homEquiv_id, homOf, of]; sorry
    map_comp := fun {X Y Z} f g ↦ sorry }
  unitIso := {
    hom := { app := fun X ↦ 𝟙 X }
    inv := { app := fun X ↦ 𝟙 X } }
  counitIso := {
    hom := { app := fun X ↦ 𝟙 X }
    inv := { app := fun X ↦ 𝟙 X } }
-/

noncomputable def whiskerRight {X X' : C} (f : X ⟶ X') (Y : C) :
    (X' ⟶[V] Y) ⟶ X ⟶[V] Y :=
  (λ_ _).inv ≫ homEquiv X X' f ▷ _ ≫ eComp V X X' Y

@[simp]
lemma whiskerRight_id (X Y : C) : whiskerRight (𝟙 X) Y = 𝟙 (X ⟶[V] Y) := by
  simp [whiskerRight, homEquiv_id]

@[simp, reassoc]
lemma whiskerRight_comp {X X' X'' : C} (f : X ⟶ X') (f' : X' ⟶ X'') (Y : C) :
    whiskerRight (f ≫ f') Y = (whiskerRight (V := V) f' Y) ≫ whiskerRight f Y := by
  dsimp [whiskerRight]
  simp only [homEquiv_comp, comp_whiskerRight, leftUnitor_inv_whiskerRight, assoc, ← e_assoc']
  sorry

-- 3.4.13
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
    { obj := EnrichedCategory.Hom X.unop
      map := whiskerLeft X.unop }
  map φ :=
    { app := whiskerRight φ.unop }

variable (V C) in
/-- The bifunctor `C ⥤ Cᵒᵖ ⥤ V` which sends `X : C` and `Y : Cᵒᵖ` to `Y.unop ⟶[V] X`. -/
@[simps]
noncomputable def eHomFunctor' : C ⥤ Cᵒᵖ ⥤ V where
  obj X :=
    { obj := fun Y ↦ (Y.unop ⟶[V] X)
      map := fun f ↦ whiskerRight (V := V) f.unop X }
  map φ :=
    { app := fun Y ↦ whiskerLeft Y.unop φ }

section Copower

class copower (A : V) (X : C) where
  -- A ⊗ᵥ X
  obj : C
  -- C(A ⊗ᵥ X, -) ≅ V(A, C(X, -))
  iso : (eHomFunctor V C).obj (Opposite.op obj) ≅
    (eHomFunctor V C).obj (.op X) ⋙ (eHomFunctor V V).obj (.op A)

  -- A ⟶ C(X, A ⊗ᵥ X)
--  α' : A ⟶ (X ⟶[V] obj)
--  fac (Y : C) : (iso.hom.app Y) =
--    curry (α' ▷ _ ≫ eComp V X obj Y)

-- iso.hom.app Y : C(A ⊗ᵥ X, Y) ⟶ V(A, C(X, Y))

-- eComp V X obj Y : C(X, A ⊗ᵥ X) ⊗ C(A ⊗ᵥ X, Y)  ⟶ C(X, Y)
-- α' ▷ _ : A ⊗ C(A ⊗ᵥ X, Y) ⟶ C(X, A ⊗ᵥ X) ⊗ C(A ⊗ᵥ X, Y)
-- α' ▷ _ ≫ eComp V X obj Y : A ⊗ C(X, A ⊗ᵥ X) ⟶ C(X, Y)
-- curry (α' ▷ _ ≫ eComp V X obj Y) : C(X, A ⊗ᵥ X) ⟶ V(A, C(X, Y))

variable (V C) in
class Copowered where
  copower (A : V) (X : C) : copower A X

attribute [instance 100] Copowered.copower

noncomputable
instance [SymmetricCategory V] : Copowered V V where
  copower A X := {
    obj := A ⊗ X
    iso := by
      refine NatIso.ofComponents (fun Y ↦ (homEquiv' A X).app Y) sorry
--    α' := curry ((β_ X) A).hom
--    fac := sorry
  }

variable (A : V) (X Y : C) [copower A X]

scoped infixr:70 " ⊗ᵥ " => copower.obj

--def copowerα : A ⟶ (X ⟶[V] (A ⊗ᵥ X)) := copower.α'

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

variable {A B : V} (f : A ⟶ B) {X Y : C} (g : X ⟶ Y) [copower A X] [copower B Y]

noncomputable def copowerMap :
    A ⊗ᵥ X ⟶ B ⊗ᵥ Y := by
  refine copowerDesc (f ≫ (?_) ≫ whiskerRight g _)
  sorry

--scoped infixr:70 " ⊗ᵥ " => copowerMap

variable (V C) in
@[simp]
def copowerFunctor [Copowered V C] : V ⥤ C ⥤ C where
  obj A := {
    obj := fun X ↦ (Copowered.copower A X).obj
    map := fun {X Y} f ↦ sorry
  }
  map {X Y} f := {
    app := by
      intro A
      simp
      sorry
  }

end Copower

section Power

class power (A : V) (X : C) where
  -- A ⊕ᵥ X
  obj : C
  -- C(-, A ⊕ᵥ X) ≅ V(A, C(-, X))
  iso : (eHomFunctor' V C).obj obj ≅
    (eHomFunctor' V C).obj X ⋙ (eHomFunctor V V).obj (.op A)

variable (V C) in
class Powered where
  power (A : V) (X : C) : power A X := by infer_instance

attribute [instance 100] Powered.power

noncomputable
instance [SymmetricCategory V] : Powered V V where
  power A X := {
    obj := (ihom A).obj X
    iso := by
      refine NatIso.ofComponents ?_ ?_
      intro Y
      simp
      sorry
      sorry
    }

variable (A : V) (X Y : C) [power A Y]

scoped infixr:70 " ⊕ᵥ " => power.obj

-- C(A ⊗ᵥ X, Y) ≅ V(A, C(X, Y))
noncomputable def powerIso : (X ⟶[V] (A ⊕ᵥ Y)) ≅ (ihom A).obj (X ⟶[V] Y) :=
  power.iso.app (.op X)

noncomputable def powerEquiv : (X ⟶ A ⊕ᵥ Y) ≃ (A ⟶ (X ⟶[V] Y)) where
  toFun f := (homEquiv _ _).symm ((homEquiv _ _ f) ≫ (powerIso A X Y).hom)
  invFun f := (homEquiv _ _).symm ((homEquiv _ _ f) ≫ (powerIso A X Y).inv)
  left_inv _ := by aesop
  right_inv _ := by aesop

variable {A X Y} in
noncomputable abbrev powerDesc (f : A ⟶ (X ⟶[V] Y)) : X ⟶ A ⊕ᵥ Y :=
  (powerEquiv _ _ _).symm f

variable (V C) in
@[simp]
def powerFunctor [Powered V C] : Vᵒᵖ ⥤ C ⥤ C where
  obj A := {
    obj := fun X ↦ (Powered.power A.unop X).obj
    map := fun {X Y} f ↦ sorry
  }
  map := sorry

end Power

variable [Powered V C] [Copowered V C]

noncomputable
def adj (A : V) : ((copowerFunctor V C).obj A) ⊣ ((powerFunctor V C).obj (.op A)) where
  homEquiv X Y := (copowerEquiv A X Y).trans (powerEquiv A X Y).symm
  unit := {
    app := fun X ↦ (copowerEquiv _ _ _).trans (powerEquiv _ _ _).symm (𝟙 _)
    naturality := sorry
  }
  counit := {
    app := fun X ↦ (powerEquiv _ _ _).trans (copowerEquiv _ _ _).symm (𝟙 _)
    naturality := sorry
  }

variable (D : Type (u + 1)) [Category.{u} D]

instance : MonoidalClosed (Type u) where
  closed X := {
    rightAdj := sorry
    adj := sorry
  }

instance : EnrichedCategoryCategory (Type u) D where
  Hom X Y := X ⟶ Y
  id X _ := 𝟙 X
  comp _ _ _ := fun ⟨f, g⟩ ↦ f ≫ g
  assoc := by
    intro W X Y Z
    simp
    sorry
  homEquiv X Y := sorry
  homEquiv_id := sorry
  homEquiv_comp := sorry

  instance : Copowered (Type u) D where
    copower A X := {
      obj := sorry
      iso := sorry
    }
