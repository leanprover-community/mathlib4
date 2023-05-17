import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Shift.ShiftedHom

universe v u

namespace CategoryTheory

open Category Preadditive DerivedCategory

namespace Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (X Y Z : C) (n : ℕ)

structure newExt : Type (max u v) :=
  hom : ShiftedHom ℤ ((singleFunctor _ 0).obj X) ((singleFunctor _ 0).obj Y) n

namespace newExt

variable {X Y Z n}

lemma hom_injective (e₁ e₂ : newExt X Y n) (h : e₁.hom = e₂.hom) : e₁ = e₂ := by
  cases e₁
  cases e₂
  simpa using h

lemma mk_surjective (e : newExt X Y n) : ∃ (f : _), e = mk f := ⟨e.hom, rfl⟩

@[simps]
noncomputable instance : AddCommGroup (newExt X Y n) where
  zero := mk 0
  neg f := mk (-f.hom)
  add f₁ f₂ := mk (f₁.hom + f₂.hom)
  sub f₁ f₂ := mk (f₁.hom - f₂.hom)
  add_assoc f₁ f₂ f₃ := hom_injective _ _ (add_assoc _ _ _)
  zero_add f := hom_injective _ _ (zero_add _)
  add_zero f := hom_injective _ _ (add_zero _)
  add_comm f₁ f₂ := hom_injective _ _ (add_comm _ _)
  add_left_neg f := hom_injective _ _ (add_left_neg _)
  sub_eq_add_neg f₁ f₂ := hom_injective _ _ (sub_eq_add_neg _ _)

noncomputable def ofHom (f : X ⟶ Y) : newExt X Y 0 :=
  mk (ShiftedHom.mk₀ ((singleFunctor _ 0).map f) ((0 : ℕ) : ℤ) rfl)

variable (X Y)

noncomputable def ofHomAddEquiv : (X ⟶ Y) ≃+ newExt X Y 0 where
  toFun f := ofHom f
  invFun g := (singleFunctor C 0).preimage (g.hom ≫
    (shiftFunctorZero' (DerivedCategory C) ((0 : ℕ) : ℤ) (by rfl)).hom.app _)
  left_inv f := by
    apply (singleFunctor C 0).map_injective
    simp only [Functor.image_preimage, ofHom, ShiftedHom.mk₀, assoc, Iso.inv_hom_id_app,
      Functor.id_obj, comp_id]
  right_inv g := by
    apply hom_injective
    dsimp only [ofHom, ShiftedHom.mk₀]
    rw [Functor.image_preimage, assoc, Iso.hom_inv_id_app, comp_id]
  map_add' x y := by
    apply hom_injective
    simp [ofHom]

noncomputable instance : One (newExt X X 0) := ⟨ofHom (𝟙 _)⟩

@[simp]
lemma one_hom : (1 : newExt X X 0).hom = ShiftedHom.mk₀ (𝟙 _) ((0 : ℕ) : ℤ) rfl := by
  rw [← (singleFunctor C 0).map_id]
  rfl

@[simp]
lemma ofHom_id : ofHom (𝟙 X) = 1 := rfl

variable {X Y}

noncomputable instance : HasGradedHSMul (newExt Y Z) (newExt X Y)
    (newExt X Z) where
  γhsmul' a b c h α β :=
    mk (α.hom •[show (a : ℤ) + b = c by rw [← h, Nat.cast_add]] β.hom)

@[simp]
lemma γhsmul_hom {p q n : ℕ} (α : newExt Y Z p) (β : newExt X Y q) (hpq : p + q = n) :
  (α •[hpq] β).hom = α.hom •[by rw [← hpq, Nat.cast_add]] β.hom := rfl

noncomputable example {p q n : ℕ} (α : newExt Y Z p) (β : newExt X Y q) (hpq : p + q = n) :
    newExt X Z n := α •[hpq] β

noncomputable example (f : newExt Y Z n) (g : X ⟶ Y) : newExt X Z n :=
  f •[add_zero n] (newExt.ofHom g)

@[simp]
lemma γhsmul_add {p q n : ℕ} (α : newExt Y Z p) (β₁ β₂ : newExt X Y q) (hpq : p + q = n) :
    α •[hpq] (β₁ + β₂) = α •[hpq] β₁ + α •[hpq] β₂ := by
  apply hom_injective
  apply ShiftedHom.γhsmul_add

@[simp]
lemma add_γhsmul {p q n : ℕ} (α₁ α₂ : newExt Y Z p) (β : newExt X Y q) (hpq : p + q = n) :
    (α₁ + α₂) •[hpq] β = α₁ •[hpq] β + α₂ •[hpq] β := by
  apply hom_injective
  apply ShiftedHom.add_γhsmul

@[simp]
lemma one_γhsmul {n : ℕ} (β : newExt X Y n) :
    (1 : newExt Y Y 0) •[zero_add n] β = β := by
  apply hom_injective
  dsimp
  rw [one_hom]
  apply ShiftedHom.one_γhsmul'

@[simp]
lemma γhsmul_one {n : ℕ} (α : newExt X Y n) :
    α •[add_zero n] (1 : newExt X X 0)  = α := by
  apply hom_injective
  dsimp
  rw [one_hom]
  apply ShiftedHom.γhsmul_one'

instance {X₁ X₂ X₃ X₄ : C} : IsAssocGradedHSMul (newExt X₃ X₄)
    (newExt X₂ X₃) (newExt X₁ X₂) (newExt X₂ X₄) (newExt X₁ X₃)
    (newExt X₁ X₄) where
  γhsmul_assoc p₁ p₂ p₃ α β γ p₁₂ p₂₃ p₁₂₃ h₁₂ h₂₃ h₁₂₃ := by
    apply hom_injective
    rw [γhsmul_hom, γhsmul_hom, γhsmul_hom, γhsmul_hom]
    apply IsAssocGradedHSMul.γhsmul_assoc

@[simp]
lemma ofHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    ofHom (f ≫ g) = ofHom g •[add_zero 0] ofHom f := by
  apply hom_injective
  dsimp [ofHom]
  simp only [Functor.map_comp, ShiftedHom.mk₀_comp]

end newExt

@[simps]
noncomputable def newExtFunctor.obj (n : ℕ) (X : C) : C ⥤ Ab where
  obj := fun Y => AddCommGroupCat.of (newExt X Y n)
  map := fun f => AddCommGroupCat.ofHom (AddMonoidHom.mk'
    (fun β => (newExt.ofHom f) •[zero_add _] β)
    (fun β₁ β₂ => by dsimp ; simp))

@[simps]
noncomputable def newExtFunctor (n : ℕ) : Cᵒᵖ ⥤ C ⥤ Ab where
  obj X := newExtFunctor.obj n X.unop
  map {X₁ X₂} g :=
    { app := fun Y => AddCommGroupCat.ofHom (AddMonoidHom.mk'
        (fun α => (show newExt X₁.unop Y n from α) •[add_zero n] (newExt.ofHom g.unop))
        (fun _ _ => newExt.add_γhsmul _ _ _ _)) }

end Abelian

end CategoryTheory
