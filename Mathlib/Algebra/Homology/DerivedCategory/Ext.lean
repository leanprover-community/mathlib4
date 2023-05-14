import Mathlib.Algebra.Homology.DerivedCategory.Basic

universe v u

namespace CategoryTheory

open Category Preadditive

namespace Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (X Y Z : C) (n : ℕ)

structure newExt : Type (max u v) :=
  hom : (DerivedCategory.singleFunctor _ 0).obj X ⟶
    ((DerivedCategory.singleFunctor _ 0).obj Y)⟦(n : ℤ)⟧

namespace newExt

variable {X Y Z n}

lemma hom_injective (e₁ e₂ : newExt X Y n) (h : e₁.hom = e₂.hom) : e₁ = e₂ := by
  cases e₁
  cases e₂
  simpa using h

lemma mk_surjective (e : newExt X Y n) : ∃ (f : _), e = mk f := ⟨e.hom, rfl⟩

attribute [local ext] hom_injective

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
  mk ((DerivedCategory.singleFunctor _ 0).map f ≫ (shiftFunctorZero _ ℤ).inv.app _)

noncomputable instance : HasGradedHSMul (newExt Y Z) (newExt X Y) (newExt X Z) where
  γhsmul' a b c h α β := mk (β.hom ≫ (α.hom⟦(b : ℤ)⟧') ≫
    (shiftFunctorAdd' (DerivedCategory C) (a : ℤ) (b : ℤ) (c : ℤ)
      (by rw [← h, Nat.cast_add])).inv.app _)

@[simp]
lemma γhsmul_hom {p q n : ℕ} (α : newExt Y Z p) (β : newExt X Y q) (hpq : p + q = n) :
  (α •[hpq] β).hom = β.hom ≫ (α.hom⟦(q : ℤ)⟧') ≫
    (shiftFunctorAdd' (DerivedCategory C) (p : ℤ) (q : ℤ) (n : ℤ)
      (by rw [← hpq, Nat.cast_add])).inv.app _ := rfl

noncomputable example {p q n : ℕ} (α : newExt Y Z p) (β : newExt X Y q) (hpq : p + q = n) :
    newExt X Z n := α •[hpq] β

noncomputable example (f : newExt Y Z n) (g : X ⟶ Y) : newExt X Z n :=
  f •[add_zero n] (newExt.ofHom g)

lemma γhsmul_add {p q n : ℕ} (α : newExt Y Z p) (β₁ β₂ : newExt X Y q) (hpq : p + q = n) :
    α •[hpq] (β₁ + β₂) = α •[hpq] β₁ + α •[hpq] β₂ := by
  obtain ⟨g, rfl⟩ := mk_surjective α
  obtain ⟨f₁, rfl⟩ := mk_surjective β₁
  obtain ⟨f₂, rfl⟩ := mk_surjective β₂
  apply hom_injective
  dsimp
  rw [add_comp]

lemma add_γhsmul {p q n : ℕ} (α₁ α₂ : newExt Y Z p) (β : newExt X Y q) (hpq : p + q = n) :
    (α₁ + α₂) •[hpq] β = α₁ •[hpq] β + α₂ •[hpq] β := by
  obtain ⟨g₁, rfl⟩ := mk_surjective α₁
  obtain ⟨g₂, rfl⟩ := mk_surjective α₂
  obtain ⟨f, rfl⟩ := mk_surjective β
  apply hom_injective
  dsimp
  rw [Functor.map_add, add_comp, comp_add]

end newExt

end Abelian

end CategoryTheory
