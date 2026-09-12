module

public import Mathlib

@[expose] public section

open CategoryTheory

namespace VanKampen

/-- Given isomorphisms `e_x : a ≅ b`, `e_y : c ≅ d`, and morphisms `A : a ⟶ c`, `B : b ⟶ d`,
  if `e_x.inv ≫ A ≫ e_y.hom = B` then `A = e_x.hom ≫ B ≫ e_y.inv`. -/
lemma iso_sandwich_rewrite {C : Type _} [Category C] {a b c d : C}
    (e_x : a ≅ b) (e_y : c ≅ d) (A : a ⟶ c) (B : b ⟶ d)
    (h : e_x.inv ≫ A ≫ e_y.hom = B) :
    A = e_x.hom ≫ B ≫ e_y.inv := by
  have h_step1 : e_x.hom ≫ (e_x.inv ≫ A ≫ e_y.hom) ≫ e_y.inv =
      e_x.hom ≫ e_x.inv ≫ (A ≫ (e_y.hom ≫ e_y.inv)) := by
    simp only [Category.assoc]
    <;> rfl
  have h_step2 : e_x.hom ≫ e_x.inv ≫ (A ≫ (e_y.hom ≫ e_y.inv)) =
      A ≫ (e_y.hom ≫ e_y.inv) := by
    rw [e_x.hom_inv_id_assoc]
  have h_step3 : A ≫ (e_y.hom ≫ e_y.inv) = A := by
    have h_id : e_y.hom ≫ e_y.inv = 𝟙 c := e_y.hom_inv_id
    rw [h_id, Category.comp_id]
  have h1 : e_x.hom ≫ (e_x.inv ≫ A ≫ e_y.hom) ≫ e_y.inv = A := by
    rw [h_step1, h_step2, h_step3]
  have h2 : e_x.hom ≫ B ≫ e_y.inv = e_x.hom ≫ (e_x.inv ≫ A ≫ e_y.hom) ≫ e_y.inv := by
    have h3 : B = e_x.inv ≫ A ≫ e_y.hom := h.symm
    have h4 : e_x.hom ≫ B ≫ e_y.inv = e_x.hom ≫ (e_x.inv ≫ A ≫ e_y.hom) ≫ e_y.inv := by
      rw [h3]
    exact h4
  have h5 : e_x.hom ≫ B ≫ e_y.inv = A := by
    rw [h2, h1]
  exact h5.symm

end VanKampen

end
