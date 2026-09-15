module

public import Mathlib

@[expose] public section

open CategoryTheory

/-- General lemma: composing two morphisms with eqToHom transports, where the
    intermediate transports cancel out. -/
lemma eqToHom_comp_cancel {C : Type*} [Category C] {X X' Y Y' Z Z' : C}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (eqToHom hX.symm ≫ f ≫ eqToHom hY) ≫ (eqToHom hY.symm ≫ g ≫ eqToHom hZ) =
    eqToHom hX.symm ≫ (f ≫ g) ≫ eqToHom hZ := by
  have h1 : eqToHom hY ≫ eqToHom hY.symm = 𝟙 Y := by
    rw [eqToHom_trans]
    <;> simp
  calc
    (eqToHom hX.symm ≫ f ≫ eqToHom hY) ≫ (eqToHom hY.symm ≫ g ≫ eqToHom hZ)
      = eqToHom hX.symm ≫ f ≫ (eqToHom hY ≫ eqToHom hY.symm) ≫ g ≫ eqToHom hZ := by
        simp only [Category.assoc]
        <;> rfl
    _ = eqToHom hX.symm ≫ f ≫ 𝟙 Y ≫ g ≫ eqToHom hZ := by
        rw [h1]
        <;> simp only [Category.assoc]
    _ = eqToHom hX.symm ≫ (f ≫ 𝟙 Y) ≫ g ≫ eqToHom hZ := by
        simp only [Category.assoc]
        <;> rfl
    _ = eqToHom hX.symm ≫ f ≫ g ≫ eqToHom hZ := by
        rw [Category.comp_id f]
        <;> simp only [Category.assoc]
        <;> rfl
    _ = eqToHom hX.symm ≫ (f ≫ g) ≫ eqToHom hZ := by
        simp only [Category.assoc]
        <;> rfl

end
