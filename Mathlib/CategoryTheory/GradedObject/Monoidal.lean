import Mathlib.CategoryTheory.GradedObject.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Fintype.Sigma

/-!
# The monoidal structure on graded objects in a monoidal category.

This is a warm-up to the monoidal structure on chain complexes.

For now I just do the special case of objects graded by `ℕ`.
We may need to generalize API around `Finset.Nat.antidiagonal` in order to generalize.
-/

universe v u

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory

variable {V : Type u} [Category.{v} V] [Preadditive V] [MonoidalCategory V] [MonoidalPreadditive V]
  [HasFiniteBiproducts V]

namespace GradedObject

namespace MonoidalCategory

def tensorObj (X Y : GradedObject ℕ V) (i : ℕ) : V :=
  biproduct (fun p : Finset.Nat.antidiagonal i => (X p.1.1) ⊗ (Y p.1.2))

def tensorHom {W X Y Z : GradedObject ℕ V} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj W Y ⟶ tensorObj X Z :=
  fun _ => biproduct.map fun p => f p.1.1 ⊗ g p.1.2

def associator_distributor (X Y Z : GradedObject ℕ V) (i : ℕ) :
    (tensorObj (tensorObj X Y) Z) i ≅
      biproduct (fun p : Finset.Nat.antidiagonal i =>
        biproduct (fun q : Finset.Nat.antidiagonal p.1.1 => (X q.1.1 ⊗ Y q.1.2) ⊗ Z p.1.2)) :=
  biproduct.mapIso fun _ => rightDistributor _ _

def associator_iterated (X Y Z : GradedObject ℕ V) (i : ℕ) :
    biproduct (fun p : Finset.Nat.antidiagonal i =>
        biproduct (fun q : Finset.Nat.antidiagonal p.1.1 => (X q.1.1 ⊗ Y q.1.2) ⊗ Z p.1.2))
      ≅ biproduct (fun p : Σ p₁ : Finset.Nat.antidiagonal i, Finset.Nat.antidiagonal p₁.1.1 =>
          (X p.2.1.1 ⊗ Y p.2.1.2) ⊗ Z p.1.1.2) :=
  biproductBiproductIso _ _

def associator_underlying (X Y Z : GradedObject ℕ V) (i : ℕ) :
    biproduct (fun p : Σ p₁ : Finset.Nat.antidiagonal i, Finset.Nat.antidiagonal p₁.1.1 =>
        (X p.2.1.1 ⊗ Y p.2.1.2) ⊗ Z p.1.1.2)
      ≅ biproduct (fun p : Σ p₁ : Finset.Nat.antidiagonal i, Finset.Nat.antidiagonal p₁.1.1 =>
          X p.2.1.1 ⊗ (Y p.2.1.2 ⊗ Z p.1.1.2)) :=
  biproduct.mapIso fun _ => α_ _ _ _

def associator₄_equiv : (Σ p₁ : Finset.Nat.antidiagonal i, Finset.Nat.antidiagonal p₁.1.1) ≃ (Σ p₁ : Finset.Nat.antidiagonal i, Finset.Nat.antidiagonal p₁.1.2) :=
  { toFun := fun ⟨⟨⟨ab, c⟩, w₁⟩, ⟨⟨a, b⟩, w₂⟩⟩ =>
      ⟨⟨⟨a, b + c⟩, by simp at w₁ w₂; subst w₁ w₂; simp [add_assoc]⟩, ⟨⟨b, c⟩, by simp⟩⟩
    invFun := fun ⟨⟨⟨a, bc⟩, w₁⟩, ⟨⟨b, c⟩, w₂⟩⟩ =>
      ⟨⟨⟨a + b, c⟩, by simp at w₁ w₂; subst w₁ w₂; simp [add_assoc]⟩, ⟨⟨a, b⟩, by simp⟩⟩
    left_inv := fun ⟨⟨⟨ab, c⟩, w₁⟩, ⟨⟨a, b⟩, w₂⟩⟩ => by
      simp at w₁ w₂
      subst w₂
      subst w₁
      simp
    right_inv := fun ⟨⟨⟨a, bc⟩, w₁⟩, ⟨⟨b, c⟩, w₂⟩⟩ => by
      simp at w₁ w₂
      subst w₂
      subst w₁
      simp }

def associator_whisker_equiv (X Y Z : GradedObject ℕ V) (i : ℕ) :
    biproduct (fun p : Σ p₁ : Finset.Nat.antidiagonal i, Finset.Nat.antidiagonal p₁.1.1 => X p.2.1.1 ⊗ (Y p.2.1.2 ⊗ Z p.1.1.2)) ≅
      biproduct (fun p : Σ p₁ : Finset.Nat.antidiagonal i, Finset.Nat.antidiagonal p₁.1.2 => X p.1.1.1 ⊗ (Y p.2.1.1 ⊗ Z p.2.1.2)) :=
  biproduct.whisker_equiv associator₄_equiv
    fun ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩ => Iso.refl _

def associator_iterated' (X Y Z : GradedObject ℕ V) (i : ℕ) :
    biproduct (fun p : Σ p₁ : Finset.Nat.antidiagonal i, Finset.Nat.antidiagonal p₁.1.2 => X p.1.1.1 ⊗ (Y p.2.1.1 ⊗ Z p.2.1.2)) ≅
      biproduct (fun p : Finset.Nat.antidiagonal i => biproduct (fun q : Finset.Nat.antidiagonal p.1.2 => X p.1.1 ⊗ (Y q.1.1 ⊗ Z q.1.2))) :=
  (biproductBiproductIso
    (fun p : Finset.Nat.antidiagonal i => Finset.Nat.antidiagonal p.1.2)
    (fun (p : Finset.Nat.antidiagonal i) (q : Finset.Nat.antidiagonal p.1.2) => X p.1.1 ⊗ (Y q.1.1 ⊗ Z q.1.2))).symm

def associator_distributor' (X Y Z : GradedObject ℕ V) (i : ℕ) :
    biproduct (fun p : Finset.Nat.antidiagonal i => biproduct (fun q : Finset.Nat.antidiagonal p.1.2 => X p.1.1 ⊗ (Y q.1.1 ⊗ Z q.1.2))) ≅
      (tensorObj X (tensorObj Y Z)) i :=
  biproduct.mapIso fun _ => (leftDistributor _ _).symm

def associator (X Y Z : GradedObject ℕ V) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  GradedObject.mkIso (fun i =>
    associator_distributor X Y Z i ≪≫ associator_iterated X Y Z i ≪≫
      associator_underlying X Y Z i ≪≫ associator_whisker_equiv X Y Z i ≪≫
      associator_iterated' X Y Z i ≪≫ associator_distributor' X Y Z i)

end MonoidalCategory

open MonoidalCategory
set_option says.verify true in
set_option maxHeartbeats 0 in
instance : MonoidalCategory (GradedObject ℕ V) where
  tensorObj := tensorObj
  tensorHom := tensorHom
  tensorUnit' := fun | 0 => (𝟙_ V) | _ => sorry
  tensor_id := sorry
  tensor_comp := sorry
  associator := associator
  leftUnitor := sorry
  rightUnitor := sorry
  associator_naturality := sorry
  leftUnitor_naturality := sorry
  rightUnitor_naturality := sorry
  triangle := sorry
  pentagon W X Y Z := by
    ext i
    dsimp [MonoidalCategory.tensorObj, MonoidalCategory.tensorHom, MonoidalCategory.associator,
      associator_distributor, associator_iterated,
      associator_underlying, associator_whisker_equiv, associator_iterated',
      associator_distributor']
    ext ⟨⟨a, bc⟩, w₁⟩ ⟨⟨de, f⟩, w₂⟩ ⟨⟨d, e⟩, w₃⟩ ⟨⟨b, c⟩, w₄⟩
    simp? says
      simp only [biproduct.lift_map, biproduct.map_desc_assoc, comp_tensor_id, id_tensor_comp,
        assoc, biproduct.lift_π, biproduct.ι_map_assoc, biproduct.lift_map_assoc]
    simp only [← comp_tensor_id, ← id_tensor_comp, ← comp_tensor_id_assoc, ← id_tensor_comp_assoc]
    simp? [-comp_tensor_id, -id_tensor_comp] says
      simp only [biproduct.ι_map_assoc, biproduct.lift_π]
    ext
    sorry

end GradedObject
