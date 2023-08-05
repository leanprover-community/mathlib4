/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kim Liesinger
-/
import Mathlib.CategoryTheory.GradedObject.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Fintype.Sigma

/-!
# The monoidal structure on graded objects in a monoidal category.

This is a warm-up to the monoidal structure on chain complexes.

As there is a faithful functor from chain complexes to graded objects (forgetting the differentials)
the result here can be used as an ingredient for the chain complex case,
to avoid having to check the pentagon, triangle, and naturality equations.

One still needs to construct the differential on the tensor product of chain complexes,
and check that the unitors and associator defined here commute with it.

For now we just do the special case of objects graded by `ℕ`.
We may need to generalize API around `antidiagonal` in order to generalize.
-/

universe v u

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory

variable {V : Type u} [Category.{v} V] [Preadditive V] [MonoidalCategory V] [MonoidalPreadditive V]
  [HasFiniteBiproducts V] [HasZeroObject V]

open ZeroObject

namespace GradedObject

namespace MonoidalCategory

open Finset.Nat

/-- The tensor product of graded objects `X` and `Y` is, in each degree `i`,
the biproduct over `a + b = i` of `X a ⊗ Y b`. -/
def tensorObj (X Y : GradedObject ℕ V) (i : ℕ) : V :=
  biproduct (fun p : antidiagonal i => (X p.1.1) ⊗ (Y p.1.2))

/-- The tensor product of morphisms between graded objects is the diagonal map
consisting of tensor products of components. -/
def tensorHom {W X Y Z : GradedObject ℕ V} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj W Y ⟶ tensorObj X Z :=
  fun _ => biproduct.map fun p => f p.1.1 ⊗ g p.1.2

/-- The tensor unit in graded `V`-objects is the tensor unit in `V`, supported in grading 0. -/
def tensorUnit : GradedObject ℕ V
| 0 => 𝟙_ V
| _ + 1 => 0

/-- The left unitor for graded objects. -/
@[simps!]
def leftUnitor (X : GradedObject ℕ V) : tensorObj tensorUnit X ≅ X :=
  GradedObject.mkIso fun i =>
    { hom :=
        biproduct.π (fun p : antidiagonal i => (tensorUnit p.1.1) ⊗ (X p.1.2)) ⟨⟨0, i⟩, by simp⟩ ≫
          (λ_ (X i)).hom
      inv := (λ_ (X i)).inv ≫
        biproduct.ι (fun p : antidiagonal i => (tensorUnit p.1.1) ⊗ (X p.1.2)) ⟨⟨0, i⟩, by simp⟩
      hom_inv_id := by
        dsimp [tensorObj]
        ext j j'
        simp [biproduct.ι_π, biproduct.ι_π_assoc]
        split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ <;> (try subst h₁) <;> (try subst h₇) <;> simp_all
        rcases j' with ⟨⟨a, b⟩, w⟩
        simp at w
        subst w
        simp at h₁
        symm
        apply IsZero.eq_zero_of_src
        apply (IsZero.iff_id_eq_zero _).mpr
        match a, h₁ with
        | a + 1, _ => simp [tensorUnit, ← MonoidalCategory.tensor_id]
      inv_hom_id := by simp }

/-- The right unitor for graded objects. -/
@[simps!]
def rightUnitor (X : GradedObject ℕ V) : tensorObj X tensorUnit ≅ X :=
  GradedObject.mkIso fun i =>
    { hom :=
        biproduct.π (fun p : antidiagonal i => (X p.1.1) ⊗ (tensorUnit p.1.2)) ⟨⟨i, 0⟩, by simp⟩ ≫
          (ρ_ (X i)).hom
      inv := (ρ_ (X i)).inv ≫
        biproduct.ι (fun p : antidiagonal i => (X p.1.1) ⊗ (tensorUnit p.1.2)) ⟨⟨i, 0⟩, by simp⟩
      hom_inv_id := by
        dsimp [tensorObj]
        ext j j'
        simp [biproduct.ι_π, biproduct.ι_π_assoc]
        split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ <;> (try subst h₁) <;> (try subst h₇) <;> simp_all
        rcases j' with ⟨⟨a, b⟩, w⟩
        simp at w
        subst w
        simp at h₁
        symm
        apply IsZero.eq_zero_of_src
        apply (IsZero.iff_id_eq_zero _).mpr
        match b, h₁ with
        | b + 1, _ => simp [tensorUnit, ← MonoidalCategory.tensor_id]
      inv_hom_id := by simp }

/-- The 1st step of constructing the associator for graded objects. -/
def associator_distributor (X Y Z : GradedObject ℕ V) (i : ℕ) :
    (tensorObj (tensorObj X Y) Z) i ≅
      biproduct (fun p : antidiagonal i =>
        biproduct (fun q : antidiagonal p.1.1 => (X q.1.1 ⊗ Y q.1.2) ⊗ Z p.1.2)) :=
  biproduct.mapIso fun _ => rightDistributor _ _

/-- The 2nd step of constructing the associator for graded objects. -/
def associator_iterated (X Y Z : GradedObject ℕ V) (i : ℕ) :
    biproduct (fun p : antidiagonal i =>
        biproduct (fun q : antidiagonal p.1.1 => (X q.1.1 ⊗ Y q.1.2) ⊗ Z p.1.2))
      ≅ biproduct (fun p : Σ p₁ : antidiagonal i, antidiagonal p₁.1.1 =>
          (X p.2.1.1 ⊗ Y p.2.1.2) ⊗ Z p.1.1.2) :=
  biproductBiproductIso _ _

/-- The 3rd step of constructing the associator for graded objects. -/
def associator_underlying (X Y Z : GradedObject ℕ V) (i : ℕ) :
    biproduct (fun p : Σ p₁ : antidiagonal i, antidiagonal p₁.1.1 =>
        (X p.2.1.1 ⊗ Y p.2.1.2) ⊗ Z p.1.1.2)
    ≅ biproduct (fun p : Σ p₁ : antidiagonal i, antidiagonal p₁.1.1 =>
      X p.2.1.1 ⊗ (Y p.2.1.2 ⊗ Z p.1.1.2)) :=
  biproduct.mapIso fun _ => α_ _ _ _

-- Move this to `Finset.NatAntidiagonal`?
@[simps apply symm_apply]
def associator_equiv :
    (Σ p₁ : antidiagonal i, antidiagonal p₁.1.1) ≃ (Σ p₁ : antidiagonal i, antidiagonal p₁.1.2) :=
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

/-- The 4th step of constructing the associator for graded objects. -/
def associator_whisker_equiv (X Y Z : GradedObject ℕ V) (i : ℕ) :
    biproduct (fun p : Σ p₁ : antidiagonal i, antidiagonal p₁.1.1 =>
      X p.2.1.1 ⊗ (Y p.2.1.2 ⊗ Z p.1.1.2)) ≅
    biproduct (fun p : Σ p₁ : antidiagonal i, antidiagonal p₁.1.2 =>
      X p.1.1.1 ⊗ (Y p.2.1.1 ⊗ Z p.2.1.2)) :=
  biproduct.whisker_equiv associator_equiv fun ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩ => Iso.refl _

/-- The 5th step of constructing the associator for graded objects. -/
def associator_iterated' (X Y Z : GradedObject ℕ V) (i : ℕ) :
    biproduct (fun p : Σ p₁ : antidiagonal i, antidiagonal p₁.1.2 =>
      X p.1.1.1 ⊗ (Y p.2.1.1 ⊗ Z p.2.1.2)) ≅
    biproduct (fun p : antidiagonal i =>
      biproduct (fun q : antidiagonal p.1.2 => X p.1.1 ⊗ (Y q.1.1 ⊗ Z q.1.2))) :=
  (biproductBiproductIso
    (fun p : antidiagonal i => antidiagonal p.1.2)
    (fun (p : antidiagonal i) (q : antidiagonal p.1.2) => X p.1.1 ⊗ (Y q.1.1 ⊗ Z q.1.2))).symm

/-- The 6th step of constructing the associator for graded objects. -/
def associator_distributor' (X Y Z : GradedObject ℕ V) (i : ℕ) :
    biproduct (fun p : antidiagonal i =>
      biproduct (fun q : antidiagonal p.1.2 => X p.1.1 ⊗ (Y q.1.1 ⊗ Z q.1.2))) ≅
      (tensorObj X (tensorObj Y Z)) i :=
  biproduct.mapIso fun _ => (leftDistributor _ _).symm

/-- The associator for graded objects. -/
def associator (X Y Z : GradedObject ℕ V) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  GradedObject.mkIso (fun i =>
    associator_distributor X Y Z i ≪≫ associator_iterated X Y Z i ≪≫
      associator_underlying X Y Z i ≪≫ associator_whisker_equiv X Y Z i ≪≫
      associator_iterated' X Y Z i ≪≫ associator_distributor' X Y Z i)

/--
The inclusion of the tensor product of the components of two graded objects
into a component of their tensor product.

The construction includes as a hypothesis that the gradings sum appropriately,
to avoid dependent type theory difficulties.
-/
def ιTensorObj (X Y : GradedObject ℕ V) (p q n : ℕ) (h : p + q = n) :
    X p ⊗ Y q ⟶ tensorObj X Y n :=
  biproduct.ι (fun p : antidiagonal n => (X p.1.1) ⊗ (Y p.1.2))
    ⟨⟨p, q⟩, by simpa using h⟩

@[reassoc (attr := simp)]
lemma ιTensorObj_comp_tensorHom {X Y X' Y' : GradedObject ℕ V}
    (f : X ⟶ X') (g : Y ⟶ Y') (p q n : ℕ) (h : p + q = n) :
    ιTensorObj X Y p q n h ≫ tensorHom f g n =
      (f p ⊗ g q) ≫ ιTensorObj X' Y' p q n h:= by
  dsimp [ιTensorObj, tensorHom]
  apply biproduct.ι_map

@[ext]
lemma tensorObj_ext (X Y : GradedObject ℕ V) (n : ℕ) {Z : V}
    (f₁ f₂ : tensorObj X Y n ⟶ Z)
    (h : ∀ (p q : ℕ) (h : p + q = n), ιTensorObj X Y p q n h ≫ f₁ = ιTensorObj X Y p q n h ≫ f₂) :
    f₁ = f₂ := by
  apply biproduct.hom_ext'
  rintro ⟨⟨p, q⟩, hpq⟩
  simp only [Finset.Nat.mem_antidiagonal] at hpq
  exact h p q hpq

lemma tensorObj_rightTensor_ext (X Y : GradedObject ℕ V) (n : ℕ) (T : V) {Z : V}
    (f₁ f₂ : tensorObj X Y n ⊗ T ⟶ Z)
    (h : ∀ (p q : ℕ)
    (h : p + q = n), (ιTensorObj X Y p q n h ⊗ 𝟙 T) ≫ f₁ = (ιTensorObj X Y p q n h ⊗ 𝟙 T) ≫ f₂) :
    f₁ = f₂ := by
  apply rightDistributor_ext_left
  rintro ⟨⟨p, q⟩, hpq⟩
  simp only [Finset.Nat.mem_antidiagonal] at hpq
  exact h p q hpq

lemma tensorObj_leftTensor_ext (X Y : GradedObject ℕ V) (n : ℕ) (T : V) {Z : V}
    (f₁ f₂ : T ⊗ tensorObj X Y n ⟶ Z)
    (h : ∀ (p q : ℕ)
    (h : p + q = n), (𝟙 T ⊗ ιTensorObj X Y p q n h) ≫ f₁ = (𝟙 T ⊗ ιTensorObj X Y p q n h) ≫ f₂) :
    f₁ = f₂ := by
  apply leftDistributor_ext_left
  rintro ⟨⟨p, q⟩, hpq⟩
  simp only [Finset.Nat.mem_antidiagonal] at hpq
  exact h p q hpq

lemma tensorObj_rightTensor_rightTensor_ext (X Y : GradedObject ℕ V) (n : ℕ) (T₁ T₂ : V) {Z : V}
    (f₁ f₂ : (tensorObj X Y n ⊗ T₁) ⊗ T₂ ⟶ Z)
    (h : ∀ (p q : ℕ)
    (h : p + q = n), ((ιTensorObj X Y p q n h ⊗ 𝟙 T₁) ⊗ 𝟙 T₂) ≫ f₁ =
      ((ιTensorObj X Y p q n h ⊗ 𝟙 T₁) ⊗ 𝟙 T₂) ≫ f₂) :
    f₁ = f₂ := by
  rw [← cancel_epi (α_ _ _ _).inv]
  apply tensorObj_rightTensor_ext
  intro p q hpq
  simpa only [MonoidalCategory.associator_conjugation, MonoidalCategory.tensor_id,
    assoc, Iso.cancel_iso_hom_left] using h p q hpq

/--
The inclusion of the (left associated) tensor product of the components of three graded objects
into a component of their (left associated) tensor product.

The construction includes as a hypothesis that the gradings sum appropriately,
to avoid dependent type theory difficulties.
-/
def ιTensorObj₃ (X₁ X₂ X₃ : GradedObject ℕ V) (p₁ p₂ p₃ n : ℕ) (h : p₁ + p₂ + p₃ = n) :
    (X₁ p₁ ⊗ X₂ p₂) ⊗ X₃ p₃ ⟶ tensorObj (tensorObj X₁ X₂) X₃ n :=
  ((ιTensorObj X₁ X₂ p₁ p₂ (p₁ + p₂) rfl) ⊗ 𝟙 (X₃ p₃)) ≫
    ιTensorObj (tensorObj X₁ X₂) X₃ (p₁ + p₂) p₃ n h

lemma ιTensorObj₃_eq (X₁ X₂ X₃ : GradedObject ℕ V) (p₁ p₂ p₃ n : ℕ) (h : p₁ + p₂ + p₃ = n)
    (p₁₂ : ℕ) (h₁₂ : p₁ + p₂ = p₁₂) :
    ιTensorObj₃ X₁ X₂ X₃ p₁ p₂ p₃ n h =
      (ιTensorObj X₁ X₂ p₁ p₂ p₁₂ h₁₂ ⊗ 𝟙 (X₃ p₃)) ≫
      ιTensorObj (tensorObj X₁ X₂) X₃ p₁₂ p₃ n (by rw [←h₁₂, h]) := by
  subst h₁₂
  rfl

lemma ιTensorObj₃_comp_tensorHom {X₁ X₂ X₃ Y Z : GradedObject ℕ V}
    (f₁ : tensorObj X₁ X₂ ⟶ Y) (f₂ : X₃ ⟶ Z)
    (p₁ p₂ p₃ n : ℕ) (h : p₁ + p₂ + p₃ = n) (h₁₂ : p₁ + p₂ = p₁₂) :
    ιTensorObj₃ X₁ X₂ X₃ p₁ p₂ p₃ n h ≫ tensorHom f₁ f₂ n =
      (ιTensorObj X₁ X₂ p₁ p₂ p₁₂ h₁₂ ≫ f₁ p₁₂ ⊗ f₂ p₃) ≫
        ιTensorObj Y Z p₁₂ p₃ n (by rw [← h₁₂, h]) := by
  rw [ιTensorObj₃_eq, assoc, ιTensorObj_comp_tensorHom, ← assoc, ← MonoidalCategory.tensor_comp,
    id_comp]

@[reassoc (attr := simp)]
lemma ιTensorObj₃_comp_tensorHom_tensorHom {X₁ Y₁ X₂ Y₂ X₃ Y₃ : GradedObject ℕ V}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) (p₁ p₂ p₃ n : ℕ) (h : p₁ + p₂ + p₃ = n) :
    ιTensorObj₃ X₁ X₂ X₃ p₁ p₂ p₃ n h ≫ tensorHom (tensorHom f₁ f₂) f₃ n =
      ((f₁ p₁ ⊗ f₂ p₂) ⊗ f₃ p₃) ≫ ιTensorObj₃ Y₁ Y₂ Y₃ p₁ p₂ p₃ n h := by
  dsimp [ιTensorObj₃]
  simp only [assoc, ιTensorObj_comp_tensorHom]
  simp only [← assoc]
  conv_lhs => simp only [← MonoidalCategory.tensor_comp]
  simp only [id_comp]
  simp only [ιTensorObj_comp_tensorHom]
  conv_rhs => simp only [← MonoidalCategory.tensor_comp]
  simp

/--
The inclusion of the (left associated) tensor product of the components of three graded objects
into a component of their (right associated) tensor product.

The construction includes as a hypothesis that the gradings sum appropriately,
to avoid dependent type theory difficulties.
-/
def ιTensorObj₃' (X₁ X₂ X₃ : GradedObject ℕ V) (p₁ p₂ p₃ n : ℕ) (h : p₁ + p₂ + p₃ = n) :
    (X₁ p₁ ⊗ X₂ p₂) ⊗ X₃ p₃ ⟶ tensorObj X₁ (tensorObj X₂ X₃) n :=
  (α_ _ _ _).hom ≫ (𝟙 (X₁ p₁) ⊗ ιTensorObj X₂ X₃ p₂ p₃ (p₂ + p₃) rfl) ≫
    ιTensorObj X₁ (tensorObj X₂ X₃) p₁ (p₂ + p₃) n (by rw [← add_assoc, h])

lemma ιTensorObj₃'_eq (X₁ X₂ X₃ : GradedObject ℕ V) (p₁ p₂ p₃ n : ℕ) (h : p₁ + p₂ + p₃ = n)
    (p₂₃ : ℕ) (h₂₃ : p₂ + p₃ = p₂₃) :
    ιTensorObj₃' X₁ X₂ X₃ p₁ p₂ p₃ n h =
      (α_ _ _ _).hom ≫ (𝟙 (X₁ p₁) ⊗ ιTensorObj X₂ X₃ p₂ p₃ p₂₃ h₂₃) ≫
      ιTensorObj X₁ (tensorObj X₂ X₃) p₁ p₂₃ n (by rw [← h₂₃, ← add_assoc, h]) := by
  subst h₂₃
  rfl

lemma ιTensorObj₃'_comp_tensorHom {X₁ X₂ X₃ Y Z : GradedObject ℕ V}
    (f₁ : X₁ ⟶ Y) (f₂ : tensorObj X₂ X₃ ⟶ Z)
    (p₁ p₂ p₃ n : ℕ) (h : p₁ + p₂ + p₃ = n) (h₂₃ : p₂ + p₃ = p₂₃) :
    ιTensorObj₃' X₁ X₂ X₃ p₁ p₂ p₃ n h ≫ tensorHom f₁ f₂ n =
      (α_ _ _ _).hom ≫ (f₁ p₁ ⊗ ιTensorObj X₂ X₃ p₂ p₃ p₂₃ h₂₃ ≫ f₂ p₂₃) ≫
        ιTensorObj Y Z p₁ p₂₃ n (by rw [← h₂₃, ← add_assoc, h]) := by
  rw [ιTensorObj₃'_eq]
  simp only [assoc, ιTensorObj_comp_tensorHom, Iso.cancel_iso_hom_left]
  rw [← MonoidalCategory.tensor_comp_assoc, id_comp]

@[reassoc (attr := simp)]
lemma ιTensorObj₃'_comp_tensorHom_tensorHom {X₁ Y₁ X₂ Y₂ X₃ Y₃ : GradedObject ℕ V}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) (p₁ p₂ p₃ n : ℕ) (h : p₁ + p₂ + p₃ = n) :
    ιTensorObj₃' X₁ X₂ X₃ p₁ p₂ p₃ n h ≫ tensorHom f₁ (tensorHom f₂ f₃) n =
      ((f₁ p₁ ⊗ f₂ p₂) ⊗ f₃ p₃) ≫ ιTensorObj₃' Y₁ Y₂ Y₃ p₁ p₂ p₃ n h := by
  dsimp [ιTensorObj₃']
  simp only [MonoidalCategory.associator_naturality_assoc]
  simp only [assoc, Iso.cancel_iso_hom_left]
  simp only [ιTensorObj_comp_tensorHom]
  simp only [← assoc]
  conv_lhs => simp only [← MonoidalCategory.tensor_comp]
  simp only [id_comp]
  simp only [ιTensorObj_comp_tensorHom]
  conv_rhs => simp only [← MonoidalCategory.tensor_comp]
  simp

@[ext]
lemma tensorObj₃_ext (X₁ X₂ X₃ : GradedObject ℕ V) (n : ℕ) {Z : V}
    (f₁ f₂ : tensorObj (tensorObj X₁ X₂) X₃ n ⟶ Z)
    (h : ∀ (p₁ p₂ p₃ : ℕ) (h : p₁ + p₂ + p₃ = n),
      ιTensorObj₃ X₁ X₂ X₃ p₁ p₂ p₃ n h ≫ f₁ = ιTensorObj₃ X₁ X₂ X₃ p₁ p₂ p₃ n h ≫ f₂) :
    f₁ = f₂ := by
  apply tensorObj_ext
  intro p₁₂ p₃ h₁₂₃
  apply tensorObj_rightTensor_ext
  intro p₁ p₂ h₁₂
  simpa only [ιTensorObj₃_eq X₁ X₂ X₃ p₁ p₂ p₃ n (by rw [h₁₂, h₁₂₃]) p₁₂ h₁₂,
    assoc] using h p₁ p₂ p₃ (by rw [h₁₂, h₁₂₃])

lemma tensorObj₃_rightTensor_ext (X₁ X₂ X₃ : GradedObject ℕ V) (n : ℕ) (T : V) {Z : V}
    (f₁ f₂ : tensorObj (tensorObj X₁ X₂) X₃ n ⊗ T ⟶ Z)
    (h : ∀ (p₁ p₂ p₃ : ℕ) (h : p₁ + p₂ + p₃ = n),
      (ιTensorObj₃ X₁ X₂ X₃ p₁ p₂ p₃ n h ⊗ 𝟙 T) ≫ f₁ =
      (ιTensorObj₃ X₁ X₂ X₃ p₁ p₂ p₃ n h ⊗ 𝟙 T) ≫ f₂) :
    f₁ = f₂ := by
  apply tensorObj_rightTensor_ext
  intro p₁₂ p₃ h₁₂₃
  apply tensorObj_rightTensor_rightTensor_ext
  intro p₁ p₂ h₁₂
  simpa only [ιTensorObj₃_eq X₁ X₂ X₃ p₁ p₂ p₃ n (by rw [h₁₂, h₁₂₃]) p₁₂ h₁₂,
    MonoidalCategory.associator_conjugation, MonoidalCategory.tensor_id, assoc,
    Iso.cancel_iso_hom_left, MonoidalCategory.comp_tensor_id] using h p₁ p₂ p₃ (by rw [h₁₂, h₁₂₃])

-- This increase to maxHeartbeats is needed during CI, when `X says Y` is reverified.
set_option maxHeartbeats 300000 in
@[reassoc (attr := simp)]
lemma ιTensorObj₃_comp_associator_hom (X₁ X₂ X₃ : GradedObject ℕ V)
    (p₁ p₂ p₃ n : ℕ) (h : p₁ + p₂ + p₃ = n) :
    ιTensorObj₃ X₁ X₂ X₃ p₁ p₂ p₃ n h ≫ (associator X₁ X₂ X₃).hom n =
      ιTensorObj₃' X₁ X₂ X₃ p₁ p₂ p₃ n h := by
  -- We progressively unfold the definition of `associator`, starting at its leftmost factors,
  -- to avoid having too large a goal.
  -- The proof is mostly just by `simp`.
  have helper : ∀ {α : Type} {β : α → Type} (p : Σ a : α, β a) (a : α) (b : a = p.1 → β p.1),
    (∃ hp : a = p.1, b hp = p.2) ↔ ∃ hp : a = p.1, ⟨a, cast (congrArg β hp.symm) (b hp)⟩ = p := by
    intros α β p a b
    constructor
    · rintro ⟨rfl, w⟩
      use rfl
      simp [w]
    · rintro ⟨rfl, w⟩
      use rfl
      cases p
      simp_all
  dsimp [associator]
  dsimp [ιTensorObj₃, ιTensorObj₃', ιTensorObj, associator]
  dsimp [associator_distributor, associator_iterated]
  simp? says simp only [assoc, biproduct.ι_map_assoc, biproduct.ι_comp_lift_assoc, ne_eq,
      biproduct_ι_comp_rightDistributor_hom_assoc]
  simp? [biproduct.ι_π_biproduct_assoc, dite_comp, comp_dite] says
    simp only [ne_eq, biproduct.ι_π_biproduct_assoc, biproduct.iterated_reindex, dite_comp,
      biproduct.whisker_equiv_hom_comp_π, eqToIso.inv, eqToHom_trans, zero_comp, comp_dite,
      comp_zero]
  simp? [biproduct.ι_π_assoc, dite_comp, dite_dite, Equiv.eq_symm_apply] says
    simp only [ne_eq, Equiv.eq_symm_apply, biproduct.ι_π_assoc, dite_comp, eqToHom_trans,
      zero_comp, dite_dite]
  simp? [Equiv.transport, helper] says
    simp only [Equiv.transport, Equiv.cast_apply, Finset.mem_val, mem_antidiagonal, helper,
      cast_cast, cast_eq, exists_prop, Sigma.eq_fst_and_eq_iff]
  conv in biproduct.lift _ =>
    -- Unfortunately `simp` does not successfully apply `biproduct.lift_dite` here,
    -- presumably because of unification difficulties.
    -- We use `convert` to provide some encouragement.
    tactic => convert biproduct.lift_dite _
  simp? says simp only [eqToHom_refl, id_comp]
  dsimp only [associator_underlying]
  simp? says simp only [biproduct.mapIso_hom, biproduct.ι_map_assoc, Iso.cancel_iso_hom_left]
  dsimp only [associator_whisker_equiv]
  simp? says simp only [associator_equiv_apply, biproduct.ι_comp_whisker_equiv_hom_assoc,
    Iso.refl_inv, id_comp]
  dsimp only [associator_iterated']
  simp? says simp only [Iso.symm_hom, biproductBiproductIso_inv, biproduct.ι_comp_lift_assoc,
    biproduct.ι_comp_lift, ne_eq, Sigma.mk.inj_iff, not_and]
  simp? [biproduct.ι_π] says simp only [ne_eq, Sigma.mk.inj_iff, not_and, biproduct.ι_π]
  simp only [Sigma.ext_iff']
  simp only [dite_exists]
  simp? says simp only [Finset.mem_val, mem_antidiagonal, biproduct.lift_dite_irrel,
    biproduct.lift_zero]
  conv in biproduct.lift _ =>
    -- As above, `simp` can not apply `biproduct.lift_dite` here.
    tactic => convert biproduct.lift_dite _
  conv in biproduct.lift _ =>
    tactic => convert biproduct.lift_dite _
  simp? says simp only [cast_eq, eqToHom_refl, id_comp, assoc]
  dsimp only [associator_distributor']
  simp? says simp only [biproduct.mapIso_hom, Iso.symm_hom, biproduct.ι_map,
    biproduct_ι_comp_leftDistributor_inv_assoc]

@[reassoc (attr := simp)]
lemma ιTensorObj₃'_comp_associator_inv (X₁ X₂ X₃ : GradedObject ℕ V)
    (p₁ p₂ p₃ n : ℕ) (h : p₁ + p₂ + p₃ = n) :
    ιTensorObj₃' X₁ X₂ X₃ p₁ p₂ p₃ n h ≫ (associator X₁ X₂ X₃).inv n =
      ιTensorObj₃ X₁ X₂ X₃ p₁ p₂ p₃ n h := by
  rw [← cancel_mono ((GradedObject.eval n).map (associator X₁ X₂ X₃).hom), assoc]
  change _ ≫ (GradedObject.eval n).map (associator X₁ X₂ X₃).inv ≫ _ = _
  rw [← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, comp_id]
  exact (ιTensorObj₃_comp_associator_hom X₁ X₂ X₃ p₁ p₂ p₃ n h).symm

/--
The inclusion of the (left associated) tensor product of the components of four graded objects
into a component of their (right associated) tensor product.

The construction includes as a hypothesis that the gradings sum appropriately,
to avoid dependent type theory difficulties.
-/
def ιTensorObj₄ (X₁ X₂ X₃ X₄ : GradedObject ℕ V) (p₁ p₂ p₃ p₄ n : ℕ)
    (h : p₁ + p₂ + p₃ + p₄ = n) :
    ((X₁ p₁ ⊗ X₂ p₂) ⊗ X₃ p₃) ⊗ X₄ p₄ ⟶ tensorObj (tensorObj (tensorObj X₁ X₂) X₃) X₄ n :=
  (ιTensorObj₃ X₁ X₂ X₃ p₁ p₂ p₃ (p₁ + p₂ + p₃) rfl ⊗ 𝟙 (X₄ p₄)) ≫
    ιTensorObj _ X₄ (p₁ + p₂ + p₃) p₄ n h

lemma ιTensorObj₄_eq (X₁ X₂ X₃ X₄ : GradedObject ℕ V) (p₁ p₂ p₃ p₄ n : ℕ)
    (h : p₁ + p₂ + p₃ + p₄ = n) (p₁₂₃ : ℕ) (h₁₂₃ : p₁ + p₂ + p₃ = p₁₂₃) :
  ιTensorObj₄ X₁ X₂ X₃ X₄ p₁ p₂ p₃ p₄ n h =
  (ιTensorObj₃ X₁ X₂ X₃ p₁ p₂ p₃ p₁₂₃ h₁₂₃ ⊗ 𝟙 (X₄ p₄)) ≫
    ιTensorObj _ X₄ p₁₂₃ p₄ n (by rw [← h₁₂₃, h]) := by
  subst h₁₂₃
  rfl

lemma ιTensorObj₄_eq' (X₁ X₂ X₃ X₄ : GradedObject ℕ V) (p₁ p₂ p₃ p₄ n : ℕ)
    (h : p₁ + p₂ + p₃ + p₄ = n) (p₁₂ : ℕ) (h₁₂ : p₁ + p₂ = p₁₂) :
  ιTensorObj₄ X₁ X₂ X₃ X₄ p₁ p₂ p₃ p₄ n h =
    ((ιTensorObj X₁ X₂ p₁ p₂ p₁₂ h₁₂ ⊗ 𝟙 (X₃ p₃)) ⊗ 𝟙 (X₄ p₄)) ≫
      ιTensorObj₃ (tensorObj X₁ X₂) X₃ X₄ p₁₂ p₃ p₄ n (by rw [← h₁₂, h]) := by
  rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ p₁ p₂ p₃ p₄ n h (p₁ + p₂ + p₃) rfl,
    ιTensorObj₃_eq X₁ X₂ X₃ p₁ p₂ p₃ (p₁ + p₂ + p₃) rfl p₁₂ h₁₂,
    ιTensorObj₃_eq (tensorObj X₁ X₂) X₃ X₄ p₁₂ p₃ p₄ n (by rw [← h₁₂, h])
      (p₁ + p₂ + p₃) (by rw [← h₁₂])]
  simp only [MonoidalCategory.comp_tensor_id, MonoidalCategory.associator_conjugation,
    MonoidalCategory.tensor_id, assoc]

@[ext]
lemma tensorObj₄_ext (X₁ X₂ X₃ X₄ : GradedObject ℕ V) (n : ℕ) {Z : V}
    (f₁ f₂ : tensorObj (tensorObj (tensorObj X₁ X₂) X₃) X₄ n ⟶ Z)
    (h : ∀ (p₁ p₂ p₃ p₄ : ℕ) (h : p₁ + p₂ + p₃ + p₄ = n),
      ιTensorObj₄ X₁ X₂ X₃ X₄ p₁ p₂ p₃ p₄ n h ≫ f₁ = ιTensorObj₄ X₁ X₂ X₃ X₄ p₁ p₂ p₃ p₄ n h ≫ f₂) :
    f₁ = f₂ := by
  apply tensorObj_ext
  intro p₁₂₃ p₄ h₁₂₃
  apply tensorObj₃_rightTensor_ext
  intro p₁ p₂ p₃ h₁₂₃'
  simpa only [ιTensorObj₄_eq X₁ X₂ X₃ X₄ p₁ p₂ p₃ p₄ n (by rw [h₁₂₃', h₁₂₃]) p₁₂₃ h₁₂₃', assoc]
    using h p₁ p₂ p₃ p₄ (by rw [h₁₂₃', h₁₂₃])

@[reassoc]
lemma pentagon_aux₁ (X₁ X₂ X₃ X₄ : GradedObject ℕ V) (p₁ p₂ p₃ p₄ n : ℕ)
    (h : p₁ + p₂ + p₃ + p₄ = n) (p₁₂ : ℕ) (h₁₂ : p₁ + p₂ = p₁₂) (p₃₄ : ℕ) (h₃₄ : p₃ + p₄ = p₃₄) :
    ((ιTensorObj X₁ X₂ p₁ p₂ p₁₂ h₁₂ ⊗ 𝟙 (X₃ p₃)) ⊗ 𝟙 (X₄ p₄)) ≫
      ιTensorObj₃' (tensorObj X₁ X₂) X₃ X₄ p₁₂ p₃ p₄ n (by rw [← h₁₂, h]) =
      (α_ _ _ _).hom ≫ (𝟙 _ ⊗ ιTensorObj X₃ X₄ p₃ p₄ p₃₄ h₃₄) ≫
        ιTensorObj₃ X₁ X₂ (tensorObj X₃ X₄) p₁ p₂ p₃₄ n (by rw [← h₃₄, ← add_assoc, h]) := by
  rw [ιTensorObj₃'_eq (tensorObj X₁ X₂) X₃ X₄ p₁₂ p₃ p₄ n (by rw [← h₁₂, h]) p₃₄ h₃₄,
    ιTensorObj₃_eq X₁ X₂ (tensorObj X₃ X₄) p₁ p₂ p₃₄ n (by rw [← h₃₄, ← add_assoc, h]) p₁₂ h₁₂]
  simp only [MonoidalCategory.associator_conjugation, MonoidalCategory.tensor_id, assoc,
    Iso.inv_hom_id_assoc, MonoidalCategory.tensor_id_comp_id_tensor_assoc,
    MonoidalCategory.id_tensor_comp_tensor_id_assoc]

lemma pentagon_aux₂ (X₁ X₂ X₃ X₄ : GradedObject ℕ V) (p₁ p₂ p₃ p₄ n : ℕ)
    (h : p₁ + p₂ + p₃ + p₄ = n) (p₁₂₃ : ℕ) (h₁₂₃ : p₁ + p₂ + p₃ = p₁₂₃) (p₂₃ : ℕ)
    (h₂₃ : p₂ + p₃ = p₂₃):
    (ιTensorObj₃' X₁ X₂ X₃ p₁ p₂ p₃ p₁₂₃ h₁₂₃ ⊗ 𝟙 (X₄ p₄)) ≫
      ιTensorObj (tensorObj X₁ (tensorObj X₂ X₃)) X₄ p₁₂₃ p₄ n (by rw [← h₁₂₃, h]) =
    (((α_ _ _ _).hom ≫ (𝟙 (X₁ p₁) ⊗ ιTensorObj X₂ X₃ p₂ p₃ p₂₃ h₂₃)) ⊗ (𝟙 (X₄ p₄))) ≫
      ιTensorObj₃ X₁ (tensorObj X₂ X₃) X₄ p₁ p₂₃ p₄ n (by rw [← h₂₃, ← add_assoc, h]) := by
  rw [ιTensorObj₃'_eq X₁ X₂ X₃ p₁ p₂ p₃ p₁₂₃ h₁₂₃ p₂₃ h₂₃,
    ιTensorObj₃_eq X₁ (tensorObj X₂ X₃) X₄ p₁ p₂₃ p₄ n
      (by rw [← h₂₃, ← add_assoc, h]) p₁₂₃ (by rw [← h₂₃, ← add_assoc, h₁₂₃])]
  simp only [MonoidalCategory.comp_tensor_id, MonoidalCategory.associator_conjugation, assoc]

@[reassoc]
lemma pentagon_aux₃ (X₁ X₂ X₃ X₄ : GradedObject ℕ V) (p₁ p₂ p₃ p₄ n : ℕ)
    (h : p₁ + p₂ + p₃ + p₄ = n) (p₂₃ : ℕ) (h₂₃ : p₂ + p₃ = p₂₃) :
    ιTensorObj₄ X₁ X₂ X₃ X₄ p₁ p₂ p₃ p₄ n h ≫
      tensorHom (associator X₁ X₂ X₃).hom (𝟙 X₄) n =
        (((α_ _ _ _).hom ≫ ((𝟙 (X₁ p₁)) ⊗ ιTensorObj X₂ X₃ p₂ p₃ p₂₃ h₂₃)) ⊗ 𝟙 (X₄ p₄)) ≫
          ιTensorObj₃ X₁ (tensorObj X₂ X₃) X₄ p₁ p₂₃ p₄ n (by rw [← h₂₃, ← add_assoc, h]) := by
  rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ p₁ p₂ p₃ p₄ n h (p₁ + p₂ + p₃) rfl,
    assoc, ιTensorObj_comp_tensorHom]
  dsimp
  rw [← MonoidalCategory.comp_tensor_id_assoc,
    ιTensorObj₃_comp_associator_hom X₁ X₂ X₃ p₁ p₂ p₃ (p₁ + p₂ + p₃) rfl,
    pentagon_aux₂ X₁ X₂ X₃ X₄ p₁ p₂ p₃ p₄ n h (p₁ + p₂ + p₃) rfl p₂₃ h₂₃]

lemma pentagon_aux₄ (X₁ X₂ X₃ X₄ : GradedObject ℕ V) (p₁ p₂ p₃ p₄ n : ℕ)
    (h : p₁ + p₂ + p₃ + p₄ = n) (p₃₄ : ℕ) (h₃₄ : p₃ + p₄ = p₃₄)
    (p₂₃₄ : ℕ) (h₂₃₄ : p₂ + p₃ + p₄ = p₂₃₄) :
    (𝟙 (X₁ p₁ ⊗ X₂ p₂) ⊗ ιTensorObj X₃ X₄ p₃ p₄ p₃₄ h₃₄) ≫
    ιTensorObj₃' X₁ X₂ (tensorObj X₃ X₄) p₁ p₂ p₃₄ n (by rw [← h₃₄, ← add_assoc, h]) =
      (α_ _ _ _).hom ≫ (𝟙 (X₁ p₁) ⊗ (α_ _ _ _).inv) ≫
        (𝟙 (X₁ p₁) ⊗ ιTensorObj₃ X₂ X₃ X₄ p₂ p₃ p₄ p₂₃₄ h₂₃₄) ≫
        ιTensorObj X₁ (tensorObj (tensorObj X₂ X₃) X₄) p₁ p₂₃₄ n
        (by rw [← h₂₃₄, ← add_assoc, ← add_assoc, h]) ≫
        tensorHom (𝟙 X₁) (associator X₂ X₃ X₄).hom n := by
  rw [ιTensorObj_comp_tensorHom, ← MonoidalCategory.id_tensor_comp_assoc]
  dsimp
  rw [← MonoidalCategory.id_tensor_comp_assoc, assoc,
    ιTensorObj₃_comp_associator_hom X₂ X₃ X₄ p₂ p₃ p₄ p₂₃₄ h₂₃₄,
    ιTensorObj₃'_eq X₂ X₃ X₄ p₂ p₃ p₄ p₂₃₄ h₂₃₄ p₃₄ h₃₄,
    ιTensorObj₃'_eq X₁ X₂ (tensorObj X₃ X₄) p₁ p₂ p₃₄ n
    (by rw [← h₃₄, ← add_assoc, h]) p₂₃₄ (by rw [← h₂₃₄, ← h₃₄, add_assoc]),
    Iso.inv_hom_id_assoc, MonoidalCategory.id_tensor_comp, assoc,
    ← MonoidalCategory.tensor_id, MonoidalCategory.associator_conjugation,
    assoc, assoc, Iso.inv_hom_id_assoc]

lemma ιTensorObj_comp_leftUnitor_zero (X : GradedObject ℕ V) :
    ιTensorObj tensorUnit X 0 p p h ≫ (leftUnitor X).hom p = (λ_ (X p)).hom := by
  simp [ιTensorObj, biproduct.ι_π]

lemma ιTensorObj_comp_leftUnitor_succ (X : GradedObject ℕ V) :
    ιTensorObj tensorUnit X (p₁ + 1) p₂ n h ≫ (leftUnitor X).hom n = 0 :=
  IsZero.eq_zero_of_src (IsZero.tensor_right (isZero_zero _) _) _

lemma ιTensorObj_comp_rightUnitor_zero (X : GradedObject ℕ V) :
    ιTensorObj X tensorUnit p 0 p h ≫ (rightUnitor X).hom p = (ρ_ (X p)).hom := by
  simp [ιTensorObj, biproduct.ι_π]

lemma ιTensorObj_comp_rightUnitor_succ (X : GradedObject ℕ V) :
    ιTensorObj X tensorUnit p₁ (p₂ + 1) n h ≫ (rightUnitor X).hom n = 0 :=
  IsZero.eq_zero_of_src (IsZero.tensor_left _ (isZero_zero _)) _

@[simp]
lemma triangle (X₁ X₂ : GradedObject ℕ V) (p₁ p₂ p₃ n : ℕ) (h : p₁ + p₂ + p₃ = n) :
    ιTensorObj₃' X₁ tensorUnit X₂ p₁ p₂ p₃ n h ≫ tensorHom (𝟙 X₁) (leftUnitor X₂).hom n =
      ιTensorObj₃ X₁ tensorUnit X₂ p₁ p₂ p₃ n h ≫ tensorHom (rightUnitor X₁).hom (𝟙 X₂) n := by
  cases p₂ with
  | zero =>
    rw [ιTensorObj₃_comp_tensorHom, ιTensorObj₃'_comp_tensorHom, ιTensorObj_comp_leftUnitor_zero,
      ιTensorObj_comp_rightUnitor_zero]
    dsimp [tensorUnit]
    rw [← assoc, CategoryTheory.MonoidalCategory.triangle]
    all_goals simp
  | succ p₂ =>
    rw [ιTensorObj₃_comp_tensorHom, ιTensorObj₃'_comp_tensorHom, ιTensorObj_comp_leftUnitor_succ,
      ιTensorObj_comp_rightUnitor_succ]
    · simp
    all_goals (try rfl)

end MonoidalCategory

open MonoidalCategory

instance : MonoidalCategory (GradedObject ℕ V) where
  tensorObj := tensorObj
  tensorHom := tensorHom
  tensorUnit' := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  leftUnitor_naturality f₁ := by
    ext
    simp only [categoryOfGradedObjects_comp, ιTensorObj_comp_tensorHom_assoc]
    simp [ιTensorObj, biproduct.ι_π_assoc]
    split_ifs with h
    · rcases h with ⟨rfl, rfl⟩
      simp [MonoidalCategory.tensorUnit]
    · simp
  rightUnitor_naturality f₁ := by
    ext n
    simp only [categoryOfGradedObjects_comp, ιTensorObj_comp_tensorHom_assoc]
    simp [ιTensorObj, biproduct.ι_π_assoc]
    split_ifs with h
    · rcases h with ⟨rfl, rfl⟩
      simp [MonoidalCategory.tensorUnit]
    · simp
  pentagon X₁ X₂ X₃ X₄ := by
    ext n p₁ p₂ p₃ p₄ h
    dsimp
    have pentagonV := MonoidalCategory.pentagon (X₁ p₁) (X₂ p₂) (X₃ p₃) (X₄ p₄)
    simp only [← cancel_mono ((𝟙 (X₁ p₁) ⊗ (α_ (X₂ p₂) (X₃ p₃) (X₄ p₄)).inv)), assoc,
      ← id_tensor_comp, Iso.hom_inv_id, tensor_id, comp_id] at pentagonV
    -- working on the RHS
    nth_rw 2 [ιTensorObj₄_eq' X₁ X₂ X₃ X₄ p₁ p₂ p₃ p₄ n h (p₁ + p₂) rfl]
    rw [assoc, ιTensorObj₃_comp_associator_hom_assoc (tensorObj X₁ X₂) X₃ X₄ (p₁ + p₂) p₃ p₄ n h]
    have eq₁ := ((α_ _ _ _).hom ≫ (𝟙 _ ⊗ ιTensorObj X₃ X₄ p₃ p₄ (p₃ + p₄) rfl)) ≫=
      ιTensorObj₃_comp_associator_hom X₁ X₂ (tensorObj X₃ X₄) p₁ p₂ (p₃ + p₄) n
        (by rw [← add_assoc, h])
    simp only [assoc] at eq₁
    rw [pentagon_aux₁_assoc X₁ X₂ X₃ X₄ p₁ p₂ p₃ p₄ n h (p₁ + p₂) rfl (p₃ + p₄) rfl, eq₁]
    clear eq₁
    -- working on the LHS
    rw [pentagon_aux₃_assoc X₁ X₂ X₃ X₄ p₁ p₂ p₃ p₄ n h (p₂ + p₃) rfl,
      ιTensorObj₃_comp_associator_hom_assoc, comp_tensor_id,
      associator_conjugation, assoc, assoc, assoc, reassoc_of% pentagonV]
    clear pentagonV
    rw [pentagon_aux₄ X₁ X₂ X₃ X₄ p₁ p₂ p₃ p₄ n h (p₃ + p₄) rfl (p₂ + p₃ + p₄) rfl,
      ιTensorObj₃'_eq X₁ (tensorObj X₂ X₃) X₄ p₁ (p₂ + p₃) p₄ n
        (by rw [← add_assoc, h]) (p₂ + p₃ + p₄) rfl,
      ιTensorObj₃_eq X₂ X₃ X₄ p₂ p₃ p₄ (p₂ + p₃ + p₄) rfl (p₂ + p₃) rfl]
    simp only [assoc, Iso.inv_hom_id_assoc, id_tensor_comp]

end GradedObject
