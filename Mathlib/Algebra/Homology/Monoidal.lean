import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Fintype.Sigma

universe v u

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory

variable {V : Type u} [Category.{v} V] [Preadditive V] [MonoidalCategory V] [MonoidalPreadditive V]
  [HasFiniteBiproducts V]

/--
Construct a morphism between two objects in a family,
either using `eqToHom` if they have equal indices, or zero otherwise.
-/
def idOrZero {β : Type _} [DecidableEq β] (X : β → V) (i j : β) : X i ⟶ X j :=
if h : i = j then
  eqToHom (congrArg X h)
else
  0

lemma idOrZero_ne_zero [DecidableEq β] {X : β → V} (w : idOrZero X i j ≠ 0) : i = j := sorry

namespace ChainComplex

namespace MonoidalCategory

theorem foo [AddCommGroup β] {a b : β} (ha : a + b ≠ 0) : a ≠ 0 ∨ b ≠ 0 := sorry

theorem bar {W X Y Z : V} {f : W ⟶ X} {g : Y ⟶ Z} (h : f ⊗ g ≠ 0) : f ≠ 0 ∧ g ≠ 0 := sorry

theorem qux {X : ChainComplex V ℕ} {i j} (h : X.d i j ≠ 0) : j + 1 = i := sorry

variable (i : ℕ) in
#synth Fintype (Finset.Nat.antidiagonal i)

def tensorObj_X (X Y : ChainComplex V ℕ) (i : ℕ) : V :=
  biproduct (fun p : Finset.Nat.antidiagonal i => (X.X p.1.1) ⊗ (Y.X p.1.2))

def tensorObj_d (X Y : ChainComplex V ℕ) (i j : ℕ) : tensorObj_X X Y i ⟶ tensorObj_X X Y j :=
  biproduct.matrix
    fun p q => X.d p.1.1 q.1.1 ⊗ idOrZero Y.X p.1.2 q.1.2 +
      ((-1 : ℤ)^p.1.1) • (idOrZero X.X p.1.1 q.1.1 ⊗ Y.d p.1.2 q.1.2)

def tensorObj (X Y : ChainComplex V ℕ) : ChainComplex V ℕ where
  X i := tensorObj_X X Y i
  d i j := tensorObj_d X Y i j
  shape i j w := by
    simp only [tensorObj_X, tensorObj_d]
    ext ⟨⟨k₁, k₂⟩, hk⟩ ⟨⟨l₁, l₂⟩, hl⟩
    simp at hk
    subst hk
    simp at hl
    subst hl
    simp
    by_contra h
    replace h := foo h
    rcases h with h | h
    · replace h := bar h
      simp at h
      have h₁ := qux h.1
      have h₂ := idOrZero_ne_zero h.2
      simp at h₂
      subst h₁
      subst h₂
      simp at w
      abel_nf at w
      assumption
    · sorry
  d_comp_d' := sorry

def tensorHom {W X Y Z : ChainComplex V ℕ} (f : W ⟶ X) (g : Y ⟶ Z) :
  tensorObj W Y ⟶ tensorObj X Z where
  f := fun i => biproduct.map fun p => f.f p.1.1 ⊗ g.f p.1.2
  comm' i j w := by
    simp [tensorObj, tensorObj_X, tensorObj_d]
    ext ⟨⟨k₁, k₂⟩, hk⟩ ⟨⟨l₁, l₂⟩, hl⟩
    simp at hk
    subst hk
    simp at hl
    subst hl
    simp
    sorry

def associator₁ (X Y Z : ChainComplex V ℕ) (i : ℕ) :
    (tensorObj (tensorObj X Y) Z).X i ≅ biproduct (fun p : Finset.Nat.antidiagonal i => biproduct (fun q : Finset.Nat.antidiagonal p.1.1 => (X.X q.1.1 ⊗ Y.X q.1.2) ⊗ Z.X p.1.2)) :=
  biproduct.mapIso fun _ => rightDistributor _ _

def associator₂ (X Y Z : ChainComplex V ℕ) (i : ℕ) :
    biproduct (fun p : Finset.Nat.antidiagonal i => biproduct (fun q : Finset.Nat.antidiagonal p.1.1 => (X.X q.1.1 ⊗ Y.X q.1.2) ⊗ Z.X p.1.2))
      ≅ biproduct (fun p : Σ p₁ : Finset.Nat.antidiagonal i, Finset.Nat.antidiagonal p₁.1.1 => (X.X p.2.1.1 ⊗ Y.X p.2.1.2) ⊗ Z.X p.1.1.2) :=
  biproductBiproductIso _ _

def associator₃ (X Y Z : ChainComplex V ℕ) (i : ℕ) :
    biproduct (fun p : Σ p₁ : Finset.Nat.antidiagonal i, Finset.Nat.antidiagonal p₁.1.1 => (X.X p.2.1.1 ⊗ Y.X p.2.1.2) ⊗ Z.X p.1.1.2)
      ≅ biproduct (fun p : Σ p₁ : Finset.Nat.antidiagonal i, Finset.Nat.antidiagonal p₁.1.1 => X.X p.2.1.1 ⊗ (Y.X p.2.1.2 ⊗ Z.X p.1.1.2)) :=
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

def associator₄ (X Y Z : ChainComplex V ℕ) (i : ℕ) :
    biproduct (fun p : Σ p₁ : Finset.Nat.antidiagonal i, Finset.Nat.antidiagonal p₁.1.1 => X.X p.2.1.1 ⊗ (Y.X p.2.1.2 ⊗ Z.X p.1.1.2)) ≅
      biproduct (fun p : Σ p₁ : Finset.Nat.antidiagonal i, Finset.Nat.antidiagonal p₁.1.2 => X.X p.1.1.1 ⊗ (Y.X p.2.1.1 ⊗ Z.X p.2.1.2)) :=
  biproduct.whisker_equiv associator₄_equiv
    fun ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩ => Iso.refl _

def associator₅ (X Y Z : ChainComplex V ℕ) (i : ℕ) :
    biproduct (fun p : Σ p₁ : Finset.Nat.antidiagonal i, Finset.Nat.antidiagonal p₁.1.2 => X.X p.1.1.1 ⊗ (Y.X p.2.1.1 ⊗ Z.X p.2.1.2)) ≅
      biproduct (fun p : Finset.Nat.antidiagonal i => biproduct (fun q : Finset.Nat.antidiagonal p.1.2 => X.X p.1.1 ⊗ (Y.X q.1.1 ⊗ Z.X q.1.2))) :=
  (biproductBiproductIso
    (fun p : Finset.Nat.antidiagonal i => Finset.Nat.antidiagonal p.1.2)
    (fun (p : Finset.Nat.antidiagonal i) (q : Finset.Nat.antidiagonal p.1.2) => X.X p.1.1 ⊗ (Y.X q.1.1 ⊗ Z.X q.1.2))).symm

def associator₆ (X Y Z : ChainComplex V ℕ) (i : ℕ) :
    biproduct (fun p : Finset.Nat.antidiagonal i => biproduct (fun q : Finset.Nat.antidiagonal p.1.2 => X.X p.1.1 ⊗ (Y.X q.1.1 ⊗ Z.X q.1.2))) ≅
      (tensorObj X (tensorObj Y Z)).X i :=
  biproduct.mapIso fun _ => (leftDistributor _ _).symm

def associator (X Y Z : ChainComplex V ℕ) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => associator₁ X Y Z i ≪≫ associator₂ X Y Z i ≪≫ associator₃ X Y Z i ≪≫ associator₄ X Y Z i ≪≫ associator₅ X Y Z i ≪≫ associator₆ X Y Z i)
    (fun i j w => by
      dsimp [tensorObj, tensorObj_X]
      ext ⟨⟨j₁, j₂⟩, wj⟩ ⟨⟨i₁, i₂⟩, wi⟩
      dsimp [tensorObj_d, associator₁, associator₂, associator₃, associator₄, associator₅, associator₆]
      simp
      -- Haha, this is horrendous.
      sorry)

end MonoidalCategory

open MonoidalCategory

instance : MonoidalCategory (ChainComplex V ℕ) where
  tensorObj := tensorObj
  tensorHom := tensorHom
  tensorUnit' := (ChainComplex.single₀ V).obj (𝟙_ V)
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
      dsimp [MonoidalCategory.tensorObj, tensorObj_X, MonoidalCategory.tensorHom]
      ext

end ChainComplex
