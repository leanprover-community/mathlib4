import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext
import Mathlib.Algebra.Homology.NewHomology

namespace CategoryTheory

open Category Limits

variable {C : Type _} [Category C] [Abelian C]

namespace Abelian

structure IteratedExtCategory (X Y : C) (n : ℕ) where
  K : CochainComplex C ℤ
  hK₀ : K.IsStrictlyGE 0
  hK₁ : K.IsStrictlyLE (n+2)
  hK (n : ℤ) : IsZero (K.newHomology n)
  iso₁ : X ≅ K.X 0
  iso₂ : K.X (n+2) ≅ Y

inductive YonedaExt' (X Y : C) : ℕ → Type _
  | ofHom (f : X ⟶ Y) : YonedaExt' X Y 0
  | ofExt (E : IteratedExtCategory X Y n) : YonedaExt' X Y (n+1)

end Abelian

end CategoryTheory
