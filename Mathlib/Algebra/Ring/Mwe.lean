import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Hom.Ring
import Mathlib.Logic.Equiv.Set

structure RingEquiv₁ (R S : Type _) [Mul R] [Mul S] [Add R] [Add S] extends R ≃ S, R ≃* S, R ≃+ S
structure RingEquiv₂ (R S : Type _) [Mul R] [Add R] [Mul S] [Add S] extends R ≃ S, R ≃* S, R ≃+ S

variable [Mul R] [Add R]

@[refl]
def refl₁ : RingEquiv₁ R R :=
  { MulEquiv.refl R, AddEquiv.refl R with }

@[refl]
def refl₂ : RingEquiv₂ R R :=
  { MulEquiv.refl R, AddEquiv.refl R with }
