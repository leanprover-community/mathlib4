import Mathlib.RingTheory.HopfAlgebra.Cat
import Mathlib.RingTheory.Bialgebra.Monoidal
import Mathlib.RingTheory.Bialgebra.ChangeOfRings

universe v u
namespace HopfAlgebra
open scoped TensorProduct

variable {R A B C D : Type u} [CommRing R] [Ring A] [Ring B] [Ring C] [Ring D]
    [HopfAlgebra R A] [HopfAlgebra R B] [HopfAlgebra R C] [HopfAlgebra R D]

noncomputable instance {A B : Type u} [Ring A] [Ring B]
    [HopfAlgebra R A] [HopfAlgebra R B] : HopfAlgebra R (A ⊗[R] B) where
      antipode := TensorProduct.map antipode antipode
      mul_antipode_rTensor_comul := sorry
      mul_antipode_lTensor_comul := sorry

open TensorProduct

variable (S : Type u) [CommRing S] [Algebra R S]

noncomputable instance : HopfAlgebra S (S ⊗[R] A) where
  antipode := LinearMap.baseChange S antipode
  mul_antipode_rTensor_comul := sorry
  mul_antipode_lTensor_comul := sorry

end HopfAlgebra
