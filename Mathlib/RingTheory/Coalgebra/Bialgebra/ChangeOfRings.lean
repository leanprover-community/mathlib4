import Mathlib.RingTheory.Coalgebra.Bialgebra.Hom
import Mathlib.RingTheory.Coalgebra.ChangeOfRings

universe v u
section
open TensorProduct

variable {R M N P Q : Type u} [CommRing R]
  [Ring M] [Ring N] [Ring P] [Ring Q] [Bialgebra R M] [Bialgebra R N]
  [Bialgebra R P] [Bialgebra R Q]

noncomputable instance instExtendScalarsBialgebra (S : Type u) [CommRing S] [Algebra R S] :
    Bialgebra S (S ⊗[R] M) where
      counit_one := sorry
      mul_compr₂_counit := sorry
      comul_one := sorry
      mul_compr₂_comul := sorry

@[simps! toLinearMap]
noncomputable def BialgHom.baseChange (S : Type u) [CommRing S] [Algebra R S] (f : M →b[R] N) :
    S ⊗[R] M →b[S] S ⊗[R] N :=
  { f.toCoalgHom.baseChange S with
    map_one' := sorry
    map_mul' := sorry
    map_zero' := sorry
    commutes' := sorry }
