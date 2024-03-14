import Mathlib.RingTheory.Coalgebra.Monoidal
import Mathlib.RingTheory.TensorProduct

universe v u
section
open TensorProduct

variable {R M N P Q : Type u} [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q] [Module R M] [Module R N]
  [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N] [Coalgebra R P] [Coalgebra R Q]

@[simps] noncomputable instance instExtendScalarsCoalgebraStruct
    (S : Type u) [CommRing S] [Algebra R S] : CoalgebraStruct S (S ⊗[R] M) where
  comul := (AlgebraTensorModule.cancelBaseChange R S S (S ⊗[R] M) M
    ≪≫ₗ (AlgebraTensorModule.assoc R R S S M M)).symm.toLinearMap
    ∘ₗ LinearMap.baseChange S (Coalgebra.comul (R := R) (A := M))
  counit := AlgebraTensorModule.rid R S S ∘ₗ LinearMap.baseChange S
    ((Coalgebra.counit (R := R) (A := M)))

noncomputable instance instExtendScalarsCoalgebra (S : Type u) [CommRing S] [Algebra R S] :
    Coalgebra S (S ⊗[R] M) where
      coassoc := sorry
      rTensor_counit_comp_comul := by
        ext x
        sorry
      lTensor_counit_comp_comul := sorry

@[simps! toLinearMap]
noncomputable def CoalgHom.baseChange (S : Type u) [CommRing S] [Algebra R S] (f : M →c[R] N) :
    S ⊗[R] M →c[S] S ⊗[R] N :=
  { LinearMap.baseChange S f.toLinearMap with
    counit_comp := sorry
    map_comp_comul := sorry }

end
