import Mathlib.RingTheory.Flat
import Mathlib.LinearAlgebra.TensorProduct.Tower

universe u v w

open Function (Injective Surjective)

open LinearMap (lsmul rTensor lTensor)

open TensorProduct

section

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)

instance : Module R S := by
  have : Algebra R S := f.toAlgebra
  infer_instance

#check g.comp f

end

class Algebra.Flat (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] where
  out : Module.Flat R S

instance (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Flat R S] :
    Module.Flat R S :=
  Algebra.Flat.out

instance Algebra.Flat.self (R : Type u) [CommRing R] : Algebra.Flat R R where
  out := Module.Flat.self R

section
--
variable (R S M N : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

--instance : Module S (M ⊗[R] N) := sorry

noncomputable def baseChangeCancel : N ⊗[R] M ≃ₗ[S] N ⊗[S] (S ⊗[R] M) := by
  letI g : (N ⊗[S] S) ⊗[R] M ≃ₗ[S] N ⊗[R] M :=
    AlgebraTensorModule.congr (TensorProduct.rid S N) (LinearEquiv.neg R)
  exact g.symm ≪≫ₗ (AlgebraTensorModule.assoc R S S N S M)

theorem Module.Flat.comp [Algebra R S] [Module R M] [IsScalarTower R S M] [Algebra.Flat R S]
    [Module.Flat S M] : Module.Flat R M where
  out := by
    intro I hfg
    have : Module S (I ⊗[R] S) := sorry
    let i : I ⊗[R] S →ₗ[R] S := lift (lsmul R S ∘ₗ Submodule.subtype I)
    let i' : I ⊗[R] S →ₗ[S] S := sorry
    have : Injective i := Module.Flat.out hfg
    have : Injective i' := sorry
    let J : Submodule S S := LinearMap.range i'
    --have : (I ⊗[R] S) ⊗[S] M →ₗ[R] I ⊗[R] M := sorry
    sorry

end

variable (R : Type u) (S : Type v) (T : Type w) [CommRing R] [CommRing S] [CommRing T]

theorem Algebra.Flat.comp [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.Flat R S] [Algebra.Flat S T] :
    Algebra.Flat R T where
  out := Module.Flat.comp R S T

class RingHom.Flat {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) where
  out : f.toAlgebra.Flat

instance RingHom.identitiy_flat (R : Type u) [CommRing R] : RingHom.Flat (1 : R →+* R) where
  out := inferInstance

variable {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]
  (f : R →+* S) (g : S →+* T)

instance RingHom.comp_flat : RingHom.Flat (g.comp f) where
  out := sorry
