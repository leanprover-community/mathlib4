import Mathlib.RingTheory.Flat
import Mathlib.LinearAlgebra.TensorProduct.Tower

universe u v w

open Function (Injective Surjective)

open LinearMap (lsmul rTensor lTensor)

open TensorProduct

section

variable (R M N : Type*) [Semiring R] [AddCommMonoid M] [Module R M] [Module.Finite R M]
  [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N)

lemma FG_of_finite : Submodule.FG (LinearMap.range f) := by
  convert_to Submodule.FG (Submodule.map f ⊤)
  exact LinearMap.range_eq_map _
  apply Submodule.FG.map 
  exact Module.finite_def.mp inferInstance

end

section

variable (R S M N : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

@[simps!]
noncomputable def baseChangeCancel : N ⊗[S] (S ⊗[R] M) ≃ₗ[S] N ⊗[R] M := by
  letI g : (N ⊗[S] S) ⊗[R] M ≃ₗ[S] N ⊗[R] M :=
    AlgebraTensorModule.congr (TensorProduct.rid S N) (LinearEquiv.refl R M)
  exact (AlgebraTensorModule.assoc R S S N S M).symm ≪≫ₗ g

end

class Algebra.Flat (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] where
  out : Module.Flat R S

namespace Algebra.Flat

attribute [instance] out

instance self (R : Type u) [CommRing R] : Algebra.Flat R R where
  out := Module.Flat.self R

end Algebra.Flat

section

variable (R S M N : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

noncomputable def aux1 (I : Ideal R) : M ⊗[R] I →ₗ[S] M := by
  let i : M ⊗[R] I →ₗ[S] M ⊗[R] R := AlgebraTensorModule.map LinearMap.id (Submodule.subtype I)
  let e' : M ⊗[R] R →ₗ[S] M := AlgebraTensorModule.rid R S M
  exact e'.comp i

lemma test_inj (I : Ideal R) :
    Injective (aux1 R S M I) ↔ Injective (lift (lsmul R M ∘ₗ Submodule.subtype I)) := by
  letI e : I ⊗[R] M →ₗ[R] M :=
    (aux1 R S M I) ∘ₗ (TensorProduct.comm R I M : I ⊗[R] M →ₗ[R] M ⊗[R] I)
  have eq : e = lift (lsmul R M ∘ₗ Submodule.subtype I) := by
    apply TensorProduct.ext'
    intro x s
    simp [e, aux1]
  simp only [← eq, LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    EquivLike.injective_comp]

noncomputable def aux (I : Ideal R) : Ideal S := LinearMap.range (aux1 R S S I)

lemma aux_FG (I : Ideal R) (h : Ideal.FG I) : Ideal.FG (aux R S I) := by
  haveI : Module.Finite R I := Module.Finite.iff_fg.mpr h
  haveI : Module.Finite S (S ⊗[R] I) := Module.Finite.base_change R S I
  apply FG_of_finite S (S ⊗[R] I) S

noncomputable def aux_iso [Algebra.Flat R S] {I : Ideal R} (h : Ideal.FG I) :
    S ⊗[R] I ≃ₗ[S] aux R S I := by
  apply LinearEquiv.ofInjective (aux1 R S S I)
  rw [test_inj]
  exact Module.Flat.out h

@[simps!]
noncomputable def aux2 [Algebra.Flat R S] {I : Ideal R} (h : Ideal.FG I) :
    M ⊗[R] I →ₗ[S] M := by
  letI e1 : M ⊗[R] I ≃ₗ[S] M ⊗[S] (S ⊗[R] I) := (baseChangeCancel R S I M).symm
  letI e2 : M ⊗[S] (S ⊗[R] I) ≃ₗ[S] M ⊗[S] (aux R S I) :=
    TensorProduct.congr (LinearEquiv.refl S M) (aux_iso R S h)
  letI e3 : M ⊗[S] (aux R S I) →ₗ[S] M := aux1 S S M (aux R S I)
  exact e3 ∘ₗ (e1 ≪≫ₗ e2)

lemma aux2_eq_aux [Algebra.Flat R S] {I : Ideal R} (h : Ideal.FG I) : aux2 R S M h = aux1 R S M I := by
  apply AlgebraTensorModule.ext
  intro x m
  dsimp [aux1, aux2, aux_iso]
  simp
  erw [LinearEquiv.ofInjective_apply]
  simp

/-- If `S` is a flat `R`-algebra, then any flat `S`-Module is also `R`-flat. -/
theorem Module.Flat.comp [Algebra.Flat R S] [Module.Flat S M] : Module.Flat R M where
  out := by
    intro I hfg
    rw [← test_inj R S M, ← aux2_eq_aux R S M hfg]
    dsimp [aux2]
    simp [test_inj]
    exact Module.Flat.out (aux_FG R S I hfg)

end

variable (R : Type u) (S : Type v) (T : Type w) [CommRing R] [CommRing S] [CommRing T]

/-- If `T` is a flat `S`-algebra and `S` is a flat `R`-algebra,
then `T` is a flat `R`-algebra. -/
theorem Algebra.Flat.comp [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.Flat R S] [Algebra.Flat S T] : Algebra.Flat R T where
  out := Module.Flat.comp R S T

/-- A `RingHom` is flat if `R` is flat as an `S` algebra. -/
class RingHom.Flat {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) where
  out : f.toAlgebra.Flat := by infer_instance

namespace RingHom.Flat

attribute [instance] out

/-- The identity of a ring is flat. -/
instance identity (R : Type u) [CommRing R] : RingHom.Flat (1 : R →+* R) where

variable {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]
  (f : R →+* S) (g : S →+* T)

/-- Composition of flat ring homomorphisms is flat. -/
noncomputable instance comp [RingHom.Flat f] [RingHom.Flat g] : RingHom.Flat (g.comp f) where
  out :=
    letI : Algebra R S := f.toAlgebra
    letI : Algebra S T := g.toAlgebra
    letI : Algebra R T := (g.comp f).toAlgebra
    letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (congrFun rfl)
    Algebra.Flat.comp R S T

end RingHom.Flat
