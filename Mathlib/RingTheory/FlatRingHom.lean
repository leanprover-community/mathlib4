import Mathlib.RingTheory.Flat
import Mathlib.LinearAlgebra.TensorProduct.Tower

universe u v w

open Function (Injective Surjective)

open LinearMap (lsmul rTensor lTensor)

open TensorProduct

section

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {N P : Type*} [AddCommGroup N] [AddCommGroup P] [Module R N] [Module R P]

lemma lTensor_inj_iff_rTensor_inj (f : N →ₗ[R] P) :
    Injective (lTensor M f) ↔ Injective (rTensor M f) := by
  haveI h1 : rTensor M f ∘ₗ TensorProduct.comm R M N =
    TensorProduct.comm R M P ∘ₗ lTensor M f := ext rfl
  haveI h2 : ⇑(TensorProduct.comm R M P) ∘ ⇑(lTensor M f) =
    (TensorProduct.comm R M P) ∘ₗ (lTensor M f) := rfl
  rw [← EquivLike.injective_comp (TensorProduct.comm R M N),
    ← EquivLike.comp_injective _ (TensorProduct.comm R M P), h2, ← h1]
  trivial

variable (R M)

lemma Module.Flat.iff_lTensor_injective :
    Module.Flat R M ↔ ∀ ⦃I : Ideal R⦄ (_ : I.FG), Injective (lTensor M I.subtype) := by
  simp [lTensor_inj_iff_rTensor_inj]
  exact Module.Flat.iff_rTensor_injective R M

lemma Module.Flat.iff_lTensor_injective' :
    Module.Flat R M ↔ ∀ (I : Ideal R), Injective (lTensor M I.subtype) := by
  simp [lTensor_inj_iff_rTensor_inj]
  exact Module.Flat.iff_rTensor_injective' R M

end

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

private noncomputable abbrev auxRightMul (I : Ideal R) : M ⊗[R] I →ₗ[S] M := by
  letI i : M ⊗[R] I →ₗ[S] M ⊗[R] R := AlgebraTensorModule.map LinearMap.id I.subtype
  letI e' : M ⊗[R] R →ₗ[S] M := AlgebraTensorModule.rid R S M
  exact AlgebraTensorModule.rid R S M ∘ₗ i

private noncomputable abbrev auxJ (I : Ideal R) : Ideal S := LinearMap.range (auxRightMul R S S I)

private noncomputable abbrev auxIsoJ [Algebra.Flat R S] {I : Ideal R} :
    S ⊗[R] I ≃ₗ[S] auxJ R S I := by
  apply LinearEquiv.ofInjective (auxRightMul R S S I)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective]
  exact (Module.Flat.iff_lTensor_injective' R S).mp inferInstance I

private noncomputable abbrev aux2 [Algebra.Flat R S] (I : Ideal R) :
    M ⊗[R] I →ₗ[S] M := by
  letI e1 : M ⊗[R] I ≃ₗ[S] M ⊗[S] (S ⊗[R] I) := (baseChangeCancel R S I M).symm
  letI e2 : M ⊗[S] (S ⊗[R] I) ≃ₗ[S] M ⊗[S] (auxJ R S I) :=
    TensorProduct.congr (LinearEquiv.refl S M) (auxIsoJ R S)
  letI e3 : M ⊗[S] (auxJ R S I) →ₗ[S] M ⊗[S] S := lTensor M (auxJ R S I).subtype
  letI e4 : M ⊗[S] S →ₗ[S] M := TensorProduct.rid S M
  exact e4 ∘ₗ e3 ∘ₗ (e1 ≪≫ₗ e2)

private lemma aux2_eq [Algebra.Flat R S] {I : Ideal R} :
    (aux2 R S M I : M ⊗[R] I →ₗ[R] M) = TensorProduct.rid R M ∘ₗ lTensor M (I.subtype) := by
  apply TensorProduct.ext'
  intro m x
  erw [TensorProduct.rid_tmul]
  simp

/-- If `S` is a flat `R`-algebra, then any flat `S`-Module is also `R`-flat. -/
theorem Module.Flat.comp [Algebra.Flat R S] [Module.Flat S M] : Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  rw [← EquivLike.comp_injective _ (TensorProduct.rid R M)]
  haveI h : TensorProduct.rid R M ∘ lTensor M (Submodule.subtype I) =
    TensorProduct.rid R M ∘ₗ lTensor M I.subtype := rfl
  simp only [h, ← aux2_eq R S M, LinearMap.coe_restrictScalars, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.comp_injective, EquivLike.injective_comp]
  exact (Module.Flat.iff_lTensor_injective' S M).mp inferInstance _

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
