import Mathlib.RingTheory.Flat
import Mathlib.LinearAlgebra.TensorProduct.Tower

universe u v w

open Function (Injective Surjective)

open LinearMap (lsmul rTensor lTensor)

open TensorProduct

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

noncomputable def aux1 (I : Ideal R) : S ⊗[R] I →ₗ[S] S := by
  let i : S ⊗[R] I →ₗ[S] S ⊗[R] R := AlgebraTensorModule.map LinearMap.id (Submodule.subtype I)
  let e' : S ⊗[R] R →ₗ[S] S := AlgebraTensorModule.rid R S S
  exact e'.comp i

private noncomputable def bli (I : Ideal R) : I ⊗[R] S →ₗ[R] S :=
  (aux1 R S I) ∘ₗ (TensorProduct.comm R I S : I ⊗[R] S →ₗ[R] S ⊗[R] I)

lemma aux1_eq (I : Ideal R) : bli R S I = lift (lsmul R S ∘ₗ Submodule.subtype I) := by
  apply TensorProduct.ext'
  intro x s
  simp [bli, aux1]

lemma test_inj (I : Ideal R) :
    Injective (aux1 R S I) ↔ Injective (lift (lsmul R S ∘ₗ Submodule.subtype I)) := by
  rw [← aux1_eq]
  dsimp [bli]
  simp only [EquivLike.injective_comp]

lemma aux1_inj [Algebra.Flat R S] {I : Ideal R} (h : Ideal.FG I) : Injective (aux1 R S I) := by
  rw [test_inj]
  exact Module.Flat.out h

lemma aux1_FG {I : Ideal R} (h : Ideal.FG I) : Module.Finite S (S ⊗[R] I) := by
  have : Module.Finite R I := Module.Finite.iff_fg.mpr h
  exact Module.Finite.base_change R S I

noncomputable def aux (I : Ideal R) : Ideal S := LinearMap.range (aux1 R S I)

lemma aux_FG (I : Ideal R) (h : Ideal.FG I) : Ideal.FG (aux R S I) := by
  dsimp [aux]
  convert_to Submodule.FG (Submodule.map (aux1 R S I) ⊤)
  exact LinearMap.range_eq_map _
  apply Submodule.FG.map 
  exact (aux1_FG R S h).out

noncomputable def aux_iso [Algebra.Flat R S] {I : Ideal R} (h : Ideal.FG I) :
    S ⊗[R] I ≃ₗ[S] aux R S I :=
  LinearEquiv.ofInjective (aux1 R S I) (aux1_inj R S h)

noncomputable def aux2 [Algebra.Flat R S] {I : Ideal R} (h : Ideal.FG I) :
    M ⊗[R] I →ₗ[S] M := by
  letI e1 : M ⊗[R] I ≃ₗ[S] M ⊗[S] (S ⊗[R] I) := (baseChangeCancel R S I M).symm
  letI e2 : M ⊗[S] (S ⊗[R] I) ≃ₗ[S] M ⊗[S] (aux R S I) :=
    TensorProduct.congr (LinearEquiv.refl S M) (aux_iso R S h)
  letI e3 : M ⊗[S] (aux R S I) ≃ₗ[S] (aux R S I) ⊗[S] M := TensorProduct.comm S M (aux R S I)
  letI e4 : (aux R S I) ⊗[S] M →ₗ[S] M := lift (lsmul S M ∘ₗ Submodule.subtype (aux R S I))
  exact e4 ∘ₗ (e1 ≪≫ₗ e2 ≪≫ₗ e3)

private noncomputable def bli2 [Algebra.Flat R S] {I : Ideal R} (h : Ideal.FG I) : I ⊗[R] M →ₗ[R] M :=
  (aux2 R S M h) ∘ₗ (TensorProduct.comm R I M : I ⊗[R] M →ₗ[R] M ⊗[R] I)

lemma aux2_eq [Algebra.Flat R S] {I : Ideal R} (h : Ideal.FG I) :
    bli2 R S M h = lift (lsmul R M ∘ₗ Submodule.subtype I) := by
  apply TensorProduct.ext'
  intro x m
  dsimp [aux2, bli2, aux_iso, aux1]
  simp
  erw [LinearEquiv.ofInjective_apply]
  simp

lemma test2_inj [Algebra.Flat R S] {I : Ideal R} (h : Ideal.FG I) :
    Injective (aux2 R S M h) ↔ Injective (lift (lsmul R M ∘ₗ Submodule.subtype I)) := by
  rw [← aux2_eq R S M h]
  dsimp [bli2]
  simp only [EquivLike.injective_comp]

/-- If `S` is a flat `R`-algebra, then any flat `S`-Module is also `R`-flat. -/
theorem Module.Flat.comp [Algebra.Flat R S] [Module.Flat S M] : Module.Flat R M where
  out := by
    intro I hfg
    rw [← test2_inj R S M hfg]
    dsimp [aux2]
    simp
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
