import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Topology.ContinuousFunction.Algebra
import Mathlib.Algebra.Algebra.Spectrum
import Mathlib.Topology.ContinuousFunction.Polynomial
import Mathlib.Topology.ContinuousFunction.StoneWeierstrass

open Polynomial

/- note: because `H` is marked as an `outParam` we can't require that there are different morphism
types for the same kind of function space. -/

/-- Here, `F` is generally some kind of algebra of functions, and `H` is a
type of algebra homomorphisms from `F` to `A`. We are agnostic about exactly what
requirements we have so that by placing sufficiently strong type class assumptions
we can get different morphisms. -/
class FunctionalCalculus (H : outParam (Type _)) {F A : Type _} [FunLike H F (fun _ ↦ A)]
    (f : F) (a : A) where
  toHom : H
  map_point' : toHom f = a

namespace FunctionalCalculus

def fc {H F A : Type _} [FunLike H F (fun _ ↦ A)] (f : F) (a : A)
    [FunctionalCalculus H f a] : H :=
  FunctionalCalculus.toHom f a

@[simp]
lemma map_point {H F A : Type _} [FunLike H F (fun _ ↦ A)] {f : F} {a : A}
    [FunctionalCalculus H f a] : (fc f a) f = a :=
  FunctionalCalculus.map_point'

class FunctionalCalculusComp (H₁ H₂ H₃ : Type _) {F₁ F₂ F₃ A : Type}
    [FunLike H₁ F₁ (fun _ ↦ A)] [FunLike H₂ F₂ (fun _ ↦ A)] [FunLike H₃ F₃ (fun _ ↦ A)]
    (cmp : F₂ → F₃) (f f₁ : F₁) (f₂ : F₂) (f₃ : F₃) (a b : A)
    [FunctionalCalculus H₁ f₁ a]
    [FunctionalCalculus H₂ f₂ (fc f₁ a f)]
    [FunctionalCalculus H₃ f₃ b] where
  fc_comp' : ∀ g : F₂, fc f₂ (fc f₁ a f) g = fc f₃ b (cmp g)

-- applied to `f₂`, this means
-- `fc f₁ a = fc f₂ (fc f₁ a f) f₂ = fc f₃ b (cmp f₂)`

instance {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A] {a : A} :
    FunctionalCalculus (R[X] →ₐ[R] A) (X : R[X]) a where
  toHom := aeval a
  map_point' := aeval_X a

lemma fc_polynomial_def {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A] {a : A} :
    fc (X : R[X]) a = aeval a :=
  rfl

example {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A] {a : A} :
    fc (X : R[X]) a X = a :=
  map_point -- `by simp` fails?

noncomputable instance {R A : Type _}
    [CommSemiring R] [Semiring A] [Algebra R A] {a : A} {p : R[X]} :
    FunctionalCalculus (R[X] →ₐ[R] A) (aeval (R := R) p X) (fc (X : R[X]) a p) where
  toHom := aeval a
  map_point' := by
    simp only [aeval_X]
    rfl

lemma fc_polynomial_def' {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A] {a : A}
    (p : R[X]) : fc (aeval (R := R) p X) (fc (X : R[X]) a p) = aeval a :=
  rfl

noncomputable instance {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A] {a : A} {p : R[X]} :
    FunctionalCalculusComp (R[X] →ₐ[R] A) (R[X] →ₐ[R] A) (R[X] →ₐ[R] A)
      (aeval (R := R) p) p (X : R[X]) (X : R[X]) (X : R[X]) a a where
  fc_comp' := by
    simp_rw [fc_polynomial_def']
    simp only [fc_polynomial_def, aeval_algHom, AlgHom.coe_comp, Function.comp_apply, forall_const]

end FunctionalCalculus

open FunctionalCalculus

class MapsSpectrum {H F R A : Type _} [CommSemiring R] [Ring A] [Algebra R A]
    [FunLike H F (fun _ ↦ A)] (f : F) (a : A) [FunctionalCalculus H f a] (im : F → Set R) where
  maps_spectrum : ∀ g : F, spectrum R (fc f a g) = im g

class UniqueFunctionalCalculus {H F A : Type _} [FunLike H F (fun _ ↦ A)]
    {f : F} {a : A} (p : FunctionalCalculus H f a → Prop) where
  fc_eq : ∀ fc₁ fc₂ : FunctionalCalculus H f a,
    p fc₁ → p fc₂ → @fc _ _ _ _ _ _ fc₁ = @fc _ _ _ _ _ _ fc₂

variable {𝕜 A : Type _} [IsROrC 𝕜] [Ring A] [StarRing A] [Algebra 𝕜 A] [TopologicalSpace A]
    [StarModule 𝕜 A]

/-- A continuous functional calculus (over either `ℝ` or `ℂ`) for an element with compact
spectrum is unique. This utilizes the Stone-Weierstrass theorem. -/
instance {𝕜 A : Type _} [IsROrC 𝕜] [Ring A] [StarRing A] [Algebra 𝕜 A] [TopologicalSpace A]
    [StarModule 𝕜 A] [T2Space A] {a : A} [CompactSpace (spectrum 𝕜 a)] :
    UniqueFunctionalCalculus
      (fun φ : FunctionalCalculus (C(spectrum 𝕜 a, 𝕜) →⋆ₐ[𝕜] A)
        (Polynomial.toContinuousMapOnAlgHom (spectrum 𝕜 a) (X : 𝕜[X])) a ↦ Continuous φ.toHom) where
  fc_eq := fun fc₁ fc₂ h₁ h₂ ↦
    ContinuousMap.starAlgHom_ext_map_X h₁ h₂ <| fc₁.map_point'.trans fc₂.map_point'.symm
