/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Grassmannians

## Main definitions

- `Module.Grassmannian`: `G(k, M; R)` is the `k`ᵗʰ Grassmannian of the `R`-module `M`. It is defined
  to be the set of submodules of `M` whose **quotient** is locally free of rank `k`. Note that there
  is another convention in literature where the `k`ᵗʰ Grassmannian would instead be `k`-dimensional
  subspaces of a given vector space over a field. See implementation notes below.

- `Module.Grassmannian.functor`: The Grassmannian functor that sends an `R`-algebra `A` to the set
  `G(k, A ⊗[R] M; A)`.

## Implementation notes

In the literature, two conventions exist:

1. The `k`ᵗʰ Grassmannian parametrises `k`-dimensional **subspaces** of a given finite-dimensional
   vector space over a field.
2. The `k`ᵗʰ Grassmannian parametrises **quotients** that are locally free of rank `k`, of a given
   module over a ring.

For the purposes of Algebraic Geometry, the first definition here cannot be generalised to obtain
a scheme to represent the functor, which is why the second definition is the one chosen by
[Grothendieck, EGA I.9.7.3][grothendieck-1971] (Springer edition only), and in EGA V.11
(unpublished).

The first definition in the stated generality (i.e. over a field `F`, and finite-dimensional vector
space `V`) can be recovered from the second definition by noting that `k`-dimensional subspaces of
`V` are canonically equivalent to `(n-k)`-dimensional quotients of `V`, and also to `k`-dimensional
quotients of `V*`, the dual of `V`. In symbols, this means that the first definition is equivalent
to `G(n - k, V; F)` and also to `G(k, V →ₗ[F] F; F)`, where `n` is the dimension of `V`.

## TODO
- Define and recover the subspace-definition (i.e. the first definition above).
- Define `chart x` indexed by `x : Fin k → M` as a subtype consisting of those
  `N ∈ G(k, A ⊗[R] M; A)` such that the composition `R^k → M → M⧸N` is an isomorphism.
- Define `chartFunctor x` to turn `chart x` into a subfunctor of `Module.Grassmannian.functor`. This
  will correspond to an affine open chart in the Grassmannian.
- Grassmannians for schemes and quasi-coherent sheaf of modules.
- Representability of `Module.Grassmannian.functor R M k`.
-/

public section

universe u v w

namespace Module

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (k : ℕ)

/-- `G(k, M; R)` is the `k`ᵗʰ Grassmannian of the `R`-module `M`. It is defined to be the set of
submodules of `M` whose quotient is locally free of rank `k`. Note that there is another convention
in literature where instead the submodule is required to have rank `k`. See the module docstring
of `RingTheory.Grassmannian`. -/
@[stacks 089R] structure Grassmannian extends Submodule R M where
  finite_quotient : Module.Finite R (M ⧸ toSubmodule)
  projective_quotient : Projective R (M ⧸ toSubmodule)
  rankAtStalk_eq : ∀ p, rankAtStalk (R := R) (M ⧸ toSubmodule) p = k

attribute [instance] Grassmannian.finite_quotient Grassmannian.projective_quotient

namespace Grassmannian

@[inherit_doc] scoped notation "G(" k ", " M "; " R ")" => Grassmannian R M k

variable {R M k}

instance : CoeOut G(k, M; R) (Submodule R M) :=
  ⟨toSubmodule⟩

@[ext] lemma ext {N₁ N₂ : G(k, M; R)} (h : (N₁ : Submodule R M) = N₂) : N₁ = N₂ := by
  cases N₁; cases N₂; congr 1

section Functor

open CategoryTheory TensorProduct AlgebraTensorModule

attribute [local ext high] ConcreteCategory.hom_ext

variable {A : Type w} [CommRing A] [Algebra R A]
variable {B : Type w} [CommRing B] [Algebra R B]
variable (f : A →ₐ[R] B)

/-- The map on Grassmannians induced by base change along an algebra map `A → B`.
Given a submodule `N` of `A ⊗[R] M`, the image is the kernel of the composition
B ⊗[R] M ≃ B ⊗[A] (A ⊗[R] M) → B ⊗[A] ((A ⊗[R] M) ⧸ N)`. -/
def map (N : G(k, (A ⊗[R] M); A)) : G(k, (B ⊗[R] M); B) :=
  letI : Algebra A B := f.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' <| IsScalarTower.algebraMap_eq R A B
  letI f' := N.toSubmodule.mkQ.baseChange B ∘ₗ (cancelBaseChange R A B B M).symm.toLinearMap
  haveI equiv := f'.quotKerEquivOfSurjective <|
    (LinearMap.baseChange_surjective B (Submodule.mkQ_surjective _)).comp
      (cancelBaseChange R A B B M).symm.surjective
  { toSubmodule := f'.ker
    finite_quotient := Module.Finite.equiv equiv.symm
    projective_quotient := Module.Projective.of_equiv equiv.symm
    rankAtStalk_eq p := by
      calc
        _ = rankAtStalk (R := B) (B ⊗[A] ((A ⊗[R] M) ⧸ N.toSubmodule)) p := by
          simpa using congrArg (fun g => g p) <| Module.rankAtStalk_eq_of_equiv equiv
        _ = rankAtStalk (R := A) (A ⊗[R] M ⧸ N.toSubmodule)
            (PrimeSpectrum.comap (algebraMap A B) p) := by
          simpa using Module.rankAtStalk_baseChange ..
        _ = k := N.rankAtStalk_eq _ }

theorem map_toSubmodule (N : G(k, A ⊗[R] M; A)) :
    letI : Algebra A B := f.toAlgebra
    letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' <|
      IsScalarTower.algebraMap_eq R A B
    (map f N).toSubmodule = LinearMap.ker
      (N.toSubmodule.mkQ.baseChange B ∘ₗ (cancelBaseChange R A B B M).symm.toLinearMap) := by rfl

variable (k)

@[simp] theorem map_id (A : CommAlgCat R) (N : G(k, A ⊗[R] M; A)) :
    map (.id R A) N = N := by
  ext : 1
  exact (ker_baseChange_comp_cancelBaseChange_symm N.mkQ).trans N.toSubmodule.ker_mkQ

variable {C : Type w} [CommRing C] [Algebra R C]
variable (g : B →ₐ[R] C)

theorem map_comp (N : G(k, A ⊗[R] M; A)) :
    map (g.comp f) N = map g (map f N) := by
  algebraize [f.toRingHom, g.toRingHom, (g.comp f).toRingHom]
  -- FIXME: `algebraize` doesn't generate this instance, even though it seems like it should
  let : IsScalarTower A B C := by apply IsScalarTower.of_algebraMap_eq'; rfl
  let fAB := N.toSubmodule.mkQ.baseChange B ∘ₗ
    (cancelBaseChange R A B B M).symm.toLinearMap
  let fAC := N.toSubmodule.mkQ.baseChange C ∘ₗ
    (cancelBaseChange R A C C M).symm.toLinearMap
  let fBC := fAB.ker.mkQ.baseChange C ∘ₗ
    (cancelBaseChange R B C C M).symm.toLinearMap
  have hfAB : Function.Surjective fAB :=
    (LinearMap.baseChange_surjective B (Submodule.mkQ_surjective _)).comp
      (cancelBaseChange R A B B M).symm.surjective
  let e := (fAB.quotKerEquivOfSurjective hfAB).baseChange B C ≪≫ₗ
    cancelBaseChange A B C C (A ⊗[R] M ⧸ N.toSubmodule)
  ext x
  have hfAC_ker_eq : (map (g.comp f) N).toSubmodule = fAC.ker := map_toSubmodule (g.comp f) N
  have hfBC_ker_eq : (map g (map f N)).toSubmodule = fBC.ker := by
    rw [map_toSubmodule g (map f N), map_toSubmodule f N]
  have hcomp : fAC = e.toLinearMap.comp fBC := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [fAC, fBC, e]
    | tmul c m =>
      simp [fAB, fAC, fBC, e, LinearMap.baseChange_tmul,
        cancelBaseChange_symm_tmul, LinearEquiv.baseChange_tmul,
        cancelBaseChange_tmul,
        LinearMap.quotKerEquivOfSurjective_apply_mk]
    | add x y hx hy =>
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, map_add] at *
      rw [hx, hy]
  rw [hfAC_ker_eq, hfBC_ker_eq, hcomp, LinearEquiv.ker_comp]

/-- The Grassmannian functor sends an `R`-algebra `A` to `G(k, A ⊗[R] M; A)`. -/
@[expose, simps]
def functor : CommAlgCat.{w, u} R ⥤ Type (max v w) where
  obj A := G(k, (A ⊗[R] M); A)
  map f := ↾map f.hom
  map_id A := by ext N : 1; exact map_id k A N
  map_comp f g := by ext N : 1; exact map_comp k f.hom g.hom N

end Functor

end Grassmannian

end Module
