/-
Copyright (c) 2024 Judith Ludwig, Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Florent Schaffhauser
-/

import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.RingTheory.Finiteness
import Mathlib.Algebra.Module.Defs

/-!
# Faithfully flat modules

A module `M` over a commutative ring `R` is *faithfully flat* if it is flat and,
for all `R`-module homomorphism `f : N → N'` such that `id ⊗ f = 0`, we have `f = 0`.

In the Stacks project, the definition of faithfully flat is different but tag
<https://stacks.math.columbia.edu/tag/00TN> proves that their definition is equivalent to this.

## Main declaration

- `Module.FaithfullyFlat`: the predicate asserting that an `R`-module `M` is faithfully flat.

## Main theorems

- `Module.FaithfullyFlat.of_linearEquiv`: modules linearly equivalent to a flat modules are flat
- `Module.FaithfullyFlat.comp`: https://stacks.math.columbia.edu/tag/00HC
-/

universe u

namespace Module

variable (R : Type u) (M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

/--
A module `M` over a commutative ring `R` is *faithfully flat* if it is flat and,
for all `R`-module homomorphism `f : N → N'` such that `id ⊗ f = 0`, we have `f = 0`.
-/

@[mk_iff] class FaithfullyFlat : Prop where
  flat : Module.Flat R M := by infer_instance
  zero_if_lTensor_zero :  ∀ ⦃N N': Type u⦄ [AddCommGroup N][Module R N][AddCommGroup N']
  [Module R N'](f : N →ₗ[R] N'),
     LinearMap.lTensor M f = 0 → (f = 0)

namespace FaithfullyFlat

attribute [instance] flat

instance self (R : Type u) [CommRing R] : FaithfullyFlat R R where
  zero_if_lTensor_zero := by
    intros N N' _ _ _ _ f hf
    ext n
    have h : f n = (TensorProduct.lid R N') (LinearMap.lTensor R f ( 1 ⊗ₜ[R] n)) := by
     simp
    rw [h, hf]
    rfl

variable {N : Type u} [AddCommGroup N] [Module R N]

/--
If `M` is a faithfully flat module, then for all linear maps `f`, the map `id ⊗ f = 0`, if and only
if  `f = 0`. -/
lemma zero_iff_lTensor_zero {N' : Type u} [AddCommGroup N'] [Module R N']
    [h: FaithfullyFlat R M] (f : N →ₗ[R] N') :
    (f = 0) ↔  LinearMap.lTensor M f = 0 := by
      constructor
      · intro hf
        rw [hf]
        exact LinearMap.lTensor_zero M
      · exact Module.FaithfullyFlat.zero_if_lTensor_zero f

/--
A faithfully flat `R`-module `M` is flat and for all linear maps `f`, the map `f ⊗ id = 0`, if and
only if  `f = 0`. -/
lemma zero_iff_lTensor_zero' :
    FaithfullyFlat R M → (Module.Flat R M ∧
  (∀ ⦃N N': Type u⦄ [AddCommGroup N][Module R N][AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N'),
  (f = 0) ↔ LinearMap.lTensor M f = 0)):= by
      intro h
      constructor
      · infer_instance
      introv
      constructor
      · intro hf
        rw [hf]
        exact LinearMap.lTensor_zero M
      exact Module.FaithfullyFlat.zero_if_lTensor_zero f

lemma lTensor_zero_iff_rTensor_zero : ∀ ⦃N N': Type u⦄ [AddCommGroup N][Module R N][AddCommGroup N']
    [Module R N'] (f : N →ₗ[R] N'), LinearMap.lTensor M f = 0 ↔ LinearMap.rTensor M f = 0 := by
    introv
    constructor
    intro lTensor_zero
    have h: LinearMap.rTensor M f =  (TensorProduct.comm R N' M).symm ∘ₗ LinearMap.lTensor M f ∘ₗ
    TensorProduct.comm R N M := by
      ext m n
      simp
    rw [h]
    ext n m
    simp [lTensor_zero]
    intro rTensor_zero
    have h: LinearMap.lTensor M f =  (TensorProduct.comm R M N').symm ∘ₗ LinearMap.rTensor M f ∘ₗ
    TensorProduct.comm R M N := by
      ext m n
      simp
    rw [h]
    ext m n
    simp [rTensor_zero]

/--
An `R`-module `M` is faithfully flat iff it is flat and for all linear maps `f`, the map
`id ⊗ f = 0`, if and only if `f = 0`. -/
lemma zero_iff_rTensor_zero :
    FaithfullyFlat R M ↔ (Module.Flat R M ∧
  (∀ ⦃N N': Type u⦄ [AddCommGroup N][Module R N][AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N'),
  LinearMap.rTensor M f = 0 → (f = 0))):= by
    constructor
    intro FF
    constructor
    · infer_instance
    introv
    intro rTensor_zero
    have h: LinearMap.lTensor M f = 0 := by exact
      (lTensor_zero_iff_rTensor_zero R M f).mpr rTensor_zero
    exact zero_if_lTensor_zero f h
    intro h
    cases' h with h1 h2
    constructor
    · infer_instance
    introv
    intro lTensor_zero
    have h: LinearMap.rTensor M f = 0 := by exact
      (lTensor_zero_iff_rTensor_zero R M f).mp lTensor_zero
    apply h2
    exact h

open LinearMap

variable (M' : Type u) [AddCommGroup M'] [Module R M']

/-- An `R`-module linearly equivalent to a faithfully flat `R`-module is faithfully flat. -/
lemma of_linearEquiv [f : FaithfullyFlat R M][AddCommGroup M'][Module R M'](e : M' ≃ₗ[R] M) :
    FaithfullyFlat R M' where
      flat := Module.Flat.of_linearEquiv R M M' e
      zero_if_lTensor_zero := by
       introv
       intro hf
       have h : lTensor M f = (rTensor N' e.toLinearMap).comp
        ((lTensor M' f).comp (rTensor N (e.symm.toLinearMap))) := by
         ext x
         simp
       simp [hf] at h
       apply zero_if_lTensor_zero (M:=M) f
       exact h

open TensorProduct

-- The following lemma proves implication (1) to (2) in https://stacks.math.columbia.edu/tag/00HP

/-- If M is faithfully flat, then for every nonzero R-module N, then tensor product M⊗RN is nonzero,
-/
lemma tensorproduct_non_zero (N : Type u) [AddCommGroup N] [Module R N] [FaithfullyFlat R M] :
    Nontrivial N  → (Nontrivial (M ⊗[R] N)) := by
  intro hN
  letI f := LinearMap.id (R:= R) (M:= N)
  have h : f ≠ 0 := by
    intro g
    simp [f] at g
    have : Subsingleton N := ⟨fun a b ↦ by
        rw [← LinearMap.id_apply (R := R) a, ← LinearMap.id_apply (R := R) b, g,
        zero_apply, zero_apply]⟩
    exact false_of_nontrivial_of_subsingleton N
  have g : lTensor M f ≠ 0 := by
    by_contra h1
    apply h
    exact zero_if_lTensor_zero (M:=M) f h1
  simp only [lTensor_id, ne_eq, f] at g
  revert g
  contrapose
  push_neg
  intro h1
  have h2: Subsingleton (M ⊗[R] N):= not_nontrivial_iff_subsingleton.mp h1
  exact identityMapOfZeroModuleIsZero

variable (R : Type u) (S : Type u) (M : Type u)
  [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- If `S` is a faithfully flat `R`-algebra, then any faithfully flat `S`-Module is faithfully flat
as an `R`-module. -/
theorem comp [Module.FaithfullyFlat R S] [Module.FaithfullyFlat S M] :
    FaithfullyFlat R M where
    flat := Module.Flat.comp R S M
    zero_if_lTensor_zero := by
     introv
     intro aux
     letI e1 : M ⊗[S] (S ⊗[R] N') →ₗ[S] (M ⊗[R] N') :=
     AlgebraTensorModule.cancelBaseChange R S S M N'
     letI e1.symm := (AlgebraTensorModule.cancelBaseChange R S S M N').symm
     letI e2 : (M ⊗[R] N) →ₗ[S] M ⊗[S] (S ⊗[R] N) :=
     (AlgebraTensorModule.cancelBaseChange R S S M N).symm
     letI e2.symm := (AlgebraTensorModule.cancelBaseChange R S S M N)
     letI fS :  M ⊗[S] (S ⊗[R] N) →ₗ[S] M ⊗[S] (S ⊗[R] N') :=
     lTensor M (TensorProduct.AlgebraTensorModule.map LinearMap.id f)
     have h : restrictScalars (R:= R) (S:= S) (e1 ∘ₗ fS ∘ₗ e2) = lTensor M f := by
        ext n
        simp [e1, e2, fS]
     have h1 : fS = e1.symm ∘ₗ (e1 ∘ₗ fS ∘ₗ e2) ∘ₗ e2.symm := by
       ext m n
       simp [e1, e1.symm, e2, e2.symm]
     have g : e1 ∘ₗ fS ∘ₗ e2 = 0 := by
       rw [aux] at h
       rwa [← DFunLike.coe_fn_eq] at h ⊢
     have g1: fS = 0 := by
       rw [aux] at h
       rw [g] at h1
       simp only [h1, zero_comp, comp_zero]
     apply zero_if_lTensor_zero (R:= R) (M := S) (N:= N) (N':= N') f
     have h3: lTensor S f = 0 ↔
     TensorProduct.AlgebraTensorModule.map (R:= R) (A:= S) (M:= S) LinearMap.id f = 0 := by
        have res : restrictScalars (R:= R) (S:= S) (TensorProduct.AlgebraTensorModule.map
        (R:= R) (A:= S) (M:= S) LinearMap.id f) = LinearMap.lTensor S f := by
            ext s n
            simp only [AlgebraTensorModule.curry_apply, curry_apply, coe_restrictScalars,
              AlgebraTensorModule.map_tmul, id_coe, id_eq, lTensor_tmul]
        constructor
        · rw [← res]
          intro h
          ext n
          simp only [AlgebraTensorModule.curry_apply, h, curry_apply, zero_apply,
            coe_restrictScalars]
        · intro h
          rw [← res]
          ext s n
          simp only [h, AlgebraTensorModule.curry_apply, curry_apply, coe_restrictScalars,
          zero_apply, restrictScalars_zero]
     rw [h3]
     apply zero_if_lTensor_zero (R:= S) (M := M) (N:= S ⊗ N) (N':= S ⊗ N')
      (AlgebraTensorModule.map LinearMap.id f)
     exact g1

end FaithfullyFlat
end Module
