/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.Span

#align_import algebra.algebra.tower from "leanprover-community/mathlib"@"71150516f28d9826c7341f8815b31f7d8770c212"

/-!
# Towers of algebras

In this file we prove basic facts about towers of algebra.

An algebra tower A/S/R is expressed by having instances of `Algebra A S`,
`Algebra R S`, `Algebra R A` and `IsScalarTower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

An important definition is `toAlgHom R S A`, the canonical `R`-algebra homomorphism `S →ₐ[R] A`.

-/


open Pointwise

universe u v w u₁ v₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

namespace Algebra

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable [AddCommMonoid M] [Module R M] [Module A M] [Module B M]
variable [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]
variable {A}


/-- The `R`-algebra morphism `A → End (M)` corresponding to the representation of the algebra `A`
on the `B`-module `M`.

This is a stronger version of `DistribMulAction.toLinearMap`, and could also have been
called `Algebra.toModuleEnd`.

The typeclasses correspond to the situation where the types act on each other as
```
R ----→ B
| ⟍     |
|   ⟍   |
↓     ↘ ↓
A ----→ M
```
where the diagram commutes, the action by `R` commutes with everything, and the action by `A` and
`B` on `M` commute.

Typically this is most useful with `B = R` as `Algebra.lsmul R R A : A →ₐ[R] Module.End R M`.
However this can be used to get the fact that left-multiplication by `A` is right `A`-linear, and
vice versa, as
```lean
example : A →ₐ[R] Module.End Aᵐᵒᵖ A := Algebra.lsmul R Aᵐᵒᵖ A
example : Aᵐᵒᵖ →ₐ[R] Module.End A A := Algebra.lsmul R A A
```
respectively; though `LinearMap.mulLeft` and `LinearMap.mulRight` can also be used here.
-/
def lsmul : A →ₐ[R] Module.End B M where
  toFun := DistribMulAction.toLinearMap B M
  map_one' := LinearMap.ext fun _ => one_smul A _
  map_mul' a b := LinearMap.ext <| smul_assoc a b
  map_zero' := LinearMap.ext fun _ => zero_smul A _
  map_add' _a _b := LinearMap.ext fun _ => add_smul _ _ _
  commutes' r := LinearMap.ext <| algebraMap_smul A r
#align algebra.lsmul Algebra.lsmulₓ

@[simp]
theorem lsmul_coe (a : A) : (lsmul R B M a : M → M) = (a • ·) := rfl
#align algebra.lsmul_coe Algebra.lsmul_coe

end Algebra

namespace IsScalarTower

section Module

variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [MulAction A M]
variable {R} {M}

theorem algebraMap_smul [SMul R M] [IsScalarTower R A M] (r : R) (x : M) :
    algebraMap R A r • x = r • x := by
  rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
#align is_scalar_tower.algebra_map_smul IsScalarTower.algebraMap_smul

variable {A} in
theorem of_algebraMap_smul [SMul R M] (h : ∀ (r : R) (x : M), algebraMap R A r • x = r • x) :
    IsScalarTower R A M where
  smul_assoc r a x := by rw [Algebra.smul_def, mul_smul, h]

variable (R M) in
theorem of_compHom : letI := MulAction.compHom M (algebraMap R A : R →* A); IsScalarTower R A M :=
  letI := MulAction.compHom M (algebraMap R A : R →* A); of_algebraMap_smul fun _ _ ↦ rfl

end Module

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra S A] [Algebra S B]
variable {R S A}

theorem of_algebraMap_eq [Algebra R A]
    (h : ∀ x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S A :=
  ⟨fun x y z => by simp_rw [Algebra.smul_def, RingHom.map_mul, mul_assoc, h]⟩
#align is_scalar_tower.of_algebra_map_eq IsScalarTower.of_algebraMap_eq

/-- See note [partially-applied ext lemmas]. -/
theorem of_algebraMap_eq' [Algebra R A]
    (h : algebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A :=
  of_algebraMap_eq <| RingHom.ext_iff.1 h
#align is_scalar_tower.of_algebra_map_eq' IsScalarTower.of_algebraMap_eq'

variable (R S A)
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R S A] [IsScalarTower R S B]

theorem algebraMap_eq : algebraMap R A = (algebraMap S A).comp (algebraMap R S) :=
  RingHom.ext fun x => by
    simp_rw [RingHom.comp_apply, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
#align is_scalar_tower.algebra_map_eq IsScalarTower.algebraMap_eq

theorem algebraMap_apply (x : R) : algebraMap R A x = algebraMap S A (algebraMap R S x) := by
  rw [algebraMap_eq R S A, RingHom.comp_apply]
#align is_scalar_tower.algebra_map_apply IsScalarTower.algebraMap_apply

@[ext]
theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by have I := h1; exact r • x) = r • x) : h1 = h2 :=
  Algebra.algebra_ext _ _ fun r => by
    simpa only [@Algebra.smul_def _ _ _ _ h1, @Algebra.smul_def _ _ _ _ h2, mul_one] using h r 1
#align is_scalar_tower.algebra.ext IsScalarTower.Algebra.ext

/-- In a tower, the canonical map from the middle element to the top element is an
algebra homomorphism over the bottom element. -/
def toAlgHom : S →ₐ[R] A :=
  { algebraMap S A with commutes' := fun _ => (algebraMap_apply _ _ _ _).symm }
#align is_scalar_tower.to_alg_hom IsScalarTower.toAlgHom

theorem toAlgHom_apply (y : S) : toAlgHom R S A y = algebraMap S A y := rfl
#align is_scalar_tower.to_alg_hom_apply IsScalarTower.toAlgHom_apply

@[simp]
theorem coe_toAlgHom : ↑(toAlgHom R S A) = algebraMap S A :=
  RingHom.ext fun _ => rfl
#align is_scalar_tower.coe_to_alg_hom IsScalarTower.coe_toAlgHom

@[simp]
theorem coe_toAlgHom' : (toAlgHom R S A : S → A) = algebraMap S A := rfl
#align is_scalar_tower.coe_to_alg_hom' IsScalarTower.coe_toAlgHom'

variable {R S A B}

@[simp]
theorem _root_.AlgHom.map_algebraMap (f : A →ₐ[S] B) (r : R) :
    f (algebraMap R A r) = algebraMap R B r := by
  rw [algebraMap_apply R S A r, f.commutes, ← algebraMap_apply R S B]
#align alg_hom.map_algebra_map AlgHom.map_algebraMap

variable (R)

@[simp]
theorem _root_.AlgHom.comp_algebraMap_of_tower (f : A →ₐ[S] B) :
    (f : A →+* B).comp (algebraMap R A) = algebraMap R B :=
  RingHom.ext (AlgHom.map_algebraMap f)
#align alg_hom.comp_algebra_map_of_tower AlgHom.comp_algebraMap_of_tower

-- conflicts with IsScalarTower.Subalgebra
instance (priority := 999) subsemiring (U : Subsemiring S) : IsScalarTower U S A :=
  of_algebraMap_eq fun _x => rfl
#align is_scalar_tower.subsemiring IsScalarTower.subsemiring

-- Porting note: @[nolint instance_priority]
instance (priority := 999) of_algHom {R A B : Type*} [CommSemiring R] [CommSemiring A]
    [CommSemiring B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    @IsScalarTower R A B _ f.toRingHom.toAlgebra.toSMul _ :=
  letI := (f : A →+* B).toAlgebra
  of_algebraMap_eq fun x => (f.commutes x).symm
#align is_scalar_tower.of_ring_hom IsScalarTower.of_algHom

end Semiring

end IsScalarTower

section Homs

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra S A] [Algebra S B]
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R S A] [IsScalarTower R S B]
variable {A S B}

open IsScalarTower

namespace AlgHom

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def restrictScalars (f : A →ₐ[S] B) : A →ₐ[R] B :=
  { (f : A →+* B) with
    commutes' := fun r => by
      rw [algebraMap_apply R S A, algebraMap_apply R S B]
      exact f.commutes (algebraMap R S r) }
#align alg_hom.restrict_scalars AlgHom.restrictScalars

theorem restrictScalars_apply (f : A →ₐ[S] B) (x : A) : f.restrictScalars R x = f x := rfl
#align alg_hom.restrict_scalars_apply AlgHom.restrictScalars_apply

@[simp]
theorem coe_restrictScalars (f : A →ₐ[S] B) : (f.restrictScalars R : A →+* B) = f := rfl
#align alg_hom.coe_restrict_scalars AlgHom.coe_restrictScalars

@[simp]
theorem coe_restrictScalars' (f : A →ₐ[S] B) : (restrictScalars R f : A → B) = f := rfl
#align alg_hom.coe_restrict_scalars' AlgHom.coe_restrictScalars'

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A →ₐ[S] B) → A →ₐ[R] B) := fun _ _ h =>
  AlgHom.ext (AlgHom.congr_fun h : _)
#align alg_hom.restrict_scalars_injective AlgHom.restrictScalars_injective

end AlgHom

namespace AlgEquiv

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def restrictScalars (f : A ≃ₐ[S] B) : A ≃ₐ[R] B :=
  { (f : A ≃+* B) with
    commutes' := fun r => by
      rw [algebraMap_apply R S A, algebraMap_apply R S B]
      exact f.commutes (algebraMap R S r) }
#align alg_equiv.restrict_scalars AlgEquiv.restrictScalars

theorem restrictScalars_apply (f : A ≃ₐ[S] B) (x : A) : f.restrictScalars R x = f x := rfl
#align alg_equiv.restrict_scalars_apply AlgEquiv.restrictScalars_apply

@[simp]
theorem coe_restrictScalars (f : A ≃ₐ[S] B) : (f.restrictScalars R : A ≃+* B) = f := rfl
#align alg_equiv.coe_restrict_scalars AlgEquiv.coe_restrictScalars

@[simp]
theorem coe_restrictScalars' (f : A ≃ₐ[S] B) : (restrictScalars R f : A → B) = f := rfl
#align alg_equiv.coe_restrict_scalars' AlgEquiv.coe_restrictScalars'

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A ≃ₐ[S] B) → A ≃ₐ[R] B) := fun _ _ h =>
  AlgEquiv.ext (AlgEquiv.congr_fun h : _)
#align alg_equiv.restrict_scalars_injective AlgEquiv.restrictScalars_injective

end AlgEquiv

end Homs

namespace Submodule

variable {M}
variable [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]
variable [Module R M] [Module A M] [IsScalarTower R A M]

/-- If `A` is an `R`-algebra such that the induced morphism `R →+* A` is surjective, then the
`R`-module generated by a set `X` equals the `A`-module generated by `X`. -/
theorem restrictScalars_span (hsur : Function.Surjective (algebraMap R A)) (X : Set M) :
    restrictScalars R (span A X) = span R X := by
  refine' ((span_le_restrictScalars R A X).antisymm fun m hm => _).symm
  refine' span_induction hm subset_span (zero_mem _) (fun _ _ => add_mem) fun a m hm => _
  obtain ⟨r, rfl⟩ := hsur a
  simpa [algebraMap_smul] using smul_mem _ r hm
#align submodule.restrict_scalars_span Submodule.restrictScalars_span

theorem coe_span_eq_span_of_surjective (h : Function.Surjective (algebraMap R A)) (s : Set M) :
    (Submodule.span A s : Set M) = Submodule.span R s :=
  congr_arg ((↑) : Submodule R M → Set M) (Submodule.restrictScalars_span R A h s)
#align submodule.coe_span_eq_span_of_surjective Submodule.coe_span_eq_span_of_surjective

end Submodule

section Semiring

variable {R S A}

namespace Submodule

section Module

variable [Semiring R] [Semiring S] [AddCommMonoid A]
variable [Module R S] [Module S A] [Module R A] [IsScalarTower R S A]

open IsScalarTower

theorem smul_mem_span_smul_of_mem {s : Set S} {t : Set A} {k : S} (hks : k ∈ span R s) {x : A}
    (hx : x ∈ t) : k • x ∈ span R (s • t) :=
  span_induction hks (fun c hc => subset_span <| Set.smul_mem_smul hc hx)
    (by rw [zero_smul]; exact zero_mem _)
    (fun c₁ c₂ ih₁ ih₂ => by rw [add_smul]; exact add_mem ih₁ ih₂)
    fun b c hc => by rw [IsScalarTower.smul_assoc]; exact smul_mem _ _ hc
#align submodule.smul_mem_span_smul_of_mem Submodule.smul_mem_span_smul_of_mem

theorem span_smul_of_span_eq_top {s : Set S} (hs : span R s = ⊤) (t : Set A) :
    span R (s • t) = (span S t).restrictScalars R :=
  le_antisymm
    (span_le.2 fun _x ⟨p, _hps, _q, hqt, hpqx⟩ ↦ hpqx ▸ (span S t).smul_mem p (subset_span hqt))
    fun p hp ↦ closure_induction hp (zero_mem _) (fun _ _ ↦ add_mem) fun s0 y hy ↦ by
      refine span_induction (hs ▸ mem_top : s0 ∈ span R s)
        (fun x hx ↦ subset_span ⟨x, hx, y, hy, rfl⟩) ?_ ?_ ?_
      · rw [zero_smul]; apply zero_mem
      · intro _ _; rw [add_smul]; apply add_mem
      · intro r s0 hy; rw [IsScalarTower.smul_assoc]; exact smul_mem _ r hy
#align submodule.span_smul_of_span_eq_top Submodule.span_smul_of_span_eq_top

-- The following two lemmas were originally used to prove `span_smul_of_span_eq_top`
-- but are now not needed.
theorem smul_mem_span_smul' {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A}
    (hx : x ∈ span R (s • t)) : k • x ∈ span R (s • t) := by
  rw [span_smul_of_span_eq_top hs] at hx ⊢; exact (span S t).smul_mem k hx
#align submodule.smul_mem_span_smul' Submodule.smul_mem_span_smul'

theorem smul_mem_span_smul {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A}
    (hx : x ∈ span R t) : k • x ∈ span R (s • t) := by
  rw [span_smul_of_span_eq_top hs]
  exact (span S t).smul_mem k (span_le_restrictScalars R S t hx)
#align submodule.smul_mem_span_smul Submodule.smul_mem_span_smul

end Module

section Algebra

variable [CommSemiring R] [Semiring S] [AddCommMonoid A]
variable [Algebra R S] [Module S A] [Module R A] [IsScalarTower R S A]

/-- A variant of `Submodule.span_image` for `algebraMap`. -/
theorem span_algebraMap_image (a : Set R) :
    Submodule.span R (algebraMap R S '' a) = (Submodule.span R a).map (Algebra.linearMap R S) :=
  (Submodule.span_image <| Algebra.linearMap R S).trans rfl
#align submodule.span_algebra_map_image Submodule.span_algebraMap_image

theorem span_algebraMap_image_of_tower {S T : Type*} [CommSemiring S] [Semiring T] [Module R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] (a : Set S) :
    Submodule.span R (algebraMap S T '' a) =
      (Submodule.span R a).map ((Algebra.linearMap S T).restrictScalars R) :=
  (Submodule.span_image <| (Algebra.linearMap S T).restrictScalars R).trans rfl
#align submodule.span_algebra_map_image_of_tower Submodule.span_algebraMap_image_of_tower

theorem map_mem_span_algebraMap_image {S T : Type*} [CommSemiring S] [Semiring T] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] (x : S) (a : Set S)
    (hx : x ∈ Submodule.span R a) : algebraMap S T x ∈ Submodule.span R (algebraMap S T '' a) := by
  rw [span_algebraMap_image_of_tower, mem_map]
  exact ⟨x, hx, rfl⟩
#align submodule.map_mem_span_algebra_map_image Submodule.map_mem_span_algebraMap_image

end Algebra

end Submodule

end Semiring

section Ring

namespace Algebra

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable [AddCommGroup M] [Module R M] [Module A M] [Module B M]
variable [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]

theorem lsmul_injective [NoZeroSMulDivisors A M] {x : A} (hx : x ≠ 0) :
    Function.Injective (lsmul R B M x) :=
  smul_right_injective M hx
#align algebra.lsmul_injective Algebra.lsmul_injective

end Algebra

end Ring
