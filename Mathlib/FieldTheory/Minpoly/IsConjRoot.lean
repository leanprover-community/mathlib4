/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Adjoin
import Mathlib.FieldTheory.Normal

/-!
# Conjugate roots

This file specialize to the property of conjugate roots. Given two elements over some ring `K`,
these two elements are conjuagte roots over some `K` if they have the same minimal polynomial over
`K`.

## Main definitions

* `IsConjRoot`: `IsConjRoot K x y` means `y` is a conjugate root of `x` over `K`.

## Main results

* `isConjRoot_iff_exists_algEquiv`: Let `L / K` be a normal field extension. For any two elements
`x` and `y` in `L`, `IsConjRoot K x y` is equivalent to the existence of an algebra equivalence
`σ : L ≃ₐ[K] L` such that `y = σ x`.
* `not_mem_iff_exists_ne_and_isConjRoot`: Let `L / K` be a field extension. If `x` is a separable
element over `K` and the minimal polynomial of `x` splits in `L`, then `x` is not in the `K` iff
there exists a different conjugate root of `x` in `L` over `K`.

## TODO
Prove `IsConjRoot.smul`, if `x` and `y` are conjugate roots, then so are `r • x` and `r • y`.

## Tags
conjugate root, minimal polynomial
-/


open Polynomial minpoly IntermediateField

variable {R K L S A B: Type*} [CommRing R] [CommRing S] [Ring A] [Ring B] [Field K] [Field L]
variable [Algebra R S] [Algebra R A] [Algebra R B]
variable [Algebra K S] [Algebra K L] [Algebra K A] [Algebra L S]

variable (R) in
/--
We say that `x'` is a conjugate root of `x` over `K` if the minimal polynomial of `x` is the
same as the minimal polynomial of `x'`.
-/
def IsConjRoot (x x' : A) : Prop := (minpoly R x) = (minpoly R x')

/--
The definition of conjugate roots.
-/
theorem isConjRoot_def {x x' : A} : IsConjRoot R x x' ↔ minpoly R x = minpoly R x' := Iff.rfl

namespace IsConjRoot

/--
Every element is a conjugate root of itself.
-/
theorem refl {x : A} : IsConjRoot R x x := rfl

/--
If `x` is a conjugate root of `x'`, then `x'` is a conjugate root of `x`.
-/
theorem symm {x x' : A} (h : IsConjRoot R x x') : IsConjRoot R x' x := Eq.symm h

/--
If `x` is a conjugate root of `x'` and `x'` is a conjugate root of `x''`, then `x` is a conjugate
root of `x''`.
-/
theorem trans {x x' x'': A} (h₁ : IsConjRoot R x x') (h₂ : IsConjRoot R x' x'') :
    IsConjRoot R x x'' := Eq.trans h₁ h₂

/--
Let `p` be the minimal polynomial of `x`. If `x'` is a conjugate root of `x`, then `p x' = 0`.
-/
theorem aeval_eq_zero {x x' : A} (h : IsConjRoot R x x') : aeval x' (minpoly R x) = 0 :=
  h ▸ minpoly.aeval R x'

/--
Let `r` be an element of the base ring. If `x` is a conjugate root of `x'`, then `x + r` is a
conjugate root of `x' + r`.
-/
theorem add_algebraMap {x x' : S} (r : K) (h : IsConjRoot K x x') :
    IsConjRoot K (x + algebraMap K S r) (x' + algebraMap K S r) := by
  rw [isConjRoot_def, minpoly.add_algebraMap x r, minpoly.add_algebraMap x' r, h]

/--
Let `r` be an element of the base ring. If `x` is a conjugate root of `x'`, then `x - r` is a
conjugate root of `x' - r`.
-/
theorem sub_algebraMap {x x' : S} (r : K) (h : IsConjRoot K x x') :
    IsConjRoot K (x - algebraMap K S r) (x' - algebraMap K S r) := by
  simpa only [sub_eq_add_neg, map_neg] using add_algebraMap (-r) h

/--
If `x` is a conjugate root of `x'`, then `-x` is a conjugate root of `-x'`.
-/
theorem neg {x x' : S} (h : IsConjRoot K x x') :
    IsConjRoot K (-x) (-x') := by
  rw [isConjRoot_def, minpoly.neg x, minpoly.neg x', h]

end IsConjRoot

open IsConjRoot

variable [IsDomain S]

/--
A variant of `isConjRoot_algHom_iff`, only assuming `Function.Injective f`,
instead of `DivisionRing A`.
If `x` is a conjugate root of `x'` and `f` is an injective `R`-algebra homomorphism, then `f x` is
a conjugate root of `f x'`.
-/
theorem isConjRoot_algHom_iff' {x x' : A} {f : A →ₐ[R] B}
    (hf : Function.Injective f) : IsConjRoot R (f x) (f x') ↔ IsConjRoot R x x' := by
  rw [isConjRoot_def, isConjRoot_def, algHom_eq f hf, algHom_eq f hf]

/--
If `x` is a conjugate root of `x'` in some division ring and `f` is a `R`-algebra homomorphism, then
`f x` is a conjugate root of
`f x'`.
-/
theorem isConjRoot_algHom_iff {A} [DivisionRing A] [Algebra R A]
    [Nontrivial B] {x x' : A} (f : A →ₐ[R] B) : IsConjRoot R (f x) (f x') ↔ IsConjRoot R x x' :=
  isConjRoot_algHom_iff' f.injective

/--
Let `p` be the minimal polynomial of `x`. If `p x'` = 0, then `x'` is a conjugate root of
`x`.
-/
theorem isConjRoot_of_aeval_eq_zero [IsDomain A] {x x' : A} (hx : IsIntegral K x)
    (h : aeval x' (minpoly K x) = 0) : IsConjRoot K x x' :=
  minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) h (minpoly.monic hx)

/--
Let `p` be the minimal polynomial of `x`. Then `x'` is a conjugate root of `x` if and only if
`p x' = 0`.
-/
theorem isConjRoot_iff_aeval_eq_zero [IsDomain A] {x x' : A}
    (h : IsIntegral K x) : IsConjRoot K x x' ↔ aeval x' (minpoly K x) = 0 :=
  ⟨IsConjRoot.aeval_eq_zero, isConjRoot_of_aeval_eq_zero h⟩

/--
Let `s` be an `R`-algebra isomorphism. Then `s x` is a conjugate root of `x`.
-/
@[simp]
theorem isConjRoot_of_algEquiv (x : A) (s : A ≃ₐ[R] A) : IsConjRoot R x (s x) :=
  Eq.symm (minpoly.algEquiv_eq s x)

/--
Let `s₁` and `s₂` be two `R`-algebra isomorphisms. Then `s₁ x` is a conjugate root of `s₂ x`.
-/
@[simp]
theorem isConjRoot_of_algEquiv₂ (x : A) (s₁ s₂ : A ≃ₐ[R] A) : IsConjRoot R (s₁ x) (s₂ x) :=
  isConjRoot_def.mpr <| (minpoly.algEquiv_eq s₂ x) ▸ (minpoly.algEquiv_eq s₁ x)

/--
Let `L / K` be a normal field extension. For any two elements `x` and `x'` in `L`, `x` is a
conjugate root of `x'` then there exists an `K`-automorphism `σ : L ≃ₐ[K] L` such
that `x' = σ x`.
-/
theorem IsConjRoot.exists_algEquiv [Normal K L] {x x': L} (h : IsConjRoot K x x') :
    ∃ σ : L ≃ₐ[K] L, σ x = x' := by
  obtain ⟨σ, hσ⟩ :=
    exists_algHom_of_splits_of_aeval (normal_iff.mp inferInstance) (h ▸ minpoly.aeval K x')
  exact ⟨AlgEquiv.ofBijective σ (σ.normal_bijective _ _ _), hσ⟩

/--
Let `L / K` be a normal field extension. For any two elements `x` and `x'` in `L`, `x` is a
conjugate root of `x'` if and only if there exists an `K`-automorphism `σ : L ≃ₐ[K] L` such
that `x' = σ x`.
-/
theorem isConjRoot_iff_exists_algEquiv [Normal K L] {x x' : L} :
    IsConjRoot K x x' ↔ ∃ σ : L ≃ₐ[K] L, σ x = x' :=
  ⟨exists_algEquiv, fun ⟨_, h⟩ => h ▸ isConjRoot_of_algEquiv _ _⟩

/--
Let `S / L / K` be a tower of extensions. For any two elements `x` and `x'` in `S`, if `x` is a
conjugate root of `x'` over `L`, then `x` is also a conjugate root of `x'` over
`K`.
-/
theorem IsConjRoot.of_isScalarTower [IsScalarTower K L S] {x x' : S} (hx : IsIntegral K x)
    (h : IsConjRoot L x x') : IsConjRoot K x x' :=
  isConjRoot_of_aeval_eq_zero hx <| minpoly.aeval_of_isScalarTower K x x' (aeval_eq_zero h)

/--
`x'` is a conjugate root of `x` over `K` if and only if `x'` is a root of the minimal polynomial of
`x`. This is variant of `isConjRoot_iff_aeval_eq_zero`.
-/
theorem isConjRoot_iff_mem_aroots {x x' : S} (h : IsIntegral K x) :
    IsConjRoot K x x' ↔ x' ∈ (minpoly K x).aroots S := by
  rw [Polynomial.mem_aroots, isConjRoot_iff_aeval_eq_zero h]
  simp only [iff_and_self]
  exact fun _ => minpoly.ne_zero h

/--
`x'` is a conjugate root of `x` over `K` if and only if `x'` is a root of the minimal polynomial of
`x`. This is variant of `isConjRoot_iff_aeval_eq_zero`.
-/
theorem isConjRoot_iff_mem_minpoly_rootSet {x x' : S}
    (h : IsIntegral K x) : IsConjRoot K x x' ↔ x' ∈ (minpoly K x).rootSet S :=
  (isConjRoot_iff_mem_aroots h).trans (by simp [rootSet])

namespace IsConjRoot

theorem isIntegral {x x' : A} (hx : IsIntegral R x) (h : IsConjRoot R x x') :
    IsIntegral R x' :=
  ⟨minpoly R x, minpoly.monic hx, h ▸ minpoly.aeval R x'⟩

/--
A variant of `IsConjRoot.eq_of_isConjRoot_algebraMap`, only assuming `Nontrivial R`,
`NoZeroSMulDivisors R A` and `Function.Injective (algebraMap R A)` instead of `Field R`. If `x` is a
conjugate root of some element `r` in the base ring, then `x = r`.
-/
theorem eq_algebraMap' [Nontrivial R] [NoZeroSMulDivisors R S] {r : R} {x : S}
    (h : IsConjRoot R x (algebraMap R S r)) (hf : Function.Injective (algebraMap R S)) :
    x = algebraMap R S r := by
  rw [IsConjRoot, minpoly.eq_X_sub_C_of_algebraMap_inj _ hf] at h
  have : x ∈ (X - C r).aroots S := by
    rw [mem_aroots]
    simp [X_sub_C_ne_zero, h ▸ minpoly.aeval R x]
  simpa [aroots_X_sub_C] using this

/--
If `x` is a conjugate root of some element `r` in the base ring, then `x = r`.
-/
theorem eq_algebraMap {r : K} {x : S} (h : IsConjRoot K x (algebraMap K S r)) :
    x = algebraMap K S r :=
  eq_algebraMap' h (algebraMap K S).injective

/--
A variant of `IsConjRoot.eq_zero`, only assuming `Nontrivial R`,
`NoZeroSMulDivisors R A` and `Function.Injective (algebraMap R A)` instead of `Field R`. If `x` is a
conjugate root of `0`, then `x = 0`.
-/
theorem eq_zero' [Nontrivial R] [NoZeroSMulDivisors R S] {x : S} (h : IsConjRoot R x 0)
    (hf : Function.Injective (algebraMap R S)) : x = 0 :=
  (algebraMap R S).map_zero ▸ (eq_algebraMap' ((algebraMap R S).map_zero ▸ h) hf)

/--
If `x` is a conjugate root of `0`, then `x = 0`.
-/
theorem eq_zero {x : S} (h : IsConjRoot K x 0) : x = 0 :=
  eq_zero' h (algebraMap K S).injective

end IsConjRoot

/--
A variant of `IsConjRoot.iff_eq_zero'`, only assuming `Nontrivial R`,
`NoZeroSMulDivisors R A` and `Function.Injective (algebraMap R A)` instead of `Field R`. `x` is a
conjugate root of `0` if and only if `x = 0`.
-/
theorem isConjRoot_zero_iff_eq_zero' [Nontrivial R] {x : S} [NoZeroSMulDivisors R S]
    (hf : Function.Injective (algebraMap R S)) : IsConjRoot R x 0 ↔ x = 0 :=
  ⟨fun h => eq_zero' h hf, fun h => h.symm ▸ rfl⟩

/--
`x` is a conjugate root of `0` if and only if `x = 0`.
-/
@[simp]
theorem isConjRoot_zero_iff_eq_zero {x : S} : IsConjRoot K x 0 ↔ x = 0 :=
  isConjRoot_zero_iff_eq_zero' (algebraMap K S).injective

namespace IsConjRoot

/--
A variant of `IsConjRoot.ne_zero'`, only assuming `Nontrivial R`,
`NoZeroSMulDivisors R A` and `Function.Injective (algebraMap R A)` instead of `Field R`. If `x'` is
a conjugate root of a nonzero element `x`, then `x'` is not zero.
-/
theorem ne_zero' [Nontrivial R] [NoZeroSMulDivisors R S] {x x' : S} (hx : x ≠ 0)
    (h : IsConjRoot R x x') (hf : Function.Injective (algebraMap R S)) : x' ≠ 0 :=
  fun h' => hx (eq_zero' (h' ▸ h) hf)

/--
If `x'` is a conjugate root of a nonzero element `x`, then `x'` is not zero.
-/
theorem ne_zero {x x' : S} (hx : x ≠ 0) (h : IsConjRoot K x x') : x' ≠ 0 :=
  ne_zero' hx h (algebraMap K S).injective

end IsConjRoot

/--
Let `L / K` be a field extension. If `x` is a separable element over `K` and the minimal polynomial
of `x` splits in `L`, then `x` is not in the `K` iff there exists a different conjugate root of `x`
in `L` over `K`.
-/
theorem not_mem_iff_exists_ne_and_isConjRoot {x : L} (h : IsSeparable K x)
    (sp : (minpoly K x).Splits (algebraMap K L)) :
    x ∉ (⊥ : Subalgebra K L) ↔ ∃ x' : L, x ≠ x' ∧ IsConjRoot K x x' := by
  calc
    _ ↔ 2 ≤ (minpoly K x).natDegree := (minpoly.two_le_natDegree_iff h.isIntegral).symm
    _ ↔ 2 ≤ Fintype.card ((minpoly K x).rootSet L) :=
      (Polynomial.card_rootSet_eq_natDegree h sp) ▸ Iff.rfl
    _ ↔ Nontrivial ((minpoly K x).rootSet L) := Fintype.one_lt_card_iff_nontrivial
    _ ↔ ∃ x' : ((minpoly K x).rootSet L), ↑x' ≠ x :=
      (nontrivial_iff_exists_ne ⟨x, mem_rootSet.mpr ⟨minpoly.ne_zero h.isIntegral,
          minpoly.aeval K x⟩⟩).trans ⟨fun ⟨x', hx'⟩ => ⟨x', Subtype.coe_ne_coe.mpr hx'⟩,
          fun ⟨x', hx'⟩ => ⟨x', Subtype.coe_ne_coe.mp hx'⟩⟩
    _ ↔ _ :=
      ⟨fun ⟨⟨x', hx'⟩, hne⟩ => ⟨x', ⟨hne.symm,
          (isConjRoot_iff_mem_minpoly_rootSet h.isIntegral).mpr hx'⟩⟩,
          fun ⟨x', hne, hx'⟩ => ⟨⟨x',
          (isConjRoot_iff_mem_minpoly_rootSet h.isIntegral).mp hx'⟩, hne.symm⟩⟩
