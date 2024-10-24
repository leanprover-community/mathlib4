/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.IntegralNormalization
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Algebraic elements and algebraic extensions

An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial.
An R-algebra is algebraic over R if and only if all its elements are algebraic over R.
The main result in this file proves transitivity of algebraicity:
a tower of algebraic field extensions is algebraic.
-/


universe u v w

open scoped Classical
open Polynomial

section

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- An element of an R-algebra is algebraic over R if it is a root of a nonzero polynomial
with coefficients in R. -/
def IsAlgebraic (x : A) : Prop :=
  ∃ p : R[X], p ≠ 0 ∧ aeval x p = 0

/-- An element of an R-algebra is transcendental over R if it is not algebraic over R. -/
def Transcendental (x : A) : Prop :=
  ¬IsAlgebraic R x

theorem is_transcendental_of_subsingleton [Subsingleton R] (x : A) : Transcendental R x :=
  fun ⟨p, h, _⟩ => h <| Subsingleton.elim p 0

variable {R}

/-- An element `x` is transcendental over `R` if and only if for any polynomial `p`,
`Polynomial.aeval x p = 0` implies `p = 0`. This is similar to `algebraicIndependent_iff`. -/
theorem transcendental_iff {x : A} :
    Transcendental R x ↔ ∀ p : R[X], aeval x p = 0 → p = 0 := by
  rw [Transcendental, IsAlgebraic, not_exists]
  congr! 1; tauto

variable (R) in
theorem Polynomial.transcendental_X : Transcendental R (X (R := R)) := by
  simp [transcendental_iff]

theorem IsAlgebraic.of_aeval {r : A} (f : R[X]) (hf : f.natDegree ≠ 0)
    (hf' : f.leadingCoeff ∈ nonZeroDivisors R) (H : IsAlgebraic R (aeval r f)) :
    IsAlgebraic R r := by
  obtain ⟨p, h1, h2⟩ := H
  have : (p.comp f).coeff (p.natDegree * f.natDegree) ≠ 0 := fun h ↦ h1 <| by
    rwa [coeff_comp_degree_mul_degree hf,
      mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hf' _),
      leadingCoeff_eq_zero] at h
  exact ⟨p.comp f, fun h ↦ this (by simp [h]), by rwa [aeval_comp]⟩

theorem Transcendental.aeval {r : A} (H : Transcendental R r) (f : R[X]) (hf : f.natDegree ≠ 0)
    (hf' : f.leadingCoeff ∈ nonZeroDivisors R) :
    Transcendental R (aeval r f) := fun h ↦ H (h.of_aeval f hf hf')

theorem Polynomial.transcendental (f : R[X]) (hf : f.natDegree ≠ 0)
    (hf' : f.leadingCoeff ∈ nonZeroDivisors R) :
    Transcendental R f := by
  simpa using (transcendental_X R).aeval f hf hf'

/-- If `E / F` is a field extension, `x` is an element of `E` transcendental over `F`,
then `{(x - a)⁻¹ | a : F}` is linearly independent over `F`. -/
theorem Transcendental.linearIndependent_sub_inv
    {F E : Type*} [Field F] [Field E] [Algebra F E] {x : E} (H : Transcendental F x) :
    LinearIndependent F fun a ↦ (x - algebraMap F E a)⁻¹ := by
  rw [transcendental_iff] at H
  refine linearIndependent_iff'.2 fun s m hm i hi ↦ ?_
  have hnz (a : F) : x - algebraMap F E a ≠ 0 := fun h ↦
    X_sub_C_ne_zero a <| H (.X - .C a) (by simp [h])
  let b := s.prod fun j ↦ x - algebraMap F E j
  have h1 : ∀ i ∈ s, m i • (b * (x - algebraMap F E i)⁻¹) =
      m i • (s.erase i).prod fun j ↦ x - algebraMap F E j := fun i hi ↦ by
    simp_rw [b, ← s.prod_erase_mul _ hi, mul_inv_cancel_right₀ (hnz i)]
  replace hm := congr(b * $(hm))
  simp_rw [mul_zero, Finset.mul_sum, mul_smul_comm, Finset.sum_congr rfl h1] at hm
  let p : Polynomial F := s.sum fun i ↦ .C (m i) * (s.erase i).prod fun j ↦ .X - .C j
  replace hm := congr(Polynomial.aeval i $(H p (by simp_rw [← hm, p, map_sum, map_mul, map_prod,
    map_sub, aeval_X, aeval_C, Algebra.smul_def])))
  have h2 : ∀ j ∈ s.erase i, m j * ((s.erase j).prod fun x ↦ i - x) = 0 := fun j hj ↦ by
    have := Finset.mem_erase_of_ne_of_mem (Finset.ne_of_mem_erase hj).symm hi
    simp_rw [← (s.erase j).prod_erase_mul _ this, sub_self, mul_zero]
  simp_rw [map_zero, p, map_sum, map_mul, map_prod, map_sub, aeval_X,
    aeval_C, Algebra.id.map_eq_self, ← s.sum_erase_add _ hi,
    Finset.sum_eq_zero h2, zero_add] at hm
  exact eq_zero_of_ne_zero_of_mul_right_eq_zero (Finset.prod_ne_zero_iff.2 fun j hj ↦
    sub_ne_zero.2 (Finset.ne_of_mem_erase hj).symm) hm

/-- A subalgebra is algebraic if all its elements are algebraic. -/
nonrec
def Subalgebra.IsAlgebraic (S : Subalgebra R A) : Prop :=
  ∀ x ∈ S, IsAlgebraic R x

variable (R A)

/-- An algebra is algebraic if all its elements are algebraic. -/
protected class Algebra.IsAlgebraic : Prop where
  isAlgebraic : ∀ x : A, IsAlgebraic R x

/-- An algebra is transcendental if some element is transcendental. -/
protected class Algebra.Transcendental : Prop where
  transcendental : ∃ x : A, Transcendental R x

variable {R A}

lemma Algebra.isAlgebraic_def : Algebra.IsAlgebraic R A ↔ ∀ x : A, IsAlgebraic R x :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma Algebra.transcendental_def : Algebra.Transcendental R A ↔ ∃ x : A, Transcendental R x :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

theorem Algebra.transcendental_iff_not_isAlgebraic :
    Algebra.Transcendental R A ↔ ¬ Algebra.IsAlgebraic R A := by
  simp [isAlgebraic_def, transcendental_def, Transcendental]

/-- A subalgebra is algebraic if and only if it is algebraic as an algebra. -/
theorem Subalgebra.isAlgebraic_iff (S : Subalgebra R A) :
    S.IsAlgebraic ↔ Algebra.IsAlgebraic R S := by
  delta Subalgebra.IsAlgebraic
  rw [Subtype.forall', Algebra.isAlgebraic_def]
  refine forall_congr' fun x => exists_congr fun p => and_congr Iff.rfl ?_
  have h : Function.Injective S.val := Subtype.val_injective
  conv_rhs => rw [← h.eq_iff, map_zero]
  rw [← aeval_algHom_apply, S.val_apply]

/-- An algebra is algebraic if and only if it is algebraic as a subalgebra. -/
theorem Algebra.isAlgebraic_iff : Algebra.IsAlgebraic R A ↔ (⊤ : Subalgebra R A).IsAlgebraic := by
  delta Subalgebra.IsAlgebraic
  simp only [Algebra.isAlgebraic_def, Algebra.mem_top, forall_prop_of_true]

theorem isAlgebraic_iff_not_injective {x : A} :
    IsAlgebraic R x ↔ ¬Function.Injective (Polynomial.aeval x : R[X] →ₐ[R] A) := by
  simp only [IsAlgebraic, injective_iff_map_eq_zero, not_forall, and_comm, exists_prop]

/-- An element `x` is transcendental over `R` if and only if the map `Polynomial.aeval x`
is injective. This is similar to `algebraicIndependent_iff_injective_aeval`. -/
theorem transcendental_iff_injective {x : A} :
    Transcendental R x ↔ Function.Injective (Polynomial.aeval x : R[X] →ₐ[R] A) :=
  isAlgebraic_iff_not_injective.not_left

/-- An element `x` is transcendental over `R` if and only if the kernel of the ring homomorphism
`Polynomial.aeval x` is the zero ideal. This is similar to `algebraicIndependent_iff_ker_eq_bot`. -/
theorem transcendental_iff_ker_eq_bot {x : A} :
    Transcendental R x ↔ RingHom.ker (aeval (R := R) x) = ⊥ := by
  rw [transcendental_iff_injective, RingHom.injective_iff_ker_eq_bot]

end

section zero_ne_one

variable {R : Type u} {S : Type*} {A : Type v} [CommRing R]
variable [CommRing S] [Ring A] [Algebra R A] [Algebra R S] [Algebra S A]
variable [IsScalarTower R S A]

/-- An integral element of an algebra is algebraic. -/
theorem IsIntegral.isAlgebraic [Nontrivial R] {x : A} : IsIntegral R x → IsAlgebraic R x :=
  fun ⟨p, hp, hpx⟩ => ⟨p, hp.ne_zero, hpx⟩

instance Algebra.IsIntegral.isAlgebraic [Nontrivial R] [Algebra.IsIntegral R A] :
    Algebra.IsAlgebraic R A := ⟨fun a ↦ (Algebra.IsIntegral.isIntegral a).isAlgebraic⟩

theorem isAlgebraic_zero [Nontrivial R] : IsAlgebraic R (0 : A) :=
  ⟨_, X_ne_zero, aeval_X 0⟩

/-- An element of `R` is algebraic, when viewed as an element of the `R`-algebra `A`. -/
theorem isAlgebraic_algebraMap [Nontrivial R] (x : R) : IsAlgebraic R (algebraMap R A x) :=
  ⟨_, X_sub_C_ne_zero x, by rw [map_sub, aeval_X, aeval_C, sub_self]⟩

theorem isAlgebraic_one [Nontrivial R] : IsAlgebraic R (1 : A) := by
  rw [← map_one (algebraMap R A)]
  exact isAlgebraic_algebraMap 1

theorem isAlgebraic_nat [Nontrivial R] (n : ℕ) : IsAlgebraic R (n : A) := by
  rw [← map_natCast (_ : R →+* A) n]
  exact isAlgebraic_algebraMap (Nat.cast n)

theorem isAlgebraic_int [Nontrivial R] (n : ℤ) : IsAlgebraic R (n : A) := by
  rw [← map_intCast (algebraMap R A)]
  exact isAlgebraic_algebraMap (Int.cast n)

theorem isAlgebraic_rat (R : Type u) {A : Type v} [DivisionRing A] [Field R] [Algebra R A] (n : ℚ) :
    IsAlgebraic R (n : A) := by
  rw [← map_ratCast (algebraMap R A)]
  exact isAlgebraic_algebraMap (Rat.cast n)

theorem isAlgebraic_of_mem_rootSet {R : Type u} {A : Type v} [Field R] [Field A] [Algebra R A]
    {p : R[X]} {x : A} (hx : x ∈ p.rootSet A) : IsAlgebraic R x :=
  ⟨p, ne_zero_of_mem_rootSet hx, aeval_eq_zero_of_mem_rootSet hx⟩

open IsScalarTower

protected theorem IsAlgebraic.algebraMap {a : S} :
    IsAlgebraic R a → IsAlgebraic R (algebraMap S A a) := fun ⟨f, hf₁, hf₂⟩ =>
  ⟨f, hf₁, by rw [aeval_algebraMap_apply, hf₂, map_zero]⟩

section

variable {B} [Ring B] [Algebra R B]

/-- This is slightly more general than `IsAlgebraic.algebraMap` in that it
  allows noncommutative intermediate rings `A`. -/
protected theorem IsAlgebraic.algHom (f : A →ₐ[R] B) {a : A}
    (h : IsAlgebraic R a) : IsAlgebraic R (f a) :=
  let ⟨p, hp, ha⟩ := h
  ⟨p, hp, by rw [aeval_algHom, f.comp_apply, ha, map_zero]⟩

theorem isAlgebraic_algHom_iff (f : A →ₐ[R] B) (hf : Function.Injective f)
    {a : A} : IsAlgebraic R (f a) ↔ IsAlgebraic R a :=
  ⟨fun ⟨p, hp0, hp⟩ ↦ ⟨p, hp0, hf <| by rwa [map_zero, ← f.comp_apply, ← aeval_algHom]⟩,
    IsAlgebraic.algHom f⟩

theorem Algebra.IsAlgebraic.of_injective (f : A →ₐ[R] B) (hf : Function.Injective f)
    [Algebra.IsAlgebraic R B] : Algebra.IsAlgebraic R A :=
  ⟨fun _ ↦ (isAlgebraic_algHom_iff f hf).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩

/-- Transfer `Algebra.IsAlgebraic` across an `AlgEquiv`. -/
theorem AlgEquiv.isAlgebraic (e : A ≃ₐ[R] B)
    [Algebra.IsAlgebraic R A] : Algebra.IsAlgebraic R B :=
  Algebra.IsAlgebraic.of_injective e.symm.toAlgHom e.symm.injective

theorem AlgEquiv.isAlgebraic_iff (e : A ≃ₐ[R] B) :
    Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic R B :=
  ⟨fun _ ↦ e.isAlgebraic, fun _ ↦ e.symm.isAlgebraic⟩

end

theorem isAlgebraic_algebraMap_iff {a : S} (h : Function.Injective (algebraMap S A)) :
    IsAlgebraic R (algebraMap S A a) ↔ IsAlgebraic R a :=
  isAlgebraic_algHom_iff (IsScalarTower.toAlgHom R S A) h

theorem transcendental_algebraMap_iff {a : S} (h : Function.Injective (algebraMap S A)) :
    Transcendental R (algebraMap S A a) ↔ Transcendental R a := by
  simp_rw [Transcendental, isAlgebraic_algebraMap_iff h]

theorem IsAlgebraic.of_pow {r : A} {n : ℕ} (hn : 0 < n) (ht : IsAlgebraic R (r ^ n)) :
    IsAlgebraic R r := by
  obtain ⟨p, p_nonzero, hp⟩ := ht
  refine ⟨Polynomial.expand _ n p, ?_, ?_⟩
  · rwa [Polynomial.expand_ne_zero hn]
  · rwa [Polynomial.expand_aeval n p r]

theorem Transcendental.pow {r : A} (ht : Transcendental R r) {n : ℕ} (hn : 0 < n) :
    Transcendental R (r ^ n) := fun ht' ↦ ht <| ht'.of_pow hn

lemma IsAlgebraic.invOf {x : S} [Invertible x] (h : IsAlgebraic R x) : IsAlgebraic R (⅟ x) := by
  obtain ⟨p, hp, hp'⟩ := h
  refine ⟨p.reverse, by simpa using hp, ?_⟩
  rwa [Polynomial.aeval_def, Polynomial.eval₂_reverse_eq_zero_iff, ← Polynomial.aeval_def]

lemma IsAlgebraic.invOf_iff {x : S} [Invertible x] :
    IsAlgebraic R (⅟ x) ↔ IsAlgebraic R x :=
  ⟨IsAlgebraic.invOf, IsAlgebraic.invOf⟩

lemma IsAlgebraic.inv_iff {K} [Field K] [Algebra R K] {x : K} :
    IsAlgebraic R (x⁻¹) ↔ IsAlgebraic R x := by
  by_cases hx : x = 0
  · simp [hx]
  letI := invertibleOfNonzero hx
  exact IsAlgebraic.invOf_iff (R := R) (x := x)

alias ⟨_, IsAlgebraic.inv⟩ := IsAlgebraic.inv_iff

end zero_ne_one

section Field

variable {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]

/-- An element of an algebra over a field is algebraic if and only if it is integral. -/
theorem isAlgebraic_iff_isIntegral {x : A} : IsAlgebraic K x ↔ IsIntegral K x := by
  refine ⟨?_, IsIntegral.isAlgebraic⟩
  rintro ⟨p, hp, hpx⟩
  refine ⟨_, monic_mul_leadingCoeff_inv hp, ?_⟩
  rw [← aeval_def, map_mul, hpx, zero_mul]

protected theorem Algebra.isAlgebraic_iff_isIntegral :
    Algebra.IsAlgebraic K A ↔ Algebra.IsIntegral K A := by
  rw [Algebra.isAlgebraic_def, Algebra.isIntegral_def,
      forall_congr' fun _ ↦ isAlgebraic_iff_isIntegral]

alias ⟨IsAlgebraic.isIntegral, _⟩ := isAlgebraic_iff_isIntegral

/-- This used to be an `alias` of `Algebra.isAlgebraic_iff_isIntegral` but that would make
`Algebra.IsAlgebraic K A` an explicit parameter instead of instance implicit. -/
protected instance Algebra.IsAlgebraic.isIntegral [Algebra.IsAlgebraic K A] :
    Algebra.IsIntegral K A := Algebra.isAlgebraic_iff_isIntegral.mp ‹_›

end Field

section

variable {K L R S A : Type*}

section Ring

section CommRing

variable [CommRing R] [CommRing S] [Ring A]
variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/-- If x is algebraic over R, then x is algebraic over S when S is an extension of R,
  and the map from `R` to `S` is injective. -/
theorem IsAlgebraic.tower_top_of_injective
    (hinj : Function.Injective (algebraMap R S)) {x : A}
    (A_alg : IsAlgebraic R x) : IsAlgebraic S x :=
  let ⟨p, hp₁, hp₂⟩ := A_alg
  ⟨p.map (algebraMap _ _), by
    rwa [Ne, ← degree_eq_bot, degree_map_eq_of_injective hinj, degree_eq_bot], by simpa⟩

/-- If A is an algebraic algebra over R, then A is algebraic over S when S is an extension of R,
  and the map from `R` to `S` is injective. -/
theorem Algebra.IsAlgebraic.tower_top_of_injective (hinj : Function.Injective (algebraMap R S))
    [Algebra.IsAlgebraic R A] : Algebra.IsAlgebraic S A :=
  ⟨fun _ ↦ _root_.IsAlgebraic.tower_top_of_injective hinj (Algebra.IsAlgebraic.isAlgebraic _)⟩

theorem Algebra.IsAlgebraic.tower_bot_of_injective [Algebra.IsAlgebraic R A]
    (hinj : Function.Injective (algebraMap S A)) :
    Algebra.IsAlgebraic R S where
  isAlgebraic x := by
    simpa [isAlgebraic_algebraMap_iff hinj] using isAlgebraic (R := R) (A := A) (algebraMap _ _ x)

end CommRing

section Field

variable [Field K] [Field L] [Ring A]
variable [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]
variable (L)

/-- If x is algebraic over K, then x is algebraic over L when L is an extension of K -/
theorem IsAlgebraic.tower_top {x : A} (A_alg : IsAlgebraic K x) :
    IsAlgebraic L x :=
  A_alg.tower_top_of_injective (algebraMap K L).injective

/-- If A is an algebraic algebra over K, then A is algebraic over L when L is an extension of K -/
theorem Algebra.IsAlgebraic.tower_top [Algebra.IsAlgebraic K A] : Algebra.IsAlgebraic L A :=
  Algebra.IsAlgebraic.tower_top_of_injective (algebraMap K L).injective

variable (K)

theorem IsAlgebraic.of_finite (e : A) [FiniteDimensional K A] : IsAlgebraic K e :=
  (IsIntegral.of_finite K e).isAlgebraic

variable (A)

/-- A field extension is algebraic if it is finite. -/
instance Algebra.IsAlgebraic.of_finite [FiniteDimensional K A] : Algebra.IsAlgebraic K A :=
  (IsIntegral.of_finite K A).isAlgebraic

theorem Algebra.IsAlgebraic.tower_bot (K L A : Type*) [CommRing K] [Field L] [Ring A]
    [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]
    [Nontrivial A] [Algebra.IsAlgebraic K A] :
    Algebra.IsAlgebraic K L :=
  tower_bot_of_injective (algebraMap L A).injective

end Field

end Ring

section CommRing

variable [Field K] [Field L] [Ring A]
variable [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]

/-- If L is an algebraic field extension of K and A is an algebraic algebra over L,
then A is algebraic over K. -/
protected theorem Algebra.IsAlgebraic.trans
    [L_alg : Algebra.IsAlgebraic K L] [A_alg : Algebra.IsAlgebraic L A] :
    Algebra.IsAlgebraic K A := by
  rw [Algebra.isAlgebraic_iff_isIntegral] at L_alg A_alg ⊢
  exact Algebra.IsIntegral.trans L

end CommRing

section NoZeroSMulDivisors

namespace Algebra.IsAlgebraic

variable [CommRing K] [Field L]
variable [Algebra K L]

theorem algHom_bijective [NoZeroSMulDivisors K L] [Algebra.IsAlgebraic K L] (f : L →ₐ[K] L) :
    Function.Bijective f := by
  refine ⟨f.injective, fun b ↦ ?_⟩
  obtain ⟨p, hp, he⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) b
  let f' : p.rootSet L → p.rootSet L := (rootSet_maps_to' (fun x ↦ x) f).restrict f _ _
  have : f'.Surjective := Finite.injective_iff_surjective.1
    fun _ _ h ↦ Subtype.eq <| f.injective <| Subtype.ext_iff.1 h
  obtain ⟨a, ha⟩ := this ⟨b, mem_rootSet.2 ⟨hp, he⟩⟩
  exact ⟨a, Subtype.ext_iff.1 ha⟩

theorem algHom_bijective₂ [NoZeroSMulDivisors K L] [Field R] [Algebra K R]
    [Algebra.IsAlgebraic K L] (f : L →ₐ[K] R) (g : R →ₐ[K] L) :
    Function.Bijective f ∧ Function.Bijective g :=
  (g.injective.bijective₂_of_surjective f.injective (algHom_bijective <| g.comp f).2).symm

theorem bijective_of_isScalarTower [NoZeroSMulDivisors K L] [Algebra.IsAlgebraic K L]
    [Field R] [Algebra K R] [Algebra L R] [IsScalarTower K L R] (f : R →ₐ[K] L) :
    Function.Bijective f :=
  (algHom_bijective₂ (IsScalarTower.toAlgHom K L R) f).2

theorem bijective_of_isScalarTower' [Field R] [Algebra K R]
    [NoZeroSMulDivisors K R]
    [Algebra.IsAlgebraic K R] [Algebra L R] [IsScalarTower K L R] (f : R →ₐ[K] L) :
    Function.Bijective f :=
  (algHom_bijective₂ f (IsScalarTower.toAlgHom K L R)).1

variable (K L)

/-- Bijection between algebra equivalences and algebra homomorphisms -/
@[simps]
noncomputable def algEquivEquivAlgHom [NoZeroSMulDivisors K L] [Algebra.IsAlgebraic K L] :
    (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) where
  toFun ϕ := ϕ.toAlgHom
  invFun ϕ := AlgEquiv.ofBijective ϕ (algHom_bijective ϕ)
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := rfl

end Algebra.IsAlgebraic

end NoZeroSMulDivisors

section Field

variable [Field K] [Field L]
variable [Algebra K L]

theorem AlgHom.bijective [FiniteDimensional K L] (ϕ : L →ₐ[K] L) : Function.Bijective ϕ :=
  (Algebra.IsAlgebraic.of_finite K L).algHom_bijective ϕ

variable (K L)

/-- Bijection between algebra equivalences and algebra homomorphisms -/
noncomputable abbrev algEquivEquivAlgHom [FiniteDimensional K L] :
    (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) :=
  Algebra.IsAlgebraic.algEquivEquivAlgHom K L

end Field

end

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]

theorem exists_integral_multiple [Algebra R S] {z : S} (hz : IsAlgebraic R z)
    (inj : ∀ x, algebraMap R S x = 0 → x = 0) :
    ∃ᵉ (x : integralClosure R S) (y ≠ (0 : R)), z * algebraMap R S y = x := by
  rcases hz with ⟨p, p_ne_zero, px⟩
  set a := p.leadingCoeff
  have a_ne_zero : a ≠ 0 := mt Polynomial.leadingCoeff_eq_zero.mp p_ne_zero
  have x_integral : IsIntegral R (z * algebraMap R S a) :=
    ⟨p.integralNormalization, monic_integralNormalization p_ne_zero,
      integralNormalization_aeval_eq_zero px inj⟩
  exact ⟨⟨_, x_integral⟩, a, a_ne_zero, rfl⟩

/-- A fraction `(a : S) / (b : S)` can be reduced to `(c : S) / (d : R)`,
if `S` is the integral closure of `R` in an algebraic extension `L` of `R`. -/
theorem IsIntegralClosure.exists_smul_eq_mul {L : Type*} [Field L] [Algebra R S] [Algebra S L]
    [Algebra R L] [IsScalarTower R S L] [IsIntegralClosure S R L] [Algebra.IsAlgebraic R L]
    (inj : Function.Injective (algebraMap R L)) (a : S) {b : S} (hb : b ≠ 0) :
    ∃ᵉ (c : S) (d ≠ (0 : R)), d • a = b * c := by
  obtain ⟨c, d, d_ne, hx⟩ :=
    exists_integral_multiple (Algebra.IsAlgebraic.isAlgebraic (algebraMap _ L a / algebraMap _ L b))
      ((injective_iff_map_eq_zero _).mp inj)
  refine
    ⟨IsIntegralClosure.mk' S (c : L) c.2, d, d_ne, IsIntegralClosure.algebraMap_injective S R L ?_⟩
  simp only [Algebra.smul_def, RingHom.map_mul, IsIntegralClosure.algebraMap_mk', ← hx, ←
    IsScalarTower.algebraMap_apply]
  rw [← mul_assoc _ (_ / _), mul_div_cancel₀ (algebraMap S L a), mul_comm]
  exact mt ((injective_iff_map_eq_zero _).mp (IsIntegralClosure.algebraMap_injective S R L) _) hb

section Field

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : Subalgebra K L)

theorem inv_eq_of_aeval_divX_ne_zero {x : L} {p : K[X]} (aeval_ne : aeval x (divX p) ≠ 0) :
    x⁻¹ = aeval x (divX p) / (aeval x p - algebraMap _ _ (p.coeff 0)) := by
  rw [inv_eq_iff_eq_inv, inv_div, eq_comm, div_eq_iff, sub_eq_iff_eq_add, mul_comm]
  conv_lhs => rw [← divX_mul_X_add p]
  · rw [map_add, map_mul, aeval_X, aeval_C]
  · exact aeval_ne

theorem inv_eq_of_root_of_coeff_zero_ne_zero {x : L} {p : K[X]} (aeval_eq : aeval x p = 0)
    (coeff_zero_ne : p.coeff 0 ≠ 0) : x⁻¹ = -(aeval x (divX p) / algebraMap _ _ (p.coeff 0)) := by
  convert inv_eq_of_aeval_divX_ne_zero (p := p) (L := L)
    (mt (fun h => (algebraMap K L).injective ?_) coeff_zero_ne) using 1
  · rw [aeval_eq, zero_sub, div_neg]
  rw [RingHom.map_zero]
  convert aeval_eq
  conv_rhs => rw [← divX_mul_X_add p]
  rw [map_add, map_mul, h, zero_mul, zero_add, aeval_C]

theorem Subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero {x : A} {p : K[X]}
    (aeval_eq : aeval x p = 0) (coeff_zero_ne : p.coeff 0 ≠ 0) : (x⁻¹ : L) ∈ A := by
  suffices (x⁻¹ : L) = (-p.coeff 0)⁻¹ • aeval x (divX p) by
    rw [this]
    exact A.smul_mem (aeval x _).2 _
  have : aeval (x : L) p = 0 := by rw [Subalgebra.aeval_coe, aeval_eq, Subalgebra.coe_zero]
  -- Porting note: this was a long sequence of `rw`.
  rw [inv_eq_of_root_of_coeff_zero_ne_zero this coeff_zero_ne, div_eq_inv_mul, Algebra.smul_def]
  simp only [aeval_coe, Submonoid.coe_mul, Subsemiring.coe_toSubmonoid, coe_toSubsemiring,
    coe_algebraMap]
  rw [map_inv₀, map_neg, inv_neg, neg_mul]

theorem Subalgebra.inv_mem_of_algebraic {x : A} (hx : _root_.IsAlgebraic K (x : L)) :
    (x⁻¹ : L) ∈ A := by
  obtain ⟨p, ne_zero, aeval_eq⟩ := hx
  rw [Subalgebra.aeval_coe, Subalgebra.coe_eq_zero] at aeval_eq
  revert ne_zero aeval_eq
  refine p.recOnHorner ?_ ?_ ?_
  · intro h
    contradiction
  · intro p a hp ha _ih _ne_zero aeval_eq
    refine A.inv_mem_of_root_of_coeff_zero_ne_zero aeval_eq ?_
    rwa [coeff_add, hp, zero_add, coeff_C, if_pos rfl]
  · intro p hp ih _ne_zero aeval_eq
    rw [map_mul, aeval_X, mul_eq_zero] at aeval_eq
    cases' aeval_eq with aeval_eq x_eq
    · exact ih hp aeval_eq
    · rw [x_eq, Subalgebra.coe_zero, inv_zero]
      exact A.zero_mem

/-- In an algebraic extension L/K, an intermediate subalgebra is a field. -/
theorem Subalgebra.isField_of_algebraic [Algebra.IsAlgebraic K L] : IsField A :=
  { show Nontrivial A by infer_instance, Subalgebra.toCommRing A with
    mul_inv_cancel := fun {a} ha =>
      ⟨⟨a⁻¹, A.inv_mem_of_algebraic (Algebra.IsAlgebraic.isAlgebraic (a : L))⟩,
        Subtype.ext (mul_inv_cancel₀ (mt (Subalgebra.coe_eq_zero _).mp ha))⟩ }

end Field

section Pi

variable (R' : Type u) (S' : Type v) (T' : Type w)

/-- This is not an instance as it forms a diamond with `Pi.instSMul`.

See the `instance_diamonds` test for details. -/
def Polynomial.hasSMulPi [Semiring R'] [SMul R' S'] : SMul R'[X] (R' → S') :=
  ⟨fun p f x => eval x p • f x⟩

/-- This is not an instance as it forms a diamond with `Pi.instSMul`.

See the `instance_diamonds` test for details. -/
noncomputable def Polynomial.hasSMulPi' [CommSemiring R'] [Semiring S'] [Algebra R' S']
    [SMul S' T'] : SMul R'[X] (S' → T') :=
  ⟨fun p f x => aeval x p • f x⟩

attribute [local instance] Polynomial.hasSMulPi Polynomial.hasSMulPi'

@[simp]
theorem polynomial_smul_apply [Semiring R'] [SMul R' S'] (p : R'[X]) (f : R' → S') (x : R') :
    (p • f) x = eval x p • f x :=
  rfl

@[simp]
theorem polynomial_smul_apply' [CommSemiring R'] [Semiring S'] [Algebra R' S'] [SMul S' T']
    (p : R'[X]) (f : S' → T') (x : S') : (p • f) x = aeval x p • f x :=
  rfl

variable [CommSemiring R'] [CommSemiring S'] [CommSemiring T'] [Algebra R' S'] [Algebra S' T']

-- Porting note: the proofs in this definition used `funext` in term-mode, but I was not able
-- to get them to work anymore.
/-- This is not an instance for the same reasons as `Polynomial.hasSMulPi'`. -/
noncomputable def Polynomial.algebraPi : Algebra R'[X] (S' → T') :=
  { Polynomial.hasSMulPi' R' S' T' with
    toFun := fun p z => algebraMap S' T' (aeval z p)
    map_one' := by
      funext z
      simp only [Polynomial.aeval_one, Pi.one_apply, map_one]
    map_mul' := fun f g => by
      funext z
      simp only [Pi.mul_apply, map_mul]
    map_zero' := by
      funext z
      simp only [Polynomial.aeval_zero, Pi.zero_apply, map_zero]
    map_add' := fun f g => by
      funext z
      simp only [Polynomial.aeval_add, Pi.add_apply, map_add]
    commutes' := fun p f => by
      funext z
      exact mul_comm _ _
    smul_def' := fun p f => by
      funext z
      simp only [polynomial_smul_apply', Algebra.algebraMap_eq_smul_one, RingHom.coe_mk,
        MonoidHom.coe_mk, OneHom.coe_mk, Pi.mul_apply, Algebra.smul_mul_assoc, one_mul] }

attribute [local instance] Polynomial.algebraPi

@[simp]
theorem Polynomial.algebraMap_pi_eq_aeval :
    (algebraMap R'[X] (S' → T') : R'[X] → S' → T') = fun p z => algebraMap _ _ (aeval z p) :=
  rfl

@[simp]
theorem Polynomial.algebraMap_pi_self_eq_eval :
    (algebraMap R'[X] (R' → R') : R'[X] → R' → R') = fun p z => eval z p :=
  rfl

end Pi
