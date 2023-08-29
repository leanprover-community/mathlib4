/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.RingTheory.IntegralClosure
import Mathlib.RingTheory.Polynomial.IntegralNormalization

#align_import ring_theory.algebraic from "leanprover-community/mathlib"@"2196ab363eb097c008d4497125e0dde23fb36db2"

/-!
# Algebraic elements and algebraic extensions

An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial.
An R-algebra is algebraic over R if and only if all its elements are algebraic over R.
The main result in this file proves transitivity of algebraicity:
a tower of algebraic field extensions is algebraic.
-/


universe u v w

open Classical Polynomial

section

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- An element of an R-algebra is algebraic over R if it is a root of a nonzero polynomial
with coefficients in R. -/
def IsAlgebraic (x : A) : Prop :=
  ∃ p : R[X], p ≠ 0 ∧ aeval x p = 0
#align is_algebraic IsAlgebraic

/-- An element of an R-algebra is transcendental over R if it is not algebraic over R. -/
def Transcendental (x : A) : Prop :=
  ¬IsAlgebraic R x
#align transcendental Transcendental

theorem is_transcendental_of_subsingleton [Subsingleton R] (x : A) : Transcendental R x :=
  fun ⟨p, h, _⟩ => h <| Subsingleton.elim p 0
#align is_transcendental_of_subsingleton is_transcendental_of_subsingleton

variable {R}

/-- A subalgebra is algebraic if all its elements are algebraic. -/
nonrec
def Subalgebra.IsAlgebraic (S : Subalgebra R A) : Prop :=
  ∀ x ∈ S, IsAlgebraic R x
#align subalgebra.is_algebraic Subalgebra.IsAlgebraic

variable (R A)

/-- An algebra is algebraic if all its elements are algebraic. -/
nonrec
def Algebra.IsAlgebraic : Prop :=
  ∀ x : A, IsAlgebraic R x
#align algebra.is_algebraic Algebra.IsAlgebraic

variable {R A}

/-- A subalgebra is algebraic if and only if it is algebraic as an algebra. -/
theorem Subalgebra.isAlgebraic_iff (S : Subalgebra R A) :
    S.IsAlgebraic ↔ @Algebra.IsAlgebraic R S _ _ S.algebra := by
  delta Algebra.IsAlgebraic Subalgebra.IsAlgebraic
  -- ⊢ (∀ (x : A), x ∈ S → _root_.IsAlgebraic R x) ↔ ∀ (x : { x // x ∈ S }), _root_ …
  rw [Subtype.forall']
  -- ⊢ (∀ (x : { a // a ∈ S }), _root_.IsAlgebraic R ↑x) ↔ ∀ (x : { x // x ∈ S }),  …
  refine' forall_congr' fun x => exists_congr fun p => and_congr Iff.rfl _
  -- ⊢ ↑(aeval ↑x) p = 0 ↔ ↑(aeval x) p = 0
  have h : Function.Injective S.val := Subtype.val_injective
  -- ⊢ ↑(aeval ↑x) p = 0 ↔ ↑(aeval x) p = 0
  conv_rhs => rw [← h.eq_iff, AlgHom.map_zero]
  -- ⊢ ↑(aeval ↑x) p = 0 ↔ ↑(val S) (↑(aeval x) p) = 0
  rw [← aeval_algHom_apply, S.val_apply]
  -- 🎉 no goals
#align subalgebra.is_algebraic_iff Subalgebra.isAlgebraic_iff

/-- An algebra is algebraic if and only if it is algebraic as a subalgebra. -/
theorem Algebra.isAlgebraic_iff : Algebra.IsAlgebraic R A ↔ (⊤ : Subalgebra R A).IsAlgebraic := by
  delta Algebra.IsAlgebraic Subalgebra.IsAlgebraic
  -- ⊢ (∀ (x : A), _root_.IsAlgebraic R x) ↔ ∀ (x : A), x ∈ ⊤ → _root_.IsAlgebraic  …
  simp only [Algebra.mem_top, forall_prop_of_true, iff_self_iff]
  -- 🎉 no goals
#align algebra.is_algebraic_iff Algebra.isAlgebraic_iff

theorem isAlgebraic_iff_not_injective {x : A} :
    IsAlgebraic R x ↔ ¬Function.Injective (Polynomial.aeval x : R[X] →ₐ[R] A) := by
  simp only [IsAlgebraic, injective_iff_map_eq_zero, not_forall, and_comm, exists_prop]
  -- 🎉 no goals
#align is_algebraic_iff_not_injective isAlgebraic_iff_not_injective

end

section zero_ne_one

variable (R : Type u) {S : Type*} {A : Type v} [CommRing R]

variable [CommRing S] [Ring A] [Algebra R A] [Algebra R S] [Algebra S A]

variable [IsScalarTower R S A]

/-- An integral element of an algebra is algebraic.-/
theorem IsIntegral.isAlgebraic [Nontrivial R] {x : A} : IsIntegral R x → IsAlgebraic R x :=
  fun ⟨p, hp, hpx⟩ => ⟨p, hp.ne_zero, hpx⟩
#align is_integral.is_algebraic IsIntegral.isAlgebraic

variable {R}

theorem isAlgebraic_zero [Nontrivial R] : IsAlgebraic R (0 : A) :=
  ⟨_, X_ne_zero, aeval_X 0⟩
#align is_algebraic_zero isAlgebraic_zero

/-- An element of `R` is algebraic, when viewed as an element of the `R`-algebra `A`. -/
theorem isAlgebraic_algebraMap [Nontrivial R] (x : R) : IsAlgebraic R (algebraMap R A x) :=
  ⟨_, X_sub_C_ne_zero x, by rw [_root_.map_sub, aeval_X, aeval_C, sub_self]⟩
                            -- 🎉 no goals
#align is_algebraic_algebra_map isAlgebraic_algebraMap

theorem isAlgebraic_one [Nontrivial R] : IsAlgebraic R (1 : A) := by
  rw [← _root_.map_one (algebraMap R A)]
  -- ⊢ IsAlgebraic R (↑(algebraMap R A) 1)
  exact isAlgebraic_algebraMap 1
  -- 🎉 no goals
#align is_algebraic_one isAlgebraic_one

theorem isAlgebraic_nat [Nontrivial R] (n : ℕ) : IsAlgebraic R (n : A) := by
  rw [← map_natCast (_ : R →+* A) n]
  -- ⊢ IsAlgebraic R (↑?m.103313 ↑n)
  exact isAlgebraic_algebraMap (Nat.cast n)
  -- 🎉 no goals
#align is_algebraic_nat isAlgebraic_nat

theorem isAlgebraic_int [Nontrivial R] (n : ℤ) : IsAlgebraic R (n : A) := by
  rw [← _root_.map_intCast (algebraMap R A)]
  -- ⊢ IsAlgebraic R (↑(algebraMap R A) ↑n)
  exact isAlgebraic_algebraMap (Int.cast n)
  -- 🎉 no goals
#align is_algebraic_int isAlgebraic_int

theorem isAlgebraic_rat (R : Type u) {A : Type v} [DivisionRing A] [Field R] [Algebra R A] (n : ℚ) :
    IsAlgebraic R (n : A) := by
  rw [← map_ratCast (algebraMap R A)]
  -- ⊢ IsAlgebraic R (↑(algebraMap R A) ↑n)
  exact isAlgebraic_algebraMap (Rat.cast n)
  -- 🎉 no goals
#align is_algebraic_rat isAlgebraic_rat

theorem isAlgebraic_of_mem_rootSet {R : Type u} {A : Type v} [Field R] [Field A] [Algebra R A]
    {p : R[X]} {x : A} (hx : x ∈ p.rootSet A) : IsAlgebraic R x :=
  ⟨p, ne_zero_of_mem_rootSet hx, aeval_eq_zero_of_mem_rootSet hx⟩
#align is_algebraic_of_mem_root_set isAlgebraic_of_mem_rootSet

open IsScalarTower

theorem isAlgebraic_algebraMap_of_isAlgebraic {a : S} :
    IsAlgebraic R a → IsAlgebraic R (algebraMap S A a) := fun ⟨f, hf₁, hf₂⟩ =>
  ⟨f, hf₁, by rw [aeval_algebraMap_apply, hf₂, map_zero]⟩
              -- 🎉 no goals
#align is_algebraic_algebra_map_of_is_algebraic isAlgebraic_algebraMap_of_isAlgebraic

/-- This is slightly more general than `isAlgebraic_algebraMap_of_isAlgebraic` in that it
  allows noncommutative intermediate rings `A`. -/
theorem isAlgebraic_algHom_of_isAlgebraic {B} [Ring B] [Algebra R B] (f : A →ₐ[R] B) {a : A}
    (h : IsAlgebraic R a) : IsAlgebraic R (f a) :=
  let ⟨p, hp, ha⟩ := h
  ⟨p, hp, by rw [aeval_algHom, f.comp_apply, ha, map_zero]⟩
             -- 🎉 no goals
#align is_algebraic_alg_hom_of_is_algebraic isAlgebraic_algHom_of_isAlgebraic

/-- Transfer `Algebra.IsAlgebraic` across an `AlgEquiv`. -/
theorem AlgEquiv.isAlgebraic {B} [Ring B] [Algebra R B] (e : A ≃ₐ[R] B)
    (h : Algebra.IsAlgebraic R A) : Algebra.IsAlgebraic R B := fun b => by
  convert← isAlgebraic_algHom_of_isAlgebraic e.toAlgHom (h _); refine e.apply_symm_apply ?_
  -- ⊢ ↑↑e ?m.164054 = b
                                                               -- 🎉 no goals
#align alg_equiv.is_algebraic AlgEquiv.isAlgebraic

theorem AlgEquiv.isAlgebraic_iff {B} [Ring B] [Algebra R B] (e : A ≃ₐ[R] B) :
    Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic R B :=
  ⟨e.isAlgebraic, e.symm.isAlgebraic⟩
#align alg_equiv.is_algebraic_iff AlgEquiv.isAlgebraic_iff

theorem isAlgebraic_algebraMap_iff {a : S} (h : Function.Injective (algebraMap S A)) :
    IsAlgebraic R (algebraMap S A a) ↔ IsAlgebraic R a :=
  ⟨fun ⟨p, hp0, hp⟩ => ⟨p, hp0, h (by rwa [map_zero, ← aeval_algebraMap_apply])⟩,
                                      -- 🎉 no goals
    isAlgebraic_algebraMap_of_isAlgebraic⟩
#align is_algebraic_algebra_map_iff isAlgebraic_algebraMap_iff

theorem isAlgebraic_of_pow {r : A} {n : ℕ} (hn : 0 < n) (ht : IsAlgebraic R (r ^ n)) :
    IsAlgebraic R r := by
  obtain ⟨p, p_nonzero, hp⟩ := ht
  -- ⊢ IsAlgebraic R r
  refine ⟨Polynomial.expand _ n p, ?_, ?_⟩
  -- ⊢ ↑(expand R n) p ≠ 0
  · rwa [Polynomial.expand_ne_zero hn]
    -- 🎉 no goals
  · rwa [Polynomial.expand_aeval n p r]
    -- 🎉 no goals
#align is_algebraic_of_pow isAlgebraic_of_pow

theorem Transcendental.pow {r : A} (ht : Transcendental R r) {n : ℕ} (hn : 0 < n) :
    Transcendental R (r ^ n) := fun ht' => ht <| isAlgebraic_of_pow hn ht'
#align transcendental.pow Transcendental.pow

end zero_ne_one

section Field

variable {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]

/-- An element of an algebra over a field is algebraic if and only if it is integral.-/
theorem isAlgebraic_iff_isIntegral {x : A} : IsAlgebraic K x ↔ IsIntegral K x := by
  refine' ⟨_, IsIntegral.isAlgebraic K⟩
  -- ⊢ IsAlgebraic K x → IsIntegral K x
  rintro ⟨p, hp, hpx⟩
  -- ⊢ IsIntegral K x
  refine' ⟨_, monic_mul_leadingCoeff_inv hp, _⟩
  -- ⊢ eval₂ (algebraMap K A) x (p * ↑C (leadingCoeff p)⁻¹) = 0
  rw [← aeval_def, AlgHom.map_mul, hpx, zero_mul]
  -- 🎉 no goals
#align is_algebraic_iff_is_integral isAlgebraic_iff_isIntegral

protected theorem Algebra.isAlgebraic_iff_isIntegral :
    Algebra.IsAlgebraic K A ↔ Algebra.IsIntegral K A :=
  ⟨fun h x => isAlgebraic_iff_isIntegral.mp (h x), fun h x => isAlgebraic_iff_isIntegral.mpr (h x)⟩
#align algebra.is_algebraic_iff_is_integral Algebra.isAlgebraic_iff_isIntegral

end Field

section

variable {K : Type*} {L : Type*} {R : Type*} {S : Type*} {A : Type*}

section Ring

section CommRing

variable [CommRing R] [CommRing S] [Ring A]

variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/-- If x is algebraic over R, then x is algebraic over S when S is an extension of R,
  and the map from `R` to `S` is injective. -/
theorem isAlgebraic_of_larger_base_of_injective
    (hinj : Function.Injective (algebraMap R S)) {x : A}
    (A_alg : IsAlgebraic R x) : IsAlgebraic S x :=
  let ⟨p, hp₁, hp₂⟩ := A_alg
  ⟨p.map (algebraMap _ _), by
    rwa [Ne.def, ← degree_eq_bot, degree_map_eq_of_injective hinj, degree_eq_bot], by simpa⟩
    -- 🎉 no goals
                                                                                      -- 🎉 no goals
#align is_algebraic_of_larger_base_of_injective isAlgebraic_of_larger_base_of_injective

/-- If A is an algebraic algebra over R, then A is algebraic over S when S is an extension of R,
  and the map from `R` to `S` is injective. -/
theorem Algebra.isAlgebraic_of_larger_base_of_injective (hinj : Function.Injective (algebraMap R S))
    (A_alg : IsAlgebraic R A) : IsAlgebraic S A := fun x =>
  _root_.isAlgebraic_of_larger_base_of_injective hinj (A_alg x)
#align algebra.is_algebraic_of_larger_base_of_injective Algebra.isAlgebraic_of_larger_base_of_injective

end CommRing

section Field

variable [Field K] [Field L] [Ring A]

variable [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]

variable (L)

/-- If x is algebraic over K, then x is algebraic over L when L is an extension of K -/
theorem isAlgebraic_of_larger_base {x : A} (A_alg : IsAlgebraic K x) :
    IsAlgebraic L x :=
  isAlgebraic_of_larger_base_of_injective (algebraMap K L).injective A_alg
#align is_algebraic_of_larger_base isAlgebraic_of_larger_base

/-- If A is an algebraic algebra over K, then A is algebraic over L when L is an extension of K -/
theorem Algebra.isAlgebraic_of_larger_base (A_alg : IsAlgebraic K A) : IsAlgebraic L A :=
  isAlgebraic_of_larger_base_of_injective (algebraMap K L).injective A_alg
#align algebra.is_algebraic_of_larger_base Algebra.isAlgebraic_of_larger_base

variable (K)

theorem isAlgebraic_of_finite (e : A) [FiniteDimensional K A] : IsAlgebraic K e :=
  isAlgebraic_iff_isIntegral.mpr (isIntegral_of_finite K e)

variable (A)

/-- A field extension is algebraic if it is finite. -/
theorem Algebra.isAlgebraic_of_finite [FiniteDimensional K A] : IsAlgebraic K A :=
  Algebra.isAlgebraic_iff_isIntegral.mpr (isIntegral_of_finite K A)
#align algebra.is_algebraic_of_finite Algebra.isAlgebraic_of_finite

end Field

end Ring

section CommRing

variable [Field K] [Field L] [CommRing A]

variable [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]

/-- If L is an algebraic field extension of K and A is an algebraic algebra over L,
then A is algebraic over K. -/
theorem Algebra.isAlgebraic_trans (L_alg : IsAlgebraic K L) (A_alg : IsAlgebraic L A) :
    IsAlgebraic K A := by
  simp only [IsAlgebraic, isAlgebraic_iff_isIntegral] at L_alg A_alg ⊢
  -- ⊢ ∀ (x : A), IsIntegral K x
  exact isIntegral_trans L_alg A_alg
  -- 🎉 no goals
#align algebra.is_algebraic_trans Algebra.isAlgebraic_trans

end CommRing

section Field

variable [Field K] [Field L]

variable [Algebra K L]

theorem Algebra.IsAlgebraic.algHom_bijective (ha : Algebra.IsAlgebraic K L) (f : L →ₐ[K] L) :
    Function.Bijective f := by
  refine' ⟨f.toRingHom.injective, fun b => _⟩
  -- ⊢ ∃ a, ↑f a = b
  obtain ⟨p, hp, he⟩ := ha b
  -- ⊢ ∃ a, ↑f a = b
  let f' : p.rootSet L → p.rootSet L := (rootSet_maps_to' (fun x => x) f).restrict f _ _
  -- ⊢ ∃ a, ↑f a = b
  have : Function.Surjective f' :=
    Finite.injective_iff_surjective.1 fun _ _ h =>
      Subtype.eq <| f.toRingHom.injective <| Subtype.ext_iff.1 h
  obtain ⟨a, ha⟩ := this ⟨b, mem_rootSet.2 ⟨hp, he⟩⟩
  -- ⊢ ∃ a, ↑f a = b
  exact ⟨a, Subtype.ext_iff.1 ha⟩
  -- 🎉 no goals
#align algebra.is_algebraic.alg_hom_bijective Algebra.IsAlgebraic.algHom_bijective

theorem AlgHom.bijective [FiniteDimensional K L] (ϕ : L →ₐ[K] L) : Function.Bijective ϕ :=
  (Algebra.isAlgebraic_of_finite K L).algHom_bijective ϕ
#align alg_hom.bijective AlgHom.bijective

variable (K L)

/-- Bijection between algebra equivalences and algebra homomorphisms -/
@[simps]
noncomputable def Algebra.IsAlgebraic.algEquivEquivAlgHom (ha : Algebra.IsAlgebraic K L) :
    (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) where
  toFun ϕ := ϕ.toAlgHom
  invFun ϕ := AlgEquiv.ofBijective ϕ (ha.algHom_bijective ϕ)
  left_inv _ := by
    ext
    -- ⊢ ↑((fun ϕ => AlgEquiv.ofBijective ϕ (_ : Function.Bijective ↑ϕ)) ((fun ϕ => ↑ …
    rfl
    -- 🎉 no goals
  right_inv _ := by
    ext
    -- ⊢ ↑((fun ϕ => ↑ϕ) ((fun ϕ => AlgEquiv.ofBijective ϕ (_ : Function.Bijective ↑ϕ …
    rfl
    -- 🎉 no goals
  map_mul' _ _ := rfl
#align algebra.is_algebraic.alg_equiv_equiv_alg_hom Algebra.IsAlgebraic.algEquivEquivAlgHom

/-- Bijection between algebra equivalences and algebra homomorphisms -/
@[reducible]
noncomputable def algEquivEquivAlgHom [FiniteDimensional K L] :
    (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) :=
  (Algebra.isAlgebraic_of_finite K L).algEquivEquivAlgHom K L
#align alg_equiv_equiv_alg_hom algEquivEquivAlgHom

end Field

end

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]

theorem exists_integral_multiple [Algebra R S] {z : S} (hz : IsAlgebraic R z)
    (inj : ∀ x, algebraMap R S x = 0 → x = 0) :
    ∃ (x : integralClosure R S) (y : _) (_ : y ≠ (0 : R)), z * algebraMap R S y = x := by
  rcases hz with ⟨p, p_ne_zero, px⟩
  -- ⊢ ∃ x y x_1, z * ↑(algebraMap R S) y = ↑x
  set a := p.leadingCoeff
  -- ⊢ ∃ x y x_1, z * ↑(algebraMap R S) y = ↑x
  have a_ne_zero : a ≠ 0 := mt Polynomial.leadingCoeff_eq_zero.mp p_ne_zero
  -- ⊢ ∃ x y x_1, z * ↑(algebraMap R S) y = ↑x
  have x_integral : IsIntegral R (z * algebraMap R S a) :=
    ⟨p.integralNormalization, monic_integralNormalization p_ne_zero,
      integralNormalization_aeval_eq_zero px inj⟩
  exact ⟨⟨_, x_integral⟩, a, a_ne_zero, rfl⟩
  -- 🎉 no goals
#align exists_integral_multiple exists_integral_multiple

/-- A fraction `(a : S) / (b : S)` can be reduced to `(c : S) / (d : R)`,
if `S` is the integral closure of `R` in an algebraic extension `L` of `R`. -/
theorem IsIntegralClosure.exists_smul_eq_mul {L : Type*} [Field L] [Algebra R S] [Algebra S L]
    [Algebra R L] [IsScalarTower R S L] [IsIntegralClosure S R L] (h : Algebra.IsAlgebraic R L)
    (inj : Function.Injective (algebraMap R L)) (a : S) {b : S} (hb : b ≠ 0) :
    ∃ (c : S) (d : _) (_ : d ≠ (0 : R)), d • a = b * c := by
  obtain ⟨c, d, d_ne, hx⟩ :=
    exists_integral_multiple (h (algebraMap _ L a / algebraMap _ L b))
      ((injective_iff_map_eq_zero _).mp inj)
  refine'
    ⟨IsIntegralClosure.mk' S (c : L) c.2, d, d_ne, IsIntegralClosure.algebraMap_injective S R L _⟩
  simp only [Algebra.smul_def, RingHom.map_mul, IsIntegralClosure.algebraMap_mk', ← hx, ←
    IsScalarTower.algebraMap_apply]
  rw [← mul_assoc _ (_ / _), mul_div_cancel' (algebraMap S L a), mul_comm]
  -- ⊢ ↑(algebraMap S L) b ≠ 0
  exact mt ((injective_iff_map_eq_zero _).mp (IsIntegralClosure.algebraMap_injective S R L) _) hb
  -- 🎉 no goals
#align is_integral_closure.exists_smul_eq_mul IsIntegralClosure.exists_smul_eq_mul

section Field

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : Subalgebra K L)

theorem inv_eq_of_aeval_divX_ne_zero {x : L} {p : K[X]} (aeval_ne : aeval x (divX p) ≠ 0) :
    x⁻¹ = aeval x (divX p) / (aeval x p - algebraMap _ _ (p.coeff 0)) := by
  rw [inv_eq_iff_eq_inv, inv_div, eq_comm, div_eq_iff, sub_eq_iff_eq_add, mul_comm]
  -- ⊢ ↑(aeval x) p = ↑(aeval x) (divX p) * x + ↑(algebraMap K L) (coeff p 0)
  conv_lhs => rw [← divX_mul_X_add p]
  -- ⊢ ↑(aeval x) (divX p * X + ↑C (coeff p 0)) = ↑(aeval x) (divX p) * x + ↑(algeb …
  rw [AlgHom.map_add, AlgHom.map_mul, aeval_X, aeval_C]
  -- ⊢ ↑(aeval x) (divX p) ≠ 0
  exact aeval_ne
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align inv_eq_of_aeval_div_X_ne_zero inv_eq_of_aeval_divX_ne_zero

theorem inv_eq_of_root_of_coeff_zero_ne_zero {x : L} {p : K[X]} (aeval_eq : aeval x p = 0)
    (coeff_zero_ne : p.coeff 0 ≠ 0) : x⁻¹ = -(aeval x (divX p) / algebraMap _ _ (p.coeff 0)) := by
  convert inv_eq_of_aeval_divX_ne_zero (p := p) (L := L)
    (mt (fun h => (algebraMap K L).injective ?_) coeff_zero_ne) using 1
  · rw [aeval_eq, zero_sub, div_neg]
    -- 🎉 no goals
  rw [RingHom.map_zero]
  -- ⊢ ↑(algebraMap K L) (coeff p 0) = 0
  convert aeval_eq
  -- ⊢ ↑(algebraMap K L) (coeff p 0) = ↑(aeval x) p
  conv_rhs => rw [← divX_mul_X_add p]
  -- ⊢ ↑(algebraMap K L) (coeff p 0) = ↑(aeval x) (divX p * X + ↑C (coeff p 0))
  rw [AlgHom.map_add, AlgHom.map_mul, h, zero_mul, zero_add, aeval_C]
  -- 🎉 no goals
#align inv_eq_of_root_of_coeff_zero_ne_zero inv_eq_of_root_of_coeff_zero_ne_zero

theorem Subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero {x : A} {p : K[X]}
    (aeval_eq : aeval x p = 0) (coeff_zero_ne : p.coeff 0 ≠ 0) : (x⁻¹ : L) ∈ A := by
  suffices (x⁻¹ : L) = (-p.coeff 0)⁻¹ • aeval x (divX p) by
    rw [this]
    exact A.smul_mem (aeval x _).2 _
  have : aeval (x : L) p = 0 := by rw [Subalgebra.aeval_coe, aeval_eq, Subalgebra.coe_zero]
  -- ⊢ (↑x)⁻¹ = ↑((-coeff p 0)⁻¹ • ↑(aeval x) (divX p))
  -- porting note: this was a long sequence of `rw`.
  rw [inv_eq_of_root_of_coeff_zero_ne_zero this coeff_zero_ne, div_eq_inv_mul, Algebra.smul_def]
  -- ⊢ -((↑(algebraMap K L) (coeff p 0))⁻¹ * ↑(aeval ↑x) (divX p)) = ↑(↑(algebraMap …
  simp only [aeval_coe, Submonoid.coe_mul, Subsemiring.coe_toSubmonoid, coe_toSubsemiring,
    coe_algebraMap]
  rw [map_inv₀, map_neg, inv_neg, neg_mul]
  -- 🎉 no goals
#align subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero Subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero

theorem Subalgebra.inv_mem_of_algebraic {x : A} (hx : _root_.IsAlgebraic K (x : L)) :
    (x⁻¹ : L) ∈ A := by
  obtain ⟨p, ne_zero, aeval_eq⟩ := hx
  -- ⊢ (↑x)⁻¹ ∈ A
  rw [Subalgebra.aeval_coe, Subalgebra.coe_eq_zero] at aeval_eq
  -- ⊢ (↑x)⁻¹ ∈ A
  revert ne_zero aeval_eq
  -- ⊢ p ≠ 0 → ↑(aeval x) p = 0 → (↑x)⁻¹ ∈ A
  refine' p.recOnHorner _ _ _
  · intro h
    -- ⊢ ↑(aeval x) 0 = 0 → (↑x)⁻¹ ∈ A
    contradiction
    -- 🎉 no goals
  · intro p a hp ha _ih _ne_zero aeval_eq
    -- ⊢ (↑x)⁻¹ ∈ A
    refine' A.inv_mem_of_root_of_coeff_zero_ne_zero aeval_eq _
    -- ⊢ coeff (p + ↑C a) 0 ≠ 0
    rwa [coeff_add, hp, zero_add, coeff_C, if_pos rfl]
    -- 🎉 no goals
  · intro p hp ih _ne_zero aeval_eq
    -- ⊢ (↑x)⁻¹ ∈ A
    rw [AlgHom.map_mul, aeval_X, mul_eq_zero] at aeval_eq
    -- ⊢ (↑x)⁻¹ ∈ A
    cases' aeval_eq with aeval_eq x_eq
    -- ⊢ (↑x)⁻¹ ∈ A
    · exact ih hp aeval_eq
      -- 🎉 no goals
    · rw [x_eq, Subalgebra.coe_zero, inv_zero]
      -- ⊢ 0 ∈ A
      exact A.zero_mem
      -- 🎉 no goals
#align subalgebra.inv_mem_of_algebraic Subalgebra.inv_mem_of_algebraic

/-- In an algebraic extension L/K, an intermediate subalgebra is a field. -/
theorem Subalgebra.isField_of_algebraic (hKL : Algebra.IsAlgebraic K L) : IsField A :=
  { show Nontrivial A by infer_instance, Subalgebra.toCommRing A with
                         -- 🎉 no goals
    mul_inv_cancel := fun {a} ha =>
      ⟨⟨a⁻¹, A.inv_mem_of_algebraic (hKL a)⟩,
        Subtype.ext (mul_inv_cancel (mt (Subalgebra.coe_eq_zero _).mp ha))⟩ }
#align subalgebra.is_field_of_algebraic Subalgebra.isField_of_algebraic

end Field

section Pi

variable (R' : Type u) (S' : Type v) (T' : Type w)

/-- This is not an instance as it forms a diamond with `Pi.instSMul`.

See the `instance_diamonds` test for details. -/
def Polynomial.hasSMulPi [Semiring R'] [SMul R' S'] : SMul R'[X] (R' → S') :=
  ⟨fun p f x => eval x p • f x⟩
#align polynomial.has_smul_pi Polynomial.hasSMulPi

/-- This is not an instance as it forms a diamond with `Pi.instSMul`.

See the `instance_diamonds` test for details. -/
noncomputable def Polynomial.hasSMulPi' [CommSemiring R'] [Semiring S'] [Algebra R' S']
    [SMul S' T'] : SMul R'[X] (S' → T') :=
  ⟨fun p f x => aeval x p • f x⟩
#align polynomial.has_smul_pi' Polynomial.hasSMulPi'

attribute [local instance] Polynomial.hasSMulPi Polynomial.hasSMulPi'

@[simp]
theorem polynomial_smul_apply [Semiring R'] [SMul R' S'] (p : R'[X]) (f : R' → S') (x : R') :
    (p • f) x = eval x p • f x :=
  rfl
#align polynomial_smul_apply polynomial_smul_apply

@[simp]
theorem polynomial_smul_apply' [CommSemiring R'] [Semiring S'] [Algebra R' S'] [SMul S' T']
    (p : R'[X]) (f : S' → T') (x : S') : (p • f) x = aeval x p • f x :=
  rfl
#align polynomial_smul_apply' polynomial_smul_apply'

variable [CommSemiring R'] [CommSemiring S'] [CommSemiring T'] [Algebra R' S'] [Algebra S' T']

-- porting note: the proofs in this definition used `funext` in term-mode, but I was not able
-- to get them to work anymore.
/-- This is not an instance for the same reasons as `Polynomial.hasSMulPi'`. -/
noncomputable def Polynomial.algebraPi : Algebra R'[X] (S' → T') :=
  { Polynomial.hasSMulPi' R' S' T' with
    toFun := fun p z => algebraMap S' T' (aeval z p)
    map_one' := by
      funext z
      -- ⊢ (fun p z => ↑(algebraMap S' T') (↑(aeval z) p)) 1 z = OfNat.ofNat 1 z
      simp only [Polynomial.aeval_one, Pi.one_apply, map_one]
      -- 🎉 no goals
    map_mul' := fun f g => by
      funext z
      -- ⊢ OneHom.toFun { toFun := fun p z => ↑(algebraMap S' T') (↑(aeval z) p), map_o …
      simp only [Pi.mul_apply, map_mul]
      -- 🎉 no goals
    map_zero' := by
      funext z
      -- ⊢ OneHom.toFun (↑{ toOneHom := { toFun := fun p z => ↑(algebraMap S' T') (↑(ae …
      simp only [Polynomial.aeval_zero, Pi.zero_apply, map_zero]
      -- 🎉 no goals
    map_add' := fun f g => by
      funext z
      -- ⊢ OneHom.toFun (↑{ toOneHom := { toFun := fun p z => ↑(algebraMap S' T') (↑(ae …
      simp only [Polynomial.aeval_add, Pi.add_apply, map_add]
      -- 🎉 no goals
    commutes' := fun p f => by
      funext z
      -- ⊢ (↑{ toMonoidHom := { toOneHom := { toFun := fun p z => ↑(algebraMap S' T') ( …
      exact mul_comm _ _
      -- 🎉 no goals
    smul_def' := fun p f => by
      funext z
      -- ⊢ (p • f) z = (↑{ toMonoidHom := { toOneHom := { toFun := fun p z => ↑(algebra …
      simp only [polynomial_smul_apply', Algebra.algebraMap_eq_smul_one, RingHom.coe_mk,
        MonoidHom.coe_mk, OneHom.coe_mk, Pi.mul_apply, Algebra.smul_mul_assoc, one_mul] }
#align polynomial.algebra_pi Polynomial.algebraPi

attribute [local instance] Polynomial.algebraPi

@[simp]
theorem Polynomial.algebraMap_pi_eq_aeval :
    (algebraMap R'[X] (S' → T') : R'[X] → S' → T') = fun p z => algebraMap _ _ (aeval z p) :=
  rfl
#align polynomial.algebra_map_pi_eq_aeval Polynomial.algebraMap_pi_eq_aeval

@[simp]
theorem Polynomial.algebraMap_pi_self_eq_eval :
    (algebraMap R'[X] (R' → R') : R'[X] → R' → R') = fun p z => eval z p :=
  rfl
#align polynomial.algebra_map_pi_self_eq_eval Polynomial.algebraMap_pi_self_eq_eval

end Pi
