/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Minimal polynomials on an algebra over a field

This file specializes the theory of minpoly to the setting of field extensions
and derives some well-known properties, amongst which the fact that minimal polynomials
are irreducible, and uniquely determined by their defining property.

-/


open Polynomial Set Function minpoly

namespace minpoly

variable {A B : Type*}
variable (A) [Field A]

section Ring

variable [Ring B] [Algebra A B] (x : B)

/-- If an element `x` is a root of a nonzero polynomial `p`, then the degree of `p` is at least the
degree of the minimal polynomial of `x`. See also `minpoly.IsIntegrallyClosed.degree_le_of_ne_zero`
which relaxes the assumptions on `A` in exchange for stronger assumptions on `B`. -/
theorem degree_le_of_ne_zero {p : A[X]} (pnz : p ≠ 0) (hp : Polynomial.aeval x p = 0) :
    degree (minpoly A x) ≤ degree p :=
  calc
    degree (minpoly A x) ≤ degree (p * C (leadingCoeff p)⁻¹) :=
      min A x (monic_mul_leadingCoeff_inv pnz) (by simp [hp])
    _ = degree p := degree_mul_leadingCoeff_inv p pnz

theorem ne_zero_of_finite (e : B) [FiniteDimensional A B] : minpoly A e ≠ 0 :=
  minpoly.ne_zero <| .of_finite A _

/-- The minimal polynomial of an element `x` is uniquely characterized by its defining property:
if there is another monic polynomial of minimal degree that has `x` as a root, then this polynomial
is equal to the minimal polynomial of `x`. See also `minpoly.IsIntegrallyClosed.Minpoly.unique`
which relaxes the assumptions on `A` in exchange for stronger assumptions on `B`. -/
theorem unique {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x p = 0)
    (pmin : ∀ q : A[X], q.Monic → Polynomial.aeval x q = 0 → degree p ≤ degree q) :
    p = minpoly A x := by
  have hx : IsIntegral A x := ⟨p, pmonic, hp⟩
  symm; apply eq_of_sub_eq_zero
  by_contra hnz
  apply degree_le_of_ne_zero A x hnz (by simp [hp]) |>.not_gt
  apply degree_sub_lt _ (minpoly.ne_zero hx)
  · rw [(monic hx).leadingCoeff, pmonic.leadingCoeff]
  · exact le_antisymm (min A x pmonic hp) (pmin (minpoly A x) (monic hx) (aeval A x))

/-- If an element `x` is a root of a polynomial `p`, then the minimal polynomial of `x` divides `p`.
See also `minpoly.isIntegrallyClosed_dvd` which relaxes the assumptions on `A` in exchange for
stronger assumptions on `B`. -/
theorem dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A x ∣ p := by
  by_cases hp0 : p = 0
  · simp only [hp0, dvd_zero]
  have hx : IsIntegral A x := IsAlgebraic.isIntegral ⟨p, hp0, hp⟩
  rw [← modByMonic_eq_zero_iff_dvd (monic hx)]
  by_contra hnz
  apply degree_le_of_ne_zero A x hnz
    ((aeval_modByMonic_eq_self_of_root (monic hx) (aeval _ _)).trans hp) |>.not_gt
  exact degree_modByMonic_lt _ (monic hx)

variable {A x} in
lemma dvd_iff {p : A[X]} : minpoly A x ∣ p ↔ Polynomial.aeval x p = 0 :=
  ⟨fun ⟨q, hq⟩ ↦ by rw [hq, map_mul, aeval, zero_mul], minpoly.dvd A x⟩

theorem isRadical [IsReduced B] : IsRadical (minpoly A x) := fun n p dvd ↦ by
  rw [dvd_iff] at dvd ⊢; rw [map_pow] at dvd; exact IsReduced.eq_zero _ ⟨n, dvd⟩

theorem dvd_map_of_isScalarTower (A K : Type*) {R : Type*} [CommRing A] [Field K] [Ring R]
    [Algebra A K] [Algebra A R] [Algebra K R] [IsScalarTower A K R] (x : R) :
    minpoly K x ∣ (minpoly A x).map (algebraMap A K) := by
  refine minpoly.dvd K x ?_
  rw [aeval_map_algebraMap, minpoly.aeval]

theorem dvd_map_of_isScalarTower' (R : Type*) {S : Type*} (K L : Type*) [CommRing R]
    [CommRing S] [Field K] [Ring L] [Algebra R S] [Algebra R K] [Algebra S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] (s : S) :
    minpoly K (algebraMap S L s) ∣ map (algebraMap R K) (minpoly R s) := by
  apply minpoly.dvd K (algebraMap S L s)
  rw [← map_aeval_eq_aeval_map, minpoly.aeval, map_zero]
  rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

/-- If `y` is a conjugate of `x` over a field `K`, then it is a conjugate over a subring `R`. -/
theorem aeval_of_isScalarTower (R : Type*) {K T U : Type*} [CommRing R] [Field K] [CommRing T]
    [Algebra R K] [Algebra K T] [Algebra R T] [IsScalarTower R K T] [CommSemiring U] [Algebra K U]
    [Algebra R U] [IsScalarTower R K U] (x : T) (y : U)
    (hy : Polynomial.aeval y (minpoly K x) = 0) : Polynomial.aeval y (minpoly R x) = 0 :=
  aeval_map_algebraMap K y (minpoly R x) ▸
    eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (algebraMap K U) y
      (minpoly.dvd_map_of_isScalarTower R K x) hy

/-- If a subfield `F` of `E` contains all the coefficients of `minpoly E a`, then
`minpoly F a` maps to `minpoly E a` via `algebraMap F E`. -/
theorem map_algebraMap {F E A : Type*} [Field F] [Field E] [CommRing A]
    [Algebra F E] [Algebra E A] [Algebra F A] [IsScalarTower F E A]
    {a : A} (ha : IsIntegral F a) (h : minpoly E a ∈ lifts (algebraMap F E)) :
    (minpoly F a).map (algebraMap F E) = minpoly E a := by
  refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic ha.tower_top)
    ((algebraMap F E).injective.monic_map_iff.mp <| minpoly.monic ha)
    (minpoly.dvd E a (by simp)) ?_
  obtain ⟨g, hg, hgdeg, hgmon⟩ := lifts_and_natDegree_eq_and_monic h (minpoly.monic ha.tower_top)
  rw [natDegree_map, ← hgdeg]
  refine natDegree_le_of_dvd (minpoly.dvd F a ?_) hgmon.ne_zero
  rw [← aeval_map_algebraMap A, IsScalarTower.algebraMap_eq F E A, ← coe_mapRingHom,
    ← mapRingHom_comp, RingHom.comp_apply, coe_mapRingHom, coe_mapRingHom, hg,
    aeval_map_algebraMap, minpoly.aeval]

/-- See also `minpoly.ker_eval` which relaxes the assumptions on `A` in exchange for
stronger assumptions on `B`. -/
@[simp]
lemma ker_aeval_eq_span_minpoly :
    RingHom.ker (Polynomial.aeval x) = A[X] ∙ minpoly A x := by
  ext p
  simp_rw [RingHom.mem_ker, ← minpoly.dvd_iff, Submodule.mem_span_singleton,
    dvd_iff_exists_eq_mul_left, smul_eq_mul, eq_comm (a := p)]

variable {A x}

theorem eq_of_irreducible_of_monic [Nontrivial B] {p : A[X]} (hp1 : Irreducible p)
    (hp2 : Polynomial.aeval x p = 0) (hp3 : p.Monic) : p = minpoly A x :=
  let ⟨_, hq⟩ := dvd A x hp2
  eq_of_monic_of_associated hp3 (monic ⟨p, ⟨hp3, hp2⟩⟩) <|
    mul_one (minpoly A x) ▸ hq.symm ▸ Associated.mul_left _
      (associated_one_iff_isUnit.2 <| (hp1.isUnit_or_isUnit hq).resolve_left <| not_isUnit A x)

theorem eq_iff_aeval_eq_zero [Nontrivial B] {p : A[X]} (irr : Irreducible p) (monic : p.Monic) :
    p = minpoly A x ↔ Polynomial.aeval x p = 0 :=
  ⟨(· ▸ aeval A x), (eq_of_irreducible_of_monic irr · monic)⟩

theorem eq_iff_aeval_minpoly_eq_zero [IsDomain B] {C} [Ring C] [Algebra A C] [Nontrivial C]
    {b : B} (h : IsIntegral A b) {c : C} :
    minpoly A b = minpoly A c ↔ Polynomial.aeval c (minpoly A b) = 0 :=
  eq_iff_aeval_eq_zero (irreducible h) (monic h)

theorem eq_of_irreducible [Nontrivial B] {p : A[X]} (hp1 : Irreducible p)
    (hp2 : Polynomial.aeval x p = 0) : p * C p.leadingCoeff⁻¹ = minpoly A x := by
  have : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp1.ne_zero
  apply eq_of_irreducible_of_monic
  · exact Associated.irreducible ⟨⟨C p.leadingCoeff⁻¹, C p.leadingCoeff,
      by rwa [← C_mul, inv_mul_cancel₀, C_1], by rwa [← C_mul, mul_inv_cancel₀, C_1]⟩, rfl⟩ hp1
  · rw [aeval_mul, hp2, zero_mul]
  · rwa [Polynomial.Monic, leadingCoeff_mul, leadingCoeff_C, mul_inv_cancel₀]

theorem add_algebraMap {B : Type*} [CommRing B] [Algebra A B] (x : B)
    (a : A) : minpoly A (x + algebraMap A B a) = (minpoly A x).comp (X - C a) := by
  by_cases hx : IsIntegral A x
  · refine (minpoly.unique _ _ ((minpoly.monic hx).comp_X_sub_C _) ?_ fun q qmo hq => ?_).symm
    · simp [aeval_comp]
    · have : (Polynomial.aeval x) (q.comp (X + C a)) = 0 := by simpa [aeval_comp] using hq
      have H := minpoly.min A x (qmo.comp_X_add_C _) this
      rw [degree_eq_natDegree qmo.ne_zero,
        degree_eq_natDegree ((minpoly.monic hx).comp_X_sub_C _).ne_zero, natDegree_comp,
        natDegree_X_sub_C, mul_one]
      rwa [degree_eq_natDegree (minpoly.ne_zero hx),
        degree_eq_natDegree (qmo.comp_X_add_C _).ne_zero, natDegree_comp,
        natDegree_X_add_C, mul_one] at H
  · rw [minpoly.eq_zero hx, minpoly.eq_zero, zero_comp]
    refine fun h ↦ hx ?_
    simpa only [add_sub_cancel_right] using IsIntegral.sub h (isIntegral_algebraMap (x := a))

theorem sub_algebraMap {B : Type*} [CommRing B] [Algebra A B] (x : B)
    (a : A) : minpoly A (x - algebraMap A B a) = (minpoly A x).comp (X + C a) := by
  simpa [sub_eq_add_neg] using add_algebraMap x (-a)

theorem neg {B : Type*} [Ring B] [Algebra A B] (x : B) :
    minpoly A (- x) = (-1) ^ (natDegree (minpoly A x)) * (minpoly A x).comp (- X) := by
  by_cases hx : IsIntegral A x
  · refine (minpoly.unique _ _ ((minpoly.monic hx).neg_one_pow_natDegree_mul_comp_neg_X)
        ?_ fun q qmo hq => ?_).symm
    · simp [aeval_comp]
    · have : (Polynomial.aeval x) ((-1) ^ q.natDegree * q.comp (- X)) = 0 := by
        simpa [aeval_comp] using hq
      have H := minpoly.min A x qmo.neg_one_pow_natDegree_mul_comp_neg_X this
      have n1 := ((minpoly.monic hx).neg_one_pow_natDegree_mul_comp_neg_X).ne_zero
      have n2 := qmo.neg_one_pow_natDegree_mul_comp_neg_X.ne_zero
      rw [degree_eq_natDegree qmo.ne_zero,
        degree_eq_natDegree n1, natDegree_mul (by simp) (right_ne_zero_of_mul n1), natDegree_comp]
      rw [degree_eq_natDegree (minpoly.ne_zero hx),
        degree_eq_natDegree qmo.neg_one_pow_natDegree_mul_comp_neg_X.ne_zero,
        natDegree_mul (by simp) (right_ne_zero_of_mul n2), natDegree_comp] at H
      simpa using H
  · rw [minpoly.eq_zero hx, minpoly.eq_zero, zero_comp]
    · simp only [natDegree_zero, pow_zero, mul_zero]
    · exact IsIntegral.neg_iff.not.mpr hx

section AlgHomFintype

open scoped Classical in
/-- A technical finiteness result. -/
noncomputable def Fintype.subtypeProd {E : Type*} {X : Set E} (hX : X.Finite) {L : Type*}
    (F : E → Multiset L) : Fintype (∀ x : X, { l : L // l ∈ F x }) :=
  @Pi.instFintype _ _ _ (Finite.fintype hX) _

variable (F E K : Type*) [Field F] [Ring E] [CommRing K] [IsDomain K] [Algebra F E] [Algebra F K]
  [FiniteDimensional F E]

/-- Function from Hom_K(E,L) to pi type Π (x : basis), roots of min poly of x -/
def rootsOfMinPolyPiType (φ : E →ₐ[F] K)
    (x : range (Module.finBasis F E : _ → E)) :
    { l : K // l ∈ (minpoly F x.1).aroots K } :=
  ⟨φ x, by
    rw [mem_roots_map (minpoly.ne_zero_of_finite F x.val),
      ← aeval_def, aeval_algHom_apply, minpoly.aeval, map_zero]⟩

theorem aux_inj_roots_of_min_poly : Injective (rootsOfMinPolyPiType F E K) := by
  intro f g h
  -- needs explicit coercion on the RHS
  suffices (f : E →ₗ[F] K) = (g : E →ₗ[F] K) by rwa [DFunLike.ext'_iff] at this ⊢
  rw [funext_iff] at h
  exact LinearMap.ext_on (Module.finBasis F E).span_eq fun e he =>
    Subtype.ext_iff.mp (h ⟨e, he⟩)

/-- Given field extensions `E/F` and `K/F`, with `E/F` finite, there are finitely many `F`-algebra
  homomorphisms `E →ₐ[K] K`. -/
noncomputable instance AlgHom.fintype : Fintype (E →ₐ[F] K) :=
  @Fintype.ofInjective _ _
    (Fintype.subtypeProd (finite_range (Module.finBasis F E)) fun e =>
      (minpoly F e).aroots K)
    _ (aux_inj_roots_of_min_poly F E K)

end AlgHomFintype

variable (B) [Nontrivial B]

/-- If `B/K` is a nontrivial algebra over a field, and `x` is an element of `K`,
then the minimal polynomial of `algebraMap K B x` is `X - C x`. -/
theorem eq_X_sub_C (a : A) : minpoly A (algebraMap A B a) = X - C a :=
  eq_X_sub_C_of_algebraMap_inj a (algebraMap A B).injective

theorem eq_X_sub_C' (a : A) : minpoly A a = X - C a :=
  eq_X_sub_C A a

variable (A)

/-- The minimal polynomial of `0` is `X`. -/
@[simp]
theorem zero : minpoly A (0 : B) = X := by
  simpa only [add_zero, C_0, sub_eq_add_neg, neg_zero, RingHom.map_zero] using eq_X_sub_C B (0 : A)

/-- The minimal polynomial of `1` is `X - 1`. -/
@[simp]
theorem one : minpoly A (1 : B) = X - 1 := by
  simpa only [RingHom.map_one, C_1, sub_eq_add_neg] using eq_X_sub_C B (1 : A)

end Ring

section IsDomain

variable [Ring B] [IsDomain B] [Algebra A B]
variable {A} {x : B}

/-- A minimal polynomial is prime. -/
theorem prime (hx : IsIntegral A x) : Prime (minpoly A x) := by
  refine ⟨minpoly.ne_zero hx, not_isUnit A x, ?_⟩
  rintro p q ⟨d, h⟩
  have : Polynomial.aeval x (p * q) = 0 := by simp [h, aeval A x]
  replace : Polynomial.aeval x p = 0 ∨ Polynomial.aeval x q = 0 := by simpa
  exact Or.imp (dvd A x) (dvd A x) this

/-- If `L/K` is a field extension and an element `y` of `K` is a root of the minimal polynomial
of an element `x ∈ L`, then `y` maps to `x` under the field embedding. -/
theorem root {x : B} (hx : IsIntegral A x) {y : A} (h : IsRoot (minpoly A x) y) :
    algebraMap A B y = x := by
  have key : minpoly A x = X - C y := eq_of_monic_of_associated (monic hx) (monic_X_sub_C y)
    (associated_of_dvd_dvd ((irreducible_X_sub_C y).dvd_symm (irreducible hx) (dvd_iff_isRoot.2 h))
      (dvd_iff_isRoot.2 h))
  have := aeval A x
  rwa [key, map_sub, aeval_X, aeval_C, sub_eq_zero, eq_comm] at this

/-- The constant coefficient of the minimal polynomial of `x` is `0` if and only if `x = 0`. -/
@[simp]
theorem coeff_zero_eq_zero (hx : IsIntegral A x) : coeff (minpoly A x) 0 = 0 ↔ x = 0 := by
  constructor
  · intro h
    have zero_root := zero_isRoot_of_coeff_zero_eq_zero h
    rw [← root hx zero_root]
    exact RingHom.map_zero _
  · rintro rfl
    simp

/-- The minimal polynomial of a nonzero element has nonzero constant coefficient. -/
theorem coeff_zero_ne_zero (hx : IsIntegral A x) (h : x ≠ 0) : coeff (minpoly A x) 0 ≠ 0 := by
  contrapose! h
  simpa only [hx, coeff_zero_eq_zero] using h

end IsDomain

end minpoly

section AlgHom

variable {K L} [Field K] [CommRing L] [IsDomain L] [Algebra K L]

/-- The minimal polynomial (over `K`) of `σ : Gal(L/K)` is `X ^ (orderOf σ) - 1`. -/
lemma minpoly_algEquiv_toLinearMap (σ : L ≃ₐ[K] L) (hσ : IsOfFinOrder σ) :
    minpoly K σ.toLinearMap = X ^ (orderOf σ) - C 1 := by
  refine (minpoly.unique _ _ (monic_X_pow_sub_C _ hσ.orderOf_pos.ne.symm) ?_ ?_).symm
  · rw [map_sub]
    simp [← AlgEquiv.pow_toLinearMap, pow_orderOf_eq_one]
  · intros q hq hs
    rw [degree_eq_natDegree hq.ne_zero, degree_X_pow_sub_C hσ.orderOf_pos, Nat.cast_le, ← not_lt]
    intro H
    rw [aeval_eq_sum_range' H, ← Fin.sum_univ_eq_sum_range] at hs
    simp_rw [← AlgEquiv.pow_toLinearMap] at hs
    apply hq.ne_zero
    simpa using Fintype.linearIndependent_iff.mp
      (((linearIndependent_algHom_toLinearMap' K L L).comp _ AlgEquiv.coe_algHom_injective).comp _
        (Subtype.val_injective.comp ((finEquivPowers hσ).injective)))
      (q.coeff ∘ (↑)) hs ⟨_, H⟩

/-- The minimal polynomial (over `K`) of `σ : Gal(L/K)` is `X ^ (orderOf σ) - 1`. -/
lemma minpoly_algHom_toLinearMap (σ : L →ₐ[K] L) (hσ : IsOfFinOrder σ) :
    minpoly K σ.toLinearMap = X ^ (orderOf σ) - C 1 := by
  have : orderOf σ = orderOf (AlgEquiv.algHomUnitsEquiv _ _ hσ.unit) := by
    rw [← MonoidHom.coe_coe, orderOf_injective, ← orderOf_units, IsOfFinOrder.val_unit]
    exact (AlgEquiv.algHomUnitsEquiv K L).injective
  rw [this, ← minpoly_algEquiv_toLinearMap]
  · apply congr_arg
    ext
    simp
  · rwa [← orderOf_pos_iff, ← this, orderOf_pos_iff]

end AlgHom
