/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.Algebra.Group.UniqueProds.VectorSpace
import Mathlib.Data.Finsupp.Quotient
import Mathlib.FieldTheory.Minpoly.ConjRootClass
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.Invariant.Basic

/-!
# The Lindemann-Weierstrass theorem

## References

* [Jacobson, *Basic Algebra I, 4.12*][jacobson1974]
-/

noncomputable section

/-- If `B` is a domain, `x : B` is nonzero and algebraic over `A`, and a ring hom out of `B` kills
`x`, then it also kills `algebraMap A B y` for some nonzero `y : A`. -/
theorem IsAlgebraic.exists_ne_zero_map_algebraMap_eq_zero {A B S : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [IsDomain B] [Semiring S] {x : B} (hx : IsAlgebraic A x)
    (f : B →+* S) (x0 : x ≠ 0) (hfx : f x = 0) : ∃ y : A, y ≠ 0 ∧ f (algebraMap A B y) = 0 := by
  obtain ⟨y, hy, y0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot <|
    Ideal.under_ne_bot_of_algebraic_mem (I := RingHom.ker f) x0 hfx hx
  exact ⟨y, y0, hy⟩

namespace LindemannWeierstrass

open scoped AddMonoidAlgebra

open Finset

attribute [local instance] AddMonoidAlgebra.comapMulSemiringAction
  AddMonoidAlgebra.comapSMulCommClass

section classSumBasis

variable {F R K : Type*} [Field F] [CommSemiring R] [Field K] [Algebra F K]
  [FiniteDimensional F K] [Normal F K]

omit [FiniteDimensional F K] in
theorem mem_fixedPoints_iff_forall_isConjRoot {x : R[K]} :
    x ∈ FixedPoints.subalgebra R R[K] Gal(K/F) ↔
      ∀ a b, IsConjRoot F a b → x.coeff a = x.coeff b := by
  simp only [FixedPoints.mem_subalgebra, AddMonoidAlgebra.ext_iff, Finsupp.ext_iff,
    AddMonoidAlgebra.coeff_comapSMul, isConjRoot_iff_exists_algEquiv, forall_exists_index]
  exact ⟨by rintro h _ b g rfl; simpa using (h g (g b)).symm, fun h g m ↦ h _ _ g⁻¹ rfl⟩

/-- Auxiliary definition for `classSumBasis`. -/
def classSumReprAux :
    FixedPoints.subalgebra R R[K] Gal(K/F) ≃ (ConjRootClass F K →₀ R) :=
  (AddMonoidAlgebra.coeffEquiv.subtypeEquiv
    (q := fun f : K →₀ R ↦ ∀ a b, IsConjRoot F a b → f a = f b)
    fun _ ↦ mem_fixedPoints_iff_forall_isConjRoot).trans <|
  Setoid.liftFinsuppEquiv (IsConjRoot.setoid F K) fun a ↦ by
    classical
    exact (ConjRootClass.mk F a).carrier.toFinite.subset fun b hb ↦
      ConjRootClass.mem_carrier.mpr (ConjRootClass.mk_eq_mk.mpr hb)

@[simp]
private theorem classSumReprAux_apply_mk (x : FixedPoints.subalgebra R R[K] Gal(K/F)) (i : K) :
    classSumReprAux x (ConjRootClass.mk F i) = x.val.coeff i :=
  rfl

variable (F R K) in
/-- The `Gal(K/F)`-invariant elements of `R[K]` have a basis indexed by `ConjRootClass F K`:
the sums `∑ i ∈ c, X ^ i` of the monomials over a conjugacy class `c`. -/
def classSumBasis : Module.Basis (ConjRootClass F K) R (FixedPoints.subalgebra R R[K] Gal(K/F)) :=
  .ofRepr
    { toEquiv := classSumReprAux
      map_add' x y := by ext i; induction i; simp
      map_smul' r x := by ext i; induction i; simp }

theorem classSumBasis_repr_apply_mk (x : FixedPoints.subalgebra R R[K] Gal(K/F)) (i : K) :
    (classSumBasis F R K).repr x (ConjRootClass.mk F i) = x.val.coeff i :=
  rfl

@[simp]
theorem classSumBasis_repr_apply_zero (x : FixedPoints.subalgebra R R[K] Gal(K/F)) :
    (classSumBasis F R K).repr x 0 = x.val.coeff 0 :=
  rfl

open Classical in
theorem coeff_classSumBasis (c : ConjRootClass F K) (i : K) :
    (classSumBasis F R K c : R[K]).coeff i = if ConjRootClass.mk F i = c then 1 else 0 := by
  rw [← classSumBasis_repr_apply_mk, Module.Basis.repr_self, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

open Classical in
theorem coe_classSumBasis (c : ConjRootClass F K) :
    (classSumBasis F R K c : R[K]) = ∑ i ∈ c.carrier.toFinset, AddMonoidAlgebra.single i 1 := by
  ext i
  simp [coeff_classSumBasis, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, ConjRootClass.mem_carrier]

theorem coeff_coe_mul_classSumBasis_zero
    (x : FixedPoints.subalgebra R R[K] Gal(K/F)) (c : ConjRootClass F K) :
    (x * classSumBasis F R K c : R[K]).coeff 0 =
      (classSumBasis F R K).repr x (-c) * c.carrier.ncard := by
  rw [coe_classSumBasis, mul_sum, AddMonoidAlgebra.coeff_sum]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply,
    AddMonoidAlgebra.coeff_mul_single_apply, zero_add, mul_one]
  classical
  calc
    _ = ∑ a ∈ c.carrier, (classSumBasis F R K).repr x (-c) := by
      refine sum_congr rfl fun a ha ↦ ?_
      rw [← classSumBasis_repr_apply_mk, ← ConjRootClass.mk_neg,
        ConjRootClass.mem_carrier.mp (Set.mem_toFinset.mp ha)]
    _ = _ := by simp [nsmul_eq_mul, mul_comm]

open Classical in
theorem lift_eq_sum_classSumBasis_repr (A : Type*) [Semiring A] [Algebra R A]
    (φ : Multiplicative K →* A) (x : FixedPoints.subalgebra R R[K] Gal(K/F)) :
    AddMonoidAlgebra.lift R A K φ x =
      ((classSumBasis F R K).repr x).sum fun c xc ↦ xc • ∑ a ∈ c.carrier, φ (.ofAdd a) := by
  conv_lhs => rw [← (classSumBasis F R K).linearCombination_repr x]
  simp [Finsupp.linearCombination_apply, Finsupp.sum, coe_classSumBasis, map_sum]

end classSumBasis

variable {ι : Type*} [Fintype ι]

theorem exists_ne_zero_lift_eq_zero {K S : Type*}
    [Field K] [Semiring S] [Algebra K S]
    (φ : Multiplicative K →* S)
    (u' : ι → K) (u'_inj : Function.Injective u')
    (v' : ι → K) (v0 : v' ≠ 0)
    (h : ∑ i : ι, algebraMap K S (v' i) * φ (.ofAdd (u' i)) = 0) :
    ∃ (f : K[K]), f ≠ 0 ∧ AddMonoidAlgebra.lift _ _ _ φ f = 0 := by
  refine ⟨(AddMonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm v').mapDomain u', ?_, ?_⟩
  · rw [← AddMonoidAlgebra.mapDomain_zero u', (AddMonoidAlgebra.mapDomain_injective u'_inj).ne_iff]
    simpa [Finsupp.ext_iff, funext_iff] using v0
  · rw [AddMonoidAlgebra.lift_apply, ← h, AddMonoidAlgebra.coeff_mapDomain,
      Finsupp.sum_mapDomain_index_inj u'_inj]
    simp [Finsupp.sum_fintype, Algebra.smul_def]

open Classical in
theorem exists_sum_conjRootClass_eq_zero {F K S : Type*}
    [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Normal F K] [CharZero F]
    [Semiring S] [Algebra F S]
    (φ : Multiplicative K →* S)
    (x : FixedPoints.subalgebra F F[K] Gal(K/F)) (x0 : x ≠ 0)
    (hx : AddMonoidAlgebra.lift F _ _ φ x = 0) :
    ∃ v : ConjRootClass F K →₀ F, v 0 ≠ 0 ∧
      Finsupp.linearCombination F
        (fun c : ConjRootClass F K ↦ ∑ x ∈ c.carrier, φ (.ofAdd x)) v = 0 := by
  rw [← (classSumBasis F F K).repr.injective.ne_iff, map_zero, Finsupp.ne_iff] at x0
  obtain ⟨i, hi⟩ := x0
  refine ⟨(classSumBasis F F K).repr (x * classSumBasis F F K (-i)), ?_, ?_⟩
  · rw [classSumBasis_repr_apply_zero, Subalgebra.coe_mul, coeff_coe_mul_classSumBasis_zero,
      neg_neg, mul_ne_zero_iff_left hi, Nat.cast_ne_zero]
    exact (-i).carrier_nonempty.ncard_pos.ne'
  · rw [Finsupp.linearCombination_apply, ← lift_eq_sum_classSumBasis_repr, Subalgebra.coe_mul,
      map_mul, hx, zero_mul]

open Polynomial

open Classical in
theorem exists_sum_conjRootClass_eq_add_sum_map_aroots (A : Type*) {R F K S : Type*}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F]
    [Field K] [Algebra F K] [FiniteDimensional F K] [Normal F K] [CharZero F]
    [Field S] [Algebra K S] [Algebra F S] [IsScalarTower F K S] [Algebra A S]
    [IsScalarTower A F S] [CommSemiring R] [Module R S]
    (φ : Multiplicative S →* S) (v : ConjRootClass F K →₀ R) :
    ∃ w : A[X] →₀ R, (∀ p ∈ w.support, p.eval 0 ≠ 0) ∧
      (v.sum fun c vc ↦ vc • ∑ x ∈ c.carrier,
          φ.comp (algebraMap K S).toAddMonoidHom.toMultiplicative (.ofAdd x)) =
        v 0 • 1 + w.sum (fun p c ↦ c • ((p.aroots S).map fun x => φ (.ofAdd x)).sum) := by
  refine ⟨(v.erase 0).mapDomain
    fun c ↦ IsLocalization.integerNormalization (nonZeroDivisors A) c.minpoly, ?_, ?_⟩
  · intro p hp
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hp)
    rw [← coeff_zero_eq_eval_zero, Ne, IsFractionRing.coeff_integerNormalization_eq_zero_iff]
    have hc0 : c ≠ 0 := Finset.ne_of_mem_erase (by simpa only [Finsupp.support_erase] using hc)
    simpa only [← coeff_zero_eq_aeval_zero', map_eq_zero, ConjRootClass.mk_zero] using
      mt (ConjRootClass.aeval_minpoly_iff (0 : K) c).mp hc0.symm
  · rw [← Finsupp.add_sum_erase' v 0 _ (by simp),
      Finsupp.sum_mapDomain_index (by simp) (by simp [add_smul])]
    congr 1
    · simp
    · refine sum_congr rfl fun c _hc ↦ ?_
      dsimp
      rw [IsFractionRing.aroots_integerNormalization, ← c.splits_minpoly.map_aroots_algebraMap,
        c.aroots_minpoly_eq_carrier_val]
      simp

public theorem exists_add_sum_map_aroots_eq_zero {S : Type*}
    [Field S] [Algebra ℚ S] [IsAlgClosed S]
    (φ : Multiplicative S →* S)
    (u : ι → S) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → S) (hv : ∀ i, IsIntegral ℚ (v i)) (v0 : v ≠ 0)
    (h : ∑ i, v i * φ (.ofAdd <| u i) = 0) :
    ∃ (w : ℤ), w ≠ 0 ∧ ∃ (w' : ℤ[X] →₀ ℤ), (∀ p ∈ w'.support, p.eval 0 ≠ 0) ∧
      w + w'.sum (fun p c ↦ c • ((p.aroots S).map (φ <| .ofAdd ·)).sum) = 0 := by
  classical
  let s := Set.range u ∪ Set.range v
  have hs : ∀ x ∈ s, IsIntegral ℚ x := by simp [s, or_imp, forall_and, hu, hv]
  let E := IntermediateField.adjoin ℚ (s : Set S)
  have : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_adjoin hs
  let K := IntermediateField.normalClosure ℚ E S
  have hK : IsNormalClosure ℚ E K :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure fun _ ↦ IsAlgClosed.splits _
  have : Normal ℚ K := hK.normal
  have mem_K {x : S} (hx : x ∈ s) : x ∈ K :=
    IntermediateField.le_normalClosure E (IntermediateField.subset_adjoin ℚ _ hx)
  let u' : ι → K := fun i ↦ ⟨u i, mem_K (by simp [s])⟩
  let v' : ι → K := fun i ↦ ⟨v i, mem_K (by simp [s])⟩
  obtain ⟨f, f0, hf⟩ : ∃ (f : K[K]), f ≠ 0 ∧
    AddMonoidAlgebra.lift _ _ _
      (φ.comp (algebraMap K S).toAddMonoidHom.toMultiplicative) f = 0 := by
    refine exists_ne_zero_lift_eq_zero _ u' ?_ v' ?_ ?_
    · exact fun i j hij ↦ u_inj (Subtype.mk.inj hij)
    · exact fun h ↦ v0 congr(($h ·))
    · simpa [u', v']
  open scoped AlgebraMonoidAlgebra in
  let A := FixedPoints.subalgebra ℚ ℚ[K] Gal(K/ℚ)
  have : Algebra.IsIntegral A ℚ[K] := Algebra.IsInvariant.isIntegral A ℚ[K] Gal(K/ℚ)
  have : Algebra.IsIntegral A K[K] := Algebra.IsIntegral.trans ℚ[K]
  obtain ⟨f, f0, hf⟩ := (Algebra.IsIntegral.isIntegral (R := A) f).isAlgebraic
    |>.exists_ne_zero_map_algebraMap_eq_zero _ f0 hf
  rw [Subalgebra.algebraMap_def, AddMonoidAlgebra.algebraMap_def, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AddMonoidAlgebra.lift_mapRingHom_algebraMap] at hf
  obtain ⟨v, v0, hv⟩ := exists_sum_conjRootClass_eq_zero _ f f0 hf
  obtain ⟨b, hb, v', hbv, hv'⟩ := IsFractionRing.exists_linearCombination_eq_zero ℤ _ v hv
  obtain ⟨w', hw', h⟩ := exists_sum_conjRootClass_eq_add_sum_map_aroots ℤ φ v'
  refine ⟨v' 0, fun h0 ↦ v0 ?_, w', hw', ?_⟩
  · have := hbv 0
    rw [h0, map_zero, eq_comm, smul_eq_zero] at this
    exact this.resolve_left (nonZeroDivisors.ne_zero hb)
  · rwa [Finsupp.linearCombination_apply, h, zsmul_one] at hv'

end LindemannWeierstrass
