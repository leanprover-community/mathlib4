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
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RingTheory.Invariant.Basic

/-!
# The Lindemann-Weierstrass theorem

## References

* [Jacobson, *Basic Algebra I, 4.12*][jacobson1974]
-/

noncomputable section

-- TODO: move to `Mathlib/Algebra/MonoidAlgebra/Basic.lean`, next to `AddMonoidAlgebra.domCongrAut`
-- (the exponent action by additive automorphisms).
namespace AddMonoidAlgebra

variable {G M R : Type*} [Group G] [AddMonoid M] [DistribMulAction G M] [CommSemiring R]

variable (G M R) in
/-- An action of `G` on `M` by additive automorphisms induces an action of `G` on `R[M]`
by `R`-algebra automorphisms, through the exponents. -/
def comapDomAlgAut : G →* R[M] ≃ₐ[R] R[M] :=
  (AddMonoidHom.toMultiplicative (domCongrAut R R (M := M))).comp (DistribMulAction.toAddAut G M)

theorem comapDomAlgAut_apply (g : G) :
    comapDomAlgAut G M R g = domCongr R R (DistribMulAction.toAddEquiv M g) :=
  rfl

/-- The action of `G` on `R[M]` through the exponents, `(g • x).coeff m = x.coeff (g⁻¹ • m)`.

This is not an instance: for `M = R` it would conflict with actions on the coefficients. -/
@[instance_reducible]
def comapMulSemiringAction : MulSemiringAction G R[M] :=
  .compHom _ (comapDomAlgAut G M R)

attribute [local instance] comapMulSemiringAction

theorem comapSMul_def (g : G) (x : R[M]) : g • x = comapDomAlgAut G M R g x :=
  rfl

@[simp]
theorem coeff_comapSMul (g : G) (x : R[M]) (m : M) : (g • x).coeff m = x.coeff (g⁻¹ • m) := by
  simp [comapSMul_def, comapDomAlgAut_apply]

@[simp]
theorem comapSMul_single (g : G) (m : M) (r : R) : g • single m r = single (g • m) r := by
  simp [comapSMul_def, comapDomAlgAut_apply]

theorem comapSMulCommClass : SMulCommClass G R R[M] where
  smul_comm g r x := by simp [comapSMul_def]

-- TODO: move to the `Pushout` section of
-- `Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean`, next to the `R[X]` instance.
open scoped AlgebraMonoidAlgebra in
instance isIntegral_algebraAddMonoidAlgebra {R S M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] [AddCommMonoid M] :
    Algebra.IsIntegral R[M] S[M] :=
  Algebra.IsPushout.isIntegral R _ S _

end AddMonoidAlgebra

-- TODO: move to `Mathlib/Algebra/Algebra/Subalgebra/Operations.lean`,
-- after `FixedPoints.subalgebra`.
theorem FixedPoints.mem_subalgebra {A B G : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] {x : B} :
    x ∈ FixedPoints.subalgebra A B G ↔ ∀ g : G, g • x = x :=
  Iff.rfl

-- TODO: move to `Mathlib/RingTheory/Invariant/Defs.lean` (or `Basic.lean`).
instance FixedPoints.subalgebra.isInvariant {A B G : Type*} [CommSemiring A] [CommSemiring B]
    [Algebra A B] [Group G] [MulSemiringAction G B] [SMulCommClass G A B] :
    Algebra.IsInvariant (FixedPoints.subalgebra A B G) B G :=
  ⟨fun b hb ↦ ⟨⟨b, hb⟩, rfl⟩⟩

-- TODO: move to `Mathlib/RingTheory/Ideal/GoingUp.lean`,
-- after `Ideal.under_ne_bot_of_algebraic_mem`.
/-- If `B` is a domain, `x : B` is nonzero and algebraic over `A`, and a ring hom out of `B` kills
`x`, then it also kills `algebraMap A B y` for some nonzero `y : A`. -/
theorem IsAlgebraic.exists_ne_zero_map_algebraMap_eq_zero {A B S : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [IsDomain B] [Semiring S] {x : B} (hx : IsAlgebraic A x)
    (f : B →+* S) (x0 : x ≠ 0) (hfx : f x = 0) : ∃ y : A, y ≠ 0 ∧ f (algebraMap A B y) = 0 := by
  obtain ⟨y, hy, y0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot <|
    Ideal.under_ne_bot_of_algebraic_mem (I := RingHom.ker f) x0 hfx hx
  exact ⟨y, y0, hy⟩

-- TODO: move to `Mathlib/Data/Finsupp/Quotient.lean`.
namespace Quotient

variable {α : Type*} {s : Setoid α} {β : Type*} [Zero β]

/-- Pull a function `Quotient s →₀ β` back to `α →₀ β`, provided the classes of `s` are finite. -/
def compMkFinsupp (hs : ∀ a, {b | s b a}.Finite) (f : Quotient s →₀ β) : α →₀ β :=
  Finsupp.ofSupportFinite (f ∘ Quotient.mk s) <| by
    rw [Function.support_comp_eq_preimage]
    refine f.hasFiniteSupport.preimage' fun q _ ↦ ?_
    induction q using Quotient.inductionOn with | h a => ?_
    convert hs a using 1
    ext b
    simp [Quotient.eq]

@[simp]
theorem compMkFinsupp_apply (hs : ∀ a, {b | s b a}.Finite) (f : Quotient s →₀ β) (a : α) :
    compMkFinsupp hs f a = f ⟦a⟧ :=
  rfl

variable (s β) in
/-- Finitely supported functions on `α` that are constant on the classes of `s` correspond to
finitely supported functions on `Quotient s`, provided the classes are finite. -/
def finsuppEquiv (hs : ∀ a, {b | s b a}.Finite) :
    {f : α →₀ β // ∀ a b, s a b → f a = f b} ≃ (Quotient s →₀ β) where
  toFun f := Quotient.liftFinsupp f.1 f.2
  invFun f := ⟨compMkFinsupp hs f, fun a b h ↦ by simp [Quotient.sound h]⟩
  left_inv _ := Subtype.ext <| Finsupp.ext fun _ ↦ rfl
  right_inv f := Finsupp.ext fun q ↦ Quotient.inductionOn q fun _ ↦ rfl

@[simp]
theorem finsuppEquiv_apply_mk (hs : ∀ a, {b | s b a}.Finite)
    (f : {f : α →₀ β // ∀ a b, s a b → f a = f b}) (a : α) :
    finsuppEquiv s β hs f ⟦a⟧ = f.1 a :=
  rfl

@[simp]
theorem coe_finsuppEquiv_symm (hs : ∀ a, {b | s b a}.Finite) (f : Quotient s →₀ β) :
    ((finsuppEquiv s β hs).symm f : α →₀ β) = compMkFinsupp hs f :=
  rfl

end Quotient

-- TODO: move to `Mathlib/RingTheory/Localization/Integral.lean`.
/-- Clearing denominators in a linear relation with coefficients in a fraction field, without
changing which coefficients vanish. -/
theorem IsFractionRing.exists_sum_smul_eq_zero (R : Type*) {F M ι : Type*} [CommRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] [AddCommMonoid M] [Module R M] [Module F M]
    [IsScalarTower R F M] (f : ι → M) (v : ι →₀ F) (h : (v.sum fun i c ↦ c • f i) = 0) :
    ∃ v' : ι →₀ R, v'.support = v.support ∧ (v'.sum fun i c ↦ c • f i) = 0 := by
  classical
  have : Nontrivial R := (algebraMap R F).domain_nontrivial
  obtain ⟨⟨b, hb⟩, hv⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) v.support v
  simp only [IsLocalization.IsInteger, RingHom.mem_rangeS] at hv
  choose a ha using hv
  let v' : ι →₀ R := Finsupp.onFinset v.support
    (fun i ↦ if hi : i ∈ v.support then a i hi else 0) fun i h ↦ by by_contra hi; simp [hi] at h
  have hv' (i : ι) : algebraMap R F (v' i) = b • v i := by
    by_cases hi : i ∈ v.support
    · simp only [v', Finsupp.onFinset_apply, hi, ↓reduceDIte, ha]
    · simp only [v', Finsupp.onFinset_apply, hi, ↓reduceDIte, map_zero,
        Finsupp.notMem_support_iff.mp hi, smul_zero]
  have hb0 : algebraMap R F b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr (nonZeroDivisors.ne_zero hb)
  have supp : v'.support = v.support := by
    ext i
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, Ne,
      ← (IsFractionRing.injective R F).eq_iff, map_zero, hv', Algebra.smul_def, mul_eq_zero,
      or_iff_right hb0]
  refine ⟨v', supp, ?_⟩
  calc (v'.sum fun i c ↦ c • f i) = ∑ i ∈ v.support, b • (v i • f i) := by
        rw [Finsupp.sum, supp]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [← algebraMap_smul F (v' i), hv', smul_assoc]
    _ = 0 := by rw [← Finset.smul_sum]; exact (congrArg (b • ·) h).trans (smul_zero b)

section integerNormalization

open Polynomial

variable {R F : Type*} [CommRing R] [Field F] [Algebra R F] [IsFractionRing R F]

-- TODO: move to `Mathlib/RingTheory/Localization/Integral.lean`.
theorem IsFractionRing.coeff_integerNormalization_eq_zero_iff (p : F[X]) (n : ℕ) :
    (IsLocalization.integerNormalization (nonZeroDivisors R) p).coeff n = 0 ↔ p.coeff n = 0 := by
  have : Nontrivial R := (algebraMap R F).domain_nontrivial
  obtain ⟨b, hb, hbp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  have hb0 : algebraMap R F b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr (nonZeroDivisors.ne_zero hb)
  rw [← (IsFractionRing.injective R F).eq_iff, map_zero, ← coeff_map, hbp, coeff_smul,
    Algebra.smul_def, mul_eq_zero, or_iff_right hb0]

-- TODO: move to `Mathlib/RingTheory/Localization/Integral.lean`.
/-- Clearing the denominators of a polynomial does not change its roots. -/
theorem IsFractionRing.aroots_integerNormalization {S : Type*} [CommRing S] [IsDomain S]
    [Algebra R S] [Algebra F S] [IsScalarTower R F S] (p : F[X]) :
    (IsLocalization.integerNormalization (nonZeroDivisors R) p).aroots S = p.aroots S := by
  have : Nontrivial R := (algebraMap R F).domain_nontrivial
  obtain ⟨b, hb, hbp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  rw [← aroots_map S F, hbp, ← algebraMap_smul F, aroots_smul_nonzero]
  exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr (nonZeroDivisors.ne_zero hb)

end integerNormalization

namespace LindemannWeierstrass

open scoped AddMonoidAlgebra

open Finset


attribute [local instance] AddMonoidAlgebra.comapMulSemiringAction
  AddMonoidAlgebra.comapSMulCommClass

section classSumBasis

variable {F R K : Type*} [Field F] [CommSemiring R] [Field K] [Algebra F K]

-- TODO: move to `Mathlib/FieldTheory/Minpoly/ConjRootClass.lean`.
@[simp]
theorem _root_.ConjRootClass.mk_algEquiv_apply (g : K ≃ₐ[F] K) (x : K) :
    ConjRootClass.mk F (g x) = ConjRootClass.mk F x :=
  ConjRootClass.mk_eq_mk.mpr (isConjRoot_of_algEquiv' x g)

-- TODO: move to `Mathlib/FieldTheory/Minpoly/ConjRootClass.lean`.
theorem _root_.ConjRootClass.carrier_nonempty (c : ConjRootClass F K) : c.carrier.Nonempty := by
  induction c using ConjRootClass.ind with
  | h a => exact ⟨a, ConjRootClass.mem_carrier.mpr rfl⟩

variable [FiniteDimensional F K] [Normal F K]

-- TODO: move to `Mathlib/FieldTheory/Minpoly/ConjRootClass.lean`.
open Classical in
theorem _root_.ConjRootClass.card_carrier_ne_zero (c : ConjRootClass F K) :
    #c.carrier.toFinset ≠ 0 :=
  (Finset.card_pos.mpr (Set.toFinset_nonempty.mpr c.carrier_nonempty)).ne'

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
  Quotient.finsuppEquiv (IsConjRoot.setoid F K) R fun a ↦ by
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

open Classical in
theorem coeff_classSumBasis_mul_classSumBasis_zero (x y : ConjRootClass F K) :
    ((classSumBasis F R K x : R[K]) * classSumBasis F R K y).coeff 0 =
      if x = -y then (#x.carrier.toFinset : R) else 0 := by
  simp only [coe_classSumBasis, sum_mul_sum, AddMonoidAlgebra.single_mul_single, mul_one,
    AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  calc _ = ∑ i ∈ x.carrier.toFinset, if x = -y then (1 : R) else 0 := by
        refine sum_congr rfl fun i hi ↦ ?_
        rw [Set.mem_toFinset, ConjRootClass.mem_carrier] at hi
        simp only [add_eq_zero_iff_eq_neg', Finset.sum_ite_eq', Set.mem_toFinset,
          ConjRootClass.mem_carrier, ← ConjRootClass.mk_neg, hi, neg_eq_iff_eq_neg]
    _ = _ := by split_ifs <;> simp

open Classical in
theorem classSumBasis_repr_mul_classSumBasis_apply_zero
    (x : FixedPoints.subalgebra R R[K] Gal(K/F)) (c : ConjRootClass F K) :
    (classSumBasis F R K).repr (x * classSumBasis F R K c) 0 =
      (classSumBasis F R K).repr x (-c) * #(-c).carrier.toFinset := by
  rw [classSumBasis_repr_apply_zero]
  conv_lhs => rw [← (classSumBasis F R K).linearCombination_repr x]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Subalgebra.coe_mul,
    AddSubmonoidClass.coe_finsetSum, sum_mul, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum,
    Finset.sum_apply, Subalgebra.coe_smul, smul_mul_assoc, AddMonoidAlgebra.coeff_smul,
    Finsupp.smul_apply, coeff_classSumBasis_mul_classSumBasis_zero, smul_eq_mul, mul_ite,
    mul_zero, sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.mp h, zero_mul]

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
  classical
  let f : K[K] := (AddMonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm v').mapDomain u'
  refine ⟨f, ?_, ?_⟩
  · obtain ⟨i, hv'i⟩ : ∃ i, v' i ≠ 0 := by simpa [Function.ne_iff, Pi.zero_apply] using v0
    have h : f.coeff (u' i) ≠ 0 := by
      simpa [f, AddMonoidAlgebra.coeff_mapDomain, AddMonoidAlgebra.coeff_ofCoeff,
        Finsupp.mapDomain_apply_of_injective u'_inj]
    contrapose h
    simp [h]
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
      (v.sum fun c vc ↦ vc • ∑ x ∈ c.carrier, φ (.ofAdd x)) = 0 := by
  rw [← (classSumBasis F F K).repr.injective.ne_iff, map_zero] at x0
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr x0
  set x' := x * classSumBasis F F K (-i) with x'_def
  have hx' : (classSumBasis F F K).repr x' 0 ≠ 0 := by
    rw [x'_def, classSumBasis_repr_mul_classSumBasis_apply_zero, neg_neg]
    exact mul_ne_zero (Finsupp.mem_support_iff.mp hi)
      (Nat.cast_ne_zero.mpr (ConjRootClass.card_carrier_ne_zero i))
  have lift_x' : AddMonoidAlgebra.lift F _ _ φ x' = 0 := by
    rw [x'_def, Subalgebra.coe_mul, map_mul, hx, zero_mul]
  exact ⟨_, hx', by rw [← lift_eq_sum_classSumBasis_repr, lift_x']⟩

open Polynomial

open Classical in
theorem exists_sum_conjRootClass_eq_add_sum_map_aroots (A : Type*) {R F K S : Type*}
    [CommRing A] [Field F] [Algebra A F] [IsFractionRing A F]
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
    induction c using ConjRootClass.ind with | h x => ?_
    rcases eq_or_ne x 0 with (rfl | hx)
    · simp at hc
    rw [ConjRootClass.minpoly_mk]
    exact minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral x) hx
  · conv_lhs => rw [← Finsupp.single_add_erase 0 v]
    rw [Finsupp.sum_add_index' (by simp) (by simp [add_smul]), Finsupp.sum_single_index (by simp),
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
  let s := univ.image u ∪ univ.image v
  have hs : ∀ x ∈ s, IsIntegral ℚ x := by simp [s, or_imp, forall_and, hu, hv]
  let poly : ℚ[X] := ∏ x ∈ s, minpoly ℚ x
  let K : IntermediateField ℚ S := IntermediateField.adjoin ℚ (poly.rootSet S)
  have _ : IsSplittingField ℚ K poly :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : FiniteDimensional ℚ K := Polynomial.IsSplittingField.finiteDimensional K poly
  have : Normal ℚ K := .of_isSplittingField poly
  have mem_K {x : S} (hx : x ∈ s) : x ∈ K := by
    apply IntermediateField.subset_adjoin
    rw [mem_rootSet, map_prod, prod_eq_zero_iff]
    exact ⟨prod_ne_zero_iff.mpr fun x hx ↦ minpoly.ne_zero (hs x hx), x, hx, minpoly.aeval _ _⟩
  have u_mem (i) : u i ∈ K := mem_K (mem_union_left _ (mem_image_of_mem _ (mem_univ i)))
  have v_mem (i) : v i ∈ K := mem_K (mem_union_right _ (mem_image_of_mem _ (mem_univ i)))
  let u' : ι → K := fun i : ι ↦ ⟨u i, u_mem i⟩
  let v' : ι → K := fun i : ι ↦ ⟨v i, v_mem i⟩
  obtain ⟨f, f0, hf⟩ : ∃ (f : K[K]), f ≠ 0 ∧
    AddMonoidAlgebra.lift _ _ _
      (φ.comp (algebraMap K S).toAddMonoidHom.toMultiplicative) f = 0 := by
    refine exists_ne_zero_lift_eq_zero _ u' ?_ v' ?_ ?_
    · exact fun i j hij ↦ u_inj (Subtype.mk.inj hij)
    · simp_rw [Function.ne_iff, Pi.zero_apply] at v0 ⊢
      exact v0.imp fun i hvi ↦ by rwa [Ne, ← ZeroMemClass.coe_eq_zero]
    · simpa [u', v']
  have : IsDomain K[K] := NoZeroDivisors.to_isDomain _
  have : IsDomain ℚ[K] := NoZeroDivisors.to_isDomain _
  open scoped AlgebraMonoidAlgebra in
  obtain ⟨f, f0, hf⟩ := (Algebra.IsIntegral.isIntegral (R := ℚ[K]) f).isAlgebraic
    |>.exists_ne_zero_map_algebraMap_eq_zero _ f0 hf
  rw [AddMonoidAlgebra.algebraMap_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AddMonoidAlgebra.lift_mapRingHom_algebraMap] at hf
  have := Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra ℚ ℚ[K] Gal(K/ℚ)) ℚ[K] Gal(K/ℚ)
  obtain ⟨f, f0, hf⟩ :=
    (Algebra.IsIntegral.isIntegral (R := FixedPoints.subalgebra ℚ ℚ[K] Gal(K/ℚ)) f).isAlgebraic
    |>.exists_ne_zero_map_algebraMap_eq_zero _ f0 hf
  obtain ⟨v, v0, hv⟩ := exists_sum_conjRootClass_eq_zero _ f f0 hf
  obtain ⟨v', hsupp, hv'⟩ := IsFractionRing.exists_sum_smul_eq_zero ℤ _ v hv
  obtain ⟨w', hw', h⟩ := exists_sum_conjRootClass_eq_add_sum_map_aroots ℤ φ v'
  refine ⟨v' 0, by rwa [← Finsupp.mem_support_iff, hsupp, Finsupp.mem_support_iff], w', hw', ?_⟩
  rwa [h, zsmul_one] at hv'

end LindemannWeierstrass
