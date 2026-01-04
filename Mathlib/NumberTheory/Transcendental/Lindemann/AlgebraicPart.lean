/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Algebra.Group.UniqueProds.VectorSpace
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Minpoly.ConjRootClass

/-!
# The Lindemann-Weierstrass theorem

## References

* [Jacobson, *Basic Algebra I, 4.12*][jacobson1974]
-/

@[expose] public section

noncomputable section

open scoped AddMonoidAlgebra

open Finset Polynomial

namespace AddMonoidAlgebra

-- avoid defeq abuse, see also #25273
/-- The coefficients `M →₀ R` of an element of the additive monoid algebra `R[M]`. -/
def coeff {R M} [Semiring R] (f : R[M]) : M →₀ R := f
/-- Construct an element of the additive monoid algebra `R[M]` from its coefficients `M →₀ R`. -/
def ofCoeff {R M} [Semiring R] (f : M →₀ R) : R[M] := f

@[simp]
lemma coeff_ofCoeff {R M} [Semiring R] (f : M →₀ R) :
    (AddMonoidAlgebra.ofCoeff f).coeff = f :=
  rfl

@[simp]
lemma coeff_sum {R M ι} [Semiring R] (s : Finset ι) (f : ι → R[M]) :
    (∑ i ∈ s, f i).coeff = ∑ i ∈ s, (f i).coeff :=
  rfl

@[simp]
lemma ofCoeff_sum {R M ι} [Semiring R] (s : Finset ι) (f : ι → M →₀ R) :
    ofCoeff (∑ i ∈ s, f i) = ∑ i ∈ s, ofCoeff (f i) :=
  rfl

@[simp]
lemma coeff_apply {R M} [Semiring R] (f : R[M]) (i : M) : f.coeff i = f i := rfl

@[simp]
lemma ofCoeff_apply {R M} [Semiring R] (f : M →₀ R) (i : M) : ofCoeff f i = f i := rfl

@[simp]
lemma ofCoeff_single {R M} [Semiring R] (i : M) (x : R) :
    ofCoeff (Finsupp.single i x) = AddMonoidAlgebra.single i x := rfl

@[simp]
lemma coeff_add {R M} [Semiring R] (f g : R[M]) : (f + g).coeff = f.coeff + g.coeff := rfl

-- Why is there already a `coeff_smul`? I think that's a mistake.
@[simp]
theorem coeff_smul' {M R A : Type*} [Semiring R] [SMulZeroClass A R]
    (a : A) (x : R[M]) (m : M) : (a • x).coeff m = a • x.coeff m :=
  rfl

end AddMonoidAlgebra

section mapDomainFixed

variable {F R K : Type*} [Field F] [CommSemiring R] [Algebra F R] [Field K] [Algebra F K]

variable (F R K) in
/-- The subalgebra of the `x : R[X]` fixed by `AddMonoidAlgebra.domCongrAut f` for all `f`. -/
def mapDomainFixed : Subalgebra R R[K] where
  carrier := {x | ∀ f : Gal(K/F), x.domCongrAut F R f = x}
  mul_mem' {a b} ha hb f := by rw [map_mul, ha, hb]
  add_mem' {a b} ha hb f := by rw [map_add, ha, hb]
  algebraMap_mem' r f := by simp

theorem mem_mapDomainFixed_iff {x : R[K]} :
    x ∈ mapDomainFixed F R K ↔ ∀ i j, i ∈ MulAction.orbit Gal(K/F) j → x i = x j := by
  simp? [MulAction.mem_orbit_iff, mapDomainFixed] says
    simp only [mapDomainFixed, AddMonoidAlgebra.domCongrAut_apply, Subalgebra.mem_mk,
      Subsemiring.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq,
      MulAction.mem_orbit_iff, AlgEquiv.smul_def, forall_exists_index]
  refine ⟨fun h i j f hi => ?_, fun h f => ?_⟩
  · simp [← hi, ← congr($(h f) (f j))]
  · ext i
    simpa using (h i (f.symm i) f (by simp)).symm

variable (F R K) in
/-- The equivalence between `mapDomainFixed F R K` and the `f : R[X]` with
`Setoid.ker f ≥ MulAction.orbitRel Gal(K/F) K`. -/
def mapDomainFixedEquivSubtype :
    mapDomainFixed F R K ≃ { f : R[K] // MulAction.orbitRel Gal(K/F) K ≤ Setoid.ker f } where
  toFun f := ⟨f, mem_mapDomainFixed_iff.mp f.2⟩
  invFun f := ⟨f, mem_mapDomainFixed_iff.mpr f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace mapDomainFixed
variable [FiniteDimensional F K] [Normal F K]

/-- Auxiliary definition for `mapDomainFixed.toFinsupp`. -/
def toFinsuppAux : mapDomainFixed F R K ≃ (ConjRootClass F K →₀ R) := by
  classical
  refine (mapDomainFixedEquivSubtype F R K).trans
    { toFun := fun f ↦
        Quot.liftFinsupp (r := IsConjRoot _) f.val.coeff (by
          simp_rw [isConjRoot_iff_exists_algEquiv]
          exact f.2)
      invFun := fun f => ⟨.ofCoeff ⟨f.support.biUnion fun i => i.carrier.toFinset,
        fun x => f (ConjRootClass.mk F x), fun i => ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · simp_rw [mem_biUnion, Set.mem_toFinset, ConjRootClass.mem_carrier, Finsupp.mem_support_iff,
      exists_eq_right']
  · change ∀ i j, i ∈ MulAction.orbit Gal(K/F) j → f ⟦i⟧ = f ⟦j⟧
    exact fun i j h => congr_arg f (Quotient.sound (isConjRoot_iff_exists_algEquiv.mpr h))
  · exact fun _ => Subtype.ext <| Finsupp.ext fun x => rfl
  · exact fun _ => Finsupp.ext fun x => Quot.inductionOn x fun i => rfl

@[simp]
private theorem toFinsuppAux_apply_apply_mk (f : mapDomainFixed F R K) (i : K) :
    toFinsuppAux f (ConjRootClass.mk F i) = f.val.coeff i :=
  rfl

/-- `mapDomainFixed F R K` is isomorphic to the finitely supported functions from
`ConjRootClass F K` into `R`. -/
def toFinsupp : mapDomainFixed F R K ≃ₗ[R] ConjRootClass F K →₀ R where
  toEquiv := toFinsuppAux
  map_add' x y := by
    ext i
    induction i
    simp_rw [Finsupp.coe_add, Pi.add_apply, Equiv.toFun_as_coe, toFinsuppAux_apply_apply_mk,
      AddMemClass.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  map_smul' r x := by
    ext i
    induction i
    simp_rw [Finsupp.coe_smul, Equiv.toFun_as_coe, toFinsuppAux_apply_apply_mk, SetLike.val_smul,
      RingHom.id_apply, AddMonoidAlgebra.coeff_smul', Pi.smul_apply, toFinsuppAux_apply_apply_mk]

@[simp]
theorem toFinsupp_apply (f : mapDomainFixed F R K) (i : K) :
    f.val i = toFinsupp f (ConjRootClass.mk F i) :=
  rfl

theorem toFinsupp_apply_mk (f : mapDomainFixed F R K) (i : K) :
    toFinsupp f (ConjRootClass.mk F i) = f.val i :=
  rfl

@[simp]
theorem toFinsupp_mk_apply_zero_eq (f : R[K]) (hf : f ∈ mapDomainFixed F R K) :
    toFinsupp (⟨f, hf⟩ : mapDomainFixed F R K) 0 = f.coeff 0 :=
  rfl

open Classical in
/-- The element of `mapDomainFixed F R K` given by `a` on `x` and `0` elsewhere. -/
def single (x : ConjRootClass F K) (a : R) :
    mapDomainFixed F R K :=
  ⟨.ofCoeff <| Finsupp.indicator x.carrier.toFinset fun _ _ => a, by
    rw [mem_mapDomainFixed_iff]
    rintro i j h
    simp_rw [AddMonoidAlgebra.ofCoeff_apply, Finsupp.indicator_apply, Set.mem_toFinset, dite_eq_ite]
    congr 1
    simp_rw [ConjRootClass.mem_carrier, eq_iff_iff]
    apply Eq.congr_left
    rwa [ConjRootClass.mk_eq_mk, isConjRoot_iff_exists_algEquiv]⟩

theorem toFinsupp_single (x : ConjRootClass F K) (a : R) :
    toFinsupp (mapDomainFixed.single x a) = Finsupp.single x a := by
  classical
  ext i; induction i with | h i => ?_
  rw [toFinsupp_apply_mk]
  simp only [single]
  rw [Finsupp.single_apply, AddMonoidAlgebra.ofCoeff_apply, Finsupp.indicator_apply, dite_eq_ite]
  congr 1
  rw [Set.mem_toFinset, ConjRootClass.mem_carrier, eq_comm (a := x)]

theorem toFinsupp_sum_single (x : mapDomainFixed F R K) :
    (toFinsupp x).sum (mapDomainFixed.single (F := F) (K := K)) = x := by
  simp_rw [← toFinsupp.injective.eq_iff, map_finsuppSum, toFinsupp_single, Finsupp.sum_single]

theorem single_mul_single_apply_zero_ne_zero_iff [CharZero F] [NoZeroDivisors R]
    (x : ConjRootClass F K) {a : R} (ha : a ≠ 0) (y : ConjRootClass F K) {b : R} (hb : b ≠ 0) :
    toFinsupp (mapDomainFixed.single x a * mapDomainFixed.single y b) 0 ≠ 0 ↔ x = -y := by
  classical
  simp_rw [mapDomainFixed.single, MulMemClass.mk_mul_mk]
  have : NoZeroSMulDivisors ℕ R := ⟨by simp [← Nat.cast_smul_eq_nsmul F, smul_eq_zero]⟩
  simp_rw [Finsupp.indicator_eq_sum_single, AddMonoidAlgebra.ofCoeff_sum,
    sum_mul, mul_sum, AddMonoidAlgebra.ofCoeff_single, AddMonoidAlgebra.single_mul_single,
    toFinsupp_mk_apply_zero_eq, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finset_sum, sum_apply,
    AddMonoidAlgebra.coeff_apply, AddMonoidAlgebra.single_apply, ← sum_product',
    sum_ite, sum_const_zero, add_zero, sum_const, smul_ne_zero_iff, mul_ne_zero_iff,
    iff_true_intro ha, iff_true_intro hb, and_true, Ne, card_eq_zero, filter_eq_empty_iff,
    not_forall, not_not, exists_prop', nonempty_prop, Prod.exists, mem_product, Set.mem_toFinset]
  convert ConjRootClass.exists_mem_carrier_add_eq_zero x y
  tauto

theorem single_mul_single_apply_zero_eq_zero_iff [CharZero F] [NoZeroDivisors R]
    (x : ConjRootClass F K) {a : R} (ha : a ≠ 0) (y : ConjRootClass F K) {b : R} (hb : b ≠ 0) :
    toFinsupp (mapDomainFixed.single x a * mapDomainFixed.single y b) 0 = 0 ↔ x ≠ -y :=
  (single_mul_single_apply_zero_ne_zero_iff x ha y hb).not_right

open Classical in
theorem lift_eq_sum_toFinsupp (A : Type*) [Semiring A] [Algebra R A]
    (φ : Multiplicative K →* A) (x : mapDomainFixed F R K) :
    AddMonoidAlgebra.lift R K A φ x =
      (toFinsupp x).sum fun c xc ↦ xc • ∑ a ∈ c.carrier, φ (.ofAdd a) := by
  conv_lhs => rw [← mapDomainFixed.toFinsupp_sum_single x]
  have (s' : Finset K) (b : R) :
      ((Finsupp.indicator s' fun _ _ => b).sum fun a c => c • φ (.ofAdd a)) =
        ∑ a ∈ s', b • φ (.ofAdd a) :=
    Finsupp.sum_indicator_index _ fun i _ => by rw [zero_smul]
  conv_lhs => rw [Finsupp.sum, AddSubmonoidClass.coe_finset_sum]
  simp_rw [map_sum, AddMonoidAlgebra.lift_apply]
  change (∑ i ∈ (toFinsupp x).support, Finsupp.sum (AddMonoidAlgebra.coeff _) _) = _
  simp_rw [mapDomainFixed.single, AddMonoidAlgebra.coeff_ofCoeff, this, smul_sum, Finsupp.sum]

end mapDomainFixed

end mapDomainFixed

open Complex

theorem linearIndependent_range_aux (F : Type*) {K G S : Type*}
    [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [AddCommMonoid G] [Semiring S] [NoZeroDivisors K[G]]
    (f : K[G] →+* S)
    (x : K[G]) (x0 : x ≠ 0) (hfx : f x = 0) :
    ∃ (y : F[G]), y ≠ 0 ∧ f (y.mapRangeRingHom _ (algebraMap F K)) = 0 := by
  classical
  let y := ∏ f : Gal(K/F), x.mapRangeAlgAut _ _ f
  have hy : ∀ f : Gal(K/F), y.mapRangeAlgAut _ _ f = y := by
    intro f; dsimp only [y]
    simp_rw [map_prod, ← AlgEquiv.trans_apply, ← AlgEquiv.aut_mul, ← map_mul]
    exact (Group.mulLeft_bijective f).prod_comp fun g => x.mapRangeAlgAut _ _ g
  have y0 : y ≠ 0 := by
    dsimp only [y]; rw [prod_ne_zero_iff]; intro f _hf
    rwa [map_ne_zero_iff]
    apply EquivLike.injective
  have hfy : f y = 0 := by
    suffices
      f (x.mapRangeAlgAut _ _ 1 * ∏ f ∈ univ.erase 1, x.mapRangeAlgAut _ _ f) = 0 by
      convert this
      exact (mul_prod_erase (univ : Finset Gal(K/F)) _ (mem_univ _)).symm
    simp [map_one, hfx]
  have y_mem : ∀ i : G, y i ∈ IntermediateField.fixedField (⊤ : Subgroup Gal(K/F)) := by
    intro i; dsimp [IntermediateField.fixedField, FixedPoints.intermediateField]
    rintro ⟨f, hf⟩; rw [Subgroup.smul_def, Subgroup.coe_mk]
    replace hy : y.mapRangeAlgAut _ _ f i = y i := by rw [hy f]
    simpa using hy
  obtain ⟨y', hy'⟩ : y ∈ Set.range (AddMonoidAlgebra.mapRangeRingHom _ (algebraMap F K)) := by
    simp [((IsGalois.tfae (F := F) (E := K)).out 0 1).mp (by infer_instance),
      IntermediateField.mem_bot] at y_mem
    rwa [AddMonoidAlgebra.coe_mapRangeRingHom, Finsupp.range_mapRange]
  rw [← hy'] at y0 y_mem hfy
  rw [map_ne_zero_iff _
    (by simpa [AddMonoidAlgebra.coe_mapRangeRingHom] using
      Finsupp.mapRange_injective _ _ (algebraMap F K).injective)] at y0
  exact ⟨y', y0, hfy⟩

theorem linearIndependent_exp_aux2_1 {F K S : Type*}
    [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [NoZeroDivisors F[K]] [Semiring S] [Algebra F S]
    (f : F[K] →ₐ[F] S)
    (x : F[K]) (x0 : x ≠ 0) (hfx : f x = 0) :
    ∃ (y : mapDomainFixed F F K) (_ : y ≠ 0), f y = 0 := by
  classical
  refine ⟨⟨∏ f : Gal(K/F), x.domCongrAut F _ (f : K ≃+ K), ?_⟩,
    fun h => absurd (Subtype.mk.inj h) ?_, ?_⟩
  · intro f
    rw [map_prod]
    simp_rw [← AlgEquiv.trans_apply, ← AlgEquiv.aut_mul, ← map_mul]
    exact (Group.mulLeft_bijective f).prod_comp fun g ↦ x.domCongrAut F _ (g : K ≃+ K)
  · simpa [prod_eq_zero_iff]
  · dsimp only
    rw [← mul_prod_erase univ _ (mem_univ 1), show ((1 : Gal(K/F)) : K ≃+ K) = 1 from rfl,
      map_one, AlgEquiv.one_apply, map_mul, hfx, zero_mul]

open Classical in
theorem linearIndependent_exp_aux2_2 {F K S : Type*}
    [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Normal F K] [CharZero F]
    [Semiring S] [Algebra F S]
    (φ : Multiplicative K →* S)
    (x : mapDomainFixed F F K) (x0 : x ≠ 0) (hx : AddMonoidAlgebra.lift F _ _ φ x = 0) :
    ∃ (w : F) (_w0 : w ≠ 0) (w' : ConjRootClass F K →₀ F) (_hw' : w' 0 = 0),
      (algebraMap F S w + w'.sum fun c wc ↦ wc • ∑ x ∈ c.carrier, φ (.ofAdd x)) = 0 := by
  rw [← (mapDomainFixed.toFinsupp.injective).ne_iff, map_zero] at x0
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr x0
  set x' := x * mapDomainFixed.single (-i) (1 : F) with x'_def
  have hx' : mapDomainFixed.toFinsupp x' 0 ≠ 0 := by
    rw [x'_def, ← mapDomainFixed.toFinsupp_sum_single x,
      Finsupp.sum, ← add_sum_erase _ _ hi, add_mul, sum_mul, map_add,
      Finsupp.add_apply]
    convert_to (mapDomainFixed.toFinsupp (mapDomainFixed.single i (mapDomainFixed.toFinsupp x i) *
      mapDomainFixed.single (-i) 1) 0 + 0 : F) ≠ 0
    · congr 1
      rw [map_sum, Finsupp.finset_sum_apply]
      refine sum_eq_zero fun j hj => ?_
      rw [mem_erase, Finsupp.mem_support_iff] at hj
      rw [mapDomainFixed.single_mul_single_apply_zero_eq_zero_iff _ hj.2]
      · rw [neg_neg]; exact hj.1
      · exact one_ne_zero
    rw [add_zero, mapDomainFixed.single_mul_single_apply_zero_ne_zero_iff]
    · rw [neg_neg]
    · rwa [Finsupp.mem_support_iff] at hi
    · exact one_ne_zero
  have zero_mem : (0 : ConjRootClass F K) ∈ (mapDomainFixed.toFinsupp x').support := by
    rwa [Finsupp.mem_support_iff]
  have lift_x' : AddMonoidAlgebra.lift F _ _ φ x' = 0 := by
    dsimp only [x']
    rw [Subalgebra.coe_mul, map_mul, hx, zero_mul]
  use mapDomainFixed.toFinsupp x' 0, hx', (mapDomainFixed.toFinsupp x').erase 0, Finsupp.erase_same
  rw [← lift_x', mapDomainFixed.lift_eq_sum_toFinsupp, ← Finsupp.add_sum_erase _ _ _ zero_mem]
  simp_rw [ConjRootClass.carrier_zero, Set.toFinset_singleton, sum_singleton, ofAdd_zero, map_one,
    Algebra.algebraMap_eq_smul_one]

variable {ι : Type*} [Fintype ι]

theorem linearIndependent_exp_aux_rat {K S : Type*}
    [Field K] [Semiring S] [Algebra K S]
    (φ : Multiplicative K →* S)
    (u' : ι → K) (u'_inj : Function.Injective u')
    (v' : ι → K) (v0 : v' ≠ 0)
    (h : ∑ i : ι, algebraMap K S (v' i) * φ (.ofAdd (u' i)) = 0) :
    ∃ (f : K[K]), f ≠ 0 ∧ AddMonoidAlgebra.lift _ _ _ φ f = 0 := by
  classical
  let f : K[K] := (Finsupp.equivFunOnFinite.symm v').mapDomain u'
  refine ⟨f, ?_, ?_⟩
  · simp_rw [Ne, funext_iff, Pi.zero_apply] at v0; push_neg at v0
    obtain ⟨i, hv'i⟩ := v0
    have h : f (u' i) ≠ 0 := by
      rw [Finsupp.mapDomain_apply u'_inj]
      simpa
    intro f0
    rw [f0, Finsupp.zero_apply] at h
    exact absurd rfl h
  · rw [AddMonoidAlgebra.lift_apply, ← h, Finsupp.sum_mapDomain_index_inj u'_inj]
    simp [Finsupp.sum_fintype, Algebra.smul_def]

theorem linearIndependent_exp_aux_int (R : Type*) {F K S : Type*}
    [CommRing R] [Nontrivial R] [Field F] [Algebra R F] [IsFractionRing R F]
    [Field K] [Algebra F K] [FiniteDimensional F K] [Normal F K]
    [Semiring S] [Algebra R S] [Algebra F S] [IsScalarTower R F S]
    (f : ConjRootClass F K → S)
    (w : F) (w0 : w ≠ 0) (w' : ConjRootClass F K →₀ F) (hw' : w' 0 = 0)
    (h : (algebraMap F S w + w'.sum fun c wc ↦ wc • f c) = 0) :
    ∃ (w : R) (_w0 : w ≠ 0) (w' : ConjRootClass F K →₀ R) (_hw' : w' 0 = 0),
      (algebraMap R S w + w'.sum fun c wc ↦ wc • f c) = 0 := by
  classical
  obtain ⟨⟨N, N0⟩, hN⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R) ({w} ∪ w'.frange)
  replace N0 := nonZeroDivisors.ne_zero N0
  simp only [mem_union, mem_singleton, IsLocalization.IsInteger, RingHom.mem_rangeS,
    forall_eq_or_imp] at hN
  choose x hx using hN.1
  choose x' hx' using hN.2
  set w'' := Finsupp.indicator w'.support
    (fun i hi ↦ x' (w' i) (by simpa [Finsupp.mem_frange] using hi)) with w''_def
  have hw'' : ∀ i, algebraMap R F (w'' i) = N • w' i := by
    simp only [w'', Finsupp.indicator_apply, Finsupp.mem_support_iff, ne_eq]
    intro i
    split_ifs with h0 <;> simp [h0, hx']
  have x0 : x ≠ 0 := by
    rintro ⟨rfl⟩
    simp [eq_comm, N0, w0] at hx
  use x, x0, w'', by simp [w'', hw']
  rw [Finsupp.sum] at h
  rw [Finsupp.sum_of_support_subset _ (Finsupp.support_indicator_subset _ _) _ (by simp), ← w''_def]
  simp_rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R F S, hx, hw'', Algebra.smul_def,
    map_mul, mul_assoc, ← mul_sum, ← mul_add, ← Algebra.smul_def, h, smul_zero]

open Classical in
theorem linearIndependent_exp_aux_aroots_rat {F K S : Type*}
    [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Normal F K] [CharZero F]
    [Field S] [Algebra K S] [Algebra F S] [IsScalarTower F K S]
    (φ : Multiplicative S →* S)
    (w : ℤ) (w' : ConjRootClass F K →₀ ℤ) (hw' : w' 0 = 0)
    (h : (w + w'.sum fun c wc ↦ wc • ∑ x ∈ c.carrier,
      φ.comp (algebraMap K S).toAddMonoidHom.toMultiplicative (.ofAdd x)) = 0) :
    ∃ (n : ℕ) (p : Fin n → F[X]) (_hp : ∀ j, (p j).eval 0 ≠ 0)
      (w' : Fin n → ℤ),
        (w + ∑ j, w' j • (((p j).aroots S).map fun x => φ (.ofAdd x)).sum) = 0 := by
  let q := w'.support
  let c : Fin q.card → ConjRootClass F K := fun j => q.equivFin.symm j
  have hc : ∀ j, c j ∈ q := fun j => Finset.coe_mem _
  refine ⟨q.card, fun j => (c j).minpoly, ?_, fun j => w' (c j), ?_⟩
  · intro j; specialize hc j
    suffices ((c j).minpoly.map (algebraMap F K)).eval (algebraMap F K 0) ≠ 0 by
      rwa [eval_map_algebraMap, aeval_algebraMap_apply, _root_.map_ne_zero] at this
    rw [RingHom.map_zero, ConjRootClass.minpoly.map_eq_prod, eval_prod, prod_ne_zero_iff]
    intro a ha
    rw [eval_sub, eval_X, eval_C, sub_ne_zero]
    rintro rfl
    rw [Set.mem_toFinset, ConjRootClass.mem_carrier, ConjRootClass.mk_zero] at ha
    rw [← ha] at hc
    simp [q, hw'] at hc
  rw [← h, add_right_inj]
  change ∑ j, ((fun c : q => w' c.1 • ((c.1.minpoly.aroots S).map (φ <| .ofAdd ·)).sum) ·) _ = _
  -- Porting note: were `rw [Equiv.sum_comp q.equivFin.symm, sum_coe_sort]`
  rw [Equiv.sum_comp q.equivFin.symm,
    sum_coe_sort _ (fun c ↦ w' c • ((c.minpoly.aroots S).map (φ <| .ofAdd ·)).sum)]
  refine sum_congr rfl fun c _hc => ?_
  rw [← c.splits_minpoly.aroots_map_algebraMap, c.aroots_minpoly_eq_carrier_val]
  simp

theorem linearIndependent_exp_aux_aroots_int (R : Type*) {F S : Type*}
    [CommRing R] [Nontrivial R] [Field F] [Algebra R F] [IsFractionRing R F]
    [CommRing S] [IsDomain S] [Algebra R S] [Algebra F S] [IsScalarTower R F S]
    (f : S → S)
    (w : ℤ) (n : ℕ) (p : Fin n → F[X]) (hp : ∀ j, (p j).eval 0 ≠ 0)
    (w' : Fin n → ℤ) (h : w + ∑ j, w' j • (((p j).aroots S).map f).sum = 0) :
    ∃ (p : Fin n → R[X]) (_hp : ∀ j, (p j).eval 0 ≠ 0)
      (w' : Fin n → ℤ), w + ∑ j, w' j • (((p j).aroots S).map f).sum = 0 := by
  choose b hb using
    fun j ↦ IsLocalization.integerNormalization_map_to_map (nonZeroDivisors R) (p j)
  refine ⟨fun i => IsLocalization.integerNormalization (nonZeroDivisors R) (p i), ?_, w', ?_⟩
  · intro j
    suffices aeval (algebraMap R F 0)
        (IsLocalization.integerNormalization (nonZeroDivisors R) (p j)) ≠ 0 by
      rwa [aeval_algebraMap_apply, map_ne_zero_iff _ (IsFractionRing.injective R F)] at this
    rw [map_zero, ← eval_map_algebraMap, hb, eval_smul, smul_ne_zero_iff]
    exact ⟨nonZeroDivisors.coe_ne_zero _, hp j⟩
  · rw [← h, add_right_inj]
    refine sum_congr rfl fun j _hj => congrArg _ (congrArg _ (Multiset.map_congr ?_ fun _ _ => rfl))
    change roots _ = roots _
    rw [IsScalarTower.algebraMap_eq R F S, ← Polynomial.map_map, hb,
      Algebra.smul_def, Polynomial.algebraMap_apply, Polynomial.map_mul, map_C, roots_C_mul]
    rw [map_ne_zero_iff _ (algebraMap F S).injective,
      map_ne_zero_iff _ (IsFractionRing.injective R F)]
    exact nonZeroDivisors.coe_ne_zero _

theorem linearIndependent_exp_aux {S : Type*}
    [Field S] [Algebra ℚ S] [IsAlgClosed S]
    (φ : Multiplicative S →* S)
    (u : ι → S) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → S) (hv : ∀ i, IsIntegral ℚ (v i)) (v0 : v ≠ 0)
    (h : ∑ i, v i * φ (.ofAdd <| u i) = 0) :
    ∃ (w : ℤ) (_w0 : w ≠ 0) (n : ℕ) (p : Fin n → ℤ[X]) (_p0 : ∀ j, (p j).eval 0 ≠ 0)
      (w' : Fin n → ℤ),
        w + ∑ j, w' j • (((p j).aroots S).map (φ <| .ofAdd ·)).sum = 0 := by
  classical
  let s := univ.image u ∪ univ.image v
  have hs : ∀ x ∈ s, IsIntegral ℚ x := by simp [s, or_imp, forall_and, hu, hv]
  let poly : ℚ[X] := ∏ x ∈ s, minpoly ℚ x
  let K : IntermediateField ℚ S := IntermediateField.adjoin ℚ (poly.rootSet S)
  let _ : Algebra K S := K.val.toRingHom.toAlgebra
  have _ : IsSplittingField ℚ K poly :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : FiniteDimensional ℚ K := Polynomial.IsSplittingField.finiteDimensional K poly
  have : Normal ℚ K := .of_isSplittingField poly
  have : IsGalois ℚ K := ⟨⟩
  have algebraMap_K_apply x : algebraMap K S x = x := rfl
  have poly_ne_0 : poly ≠ 0 := prod_ne_zero_iff.mpr fun x hx => minpoly.ne_zero (hs x hx)
  have u_mem : ∀ i, u i ∈ K := by
    intro i
    apply IntermediateField.subset_adjoin
    rw [mem_rootSet, map_prod, prod_eq_zero_iff]
    exact ⟨poly_ne_0, u i, mem_union_left _ (mem_image_of_mem _ (mem_univ _)), minpoly.aeval _ _⟩
  have v_mem : ∀ i, v i ∈ K := by
    intro i
    apply IntermediateField.subset_adjoin
    rw [mem_rootSet, map_prod, prod_eq_zero_iff]
    exact ⟨poly_ne_0, v i, mem_union_right _ (mem_image_of_mem _ (mem_univ _)), minpoly.aeval _ _⟩
  let u' : ι → K := fun i : ι => ⟨u i, u_mem i⟩
  let v' : ι → K := fun i : ι => ⟨v i, v_mem i⟩
  obtain ⟨f, f0, hf⟩ : ∃ (f : K[K]), f ≠ 0 ∧
    AddMonoidAlgebra.lift _ _ _
      (φ.comp (algebraMap K S).toAddMonoidHom.toMultiplicative) f = 0 := by
    refine linearIndependent_exp_aux_rat _ u' ?_ v' ?_ ?_
    · exact fun i j hij ↦ u_inj (Subtype.mk.inj hij)
    · simp_rw [Ne, funext_iff, Pi.zero_apply] at v0 ⊢; push_neg at v0 ⊢
      exact v0.imp fun i hvi ↦ by rwa [Ne, ← ZeroMemClass.coe_eq_zero]
    · simpa [algebraMap_K_apply, u', v']
  obtain ⟨f, f0, hf⟩ := linearIndependent_range_aux ℚ _ f f0 hf
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AddMonoidAlgebra.lift_mapRangeRingHom_algebraMap] at hf
  obtain ⟨f, f0, hf⟩ := linearIndependent_exp_aux2_1 _ f f0 hf
  obtain ⟨w, w0, w', hw', h⟩ := linearIndependent_exp_aux2_2 _ f f0 hf
  obtain ⟨w, w0, w', hw', h⟩ := linearIndependent_exp_aux_int ℤ _ w w0 w' hw' h
  obtain ⟨n, p, hp, w', h⟩ := linearIndependent_exp_aux_aroots_rat _ w w' hw' h
  exact ⟨w, w0, n, linearIndependent_exp_aux_aroots_int ℤ _ w n p hp w' h⟩
