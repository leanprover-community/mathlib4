/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Algebra.Group.UniqueProds.VectorSpace
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Minpoly.ConjRootClass

/-!
# The Lindemann-Weierstrass theorem

## References

* [Jacobson, *Basic Algebra I, 4.12*][jacobson1974]
-/

noncomputable section

open scoped AddMonoidAlgebra BigOperators Polynomial

open Finset Polynomial

variable {R A : Type*} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]

namespace Quot

open Classical in
protected def liftFinsupp {α : Type*} {r : α → α → Prop} {β : Type*} [Zero β] (f : α →₀ β)
    (h : ∀ a b, r a b → f a = f b) : Quot r →₀ β := by
  refine ⟨image (mk r) f.support, Quot.lift f h, fun a => ⟨?_, ?_⟩⟩
  · rw [mem_image]; rintro ⟨b, hb, rfl⟩; exact Finsupp.mem_support_iff.mp hb
  · induction a using Quot.ind
    rw [lift_mk _ h]; refine fun hb => mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hb)

theorem liftFinsupp_mk {α : Type*} {r : α → α → Prop} {γ : Type*} [Zero γ] (f : α →₀ γ)
    (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) (a : α) : Quot.liftFinsupp f h (Quot.mk r a) = f a :=
  rfl

end Quot

namespace Quotient

@[reducible]
protected def liftFinsupp {α : Type*} {β : Type*} {s : Setoid α} [Zero β] (f : α →₀ β) :
    (∀ a b, a ≈ b → f a = f b) → Quotient s →₀ β :=
  Quot.liftFinsupp f

set_option linter.docPrime false in -- Quotient.mk'
@[simp]
theorem liftFinsupp_mk' {α : Type*} {β : Type*} {_ : Setoid α} [Zero β] (f : α →₀ β)
    (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) : Quotient.liftFinsupp f h (Quotient.mk' x) = f x :=
  rfl

end Quotient

section mapDomainFixed

variable {F R K : Type*} [Field F] [CommSemiring R] [Algebra F R] [Field K] [Algebra F K]

variable (F R K) in
def mapDomainFixed : Subalgebra R R[K] where
  carrier := {x | ∀ f : K ≃ₐ[F] K, x.domCongrAut F R f = x}
  mul_mem' {a b} ha hb f := by rw [map_mul, ha, hb]
  add_mem' {a b} ha hb f := by rw [map_add, ha, hb]
  algebraMap_mem' r f := by
    dsimp [AddMonoidAlgebra.domCongrAut]
    rw [AddMonoidAlgebra.domCongr_single, map_zero]

theorem mem_mapDomainFixed_iff {x : R[K]} :
    x ∈ mapDomainFixed F R K ↔ ∀ i j, i ∈ MulAction.orbit (K ≃ₐ[F] K) j → x i = x j := by
  simp_rw [MulAction.mem_orbit_iff]
  change (∀ f : K ≃ₐ[F] K, Finsupp.equivMapDomain f.toAddEquiv x = x) ↔ _
  refine ⟨fun h i j hij => ?_, fun h f => ?_⟩
  · obtain ⟨f, rfl⟩ := hij
    rw [AlgEquiv.smul_def, ← DFunLike.congr_fun (h f) (f j)]
    change x (f.symm (f j)) = _; rw [AlgEquiv.symm_apply_apply]
  · ext i; change x (f.symm i) = x i
    refine (h i (f.symm i) ⟨f, ?_⟩).symm
    rw [AlgEquiv.smul_def, AlgEquiv.apply_symm_apply]

variable (F R K) in
def mapDomainFixedEquivSubtype :
    mapDomainFixed F R K ≃ { f : R[K] // MulAction.orbitRel (K ≃ₐ[F] K) K ≤ Setoid.ker f } where
  toFun f := ⟨f, mem_mapDomainFixed_iff.mp f.2⟩
  invFun f := ⟨f, mem_mapDomainFixed_iff.mpr f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace mapDomainFixed
variable [FiniteDimensional F K] [Normal F K]

open Classical in
variable (F R K) in
def toFinsuppAux : mapDomainFixed F R K ≃ (ConjRootClass F K →₀ R) := by
  refine (mapDomainFixedEquivSubtype F R K).trans
    { toFun := fun f ↦
       Quotient.liftFinsupp (s := IsConjRoot.setoid _ _) (f : R[K]) (by
        change ∀ _ _, IsConjRoot F _ _ → _
        simp_rw [isConjRoot_iff_exists_algEquiv]
        exact f.2)
      invFun := fun f => ⟨?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨f.support.biUnion fun i => i.carrier.toFinset, fun x => f (ConjRootClass.mk F x),
      fun i => ?_⟩
    simp_rw [mem_biUnion, Set.mem_toFinset, ConjRootClass.mem_carrier, Finsupp.mem_support_iff,
      exists_eq_right']
  · change ∀ i j, i ∈ MulAction.orbit (K ≃ₐ[F] K) j → f ⟦i⟧ = f ⟦j⟧
    exact fun i j h => congr_arg f (Quotient.sound (isConjRoot_iff_exists_algEquiv.mpr h))
  · exact fun _ => Subtype.eq <| Finsupp.ext fun x => rfl
  · refine fun f => Finsupp.ext fun x => Quotient.inductionOn' x fun i => rfl

@[simp]
theorem toFinsuppAux_apply_apply_mk (f : mapDomainFixed F R K) (i : K) :
    toFinsuppAux F R K f (ConjRootClass.mk F i) = (f : R[K]) i :=
  rfl

variable (F R K) in
def toFinsupp : mapDomainFixed F R K ≃ₗ[R] ConjRootClass F K →₀ R where
  __ := toFinsuppAux F R K
  toFun := toFinsuppAux F R K
  invFun := (toFinsuppAux F R K).symm
  map_add' := fun x y => by
    ext i
    induction i
    simp_rw [Finsupp.coe_add, Pi.add_apply, toFinsuppAux_apply_apply_mk, AddMemClass.coe_add,
      (Finsupp.add_apply)]
  map_smul' := fun r x => by
    ext i
    induction i
    simp_rw [Finsupp.coe_smul, toFinsuppAux_apply_apply_mk]
    simp only [SetLike.val_smul, RingHom.id_apply]
    rw [Finsupp.coe_smul, Pi.smul_apply]
    rw [Pi.smul_apply]
    rw [toFinsuppAux_apply_apply_mk]

@[coe]
def coe : mapDomainFixed F R K → ConjRootClass F K →₀ R := toFinsupp F R K

instance : Coe (mapDomainFixed F R K) (ConjRootClass F K →₀ R) where
  coe := coe

instance : CoeFun (mapDomainFixed F R K) (fun _ ↦ ConjRootClass F K → R) where
  coe f := (f : ConjRootClass F K →₀ R)

@[simp]
theorem coe_toFinsupp :
    ⇑(toFinsupp F R K) = ((↑) : mapDomainFixed F R K → ConjRootClass F K →₀ R) :=
  rfl

@[simp]
theorem coe_apply (f : mapDomainFixed F R K) (i : K) :
    (f : R[K]) i = f (ConjRootClass.mk F i) :=
  rfl

@[simp]
theorem coe_injective :
    Function.Injective ((↑) : mapDomainFixed F R K → ConjRootClass F K →₀ R) :=
  (toFinsupp F R K).injective

@[simp, norm_cast]
theorem coe_zero :
    ↑(0 : mapDomainFixed F R K) = (0 : ConjRootClass F K →₀ R) :=
  map_zero _

@[simp, norm_cast]
theorem coe_add (f g : mapDomainFixed F R K) :
    ↑(f + g) = f + (g : ConjRootClass F K →₀ R) :=
  map_add _ _ _

@[simp, norm_cast]
theorem coe_sum {ι : Type*} (f : ι → mapDomainFixed F R K) (s : Finset ι) :
    ↑(∑ i ∈ s, f i) = ∑ i ∈ s, (f i : ConjRootClass F K →₀ R) :=
  map_sum _ _ _

theorem apply_mk (f : mapDomainFixed F R K) (i : K) :
    f (ConjRootClass.mk F i) = (f : R[K]) i :=
  rfl

@[simp]
theorem mk_apply_zero_eq (f : R[K]) (hf : f ∈ mapDomainFixed F R K) :
    (⟨f, hf⟩ : mapDomainFixed F R K) 0 = (f : R[K]) 0 :=
  rfl

open Classical in
def single (x : ConjRootClass F K) (a : R) :
    mapDomainFixed F R K :=
  ⟨Finsupp.indicator x.carrier.toFinset fun _ _ => a, by
    rw [mem_mapDomainFixed_iff]
    rintro i j h
    simp_rw [Finsupp.indicator_apply, Set.mem_toFinset]; dsimp; congr 1
    simp_rw [ConjRootClass.mem_carrier, eq_iff_iff]
    apply Eq.congr_left
    rwa [ConjRootClass.mk_eq_mk, isConjRoot_iff_exists_algEquiv]⟩

theorem coe_single (x : ConjRootClass F K) (a : R) :
    ↑(mapDomainFixed.single x a) = Finsupp.single x a := by
  classical
  ext i; induction i with | h i => ?_
  rw [apply_mk]
  simp only [single]
  rw [Finsupp.single_apply, Finsupp.indicator_apply]; dsimp; congr 1
  rw [Set.mem_toFinset, ConjRootClass.mem_carrier, eq_comm (a := x)]

theorem sum_single (x : mapDomainFixed F R K) :
    (x : ConjRootClass F K →₀ R).sum (mapDomainFixed.single (F := F) (K := K)) = x := by
  rw [← (toFinsupp F R K).injective.eq_iff, map_finsupp_sum,
    ← Finsupp.sum_single (toFinsupp F R K x), coe_toFinsupp]
  simp_rw [coe_single]

theorem single_mul_single_apply_zero_ne_zero_iff [CharZero F] [NoZeroDivisors R]
    (x : ConjRootClass F K) {a : R} (ha : a ≠ 0) (y : ConjRootClass F K) {b : R} (hb : b ≠ 0) :
    (mapDomainFixed.single x a * mapDomainFixed.single y b) 0 ≠ 0 ↔ x = -y := by
  classical
  simp_rw [mapDomainFixed.single, MulMemClass.mk_mul_mk]
  have := Nat.noZeroSMulDivisors F R
  simp_rw [Finsupp.indicator_eq_sum_single, sum_mul, mul_sum, AddMonoidAlgebra.single_mul_single,
    mk_apply_zero_eq, (Finsupp.coe_finset_sum), sum_apply, Finsupp.single_apply, ← sum_product',
    sum_ite, sum_const_zero, add_zero, sum_const, smul_ne_zero_iff, mul_ne_zero_iff,
    iff_true_intro ha, iff_true_intro hb, and_true, Ne, card_eq_zero, filter_eq_empty_iff,
    not_forall, not_not, exists_prop', nonempty_prop, Prod.exists, mem_product, Set.mem_toFinset]
  exact ConjRootClass.exist_mem_carrier_add_eq_zero x y

theorem single_mul_single_apply_zero_eq_zero_iff [CharZero F] [NoZeroDivisors R]
    (x : ConjRootClass F K) {a : R} (ha : a ≠ 0) (y : ConjRootClass F K) {b : R} (hb : b ≠ 0) :
    (mapDomainFixed.single x a * mapDomainFixed.single y b) 0 = 0 ↔ x ≠ -y :=
  (single_mul_single_apply_zero_ne_zero_iff x ha y hb).not_right

open Classical in
theorem lift_eq_sum_toFinsupp (A : Type*) [Semiring A] [Algebra R A]
    (φ : Multiplicative K →* A) (x : mapDomainFixed F R K) :
    AddMonoidAlgebra.lift R K A φ x =
      (x : ConjRootClass F K →₀ R).sum fun c xc ↦ xc • ∑ a ∈ c.carrier, φ (.ofAdd a) := by
  conv_lhs => rw [← mapDomainFixed.sum_single x]
  have (s' : Finset K) (b : R) :
      ((Finsupp.indicator s' fun _ _ => b).sum fun a c => c • φ (.ofAdd a)) =
        ∑ a ∈ s', b • φ (.ofAdd a) :=
    Finsupp.sum_indicator_index _ fun i _ => by rw [zero_smul]
  conv_lhs => rw [Finsupp.sum, AddSubmonoidClass.coe_finset_sum]
  simp_rw [map_sum, AddMonoidAlgebra.lift_apply, mapDomainFixed.single, this, smul_sum, Finsupp.sum]

end mapDomainFixed

end mapDomainFixed

open Complex

theorem linearIndependent_range_aux (F : Type*) {K G S : Type*}
    [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [AddCommMonoid G] [Semiring S] [NoZeroDivisors K[G]]
    (f : K[G] →+* S)
    (x : K[G]) (x0 : x ≠ 0) (hfx : f x = 0) :
    ∃ (y : F[G]), y ≠ 0 ∧ f (y.mapRangeAlgHom (algebraMap F K).toNatAlgHom) = 0 := by
  classical
  let y := ∏ f : K ≃ₐ[F] K, x.mapRangeAlgAut f
  have hy : ∀ f : K ≃ₐ[F] K, y.mapRangeAlgAut f = y := by
    intro f; dsimp only [y]
    simp_rw [map_prod, ← AlgEquiv.trans_apply, ← AlgEquiv.aut_mul, ← map_mul]
    exact (Group.mulLeft_bijective f).prod_comp fun g => x.mapRangeAlgAut g
  have y0 : y ≠ 0 := by
    dsimp only [y]; rw [prod_ne_zero_iff]; intro f _hf
    rwa [map_ne_zero_iff]
    apply EquivLike.injective
  have hfy : f y = 0 := by
    suffices
      f (x.mapRangeAlgAut 1 * ∏ f ∈ univ.erase 1, x.mapRangeAlgAut f) = 0 by
      convert this
      exact (mul_prod_erase (univ : Finset (K ≃ₐ[F] K)) _ (mem_univ _)).symm
    simp [map_one, hfx]
  have y_mem : ∀ i : G, y i ∈ IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[F] K)) := by
    intro i; dsimp [IntermediateField.fixedField, FixedPoints.intermediateField]
    rintro ⟨f, hf⟩; rw [Subgroup.smul_def, Subgroup.coe_mk]
    replace hy : y.mapRangeAlgAut f i = y i := by rw [hy f]
    rwa [AddMonoidAlgebra.mapRangeAlgAut_apply, AddMonoidAlgebra.mapRangeAlgEquiv_apply,
      Finsupp.mapRange_apply] at hy
  obtain ⟨y', hy'⟩ :
      y ∈ Set.range (AddMonoidAlgebra.mapRangeAlgHom (algebraMap F K).toNatAlgHom) := by
    simp [((IsGalois.tfae (F := F) (E := K)).out 0 1).mp (by infer_instance),
      IntermediateField.mem_bot] at y_mem
    rwa [AddMonoidAlgebra.mapRangeAlgHom_apply, Finsupp.range_mapRange]
  rw [← hy'] at y0 y_mem hfy
  rw [map_ne_zero_iff _
    (by simpa using Finsupp.mapRange_injective _ _ (algebraMap F K).injective)] at y0
  exact ⟨y', y0, hfy⟩

theorem linearIndependent_exp_aux2_1 {F K S : Type*}
    [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [NoZeroDivisors F[K]] [Semiring S] [Algebra F S]
    (f : F[K] →ₐ[F] S)
    (x : F[K]) (x0 : x ≠ 0) (hfx : f x = 0) :
    ∃ (y : mapDomainFixed F F K) (_ : y ≠ 0), f y = 0 := by
  classical
  refine ⟨⟨∏ f : K ≃ₐ[F] K, x.domCongrAut F _ (f : K ≃+ K), ?_⟩,
    fun h => absurd (Subtype.mk.inj h) ?_, ?_⟩
  · intro f
    rw [map_prod]
    simp_rw [← AlgEquiv.trans_apply, ← AlgEquiv.aut_mul, ← map_mul]
    exact (Group.mulLeft_bijective f).prod_comp fun g ↦ x.domCongrAut F _ (g : K ≃+ K)
  · simpa [prod_eq_zero_iff]
  · dsimp only
    rw [← mul_prod_erase univ _ (mem_univ 1), show ((1 : K ≃ₐ[F] K) : K ≃+ K) = 1 from rfl,
      map_one, AlgEquiv.one_apply, map_mul, hfx, zero_mul]

open Classical in
theorem linearIndependent_exp_aux2_2 {F K S : Type*}
    [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Normal F K] [CharZero F]
    [Semiring S] [Algebra F S]
    (φ : Multiplicative K →* S)
    (x : mapDomainFixed F F K) (x0 : x ≠ 0) (hx : AddMonoidAlgebra.lift F _ _ φ x = 0) :
    ∃ (w : F) (_w0 : w ≠ 0) (w' : ConjRootClass F K →₀ F) (_hw' : w' 0 = 0),
      (algebraMap F S w + w'.sum fun c wc ↦ wc • ∑ x ∈ c.carrier, φ (.ofAdd x)) = 0 := by
  rw [← (mapDomainFixed.coe_injective (F := F) (R := F) (K := K)).ne_iff,
    mapDomainFixed.coe_zero] at x0
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr x0
  set x' := x * mapDomainFixed.single (-i) (1 : F) with x'_def
  have hx' : x' 0 ≠ 0 := by
    rw [x'_def, ← mapDomainFixed.sum_single x,
      Finsupp.sum, ← add_sum_erase _ _ hi, add_mul, sum_mul, mapDomainFixed.coe_add,
      Finsupp.add_apply]
    convert_to ((mapDomainFixed.single i (x i) *
      mapDomainFixed.single (-i) 1 : mapDomainFixed F F K) 0 + 0 : F) ≠ 0
    · congr 1
      rw [mapDomainFixed.coe_sum, Finsupp.finset_sum_apply]
      refine sum_eq_zero fun j hj => ?_
      rw [mem_erase, Finsupp.mem_support_iff] at hj
      rw [mapDomainFixed.single_mul_single_apply_zero_eq_zero_iff _ hj.2]
      · rw [neg_neg]; exact hj.1
      · exact one_ne_zero
    rw [add_zero, mapDomainFixed.single_mul_single_apply_zero_ne_zero_iff]
    · rw [neg_neg]
    · rwa [Finsupp.mem_support_iff] at hi
    · exact one_ne_zero
  have zero_mem : (0 : ConjRootClass F K) ∈ (x' : ConjRootClass F K →₀ F).support := by
    rwa [Finsupp.mem_support_iff]
  have lift_x' : AddMonoidAlgebra.lift F _ _ φ x' = 0 := by
    dsimp only [x']
    rw [Subalgebra.coe_mul, map_mul, hx, zero_mul]
  use x' 0, hx', (x' : ConjRootClass F K →₀ F).erase 0, Finsupp.erase_same
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
  let f : K[K] :=
    Finsupp.onFinset (image u' univ)
      (fun x =>
        if hx : x ∈ image u' univ then
          v' (u'_inj.invOfMemRange ⟨x, mem_image_univ_iff_mem_range.mp hx⟩)
        else 0)
      fun x => by contrapose!; intro hx; rw [dif_neg hx]
  refine ⟨f, ?_, ?_⟩
  · simp_rw [Ne, funext_iff, Pi.zero_apply] at v0; push_neg at v0
    obtain ⟨i, hv'i⟩ := v0
    have h : f (u' i) ≠ 0 := by
      rwa [Finsupp.onFinset_apply, dif_pos, u'_inj.right_inv_of_invOfMemRange, Ne]
      exact mem_image_of_mem _ (mem_univ _)
    intro f0
    rw [f0, Finsupp.zero_apply] at h
    exact absurd rfl h
  · rw [AddMonoidAlgebra.lift_apply, ← h, Finsupp.onFinset_sum _ fun a => _]; swap
    · intro _; rw [zero_smul]
    rw [sum_image, sum_congr rfl]; swap; · exact fun i _ j _ hij => u'_inj hij
    intro x _
    rw [dif_pos, u'_inj.right_inv_of_invOfMemRange, Algebra.smul_def]
    exact mem_image_of_mem _ (mem_univ _)

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
  have x0 : x ≠ 0 := by
    rintro ⟨rfl⟩
    simp [eq_comm, N0, w0] at hx
  use x, x0, .indicator w'.support (fun i hi ↦ x' (w' i) (by simpa [Finsupp.mem_frange] using hi)),
    by simp [hw']
  rw [Finsupp.sum] at h
  rw [Finsupp.sum_indicator_index_eq_sum_attach _ (by simp)]
  simp_rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R F S, hx, hx', Algebra.smul_def,
    map_mul, mul_assoc, ← mul_sum, ← mul_add, ← Algebra.smul_def,
    sum_attach _ fun x ↦ w' x • f x, h, smul_zero]

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
      rwa [eval_map, ← aeval_def, aeval_algebraMap_apply, _root_.map_ne_zero] at this
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
  have : c.minpoly.aroots S = (c.minpoly.aroots K).map (algebraMap K S) := by
    change roots _ = _
    rw [← roots_map, Polynomial.map_map, IsScalarTower.algebraMap_eq F K S]
    rw [splits_map_iff, RingHom.id_comp]; exact c.splits_minpoly
  rw [this, c.aroots_minpoly_eq_carrier_val, Multiset.map_map]; rfl

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
    rw [map_zero, aeval_def, eval₂_eq_eval_map, hb, eval_smul, smul_ne_zero_iff]
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
        (w + ∑ j, w' j • (((p j).aroots S).map (φ <| .ofAdd ·)).sum) = 0 := by
  classical
  let s := univ.image u ∪ univ.image v
  have hs : ∀ x ∈ s, IsIntegral ℚ x := by simp [s, or_imp, forall_and, hu, hv]
  let poly : ℚ[X] := ∏ x ∈ s, minpoly ℚ x
  let K : IntermediateField ℚ S := IntermediateField.adjoin ℚ (poly.rootSet S)
  let _ : Algebra K S := K.val.toRingHom.toAlgebra
  have _ : IsSplittingField ℚ K poly :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits_codomain poly)
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
    AddMonoidAlgebra.lift_mapRangeAlgHom_algebraMap] at hf
  obtain ⟨f, f0, hf⟩ := linearIndependent_exp_aux2_1 _ f f0 hf
  obtain ⟨w, w0, w', hw', h⟩ := linearIndependent_exp_aux2_2 _ f f0 hf
  obtain ⟨w, w0, w', hw', h⟩ := linearIndependent_exp_aux_int ℤ _ w w0 w' hw' h
  obtain ⟨n, p, hp, w', h⟩ := linearIndependent_exp_aux_aroots_rat _ w w' hw' h
  exact ⟨w, w0, n, linearIndependent_exp_aux_aroots_int ℤ _ w n p hp w' h⟩
