/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Algebra.Group.UniqueProds.VectorSpace
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Minpoly.ConjRootClass

/-!
# The Lindemann-Weierstrass theorem
-/

noncomputable section

open scoped BigOperators Classical Polynomial Nat AddMonoidAlgebra

open Finset Polynomial

variable {R A : Type*} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]

namespace AuxInstances

variable (p : ℚ[X])

/--
The intermediate field between ℚ and ℂ given by adjoining the roots of `p` to ℚ
-/
abbrev K' : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (p.rootSet ℂ)

instance K'.isSplittingField : IsSplittingField ℚ (K' p) p :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits_codomain p)

abbrev K : Type _ :=
  p.SplittingField

instance : CharZero (K p) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (K p)).injective

instance : IsGalois ℚ (K p) where

abbrev Lift : K' p ≃ₐ[ℚ] K p :=
  IsSplittingField.algEquiv (K' p) p

instance algebraKℂ : Algebra (K p) ℂ :=
  ((K' p).val.comp (Lift p).symm.toAlgHom).toRingHom.toAlgebra

instance : Algebra ℚ (K p) :=
  inferInstance

instance : SMul ℚ (K p) :=
  Algebra.toSMul

instance cache_ℚ_K_ℂ : IsScalarTower ℚ (K p) ℂ :=
  inferInstance

instance cache_ℤ_K_ℂ : IsScalarTower ℤ (K p) ℂ :=
  inferInstance

end AuxInstances

namespace Quot

@[reducible]
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

section

variable (s : Finset ℂ)

namespace Transcendental -- Conflict with Mathlib.NumberTheory.Dioph
abbrev Poly : ℚ[X] :=
  ∏ x in s, minpoly ℚ x
end Transcendental

open Transcendental

/--
The intermediate field between ℚ and ℂ given by adjoining the roots of `Poly s` to ℚ
-/
abbrev K' : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ((Poly s).rootSet ℂ)

abbrev K : Type _ :=
  (Poly s).SplittingField

abbrev Gal : Type _ :=
  (Poly s).Gal

abbrev Lift : K' s ≃ₐ[ℚ] K s :=
  IsSplittingField.algEquiv (K' s) (Poly s)


theorem algebraMap_K_apply (x) : algebraMap (K s) ℂ x = ((Lift s).symm x : ℂ) :=
  rfl

theorem poly_ne_zero (hs : ∀ x ∈ s, IsIntegral ℚ x) : Poly s ≠ 0 :=
  prod_ne_zero_iff.mpr fun x hx => minpoly.ne_zero (hs x hx)

--cache
instance : ZeroMemClass (IntermediateField ℚ (K s)) (K s) :=
  inferInstance
instance : AddCommMonoid (⊥ : IntermediateField ℚ (K s)) :=
  letI : AddCommGroup (⊥ : IntermediateField ℚ (K s)) := NonUnitalNonAssocRing.toAddCommGroup
  AddCommGroup.toAddCommMonoid
instance : Algebra ℚ (⊥ : IntermediateField ℚ (K s)) :=
  DivisionRing.toRatAlgebra

section mapDomainFixed

variable (K L G : Type*) [Field K] [Field L] [Algebra K L] [Field G] [Algebra K G]

noncomputable def mapDomainFixed : Subalgebra L L[G] where
  carrier := {x | ∀ f : G ≃ₐ[K] G, AddMonoidAlgebra.domCongrAut K _ f x = x}
  mul_mem' {a b} ha hb f := by rw [map_mul, ha, hb]
  add_mem' {a b} ha hb f := by rw [map_add, ha, hb]
  algebraMap_mem' r f := by
    dsimp [AddMonoidAlgebra.domCongrAut]
    rw [AddMonoidAlgebra.domCongr_single, map_zero]

theorem mem_mapDomainFixed_iff (x : L[G]) :
    x ∈ mapDomainFixed K L G ↔ ∀ i j, i ∈ MulAction.orbit (G ≃ₐ[K] G) j → x i = x j := by
  simp_rw [MulAction.mem_orbit_iff]
  change (∀ f : G ≃ₐ[K] G, Finsupp.equivMapDomain (↑(AlgEquiv.toAddEquiv f)) x = x) ↔ _
  refine ⟨fun h i j hij => ?_, fun h f => ?_⟩
  · obtain ⟨f, rfl⟩ := hij
    rw [AlgEquiv.smul_def, ← DFunLike.congr_fun (h f) (f j)]
    change x (f.symm (f j)) = _; rw [AlgEquiv.symm_apply_apply]
  · ext i; change x (f.symm i) = x i
    refine (h i ((AlgEquiv.symm f) i) ⟨f, ?_⟩).symm
    rw [AlgEquiv.smul_def, AlgEquiv.apply_symm_apply]

noncomputable def mapDomainFixedEquivSubtype :
    mapDomainFixed K L G ≃
      { f : L[G] // MulAction.orbitRel (G ≃ₐ[K] G) G ≤ Setoid.ker f }
    where
  toFun f := ⟨f, (mem_mapDomainFixed_iff K L G f).mp f.2⟩
  invFun f := ⟨f, (mem_mapDomainFixed_iff K L G f).mpr f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace mapDomainFixed
variable [FiniteDimensional K G] [Normal K G]
variable {K L G}

instance : SemilinearMapClass
    ((mapDomainFixed K L G) ≃ₗ[L] ConjRootClass K G →₀ L)
    (RingHom.id L)
    (mapDomainFixed K L G)
    (ConjRootClass K G →₀ L) :=
  inferInstance

instance : DistribMulActionSemiHomClass
    ((mapDomainFixed K L G) ≃ₗ[L] ConjRootClass K G →₀ L)
    (RingHom.id L)
    (mapDomainFixed K L G)
    (ConjRootClass K G →₀ L) :=
  inferInstance

instance : AddMonoidHomClass
    ((mapDomainFixed K L G) ≃ₗ[L] ConjRootClass K G →₀ L)
    (mapDomainFixed K L G)
    (ConjRootClass K G →₀ L) :=
  inferInstance

instance : AddHomClass
    ((mapDomainFixed K L G) ≃ₗ[L] ConjRootClass K G →₀ L)
    (mapDomainFixed K L G)
    (ConjRootClass K G →₀ L) :=
  inferInstance

instance : ZeroHomClass
    ((mapDomainFixed K L G) ≃ₗ[L] ConjRootClass K G →₀ L)
    (mapDomainFixed K L G)
    (ConjRootClass K G →₀ L) :=
  inferInstance

variable (K L G) in
def toFinsuppAux : mapDomainFixed K L G ≃ (ConjRootClass K G →₀ L) := by
  refine (mapDomainFixedEquivSubtype K L G).trans
    { toFun := fun f ↦
       Quotient.liftFinsupp (s := IsConjRoot.setoid _ _) (f : L[G]) (by
        change ∀ _ _, IsConjRoot K _ _ → _
        simp_rw [isConjRoot_iff_exists_algEquiv]
        exact f.2)
      invFun := fun f => ⟨?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨f.support.biUnion fun i => i.carrier.toFinset, fun x => f (ConjRootClass.mk K x),
      fun i => ?_⟩
    simp_rw [mem_biUnion, Set.mem_toFinset, ConjRootClass.mem_carrier, Finsupp.mem_support_iff,
      exists_eq_right']
  · change ∀ i j, i ∈ MulAction.orbit (G ≃ₐ[K] G) j → f (Quotient.mk'' i) = f (Quotient.mk'' j)
    exact fun i j h => congr_arg f (Quotient.sound' (isConjRoot_iff_exists_algEquiv.mpr h))
  · exact fun _ => Subtype.eq <| Finsupp.ext fun x => rfl
  · refine fun f => Finsupp.ext fun x => Quotient.inductionOn' x fun i => rfl

@[simp]
theorem toFinsuppAux_apply_apply_mk (f : mapDomainFixed K L G) (i : G) :
    toFinsuppAux K L G f (ConjRootClass.mk K i) = (f : L[G]) i :=
  rfl

variable (K L G) in
def toFinsupp : mapDomainFixed K L G ≃ₗ[L] ConjRootClass K G →₀ L where
  __ := toFinsuppAux K L G
  toFun := toFinsuppAux K L G
  invFun := (toFinsuppAux K L G).symm
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
def coe : mapDomainFixed K L G → ConjRootClass K G →₀ L := toFinsupp K L G

instance : Coe (mapDomainFixed K L G) (ConjRootClass K G →₀ L) where
  coe := coe

instance : CoeFun (mapDomainFixed K L G) (fun _ ↦ ConjRootClass K G → L) where
  coe f := (f : ConjRootClass K G →₀ L)

@[simp]
theorem coe_toFinsupp :
    ⇑(toFinsupp K L G) = ((↑) : mapDomainFixed K L G → ConjRootClass K G →₀ L) :=
  rfl

@[simp]
theorem coe_apply (f : mapDomainFixed K L G) (i : G) :
    (f : L[G]) i = f (ConjRootClass.mk K i) :=
  rfl

@[simp]
theorem coe_injective :
    Function.Injective ((↑) : mapDomainFixed K L G → ConjRootClass K G →₀ L) :=
  (toFinsupp K L G).injective

@[simp, norm_cast]
theorem coe_zero :
    ↑(0 : mapDomainFixed K L G) = (0 : ConjRootClass K G →₀ L) :=
  map_zero _

@[simp, norm_cast]
theorem coe_add (f g : mapDomainFixed K L G) :
    ↑(f + g) = f + (g : ConjRootClass K G →₀ L) :=
  map_add _ _ _

@[simp, norm_cast]
theorem coe_sum {ι : Type*} (f : ι → mapDomainFixed K L G) (s : Finset ι) :
    ↑(∑ i ∈ s, f i) = ∑ i ∈ s, (f i : ConjRootClass K G →₀ L) :=
  map_sum _ _ _

theorem apply_mk (f : mapDomainFixed K L G) (i : G) :
    f (ConjRootClass.mk K i) = (f : L[G]) i :=
  rfl

@[simp]
theorem mk_apply_zero_eq (f : L[G]) (hf : f ∈ mapDomainFixed K L G) :
    (⟨f, hf⟩ : mapDomainFixed K L G) 0 = (f : L[G]) 0 :=
  rfl

def single (x : ConjRootClass K G) (a : L) :
    mapDomainFixed K L G :=
  ⟨Finsupp.indicator x.carrier.toFinset fun _ _ => a, by
    rw [mem_mapDomainFixed_iff]
    rintro i j h
    simp_rw [Finsupp.indicator_apply, Set.mem_toFinset]; dsimp; congr 1
    simp_rw [ConjRootClass.mem_carrier, eq_iff_iff]
    apply Eq.congr_left
    rwa [ConjRootClass.mk_eq_mk, isConjRoot_iff_exists_algEquiv]⟩

theorem coe_single (x : ConjRootClass K G) (a : L) :
    ↑(mapDomainFixed.single x a) = Finsupp.single x a := by
  ext i; induction i with | h i => ?_
  rw [apply_mk]
  change Finsupp.indicator x.carrier.toFinset (fun _ _ => a) i = Finsupp.single x a _
  rw [Finsupp.single_apply, Finsupp.indicator_apply]; dsimp; congr 1
  rw [Set.mem_toFinset, ConjRootClass.mem_carrier, eq_comm (a := x)]

theorem sum_single (x : mapDomainFixed K L G) :
    (x : ConjRootClass K G →₀ L).sum (mapDomainFixed.single (K := K) (G := G)) = x := by
  rw [← (toFinsupp K L G).injective.eq_iff, map_finsupp_sum,
    ← Finsupp.sum_single ((toFinsupp K L G) x), coe_toFinsupp]
  simp_rw [coe_single]

theorem single_mul_single_apply_zero_ne_zero_iff [CharZero K]
    (x : ConjRootClass K G) {a : L} (ha : a ≠ 0) (y : ConjRootClass K G) {b : L} (hb : b ≠ 0) :
    (mapDomainFixed.single x a * mapDomainFixed.single y b) 0 ≠ 0 ↔ x = -y := by
  simp_rw [mapDomainFixed.single, MulMemClass.mk_mul_mk]
  haveI := Nat.noZeroSMulDivisors K L
  simp_rw [Finsupp.indicator_eq_sum_single, sum_mul, mul_sum, AddMonoidAlgebra.single_mul_single,
    mk_apply_zero_eq, (Finsupp.coe_finset_sum), sum_apply, Finsupp.single_apply, ← sum_product',
    sum_ite, sum_const_zero, add_zero, sum_const, smul_ne_zero_iff, mul_ne_zero_iff,
    iff_true_intro ha, iff_true_intro hb, and_true, Ne, card_eq_zero, filter_eq_empty_iff,
    not_forall, not_not, exists_prop', nonempty_prop, Prod.exists, mem_product, Set.mem_toFinset]
  exact ConjRootClass.exist_mem_carrier_add_eq_zero x y

theorem single_mul_single_apply_zero_eq_zero_iff [CharZero K]
    (x : ConjRootClass K G) {a : L} (ha : a ≠ 0) (y : ConjRootClass K G) {b : L} (hb : b ≠ 0) :
    (mapDomainFixed.single x a * mapDomainFixed.single y b) 0 = 0 ↔ x ≠ -y :=
  (single_mul_single_apply_zero_ne_zero_iff x ha y hb).not_right

end mapDomainFixed

end mapDomainFixed

open Complex

section Eval

variable (F : Type*) [Field F] [Algebra F ℂ]

def Eval : F[K s] →ₐ[F] ℂ :=
  AddMonoidAlgebra.lift F (K s) ℂ
    (expMonoidHom.comp (AddMonoidHom.toMultiplicative (algebraMap (K s) ℂ).toAddMonoidHom))

theorem Eval_apply (x : F[K s]) :
    Eval s F x = x.sum fun a c => c • exp (algebraMap (K s) ℂ a) := by
  rw [Eval, AddMonoidAlgebra.lift_apply]
  simp_rw [RingHom.toAddMonoidHom_eq_coe, MonoidHom.coe_comp, AddMonoidHom.coe_toMultiplicative,
    AddMonoidHom.coe_coe, Function.comp_apply, expMonoidHom_apply, toAdd_ofAdd]

theorem Eval_mapRange (x : ℚ[K s]) :
    Eval s (K s) (AddMonoidAlgebra.mapRangeAlgHom (algebraMap ℚ (K s)).toNatAlgHom x) =
      Eval s ℚ x := by
  simp_rw [Eval_apply, Finsupp.sum, AddMonoidAlgebra.mapRangeAlgHom_apply, RingHom.toNatAlgHom_coe,
    Finsupp.mapRange_apply, algebraMap_smul,
    Finsupp.support_mapRange_of_injective _ _ (algebraMap ℚ (K s)).injective]

theorem Eval_eq_sum_toFinsupp (x : mapDomainFixed ℚ ℚ (K s)) :
    Eval s ℚ (x : mapDomainFixed ℚ ℚ (K s)) =
      (x : ConjRootClass ℚ (K s) →₀ ℚ).sum fun c xc ↦
        xc • ∑ i : K s in c.carrier.toFinset, exp (algebraMap (K s) ℂ i) := by
  conv_lhs => rw [← mapDomainFixed.sum_single x]
  have :
    ∀ (s' : Finset (K s)) (b : ℚ),
      ((Finsupp.indicator s' fun _ _ => b).sum fun a c => c • exp (algebraMap (K s) ℂ a)) =
        ∑ i in s', b • exp (algebraMap (K s) ℂ i) :=
    fun s' b => Finsupp.sum_indicator_index _ fun i _ => by rw [zero_smul]
  simp_rw [Finsupp.sum, AddSubmonoidClass.coe_finset_sum, map_sum, Eval_apply,
    mapDomainFixed.single, this, smul_sum]

end Eval

instance instIsDomain1 : NoZeroDivisors (K s)[K s] := inferInstance
instance instIsDomain2 : IsDomain ℚ[K s] := IsDomain.mk
instance : AddZeroClass (mapDomainFixed ℚ ℚ (K s)) := inferInstance

theorem linearIndependent_range_aux (K : Type*) {L G R : Type*}
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [AddCommMonoid G] [Semiring R] [NoZeroDivisors L[G]]
    (f : L[G] →+* R)
    (x : L[G]) (x0 : x ≠ 0) (hfx : f x = 0) :
    ∃ (y : K[G]), y ≠ 0 ∧ f (y.mapRangeAlgHom (algebraMap K L).toNatAlgHom) = 0 := by
  let y := ∏ f : L ≃ₐ[K] L, x.mapRangeAlgAut f
  have hy : ∀ f : L ≃ₐ[K] L, y.mapRangeAlgAut f = y := by
    intro f; dsimp only [y]
    simp_rw [map_prod, ← AlgEquiv.trans_apply, ← AlgEquiv.aut_mul, ← map_mul]
    exact (Group.mulLeft_bijective f).prod_comp fun g => AddMonoidAlgebra.mapRangeAlgAut g x
  have y0 : y ≠ 0 := by
    dsimp only [y]; rw [prod_ne_zero_iff]; intro f _hf
    rwa [AddEquivClass.map_ne_zero_iff]
  have hfy : f y = 0 := by
    suffices
      f (AddMonoidAlgebra.mapRangeAlgAut 1 x *
          ∏ f : L ≃ₐ[K] L in univ.erase 1, AddMonoidAlgebra.mapRangeAlgAut f x) = 0 by
      convert this
      exact (mul_prod_erase (univ : Finset (L ≃ₐ[K] L)) _ (mem_univ _)).symm
    simp [map_one, hfx]
  have y_mem : ∀ i : G, y i ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := by
    intro i; dsimp [IntermediateField.fixedField, FixedPoints.intermediateField]
    rintro ⟨f, hf⟩; rw [Subgroup.smul_def, Subgroup.coe_mk]
    replace hy : AddMonoidAlgebra.mapRangeAlgAut f y i = y i := by rw [hy f]
    rwa [AddMonoidAlgebra.mapRangeAlgAut_apply, AddMonoidAlgebra.mapRangeAlgEquiv_apply,
      Finsupp.mapRange_apply] at hy
  obtain ⟨y', hy'⟩ :
      y ∈ Set.range (AddMonoidAlgebra.mapRangeAlgHom (algebraMap K L).toNatAlgHom) := by
    simp [((IsGalois.tfae (F := K) (E := L)).out 0 1).mp (by infer_instance),
      IntermediateField.mem_bot] at y_mem
    rwa [AddMonoidAlgebra.mapRangeAlgHom_apply, Finsupp.range_mapRange]
  rw [← hy'] at y0 y_mem hfy
  rw [map_ne_zero_iff _
    (by simpa using Finsupp.mapRange_injective _ _ (algebraMap K L).injective)] at y0
  exact ⟨y', y0, hfy⟩

theorem linearIndependent_exp_aux2_1 {K L R : Type*}
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Normal K L] [NoZeroDivisors K[L]]
    [Semiring R] [Algebra K R]
    (f : K[L] →ₐ[K] R)
    (x : K[L]) (x0 : x ≠ 0) (hfx : f x = 0) :
    ∃ (y : mapDomainFixed K K L) (_ : y ≠ 0), f y = 0 := by
  refine ⟨⟨∏ f : L ≃ₐ[K] L, x.domCongrAut K _ (f : L ≃+ L), ?_⟩,
    fun h => absurd (Subtype.mk.inj h) ?_, ?_⟩
  · intro f
    rw [map_prod]
    simp_rw [← AlgEquiv.trans_apply, ← AlgEquiv.aut_mul, ← map_mul]
    exact
      (Group.mulLeft_bijective f).prod_comp fun g =>
        AddMonoidAlgebra.domCongrAut K _ (g : L ≃+ L) x
  · simpa [prod_eq_zero_iff]
  · dsimp only
    rw [← mul_prod_erase (univ : Finset (L ≃ₐ[K] L)) _ (mem_univ 1),
      show ((1 : L ≃ₐ[K] L) : L ≃+ L) = 1 from rfl,
      map_one, AlgEquiv.one_apply, map_mul, hfx, zero_mul]

theorem linearIndependent_exp_aux2_2
    (x : mapDomainFixed ℚ ℚ (K s)) (x0 : x ≠ 0) (hx : Eval s ℚ x = 0) :
    ∃ (w : ℚ) (_w0 : w ≠ 0) (w' : ConjRootClass ℚ (K s) →₀ ℚ) (_hw' : w' 0 = 0),
      (w + w'.sum fun c wc ↦ wc • ∑ x in c.carrier, exp (algebraMap (K s) ℂ x)) = 0 := by
  rw [← (mapDomainFixed.coe_injective (K := ℚ) (L := ℚ) (G := K s)).ne_iff,
    mapDomainFixed.coe_zero] at x0
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr x0
  set x' := x * mapDomainFixed.single (-i) (1 : ℚ) with x'_def
  have hx' : x' 0 ≠ 0 := by
    rw [x'_def, ← mapDomainFixed.sum_single x,
      Finsupp.sum, ← add_sum_erase _ _ hi, add_mul, sum_mul, mapDomainFixed.coe_add,
      Finsupp.add_apply]
    convert_to ((mapDomainFixed.single i (x i) *
      mapDomainFixed.single (-i) 1 : mapDomainFixed ℚ ℚ (K s)) 0 + 0 : ℚ) ≠ 0
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
  have zero_mem : (0 : ConjRootClass ℚ (K s)) ∈ (x' : ConjRootClass ℚ (K s) →₀ ℚ).support := by
    rwa [Finsupp.mem_support_iff]
  have Eval_x' : Eval s ℚ x' = 0 := by
    dsimp only [x']
    rw [Subalgebra.coe_mul, map_mul, hx, zero_mul]
  use x' 0, hx', (x' : ConjRootClass ℚ (K s) →₀ ℚ).erase 0, Finsupp.erase_same
  rw [← Eval_x', Eval_eq_sum_toFinsupp, ← Finsupp.add_sum_erase _ _ _ zero_mem]
  congr 1
  simp_rw [ConjRootClass.carrier_zero, Set.toFinset_singleton, sum_singleton, map_zero, exp_zero,
    Rat.smul_one_eq_cast]

theorem linearIndependent_exp_aux2 (s : Finset ℂ) (x : ℚ[K s]) (x0 : x ≠ 0)
    (x_ker : x ∈ RingHom.ker (Eval s ℚ)) :
    ∃ (w : ℚ) (_w0 : w ≠ 0) (w' : ConjRootClass ℚ (K s) →₀ ℚ) (_hw' : w' 0 = 0),
      (w + w'.sum fun c wc ↦ wc • ∑ x in c.carrier, exp (algebraMap (K s) ℂ x)) = 0 := by
  obtain ⟨y, y0, hy⟩ := linearIndependent_exp_aux2_1 _ x x0 x_ker
  exact linearIndependent_exp_aux2_2 s y y0 hy

theorem linearIndependent_exp_aux1 (s : Finset ℂ) (x : (K s)[K s]) (x0 : x ≠ 0)
    (x_ker : x ∈ RingHom.ker (Eval s (K s))) :
    ∃ (w : ℚ) (_w0 : w ≠ 0) (w' : ConjRootClass ℚ (K s) →₀ ℚ) (_hw' : w' 0 = 0),
      (w + w'.sum fun c wc ↦ wc • ∑ x in c.carrier, exp (algebraMap (K s) ℂ x)) = 0 := by
  obtain ⟨y, y0, hfy⟩ := linearIndependent_range_aux ℚ _ x x0 x_ker
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Eval_mapRange] at hfy
  exact linearIndependent_exp_aux2 s y y0 hfy

end

open Complex

variable {ι : Type*} [Fintype ι]

abbrev range (u : ι → ℂ) (v : ι → ℂ) : Finset ℂ :=
  univ.image u ∪ univ.image v

theorem linearIndependent_exp_aux_rat_2
    (s : Finset ℂ)
    (u' : ι → K s) (u'_inj : Function.Injective u')
    (v' : ι → K s) (v0 : v' ≠ 0)
    (h : ∑ i : ι, (algebraMap (K s) ℂ) (v' i) * cexp ((algebraMap (K s) ℂ) (u' i)) = 0) :
    ∃ (f : (K s)[K s]), f ≠ 0 ∧ Eval s (K s) f = 0 := by
  let f : (K s)[K s] :=
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
  · rw [Eval_apply, ← h, Finsupp.onFinset_sum _ fun a => _]; swap; · intro _; rw [zero_smul]
    rw [sum_image, sum_congr rfl]; swap; · exact fun i _ j _ hij => u'_inj hij
    intro x _
    rw [dif_pos, u'_inj.right_inv_of_invOfMemRange]; · rfl
    exact mem_image_of_mem _ (mem_univ _)

theorem linearIndependent_exp_aux_rat_1 (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i)) (v0 : v ≠ 0)
    (h : ∑ i, v i * exp (u i) = 0) :
    ∃ (f : (K (range u v))[K (range u v)]), f ≠ 0 ∧ Eval (range u v) (K (range u v)) f = 0 := by
  set s := range u v
  have hs : ∀ x ∈ s, IsIntegral ℚ x := by
    intro x hx
    cases' mem_union.mp hx with hxu hxv
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hxu
      exact hu i
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hxv
      exact hv i
  have u_mem : ∀ i, u i ∈ K' s := by
    intro i
    apply IntermediateField.subset_adjoin
    rw [mem_rootSet, map_prod, prod_eq_zero_iff]
    exact
      ⟨poly_ne_zero s hs, u i, mem_union_left _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩),
        minpoly.aeval _ _⟩
  have v_mem : ∀ i, v i ∈ K' s := by
    intro i
    apply IntermediateField.subset_adjoin
    rw [mem_rootSet, map_prod, prod_eq_zero_iff]
    exact
      ⟨poly_ne_zero s hs, v i, mem_union_right _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩),
        minpoly.aeval _ _⟩
  let u' : ι → K s := fun i : ι => Lift s ⟨u i, u_mem i⟩
  let v' : ι → K s := fun i : ι => Lift s ⟨v i, v_mem i⟩
  refine linearIndependent_exp_aux_rat_2 s u' ?_ v' ?_ ?_
  · exact fun i j hij ↦ u_inj (Subtype.mk.inj ((Lift s).injective hij))
  · simp_rw [Ne, funext_iff, Pi.zero_apply] at v0 ⊢; push_neg at v0 ⊢
    refine v0.imp fun i hvi ↦ ?_
    rwa [Ne, map_eq_zero_iff _ (AlgEquiv.injective _), ← ZeroMemClass.coe_eq_zero]
  · simp_rw [algebraMap_K_apply, u', v', AlgEquiv.symm_apply_apply, h]

theorem linearIndependent_exp_aux_rat (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i)) (v0 : v ≠ 0)
    (h : ∑ i, v i * exp (u i) = 0) :
    ∃ (w : ℚ) (_w0 : w ≠ 0) (w' : ConjRootClass ℚ (K (range u v)) →₀ ℚ) (_hw' : w' 0 = 0),
      (w + w'.sum fun c wc ↦ wc • ∑ x in c.carrier, exp (algebraMap (K (range u v)) ℂ x)) = 0 := by
  obtain ⟨f, f0, hf⟩ := linearIndependent_exp_aux_rat_1 u hu u_inj v hv v0 h
  exact linearIndependent_exp_aux1 (range u v) f f0 hf

theorem linearIndependent_exp_aux_int_1
    (s : Finset ℂ)
    (w : ℚ) (w0 : w ≠ 0) (w' : ConjRootClass ℚ (K s) →₀ ℚ) (hw' : w' 0 = 0)
    (h : (w + w'.sum fun c wc ↦ wc • ∑ x in c.carrier, exp (algebraMap (K s) ℂ x) : ℂ) = 0) :
    ∃ (w : ℤ) (_w0 : w ≠ 0) (w' : ConjRootClass ℚ (K s) →₀ ℤ) (_hw' : w' 0 = 0),
      (w + w'.sum fun c wc ↦ wc • ∑ x in c.carrier, exp (algebraMap (K s) ℂ x)) = 0 := by
  let N := w.den * ∏ c in w'.support, (w' c).den
  have N0 : N ≠ 0 := by
    rw [mul_ne_zero_iff, prod_ne_zero_iff]
    exact ⟨Rat.den_nz _, fun c _hc => Rat.den_nz _⟩
  have wN0 : (w * N).num ≠ 0 := by positivity
  use (w * N).num, wN0, w'.mapRange (fun wc => (wc * N : ℚ).num) (by simp), by simp [hw']
  rw [Finsupp.sum_mapRange_index (by simp)]
  have hw : ((w * N).num : ℂ) = w * N := by
    norm_cast; dsimp only [N]
    rw [← Rat.den_eq_one_iff, Nat.cast_mul, ← mul_assoc, Rat.mul_den_eq_num]
    norm_cast
  have hw' c : ((w' c * N).num : ℂ) = w' c * N := by
    norm_cast; dsimp only [N]
    by_cases hc : c ∈ w'.support
    · rw [← Rat.den_eq_one_iff, ← mul_prod_erase _ _ hc, mul_left_comm, Nat.cast_mul, ← mul_assoc,
        Rat.mul_den_eq_num]
      norm_cast
    · simp [Finsupp.not_mem_support_iff.mp hc]
  simp_rw [Finsupp.sum, hw, zsmul_eq_mul, hw', mul_comm _ (N : ℂ), mul_assoc, ← mul_sum, ← mul_add,
    ← nsmul_eq_mul, smul_eq_zero_iff_right N0]
  exact h

theorem linearIndependent_exp_aux_int (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i)) (v0 : v ≠ 0)
    (h : ∑ i, v i * exp (u i) = 0) :
    ∃ (w : ℤ) (_w0 : w ≠ 0) (w' : ConjRootClass ℚ (K (range u v)) →₀ ℤ) (_hw' : w' 0 = 0),
      (w + w'.sum fun c wc ↦ wc • ∑ x in c.carrier, exp (algebraMap (K (range u v)) ℂ x)) = 0 := by
  obtain ⟨w, w0, w', hw', h⟩ := linearIndependent_exp_aux_rat u hu u_inj v hv v0 h
  exact linearIndependent_exp_aux_int_1 (range u v) w w0 w' hw' h

theorem linearIndependent_exp_aux_aroots_rat_1
    (s : Finset ℂ)
    (w : ℤ) (w0 : w ≠ 0) (w' : ConjRootClass ℚ (K s) →₀ ℤ) (hw' : w' 0 = 0)
    (h : (w + w'.sum fun c wc ↦ wc • ∑ x ∈ c.carrier, cexp (algebraMap (K s) ℂ x)) = 0) :
    ∃ (w : ℤ) (_w0 : w ≠ 0) (n : ℕ) (p : Fin n → ℚ[X]) (_hp : ∀ j, (p j).eval 0 ≠ 0)
      (w' : Fin n → ℤ),
        (w + ∑ j, w' j • (((p j).aroots ℂ).map fun x => exp x).sum : ℂ) = 0 := by
  let q := w'.support
  let c : Fin q.card → ConjRootClass ℚ (K s) := fun j => q.equivFin.symm j
  have hc : ∀ j, c j ∈ q := fun j => Finset.coe_mem _
  refine ⟨w, w0, q.card, fun j => (c j).minpoly, ?_, fun j => w' (c j), ?_⟩
  · intro j; specialize hc j
    suffices ((c j).minpoly.map (algebraMap ℚ (K s))).eval
        (algebraMap ℚ (K s) 0) ≠ 0 by
      rwa [eval_map, ← aeval_def, aeval_algebraMap_apply, _root_.map_ne_zero] at this
    rw [RingHom.map_zero, ConjRootClass.minpoly.map_eq_prod, eval_prod, prod_ne_zero_iff]
    intro a ha
    rw [eval_sub, eval_X, eval_C, sub_ne_zero]
    rintro rfl
    rw [Set.mem_toFinset, ConjRootClass.mem_carrier, ConjRootClass.mk_zero] at ha
    rw [← ha] at hc
    simp [q, hw'] at hc
  rw [← h, add_right_inj]
  change ∑ j, ((fun c => w' c • ((c.minpoly.aroots ℂ).map exp).sum) ·) (q.equivFin.symm j) = _
  -- Porting note: were `rw [Equiv.sum_comp q.equivFin.symm, sum_coe_sort]`
  rw [Equiv.sum_comp q.equivFin.symm ((fun c ↦ w' c • ((c.minpoly.aroots ℂ).map exp).sum) ·),
    sum_coe_sort _ (fun c ↦ w' c • ((c.minpoly.aroots ℂ).map exp).sum)]
  refine sum_congr rfl fun c _hc => ?_
  have : c.minpoly.aroots ℂ =
      (c.minpoly.aroots (K s)).map (algebraMap (K s) ℂ) := by
    change roots _ = _
    rw [← roots_map, Polynomial.map_map, IsScalarTower.algebraMap_eq ℚ (K s) ℂ]
    rw [splits_map_iff, RingHom.id_comp]; exact c.splits_minpoly
  rw [this, c.aroots_minpoly_eq_carrier_val, Multiset.map_map]; rfl

theorem linearIndependent_exp_aux_aroots_rat (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i)) (v0 : v ≠ 0)
    (h : ∑ i, v i * exp (u i) = 0) :
    ∃ (w : ℤ) (_w0 : w ≠ 0) (n : ℕ) (p : Fin n → ℚ[X]) (_hp : ∀ j, (p j).eval 0 ≠ 0)
      (w' : Fin n → ℤ),
        w + ∑ j, w' j • (((p j).aroots ℂ).map fun x => exp x).sum = 0 := by
  obtain ⟨w, w0, w', hw', h⟩ := linearIndependent_exp_aux_int u hu u_inj v hv v0 h
  exact linearIndependent_exp_aux_aroots_rat_1 (range u v) w w0 w' hw' h

theorem linearIndependent_exp_aux_aroots_int_1
    (w : ℤ) (w0 : w ≠ 0) (n : ℕ) (p : Fin n → ℚ[X]) (hp : ∀ j, (p j).eval 0 ≠ 0)
    (w' : Fin n → ℤ) (h : w + ∑ j, w' j • (((p j).aroots ℂ).map fun x => exp x).sum = 0) :
    ∃ (w : ℤ) (_w0 : w ≠ 0) (n : ℕ) (p : Fin n → ℤ[X]) (_hp : ∀ j, (p j).eval 0 ≠ 0)
      (w' : Fin n → ℤ), w + ∑ j, w' j • (((p j).aroots ℂ).map fun x => exp x).sum = 0 := by
  choose b hb using
    fun j ↦ IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) (p j)
  refine
    ⟨w, w0, n, fun i => IsLocalization.integerNormalization (nonZeroDivisors ℤ) (p i), ?_, w', ?_⟩
  · intro j
    suffices
      aeval (algebraMap ℤ ℚ 0) (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (p j)) ≠ 0
      by rwa [aeval_algebraMap_apply, map_ne_zero_iff _ (algebraMap ℤ ℚ).injective_int] at this
    rw [map_zero, aeval_def, eval₂_eq_eval_map, hb, eval_smul, smul_ne_zero_iff]
    exact ⟨nonZeroDivisors.coe_ne_zero _, hp j⟩
  rw [← h, add_right_inj]
  refine sum_congr rfl fun j _hj => congr_arg _ (congr_arg _ (Multiset.map_congr ?_ fun _ _ => rfl))
  change roots _ = roots _
  rw [IsScalarTower.algebraMap_eq ℤ ℚ ℂ, ← Polynomial.map_map, hb,
    zsmul_eq_mul, ← C_eq_intCast, Polynomial.map_mul, map_C, roots_C_mul]
  rw [map_ne_zero_iff _ (algebraMap ℚ ℂ).injective, Int.cast_ne_zero]
  exact nonZeroDivisors.coe_ne_zero _

theorem linearIndependent_exp_aux_aroots_int (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i)) (v0 : v ≠ 0)
    (h : ∑ i, v i * exp (u i) = 0) :
    ∃ (w : ℤ) (_w0 : w ≠ 0) (n : ℕ) (p : Fin n → ℤ[X]) (_p0 : ∀ j, (p j).eval 0 ≠ 0)
      (w' : Fin n → ℤ),
        (w + ∑ j, w' j • (((p j).aroots ℂ).map fun x => exp x).sum : ℂ) = 0 := by
  obtain ⟨w, w0, n, p, hp, w', h⟩ := linearIndependent_exp_aux_aroots_rat u hu u_inj v hv v0 h
  exact linearIndependent_exp_aux_aroots_int_1 w w0 n p hp w' h
