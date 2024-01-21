/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Data.Complex.Exponential
import Mathlib.FieldTheory.GalConj

/-!
# The Lindemann-Weierstrass theorem
-/

noncomputable section

open scoped BigOperators Classical Polynomial Nat

open Finset Polynomial

variable {R A : Type*} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]

namespace AuxInstances

variable (p : ℚ[X])

abbrev K' : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (p.rootSet ℂ)
set_option linter.uppercaseLean3 false in
#align aux.K' AuxInstances.K'

instance K'.isSplittingField : IsSplittingField ℚ (K' p) p :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits_codomain p)
set_option linter.uppercaseLean3 false in
#align aux.K'.is_splitting_field AuxInstances.K'.isSplittingField

abbrev K : Type _ :=
  p.SplittingField
set_option linter.uppercaseLean3 false in
#align aux.K AuxInstances.K

instance : CharZero (K p) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (K p)).injective

instance : IsGalois ℚ (K p) where

abbrev Lift : K' p ≃ₐ[ℚ] K p :=
  IsSplittingField.algEquiv (K' p) p
set_option linter.uppercaseLean3 false in
#align aux.Lift AuxInstances.Lift

instance algebraKℂ : Algebra (K p) ℂ :=
  ((K' p).val.comp (Lift p).symm.toAlgHom).toRingHom.toAlgebra
set_option linter.uppercaseLean3 false in
#align aux.algebra_K_ℂ AuxInstances.algebraKℂ

instance : Algebra ℚ (K p) :=
  inferInstance

instance : SMul ℚ (K p) :=
  Algebra.toSMul

instance cache_ℚ_K_ℂ : IsScalarTower ℚ (K p) ℂ :=
  inferInstance
set_option linter.uppercaseLean3 false in
#align aux.cache_ℚ_K_ℂ AuxInstances.cache_ℚ_K_ℂ

instance cache_ℤ_K_ℂ : IsScalarTower ℤ (K p) ℂ :=
  inferInstance
set_option linter.uppercaseLean3 false in
#align aux.cache_ℤ_K_ℂ AuxInstances.cache_ℤ_K_ℂ

end AuxInstances

namespace Quot

@[reducible] --, elab_as_elim]
protected def liftFinsupp {α : Type*} {r : α → α → Prop} {β : Type*} [Zero β] (f : α →₀ β)
    (h : ∀ a b, r a b → f a = f b) : Quot r →₀ β := by
  refine' ⟨image (mk r) f.support, Quot.lift f h, fun a => ⟨_, _⟩⟩
  · rw [mem_image]; rintro ⟨b, hb, rfl⟩; exact Finsupp.mem_support_iff.mp hb
  · induction a using Quot.ind
    rw [lift_mk _ h]; refine' fun hb => mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hb)
#align quot.lift_finsupp Quot.liftFinsupp

theorem liftFinsupp_mk {α : Type*} {r : α → α → Prop} {γ : Type*} [Zero γ] (f : α →₀ γ)
    (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) (a : α) : Quot.liftFinsupp f h (Quot.mk r a) = f a :=
  rfl
#align quot.lift_finsupp_mk Quot.liftFinsupp_mk

end Quot

namespace Quotient

@[reducible] --, elab_as_elim]
protected def liftFinsupp {α : Type*} {β : Type*} [s : Setoid α] [Zero β] (f : α →₀ β) :
    (∀ a b, a ≈ b → f a = f b) → Quotient s →₀ β :=
  Quot.liftFinsupp f
#align quotient.lift_finsupp Quotient.liftFinsupp

@[simp]
theorem liftFinsupp_mk' {α : Type*} {β : Type*} [Setoid α] [Zero β] (f : α →₀ β)
    (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) : Quotient.liftFinsupp f h (Quotient.mk' x) = f x :=
  rfl
#align quotient.lift_finsupp_mk Quotient.liftFinsupp_mk'

end Quotient

section

variable (s : Finset ℂ)

namespace Transcendental -- Conflict with Mathlib.NumberTheory.Dioph
abbrev Poly : ℚ[X] :=
  ∏ x in s, minpoly ℚ x
set_option linter.uppercaseLean3 false in
#align Poly Transcendental.Poly
end Transcendental

open Transcendental

abbrev K' : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ((Poly s).rootSet ℂ)
set_option linter.uppercaseLean3 false in
#align K' K'

abbrev K : Type _ :=
  (Poly s).SplittingField
set_option linter.uppercaseLean3 false in
#align K K

abbrev Gal : Type _ :=
  (Poly s).Gal
set_option linter.uppercaseLean3 false in
#align Gal Gal

abbrev Lift : K' s ≃ₐ[ℚ] K s :=
  IsSplittingField.algEquiv (K' s) (Poly s)
set_option linter.uppercaseLean3 false in
#align Lift Lift


theorem algebraMap_K_apply (x) : algebraMap (K s) ℂ x = ((Lift s).symm x : ℂ) :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebra_map_K_apply algebraMap_K_apply

theorem poly_ne_zero (hs : ∀ x ∈ s, IsIntegral ℚ x) : Poly s ≠ 0 :=
  prod_ne_zero_iff.mpr fun x hx => minpoly.ne_zero (hs x hx)
set_option linter.uppercaseLean3 false in
#align Poly_ne_zero poly_ne_zero

noncomputable def ratCoeff : Subalgebra ℚ (AddMonoidAlgebra (K s) (K s))
    where
  carrier := {x | ∀ i : K s, x i ∈ (⊥ : IntermediateField ℚ (K s))}
  mul_mem' {a b} ha hb i := by
    rw [AddMonoidAlgebra.mul_apply]
    refine' sum_mem fun c _ => sum_mem fun d _ => _
    dsimp only; split_ifs; exacts [mul_mem (ha c) (hb d), zero_mem _]
  add_mem' {a b} ha hb i := by rw [Finsupp.add_apply]; exact add_mem (ha i) (hb i)
  algebraMap_mem' r hr := by
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Finsupp.single_apply]
    split_ifs; exacts [IntermediateField.algebraMap_mem _ _, zero_mem _]
#align rat_coeff ratCoeff

--cache
instance : ZeroMemClass (IntermediateField ℚ (K s)) (K s) :=
  inferInstance
instance : AddCommMonoid (⊥ : IntermediateField ℚ (K s)) :=
  letI : AddCommGroup (⊥ : IntermediateField ℚ (K s)) := NonUnitalNonAssocRing.toAddCommGroup
  AddCommGroup.toAddCommMonoid
instance : Algebra ℚ (⊥ : IntermediateField ℚ (K s)) :=
  IntermediateField.algebra _

@[simps!]
def RatCoeffEquiv.aux : ratCoeff s ≃ₐ[ℚ] AddMonoidAlgebra (⊥ : IntermediateField ℚ (K s)) (K s)
    where
  toFun x :=
    { support := (x : AddMonoidAlgebra (K s) (K s)).support
      toFun := fun i => ⟨(x : AddMonoidAlgebra (K s) (K s)) i, x.2 i⟩
      mem_support_toFun := fun i => by
        rw [Finsupp.mem_support_iff]
        have : (0 : (⊥ : IntermediateField ℚ (K s))) = ⟨0, ZeroMemClass.zero_mem _⟩ := rfl
        simp_rw [this, Ne.def, Subtype.mk_eq_mk] }
  invFun x :=
    ⟨⟨x.support, fun i => x i, fun i => by
        simp_rw [Finsupp.mem_support_iff, Ne.def, ZeroMemClass.coe_eq_zero]⟩,
      fun i => SetLike.coe_mem _⟩
  left_inv x := by ext; rfl
  right_inv x := by
    refine Finsupp.ext fun a => ?_
    rfl
  map_mul' x y := by
    refine Finsupp.ext fun a => ?_
    ext
    change (x * y : AddMonoidAlgebra (K s) (K s)) a = _
    simp_rw [AddMonoidAlgebra.mul_apply, Finsupp.sum, AddSubmonoidClass.coe_finset_sum]
    refine' sum_congr rfl fun i _ => sum_congr rfl fun j _ => _
    split_ifs <;> rfl
  map_add' x y := by
    refine Finsupp.ext fun a => ?_
    ext
    change (x + y : AddMonoidAlgebra (K s) (K s)) a =
      (x : AddMonoidAlgebra (K s) (K s)) a + (y : AddMonoidAlgebra (K s) (K s)) a
    rw [Finsupp.add_apply]
  commutes' x := by
    refine Finsupp.ext fun a => ?_
    ext
    change
      ((algebraMap ℚ (ratCoeff s) x) : AddMonoidAlgebra (K s) (K s)) a =
        (Finsupp.single 0 (algebraMap ℚ (⊥ : IntermediateField ℚ (K s)) x)) a
    simp_rw [Algebra.algebraMap_eq_smul_one]
    change (x • Finsupp.single 0 (1 : K s)) a = _
    simp_rw [Finsupp.smul_single, Finsupp.single_apply]
    split_ifs <;> rfl
#align rat_coeff_equiv.aux RatCoeffEquiv.aux

@[simps! apply]
def ratCoeffEquiv : ratCoeff s ≃ₐ[ℚ] AddMonoidAlgebra ℚ (K s) :=
  (RatCoeffEquiv.aux s).trans
    (AddMonoidAlgebra.mapRangeAlgEquiv (IntermediateField.botEquiv ℚ (K s)))
#align rat_coeff_equiv ratCoeffEquiv

theorem ratCoeffEquiv_apply_apply (x : ratCoeff s) (i : K s) :
    ratCoeffEquiv s x i =
      (IntermediateField.botEquiv ℚ (K s)) ⟨(x : AddMonoidAlgebra (K s) (K s)) i, x.2 i⟩ := by
  rw [ratCoeffEquiv_apply]; rfl

#align rat_coeff_equiv_apply_apply ratCoeffEquiv_apply_apply

theorem support_ratCoeffEquiv (x : ratCoeff s) :
    (ratCoeffEquiv s x).support = (x : AddMonoidAlgebra (K s) (K s)).support := by
  simp [Finsupp.support_mapRange_of_injective _ _ (AlgEquiv.injective _)]
#align support_rat_coeff_equiv support_ratCoeffEquiv

section

variable (F : Type*) [Field F] [Algebra ℚ F]

noncomputable def mapDomainFixed : Subalgebra F (AddMonoidAlgebra F (K s)) where
  carrier := {x | ∀ f : Gal s, AddMonoidAlgebra.domCongrAut ℚ _ f.toAddEquiv x = x}
  mul_mem' {a b} ha hb f := by rw [map_mul, ha, hb]
  add_mem' {a b} ha hb f := by rw [map_add, ha, hb]
  algebraMap_mem' r f := by
    change Finsupp.equivMapDomain f.toEquiv (Finsupp.single _ _) = Finsupp.single _ _
    rw [Finsupp.equivMapDomain_single]
    change Finsupp.single (f 0) _ = _; rw [AlgEquiv.map_zero]
#align map_domain_fixed mapDomainFixed

instance : CoeFun (mapDomainFixed s F) fun _ => (K s) → F where
  coe f := f.1

theorem mem_mapDomainFixed_iff (x : AddMonoidAlgebra F (K s)) :
    x ∈ mapDomainFixed s F ↔ ∀ i j, i ∈ MulAction.orbit (Gal s) j → x i = x j := by
  simp_rw [MulAction.mem_orbit_iff]
  change (∀ f : Gal s, Finsupp.equivMapDomain (↑(AlgEquiv.toAddEquiv f)) x = x) ↔ _
  refine' ⟨fun h i j hij => _, fun h f => _⟩
  · obtain ⟨f, rfl⟩ := hij
    rw [AlgEquiv.smul_def, ← DFunLike.congr_fun (h f) (f j)]
    change x (f.symm (f j)) = _; rw [AlgEquiv.symm_apply_apply]
  · ext i; change x (f.symm i) = x i
    refine' (h i ((AlgEquiv.symm f) i) ⟨f, _⟩).symm
    rw [AlgEquiv.smul_def, AlgEquiv.apply_symm_apply]
#align mem_map_domain_fixed_iff mem_mapDomainFixed_iff

noncomputable def mapDomainFixedEquivSubtype :
    mapDomainFixed s F ≃
      { f : AddMonoidAlgebra F (K s) // MulAction.orbitRel (Gal s) (K s) ≤ Setoid.ker f }
    where
  toFun f := ⟨f, (mem_mapDomainFixed_iff s F f).mp f.2⟩
  invFun f := ⟨f, (mem_mapDomainFixed_iff s F f).mpr f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align map_domain_fixed_equiv_subtype mapDomainFixedEquivSubtype

end

section toConjEquiv

variable (F : Type*) [Field F] [Algebra ℚ F]

open GalConjClasses

def toConjEquiv : mapDomainFixed s F ≃ (GalConjClasses ℚ (K s) →₀ F) := by
  refine' (mapDomainFixedEquivSubtype s F).trans _
  let f'
      (f : { f : AddMonoidAlgebra F (K s) // MulAction.orbitRel (Gal s) (K s) ≤ Setoid.ker ↑f }) :=
    @Quotient.liftFinsupp _ _ (IsGalConj.setoid _ _) _ (f : AddMonoidAlgebra F (K s)) f.2
  refine'
    { toFun := f'
      invFun := fun f => ⟨_, _⟩
      left_inv := _
      right_inv := _ }
  · refine' ⟨f.support.biUnion fun i => i.orbit.toFinset, fun x => f (GalConjClasses.mk ℚ x),
      fun i => _⟩
    simp_rw [mem_biUnion, Set.mem_toFinset, mem_orbit, Finsupp.mem_support_iff, exists_eq_right']
  · change ∀ i j, i ∈ MulAction.orbit (Gal s) j → f (Quotient.mk'' i) = f (Quotient.mk'' j)
    exact fun i j h => congr_arg f (Quotient.sound' h)
  · exact fun _ => Subtype.eq <| Finsupp.ext fun x => rfl
  · refine' fun f => Finsupp.ext fun x => Quotient.inductionOn' x fun i => rfl
#align to_conj_equiv toConjEquiv

@[simp 1001] -- LHS simplifies
theorem toConjEquiv_apply_apply_mk (f : mapDomainFixed s F) (i : K s) :
    toConjEquiv s F f (mk ℚ i) = f i :=
  rfl
#align to_conj_equiv_apply_apply_mk toConjEquiv_apply_apply_mk

@[simp]
theorem toConjEquiv_symm_apply_apply (f : GalConjClasses ℚ (K s) →₀ F) (i : K s) :
    (toConjEquiv s F).symm f i = f (mk ℚ i) :=
  rfl
#align to_conj_equiv_symm_apply_apply toConjEquiv_symm_apply_apply

@[simp]
theorem toConjEquiv_apply_apply (f : mapDomainFixed s F) (i : GalConjClasses ℚ (K s)) :
    toConjEquiv s F f i = f i.out := by rw [← i.out_eq, toConjEquiv_apply_apply_mk, i.out_eq]
#align to_conj_equiv_apply_apply toConjEquiv_apply_apply

@[simp 1001] -- LHS simplifies
theorem toConjEquiv_apply_zero_eq (f : mapDomainFixed s F) : toConjEquiv s F f 0 = f 0 := by
  rw [toConjEquiv_apply_apply, GalConjClasses.zero_out]
#align to_conj_equiv_apply_zero_eq toConjEquiv_apply_zero_eq

@[simp 1001] -- LHS simplifies
theorem toConjEquiv_symm_apply_zero_eq (f : GalConjClasses ℚ (K s) →₀ F) :
    (toConjEquiv s F).symm f 0 = f 0 := by rw [toConjEquiv_symm_apply_apply]; rfl
#align to_conj_equiv_symm_apply_zero_eq toConjEquiv_symm_apply_zero_eq

instance : AddCommMonoid (mapDomainFixed s F) :=
  letI : AddCommGroup (mapDomainFixed s F) := NonUnitalNonAssocRing.toAddCommGroup
  AddCommGroup.toAddCommMonoid

@[simps]
def toConjLinearEquiv : mapDomainFixed s F ≃ₗ[F] GalConjClasses ℚ (K s) →₀ F :=
  { toConjEquiv s F with
    toFun := toConjEquiv s F
    invFun := (toConjEquiv s F).symm
    map_add' := fun x y => by
      ext i; simp_rw [Finsupp.coe_add, Pi.add_apply, toConjEquiv_apply_apply]
      rfl
    map_smul' := fun r x => by
      ext i; simp_rw [Finsupp.coe_smul, toConjEquiv_apply_apply]
      simp only [SetLike.val_smul, RingHom.id_apply]
      rw [Finsupp.coe_smul, Pi.smul_apply]
      rw [Pi.smul_apply]
      rw [toConjEquiv_apply_apply] }
#align to_conj_linear_equiv toConjLinearEquiv

namespace Finsupp.GalConjClasses

instance : One (GalConjClasses ℚ (K s) →₀ F) where
  one := toConjLinearEquiv s F 1

theorem one_def : (1 : GalConjClasses ℚ (K s) →₀ F) = toConjLinearEquiv s F 1 :=
  rfl
#align finsupp.gal_conj_classes.one_def Finsupp.GalConjClasses.one_def

instance : Mul (GalConjClasses ℚ (K s) →₀ F) where
  mul x y :=
    toConjLinearEquiv s F <| (toConjLinearEquiv s F).symm x * (toConjLinearEquiv s F).symm y

theorem mul_def (x y : GalConjClasses ℚ (K s) →₀ F) :
    x * y =
      toConjLinearEquiv s F ((toConjLinearEquiv s F).symm x * (toConjLinearEquiv s F).symm y) :=
  rfl
#align finsupp.gal_conj_classes.mul_def Finsupp.GalConjClasses.mul_def

instance : CommSemigroup (GalConjClasses ℚ (K s) →₀ F) where
  mul_assoc a b c := by
    simp_rw [mul_def, LinearEquiv.symm_apply_apply, mul_assoc]
  mul_comm a b := by
    simp_rw [mul_def]
    exact congr_arg _ (mul_comm _ _)

instance : MulZeroClass (GalConjClasses ℚ (K s) →₀ F) where
  zero_mul a :=
    graph_eq_empty.mp rfl
  mul_zero a := by
    rw [mul_comm]
    exact graph_eq_empty.mp rfl

instance : CommRing (GalConjClasses ℚ (K s) →₀ F) :=
  { (inferInstance : AddCommGroup (GalConjClasses ℚ (K s) →₀ F)),
    (inferInstance : CommSemigroup (GalConjClasses ℚ (K s) →₀ F)),
    (inferInstance : MulZeroClass (GalConjClasses ℚ (K s) →₀ F)) with
    one_mul := fun a => by
      simp_rw [one_def, mul_def, LinearEquiv.symm_apply_apply, one_mul,
        LinearEquiv.apply_symm_apply]
    mul_one := fun a => by
      simp_rw [one_def, mul_def, LinearEquiv.symm_apply_apply, mul_one,
        LinearEquiv.apply_symm_apply]
    left_distrib := fun a b c => by
      simp only [mul_def, ← map_add, ← mul_add]
    right_distrib := fun a b c => by
      simp only [mul_def, ← map_add, ← add_mul] }

instance : Algebra F (GalConjClasses ℚ (K s) →₀ F) :=
  Algebra.ofModule'
    (fun r x => by
      rw [one_def, mul_def, SMulHomClass.map_smul, LinearEquiv.symm_apply_apply, smul_one_mul, ←
        SMulHomClass.map_smul, LinearEquiv.apply_symm_apply])
    fun r x => by
    rw [one_def, mul_def, SMulHomClass.map_smul, LinearEquiv.symm_apply_apply, mul_smul_one, ←
      SMulHomClass.map_smul, LinearEquiv.apply_symm_apply]

theorem one_eq_single : (1 : GalConjClasses ℚ (K s) →₀ F) = Finsupp.single 0 1 := by
  change toConjEquiv s F 1 = _
  ext i; rw [toConjEquiv_apply_apply]
  change (1 : AddMonoidAlgebra F (K s)) i.out = Finsupp.single 0 1 i
  simp_rw [AddMonoidAlgebra.one_def, Finsupp.single_apply]
  change (ite (0 = i.out) 1 0 : F) = ite (0 = i) 1 0
  simp_rw [@eq_comm _ _ i.out, @eq_comm _ _ i, GalConjClasses.out_eq_zero_iff]
#align finsupp.gal_conj_classes.one_eq_single Finsupp.GalConjClasses.one_eq_single

theorem algebraMap_eq_single (x : F) :
    algebraMap F (GalConjClasses ℚ (K s) →₀ F) x = Finsupp.single 0 x := by
  change x • (1 : GalConjClasses ℚ (K s) →₀ F) = Finsupp.single 0 x
  rw [one_eq_single, Finsupp.smul_single, smul_eq_mul, mul_one]
#align finsupp.gal_conj_classes.algebra_map_eq_single Finsupp.GalConjClasses.algebraMap_eq_single

end Finsupp.GalConjClasses

@[simps]
def toConjAlgEquiv : mapDomainFixed s F ≃ₐ[F] GalConjClasses ℚ (K s) →₀ F :=
  { toConjLinearEquiv s F with
    toFun := toConjLinearEquiv s F
    invFun := (toConjLinearEquiv s F).symm
    map_mul' := fun x y => by simp_rw [Finsupp.GalConjClasses.mul_def, LinearEquiv.symm_apply_apply]
    commutes' := fun r => by
      simp_rw [Finsupp.GalConjClasses.algebraMap_eq_single]
      change toConjEquiv s F (algebraMap F (mapDomainFixed s F) r) = _
      ext i; rw [toConjEquiv_apply_apply]
      change Finsupp.single 0 r i.out = Finsupp.single 0 r i
      simp_rw [Finsupp.single_apply]
      change ite (0 = i.out) r 0 = ite (0 = i) r 0
      simp_rw [@eq_comm _ _ i.out, @eq_comm _ _ i, out_eq_zero_iff] }
#align to_conj_alg_equiv toConjAlgEquiv

theorem ToConjEquivSymmSingle.aux (x : GalConjClasses ℚ (K s)) (a : F) :
    (Finsupp.indicator x.orbit.toFinset fun _ _ => a) ∈ mapDomainFixed s F := by
  rw [mem_mapDomainFixed_iff]
  rintro i j h
  simp_rw [Finsupp.indicator_apply, Set.mem_toFinset]; dsimp; congr 1
  simp_rw [mem_orbit, eq_iff_iff]
  apply Eq.congr_left
  rwa [GalConjClasses.eq]
#align to_conj_equiv_symm_single.aux ToConjEquivSymmSingle.aux

theorem toConjEquiv_symm_single (x : GalConjClasses ℚ (K s)) (a : F) :
    (toConjEquiv s F).symm (Finsupp.single x a) =
      ⟨Finsupp.indicator x.orbit.toFinset fun _ _ => a, ToConjEquivSymmSingle.aux s F x a⟩ := by
  rw [Equiv.symm_apply_eq]
  ext i; rw [toConjEquiv_apply_apply]
  change Finsupp.single x a i = Finsupp.indicator x.orbit.toFinset (fun _ _ => a) i.out
  rw [Finsupp.single_apply, Finsupp.indicator_apply]; dsimp; congr 1
  rw [Set.mem_toFinset, mem_orbit, out_eq, @eq_comm _ i]
#align to_conj_equiv_symm_single toConjEquiv_symm_single

theorem single_prod_apply_zero_ne_zero_iff (x : GalConjClasses ℚ (K s)) {a : F} (ha : a ≠ 0)
    (y : GalConjClasses ℚ (K s)) {b : F} (hb : b ≠ 0) :
    (Finsupp.single x a * Finsupp.single y b) 0 ≠ 0 ↔ x = -y := by
  simp_rw [Finsupp.GalConjClasses.mul_def, toConjLinearEquiv_apply, toConjLinearEquiv_symm_apply,
    toConjEquiv_apply_zero_eq]
  simp_rw [toConjEquiv_symm_single, MulMemClass.mk_mul_mk]
  haveI := Nat.noZeroSMulDivisors ℚ F
  simp_rw [Finsupp.indicator_eq_sum_single, sum_mul, mul_sum,
    AddMonoidAlgebra.single_mul_single]
  -- Porting note: next four lines were `simp_rw [Finsupp.coe_finset_sum, sum_apply]`
  rw [Finsupp.coe_finset_sum, sum_apply]
  conv =>
    enter [1, 1, 2, c]
    rw [Finsupp.coe_finset_sum, sum_apply]
  simp_rw [Finsupp.single_apply, ←
    sum_product', sum_ite, sum_const_zero, add_zero, sum_const, smul_ne_zero_iff, mul_ne_zero_iff,
    iff_true_intro ha, iff_true_intro hb, and_true_iff, Ne.def, card_eq_zero, filter_eq_empty_iff]
  push_neg
  simp_rw [Prod.exists, mem_product, Set.mem_toFinset]
  exact GalConjClasses.exist_mem_orbit_add_eq_zero x y
#align single_prod_apply_zero_ne_zero_iff single_prod_apply_zero_ne_zero_iff

theorem single_prod_apply_zero_eq_zero_iff (x : GalConjClasses ℚ (K s)) {a : F} (ha : a ≠ 0)
    (y : GalConjClasses ℚ (K s)) {b : F} (hb : b ≠ 0) :
    (Finsupp.single x a * Finsupp.single y b) 0 = 0 ↔ x ≠ -y :=
  (single_prod_apply_zero_ne_zero_iff s F x ha y hb).not_right
#align single_prod_apply_zero_eq_zero_iff single_prod_apply_zero_eq_zero_iff

end toConjEquiv

open Complex

section Eval

set_option linter.uppercaseLean3 false

variable (F : Type*) [Field F] [Algebra F ℂ]

def Eval : AddMonoidAlgebra F (K s) →ₐ[F] ℂ :=
  AddMonoidAlgebra.lift F (K s) ℂ
    (expMonoidHom.comp (AddMonoidHom.toMultiplicative (algebraMap (K s) ℂ).toAddMonoidHom))
#align Eval Eval

theorem Eval_apply (x : AddMonoidAlgebra F (K s)) :
    Eval s F x = x.sum fun a c => c • exp (algebraMap (K s) ℂ a) := by
  rw [Eval, AddMonoidAlgebra.lift_apply]; rfl
#align Eval_apply Eval_apply

theorem Eval_ratCoeff (x : ratCoeff s) : Eval s (K s) x = Eval s ℚ (ratCoeffEquiv s x) := by
  simp_rw [Eval_apply, Finsupp.sum, support_ratCoeffEquiv, ratCoeffEquiv_apply_apply]
  refine' sum_congr rfl fun i _ => _
  simp_rw [Algebra.smul_def, IsScalarTower.algebraMap_eq ℚ (K s) ℂ, RingHom.comp_apply]
  congr 2
  simp_rw [IsScalarTower.algebraMap_apply ℚ (⊥ : IntermediateField ℚ (K s)) (K s),
    ← IntermediateField.botEquiv_symm]
  rw [AlgEquiv.symm_apply_apply]
  rfl
#align Eval_rat_coeff Eval_ratCoeff

theorem Eval_toConjAlgEquiv_symm (x : GalConjClasses ℚ (K s) →₀ ℚ) :
    Eval s ℚ ((toConjAlgEquiv s ℚ).symm x) =
      ∑ c : GalConjClasses ℚ (K s) in x.support,
        x c • ∑ i : K s in c.orbit.toFinset, exp (algebraMap (K s) ℂ i) := by
  conv_lhs => rw [← x.sum_single, Finsupp.sum, map_sum]
  simp_rw [toConjAlgEquiv_symm_apply, toConjLinearEquiv_symm_apply]
  have :
    ∀ (s' : Finset (K s)) (b : ℚ),
      ((Finsupp.indicator s' fun _ _ => b).sum fun a c => c • exp (algebraMap (K s) ℂ a)) =
        ∑ i in s', b • exp (algebraMap (K s) ℂ i) :=
    fun s' b => Finsupp.sum_indicator_index _ fun i _ => by rw [zero_smul]
  simp_rw [toConjEquiv_symm_single, AddSubmonoidClass.coe_finset_sum, map_sum,
    Eval_apply, this, smul_sum]
#align Eval_to_conj_alg_equiv_symm Eval_toConjAlgEquiv_symm

end Eval

instance instIsDomain1 : NoZeroDivisors (AddMonoidAlgebra (K s) (K s)) := inferInstance
instance instIsDomain2 : IsDomain (AddMonoidAlgebra ℚ (K s)) := IsDomain.mk
instance instIsDomain3 : IsDomain (GalConjClasses ℚ (K s) →₀ ℚ) :=
  MulEquiv.isDomain (mapDomainFixed s ℚ) (toConjAlgEquiv s ℚ).symm
instance : AddZeroClass { x // x ∈ mapDomainFixed s ℚ } := inferInstance

theorem linear_independent_exp_aux2 (s : Finset ℂ) (x : AddMonoidAlgebra ℚ (K s)) (x0 : x ≠ 0)
    (x_ker : x ∈ RingHom.ker (Eval s ℚ)) :
    ∃ (w : ℚ) (_w0 : w ≠ 0) (q : Finset (GalConjClasses ℚ (K s))) (_hq :
      (0 : GalConjClasses ℚ (K s)) ∉ q) (w' : GalConjClasses ℚ (K s) → ℚ),
      (w + ∑ c in q, w' c • ∑ x in c.orbit.toFinset, exp (algebraMap (K s) ℂ x) : ℂ) = 0 := by
  let V := ∏ f : Gal s, AddMonoidAlgebra.domCongrAut ℚ _ f.toAddEquiv x
  have hV : V ∈ mapDomainFixed s ℚ
  · intro f; dsimp only
    rw [map_prod]; simp_rw [← AlgEquiv.trans_apply, ← AlgEquiv.aut_mul, ← map_mul]
    exact
      (Group.mulLeft_bijective f).prod_comp fun g =>
        AddMonoidAlgebra.domCongrAut ℚ _ g.toAddEquiv x
  have V0 : V ≠ 0
  · dsimp only; rw [prod_ne_zero_iff]; intro f _hf
    rwa [AddEquivClass.map_ne_zero_iff]
  have V_ker : V ∈ RingHom.ker (Eval s ℚ)
  · dsimp only
    rw [← mul_prod_erase (univ : Finset (Gal s)) _ (mem_univ 1)]
    erw [map_one]
    rw [AlgEquiv.one_apply]
    exact Ideal.mul_mem_right _ _ x_ker
  set V' := toConjAlgEquiv s ℚ ⟨V, hV⟩ with V'_def
  have V'0 : V' ≠ 0
  · dsimp only; rw [AddEquivClass.map_ne_zero_iff]
    exact fun h => absurd (Subtype.mk.inj h) V0
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr V'0
  set V'' := V' * Finsupp.single (-i) (1 : ℚ) with V''_def
  have V''0 : V'' ≠ 0
  · have : NoZeroDivisors (GalConjClasses ℚ (K s) →₀ ℚ) := IsDomain.to_noZeroDivisors _
    rw [V''_def]
    refine' mul_ne_zero V'0 fun h => _
    rw [Finsupp.single_eq_zero] at h
    exact one_ne_zero h
  have hV'' : V'' 0 ≠ 0
  · rw [V''_def, ← V'.sum_single, Finsupp.sum, ← add_sum_erase _ _ hi, add_mul, sum_mul,
      Finsupp.add_apply]
    convert_to
      ((Finsupp.single i (V' i) * Finsupp.single (-i) 1 : GalConjClasses ℚ (K s) →₀ ℚ) 0 + 0) ≠ 0
    · congr 1
      rw [Finsupp.finset_sum_apply]
      refine' sum_eq_zero fun j hj => _
      rw [mem_erase, Finsupp.mem_support_iff] at hj
      rw [single_prod_apply_zero_eq_zero_iff _ _ _ hj.2]
      · rw [neg_neg]; exact hj.1
      · exact one_ne_zero
    rw [add_zero, single_prod_apply_zero_ne_zero_iff]
    · rw [neg_neg]
    · rwa [Finsupp.mem_support_iff] at hi
    · exact one_ne_zero
  have zero_mem : (0 : GalConjClasses ℚ (K s)) ∈ V''.support := by rwa [Finsupp.mem_support_iff]
  have Eval_V'' : Eval s ℚ ((toConjAlgEquiv s ℚ).symm V'') = 0
  · dsimp only
    rw [map_mul, Subalgebra.coe_mul, map_mul, AlgEquiv.symm_apply_apply, Subtype.coe_mk]
    rw [RingHom.mem_ker] at V_ker
    rw [V_ker, MulZeroClass.zero_mul]
  use V'' 0, hV'', V''.support.erase 0, not_mem_erase _ _, V''
  rw [← Eval_V'', Eval_toConjAlgEquiv_symm, ← add_sum_erase _ _ zero_mem]
  congr 1
  simp_rw [GalConjClasses.orbit_zero, Set.toFinset_singleton, sum_singleton, map_zero, exp_zero,
    Rat.smul_one_eq_coe]
#align linear_independent_exp_aux2 linear_independent_exp_aux2

instance : AddZeroClass { x // x ∈ ratCoeff s } := inferInstance

theorem linear_independent_exp_aux1 (s : Finset ℂ) (x : AddMonoidAlgebra (K s) (K s)) (x0 : x ≠ 0)
    (x_ker : x ∈ RingHom.ker (Eval s (K s))) :
    ∃ (w : ℚ) (_w0 : w ≠ 0) (q : Finset (GalConjClasses ℚ (K s))) (_hq :
      (0 : GalConjClasses ℚ (K s)) ∉ q) (w' : GalConjClasses ℚ (K s) → ℚ),
      (w + ∑ c in q, w' c • ∑ x in c.orbit.toFinset, exp (algebraMap (K s) ℂ x) : ℂ) = 0 := by
  let U := ∏ f : Gal s, AddMonoidAlgebra.mapRangeAlgAut f x
  have hU : ∀ f : Gal s, AddMonoidAlgebra.mapRangeAlgAut f U = U
  · intro f; dsimp only
    simp_rw [map_prod, ← AlgEquiv.trans_apply, ← AlgEquiv.aut_mul, ← map_mul]
    exact (Group.mulLeft_bijective f).prod_comp fun g => AddMonoidAlgebra.mapRangeAlgAut g x
  have U0 : U ≠ 0
  · dsimp only; rw [prod_ne_zero_iff]; intro f _hf
    rwa [AddEquivClass.map_ne_zero_iff]
  have U_ker : U ∈ RingHom.ker (Eval s (K s))
  · suffices
      (fun f : Gal s => AddMonoidAlgebra.mapRangeAlgAut f x) 1 *
          ∏ f : Gal s in univ.erase 1, AddMonoidAlgebra.mapRangeAlgAut f x ∈
            RingHom.ker (Eval s (K s)) by
      convert this
      exact (mul_prod_erase (univ : Finset (Gal s)) _ (mem_univ _)).symm
    dsimp only
    rw [map_one]; exact Ideal.mul_mem_right _ _ x_ker
  have U_mem : ∀ i : K s, U i ∈ IntermediateField.fixedField (⊤ : Subgroup (K s ≃ₐ[ℚ] K s))
  · intro i; dsimp [IntermediateField.fixedField, FixedPoints.intermediateField]
    rintro ⟨f, hf⟩; rw [Subgroup.smul_def, Subgroup.coe_mk]
    replace hU : AddMonoidAlgebra.mapRangeAlgAut f U i = U i; · rw [hU f]
    rwa [AddMonoidAlgebra.mapRangeAlgAut_apply, AddMonoidAlgebra.mapRangeAlgEquiv_apply,
      Finsupp.mapRange_apply] at hU
  replace U_mem : U ∈ ratCoeff s
  · intro i; specialize U_mem i
    have := ((@IsGalois.tfae ℚ _ (K s) _ _ _).out 0 1).mp (by infer_instance)
    rwa [this] at U_mem
  let U' := ratCoeffEquiv s ⟨U, U_mem⟩
  have U'0 : U' ≠ 0
  · dsimp only
    rw [AddEquivClass.map_ne_zero_iff, ZeroMemClass.zero_def]
    exact fun h => absurd (Subtype.mk.inj h) U0
  have U'_ker : U' ∈ RingHom.ker (Eval s ℚ)
  · dsimp only
    rw [RingHom.mem_ker, ← Eval_ratCoeff]
    rwa [RingHom.mem_ker] at U_ker
  exact linear_independent_exp_aux2 s U' U'0 U'_ker
#align linear_independent_exp_aux1 linear_independent_exp_aux1

end

open Complex

variable {ι : Type*} [Fintype ι]

abbrev range (u : ι → ℂ) (v : ι → ℂ) : Finset ℂ :=
  univ.image u ∪ univ.image v
set_option linter.uppercaseLean3 false in
#align Range range

theorem linear_independent_exp_aux_rat (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i)) (v0 : v ≠ 0)
    (h : ∑ i, v i * exp (u i) = 0) :
    ∃ (w : ℚ) (_ : w ≠ 0) (q : Finset (GalConjClasses ℚ (K (range u v)))) (_ :
      (0 : GalConjClasses _ _) ∉ q) (w' : GalConjClasses ℚ (K (range u v)) → ℚ),
      (w + ∑ c in q, w' c • ∑ x in c.orbit.toFinset, exp (algebraMap (K (range u v)) ℂ x) : ℂ) =
        0 := by
  let s := range u v
  have hs : ∀ x ∈ s, IsIntegral ℚ x
  · intro x hx
    cases' mem_union.mp hx with hxu hxv
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hxu
      exact hu i
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hxv
      exact hv i
  have u_mem : ∀ i, u i ∈ K' s
  · intro i
    apply IntermediateField.subset_adjoin
    rw [mem_rootSet, map_prod, prod_eq_zero_iff]
    exact
      ⟨poly_ne_zero s hs, u i, mem_union_left _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩),
        minpoly.aeval _ _⟩
  have v_mem : ∀ i, v i ∈ K' s
  · intro i
    apply IntermediateField.subset_adjoin
    rw [mem_rootSet, map_prod, prod_eq_zero_iff]
    exact
      ⟨poly_ne_zero s hs, v i, mem_union_right _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩),
        minpoly.aeval _ _⟩
  let u' : ∀ _, K s := fun i : ι => Lift s ⟨u i, u_mem i⟩
  let v' : ∀ _, K s := fun i : ι => Lift s ⟨v i, v_mem i⟩
  have u'_inj : Function.Injective u' := fun i j hij =>
    u_inj (Subtype.mk.inj ((Lift s).injective hij))
  replace h : ∑ i, algebraMap (K s) ℂ (v' i) * exp (algebraMap (K s) ℂ (u' i)) = 0
  · simp_rw [algebraMap_K_apply, AlgEquiv.symm_apply_apply, ← h]
  let f : AddMonoidAlgebra (K s) (K s) :=
    Finsupp.onFinset (image u' univ)
      (fun x =>
        if hx : x ∈ image u' univ then
          v' (u'_inj.invOfMemRange ⟨x, mem_image_univ_iff_mem_range.mp hx⟩)
        else 0)
      fun x => by contrapose!; intro hx; rw [dif_neg hx]
  replace hf : Eval s (K s) f = 0
  · rw [Eval_apply, ← h, Finsupp.onFinset_sum _ fun a => _]; swap; · intro _; rw [zero_smul]
    rw [sum_image, sum_congr rfl]; swap; · exact fun i _ j _ hij => u'_inj hij
    intro x _
    rw [dif_pos, u'_inj.right_inv_of_invOfMemRange]; · rfl
    exact mem_image_of_mem _ (mem_univ _)
  have f0 : f ≠ 0
  · rw [Ne.def, Function.funext_iff] at v0; push_neg at v0
    cases' v0 with i hi
    rw [Pi.zero_apply] at hi
    have h : f (u' i) ≠ 0
    · rwa [Finsupp.onFinset_apply, dif_pos, u'_inj.right_inv_of_invOfMemRange, Ne.def,
        AddEquivClass.map_eq_zero_iff, ← ZeroMemClass.coe_eq_zero]
      exact mem_image_of_mem _ (mem_univ _)
    intro f0
    rw [f0, Finsupp.zero_apply] at h
    exact absurd rfl h
  rw [← AlgHom.coe_toRingHom, ← RingHom.mem_ker] at hf
  exact linear_independent_exp_aux1 s f f0 hf
#align linear_independent_exp_aux_rat linear_independent_exp_aux_rat

theorem linear_independent_exp_aux'' (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i)) (v0 : v ≠ 0)
    (h : ∑ i, v i * exp (u i) = 0) :
    ∃ (w : ℤ) (_w0 : w ≠ 0) (q : Finset (GalConjClasses ℚ (K (range u v)))) (_hq :
      (0 : GalConjClasses _ _) ∉ q) (w' : GalConjClasses ℚ (K (range u v)) → ℤ),
      (w + ∑ c in q, w' c • ∑ x in c.orbit.toFinset, exp (algebraMap (K (range u v)) ℂ x) : ℂ) =
        0 := by
  obtain ⟨w, w0, q, hq, w', h⟩ := linear_independent_exp_aux_rat u hu u_inj v hv v0 h
  let N := w.den * ∏ c in q, (w' c).den
  have wN0 : (w * N).num ≠ 0
  · refine' Rat.num_ne_zero_of_ne_zero (mul_ne_zero w0 _); dsimp only
    rw [Nat.cast_ne_zero, mul_ne_zero_iff, prod_ne_zero_iff]
    exact ⟨Rat.den_nz _, fun c _hc => Rat.den_nz _⟩
  use (w * N).num, wN0, q, hq, fun c => (w' c * N).num
  have hw : ((w * N).num : ℚ) = w * N
  · dsimp only
    rw [← Rat.den_eq_one_iff, Nat.cast_mul, ← mul_assoc, Rat.mul_den_eq_num]
    norm_cast
  have hw' : ∀ c ∈ q, ((w' c * N).num : ℚ) = w' c * N
  · intro c hc; dsimp only
    rw [← Rat.den_eq_one_iff, ← mul_prod_erase _ _ hc, mul_left_comm, Nat.cast_mul, ← mul_assoc,
      Rat.mul_den_eq_num]
    norm_cast
  convert_to
    (w * N + ∑ c in q, (w' c * N) • ∑ x in c.orbit.toFinset, exp (algebraMap (K (range u v)) ℂ x))
      = 0
  · congr 1
    · norm_cast
    · refine' sum_congr rfl fun i hi => _
      rw [← hw' i hi, Rat.coe_int_num, ← zsmul_eq_smul_cast]
  · simp_rw [mul_comm _ (N : ℂ), mul_comm _ (N : ℚ), ← smul_smul, ← smul_sum, ← nsmul_eq_mul,
      ← nsmul_eq_smul_cast, ← smul_add, h, nsmul_zero]
#align linear_independent_exp_aux'' linear_independent_exp_aux''

theorem linear_independent_exp_aux' (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i)) (v0 : v ≠ 0)
    (h : ∑ i, v i * exp (u i) = 0) :
    ∃ (w : ℤ) (w0 : w ≠ 0) (n : ℕ) (p : Fin n → ℚ[X]) (_p0 : ∀ j, (p j).eval 0 ≠ 0)
      (w' : Fin n → ℤ),
        (w + ∑ j, w' j • (((p j).aroots ℂ).map fun x => exp x).sum : ℂ) = 0 := by
  obtain ⟨w, w0, q, hq, w', h⟩ := linear_independent_exp_aux'' u hu u_inj v hv v0 h
  let c : Fin q.card → GalConjClasses ℚ (K (range u v)) := fun j => q.equivFin.symm j
  have hc : ∀ j, c j ∈ q := fun j => Finset.coe_mem _
  refine' ⟨w, w0, q.card, fun j => (c j).minpoly, _, fun j => w' (c j), _⟩
  · intro j; specialize hc j
    suffices ((c j).minpoly.map (algebraMap ℚ (K (range u v)))).eval
        (algebraMap ℚ (K (range u v)) 0) ≠ 0 by
      rwa [eval_map, ← aeval_def, aeval_algebraMap_apply, _root_.map_ne_zero] at this
    rw [RingHom.map_zero, GalConjClasses.minpoly.map_eq_prod, eval_prod, prod_ne_zero_iff]
    intro a ha
    rw [eval_sub, eval_X, eval_C, sub_ne_zero]
    rintro rfl
    rw [Set.mem_toFinset, GalConjClasses.mem_orbit, GalConjClasses.mk_zero] at ha
    rw [← ha] at hc; exact hq hc
  rw [← h, add_right_inj]
  change ∑ j, ((fun c => w' c • ((c.minpoly.aroots ℂ).map exp).sum) ·) (q.equivFin.symm j) = _
  -- Porting note: were `rw [Equiv.sum_comp q.equivFin.symm, sum_coe_sort]`
  rw [Equiv.sum_comp q.equivFin.symm
    ((fun c ↦ w' c • ((c.minpoly.aroots ℂ).map exp).sum) ·),
    sum_coe_sort _ (fun c ↦ w' c • ((c.minpoly.aroots ℂ).map exp).sum)]
  refine' sum_congr rfl fun c _hc => _
  have : c.minpoly.aroots ℂ = (c.minpoly.aroots (K (range u v))).map (algebraMap (K (range u v)) ℂ)
  · change roots _ = _
    rw [← roots_map, Polynomial.map_map, IsScalarTower.algebraMap_eq ℚ (K (range u v)) ℂ]
    rw [splits_map_iff, RingHom.id_comp]; exact c.splits_minpoly
  rw [this, c.aroots_minpoly_eq_orbit_val, Multiset.map_map, sum_eq_multiset_sum]; rfl
#align linear_independent_exp_aux' linear_independent_exp_aux'

theorem linear_independent_exp_aux (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i)) (v0 : v ≠ 0)
    (h : ∑ i, v i * exp (u i) = 0) :
    ∃ (w : ℤ) (w0 : w ≠ 0) (n : ℕ) (p : Fin n → ℤ[X]) (_p0 : ∀ j, (p j).eval 0 ≠ 0)
      (w' : Fin n → ℤ),
        (w + ∑ j, w' j • (((p j).aroots ℂ).map fun x => exp x).sum : ℂ) = 0 := by
  obtain ⟨w, w0, n, p, hp, w', h⟩ := linear_independent_exp_aux' u hu u_inj v hv v0 h
  choose b hb using
    fun j ↦ IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) (p j)
  refine'
    ⟨w, w0, n, fun i => IsLocalization.integerNormalization (nonZeroDivisors ℤ) (p i), _, w', _⟩
  · intro j
    suffices
      aeval (algebraMap ℤ ℚ 0) (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (p j)) ≠ 0
      by rwa [aeval_algebraMap_apply, map_ne_zero_iff _ (algebraMap ℤ ℚ).injective_int] at this
    rw [map_zero, aeval_def, eval₂_eq_eval_map, hb, eval_smul, smul_ne_zero_iff]
    exact ⟨nonZeroDivisors.coe_ne_zero _, hp j⟩
  rw [← h, add_right_inj]
  refine' sum_congr rfl fun j _hj => congr_arg _ (congr_arg _ (Multiset.map_congr _ fun _ _ => rfl))
  change roots _ = roots _
  rw [IsScalarTower.algebraMap_eq ℤ ℚ ℂ, ← Polynomial.map_map, hb,
    zsmul_eq_mul, ← C_eq_int_cast, Polynomial.map_mul, map_C, roots_C_mul]
  rw [map_ne_zero_iff _ (algebraMap ℚ ℂ).injective, Int.cast_ne_zero]
  exact nonZeroDivisors.coe_ne_zero _
#align linear_independent_exp_aux linear_independent_exp_aux
