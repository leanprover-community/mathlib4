/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/

import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
TODO
-/

noncomputable section

namespace AddMonoidAlgebra

@[simps]
def ringHomCongrLeft {R S G : Type _} [Semiring R] [Semiring S] [AddZeroClass G] (f : R →+* S) :
    AddMonoidAlgebra R G →+* AddMonoidAlgebra S G :=
  { Finsupp.mapRange.addMonoidHom f.toAddMonoidHom with
    toFun := (Finsupp.mapRange f f.map_zero : AddMonoidAlgebra R G → AddMonoidAlgebra S G)
    map_one' := by
      classical
      refine Finsupp.ext fun a => ?_
      simp [one_def]
    map_mul' := fun x y => by
      classical
      -- Porting note: was `ext`
      refine Finsupp.ext fun a => ?_
      simp_rw [mul_apply, mul_def, Finsupp.mapRange_apply]
      rw [Finsupp.sum_apply, map_finsupp_sum f]
      rw [Finsupp.sum_mapRange_index];
      -- Porting note: was `congrm`
      apply congr_arg _ <| funext₂ fun g1 r1 => ?_
      rw [Finsupp.sum_mapRange_index];
      rw [Finsupp.sum_apply, map_finsupp_sum f]
      -- Porting note: was `congrm`
      apply congr_arg _ <| funext₂ fun g2 r2 => ?_
      · rw [Finsupp.single_apply]
        split_ifs with h <;> simp only [h, if_false, if_true, map_mul, map_zero]
      all_goals
        intro; simp only [MulZeroClass.mul_zero, MulZeroClass.zero_mul];
        simp only [ite_self, Finsupp.sum_zero] }

-- TODO: times out with `AddZeroClass G`
@[simps!]
def ringEquivCongrLeft {R S G : Type _} [Semiring R] [Semiring S] [AddMonoid G] (f : R ≃+* S) :
    AddMonoidAlgebra R G ≃+* AddMonoidAlgebra S G :=
  .ofHomInv (ringHomCongrLeft f) (ringHomCongrLeft f.symm) (by ext <;> simp) (by ext <;> simp)

@[simps]
def algHomCongrLeft {k R S G : Type _} [CommSemiring k] [Semiring R] [Algebra k R] [Semiring S]
    [Algebra k S] [AddMonoid G] (f : R →ₐ[k] S) : AddMonoidAlgebra R G →ₐ[k] AddMonoidAlgebra S G :=
  { ringHomCongrLeft f.toRingHom with
    toFun := (Finsupp.mapRange f f.map_zero : AddMonoidAlgebra R G → AddMonoidAlgebra S G)
    commutes' := fun r => by
      -- Porting note: was `ext`
      refine Finsupp.ext fun a => ?_
      simp_rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Finsupp.mapRange_single]
      congr 2
      rw [AlgHom.map_algebraMap] }

@[simps!]
def algEquivCongrLeft {k R S G : Type _} [CommSemiring k] [Semiring R] [Algebra k R] [Semiring S]
    [Algebra k S] [AddMonoid G] (f : R ≃ₐ[k] S) : AddMonoidAlgebra R G ≃ₐ[k] AddMonoidAlgebra S G :=
  .ofAlgHom (algHomCongrLeft f) (algHomCongrLeft f.symm)
    (AlgHom.ext fun x => Finsupp.ext fun a => by simp)
    (AlgHom.ext fun x => Finsupp.ext fun a => by simp)

@[simps]
def algAutCongrLeft {k R G : Type _} [CommSemiring k] [Semiring R] [Algebra k R] [AddMonoid G] :
    (R ≃ₐ[k] R) →* AddMonoidAlgebra R G ≃ₐ[k] AddMonoidAlgebra R G where
  toFun f := algEquivCongrLeft f
  map_one' := by
    ext
    refine Finsupp.ext fun a => ?_
    simp [Finsupp.mapRange_apply]
  map_mul' x y := by
    ext
    refine Finsupp.ext fun a => ?_
    simp [Finsupp.mapRange_apply]

@[simp 1001] -- LHS simplifies
lemma algAutCongrLeft_apply_one {k R G : Type _} [CommSemiring k] [Semiring R] [Algebra k R]
    [AddMonoid G] :
    algAutCongrLeft (k := k) (R := R) (G := G) 1 = AlgEquiv.refl := by
  ext
  exact Finsupp.mapRange_id _

@[simps]
def mapDomainRingEquiv (k : Type _) [Semiring k] {G H : Type _} [AddMonoid G] [AddMonoid H]
    (f : G ≃+ H) : AddMonoidAlgebra k G ≃+* AddMonoidAlgebra k H :=
  { Finsupp.domCongr f.toEquiv with
    toFun := Finsupp.equivMapDomain f
    invFun := Finsupp.equivMapDomain f.symm
    map_mul' := fun x y => by
      simp_rw [← Finsupp.domCongr_apply]
      induction x using Finsupp.induction_linear with
      | h0 =>
        simp only [map_zero, MulZeroClass.zero_mul]
      | hadd f g hf hg =>
        -- Porting note: was
        -- simp only [add_mul, map_add, *]
        rw [add_mul, map_add, hf, hg, map_add, add_mul]
      | hsingle => ?_
      induction y using Finsupp.induction_linear with
      | h0 =>
        simp only [mul_zero, map_zero]
      | hadd f g hf hg =>
        simp only [map_add]
        rw [mul_add, map_add, hf, hg, mul_add]
      | hsingle =>
        -- Porting note: was `ext`
        refine Finsupp.ext fun a => ?_
        simp only [Finsupp.domCongr_apply, single_mul_single, Finsupp.equivMapDomain_single,
          AddEquiv.coe_toEquiv, map_add] }

@[simps]
def mapDomainAlgEquiv (k A : Type _) [CommSemiring k] [Semiring A] [Algebra k A] {G H : Type _}
    [AddMonoid G] [AddMonoid H] (f : G ≃+ H) : AddMonoidAlgebra A G ≃ₐ[k] AddMonoidAlgebra A H :=
  { mapDomainRingEquiv A f with
    toFun := Finsupp.equivMapDomain f
    invFun := Finsupp.equivMapDomain f.symm
    commutes' := fun r => by
      simp only [Function.comp_apply, Finsupp.equivMapDomain_single,
        AddMonoidAlgebra.coe_algebraMap, map_zero, AddEquiv.coe_toEquiv] }

@[simps]
def mapDomainAlgAut (k A : Type _) [CommSemiring k] [Semiring A] [Algebra k A] {G : Type _}
    [AddMonoid G] : AddAut G →* AddMonoidAlgebra A G ≃ₐ[k] AddMonoidAlgebra A G
    where
  toFun := mapDomainAlgEquiv k A
  map_one' := by
    ext
    refine Finsupp.ext fun a => ?_
    rfl
  map_mul' x y := by
    ext
    refine Finsupp.ext fun a => ?_
    rfl

end AddMonoidAlgebra
