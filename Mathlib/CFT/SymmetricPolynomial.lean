module

public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.RingTheory.TensorProduct.Free

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}

noncomputable section

open scoped Polynomial

@[simp]
lemma Multiset.esymm_zero {R : Type*} [CommSemiring R] (s : Multiset R) : s.esymm 0 = 1 := by
  simp [esymm]

@[simp]
lemma Multiset.esymm_of_card_lt {R : Type*} [CommSemiring R]
    (s : Multiset R) {n : ℕ} (hs : s.card < n) : s.esymm n = 0 := by
  simp [esymm, hs]

namespace Polynomial

variable (R n) in
def freeMonic' : (MvPolynomial (Fin n) R)[X] :=
  (freeMonic R n).map (MvPolynomial.rename Fin.revPerm).toRingHom

lemma coeff_freeMonic' (k) :
    (freeMonic' R n).coeff k = if h : k < n then .X (.rev ⟨k, h⟩) else if k = n then 1 else 0 := by
  simp [freeMonic', coeff_freeMonic, apply_dite (MvPolynomial.rename _)]

lemma degree_freeMonic' [Nontrivial R] : (freeMonic' R n).degree = n := by
  rw [freeMonic', (monic_freeMonic _ _).degree_map, degree_freeMonic]

lemma natDegree_freeMonic' [Nontrivial R] : (freeMonic' R n).natDegree = n :=
  natDegree_eq_of_degree_eq_some degree_freeMonic'

lemma monic_freeMonic' : (freeMonic' R n).Monic :=
  (monic_freeMonic _ _).map _

end Polynomial

variable (R n) in
def MvPolynomial.Symm := MvPolynomial (Fin n) R
  deriving CommRing, Algebra R

open MvPolynomial in
instance : Algebra (MvPolynomial (Fin n) R) (MvPolynomial.Symm R n) :=
  ((symmetricSubalgebra (Fin n) R).val.comp (esymmAlgHom (Fin n) R n)).toRingHom.toAlgebra

open MvPolynomial in
instance : IsScalarTower R (MvPolynomial (Fin n) R) (MvPolynomial.Symm R n) := .of_algebraMap_eq'
  ((symmetricSubalgebra (Fin n) R).val.comp (esymmAlgHom (Fin n) R n)).comp_algebraMap.symm

@[simp]
lemma MvPolynomial.Symm.algebraMap_C (r) :
    algebraMap (MvPolynomial (Fin n) R) (Symm R n) (.C r) = .C r :=
  (IsScalarTower.algebraMap_apply ..).symm

lemma MvPolynomial.Symm.map_freeMonic' :
    (Polynomial.freeMonic' R n).map (algebraMap _ (MvPolynomial.Symm R n)) =
    ∏ i : Fin n, (.X + .C (.X i)) := by
  convert (Multiset.prod_X_add_C_eq_sum_esymm (R := MvPolynomial (Fin n) R)
    (s := Finset.univ.val.map X)).symm
  · trans Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C ((Multiset.ofList <| List.ofFn X).esymm
      (n - (i + 1) + 1)) * Polynomial.X ^ i.1
    · simp [Polynomial.map_sum, esymmAlgHom, RingHom.algebraMap_toAlgebra,
        MvPolynomial.esymm_eq_multiset_esymm, Polynomial.freeMonic', Polynomial.freeMonic,
        MvPolynomial.Symm]
    rw [← Equiv.sum_comp Fin.revPerm]
    simp only [Fin.revPerm_apply, ← Fin.val_rev, Fin.rev_rev]
    rw [Finset.sum_range_succ', Multiset.esymm_zero, map_one, one_mul, add_comm,
      Finset.sum_fin_eq_sum_range]
    simp only [Fin.val_rev, dite_eq_ite, Fin.univ_val_map, Multiset.coe_card, List.length_ofFn,
      tsub_zero]
    congr with i j e
    split_ifs with hin
    · congr
    · have : (Multiset.ofList (List.ofFn X) : Multiset (MvPolynomial (Fin n) R)).card < i + 1 := by
        simp; lia
      simp [Multiset.esymm_of_card_lt _ this]
  · simp [Finset.prod, Function.comp_def, MvPolynomial.Symm]

instance [Nontrivial R] [NeZero n] : Nontrivial (AdjoinRoot (.freeMonic' R n)) := by
  rw [(AdjoinRoot.powerBasis' Polynomial.monic_freeMonic').basis.repr.nontrivial_congr]
  simpa [Polynomial.natDegree_freeMonic'] using
    inferInstanceAs (Nontrivial (Fin n →₀ MvPolynomial (Fin n) R))

instance [Subsingleton R] (p : R[X]) : Subsingleton (AdjoinRoot p) :=
  (algebraMap R _).codomain_trivial

variable (R n)

def Polynomial.freeMonicDivRoot : (AdjoinRoot (freeMonic' R n))[X] :=
  ((freeMonic' R n).map (algebraMap _ _) /ₘ (.X - .C (.root _)))

lemma Polynomial.freeMonicDivRoot_spec :
    (X - C (.root _)) * freeMonicDivRoot R n = (freeMonic' R n).map (algebraMap _ _) := by
  have := ((freeMonic' R n).map (algebraMap _ (AdjoinRoot (freeMonic' R n)))).modByMonic_add_div
    (monic_X_sub_C (.root _))
  simp only [modByMonic_X_sub_C_eq_C_eval, eval_map_algebraMap] at this
  simpa using this

lemma Polynomial.natDegree_freeMonicDivRoot [Nontrivial R] [NeZero n] :
    (freeMonicDivRoot R n).natDegree = n - 1 := by
  rw [freeMonicDivRoot, natDegree_divByMonic _ (monic_X_sub_C _),
    monic_freeMonic'.natDegree_map, natDegree_freeMonic', natDegree_X_sub_C]

lemma Polynomial.monic_freeMonicDivRoot [Nontrivial R] [NeZero n] :
    (freeMonicDivRoot R n).Monic := by
  have := congr($(freeMonicDivRoot_spec R n).leadingCoeff)
  rwa [leadingCoeff_monic_mul (monic_X_sub_C _), monic_freeMonic'.map _] at this

@[local instance]
abbrev Polynomial.freeMonicDivRootAlgebra :
    Algebra (MvPolynomial (Fin n) R) (AdjoinRoot (freeMonic' R (n + 1))) :=
  (MvPolynomial.aeval fun i : Fin n ↦ (freeMonicDivRoot R (n + 1)).coeff i.rev).toRingHom.toAlgebra

@[local instance]
lemma Polynomial.isScalarTower_freeMonicDivRootAlgebra :
    IsScalarTower R (MvPolynomial (Fin n) R) (AdjoinRoot (freeMonic' R (n + 1))) :=
  .of_algebraMap_eq' (MvPolynomial.aeval _).comp_algebraMap.symm

@[simp]
lemma Polynomial.algebraMap_freeMonicDivRootAlgebra_C (r) :
    algebraMap (MvPolynomial (Fin n) R) (AdjoinRoot (freeMonic' R (n + 1))) (.C r) =
      algebraMap _ _ r :=
  (IsScalarTower.algebraMap_apply ..).symm

@[simp]
lemma Polynomial.map_algebraMap_freeMonicDivRootAlgebra_freeMonic' :
    (freeMonic' R n).map (algebraMap (MvPolynomial (Fin n) R) (AdjoinRoot (freeMonic' R (n + 1)))) =
      freeMonicDivRoot R (n + 1) := by
  nontriviality R
  ext i
  by_cases hin : i < n
  · simp [coeff_freeMonic', hin, RingHom.algebraMap_toAlgebra,
      show n - (n - (i + 1) + 1) = i by lia]
  · trans if i = n then 1 else 0
    · simp [coeff_freeMonic', hin]
    split_ifs with hin'
    · convert (monic_freeMonicDivRoot R (n + 1)).symm using 1
      rw [leadingCoeff, natDegree_freeMonicDivRoot, Nat.add_sub_cancel, hin']
    · rw [coeff_eq_zero_of_natDegree_lt]; rw [natDegree_freeMonicDivRoot]; lia

@[local instance]
abbrev MvPolynomial.Symm.succAlgebra :
    Algebra (Symm R n) (Symm R (n + 1)) :=
  (MvPolynomial.rename Fin.succ).toRingHom.toAlgebra

attribute [local instance] MvPolynomial.Symm.succAlgebra -- why needed?

@[local instance]
lemma MvPolynomial.Symm.isScalarTower_succAlgebra :
    IsScalarTower R (Symm R n) (Symm R (n + 1)) :=
  .of_algebraMap_eq' (MvPolynomial.rename Fin.succ).comp_algebraMap.symm

@[simp]
lemma MvPolynomial.Symm.algebraMap_succAlgebra_C (r) :
    algebraMap (Symm R n) (Symm R (n + 1)) (.C r) = .C r :=
  (MvPolynomial.rename Fin.succ).commutes _

@[simp]
lemma MvPolynomial.Symm.algebraMap_succAlgebra_X (i) :
    algebraMap (Symm R n) (Symm R (n + 1)) (.X i) = .X i.succ :=
  MvPolynomial.rename_X Fin.succ _

@[local instance]
abbrev MvPolynomial.Symm.succAlgebra' :
    Algebra (MvPolynomial (Fin n) R) (Symm R (n + 1)) :=
  Algebra.compHom _ (algebraMap _ (Symm R n))

attribute [local instance] MvPolynomial.Symm.succAlgebra'

instance MvPolynomial.Symm.isScalarTower_succAlgebra' :
    IsScalarTower (MvPolynomial (Fin n) R) (Symm R n) (Symm R (n + 1)) :=
  .of_algebraMap_eq' rfl

@[simp]
lemma MvPolynomial.Symm.algebraMap_succAlgebra' :
    algebraMap (MvPolynomial (Fin n) R) (Symm R (n + 1)) =
    (algebraMap _ _).comp (algebraMap _ (Symm R n)) := rfl

lemma MvPolynomial.Symm.aeval_neg_X_freeMonic' [NeZero n] :
    Polynomial.aeval (A := Symm R n) (-X 0) (.freeMonic' R n) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, MvPolynomial.Symm.map_freeMonic',
    Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ 0)]
  simp

@[local instance]
abbrev MvPolynomial.Symm.adjoinRootAlgebra [NeZero n] :
    Algebra (AdjoinRoot (.freeMonic' R n)) (Symm R n) :=
  (AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (-.X 0)
    (by exact aeval_neg_X_freeMonic' R n)).toRingHom.toAlgebra

attribute [local instance] MvPolynomial.Symm.adjoinRootAlgebra

instance MvPolynomial.Symm.isScalarTower_freeMonicDivRootAlgebra [NeZero n] :
    IsScalarTower (MvPolynomial (Fin n) R) (AdjoinRoot (.freeMonic' R n)) (Symm R n) :=
  .of_algebraMap_eq' (AdjoinRoot.liftAlgHom _ _ _ (aeval_neg_X_freeMonic' R n)).comp_algebraMap.symm

instance MvPolynomial.Symm.isScalarTower_freeMonicDivRootAlgebra' [NeZero n] :
    IsScalarTower R (AdjoinRoot (.freeMonic' R n)) (Symm R n) :=
  .to₁₃₄ _ (MvPolynomial (Fin n) R) _ _

@[simp]
lemma MvPolynomial.Symm.algebraMap_freeMonicDivRootAlgebra_of [NeZero n] (p) :
    algebraMap (AdjoinRoot (.freeMonic' R n)) (Symm R n) (.of _ p) = algebraMap _ _ p :=
  (AdjoinRoot.liftAlgHom _ _ _ (aeval_neg_X_freeMonic' R n)).commutes _

@[simp]
lemma MvPolynomial.Symm.algebraMap_freeMonicDivRootAlgebra_comp_of [NeZero n] :
    (algebraMap (AdjoinRoot (.freeMonic' R n)) (Symm R n)).comp (AdjoinRoot.of _) =
      algebraMap _ _ :=
  (AdjoinRoot.liftAlgHom _ _ _ (aeval_neg_X_freeMonic' R n)).comp_algebraMap

@[simp]
lemma MvPolynomial.Symm.algebraMap_freeMonicDivRootAlgebra_root [NeZero n] :
    algebraMap (AdjoinRoot (.freeMonic' R n)) (Symm R n) (.root _) = - .X 0 :=
  AdjoinRoot.lift_root (aeval_neg_X_freeMonic' R n)

lemma MvPolynomial.Symm.map_freeMonicDivRoot_algebraMap_adjoinRoot_symm :
    (Polynomial.freeMonicDivRoot R (n + 1)).map (algebraMap _ (Symm R (n + 1))) =
        ∏ i : Fin n, (.X + .C (.X i.succ)) := by
  have : (.X + .C (MvPolynomial.X 0)) * (Polynomial.freeMonicDivRoot R (n + 1)).map
    (algebraMap (AdjoinRoot (.freeMonic' R (n + 1))) (Symm R (n + 1))) =
      ∏ i, (.X + .C (.X i)) := by
    simpa [Polynomial.map_map, MvPolynomial.Symm.map_freeMonic'] using
      congr(($(Polynomial.freeMonicDivRoot_spec R (n + 1))).map (algebraMap _ (Symm R (n + 1))))
  apply (isRegular_iff_mem_nonZeroDivisors.mpr
    ((Polynomial.monic_X_add_C (.X 0)).mem_nonZeroDivisors)).1
  simp only [this, Fin.prod_univ_succ]

instance MvPolynomial.Symm.isScalarTower_freeMonicDivRootAlgebra_adjoinRootAlgebra :
    IsScalarTower (MvPolynomial (Fin n) R)
      (AdjoinRoot (.freeMonic' R (n + 1))) (Symm R (n + 1)) := by
  refine .of_algebraMap_eq' ?_
  apply MvPolynomial.ringHom_ext
  · simp [AdjoinRoot.algebraMap_eq']
  · intro i
    suffices (algebraMap (AdjoinRoot (.freeMonic' R (n + 1))) (Symm R (n + 1)))
      ((Polynomial.freeMonicDivRoot R _).coeff i.rev) = rename Fin.succ (esymm (Fin n) R (i + 1)) by
      simpa [RingHom.algebraMap_toAlgebra, Symm, esymmAlgHom] using this.symm
    rw [← Polynomial.coeff_map, map_freeMonicDivRoot_algebraMap_adjoinRoot_symm,
      Finset.prod_X_add_C_coeff]
    · simp [Fin.val_rev, esymm, map_sum, map_prod, rename_X]
      congr; lia
    · simp

open TensorProduct

def MvPolynomial.Symm.toTensor :
    MvPolynomial.Symm R (n + 1) →ₐ[R]
      (AdjoinRoot (.freeMonic' R (n + 1))) ⊗[MvPolynomial (Fin n) R] MvPolynomial.Symm R n :=
  MvPolynomial.aeval (Fin.cases (- .root _ ⊗ₜ 1) (1 ⊗ₜ .X ·))

@[simp] lemma MvPolynomial.Symm.toTensor_C (r) :
    toTensor R n (.C r) = algebraMap _ _ r :=
  (toTensor R n).commutes _

@[simp] lemma MvPolynomial.Symm.toTensor_X_zero :
    toTensor R n (.X 0) = - .root _ ⊗ₜ 1 := by
  simp [toTensor, Symm]

@[simp] lemma MvPolynomial.Symm.toTensor_X_succ (i : Fin n) :
    toTensor R n (.X i.succ) = 1 ⊗ₜ .X i := by
  simp [toTensor, Symm]

-- set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
@[simp] lemma MvPolynomial.Symm.toTensor_comp_algebraMap :
    (toTensor R n).toRingHom.comp (algebraMap _ _) = Algebra.TensorProduct.includeLeftRingHom := by
  suffices ((Polynomial.freeMonic' R (n + 1)).map
      (algebraMap _ (AdjoinRoot (.freeMonic' R (n + 1))))).map
        ((toTensor R n).toRingHom.comp (algebraMap _ _)) =
    ((Polynomial.freeMonic' R (n + 1)).map
      (algebraMap _ (AdjoinRoot (.freeMonic' R (n + 1))))).map
        Algebra.TensorProduct.includeLeftRingHom by
    ext i
    · simp; rfl
    · obtain ⟨i, rfl⟩ := Fin.rev_bijective.surjective i
      simpa [Polynomial.coeff_freeMonic'] using congr(($this).coeff i)
    · simp
  rw [← Polynomial.freeMonicDivRoot_spec,
    ← Polynomial.map_algebraMap_freeMonicDivRootAlgebra_freeMonic', Polynomial.map_mul,
    Polynomial.map_mul]
  congr 1; · simp
  simp only [Polynomial.map_map, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  rw [Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap,
    IsScalarTower.algebraMap_eq _ (Symm R n)]
  simp only [← Polynomial.map_map, map_freeMonic', Polynomial.map_prod]
  simp

def MvPolynomial.Symm.adjoinRootTensorEquiv :
    (AdjoinRoot (.freeMonic' R (n + 1))) ⊗[MvPolynomial (Fin n) R] MvPolynomial.Symm R n
      ≃ₐ[AdjoinRoot (.freeMonic' R (n + 1))] MvPolynomial.Symm R (n + 1) :=
  .ofAlgHom (Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom _ _ _)
    fun _ _ ↦ .all _ _) ⟨toTensor R n, fun r ↦ congr($(toTensor_comp_algebraMap R n) r)⟩ (by
    refine AlgHom.restrictScalars_injective R ?_
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    induction i using Fin.cases with
    | zero => dsimp; erw [toTensor_X_zero]; simp; rfl
    | succ i => dsimp; erw [toTensor_X_succ]; simp; rfl) (by
    refine Algebra.TensorProduct.ext (by ext) ?_
    refine AlgHom.restrictScalars_injective R ?_
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    simpa [Symm, RingHom.algebraMap_toAlgebra, -toTensor_X_succ] using toTensor_X_succ ..)

def TensorProduct.AlgebraTensorModule.finsuppRight
    (R S M N : Type*) [CommSemiring R] [AddCommMonoid M] [Semiring S] [Module S M]
    [Module R M] [AddCommMonoid N] [Module R N] [SMulCommClass R S M] (ι : Type*)
    [DecidableEq ι] :
    M ⊗[R] (ι →₀ N) ≃ₗ[S] ι →₀ M ⊗[R] N where
  __ := TensorProduct.finsuppRight R M N ι
  map_smul' m x := by induction x <;>
    simp_all [TensorProduct.finsuppRight_apply_tmul, smul_tmul', Finsupp.smul_sum]

def _root_.TensorProduct.AlgebraTensorModule.rid'.{uR, uA, uM}
    (R : Type uR) (A : Type uA) (M : Type uM) [CommSemiring R]
    [Semiring A] [AddCommMonoid M] [Module R M] [Module A M] [SMulCommClass R A M] :
    M ⊗[R] R ≃ₗ[A] M where
  __ := TensorProduct.rid R M
  map_smul' m x := by induction x <;> simp_all [smul_tmul', smul_comm]

def TensorProduct.AlgebraTensorModule.finsuppScalarRight
    (R S M : Type*) [CommSemiring R] [AddCommMonoid M] [Semiring S] [Module S M]
    [Module R M] [SMulCommClass R S M] (ι : Type*)
    [DecidableEq ι] :
    M ⊗[R] (ι →₀ R) ≃ₗ[S] ι →₀ M :=
  TensorProduct.AlgebraTensorModule.finsuppRight .. ≪≫ₗ
    (Finsupp.mapRange.linearEquiv (TensorProduct.AlgebraTensorModule.rid' _ _ _))

def MvPolymial.Symm.zeroEquiv :
    MvPolynomial (Fin 0) R ≃ₐ[MvPolynomial (Fin 0) R] MvPolynomial.Symm R 0 where
  toRingEquiv := .refl _
  commutes' r := by
    change r = _
    obtain ⟨r, rfl⟩ := (MvPolynomial.isEmptyAlgEquiv _ _).symm.surjective r
    simp [MvPolynomial.isEmptyAlgEquiv]

open Polynomial (freeMonic') in
set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 0 in
def MvPolynomial.Symm.equivFinsupp' [Nontrivial R] :
    ∀ n, ((Π i : Fin n, Fin (i + 1)) →₀ (MvPolynomial (Fin n) R))
      ≃ₗ[MvPolynomial (Fin n) R] MvPolynomial.Symm R n
  | 0 => (Finsupp.LinearEquiv.finsuppUnique _ _ _) ≪≫ₗ
      (MvPolymial.Symm.zeroEquiv R).toLinearEquiv
  | (n + 1) =>
    Finsupp.mapDomain.linearEquiv _ _ ((Fin.snocEquiv _).symm.trans
      ((Equiv.prodComm _ _).trans (Equiv.prodCongr (.refl _)
      (finCongr (by simp [Polynomial.natDegree_freeMonic']))))) ≪≫ₗ
    Finsupp.finsuppProdLEquiv _ ≪≫ₗ
    Finsupp.mapRange.linearEquiv (AdjoinRoot.powerBasis'
    (Polynomial.monic_freeMonic' (R := R) (n := n + 1))).basis.repr.symm ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.finsuppScalarRight _ _ _ _).symm ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.congr (.refl (AdjoinRoot (freeMonic' R (n + 1)))
      (AdjoinRoot (freeMonic' R (n + 1)))) (equivFinsupp' n)).restrictScalars
      (MvPolynomial (Fin (n + 1)) R) ≪≫ₗ
    (Symm.adjoinRootTensorEquiv R n).toLinearEquiv.restrictScalars _

lemma MvPolynomial.Symm.equivFinsupp'_single_one
    [Nontrivial R] (n : ℕ) (p : Π i : Fin n, Fin (i + 1)) :
    MvPolynomial.Symm.equivFinsupp' R n (.single p 1) =
      ((-1) ^ ∑ i, (p i).1) * monomial (Finsupp.equivFunOnFinite.symm (p ·.rev)) 1 := by
  induction n with
  | zero =>
    obtain rfl := Subsingleton.elim p isEmptyElim
    simp [equivFinsupp', -Pi.default_def, Pi.uniqueOfIsEmpty, Unique.instInhabited,
      Subsingleton.elim (Finsupp.equivFunOnFinite.symm _) 0]
  | succ n IH =>
    trans (-X 0) ^ (p (.last n)).1 * ((-1) ^ ∑ x : Fin n, ↑(p x.castSucc)) *
      algebraMap (Symm R n) (Symm R (n + 1))
        (monomial (Finsupp.equivFunOnFinite.symm fun x ↦ (p x.rev.castSucc).1) 1)
    · simp [equivFinsupp', AlgebraTensorModule.finsuppScalarRight, mul_assoc,
        TensorProduct.AlgebraTensorModule.finsuppRight, -AdjoinRoot.powerBasis'_dim,
        AlgebraTensorModule.rid', adjoinRootTensorEquiv, IH, Fin.snocEquiv, Fin.init]
    rw [neg_pow, mul_right_comm (_ ^ _), ← pow_add, mul_assoc]
    simp only [Symm, Fin.val_last, Fin.val_castSucc, RingHom.algebraMap_toAlgebra,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_monomial, ← monomial_single_add]
    congr
    · simp [Fin.sum_univ_castSucc, add_comm]
    · ext i
      cases i using Fin.cases with
      | zero => simp [Finsupp.mapDomain_notin_range]; rfl
      | succ i =>
        suffices (p i.rev.castSucc).1 = p i.succ.rev by
          simpa [Finsupp.mapDomain_apply, Fin.succ_injective]
        congr <;> rw [Fin.rev_succ]

lemma MvPolynomial.Symm.equivFinsupp'_single [Nontrivial R]
      (n : ℕ) (p : Π i : Fin n, Fin (i + 1)) (a) :
    MvPolynomial.Symm.equivFinsupp' R n (.single p a) =
      a • (((-1) ^ ∑ i, (p i).1) * monomial (Finsupp.equivFunOnFinite.symm (p ·.rev)) 1) := by
  rw [← equivFinsupp'_single_one, ← LinearEquiv.map_smul, Finsupp.smul_single_one]

def MvPolynomial.Symm.renameEquiv (σ : Equiv.Perm (Fin n)) :
    Symm R n ≃ₐ[MvPolynomial (Fin n) R] Symm R n where
  toRingEquiv := (MvPolynomial.renameEquiv _ σ).toRingEquiv
  commutes' r := by
    have : (MvPolynomial.renameEquiv R σ).toAlgHom.comp (IsScalarTower.toAlgHom R
        (MvPolynomial (Fin n) R) (Symm R n)) = IsScalarTower.toAlgHom _ _ (Symm R n) := by
      ext1 i
      simp [Symm, RingHom.algebraMap_toAlgebra, esymmAlgHom, rename_esymm]
    exact congr($this r)

def MvPolynomial.Symm.basis (n : ℕ) :
    Module.Basis (Π i : Fin n, Fin (i + 1)) (MvPolynomial (Fin n) R) (MvPolynomial.Symm R n) :=
  letI := Classical.propDecidable (Subsingleton R)
  if h : Subsingleton R then ⟨Module.subsingletonEquiv ..⟩ else
  haveI : Nontrivial R := not_subsingleton_iff_nontrivial.mp h
  ⟨(Finsupp.linearEquivFunOnFinite _ _ _ ≪≫ₗ
    (LinearEquiv.piCongrRight fun p ↦ LinearEquiv.smulOfUnit ((-1) ^ ∑ i, (p i).1)) ≪≫ₗ
    (Finsupp.linearEquivFunOnFinite _ _ _).symm ≪≫ₗ
    equivFinsupp' R n ≪≫ₗ (renameEquiv _ _ Fin.revPerm).toLinearEquiv).symm⟩

lemma MvPolynomial.Symm.basis_apply (n : ℕ) (p : Π i : Fin n, Fin (i + 1)) :
    MvPolynomial.Symm.basis R n p =
      monomial (Finsupp.equivFunOnFinite.symm (p ·)) 1 := by
  cases subsingleton_or_nontrivial R
  · dsimp [Symm]; exact Subsingleton.elim _ _
  have H : (fun q ↦ LinearEquiv.smulOfUnit ((-1 : (MvPolynomial (Fin n) R)ˣ) ^ ∑ i, (q i).1)
    ((Pi.single p 1 : (Π i : Fin n, Fin (i + 1)) → MvPolynomial (Fin n) R) q) :
      (Π i : Fin n, Fin (i + 1)) → MvPolynomial (Fin n) R) = Pi.single p ((-1) ^ ∑ i, (p i).1) := by
    ext1; simp +contextual [Pi.single_apply, apply_ite, LinearEquiv.smulOfUnit, Units.smul_def]
  trans renameEquiv R n Fin.revPerm (monomial (Finsupp.equivFunOnFinite.symm (p ·.rev)) 1)
  · simp [MvPolynomial.Symm.basis, LinearEquiv.piCongrRight, H, equivFinsupp'_single,
      Algebra.smul_def, ← mul_assoc, ← pow_add, not_subsingleton R]
  have (a : Fin n) : (p a.rev.rev).1 = p a := by grind
  simp [renameEquiv, Symm, rename_monomial, Finsupp.ext_iff, this]

public def MvPolynomial.symmetricSubalgebraBasis (n : ℕ) :
    Module.Basis (Π i : Fin n, Fin (i + 1)) (symmetricSubalgebra (Fin n) R)
      (MvPolynomial (Fin n) R) :=
  @Module.Basis.mapCoeffs _ _ _ _ _ _ (MvPolynomial.Symm.basis _ _) _ _
    (inferInstanceAs (Module (symmetricSubalgebra (Fin n) R) (MvPolynomial (Fin n) R)))
    (esymmAlgEquiv _ _ (by simp)).toRingEquiv fun c x ↦ rfl

public lemma MvPolynomial.symmetricSubalgebraBasis_apply (n : ℕ) (p : Π i : Fin n, Fin (i + 1)) :
    MvPolynomial.symmetricSubalgebraBasis R n p =
      monomial (Finsupp.equivFunOnFinite.symm (p ·)) 1 := by
  rw [MvPolynomial.symmetricSubalgebraBasis]
  erw [@Module.Basis.mapCoeffs_apply]
  rw [MvPolynomial.Symm.basis_apply]

public instance : Module.Free (MvPolynomial.symmetricSubalgebra (Fin n) R)
    (MvPolynomial (Fin n) R) := .of_basis (MvPolynomial.symmetricSubalgebraBasis R n)

public instance : Module.Finite (MvPolynomial.symmetricSubalgebra (Fin n) R)
    (MvPolynomial (Fin n) R) := .of_basis (MvPolynomial.symmetricSubalgebraBasis R n)

public lemma MvPolynomial.finrank_symmetricSubalgebra [Nontrivial R] (n : ℕ) :
    Module.finrank (symmetricSubalgebra (Fin n) R) (MvPolynomial (Fin n) R) = n.factorial := by
  rw [Module.finrank_eq_card_basis (symmetricSubalgebraBasis R n)]
  simp [Fin.prod_univ_eq_prod_range (f := (· + 1))]

@[expose] public section SplittingAlgebra

open Polynomial TensorProduct

variable {R}

def Polynomial.SplittingAlgebra (p : R[X]) : Type _ :=
    letI n := p.natDegree
    letI f : (MvPolynomial.symmetricSubalgebra (Fin n) ℤ) →+* R :=
      (MvPolynomial.aeval (p.coeff ·.rev.1)).toRingHom.comp
        (MvPolynomial.esymmAlgEquiv (n := n) _ _ (by simp)).symm.toRingHom
    letI := f.toAlgebra
    R ⊗[MvPolynomial.symmetricSubalgebra (Fin n) ℤ] MvPolynomial (Fin n) ℤ
  deriving CommRing, Algebra R, Module.Free R, Module.Finite R

lemma Polynomial.splits_splittingAlgebra (p : R[X]) (hp : p.Monic) :
  letI := Polynomial.instAlgebraSplittingAlgebra p;
    (p.map (algebraMap R p.SplittingAlgebra)).Splits := by
  letI n := p.natDegree
  letI f : (MvPolynomial.symmetricSubalgebra (Fin n) ℤ) →+* R :=
    (MvPolynomial.aeval (p.coeff ·.rev.1)).toRingHom.comp
      (MvPolynomial.esymmAlgEquiv (n := n) _ _ (by simp)).symm.toRingHom
  letI := f.toAlgebra
  letI : Algebra (MvPolynomial.symmetricSubalgebra (Fin n) ℤ)
    (R ⊗[MvPolynomial.symmetricSubalgebra (Fin n) ℤ] MvPolynomial (Fin n) ℤ) :=
      Algebra.TensorProduct.leftAlgebra ..
  have : (Polynomial.freeMonic' ℤ n).map
      ((algebraMap _ (R ⊗[MvPolynomial.symmetricSubalgebra (Fin n) ℤ] MvPolynomial (Fin n) ℤ)).comp
        (MvPolynomial.esymmAlgEquiv (Fin n) _ (by simp)).toRingHom) =
      p.map (algebraMap R p.SplittingAlgebra) := by
    ext i
    by_cases hi : i < n
    · simp [coeff_freeMonic', hi, RingHom.algebraMap_toAlgebra, f, - AlgEquiv.symm_toRingEquiv,
        - MvPolynomial.esymmAlgEquiv_apply, - Fin.val_rev]; rfl
    by_cases hi' : i = n
    · simp [coeff_freeMonic', hi', n, hp, Algebra.TensorProduct.one_def]
    · simp [coeff_freeMonic', *, coeff_eq_zero_of_natDegree_lt (show n < i by lia)]
  rw [← this, ← Algebra.TensorProduct.includeRight.comp_algebraMap, ← Polynomial.map_map,
    ← Polynomial.map_map]
  refine .map ?_ _
  have : (∏ i : Fin n, (X + C (.X i)) : (MvPolynomial (Fin n) ℤ)[X]).Splits :=
    .prod fun _ _ ↦ .X_add_C _
  convert this
  ext1 i
  by_cases hi : i < n
  · rw [Finset.prod_X_add_C_coeff (h := by simpa using hi.le)]
    simp [coeff_freeMonic', hi, MvPolynomial.esymmAlgHom, MvPolynomial.esymm,
      show n - (i + 1) + 1 = n - i by lia]
  have H : (∏ i : Fin n, (X + C (.X i)) : (MvPolynomial (Fin n) ℤ)[X]).natDegree = n := by
    simp [natDegree_prod_of_monic, monic_X_add_C]
  by_cases hi' : i = n
  · trans 1
    · simp [coeff_freeMonic', hi']
    trans (∏ i : Fin n, (X + C (.X i)) : (MvPolynomial (Fin n) ℤ)[X]).leadingCoeff
    · simp [monic_prod_of_monic, monic_X_add_C]
    · rw [leadingCoeff, H, hi']
  · simp [coeff_freeMonic', hi, hi', coeff_eq_zero_of_natDegree_lt (H.trans_lt (show n < i by lia))]

lemma Polynomial.finrank_splittingAlgebra [Nontrivial R] (p : R[X]) :
    Module.finrank R p.SplittingAlgebra = p.natDegree.factorial := by
  letI n := p.natDegree
  letI f : (MvPolynomial.symmetricSubalgebra (Fin n) ℤ) →+* R :=
    (MvPolynomial.aeval (p.coeff ·.rev.1)).toRingHom.comp
      (MvPolynomial.esymmAlgEquiv (n := n) _ _ (by simp)).symm.toRingHom
  letI := f.toAlgebra
  refine (Module.finrank_baseChange ..).trans ?_
  rw [MvPolynomial.finrank_symmetricSubalgebra]

instance [Nontrivial R] (p : R[X]) : Nontrivial p.SplittingAlgebra :=
  not_subsingleton_iff_nontrivial.mp fun _ ↦
    p.natDegree.factorial_ne_zero
      (p.finrank_splittingAlgebra.symm.trans Module.finrank_zero_of_subsingleton)

end SplittingAlgebra
