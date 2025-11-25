/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Polynomial.Resultant.Basic


/-!

# Universal factorization ring

Let `R` be a commutative ring and `p : R[X]` be monic of degree `n` and let `n = m + k`.
We construct the universal ring of the following functors on `R-Alg`:
- `S ↦ "monic polynomials over S of degree n"`:
  Represented by `R[X₁,...,Xₙ]`. See `MvPolynomial.mapEquivMonic`.
- `S ↦ "factorizations of p into (monic deg m) * (monic deg k) in S"`:
  Represented by an `R`-algebra (`Polynomial.UniversalFactorizationRing`) that is finitely-presented
  as an `R`-module. See `Polynomial.UniversalFactorizationRing.homEquiv`.
- `S ↦ "factorizations of p into coprime (monic deg m) * (monic deg k) in S"`:
  Represented by an etale `R`-algebra (TODO).

-/

@[expose] public section

open scoped Polynomial TensorProduct

open RingHomClass (toRingHom)

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (n m k : ℕ) (hn : n = m + k)

noncomputable section

namespace Polynomial

/-- The free monic polynomial of degree `n`, as a polynomial in `R[X₁,...,Xₙ][X]`. -/
def freeMonic : (MvPolynomial (Fin n) R)[X] :=
  .X ^ n + ∑ i : Fin n, .C (.X i) * .X ^ (i : ℕ)

lemma coeff_freeMonic :
    (freeMonic R n).coeff k = if h : k < n then .X ⟨k, h⟩ else if k = n then 1 else 0 := by
  simp only [freeMonic, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul, mul_ite, mul_one, mul_zero]
  by_cases h : k < n
  · simp +contextual [Finset.sum_eq_single (ι := Fin n) (a := ⟨k, h⟩),
      Fin.ext_iff, @eq_comm _ k, h, h.ne']
  ·rw [Finset.sum_eq_zero fun x _ ↦ if_neg (by cases x; omega), add_zero, dif_neg h]

lemma degree_freeMonic [Nontrivial R] : (freeMonic R n).degree = n :=
  Polynomial.degree_eq_of_le_of_coeff_ne_zero ((Polynomial.degree_le_iff_coeff_zero _ _).mpr
    (by simp +contextual [coeff_freeMonic, LT.lt.not_gt, LT.lt.ne']))
    (by simp [coeff_freeMonic])

lemma natDegree_freeMonic [Nontrivial R] : (freeMonic R n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_freeMonic R n)

lemma monic_freeMonic : (freeMonic R n).Monic := by
  nontriviality R
  simp [Polynomial.Monic, ← Polynomial.coeff_natDegree, natDegree_freeMonic, coeff_freeMonic]

omit [Algebra R S] in
lemma map_map_freeMonic (f : R →+* S) :
    (freeMonic R n).map (MvPolynomial.map f) = freeMonic S n := by
  simp [freeMonic, Polynomial.map_sum]

open Polynomial (MonicDegreeEq)

/-- The free monic polynomial of degree `n`, as a `MonicDegreeEq` in `R[X₁,...,Xₙ][X]`. -/
@[simps]
def MonicDegreeEq.freeMonic : MonicDegreeEq (MvPolynomial (Fin n) R) n :=
  ⟨.freeMonic R n, by simp +contextual [coeff_freeMonic, not_lt_of_gt, LT.lt.ne']⟩

end Polynomial

namespace MvPolynomial

open Polynomial

/-- `MonicDegreeEq · n` is representable by `R[X₁,...,Xₙ]`,
with the universal element being `freeMonic`. -/
def mapEquivMonic : (MvPolynomial (Fin n) R →ₐ[R] S) ≃ MonicDegreeEq S n where
  toFun f := .map (.freeMonic _ _) f.toRingHom
  invFun p := aeval (p.1.coeff ·)
  left_inv f := by ext i; simp [coeff_freeMonic]
  right_inv p := by
    suffices ∀ i ≥ n, (if i = n then 1 else 0) = p.1.coeff i by
      ext i; simp +contextual [coeff_freeMonic, apply_dite, this]
    intro i hi
    split_ifs with hi'
    · simp [hi', p.2.1]
    · simp [p.2.2 _ (hi.lt_of_ne' hi')]

variable {R S T} in
lemma coe_mapEquivMonic_comp (f : MvPolynomial (Fin n) R →ₐ[R] S) (g : S →ₐ[R] T) :
    (mapEquivMonic R T n (g.comp f)).1 = (mapEquivMonic R S n f).1.map g :=
  (Polynomial.map_map ..).symm

variable {R S T} in
lemma coe_mapEquivMonic_comp' (f : MvPolynomial (Fin n) R →ₐ[R] S) (g : S →ₐ[R] T) :
    mapEquivMonic R T n (g.comp f) = (mapEquivMonic R S n f).map g :=
  Subtype.ext (coe_mapEquivMonic_comp ..)

variable {R S T} in
lemma mapEquivMonic_symm_map (p : MonicDegreeEq S n) (g : S →ₐ[R] T) :
    (mapEquivMonic R T n).symm (p.map g) = g.comp ((mapEquivMonic R S n).symm p) := by
  obtain ⟨f, rfl⟩ := (mapEquivMonic R S n).surjective p
  exact (mapEquivMonic R T n).symm_apply_eq.mpr (by simp [coe_mapEquivMonic_comp'])

variable {R S T} in
lemma mapEquivMonic_symm_map_algebraMap
    (p : MonicDegreeEq S n) [Algebra S T] [IsScalarTower R S T] :
    (mapEquivMonic R T n).symm (p.map (algebraMap S T)) =
      (IsScalarTower.toAlgHom R S T).comp ((mapEquivMonic R S n).symm p) := by
  rw [← mapEquivMonic_symm_map]; rfl

/-- In light of the fact that `MonicDegreeEq · n` is representable by `R[X₁,...,Xₙ]`,
this is the map `R[X₁,...,Xₘ₊ₖ] → R[X₁,...,Xₘ] ⊗ R[X₁,...,Xₖ]` corresponding to the multiplication
`MonicDegreeEq · m × MonicDegreeEq · k → MonicDegreeEq · (m + k)`. -/
def universalFactorizationMap (hn : n = m + k) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R :=
  (mapEquivMonic R _ n).symm
  ⟨(mapEquivMonic R _ m Algebra.TensorProduct.includeLeft).1 *
    (mapEquivMonic R _ k Algebra.TensorProduct.includeRight).1, by
    nontriviality R
    nontriviality MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R
    refine (MonicDegreeEq.mk _ ?_ ?_).2
    · exact ((monic_freeMonic R m).map _).mul ((monic_freeMonic R _).map _)
    dsimp [mapEquivMonic]
    rw [((monic_freeMonic R m).map _).natDegree_mul ((monic_freeMonic R k).map _)]
    simp_rw [(monic_freeMonic R _).natDegree_map, natDegree_freeMonic, hn]⟩

lemma universalFactorizationMap_freeMonic :
    (freeMonic R n).map (toRingHom <| universalFactorizationMap R n m k hn) =
      (freeMonic R m).map (algebraMap _ _) *
        (freeMonic R k).map (toRingHom <| Algebra.TensorProduct.includeRight) := by
  change (mapEquivMonic _ _ _ (universalFactorizationMap R n m k hn)).1 = _
  simp [universalFactorizationMap]
  rfl

lemma universalFactorizationMap_comp_map :
    (universalFactorizationMap S n m k hn).toRingHom.comp (map (algebraMap R S)) =
    .comp (Algebra.TensorProduct.lift (S := R)
      (Algebra.TensorProduct.includeLeft.comp (mapAlgHom (Algebra.ofId R S)))
      ((Algebra.TensorProduct.includeRight.restrictScalars R).comp (mapAlgHom (Algebra.ofId R S)))
      fun _ _ ↦ .all _ _).toRingHom
      (universalFactorizationMap R n m k hn).toRingHom := by
  ext
  · simp
  · dsimp [universalFactorizationMap, mapEquivMonic]
    simp only [map_X, aeval_X, ← AlgHom.coe_toRingHom, ← Polynomial.coeff_map, Polynomial.map_mul,
      Polynomial.map_map, ← map_map_freeMonic (f := algebraMap R S)]
    congr <;> ext <;> simp [← algebraMap_apply]

/-- Lifts along `universalFactorizationMap` corresponds to factorization of `p` into
monic polynomials with fixed degrees. -/
def universalFactorizationMapLiftEquiv (p : MonicDegreeEq S n) :
    { f // AlgHom.comp f (universalFactorizationMap R n m k hn) =
        (mapEquivMonic _ _ n).symm p } ≃
    { q : MonicDegreeEq S m × MonicDegreeEq S k // q.1.1 * q.2.1 = p } where
  toFun f := ⟨(mapEquivMonic R _ _ (f.1.comp Algebra.TensorProduct.includeLeft),
    mapEquivMonic R _ _ (f.1.comp Algebra.TensorProduct.includeRight)), by
      conv_rhs => rw [← (Equiv.eq_symm_apply _).mp f.2]
      simp [MvPolynomial.coe_mapEquivMonic_comp, MvPolynomial.universalFactorizationMap]⟩
  invFun q := ⟨Algebra.TensorProduct.lift ((mapEquivMonic _ _ _).symm q.1.1)
    ((mapEquivMonic _ _ _).symm q.1.2) fun _ _ ↦ .all _ _, by
    refine (mapEquivMonic R S n).eq_symm_apply.mpr <| Subtype.ext ?_
    simp only [universalFactorizationMap, coe_mapEquivMonic_comp, Equiv.apply_symm_apply,
      Polynomial.map_mul]
    simp [← coe_mapEquivMonic_comp, ← q.2]⟩
  left_inv f := by ext <;> simp
  right_inv q := by ext <;> simp

lemma ker_eval₂Hom_universalFactorizationMap :
    RingHom.ker (eval₂Hom (S₁ := MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R)
      (universalFactorizationMap R n m k hn) (Sum.elim (.X · ⊗ₜ 1) (1 ⊗ₜ .X ·))) =
    Ideal.span (Set.range fun i ↦ C (X i) - map C (tensorEquivSum _ _ _ _
      (universalFactorizationMap R n m k hn (X i)))) := by
  set f := eval₂Hom (R := MvPolynomial (Fin n) R)
    (S₁ := MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R)
    (universalFactorizationMap R n m k hn) (Sum.elim (.X · ⊗ₜ 1) (1 ⊗ₜ .X ·))
  have H (i : _) : tensorEquivSum _ _ _ _ (f (.X i)) = .X i := by aesop
  apply le_antisymm
  · intro x hx
    convert_to x - (tensorEquivSum _ _ _ _ (f x)).map C ∈ Ideal.span _ using 1
    · simp_all only [RingHom.mem_ker, map_zero, sub_zero]
    clear hx
    induction x using MvPolynomial.induction_on with
    | add p q _ _ => simp only [map_add, add_sub_add_comm]; exact add_mem ‹_› ‹_›
    | mul_X p i _ => simp only [map_mul, H, map_X, ← sub_mul]; exact Ideal.mul_mem_right _ _ ‹_›
    | C x =>
    induction x using MvPolynomial.induction_on with
    | C a => simp [f]
    | add p q _ _ => simp only [map_add, add_sub_add_comm]; exact add_mem ‹_› ‹_›
    | mul_X p i IH =>
      simp only [map_mul]
      exact Ideal.mul_sub_mul_mem _ IH (Ideal.subset_span ⟨i, by simp [f]⟩)
  · simp only [Ideal.span_le, Set.range_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub,
      eval₂Hom_C, RingHom.coe_coe, eval₂Hom_map_hom, coe_eval₂Hom, sub_eq_zero, f]
    simp only [← algebraMap_eq, AlgHom.comp_algebraMap_of_tower, ← aeval_def]
    intro i
    generalize universalFactorizationMap R n m k hn (X i) = p
    change AlgHom.id R _ p = ((aeval _).comp (tensorEquivSum R _ _ R).toAlgHom) p
    congr 1
    ext <;> simp

/-- The canonical presentation of `universalFactorizationMap`. -/
@[simps] def universalFactorizationMapPresentation :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    Algebra.PreSubmersivePresentation (MvPolynomial (Fin n) R)
      (MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R) (Fin m ⊕ Fin k) (Fin n) :=
  letI := (universalFactorizationMap R n m k hn).toAlgebra
  { val := Sum.elim (.X · ⊗ₜ 1) (1 ⊗ₜ .X ·)
    σ' f := (tensorEquivSum _ _ _ _ f).map C
    aeval_val_σ' s := by
      change ((aeval _).restrictScalars R |>.comp (mapAlgHom (Algebra.ofId _ _)) |>.comp
          (tensorEquivSum R (Fin m) (Fin k) R).toAlgHom) s = AlgHom.id R _ s
      congr 1
      ext <;> simp
    algebra := (aeval _).toAlgebra
    algebraMap_eq := rfl
    relation i := .C (.X i) - (tensorEquivSum R (Fin m) (Fin k) R
      (universalFactorizationMap R n m k hn (.X i))).map C
    span_range_relation_eq_ker := by
      exact (ker_eval₂Hom_universalFactorizationMap R n m k hn).symm,
    map := finSumFinEquiv.symm ∘ finCongr hn
    map_inj := finSumFinEquiv.symm.injective.comp (finCongr hn).injective }

lemma pderiv_inl_universalFactorizationMap_X (i j) :
    pderiv (Sum.inl i) (tensorEquivSum R (Fin m) (Fin k) R
      (universalFactorizationMap R n m k hn (X j))) =
    if ↑j < (i : ℕ) then 0 else if h : ↑j - ↑i < k then X (.inr ⟨↑j - ↑i, h⟩)
      else if ↑j - ↑i = k then 1 else 0 := by
  classical
  trans ∑ x ∈ Finset.antidiagonal ↑j,
    if h : x.2 < k then if x.1 < m ∧ x.1 = ↑i then X (Sum.inr ⟨x.2, h⟩) else 0
    else if x.2 = k ∧ x.1 < m ∧ x.1 = ↑i then 1 else 0
  · simp [universalFactorizationMap, mapEquivMonic, Polynomial.coeff_mul, coeff_freeMonic,
      apply_dite, apply_ite, ← Algebra.TensorProduct.one_def,
      Pi.single_apply, Fin.ext_iff, ← ite_and]
  · obtain h | h := lt_or_ge j.1 i.1
    · rw [Finset.sum_eq_zero, if_pos h]
      simp only [Finset.mem_antidiagonal, Prod.forall]
      intro a b hab
      simp [show a ≠ i by omega]
    rw [Finset.sum_eq_single ⟨i.1, j.1 - i.1⟩, if_neg h.not_gt]
    · simp
    · simp only [Finset.mem_antidiagonal, ne_eq, Prod.forall, Prod.mk.injEq, not_and]
      intro a b e h
      simp [show a ≠ i by omega]
    · simp [h]

lemma pderiv_inr_universalFactorizationMap_X (i j) :
    pderiv (Sum.inr i) (tensorEquivSum R (Fin m) (Fin k) R
      (universalFactorizationMap R n m k hn (X j))) =
    if ↑j < (i : ℕ) then 0 else if h : ↑j - ↑i < m then
      X (.inl ⟨↑j - ↑i, h⟩) else if ↑j - ↑i = m then 1 else 0 := by
  classical
  trans ∑ x ∈ Finset.antidiagonal ↑j, if x.2 < k then if h : x.1 < m then if x.2 = ↑i then
    X (Sum.inl ⟨x.1, h⟩) else 0 else if x.1 = m ∧ x.2 = ↑i then 1 else 0 else 0
  · simp [universalFactorizationMap, mapEquivMonic, Polynomial.coeff_mul, coeff_freeMonic,
      apply_dite, apply_ite, ← Algebra.TensorProduct.one_def,
      Pi.single_apply, Fin.ext_iff, ← ite_and]
  · obtain h | h := lt_or_ge j.1 i.1
    · rw [Finset.sum_eq_zero, if_pos h]
      simp only [Finset.mem_antidiagonal, Prod.forall]
      intro a b hab
      simp [show b ≠ i by omega]
    rw [Finset.sum_eq_single ⟨j.1 - i.1, i.1⟩, if_neg h.not_gt]
    · simp
    · simp only [Finset.mem_antidiagonal, ne_eq, ite_eq_right_iff, Prod.forall, Prod.mk.injEq]
      intro a b _ _ _
      simp [show b ≠ i by omega]
    · simp [h]

lemma universalFactorizationMapPresentation_jacobiMatrix :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    (universalFactorizationMapPresentation R n m k hn).jacobiMatrix =
    -((Polynomial.sylvester
      ((freeMonic R m).map (((mapAlgHom (Algebra.ofId _ _)).comp (rename Sum.inl)).toRingHom))
      ((freeMonic R k).map (((mapAlgHom (Algebra.ofId _ _)).comp (rename Sum.inr)).toRingHom))
      m k).reindex (finCongr (by omega)) (finCongr (by omega))).transpose := by
  letI := (universalFactorizationMap R n m k hn).toAlgebra
  subst hn
  ext i j : 1
  dsimp [Polynomial.sylvester]
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;>
    induction j using Fin.addCases <;>
      simp [pderiv_map, coeff_freeMonic, apply_dite (DFunLike.coe _), apply_ite (DFunLike.coe _),
        pderiv_inl_universalFactorizationMap_X, pderiv_inr_universalFactorizationMap_X] <;> grind

lemma universalFactorizationMapPresentation_jacobian :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    (universalFactorizationMapPresentation R n m k hn).jacobian =
    (-1) ^ n * (Polynomial.resultant
      ((freeMonic R m).map Algebra.TensorProduct.includeLeftRingHom)
      ((freeMonic R k).map Algebra.TensorProduct.includeRight.toRingHom)) := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  letI := (universalFactorizationMap R n m k hn).toAlgebra
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    MvPolynomial.universalFactorizationMapPresentation_jacobiMatrix]
  simp only [AlgHom.toRingHom_eq_coe, Matrix.det_neg, Matrix.det_transpose, Matrix.det_reindex_self,
    Algebra.Generators.algebraMap_apply, ← Polynomial.resultant.eq_def,
    Fintype.card_fin, map_mul, map_pow, map_neg, map_one]
  congr 1
  rw [← (aeval _).coe_toRingHom, ← Polynomial.resultant_map_map,
    Polynomial.map_map, Polynomial.map_map]
  congr 2
  · ext <;> simp [- algebraMap_apply, ← algebraMap_eq]
  · ext <;> simp [- algebraMap_apply, ← algebraMap_eq]
  · rw [(monic_freeMonic ..).natDegree_map, natDegree_freeMonic]
  · rw [(monic_freeMonic ..).natDegree_map, natDegree_freeMonic]

lemma finitePresentation_universalFactorizationMap :
    (universalFactorizationMap R n m k hn).FinitePresentation :=
  letI := (universalFactorizationMap R n m k hn).toAlgebra
  (universalFactorizationMapPresentation R n m k hn).finitePresentation_of_isFinite

lemma finite_universalFactorizationMap :
    (universalFactorizationMap R n m k hn).Finite := by
  refine RingHom.IsIntegral.to_finite ?_
    (.of_finitePresentation (finitePresentation_universalFactorizationMap R n m k hn))
  letI := (universalFactorizationMap R n m k hn).toAlgebra
  have : IsDomain (MvPolynomial (Fin m) ℤ ⊗[ℤ] MvPolynomial (Fin k) ℤ) :=
    (MvPolynomial.tensorEquivSum ℤ (Fin m) (Fin k) ℤ).toRingEquiv.isDomain_iff.mpr inferInstance
  letI := (universalFactorizationMap ℤ n m k hn).toAlgebra
  let F : MvPolynomial (Fin m) ℤ ⊗[ℤ] MvPolynomial (Fin k) ℤ →ₐ[ℤ]
      MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R :=
    Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft.comp (mapAlgHom (Algebra.ofId ℤ R)))
      ((Algebra.TensorProduct.includeRight.restrictScalars ℤ).comp (mapAlgHom (Algebra.ofId ℤ R)))
      fun _ _ ↦ .all _ _
  have H₁ (i : _) : (universalFactorizationMap R n m k hn).IsIntegralElem (.X i ⊗ₜ 1) := by
    obtain ⟨p, hp, hp'⟩ : (universalFactorizationMap ℤ n m k hn).IsIntegralElem (.X i ⊗ₜ 1) := by
      simpa [coeff_freeMonic] using Polynomial.isIntegral_coeff_of_dvd _ _ (monic_freeMonic _ _)
        (by simp [((monic_freeMonic _ _).map _).leadingCoeff, isIntegral_one])
        ⟨_, universalFactorizationMap_freeMonic ℤ n m k hn⟩ i
    refine ⟨p.map (MvPolynomial.map (algebraMap ℤ R)), hp.map _, ?_⟩
    apply_fun F.toRingHom at hp'
    rw [Polynomial.hom_eval₂, ← MvPolynomial.universalFactorizationMap_comp_map] at hp'
    simpa [← Polynomial.eval₂_map, F] using hp'
  have H₂ (i : _) : (universalFactorizationMap R n m k hn).IsIntegralElem (1 ⊗ₜ .X i) := by
    obtain ⟨p, hp, hp'⟩ : (universalFactorizationMap ℤ n m k hn).IsIntegralElem (1 ⊗ₜ .X i) := by
      simpa [coeff_freeMonic] using Polynomial.isIntegral_coeff_of_dvd _ _ (monic_freeMonic _ _)
        (by simp [((monic_freeMonic _ _).map _).leadingCoeff, isIntegral_one])
        ⟨_, (universalFactorizationMap_freeMonic ℤ n m k hn).trans (mul_comm _ _)⟩ i
    refine ⟨p.map (MvPolynomial.map (algebraMap ℤ R)), hp.map _, ?_⟩
    apply_fun F.toRingHom at hp'
    rw [Polynomial.hom_eval₂, ← MvPolynomial.universalFactorizationMap_comp_map] at hp'
    simpa [← Polynomial.eval₂_map, F] using hp'
  intro x
  induction x with
  | zero => exact RingHom.isIntegralElem_zero _
  | add x y _ _ => exact RingHom.IsIntegralElem.add _ ‹_› ‹_›
  | tmul x y =>
    suffices (universalFactorizationMap R n m k hn).IsIntegralElem (x ⊗ₜ 1 * 1 ⊗ₜ y) by simpa
    refine RingHom.IsIntegralElem.mul _ ?_ ?_
    · induction x using MvPolynomial.induction_on with
      | C a => simpa using (universalFactorizationMap R n m k hn).isIntegralElem_map (x := .C a)
      | add p q _ _ => simp only [TensorProduct.add_tmul, RingHom.IsIntegralElem.add, *]
      | mul_X p i IH => simpa [← map_mul] using IH.mul _ (H₁ i)
    · induction y using MvPolynomial.induction_on with
      | C a => simpa [← algebraMap_eq, ← algebraMap_apply, Algebra.algebraMap_eq_smul_one] using
          (universalFactorizationMap R n m k hn).isIntegralElem_map (x := .C a)
      | add p q _ _ => simp only [TensorProduct.tmul_add, RingHom.IsIntegralElem.add, *]
      | mul_X p i IH => simpa [← map_mul] using IH.mul _ (H₂ i)

end MvPolynomial

namespace Polynomial

open TensorProduct

variable {R n} (p : Polynomial.MonicDegreeEq R n)

attribute [-instance] leftModule in
/-- The universal factorization ring of a monic polynomial `p` of degree `n`.
This is the representing object of the functor
`S ↦ "factorizations of p into (monic deg m) * (monic deg k) in S"`.
See `UniversalFactorizationRing.homEquiv`. -/
def UniversalFactorizationRing : Type _ :=
  letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  R ⊗[MvPolynomial (Fin n) R] (MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R)
  deriving CommRing, Algebra R

local notation "𝓡" => UniversalFactorizationRing m k hn p

/-- The canonical map `R[X₁,...,Xₘ] ⊗ R[X₁,...,Xₙ] → UniversalFactorizationRing`. -/
def UniversalFactorizationRing.fromTensor :
    (MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R) →ₐ[R] 𝓡 :=
  letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  Algebra.TensorProduct.includeRight.restrictScalars _

/-- The image of `p` in the universal factorization ring of `p`. -/
@[simps] def UniversalFactorizationRing.monicDegreeEq :
    MonicDegreeEq 𝓡 n :=
  ⟨p.1.map (algebraMap _ _), by simp +contextual only [Polynomial.coeff_map, p.2,
    map_one, map_zero, gt_iff_lt, implies_true, and_self]⟩

lemma UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap :
  (fromTensor m k hn p).comp (MvPolynomial.universalFactorizationMap R n m k hn) =
    (Algebra.ofId R _).comp ((MvPolynomial.mapEquivMonic R _ n).symm p) := by
  letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  exact AlgHom.ext fun x ↦ (Algebra.TensorProduct.tmul_one_eq_one_tmul x).symm

lemma UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap' :
  (fromTensor m k hn p).comp (MvPolynomial.universalFactorizationMap R n m k hn) =
    ((MvPolynomial.mapEquivMonic _ _ n).symm (monicDegreeEq m k hn p)) := by
  rw [UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap, Equiv.eq_symm_apply]
  ext1
  simp [MvPolynomial.coe_mapEquivMonic_comp, monicDegreeEq]

/-- The first factor of `p` in the universal factorization ring of `p`. -/
def UniversalFactorizationRing.factor₁ : MonicDegreeEq 𝓡 m :=
  (MvPolynomial.universalFactorizationMapLiftEquiv _ _ n m k hn _
    ⟨fromTensor m k hn p, fromTensor_comp_universalFactorizationMap' m k hn p⟩).1.1

/-- The second factor of `p` in the universal factorization ring of `p`. -/
def UniversalFactorizationRing.factor₂ : MonicDegreeEq 𝓡 k :=
  (MvPolynomial.universalFactorizationMapLiftEquiv _ _ n m k hn _
    ⟨fromTensor m k hn p, fromTensor_comp_universalFactorizationMap' m k hn p⟩).1.2

lemma UniversalFactorizationRing.factor₁_mul_factor₂ :
    (factor₁ m k hn p).1 * (factor₂ m k hn p).1 = (monicDegreeEq m k hn p).1 :=
  (MvPolynomial.universalFactorizationMapLiftEquiv _ _ n m k hn _
    ⟨fromTensor m k hn p, fromTensor_comp_universalFactorizationMap' m k hn p⟩).2

attribute [-instance] leftModule in
/-- The universal factorization ring that represents
`S ↦ "factorizations of p into (monic deg m) * (monic deg k) in S"`. -/
def UniversalFactorizationRing.homEquiv :
    (𝓡 →ₐ[R] S) ≃ { q : MonicDegreeEq S m × MonicDegreeEq S k //
      q.1.1 * q.2.1 = p.1.map (algebraMap R S) } where
  toFun f := ⟨((factor₁ m k hn p).map f, (factor₂ m k hn p).map f), by
    simp [← Polynomial.map_mul, factor₁_mul_factor₂ m k hn p, Polynomial.map_map]⟩
  invFun q :=
    letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
    letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
    letI := Algebra.compHom S ((MvPolynomial.mapEquivMonic R _ n).symm p).toRingHom
    haveI : IsScalarTower (MvPolynomial (Fin n) R) R S := .of_algebraMap_eq' rfl
    letI f := ((MvPolynomial.universalFactorizationMapLiftEquiv R _ n m k hn
          (p.map (algebraMap R S))).symm q)
    Algebra.TensorProduct.lift (R := MvPolynomial (Fin n) R) (S := R) (A := R)
      (B := MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R) (C := S) (Algebra.ofId R S)
      { toRingHom := f.1.toRingHom
        commutes' r := congr($(f.2) r).trans
          (by simp [MvPolynomial.mapEquivMonic_symm_map_algebraMap]; rfl) } fun _ _ ↦ .all _ _
  left_inv f := by
    letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
    letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
    letI := Algebra.compHom S ((MvPolynomial.mapEquivMonic R _ n).symm p).toRingHom
    haveI : IsScalarTower (MvPolynomial (Fin n) R) R S := .of_algebraMap_eq' rfl
    have : IsScalarTower R (MvPolynomial (Fin n) R) S := .of_algebraMap_eq fun r ↦ by
      simp [Algebra.compHom_algebraMap_apply]
    refine Algebra.TensorProduct.ext (by ext) ?_
    refine AlgHom.restrictScalars_injective R (Algebra.TensorProduct.ext ?_ ?_)
    · ext; simp [MvPolynomial.universalFactorizationMapLiftEquiv, MvPolynomial.mapEquivMonic,
        UniversalFactorizationRing.factor₁, coeff_freeMonic]; rfl
    · ext; simp [MvPolynomial.universalFactorizationMapLiftEquiv, MvPolynomial.mapEquivMonic,
        UniversalFactorizationRing.factor₂, coeff_freeMonic]; rfl
  right_inv q := by
    letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
    letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
    simp only [UniversalFactorizationRing, MvPolynomial.mapEquivMonic, AlgHom.toRingHom_eq_coe,
      Equiv.coe_fn_symm_mk, MvPolynomial.coe_aeval_eq_eval, factor₁, monicDegreeEq_coe,
      MvPolynomial.universalFactorizationMapLiftEquiv, Equiv.coe_fn_mk, fromTensor,
      MonicDegreeEq.map_coe, factor₂]
    ext <;> simp +contextual [coeff_freeMonic, apply_dite, MonicDegreeEq.coeff_of_ge]

attribute [-instance] leftModule in
instance : Module.Finite R 𝓡 :=
  letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  letI : Module.Finite _ _ := MvPolynomial.finite_universalFactorizationMap R n m k hn
  inferInstanceAs (Module.Finite R (R ⊗[_] _))

attribute [-instance] leftModule in
instance : Algebra.FinitePresentation R 𝓡 :=
  letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  letI : Algebra.FinitePresentation _ _ :=
    MvPolynomial.finitePresentation_universalFactorizationMap R n m k hn
  inferInstanceAs (Algebra.FinitePresentation R (R ⊗[_] _))

end Polynomial
