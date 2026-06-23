/-
Copyright (c) 2026 Nailin Guan, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jingting Wang
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.RingTheory.KoszulComplex.Complex
public import Mathlib.RingTheory.KoszulComplex.Cocomplex

/-!
# Homotopy on Koszul complex
-/

@[expose] public section

universe u v

open ExteriorAlgebra CategoryTheory

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  (φ : M →ₗ[R] R) (x : M)

section homotopy

lemma contraction_wedge_zero_degree
    (x : M) (φ : M →ₗ[R] R) :
    (koszulComplexAux φ 0).comp (koszulCocomplexAux R M x 0) = (φ x) • LinearMap.id := by
  -- Degree `0` has only the empty wedge generator, so the scalar term is the whole answer.
  apply exteriorPower.linearMap_ext
  ext v
  have hwedge : koszulCocomplexAux R M x 0 ((exteriorPower.ιMulti R 0) v) =
      exteriorPower.ιMulti R 1 (Matrix.vecCons x v) := by
    apply Subtype.ext
    simp [koszulCocomplexAux, exteriorPower.oneEquiv_symm_apply, GradedAlgebra.linearGMul_eq_mul,
      exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]
  simp only [LinearMap.smul_compAlternatingMap, AlternatingMap.smul_apply,
    LinearMap.compAlternatingMap_apply, LinearMap.id_apply, LinearMap.comp_apply, koszulComplexAux]
  rw  [hwedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  simp [koszulComplexAuxAlternating, AlternatingMap.alternatizeUncurryFin_apply]

lemma contraction_wedge_cartan_formula (x : M) (φ : M →ₗ[R] R) (n : ℕ) :
    (koszulCocomplexAux R M x n).comp (koszulComplexAux φ n) +
      (koszulComplexAux φ (n + 1)).comp (koszulCocomplexAux R M x (n + 1)) =
        (φ x) • LinearMap.id := by
  -- Compare the two operators on the standard exterior-power generators `ιMulti`.
  apply exteriorPower.linearMap_ext
  ext v
  -- After expanding contraction on `x ∧ v`, the terms cancel pairwise except for `φ x`.
  simp only [LinearMap.add_compAlternatingMap, LinearMap.smul_compAlternatingMap,
    AlternatingMap.add_apply, AlternatingMap.smul_apply, LinearMap.compAlternatingMap_apply,
    LinearMap.id_apply, koszulComplexAux]
  have hwedge : koszulCocomplexAux R M x (n + 1) ((exteriorPower.ιMulti R (n + 1)) v) =
      exteriorPower.ιMulti R (n + 2) (Matrix.vecCons x v) := by
    apply Subtype.ext
    simp [koszulCocomplexAux, exteriorPower.oneEquiv_symm_apply, GradedAlgebra.linearGMul_eq_mul,
      exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, hwedge,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rw [koszulComplexAuxAlternating, AlternatingMap.alternatizeUncurryFin_apply,
      koszulComplexAuxAlternating, AlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ,
      Fin.sum_univ_succ]
  -- Rewrite the removed tuples so both Leibniz expansions are indexed the same way.
  have hremove (i : Fin (n + 1)) :
      i.succ.removeNth (Matrix.vecCons x v) = Matrix.vecCons x (i.removeNth v) := by
    ext j
    exact Fin.cases (by simp [Fin.removeNth]) (fun j ↦ (by simp [Fin.removeNth])) j
  simp only [koszulCocomplexAux, exteriorPower.oneEquiv_symm_apply, Int.reduceNeg,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, LinearMap.coe_smulRight, Fin.removeNth_zero,
    AlternatingMap.smul_apply, one_smul, Fin.val_succ, pow_succ, mul_comm, neg_mul, one_mul,
    neg_smul, Finset.sum_neg_distrib, map_add, map_smul, map_neg, map_sum,
    LinearMap.map_smul_of_tower, Matrix.cons_val_zero, Fin.tail_vecCons, Matrix.cons_val_succ,
    hremove, Submodule.coe_add, SetLike.val_smul, GradedAlgebra.linearGMul_eq_mul,
    exteriorPower.ιMulti_apply_coe, ιMulti_succ_apply, ιMulti_zero_apply, mul_one,
    NegMemClass.coe_neg, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul_of_tower, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, Algebra.mul_smul_comm, Matrix.tail_cons,
    Fin.sum_univ_succ, neg_add_rev, neg_neg]
  abel

lemma koszulCocomplex.scalar_homotopy_comm_zero (x : M) (φ : M →ₗ[R] R) :
    (((φ x) • (𝟙 (koszulCocomplex R x))).f 0) =
      dNext 0 (fun i j => if h : j + 1 = i then h ▸ ModuleCat.ofHom (koszulComplexAux φ j) else 0) +
        prevD 0
          (fun i j => if h : j + 1 = i then h ▸ ModuleCat.ofHom (koszulComplexAux φ j) else 0) := by
  -- In degree `0`, only the `δ_φ d_x` term survives.
  rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex]
  simp only [↓reduceDIte, HomologicalComplex.smul_f_apply, HomologicalComplex.id_f, Nat.reduceAdd,
    koszulCocomplex.d_eq_aux, zero_add, add_zero]
  exact congrArg ModuleCat.ofHom (contraction_wedge_zero_degree (R := R) x φ).symm

lemma koszulComplex.scalar_homotopy_comm_zero (x : M) (φ : M →ₗ[R] R) :
    (((φ x) • 𝟙 (koszulComplex φ)).f 0) =
      dNext 0
        (fun i j => if h : i + 1 = j then h ▸ ModuleCat.ofHom (koszulCocomplexAux R M x i) else 0) +
        prevD 0
          (fun i j =>
            if h : i + 1 = j then h ▸ ModuleCat.ofHom (koszulCocomplexAux R M x i) else 0) := by
  -- In degree `0`, only the `d_x δ_φ` term survives.
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
  simp only [↓reduceDIte, koszulComplex.d_eq_aux, zero_add, HomologicalComplex.smul_f_apply,
    HomologicalComplex.id_f, Nat.reduceAdd]
  exact congrArg ModuleCat.ofHom (contraction_wedge_zero_degree (R := R) x φ).symm

lemma koszulCocomplex.scalar_homotopy_comm (x : M) (φ : M →ₗ[R] R) (i : ℕ) :
    (((φ x) • 𝟙 (koszulCocomplex R x)).f (i + 1)) =
      dNext (i + 1)
          (fun i j => if h : j + 1 = i then h ▸ ModuleCat.ofHom (koszulComplexAux φ j) else 0) +
        prevD (i + 1)
          (fun i j => if h : j + 1 = i then h ▸ ModuleCat.ofHom (koszulComplexAux φ j) else 0) := by
  -- In positive degrees, the homotopy relation is exactly the Cartan formula.
  rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex]
  simp only [↓reduceDIte, HomologicalComplex.smul_f_apply, HomologicalComplex.id_f, d_eq_aux]
  let A := (koszulCocomplexAux R M x i).comp (koszulComplexAux φ i)
  let B := (koszulComplexAux φ (i + 1)).comp (koszulCocomplexAux R M x (i + 1))
  have hcartan : (φ x) • LinearMap.id = B + A := by
    simpa [A, B, ← add_comm A B] using (contraction_wedge_cartan_formula (R := R) x φ i).symm
  exact congrArg ModuleCat.ofHom hcartan

lemma koszulComplex.scalar_homotopy_comm (x : M) (φ : M →ₗ[R] R) (i : ℕ) :
    (((φ x) • 𝟙 (koszulComplex φ)).f (i + 1)) =
      dNext (i + 1)
          (fun i j =>
            if h : i + 1 = j then h ▸ ModuleCat.ofHom (koszulCocomplexAux R M x i) else 0) +
        prevD (i + 1)
          (fun i j =>
            if h : i + 1 = j then h ▸ ModuleCat.ofHom (koszulCocomplexAux R M x i) else 0) := by
  -- In positive degrees, the homotopy relation is exactly the Cartan formula.
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
  simp only [↓reduceDIte, koszulComplex.d_eq_aux, HomologicalComplex.smul_f_apply,
    HomologicalComplex.id_f]
  exact congrArg ModuleCat.ofHom (contraction_wedge_cartan_formula x φ i).symm

noncomputable def koszulCocomplex.homotopySMulIdZero (x : M) (φ : M →ₗ[R] R) :
    Homotopy ((φ x) • 𝟙 (koszulCocomplex R x))
      (0 : koszulCocomplex R x ⟶ koszulCocomplex R x) where
  hom := fun i j =>
    if h : j + 1 = i then h ▸ ModuleCat.ofHom (koszulComplexAux φ j) else 0
  zero i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    simp [hij]
  comm i := by
    cases i with
    | zero => simpa using! scalar_homotopy_comm_zero x φ
    | succ i => simpa using! koszulCocomplex.scalar_homotopy_comm x φ i

noncomputable def koszulComplex.homotopySMulIdZero (x : M) (φ : M →ₗ[R] R) :
    Homotopy ((φ x) • 𝟙 (koszulComplex φ)) (0 : koszulComplex φ ⟶ koszulComplex φ) where
  hom := fun i j =>
    if h : i + 1 = j then h ▸ ModuleCat.ofHom (koszulCocomplexAux R M x i) else 0
  zero i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    simp [hij]
  comm i := by
    cases i with
    | zero => simpa using! scalar_homotopy_comm_zero (R := R) x φ
    | succ i => simpa using! scalar_homotopy_comm (R := R) x φ i

end homotopy

section homology_annihilator

set_option backward.isDefEq.respectTransparency false in
lemma koszulComplex.mem_annihilator_homology (i : ℕ) :
    φ x ∈ Module.annihilator R ((koszulComplex φ).homology i) := by
  rw [Module.mem_annihilator]
  intro z
  have ofht : (HomologicalComplex.homologyMap (φ x • 𝟙 (koszulComplex φ)) i).hom z = 0 := by
    simp [(homotopySMulIdZero x φ).homologyMap_eq i]
  have : (ShortComplex.homologyMap (φ x • ((HomologicalComplex.shortComplexFunctor _ _ i).map
      (𝟙 (koszulComplex φ))))).hom z = φ x • z := by simp
  exact this.symm.trans ofht

lemma koszulComplex.range_le_annihilator_homology (i : ℕ) :
    φ.range ≤ Module.annihilator R ((koszulComplex φ).homology i) := by
  rintro _ ⟨x, rfl⟩
  exact mem_annihilator_homology φ x i

lemma koszulComplex.ofList_ideal_annihilator_homology (l : List R) (i : ℕ) :
    Ideal.ofList l ≤ Module.annihilator R ((ofList l).homology i) :=
  le_of_eq_of_le (by simp) (range_le_annihilator_homology (Fintype.linearCombination R l.get) i)

set_option backward.isDefEq.respectTransparency false in
lemma koszulCocomplex.mem_annihilator_homology (i : ℕ) :
    φ x ∈ Module.annihilator R ((koszulCocomplex R x).homology i) := by
  rw [Module.mem_annihilator]
  intro z
  have ofht : (HomologicalComplex.homologyMap (φ x • 𝟙 (koszulCocomplex R x)) i).hom z = 0 := by
    simp [(homotopySMulIdZero x φ).homologyMap_eq i]
  have : (ShortComplex.homologyMap (φ x • ((HomologicalComplex.shortComplexFunctor _ _ i).map
      (𝟙 (koszulCocomplex R x))))).hom z = φ x • z := by simp
  exact this.symm.trans ofht

lemma koszulCocomplex.ofList_ideal_le_mem_annihilator_homology (l : List R) (i : ℕ) :
    Ideal.ofList l ≤ Module.annihilator R ((koszulCocomplex.ofList R l).homology i) := by
  intro r hr
  have hr' : r ∈ Ideal.span (Set.range l.get) := by simpa only [Set.range_list_get l]
  rcases (Ideal.mem_span_range_iff_exists_fun (R := R) (x := r) (v := l.get)).1 hr' with ⟨c, hc⟩
  let φ : (Fin l.length → R) →ₗ[R] R := Fintype.linearCombination R c
  have hφ : φ l.get = r := by
    simp only [φ, ← hc, Fintype.linearCombination_apply, mul_comm (c _), smul_eq_mul]
  exact hφ ▸ mem_annihilator_homology φ l.get i

end homology_annihilator
