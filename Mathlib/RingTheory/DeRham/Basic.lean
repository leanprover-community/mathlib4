/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Module.Presentation.Differentials
import Mathlib.Algebra.Module.Presentation.ExteriorPower
import Mathlib.Algebra.Module.Presentation.RestrictScalars
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Kaehler.Basic

/-!
# The algebraic De Rham complex

-/

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

open Function

namespace Algebra

namespace Generators

@[simps]
noncomputable def tautological : Algebra.Generators A B where
  vars := B
  val := _root_.id
  σ' := MvPolynomial.X
  aeval_val_σ' := by simp

end Generators

namespace Presentation

namespace tautological

inductive Rels
  | add (b b' : B)
  | mul (b b' : B)
  | algebraMap (a : A)

@[simp]
noncomputable def relation : Rels A B → (Generators.tautological A B).Ring
  | .add b b' => .X b + .X b' - .X (b + b')
  | .mul b b' => .X b * .X b' - .X (b * b')
  | .algebraMap a => a • 1 - .X (algebraMap A B a)

lemma le_ker : Ideal.span (Set.range (tautological.relation A B)) ≤
    (Generators.tautological A B).ker := by
  rw [Ideal.span_le]
  rintro _ ⟨(⟨b, b'⟩ | ⟨b, b'⟩ | a), rfl⟩
  · simp
  · simp
  · simp [Algebra.smul_def a (1 : B)]

@[simps]
noncomputable def toQuotient :
    B →+* (Generators.tautological A B).Ring ⧸
      Ideal.span (Set.range (tautological.relation A B)) where
  toFun b := Submodule.Quotient.mk (.X b)
  map_add' b b' := by
    dsimp
    symm
    rw [← map_add, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.subset_span ⟨.add b b', by simp⟩
  map_mul' b b' := by
    dsimp
    symm
    rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.subset_span ⟨.mul b b', by simp⟩
  map_one' := by
    dsimp
    symm
    rw [← (Ideal.Quotient.mk _).map_one, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.subset_span ⟨.algebraMap 1, by simp⟩
  map_zero' := by
    dsimp
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨.add 0 0, by simp⟩

lemma fac : (toQuotient A B).comp (algebraMap (Generators.tautological A B).Ring B) =
    Ideal.Quotient.mk _ := by
  ext x
  · symm
    erw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    refine Ideal.subset_span ⟨.algebraMap x, ?_⟩
    dsimp
    rw [MvPolynomial.algHom_C, MvPolynomial.C_eq_smul_one]
  · dsimp
    congr 1
    simp [Algebra.Generators.algebraMap_eq]

end tautological

@[simps!]
noncomputable def tautological : Algebra.Presentation A B where
  toGenerators := .tautological A B
  rels := tautological.Rels A B
  relation := tautological.relation A B
  span_range_relation_eq_ker := le_antisymm (tautological.le_ker A B) (by
    rintro x hx
    simp only [Generators.tautological_vars, RingHom.mem_ker] at hx
    have := (DFunLike.congr_fun (tautological.fac A B) x).symm
    simpa only [RingHom.coe_comp, comp_apply, hx, map_zero, Ideal.Quotient.eq_zero_iff_mem]
      using (DFunLike.congr_fun (tautological.fac A B) x).symm)

end Presentation

end Algebra

open ExteriorAlgebra

@[simps! G R var]
noncomputable abbrev KaehlerDifferential.presentation :
    Module.Presentation B (KaehlerDifferential A B) :=
  Algebra.Presentation.differentials (Algebra.Presentation.tautological A B)

namespace DeRhamComplex

variable {n : ℕ}

section

variable {α : Type*} (x : α) (f : Fin n → α)

def finInsert : Fin (n + 1) → α
  | ⟨0, _⟩ => x
  | ⟨n + 1, _⟩ => f ⟨n, by omega⟩

@[simp]
lemma finInsert_zero : finInsert x f 0 = x := rfl

@[simp]
lemma finInsert_succ (i : Fin n) : finInsert x f i.succ = f i := rfl

lemma comp_finInsert {β : Type*} (g : α → β) :
    g.comp (finInsert x f) = finInsert (g x) (g.comp f) := by
  ext ⟨(_ | _), _⟩ <;> rfl

lemma finInsert_eq_update_finInsert_zero [Zero α]:
    finInsert x f = update (finInsert 0 f) 0 x := by
  ext ⟨(_ | _), _⟩ <;> rfl

lemma finInsert_update (i : Fin n) (a : α) :
    finInsert x (update f i a) = update (finInsert x f) i.succ a := by
  ext j
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ j
  · rfl
  · by_cases h : j = i
    · subst h
      simp only [finInsert_succ, update_same]
    · rw [update_noteq (by simpa using h), finInsert_succ, finInsert_succ,
        update_noteq (by simpa using h)]

lemma finInsert_swapValues (i j : Fin n) :
    finInsert x (swapValues f i j) =
      swapValues (finInsert x f) i.succ j.succ := by
  simp only [swapValues_eq_update_update, finInsert_update, finInsert_succ]

lemma _root_.Fin.eq_zero_or_succ {n : ℕ} (i : Fin (n + 1)) :
    i = 0 ∨ ∃ (j : Fin n), i = j.succ := by exact Fin.eq_zero_or_eq_succ i

lemma swapValues_finInsert_embedding (i : Fin n)
    (g : ((Set.singleton i)ᶜ : Set (Fin n)) → α) (x y : α) :
    swapValues (finInsert y (embedding (G := fun (_ : Fin n) ↦ α) i g x)) 0 i.succ =
      finInsert x (embedding (G := fun (_ : Fin n) ↦ α) i g y) := by
  ext j
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ j
  · simp only [swapValues_fst, finInsert_succ, embedding_apply_self, finInsert_zero]
  · simp only [finInsert_succ]
    by_cases h : j = i
    · subst h
      simp only [swapValues_snd, finInsert_zero, embedding_apply_self]
    · rw [embedding_apply_of_neq _ _ _ _ _ h, swapValues_apply _ _ _ _
          (by simp [Fin.ext_iff]) (by simpa using h),
        finInsert_succ, embedding_apply_of_neq _ _ _ _ _ h]

end

variable (n)

@[simps! G R relation]
noncomputable def presentationDifferentialsUp :
    Module.Presentation B (exteriorPower B n (KaehlerDifferential A B)) :=
  (KaehlerDifferential.presentation A B).exteriorPower n

@[simp]
lemma presentationDifferentialsUp_var {n : ℕ} (g : Fin n → B) :
    ((presentationDifferentialsUp A B n).var g) =
      exteriorPower.ιMulti _ _ (KaehlerDifferential.D A B ∘ g) := by
  dsimp [presentationDifferentialsUp]
  congr
  aesop

lemma presentationDifferentialsUp_relation_alternate
    (g : Fin n → B) (i j : Fin n) (hg : g i = g j) (hij : i ≠ j):
    (presentationDifferentialsUp A B n).relation
    (Module.Relations.exteriorPower.Rels.alternate g i j hg hij) =
      Finsupp.single g 1 := by
  dsimp

open Classical in
@[simps!]
noncomputable def differentialsRestrictScalarsData :
    (presentationDifferentialsUp A B n).RestrictScalarsData
      (Module.Presentation.tautological A B) where
  lift r := match r with
    | ⟨b₀, .piTensor i₀ (.add b₁ b₂) g⟩ =>
        Finsupp.single ⟨embedding (G := fun _ ↦ B) i₀
          (fun j ↦ g j j.2) b₁, b₀⟩ 1 +
          Finsupp.single ⟨embedding (G := fun _ ↦ B) i₀
            (fun j ↦ g j j.2) b₂, b₀⟩ 1 -
          Finsupp.single ⟨embedding (G := fun _ ↦ B) i₀
            (fun j ↦ g j j.2) (b₁ + b₂), b₀⟩ 1
    | ⟨(b₀ : B), .piTensor i₀ (.mul (b₁ : B) (b₂ : B)) g⟩ =>
        Finsupp.single ⟨embedding (G := fun _ ↦ B) i₀
          (fun j ↦ g j j.2) b₂, b₀ * b₁⟩ 1 +
          Finsupp.single ⟨embedding (G := fun _ ↦ B) i₀
            (fun j ↦ g j j.2) b₁, b₀ * b₂⟩ 1 -
          Finsupp.single ⟨embedding (G := fun _ ↦ B) i₀
            (fun j ↦ g j j.2) (b₁ * b₂), b₀⟩ 1
    | ⟨b₀, .piTensor i₀ (.algebraMap a) g⟩ =>
        -Finsupp.single ⟨embedding (G := fun _ ↦ B) i₀ (fun j ↦ g j j.2)
          (algebraMap A B a), b₀⟩  1
    | ⟨b₀, .alternate g _ _ _ _⟩ => Finsupp.single ⟨g, b₀⟩ 1
    | ⟨b₀, .antisymmetry g i j _⟩ =>
        Finsupp.single ⟨swapValues g i j, b₀⟩ 1 + Finsupp.single ⟨g, b₀⟩ 1
  π_lift r := match r with
    | ⟨b₀, .piTensor i₀ (.add b₁ b₂) g⟩ => by
        dsimp
        simp only [map_sub, map_add, map_smul]
        erw [Module.Presentation.finsupp_π, Module.Presentation.finsupp_π,
          Module.Presentation.finsupp_π, Module.Relations.map_single]
        dsimp [KaehlerDifferential.presentation, Algebra.Presentation.tautological,
          Algebra.Presentation.differentials]
        simp only [map_sub, map_add, KaehlerDifferential.mvPolynomialBasis_repr_D_X]
        rw [Finsupp.mapRange_sub (by simp), Finsupp.mapRange_add (by simp)]
        simp only [Finsupp.mapRange_single, Algebra.Generators.algebraMap_apply, map_one,
          Finsupp.embDomain_sub, Finsupp.embDomain_add, Finsupp.embDomain_single, smul_sub,
          smul_add, Finsupp.smul_single, smul_eq_mul, mul_one]
    | ⟨b₀, .piTensor i₀ (.mul b₁ b₂) g⟩ => by
        dsimp
        simp only [map_sub, map_add, map_smul]
        erw [Module.Presentation.finsupp_π, Module.Presentation.finsupp_π,
          Module.Presentation.finsupp_π, Module.Relations.map_single]
        dsimp [KaehlerDifferential.presentation, Algebra.Presentation.tautological,
          Algebra.Generators.tautological, Algebra.Presentation.differentials]
        simp only [map_sub, Derivation.leibniz, map_add, map_smul,
          KaehlerDifferential.mvPolynomialBasis_repr_D_X]
        rw [Finsupp.mapRange_sub (by simp), Finsupp.mapRange_add (by simp)]
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.mapRange_single,
          Algebra.Generators.algebraMap_apply, MvPolynomial.aeval_X, id_eq, map_one,
          Finsupp.embDomain_sub, Finsupp.embDomain_add, Finsupp.embDomain_single, smul_sub,
          smul_add]
    | ⟨b₀, .piTensor i₀ (.algebraMap a) g⟩ => by
        dsimp
        rw [map_neg]
        erw [Module.Presentation.finsupp_π]
        rw [map_smul]
        erw [Module.Relations.map_single]
        dsimp [KaehlerDifferential.presentation, Algebra.Presentation.tautological,
          Algebra.Presentation.differentials]
        simp only [map_sub, Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero, zero_sub,
          map_neg, KaehlerDifferential.mvPolynomialBasis_repr_D_X]
        rw [Finsupp.mapRange_neg (by simp)]
        simp only [Finsupp.mapRange_single, Algebra.Generators.algebraMap_apply, map_one,
          Finsupp.embDomain_neg, Finsupp.embDomain_single, smul_neg, Finsupp.smul_single,
          smul_eq_mul, mul_one]
    | ⟨b₀, .antisymmetry g i j hg⟩ => by
        dsimp
        rw [map_add, map_smul]
        erw [Module.Presentation.finsupp_π, Module.Presentation.finsupp_π,
          Module.Relations.map_single]
        dsimp
        simp only [smul_add, Finsupp.smul_single, smul_eq_mul, mul_one]
    | ⟨b₀, .alternate g i j hg hij⟩ => by
        dsimp
        rw [map_smul]
        erw [Module.Presentation.finsupp_π, Module.Relations.map_single]
        dsimp
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]

open Classical in
@[simps! G R relation]
noncomputable def presentationDifferentialsDown :
    Module.Presentation A (exteriorPower B n (KaehlerDifferential A B)) :=
  (presentationDifferentialsUp A B n).restrictScalars
    (Module.Presentation.tautological A B) (differentialsRestrictScalarsData A B n)

lemma presentationDifferentialsDown_var (b₀ : B) {n : ℕ} (g : Fin n → B) :
    ((presentationDifferentialsDown A B n).var ⟨g, b₀⟩) =
      b₀ • exteriorPower.ιMulti _ _ (KaehlerDifferential.D A B ∘ g) := by
  dsimp [presentationDifferentialsDown, Module.Presentation.restrictScalars,
    Module.Presentation.ofExact]
  simp only [Module.Presentation.finsupp_var, Module.Presentation.tautological_var]
  erw [Module.Relations.Solution.π_single']
  rw [presentationDifferentialsUp_var]

lemma smul_def (M : Type*) [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] (m : M) (a : A) : a • m = (algebraMap A B a) • m := by
  exact algebra_compatible_smul B a m

noncomputable def d (n : ℕ) : exteriorPower B n (KaehlerDifferential A B) →ₗ[A]
    exteriorPower B (n + 1) (KaehlerDifferential A B) :=
  (presentationDifferentialsDown A B n).desc
    { var := fun ⟨g, b₀⟩ ↦
        ((presentationDifferentialsDown A B (n + 1)).var ⟨finInsert b₀ g, (1 : B)⟩)
      linearCombination_var_relation := by
        rintro (⟨g, r⟩ | ⟨b₀, r⟩)
        · induction r with
          | add b₁ b₂ =>
              dsimp
              simp only [presentationDifferentialsDown_relation,
                Finsupp.linearCombination_embDomain, map_sub, map_add,
                Finsupp.linearCombination_single, Function.comp_apply,
                Function.Embedding.sigmaMk_apply, one_smul]
              rw [presentationDifferentialsDown_var,
                presentationDifferentialsDown_var,
                presentationDifferentialsDown_var]
              simp only [comp_finInsert, one_smul, map_add, sub_eq_zero]
              rw [finInsert_eq_update_finInsert_zero]
              nth_rw 2 [finInsert_eq_update_finInsert_zero]
              nth_rw 3 [finInsert_eq_update_finInsert_zero]
              rw [AlternatingMap.map_update_add]
          | smul a b =>
              dsimp
              simp only [presentationDifferentialsDown_relation,
                Finsupp.linearCombination_embDomain, map_sub, Finsupp.linearCombination_single,
                Function.comp_apply, Function.Embedding.sigmaMk_apply, one_smul]
              rw [presentationDifferentialsDown_var,
                presentationDifferentialsDown_var]
              simp only [one_smul, comp_finInsert, Derivation.map_smul, sub_eq_zero]
              rw [finInsert_eq_update_finInsert_zero]
              nth_rw 2 [finInsert_eq_update_finInsert_zero]
              rw [algebra_compatible_smul B a, algebra_compatible_smul B a,
                AlternatingMap.map_update_smul]
        · dsimp at b₀
          induction r with
          | piTensor i r g =>
              induction r with
              | add b₁ b₂ =>
                  dsimp
                  simp only [presentationDifferentialsDown_relation, map_sub, map_add,
                    Finsupp.linearCombination_single, one_smul, sub_eq_zero]
                  rw [presentationDifferentialsDown_var, one_smul,
                    presentationDifferentialsDown_var, one_smul,
                    presentationDifferentialsDown_var, one_smul]
                  simp only [comp_finInsert, comp_embedding, map_add]
                  rw [embedding_eq_update_embedding_zero]
                  nth_rw 2 [embedding_eq_update_embedding_zero]
                  nth_rw 3 [embedding_eq_update_embedding_zero]
                  simp only [finInsert_update, AlternatingMap.map_update_add]
              | mul b₁ b₂ =>
                  dsimp
                  simp only [presentationDifferentialsDown_relation, map_sub, map_add,
                    Finsupp.linearCombination_single, one_smul, sub_eq_zero]
                  rw [presentationDifferentialsDown_var, one_smul,
                    presentationDifferentialsDown_var, one_smul,
                    presentationDifferentialsDown_var, one_smul]
                  simp only [comp_finInsert, comp_embedding]
                  conv_rhs =>
                    rw [Derivation.leibniz, embedding_eq_update_embedding_zero,
                      finInsert_update, AlternatingMap.map_update_add,
                      AlternatingMap.map_update_smul, AlternatingMap.map_update_smul,
                      ← finInsert_update, ← finInsert_update,
                      ← embedding_eq_update_embedding_zero,
                      ← embedding_eq_update_embedding_zero]
                  rw [finInsert_eq_update_finInsert_zero]
                  nth_rw 2 [finInsert_eq_update_finInsert_zero]
                  conv_lhs =>
                    rw [Derivation.leibniz, AlternatingMap.map_update_add,
                      AlternatingMap.map_update_smul, AlternatingMap.map_update_smul,
                      ← finInsert_eq_update_finInsert_zero]
                    rw [Derivation.leibniz, AlternatingMap.map_update_add,
                      AlternatingMap.map_update_smul, AlternatingMap.map_update_smul,
                      ← finInsert_eq_update_finInsert_zero,
                      ← finInsert_eq_update_finInsert_zero,
                      ← finInsert_eq_update_finInsert_zero]
                  have : ∀ (x₁ x₂ x₃ x₄ : (⋀[B]^(n + 1) (Ω[B⁄A]))),
                      x₁ = -x₃ → x₁ + x₂ + (x₃ + x₄) = x₂ + x₄ := by
                    rintro x₁ x₂ x₃ x₄ rfl; abel
                  apply this
                  rw [← smul_neg]
                  congr
                  rw [← AlternatingMap.antisymmetry _ _ 0 i.succ (by simp [Fin.ext_iff]),
                    swapValues_finInsert_embedding]
              | algebraMap a =>
                  dsimp
                  simp only [presentationDifferentialsDown_relation, map_neg,
                    Finsupp.linearCombination_single, one_smul, neg_eq_zero]
                  rw [presentationDifferentialsDown_var, one_smul]
                  apply MultilinearMap.map_of_eq_zero _ _ i.succ (by simp)
          | antisymmetry g i j hij =>
              dsimp
              simp only [presentationDifferentialsDown_relation, map_add,
                Finsupp.linearCombination_single, one_smul]
              rw [presentationDifferentialsDown_var, one_smul, comp_finInsert,
                presentationDifferentialsDown_var, one_smul, comp_finInsert]
              rw [← comp_finInsert, finInsert_swapValues,
                ← Function.swapValues_comp, ← comp_finInsert,
                AlternatingMap.antisymmetry _ _ _ _ (by simpa using hij), neg_add_cancel]
          | alternate g i j hg hij =>
              dsimp
              simp only [presentationDifferentialsDown_relation, Finsupp.linearCombination_single,
                one_smul]
              rw [presentationDifferentialsDown_var, one_smul, comp_finInsert]
              apply AlternatingMap.map_eq_zero_of_eq (i := i.succ) (j := j.succ)
              · simp [hg]
              · simpa using hij }

@[simp]
lemma d_apply (b₀ : B) {n : ℕ} (g : Fin n → B) :
    d A B n ((presentationDifferentialsDown A B n).var ⟨g, b₀⟩) =
      ((presentationDifferentialsDown A B (n + 1)).var ⟨finInsert b₀ g, (1 : B)⟩) := by
  apply (presentationDifferentialsDown A B n).desc_var

@[simp]
lemma d_d (n : ℕ) : d A B (n + 1) ∘ₗ d A B n = 0 := by
  apply (presentationDifferentialsDown A B n).postcomp_injective
  ext ⟨g, b₀⟩
  dsimp
  rw [d_apply, d_apply, presentationDifferentialsDown_var, one_smul]
  exact MultilinearMap.map_of_eq_zero _ _ 0 (by simp)

@[simp]
lemma d_d_apply {n : ℕ} (x) : d A B (n + 1) (d A B n x) = 0 := DFunLike.congr_fun (d_d A B n) x

end DeRhamComplex

noncomputable def deRhamComplex : CochainComplex (ModuleCat A) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of A (exteriorPower B n (KaehlerDifferential A B)))
    (DeRhamComplex.d A B) (fun _ ↦ DeRhamComplex.d_d _ _ _)
