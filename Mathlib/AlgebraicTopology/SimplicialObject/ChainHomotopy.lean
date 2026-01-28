/-
Copyright (c) 2025 Fabian Odermatt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Odermatt
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.SimplicialHomotopy
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Simplicial homotopies induce chain homotopies

Given a simplicial homotopy between morphisms of simplicial objects in a preadditive category,
we construct a chain homotopy between the induced morphisms on the alternating face map complexes.

Concretely, if `H : SimplicialHomotopy f g` gives maps
`H.h i : X _⦋n⦌ ⟶ Y _⦋n+1⦌` indexed by `i : Fin (n+1)`, we define the degree-`n` component
of the chain homotopy as the alternating sum `∑ i, (-1)^i • H.h i`.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.SimplicialObject
open SimplexCategory Simplicial Opposite AlgebraicTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X Y : SimplicialObject C} {f g : X ⟶ Y}

namespace SimplicialHomotopy

/-- The degree-`n` component of the chain homotopy associated to a simplicial homotopy.

This is the alternating sum `H_n = ∑ i : Fin (n+1), (-1)^i • H.h i`.
-/
def chainHomotopyComponent (H : SimplicialHomotopy f g) (n : ℕ) :
    X _⦋n⦌ ⟶ Y _⦋n+1⦌ := ∑ i : Fin (n+1), ( (-1 : ℤ) ^ (i : ℕ) : ℤ ) • H.h i

/-- The family of components of the induced chain homotopy -/
noncomputable def hom (H : SimplicialHomotopy f g) : ∀ i j : ℕ,
    ((alternatingFaceMapComplex C).obj X).X i ⟶ ((alternatingFaceMapComplex C).obj Y).X j :=
  fun i j =>
    if h : j = i + 1 then by
      subst h
      exact H.chainHomotopyComponent i
    else 0

private lemma comm_zero_form (H : SimplicialHomotopy f g) :
    ((alternatingFaceMapComplex C).map g).f 0 =
    prevD 0 H.hom + ((alternatingFaceMapComplex C).map f).f 0 := by
  dsimp [prevD, hom, chainHomotopyComponent]
  have h_prev : (ComplexShape.down ℕ).prev 0 = 1 := by simp [(ChainComplex.prev (α := ℕ) 0)]
  have h_last := H.h_last_comp_δ_last 0
  dsimp at h_last
  rw [h_prev]
  simp only [↓reduceDIte, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Int.reduceNeg,
    Fin.val_eq_zero, pow_zero, one_smul, Finset.sum_singleton, alternatingFaceMapComplex_obj_d,
    AlternatingFaceMapComplex.objD, Nat.reduceAdd, Fin.sum_univ_two, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, Nat.mod_succ, pow_one, neg_smul, Preadditive.comp_add, H.h_zero_comp_δ_zero 0,
    Preadditive.comp_neg, h_last, neg_add_cancel_right]

private lemma comm_succ_form (H : SimplicialHomotopy f g) (n : ℕ) :
    ((alternatingFaceMapComplex C).map g).f (n + 1) = dNext (n + 1) H.hom + prevD (n + 1) H.hom +
      ((alternatingFaceMapComplex C).map f).f (n + 1) := by
  dsimp [dNext, prevD, hom, chainHomotopyComponent]
  rw [(show (ComplexShape.down ℕ).next (n + 1) = n by
      simp only [ChainComplex.next_nat_succ]),
      (show (ComplexShape.down ℕ).prev (n + 1) = n + 2 by
      simp only [ChainComplex.prev, Nat.reduceEqDiff])]
  simp only [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD,
    Int.reduceNeg, ↓reduceDIte]
  refine (sub_eq_iff_eq_add).1 ?_
  rw [sub_eq_add_neg]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, ← Finset.sum_product']
  simp only [Finset.univ_product_univ, Int.reduceNeg, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, smul_smul]
  -- We partition indices (j,i) based on whether i ≤ j to separate terms that behave differently
  let P := (Fin (n + 1) × Fin (n + 2))
  let S : Finset P := {x : P | (x.2 : ℕ) ≤ (x.1 : ℕ)}
  let Q := Fin (n + 3) × Fin (n + 2)
  let t : Q → (X _⦋n+1⦌ ⟶ Y _⦋n+1⦌) :=
    fun x => ((-1) ^ (x.1 : ℕ) * (-1) ^ (x.2 : ℕ)) • (H.h x.2 ≫ Y.δ x.1)
  let U : Finset Q :=
    (Finset.univ.image (fun b : Fin (n + 2) => (b.castSucc, b))) ∪
    (Finset.univ.image (fun b : Fin (n + 2) => (b.succ, b)))
  let φS  : P → Q := fun ⟨j,i⟩ => (i.castSucc, j.succ)
  let φSc : P → Q := fun ⟨j,i⟩ => (i.succ, j.castSucc)
  let U1 : Finset Q := (S.image φS)
  let U2 : Finset Q := (Sᶜ.image φSc)
  set SumQ : (X _⦋n+1⦌ ⟶ Y _⦋n+1⦌) := ∑ x : Q, t x
  set Sum1 : (X _⦋n+1⦌ ⟶ Y _⦋n+1⦌) :=
    ∑ i ∈ S, ((-1) ^ (i.1 : ℕ) * (-1) ^ (i.2 : ℕ)) • X.δ i.2 ≫ H.h i.1
  set Sum2 : (X _⦋n+1⦌ ⟶ Y _⦋n+1⦌) :=
    ∑ i ∈ Sᶜ, ((-1) ^ (i.1 : ℕ) * (-1) ^ (i.2 : ℕ)) • X.δ i.2 ≫ H.h i.1
  set Sum3 : (X _⦋n+1⦌ ⟶ Y _⦋n+1⦌) := ∑ x ∈ U, t x
  set Sum4 : (X _⦋n+1⦌ ⟶ Y _⦋n+1⦌) := ∑ x ∈ Uᶜ, t x
  -- U consists of "diagonal" terms where face maps satisfy d_i h_j with i adjacent to j
  -- The complement Uᶜ splits into U1 (i < j) and U2 (i > j+1), which we'll show cancel
  have U1_lt : ∀ q : Q, q ∈ U1 → (q.1 : ℕ) < (q.2 : ℕ) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨⟨j, i⟩, hxS, rfl⟩
    have hij : (i : ℕ) ≤ (j : ℕ) := by simpa [S] using hxS
    simpa using (Nat.lt_succ_of_le hij)
  have U2_gt : ∀ q : Q, q ∈ U2 → (q.2 : ℕ) + 1 < (q.1 : ℕ) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨⟨j, i⟩, hxSc, rfl⟩
    have hji : (j : ℕ) < (i : ℕ) := by
      have : ¬ ((i : ℕ) ≤ (j : ℕ)) := by simpa [S] using hxSc
      exact Nat.lt_of_not_ge this
    simpa [φSc, Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm]
      using (Nat.succ_lt_succ hji)
  have mem_U_iff (q : Q) : q ∈ U ↔ q.1 = q.2.castSucc ∨ q.1 = q.2.succ := by
    rcases q with ⟨i, j⟩
    simp only [U, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨x, h⟩ | ⟨x, h⟩) <;> cases h <;> simp
    · rintro (rfl | rfl) <;> [left; right] <;> exact ⟨j, rfl⟩
  have hU : Uᶜ = U1 ∪ U2 := by
    ext q
    constructor
    · intro hqC
      have hnotU : q ∉ U := by simpa using hqC
      by_cases hlt : (q.1 : ℕ) < (q.2 : ℕ)
      · rcases q with ⟨a, b⟩
        have hb0 : b ≠ 0 := fun h => Nat.not_lt_zero a (by simp [h] at hlt)
        apply Finset.mem_union.2
        left
        refine Finset.mem_image.2 ⟨(b.pred hb0, ⟨a, by linarith [hlt, b.isLt]⟩), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, Fin.val_pred, true_and, S]
          exact Nat.le_pred_of_lt hlt
        · simp only [Fin.castSucc_mk, Fin.eta, Fin.succ_pred, φS]
      · rcases q with ⟨a, b⟩
        simp only [mem_U_iff, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, not_or] at hnotU
        have hgt : (b : ℕ) + 1 < a := by
          refine Nat.lt_of_le_of_ne (Nat.succ_le_of_lt ?_) (Ne.symm hnotU.2)
          exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hnotU.1)
        have ha0 : a ≠ 0 := fun h => Nat.not_lt_zero ((b : ℕ) + 1)
          (by simp only [h, Fin.coe_ofNat_eq_mod, Nat.zero_mod, not_lt_zero] at hgt)
        apply Finset.mem_union.2
        right
        refine Finset.mem_image.2 ⟨(⟨b, by linarith [hgt, a.isLt]⟩, a.pred ha0), ?_, ?_⟩
        · simp only [Finset.compl_filter, not_le, Finset.mem_filter, Finset.mem_univ,
          true_and, S]
          exact Nat.lt_pred_iff.mpr hgt
        · simp only [φSc, Fin.succ_pred]; ext <;> simp [Fin.castSucc_mk]
    · intro hqU12
      refine Finset.mem_compl.2 (fun hqU ↦ ?_)
      simp only [mem_U_iff, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hqU
      rcases Finset.mem_union.mp hqU12 with h | h
      · have := U1_lt q h; omega
      · have := U2_gt q h; omega
  -- Using the simplicial identities, U1 and U2 terms reindex to give ±Sum1 and ±Sum2
  -- These combine to cancel in Sum4 = -(Sum1 + Sum2)
  have hU1 : (∑ q ∈ U1, t q) = -Sum1 := by
    have hSum1 : Sum1 =
        ∑ x ∈ S, ((-1) ^ (x.1 : ℕ) * (-1) ^ (x.2 : ℕ)) • (H.h x.1.succ ≫ Y.δ x.2.castSucc) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rcases x with ⟨j, i⟩
      have hij : i ≤ j.castSucc := by simpa [S] using hx
      simpa using congrArg (fun m => ((-1 : ℤ) ^ (j : ℕ) * (-1 : ℤ) ^ (i : ℕ)) • m)
        ((H.h_succ_comp_δ_castSucc_of_lt (i := i) (j := j) hij).symm)
    have hφS_inj : Set.InjOn φS (↑S : Set P) := by
      rintro ⟨j, i⟩ _ ⟨j', i'⟩ _ h
      simp only [φS] at h
      injection h with h1 h2
      rw [Fin.castSucc_inj.mp h1, Fin.succ_inj.mp h2]
    calc (∑ q ∈ U1, t q)
      _ = ∑ x ∈ S, t (φS x) := by
        rw [Finset.sum_image]
        simp only [hφS_inj]
      _ = - ∑ x ∈ S, ((-1) ^ (x.1 : ℕ) * (-1) ^ (x.2 : ℕ)) • (H.h x.1.succ ≫ Y.δ x.2.castSucc) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun ⟨j, i⟩ _ ↦ ?_
        simp only [Int.reduceNeg, Fin.val_castSucc, Fin.val_succ, pow_succ, mul_comm, neg_mul,
          one_mul, mul_neg, neg_smul, t, φS]
    simp only [Int.reduceNeg, hSum1]
  have hU2 : (∑ q ∈ U2, t q) = -Sum2 := by
    have hSum2 : Sum2 =
        ∑ x ∈ Sᶜ, ((-1) ^ (x.1 : ℕ) * (-1) ^ (x.2 : ℕ)) • (H.h x.1.castSucc ≫ Y.δ x.2.succ) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rcases x with ⟨j, i⟩
      have hji : j.castSucc < i := by simpa [S, not_le] using hx
      simpa using congrArg (fun m => ((-1 : ℤ) ^ (j : ℕ) * (-1 : ℤ) ^ (i : ℕ)) • m)
        ((H.h_castSucc_comp_δ_succ_of_lt (i := i) (j := j) hji).symm)
    have hφSc_inj : Set.InjOn φSc (↑(Sᶜ) : Set P) := by
      rintro ⟨j, i⟩ _ ⟨j', i'⟩ _ h
      simp only [φSc] at h
      injection h with h1 h2
      rw [Fin.succ_inj.mp h1, Fin.castSucc_inj.mp h2]
    calc (∑ q ∈ U2, t q) = ∑ x ∈ Sᶜ, t (φSc x) := by rw [Finset.sum_image]; simp only [hφSc_inj]
      _ = - ∑ x ∈ Sᶜ, ((-1) ^ (x.1 : ℕ) * (-1) ^ (x.2 : ℕ)) •
        (H.h x.1.castSucc ≫ Y.δ x.2.succ) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun ⟨j, i⟩ _ ↦ ?_
        simp only [Int.reduceNeg, Fin.val_succ, pow_succ, mul_comm, neg_mul, one_mul,
          Fin.val_castSucc, mul_neg, neg_smul, t, φSc]
    rw [hSum2]
  have h_cancel : Sum4 = -(Sum1 + Sum2) := by
    have hdisj : Disjoint U1 U2 := by
      refine Finset.disjoint_left.2 ?_
      intro q hq1 hq2
      exact (Nat.not_lt_of_ge (Nat.le_succ (q.2 : ℕ))) (Nat.lt_trans (U2_gt q hq2) (U1_lt q hq1))
    have hSum4_split : Sum4 = (∑ x ∈ U1, t x) + (∑ x ∈ U2, t x) := by
      simp only [hU, hdisj, Finset.sum_union, Sum4]
    calc Sum4 = (∑ q ∈ U1, t q) + (∑ q ∈ U2, t q) := by simp only [hSum4_split]
          _   = (-Sum1) + (-Sum2) := by simp only [hU1, hU2]
          _   = -(Sum1 + Sum2) := by abel
  -- Sum3 contains only terms where i is adjacent to j, which telescope to leave only
  -- the endpoints h_0 ∘ d_0 = f and h_n ∘ d_{n+1} = g
  have h_band : Sum3 = g.app (op ⦋n+1⦌) + -f.app (op ⦋n+1⦌) := by
    let A : Finset Q := Finset.univ.image (fun b : Fin (n + 2) => (b.castSucc, b))
    let B : Finset Q := Finset.univ.image (fun b : Fin (n + 2) => (b.succ, b))
    have hU' : U = A ∪ B := by simp [U, A, B]
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      simp only [A, B, Finset.mem_image, Finset.mem_univ, true_and]
      rintro _ ⟨i, rfl⟩ ⟨j, h_eq⟩
      injection h_eq with h1 h2
      subst h2
      exact Fin.castSucc_lt_succ.ne h1.symm
    have h_cancel : (∑ i : Fin (n + 1), H.h i.succ ≫ Y.δ i.succ.castSucc) =
                    (∑ i : Fin (n + 1), H.h i.castSucc ≫ Y.δ i.castSucc.succ) := by
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      rw [Fin.castSucc_succ, h_succ_comp_δ_castSucc_succ]
    have h_diff : Sum3 = (∑ b : Fin (n + 2), H.h b ≫ Y.δ b.castSucc) -
                         (∑ b : Fin (n + 2), H.h b ≫ Y.δ b.succ) := by
      simp only [Sum3, U, A, B, hdisj, Finset.sum_union, sub_eq_add_neg]
      rw [Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj h).2),
          Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj h).2)]
      simp only [Int.reduceNeg, Fin.val_castSucc, ← mul_pow, mul_neg, mul_one, neg_neg, one_pow,
        one_smul, Fin.val_succ, pow_succ, neg_mul, neg_smul, Finset.sum_neg_distrib, t]
    calc Sum3
      _ = (∑ b : Fin (n + 2), H.h b ≫ Y.δ b.castSucc) -
          (∑ b : Fin (n + 2), H.h b ≫ Y.δ b.succ) := by simp only [h_diff]
      _ = (H.h 0 ≫ Y.δ 0 + ∑ i : Fin (n + 1), H.h i.succ ≫ Y.δ i.succ.castSucc) -
          ((∑ i : Fin (n + 1), H.h i.castSucc ≫ Y.δ i.castSucc.succ) +
           H.h (Fin.last _) ≫ Y.δ (Fin.last _)) := by
        congr 1
        · simp only [Fin.sum_univ_succ, Fin.castSucc_zero]
        · simp only [Fin.sum_univ_castSucc, Fin.succ_last]
      _ = (H.h 0 ≫ Y.δ 0) - (H.h (Fin.last _) ≫ Y.δ (Fin.last _)) := by
        rw [h_cancel]
        abel
      _ = g.app (op ⦋n+1⦌) + -f.app (op ⦋n+1⦌) := by
        simp only [H.h_zero_comp_δ_zero, H.h_last_comp_δ_last, sub_eq_add_neg]
  rw [← Finset.sum_add_sum_compl S, (show SumQ = Sum3 + Sum4 by simpa [SumQ, Sum3, Sum4] using
    (Finset.sum_add_sum_compl (s := U) (f := t)).symm), ← add_assoc]
  simp only [Int.reduceNeg, h_band, h_cancel, neg_add_rev]
  abel

/-- A simplicial homotopy between `f` and `g` induces a chain homotopy
between the induced morphisms on the alternating face map complexes. -/
noncomputable def toChainHomotopy (H : SimplicialHomotopy f g) :
    Homotopy
      ((alternatingFaceMapComplex C).map g)
      ((alternatingFaceMapComplex C).map f) := by
  refine
    { hom := H.hom
      zero := by
        intro i j hij
        by_cases h : j = i + 1
        · exfalso
          exact hij (by simpa [ComplexShape.down] using h.symm)
        · unfold hom
          simp only [alternatingFaceMapComplex_obj_X, h, ↓reduceDIte]
      comm := by
        intro n
        cases n with
        | zero =>
            simpa only [ComplexShape.down, alternatingFaceMapComplex,
              AlternatingFaceMapComplex.obj_X, AlternatingFaceMapComplex.map_f, dNext,
              ComplexShape.down'_Rel, Nat.add_eq_zero_iff, one_ne_zero, and_false,
              not_false_eq_true, HomologicalComplex.shape, Limits.zero_comp, AddMonoidHom.mk'_apply,
              prevD, zero_add, id_eq, Nat.reduceAdd] using
              (comm_zero_form (H := H) (C := C) (f := f) (g := g))
        | succ n =>
            simpa only [ComplexShape.down, alternatingFaceMapComplex,
              AlternatingFaceMapComplex.obj_X, AlternatingFaceMapComplex.map_f, dNext,
              AddMonoidHom.mk'_apply, hom, Nat.add_right_cancel_iff, prevD, id_eq] using
              (comm_succ_form (H := H) (C := C) (f := f) (g := g) n) }

theorem map_homology_eq [CategoryWithHomology C] (H : SimplicialHomotopy f g) (n : ℕ) :
    (HomologicalComplex.homologyFunctor C _ n).map ((alternatingFaceMapComplex C).map f) =
    (HomologicalComplex.homologyFunctor C _ n).map ((alternatingFaceMapComplex C).map g) := by
  simpa [eq_comm] using (H.toChainHomotopy).homologyMap_eq n

end SimplicialHomotopy
end CategoryTheory
