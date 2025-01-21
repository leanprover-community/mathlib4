/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Wojciech Nawrocki
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Ideals in a matrix ring

This file defines left (resp. two-sided) ideals in a matrix semiring (resp. ring)
over left (resp. two-sided) ideals in the base semiring (resp. ring).
We also characterize Jacobson radicals of ideals in such rings.

## Main results

* `TwoSidedIdeal.equivMatricesOver` and `TwoSidedIdeal.orderIsoMatricesOver`
  establish an order isomorphism between two-sided ideals in $R$ and those in $Mₙ(R)$.
* `TwoSidedIdeal.jacobson_matricesOver` shows that $J(Mₙ(I)) = Mₙ(J(I))$
  for any two-sided ideal $I ≤ R$.
-/

/-! ### Left ideals in a matrix semiring -/

namespace Ideal
open Matrix

variable {R : Type*} [Semiring R]
         (n : Type*) [Fintype n] [DecidableEq n]

/-- The left ideal of matrices with entries in `I ≤ R`. -/
def matricesOver (I : Ideal R) : Ideal (Matrix n n R) where
  carrier := { M | ∀ i j, M i j ∈ I }
  add_mem' ha hb i j := I.add_mem (ha i j) (hb i j)
  zero_mem' _ _ := I.zero_mem
  smul_mem' M N hN := by
    intro i j
    rw [smul_eq_mul, mul_apply]
    apply sum_mem
    intro k _
    apply I.mul_mem_left _ (hN k j)

@[simp]
theorem mem_matricesOver (I : Ideal R) (M : Matrix n n R) :
    M ∈ I.matricesOver n ↔ ∀ i j, M i j ∈ I := by rfl

theorem matricesOver_monotone : Monotone (matricesOver (R := R) n) :=
  fun _ _ IJ _ MI i j => IJ (MI i j)

theorem matricesOver_strictMono_of_nonempty [Nonempty n] :
    StrictMono (matricesOver (R := R) n) :=
  matricesOver_monotone n |>.strictMono_of_injective <| fun I J eq => by
    ext x
    have : (∀ _ _, x ∈ I) ↔ (∀ _ _, x ∈ J) := congr((Matrix.of fun _ _ => x) ∈ $eq)
    simpa only [forall_const] using this

@[simp]
theorem matricesOver_bot : (⊥ : Ideal R).matricesOver n = ⊥ := by
  ext M
  simp only [mem_matricesOver, mem_bot]
  constructor
  · intro H; ext; apply H
  · intro H; simp [H]

@[simp]
theorem matricesOver_top : (⊤ : Ideal R).matricesOver n = ⊤ := by
  ext; simp

end Ideal

/-! ### Jacobson radicals of left ideals in a matrix ring -/

namespace Ideal
open Matrix

variable {R : Type*} [Ring R] {n : Type*} [Fintype n] [DecidableEq n]

/-- A standard basis matrix is in $J(Mₙ(I))$
as long as its one possibly non-zero entry is in $J(I)$. -/
theorem stdBasisMatrix_mem_jacobson_matricesOver (I : Ideal R) :
    ∀ x ∈ I.jacobson, ∀ (i j : n), stdBasisMatrix i j x ∈ (I.matricesOver n).jacobson := by
  -- Proof generalized from example 8 in
  -- https://ysharifi.wordpress.com/2022/08/16/the-jacobson-radical-basic-examples/
  simp_rw [Ideal.mem_jacobson_iff]
  intro x xIJ p q M
  have ⟨z, zMx⟩ := xIJ (M q p)
  let N : Matrix n n R := 1 - ∑ i, stdBasisMatrix i q (if i = q then 1 - z else (M i p)*x*z)
  use N
  intro i j
  obtain rfl | qj := eq_or_ne q j
  · by_cases iq : i = q
    · simp [iq, N, zMx, stdBasisMatrix, mul_apply, sum_apply, ite_and, sub_mul]
    · convert I.mul_mem_left (-M i p * x) zMx
      simp [iq, N, zMx, stdBasisMatrix, mul_apply, sum_apply, ite_and, sub_mul]
      simp [sub_add, mul_add, mul_sub, mul_assoc]
  · simp [N, qj, sum_apply, mul_apply]

/-- For any left ideal $I ≤ R$, we have $Mₙ(J(I)) ≤ J(Mₙ(I))$. -/
theorem matricesOver_jacobson_le (I : Ideal R) :
    I.jacobson.matricesOver n ≤ (I.matricesOver n).jacobson := by
  intro M MI
  rw [matrix_eq_sum_stdBasisMatrix M]
  apply sum_mem
  intro i _
  apply sum_mem
  intro j _
  apply stdBasisMatrix_mem_jacobson_matricesOver I _ (MI i j)

end Ideal

/-! ### Two-sided ideals in a matrix ring -/

namespace TwoSidedIdeal
open Matrix

variable {R : Type*} [Ring R]
         (n : Type*) [Fintype n]

/-- The two-sided ideal of matrices with entries in `I ≤ R`. -/
def matricesOver (I : TwoSidedIdeal R) : TwoSidedIdeal (Matrix n n R) :=
  TwoSidedIdeal.mk' { M | ∀ i j, M i j ∈ I }
    (fun _ _ => I.zero_mem)
    (fun ha hb i j => I.add_mem (ha i j) (hb i j))
    (fun ha i j => I.neg_mem (ha i j))
    (fun ha i j => by
      rw [mul_apply]
      apply sum_mem
      intro k _
      apply I.mul_mem_left _ _ (ha k j))
    (fun ha i j => by
      rw [mul_apply]
      apply sum_mem
      intro k _
      apply I.mul_mem_right _ _ (ha i k))

@[simp]
lemma mem_matricesOver (I : TwoSidedIdeal R) (M : Matrix n n R) :
    M ∈ I.matricesOver n ↔ ∀ i j, M i j ∈ I := by
  simp [matricesOver]

theorem matricesOver_monotone : Monotone (matricesOver (R := R) n) :=
  fun _ _ IJ _ MI i j => IJ (MI i j)

theorem matricesOver_strictMono_of_nonempty [h : Nonempty n] :
    StrictMono (matricesOver (R := R) n) :=
  matricesOver_monotone n |>.strictMono_of_injective <| fun I J eq => by
    ext x
    have : _ ↔ _ := congr((Matrix.of fun _ _ => x) ∈ $eq)
    simpa only [mem_matricesOver, of_apply, forall_const] using this

@[simp]
theorem matricesOver_bot : (⊥ : TwoSidedIdeal R).matricesOver n = ⊥ := by
  ext M
  simp only [mem_matricesOver, mem_bot]
  constructor
  · intro H; ext; apply H
  · intro H; simp [H]

@[simp]
theorem matricesOver_top : (⊤ : TwoSidedIdeal R).matricesOver n = ⊤ := by
  ext; simp

theorem asIdeal_matricesOver [DecidableEq n] (I : TwoSidedIdeal R) :
    asIdeal (I.matricesOver n) = (asIdeal I).matricesOver n := by
  ext; simp

variable {n : Type*} [Fintype n]

/--
Two-sided ideals in $R$ correspond bijectively to those in $Mₙ(R)$.
Given an ideal $I ≤ R$, we send it to $Mₙ(I)$.
Given an ideal $J ≤ Mₙ(R)$, we send it to $\{Nᵢⱼ ∣ ∃ N ∈ J\}$.
-/
@[simps]
def equivMatricesOver (i j : n) : TwoSidedIdeal R ≃ TwoSidedIdeal (Matrix n n R) where
  toFun I := I.matricesOver n
  invFun J := TwoSidedIdeal.mk'
    { N i j | N ∈ J }
    ⟨0, J.zero_mem, rfl⟩
    (by rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩; exact ⟨x + y, J.add_mem hx hy, rfl⟩)
    (by rintro _ ⟨x, hx, rfl⟩; exact ⟨-x, J.neg_mem hx, rfl⟩)
    (by
      classical
      rintro x _ ⟨y, hy, rfl⟩
      exact ⟨diagonal (fun _ ↦ x) * y, J.mul_mem_left _ _ hy, by simp⟩)
    (by
      classical
      rintro _ y ⟨x, hx, rfl⟩
      exact ⟨x * diagonal (fun _ ↦ y), J.mul_mem_right _ _ hx, by simp⟩)
  right_inv J := SetLike.ext fun x ↦ by
    classical
    simp only [mem_mk', Set.mem_image, SetLike.mem_coe, mem_matricesOver]
    constructor
    · intro h
      choose y hy1 hy2 using h
      rw [matrix_eq_sum_stdBasisMatrix x]
      refine sum_mem fun k _ ↦ sum_mem fun l _ ↦ ?_
      suffices
          stdBasisMatrix k l (x k l) =
          stdBasisMatrix k i 1 * y k l * stdBasisMatrix j l 1 by
        rw [this]
        exact J.mul_mem_right _ _ (J.mul_mem_left _ _ <| hy1 _ _)
      ext a b
      by_cases hab : a = k ∧ b = l
      · rcases hab with ⟨ha, hb⟩
        subst ha hb
        simp only [StdBasisMatrix.apply_same, StdBasisMatrix.mul_right_apply_same,
          StdBasisMatrix.mul_left_apply_same, one_mul, mul_one]
        rw [hy2 a b]
      · conv_lhs =>
          dsimp [stdBasisMatrix]
          rw [if_neg (by tauto)]
        rw [not_and_or] at hab
        rcases hab with ha | hb
        · rw [mul_assoc, StdBasisMatrix.mul_left_apply_of_ne (h := ha)]
        · rw [StdBasisMatrix.mul_right_apply_of_ne (hbj := hb)]
    · intro hx k l
      refine ⟨stdBasisMatrix i k 1 * x * stdBasisMatrix l j 1,
        J.mul_mem_right _ _ (J.mul_mem_left _ _ hx), ?_⟩
      rw [StdBasisMatrix.mul_right_apply_same, StdBasisMatrix.mul_left_apply_same,
        mul_one, one_mul]
  left_inv I := SetLike.ext fun x ↦ by
    simp only [mem_mk', Set.mem_image, SetLike.mem_coe, mem_matricesOver]
    constructor
    · intro h
      choose y hy1 hy2 using h
      exact hy2 ▸ hy1 _ _
    · intro h
      exact ⟨of fun _ _ => x, by simp [h], rfl⟩

/--
Two-sided ideals in $R$ are order-isomorphic with those in $Mₙ(R)$.
See also `equivMatricesOver`.
-/
@[simps!]
def orderIsoMatricesOver (i j : n) : TwoSidedIdeal R ≃o TwoSidedIdeal (Matrix n n R) where
  __ := equivMatricesOver i j
  map_rel_iff' {I J} := by
    simp only [equivMatricesOver_apply]
    constructor
    · intro le x xI
      specialize @le (of fun _ _ => x) (by simp [xI])
      letI : Inhabited n := ⟨i⟩
      simpa using le
    · intro IJ M MI i j
      exact IJ <| MI i j

end TwoSidedIdeal

/-! ### Jacobson radicals of two-sided ideals in a matrix ring -/

namespace TwoSidedIdeal
open Matrix

variable {R : Type*} [Ring R] {n : Type*} [Fintype n] [DecidableEq n]

private lemma jacobson_matricesOver_le (I : TwoSidedIdeal R) :
    (I.matricesOver n).jacobson ≤ I.jacobson.matricesOver n := by
  -- Proof generalized from example 8 in
  -- https://ysharifi.wordpress.com/2022/08/16/the-jacobson-radical-basic-examples/
  intro M Mmem p q
  rw [sub_zero, mem_jacobson_iff]
  replace Mmem := mul_mem_right _ _ (stdBasisMatrix q p 1) Mmem
  rw [mem_jacobson_iff] at Mmem
  intro y
  specialize Mmem (y • stdBasisMatrix p p 1)
  have ⟨N, NxMI⟩ := Mmem
  use N p p
  simpa [mul_apply, stdBasisMatrix, ite_and] using NxMI p p

/-- For any two-sided ideal $I ≤ R$, we have $J(Mₙ(I)) = Mₙ(J(I))$. -/
theorem jacobson_matricesOver (I : TwoSidedIdeal R) :
    (I.matricesOver n).jacobson = I.jacobson.matricesOver n := by
  apply le_antisymm
  · apply jacobson_matricesOver_le
  · show asIdeal (I.matricesOver n).jacobson ≥ asIdeal (I.jacobson.matricesOver n)
    simp [asIdeal_jacobson, asIdeal_matricesOver, Ideal.matricesOver_jacobson_le]

theorem matricesOver_jacobson_bot :
    (⊥ : TwoSidedIdeal R).jacobson.matricesOver n = (⊥ : TwoSidedIdeal (Matrix n n R)).jacobson :=
  matricesOver_bot n (R := R) ▸ (jacobson_matricesOver _).symm

end TwoSidedIdeal
