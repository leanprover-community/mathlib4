/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Wojciech Nawrocki
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.GroupTheory.Congruence.BigOperators
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
theorem single_mem_jacobson_matricesOver (I : Ideal R) :
    ∀ x ∈ I.jacobson, ∀ (i j : n), single i j x ∈ (I.matricesOver n).jacobson := by
  -- Proof generalized from example 8 in
  -- https://ysharifi.wordpress.com/2022/08/16/the-jacobson-radical-basic-examples/
  simp_rw [Ideal.mem_jacobson_iff]
  intro x xIJ p q M
  have ⟨z, zMx⟩ := xIJ (M q p)
  let N : Matrix n n R := 1 - ∑ i, single i q (if i = q then 1 - z else (M i p)*x*z)
  use N
  intro i j
  obtain rfl | qj := eq_or_ne q j
  · by_cases iq : i = q
    · simp [iq, N, zMx, single, mul_apply, sum_apply, ite_and, sub_mul]
    · convert I.mul_mem_left (-M i p * x) zMx
      simp [iq, N, zMx, single, mul_apply, sum_apply, ite_and, sub_mul]
      simp [sub_add, mul_add, mul_sub, mul_assoc]
  · simp [N, qj, sum_apply, mul_apply]

@[deprecated (since := "2025-05-05")]
alias stdBasisMatrix_mem_jacobson_matricesOver := single_mem_jacobson_matricesOver

/-- For any left ideal $I ≤ R$, we have $Mₙ(J(I)) ≤ J(Mₙ(I))$. -/
theorem matricesOver_jacobson_le (I : Ideal R) :
    I.jacobson.matricesOver n ≤ (I.matricesOver n).jacobson := by
  intro M MI
  rw [matrix_eq_sum_single M]
  apply sum_mem
  intro i _
  apply sum_mem
  intro j _
  apply single_mem_jacobson_matricesOver I _ (MI i j)

end Ideal

/-! ### Two-sided ideals in a matrix ring -/

namespace RingCon
variable {R n : Type*}

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R] [Fintype n]
variable (n)

/-- The ring congruence of matrices with entries related by `c`. -/
def matrix (c : RingCon R) : RingCon (Matrix n n R) where
  r M N := ∀ i j, c (M i j) (N i j)
  -- note: kept `fun` to distinguish `RingCon`'s binders from `r`'s binders.
  iseqv.refl _ := fun _ _ ↦ c.refl _
  iseqv.symm h := fun _ _ ↦ c.symm <| h _ _
  iseqv.trans h₁ h₂ := fun _ _ ↦ c.trans (h₁ _ _) (h₂ _ _)
  add' h₁ h₂ := fun _ _ ↦ c.add (h₁ _ _) (h₂ _ _)
  mul' h₁ h₂ := fun _ _ ↦ c.finset_sum _ fun _ _ => c.mul (h₁ _ _) (h₂ _ _)

@[simp low]
theorem matrix_apply {c : RingCon R} {M N : Matrix n n R} :
    c.matrix n M N ↔ ∀ i j, c (M i j) (N i j) :=
  Iff.rfl

@[simp]
theorem matrix_apply_single [DecidableEq n] {c : RingCon R} {i j : n} {x y : R} :
    c.matrix n (Matrix.single i j x) (Matrix.single i j y) ↔ c x y := by
  refine ⟨fun h ↦ by simpa using h i j, fun h i' j' ↦ ?_⟩
  obtain hi | rfl := ne_or_eq i i'
  · simpa [hi] using c.refl 0
  obtain hj | rfl := ne_or_eq j j'
  · simpa [hj] using c.refl _
  simpa using h

@[deprecated (since := "2025-05-05")] alias matrix_apply_stdBasisMatrix := matrix_apply_single

theorem matrix_monotone : Monotone (matrix (R := R) n) :=
  fun _ _ hc _ _ h _ _ ↦ hc (h _ _)

theorem matrix_injective [Nonempty n] : Function.Injective (matrix (R := R) n) :=
  fun I J eq ↦ RingCon.ext fun r s ↦ by
    have := congr_fun (DFunLike.congr_fun eq (Matrix.of fun _ _ ↦ r)) (Matrix.of fun _ _ ↦ s)
    simpa using this

theorem matrix_strictMono_of_nonempty [Nonempty n] :
    StrictMono (matrix (R := R) n) :=
  matrix_monotone n |>.strictMono_of_injective <| matrix_injective _

@[simp]
theorem matrix_bot : (⊥ : RingCon R).matrix n = ⊥ :=
  eq_bot_iff.2 fun _ _ h ↦ Matrix.ext h

@[simp]
theorem matrix_top : (⊤ : RingCon R).matrix n = ⊤ :=
  eq_top_iff.2 fun _ _ _ _ _ ↦ by simp

open Matrix

variable {n}

/-- The congruence relation induced by `c` on `single i j`. -/
def ofMatrix [DecidableEq n] (c : RingCon (Matrix n n R)) : RingCon R where
  r x y := ∀ i j, c (single i j x) (single i j y)
  iseqv.refl _ := fun _ _ ↦ c.refl _
  iseqv.symm h := fun _ _ ↦ c.symm <| h _ _
  iseqv.trans h₁ h₂ := fun _ _ ↦ c.trans (h₁ _ _) (h₂ _ _)
  add' h₁ h₂ := fun _ _ ↦ by simpa [single_add] using c.add (h₁ _ _) (h₂ _ _)
  mul' h₁ h₂ := fun i j ↦ by simpa using c.mul (h₁ i i) (h₂ i j)

@[simp]
theorem ofMatrix_rel [DecidableEq n] {c : RingCon (Matrix n n R)} {x y : R} :
    ofMatrix c x y ↔ ∀ i j, c (single i j x) (single i j y) :=
  Iff.rfl

@[simp] theorem ofMatrix_matrix [DecidableEq n] [Nonempty n] (c : RingCon R) :
    ofMatrix (matrix n c) = c := by
  ext x y
  classical
  constructor
  · intro h
    inhabit n
    simpa using h default default default default
  · intro h i j
    rwa [matrix_apply_single]

end NonUnitalNonAssocSemiring

section NonAssocSemiring
variable [NonAssocSemiring R] [Fintype n]
open Matrix

/-- Note that this does not apply to a non-unital ring, with counterexample where the elementwise
congruence relation `!![⊤,⊤;⊤,(· ≡ · [PMOD 4])]` is a ring congruence over
`Matrix (Fin 2) (Fin 2) 2ℤ`. -/
@[simp]
theorem matrix_ofMatrix [DecidableEq n] (c : RingCon (Matrix n n R)) :
    matrix n (ofMatrix c) = c := by
  ext x y
  classical
  constructor
  · intro h
    rw [matrix_eq_sum_single x, matrix_eq_sum_single y]
    refine c.finset_sum _ fun i _ ↦ c.finset_sum _ fun j _ ↦ h i j i j
  · intro h i' j' i j
    simpa using c.mul (c.mul (c.refl <| single i i' 1) h) (c.refl <| single j' j 1)

/-- A version of `ofMatrix_rel` for a single matrix index, rather than all indices. -/
theorem ofMatrix_rel' [DecidableEq n] {c : RingCon (Matrix n n R)} {x y : R} (i j : n) :
    ofMatrix c x y ↔ c (single i j x) (single i j y) := by
  refine ⟨fun h ↦ h i j, fun h i' j' ↦ ?_⟩
  simpa using c.mul (c.mul (c.refl <| single i' i 1) h) (c.refl <| single j j' 1)

theorem coe_ofMatrix_eq_relationMap [DecidableEq n] {c : RingCon (Matrix n n R)} (i j : n) :
    ⇑(ofMatrix c) = Relation.Map c (· i j) (· i j) := by
  ext x y
  constructor
  · intro h
    refine ⟨_,_, h i j, ?_⟩
    simp
  · rintro ⟨X, Y, h, rfl, rfl⟩ i' j'
    simpa using c.mul (c.mul (c.refl <| single i' i 1) h) (c.refl <| single j j' 1)

end NonAssocSemiring

end RingCon

namespace TwoSidedIdeal
open Matrix

variable {R : Type*} (n : Type*)

section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing R] [Fintype n]

/-- The two-sided ideal of matrices with entries in `I ≤ R`. -/
@[simps]
def matricesOver (I : TwoSidedIdeal R) : TwoSidedIdeal (Matrix n n R) where
  ringCon := I.ringCon.matrix n

@[simp]
lemma mem_matricesOver (I : TwoSidedIdeal R) (M : Matrix n n R) :
    M ∈ I.matricesOver n ↔ ∀ i j, M i j ∈ I := Iff.rfl

theorem matricesOver_monotone : Monotone (matricesOver (R := R) n) :=
  fun _ _ IJ _ MI i j => IJ (MI i j)

theorem matricesOver_strictMono_of_nonempty [h : Nonempty n] :
    StrictMono (matricesOver (R := R) n) :=
  matricesOver_monotone n |>.strictMono_of_injective <|
    .comp (fun _ _ => mk.inj) <| (RingCon.matrix_injective n).comp ringCon_injective

@[simp]
theorem matricesOver_bot : (⊥ : TwoSidedIdeal R).matricesOver n = ⊥ :=
  ringCon_injective <| RingCon.matrix_bot _

@[simp]
theorem matricesOver_top : (⊤ : TwoSidedIdeal R).matricesOver n = ⊤ :=
  ringCon_injective <| RingCon.matrix_top _

end NonUnitalNonAssocRing

section NonAssocRing
variable [NonAssocRing R] [Fintype n] [Nonempty n] [DecidableEq n]

variable {n}

/--
Two-sided ideals in $R$ correspond bijectively to those in $Mₙ(R)$.
Given an ideal $I ≤ R$, we send it to $Mₙ(I)$.
Given an ideal $J ≤ Mₙ(R)$, we send it to $\{Nᵢⱼ ∣ ∃ N ∈ J\}$.
-/
@[simps]
def equivMatricesOver [Nonempty n] [DecidableEq n] :
    TwoSidedIdeal R ≃ TwoSidedIdeal (Matrix n n R) where
  toFun I := I.matricesOver n
  invFun J := { ringCon := J.ringCon.ofMatrix }
  right_inv _ := ringCon_injective <| RingCon.matrix_ofMatrix _
  left_inv _ := ringCon_injective <| RingCon.ofMatrix_matrix _

theorem coe_equivMatricesOver_symm_apply (I : TwoSidedIdeal (Matrix n n R)) (i j : n) :
    equivMatricesOver.symm I = {N i j | N ∈ I} := by
  ext r
  constructor
  · intro h
    exact ⟨single i j r, by simpa using h i j, by simp⟩
  · rintro ⟨n, hn, rfl⟩
    rw [SetLike.mem_coe, mem_iff, equivMatricesOver_symm_apply_ringCon,
      RingCon.coe_ofMatrix_eq_relationMap i j]
    exact ⟨n, 0, (I.mem_iff n).mp hn, rfl, rfl⟩

/--
Two-sided ideals in $R$ are order-isomorphic with those in $Mₙ(R)$.
See also `equivMatricesOver`.
-/
@[simps!]
def orderIsoMatricesOver : TwoSidedIdeal R ≃o TwoSidedIdeal (Matrix n n R) where
  __ := equivMatricesOver
  map_rel_iff' {I J} := by
    simp only [equivMatricesOver_apply]
    constructor
    · intro le x xI
      specialize @le (of fun _ _ => x) (by simp [xI])
      simpa using le
    · intro IJ M MI i j
      exact IJ <| MI i j

end NonAssocRing

section Ring
variable [Ring R] [Fintype n]

theorem asIdeal_matricesOver [DecidableEq n] (I : TwoSidedIdeal R) :
    asIdeal (I.matricesOver n) = (asIdeal I).matricesOver n := by
  ext; simp

end Ring

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
  simp only [zero_apply, ← mem_iff]
  rw [mem_jacobson_iff]
  replace Mmem := mul_mem_right _ _ (single q p 1) Mmem
  rw [mem_jacobson_iff] at Mmem
  intro y
  specialize Mmem (y • single p p 1)
  have ⟨N, NxMI⟩ := Mmem
  use N p p
  simpa [mul_apply, single, ite_and] using NxMI p p

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
