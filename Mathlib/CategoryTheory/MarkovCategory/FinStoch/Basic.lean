/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.NNReal.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite Stochastic Matrices

FinStoch: finite types with stochastic matrices.

## Main definitions

* `StochasticMatrix m n` - Matrix where rows sum to 1
* `FinStoch` - Category of finite types and stochastic matrices
* `DetMorphism m n` - Deterministic matrix with underlying function
* `isDeterministic` - Matrix has exactly one 1 per row

## Design

Rows sum to 1. Entry (i,j) gives P(j|i).
Uses NNReal to avoid negativity.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]

## Tags

Markov category, stochastic matrix
-/

namespace CategoryTheory.MarkovCategory

universe u

/-- Stochastic matrix where rows sum to 1. Entry (i,j) is P(j|i). -/
structure StochasticMatrix (m n : Type u) [Fintype m] [Fintype n] where
  /-- The matrix of non-negative reals -/
  toMatrix : Matrix m n NNReal
  /-- Each row sums to 1 -/
  row_sum : ∀ i : m, ∑ j : n, toMatrix i j = 1

namespace StochasticMatrix

variable {m n p : Type u} [Fintype m] [Fintype n] [Fintype p]

/-- Identity matrix. -/
def id (m : Type u) [Fintype m] [DecidableEq m] : StochasticMatrix m m where
  toMatrix := fun i j => if i = j then (1 : NNReal) else 0
  row_sum := fun i => by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp only [if_neg (Ne.symm hj)]
    · intro h
      exfalso
      exact h (Finset.mem_univ _)

/-- Composition: P(Z|X) = ∑_Y P(Y|X) * P(Z|Y). -/
def comp (f : StochasticMatrix m n) (g : StochasticMatrix n p) : StochasticMatrix m p where
  toMatrix := fun i k => ∑ j : n, f.toMatrix i j * g.toMatrix j k
  row_sum := fun i => by
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, g.row_sum, f.row_sum]

/-- Tensor product for independent processes. -/
def tensor {m₁ n₁ m₂ n₂ : Type u} [Fintype m₁] [Fintype n₁] [Fintype m₂] [Fintype n₂]
    (f : StochasticMatrix m₁ n₁) (g : StochasticMatrix m₂ n₂) :
    StochasticMatrix (m₁ × m₂) (n₁ × n₂) where
  toMatrix := fun ij kl => f.toMatrix ij.1 kl.1 * g.toMatrix ij.2 kl.2
  row_sum := fun ij => by
    obtain ⟨i₁, i₂⟩ := ij
    rw [← Finset.univ_product_univ, Finset.sum_product, ← Finset.sum_mul_sum]
    simp [f.row_sum i₁, g.row_sum i₂]

@[ext]
theorem ext {f g : StochasticMatrix m n} (h : f.toMatrix = g.toMatrix) : f = g := by
  cases f
  cases g
  congr

/-! ### Deterministic matrices -/

/-- Each row has exactly one 1. -/
def isDeterministic (f : StochasticMatrix m n) : Prop :=
  ∀ i : m, ∃! j : n, f.toMatrix i j = 1

/-- Extract function from deterministic matrix. -/
noncomputable def apply (f : StochasticMatrix m n)
    (h : f.isDeterministic) (i : m) : n :=
  (h i).choose

/-- Apply gives the unique 1. -/
lemma apply_spec (f : StochasticMatrix m n) (h : f.isDeterministic) (i : m) :
    f.toMatrix i (f.apply h i) = 1 :=
  (h i).choose_spec.1

/-- Non-chosen outputs are 0. -/
lemma apply_spec_ne (f : StochasticMatrix m n) [DecidableEq n] (h : f.isDeterministic) (i : m)
    (j : n) (hj : j ≠ f.apply h i) : f.toMatrix i j = 0 := by
  by_contra h_nonzero
  push_neg at h_nonzero
  have h_sum := f.row_sum i
  have h_unique := (h i).choose_spec.2
  by_cases h_one : f.toMatrix i j = 1
  · exact hj (h_unique j h_one)
  · -- Since row sums to 1 and has unique 1, all other entries must be 0
    have h_apply_one := apply_spec f h i
    -- The sum equals 1 and one entry is 1, so all others must be 0
    have h_sum_eq : ∑ k : n, f.toMatrix i k = 1 := f.row_sum i
    -- Split the sum: chosen entry + rest
    have h_split : ∑ k : n, f.toMatrix i k =
        f.toMatrix i (f.apply h i) + ∑ k ∈ Finset.univ.erase (f.apply h i), f.toMatrix i k := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (f.apply h i))]
      ring
    -- Substitute known values
    rw [h_split] at h_sum_eq
    rw [h_apply_one] at h_sum_eq
    -- So the rest sums to 0: 1 + rest = 1 implies rest = 0
    have h_others_zero : ∑ k ∈ Finset.univ.erase (f.apply h i), f.toMatrix i k = 0 := by
      grind only
    -- Non-negative terms summing to 0 means each is 0
    have h_all_zero : ∀ k ∈ Finset.univ.erase (f.apply h i), f.toMatrix i k = 0 := by
      have h_nonneg : ∀ k ∈ Finset.univ.erase (f.apply h i), 0 ≤ f.toMatrix i k := by
        intro k _
        exact (f.toMatrix i k).2
      exact Finset.sum_eq_zero_iff_of_nonneg h_nonneg |>.mp h_others_zero
    -- j is different from f.apply h i, so it's in the erased set
    have h_j_in : j ∈ Finset.univ.erase (f.apply h i) := by
      simp [hj]
    exact h_nonzero (h_all_zero j h_j_in)

/-- Matrix entry is 1 iff it's the unique output. -/
@[simp]
lemma det_matrix_eq_one_iff (f : StochasticMatrix m n) (h : f.isDeterministic)
    (i : m) (j : n) : f.toMatrix i j = 1 ↔ j = f.apply h i := by
  constructor
  · intro hj
    exact (h i).choose_spec.2 j hj
  · intro hj
    rw [hj]
    exact apply_spec f h i

/-- All other entries are 0. -/
@[simp]
lemma det_matrix_eq_zero_of_ne (f : StochasticMatrix m n) [DecidableEq n] (h : f.isDeterministic)
    (i : m) (j : n) (hne : j ≠ f.apply h i) : f.toMatrix i j = 0 :=
  apply_spec_ne f h i j hne

/-- Identity matrix is deterministic. -/
lemma id_isDeterministic (m : Type u) [Fintype m] [DecidableEq m] :
    (id m).isDeterministic := by
  intro i
  use i
  constructor
  · simp [id]
  · intro j hj
    simp [id] at hj
    exact hj.symm

/-- Deterministic matrices compose to deterministic matrices. -/
theorem det_comp_det (f : StochasticMatrix m n) (g : StochasticMatrix n p)
    [DecidableEq n] (hf : f.isDeterministic) (hg : g.isDeterministic) :
    (comp f g).isDeterministic := by
  intro i
  use g.apply hg (f.apply hf i)
  constructor
  · simp only [comp]
    rw [Finset.sum_eq_single (f.apply hf i)]
    · simp [apply_spec f hf i, apply_spec g hg (f.apply hf i)]
    · intro j _ hj
      simp [apply_spec_ne f hf i j hj]
    · intro h; exfalso; exact h (Finset.mem_univ _)
  · intro k hk
    simp only [comp] at hk
    -- The sum equals 1, so there's exactly one j with f(i,j) * g(j,k) = 1
    -- This means f(i,j) = 1 and g(j,k) = 1
    have h_exist : ∃ j : n, f.toMatrix i j = 1 ∧ g.toMatrix j k = 1 := by
      by_contra h_none
      push_neg at h_none
      -- The sum simplifies because f is deterministic
      have h_sum_simp : ∑ j : n, f.toMatrix i j * g.toMatrix j k = g.toMatrix (f.apply hf i) k := by
        rw [Finset.sum_eq_single (f.apply hf i)]
        · simp [apply_spec f hf i]
        · intro j _ hj
          simp [apply_spec_ne f hf i j hj]
        · intro h; exfalso; exact h (Finset.mem_univ _)
      -- So g(f.apply hf i, k) = 1
      rw [h_sum_simp] at hk
      -- But h_none says if f(i, f.apply hf i) = 1 then g(f.apply hf i, k) ≠ 1
      have : g.toMatrix (f.apply hf i) k ≠ 1 := h_none _ (apply_spec f hf i)
      exact this hk
    obtain ⟨j, hf_j, hg_j⟩ := h_exist
    have h_j_unique : j = f.apply hf i := (hf i).choose_spec.2 j hf_j
    rw [h_j_unique] at hg_j
    exact (hg (f.apply hf i)).choose_spec.2 k hg_j

/-- Composition of deterministic matrices equals function composition. -/
theorem det_comp_eq_fun_comp (f : StochasticMatrix m n) (g : StochasticMatrix n p)
    [DecidableEq n] (hf : f.isDeterministic) (hg : g.isDeterministic) (i : m) :
    (comp f g).apply (det_comp_det f g hf hg) i = g.apply hg (f.apply hf i) := by
  -- By det_comp_det, the unique 1 in row i of comp f g is at column g.apply hg (f.apply hf i)
  -- The apply function returns this unique column
  have h_unique := (det_comp_det f g hf hg i).choose_spec
  -- We know comp f g has value 1 at g.apply hg (f.apply hf i)
  have h_one : (comp f g).toMatrix i (g.apply hg (f.apply hf i)) = 1 := by
    simp only [comp]
    rw [Finset.sum_eq_single (f.apply hf i)]
    · simp [apply_spec f hf i, apply_spec g hg (f.apply hf i)]
    · intro j _ hj
      simp [apply_spec_ne f hf i j hj]
    · intro h; exfalso; exact h (Finset.mem_univ _)
  -- By uniqueness, apply must return this value
  have h_eq := h_unique.2 _ h_one
  exact h_eq.symm

/-! ### Helper lemmas for sums -/

/-- Sum of delta function equals 1 at unique point. -/
lemma sum_delta {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    ∑ x : α, (if x = a then (1 : NNReal) else 0) = 1 := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exfalso; exact h (Finset.mem_univ _)

/-- Product of delta functions. -/
lemma delta_mul_delta {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a a' : α) (b b' : β) :
    (if a = a' then (1 : NNReal) else 0) * (if b = b' then 1 else 0) =
    if a = a' ∧ b = b' then 1 else 0 := by
  by_cases ha : a = a'
  · by_cases hb : b = b'
    · simp [ha, hb]
    · simp [ha, hb]
  · simp [ha]

/-! ### Extensionality lemmas for deterministic matrices -/

/-- Tensor product of deterministic matrices is deterministic. -/
theorem det_tensor_det {m₁ n₁ m₂ n₂ : Type u} [Fintype m₁] [Fintype n₁] [Fintype m₂] [Fintype n₂]
    (f : StochasticMatrix m₁ n₁) (g : StochasticMatrix m₂ n₂)
    [DecidableEq n₁]
    (hf : f.isDeterministic) (hg : g.isDeterministic) :
    (tensor f g).isDeterministic := by
  intro ⟨i₁, i₂⟩
  -- The unique output is (f.apply hf i₁, g.apply hg i₂)
  use (f.apply hf i₁, g.apply hg i₂)
  constructor
  · -- Show this output has value 1
    simp only [tensor]
    rw [apply_spec f hf i₁, apply_spec g hg i₂]
    simp
  · -- Show uniqueness
    intro ⟨j₁, j₂⟩ hj
    simp only [tensor] at hj
    -- Since f and g are deterministic, the product equals 1 iff both equal 1
    have h_prod : f.toMatrix i₁ j₁ * g.toMatrix i₂ j₂ = 1 := hj
    -- In NNReal, a product equals 1 iff both factors equal 1
    have h₁ : f.toMatrix i₁ j₁ = 1 := by
      by_contra h_not_one
      by_cases h_zero : f.toMatrix i₁ j₁ = 0
      · rw [h_zero, zero_mul] at h_prod
        simp at h_prod
      · -- f.toMatrix i₁ j₁ is between 0 and 1 but not 0 or 1
        -- Since f is deterministic, each entry is either 0 or 1
        by_cases h_eq : j₁ = f.apply hf i₁
        · subst h_eq
          exact absurd (apply_spec f hf i₁) h_not_one
        · have := apply_spec_ne f hf i₁ j₁ h_eq
          exact absurd this h_zero
    have h₂ : g.toMatrix i₂ j₂ = 1 := by
      rw [h₁, one_mul] at h_prod
      exact h_prod
    -- By uniqueness of deterministic matrices
    have hj₁ : j₁ = f.apply hf i₁ := (hf i₁).choose_spec.2 j₁ h₁
    have hj₂ : j₂ = g.apply hg i₂ := (hg i₂).choose_spec.2 j₂ h₂
    simp [hj₁, hj₂]

/-- Apply function for tensor products of deterministic matrices. -/
theorem apply_tensor {m₁ n₁ m₂ n₂ : Type u} [Fintype m₁] [Fintype n₁] [Fintype m₂] [Fintype n₂]
    (f : StochasticMatrix m₁ n₁) (g : StochasticMatrix m₂ n₂)
    [DecidableEq n₁]
    (hf : f.isDeterministic) (hg : g.isDeterministic) (i₁ : m₁) (i₂ : m₂) :
    (tensor f g).apply (det_tensor_det f g hf hg) (i₁, i₂) =
    (f.apply hf i₁, g.apply hg i₂) := by
  -- By uniqueness in the proof of det_tensor_det
  have h := (det_tensor_det f g hf hg (i₁, i₂)).choose_spec
  have h_val : (tensor f g).toMatrix (i₁, i₂) (f.apply hf i₁, g.apply hg i₂) = 1 := by
    simp only [tensor]
    rw [apply_spec f hf i₁, apply_spec g hg i₂]
    simp
  exact h.2 _ h_val |>.symm

/-- Two deterministic matrices are equal if their apply functions agree. -/
theorem ext_deterministic {m n : Type u} [Fintype m] [Fintype n] [DecidableEq n]
    {f g : StochasticMatrix m n} (hf : f.isDeterministic) (hg : g.isDeterministic) :
    f = g ↔ ∀ i, f.apply hf i = g.apply hg i := by
  constructor
  · intro h i
    subst h
    rfl
  · intro h
    ext i j
    by_cases hj : j = f.apply hf i
    · rw [hj, apply_spec f hf i]
      have : g.apply hg i = f.apply hf i := (h i).symm
      rw [← this, apply_spec g hg i]
    · rw [apply_spec_ne f hf i j hj]
      have : j ≠ g.apply hg i := by
        rw [← h i]
        exact hj
      rw [apply_spec_ne g hg i j this]

end StochasticMatrix

/-! ### Deterministic morphisms as functions -/

/-- Bundle for deterministic stochastic matrices with their underlying function. -/
structure DetMorphism (m n : Type u) [Fintype m] [Fintype n] [DecidableEq n] where
  /-- The underlying function -/
  func : m → n
  /-- The stochastic matrix representation -/
  toStochastic : StochasticMatrix m n
  /-- Proof that the matrix is deterministic -/
  is_det : toStochastic.isDeterministic
  /-- The function agrees with the matrix -/
  spec : ∀ i, toStochastic.apply is_det i = func i

namespace DetMorphism

variable {m n p : Type u} [Fintype m] [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

/-- Create deterministic morphism from function. -/
def ofFunc (f : m → n) : DetMorphism m n :=
  let mat : StochasticMatrix m n := {
    toMatrix := fun i j => if f i = j then 1 else 0
    row_sum := fun i => by
      rw [Finset.sum_eq_single (f i)]
      · simp
      · intro j _ hj
        simp only [if_neg (Ne.symm hj)]
      · intro h; exfalso; exact h (Finset.mem_univ _)
  }
  let det : mat.isDeterministic := fun i => by
    use f i
    constructor
    · simp [mat]
    · intro j hj
      simp [mat] at hj
      exact hj.symm
  { func := f
    toStochastic := mat
    is_det := det
    spec := fun i => by
      unfold StochasticMatrix.apply
      -- The apply function returns the unique j with matrix entry 1
      have h_det := det i
      have h_spec := h_det.choose_spec
      have h_one : mat.toMatrix i (f i) = 1 := by simp [mat]
      exact h_spec.2 (f i) h_one |>.symm }

/-- Identity as deterministic morphism. -/
def id (m : Type u) [Fintype m] [DecidableEq m] : DetMorphism m m :=
  ofFunc _root_.id

/-- Composition of deterministic morphisms. -/
def comp (f : DetMorphism m n) (g : DetMorphism n p) : DetMorphism m p where
  func := g.func ∘ f.func
  toStochastic := StochasticMatrix.comp f.toStochastic g.toStochastic
  is_det := StochasticMatrix.det_comp_det f.toStochastic g.toStochastic f.is_det g.is_det
  spec := fun i => by
    rw [StochasticMatrix.det_comp_eq_fun_comp _ _ f.is_det g.is_det]
    simp [f.spec, g.spec]

/-- Tensor product of deterministic morphisms. -/
def tensor {m₁ n₁ m₂ n₂ : Type u} [Fintype m₁] [Fintype n₁] [Fintype m₂] [Fintype n₂]
    [DecidableEq n₁] [DecidableEq n₂] [DecidableEq (n₁ × n₂)]
    (f : DetMorphism m₁ n₁) (g : DetMorphism m₂ n₂) : DetMorphism (m₁ × m₂) (n₁ × n₂) where
  func := fun ⟨i₁, i₂⟩ => (f.func i₁, g.func i₂)
  toStochastic := StochasticMatrix.tensor f.toStochastic g.toStochastic
  is_det := StochasticMatrix.det_tensor_det f.toStochastic g.toStochastic f.is_det g.is_det
  spec := fun ⟨i₁, i₂⟩ => by
    rw [StochasticMatrix.apply_tensor _ _ f.is_det g.is_det]
    simp [f.spec, g.spec]

/-- Extensionality for deterministic morphisms. -/
@[ext]
theorem ext (f g : DetMorphism m n) (h : f.func = g.func) : f = g := by
  -- Two deterministic morphisms with the same function are equal
  have h_apply : ∀ i, f.toStochastic.apply f.is_det i = g.toStochastic.apply g.is_det i := by
    intro i
    rw [f.spec, g.spec, h]
  have h_mat := (StochasticMatrix.ext_deterministic f.is_det g.is_det).mpr h_apply
  cases f; cases g
  simp at h ⊢
  exact ⟨h, h_mat⟩

/-! ### Helper lemmas for reasoning about DetMorphisms -/

/-- Matrix entry of a DetMorphism. -/
@[simp]
lemma toMatrix_apply (f : DetMorphism m n) (i : m) (j : n) :
    f.toStochastic.toMatrix i j = if f.func i = j then 1 else 0 := by
  by_cases h : f.func i = j
  · rw [if_pos h]
    have hj : j = f.toStochastic.apply f.is_det i := by
      rw [f.spec i]
      exact h.symm
    rw [hj]
    exact StochasticMatrix.apply_spec f.toStochastic f.is_det i
  · rw [if_neg h]
    have hne : j ≠ f.toStochastic.apply f.is_det i := by
      rw [f.spec i]
      exact Ne.symm h
    exact StochasticMatrix.apply_spec_ne f.toStochastic f.is_det i j hne

/-- Composition of DetMorphisms as matrices. -/
lemma comp_toMatrix (f : DetMorphism m n) (g : DetMorphism n p)
    (i : m) (k : p) :
    (comp f g).toStochastic.toMatrix i k = if g.func (f.func i) = k then 1 else 0 := by
  simp only [comp]
  exact toMatrix_apply (comp f g) i k

/-- Tensor product of DetMorphisms as matrices. -/
lemma tensor_toMatrix {m₁ n₁ m₂ n₂ : Type u} [Fintype m₁] [Fintype n₁]
    [Fintype m₂] [Fintype n₂] [DecidableEq n₁] [DecidableEq n₂] [DecidableEq (n₁ × n₂)]
    (f : DetMorphism m₁ n₁) (g : DetMorphism m₂ n₂)
    (i : m₁ × m₂) (j : n₁ × n₂) :
    (tensor f g).toStochastic.toMatrix i j =
    if (f.func i.1, g.func i.2) = j then 1 else 0 := by
  simp only [tensor]
  exact toMatrix_apply (tensor f g) i j

/-- Identity composition left. -/
@[simp]
lemma id_comp [DecidableEq m] (f : DetMorphism m n) :
    comp (id m) f = f := by
  ext i
  simp [comp, id, ofFunc]

omit [DecidableEq n] in
/-- Identity composition right. -/
@[simp]
lemma comp_id [DecidableEq n] (f : DetMorphism m n) :
    comp f (id n) = f := by
  ext i
  simp [comp, id, ofFunc]

/-- Composition is associative. -/
lemma comp_assoc {q : Type u} [Fintype q] [DecidableEq q]
    (f : DetMorphism m n) (g : DetMorphism n p) (h : DetMorphism p q) :
    comp (comp f g) h = comp f (comp g h) := by
  ext i
  simp [comp]

end DetMorphism

/-- FinStoch: finite types with stochastic matrices. -/
structure FinStoch : Type (u+1) where
  /-- The underlying finite type. -/
  carrier : Type u
  /-- Proof that the carrier is finite. -/
  [fintype : Fintype carrier]
  /-- Decidable equality for the carrier type. -/
  [decidableEq : DecidableEq carrier]

namespace FinStoch

instance (X : FinStoch) : Fintype X.carrier := X.fintype

instance (X : FinStoch) : DecidableEq X.carrier := X.decidableEq

/-- Morphisms are stochastic matrices. -/
abbrev Hom (X Y : FinStoch) := StochasticMatrix X.carrier Y.carrier

instance : CategoryStruct FinStoch where
  Hom := Hom
  id X := StochasticMatrix.id X.carrier
  comp f g := StochasticMatrix.comp f g

instance : Category FinStoch where
  id_comp f := by
    apply StochasticMatrix.ext
    ext i j
    simp only [CategoryStruct.comp, StochasticMatrix.comp, CategoryStruct.id]
    -- Identity selects row i
    rw [Finset.sum_eq_single i]
    · simp [StochasticMatrix.id]
    · intro k _ hk
      simp [StochasticMatrix.id]
      intro h
      exact absurd h (Ne.symm hk)
    · intro h
      exfalso
      exact h (Finset.mem_univ _)
  comp_id f := by
    apply StochasticMatrix.ext
    ext i j
    simp only [CategoryStruct.comp, StochasticMatrix.comp, CategoryStruct.id]
    -- Identity selects column j
    rw [Finset.sum_eq_single j]
    · simp [StochasticMatrix.id]
    · intro k _ hk
      simp [StochasticMatrix.id]
      intro h
      exact absurd h.symm (Ne.symm hk)
    · intro h
      exfalso
      exact h (Finset.mem_univ _)
  assoc f g h := by
    apply StochasticMatrix.ext
    ext i k
    simp only [CategoryStruct.comp, StochasticMatrix.comp]
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]

/-- Singleton type as tensor unit. -/
def tensorUnit : FinStoch where
  carrier := Unit

/-- Tensor product of objects. -/
def tensorObj (X Y : FinStoch) : FinStoch where
  carrier := X.carrier × Y.carrier

/-! ### Structural morphisms as deterministic morphisms -/

section Structural

/-- Associator as deterministic morphism. -/
def associatorDet (X Y Z : FinStoch) :
    DetMorphism ((X.tensorObj Y).tensorObj Z).carrier (X.tensorObj (Y.tensorObj Z)).carrier :=
  DetMorphism.ofFunc fun ⟨⟨x, y⟩, z⟩ => (x, (y, z))

/-- Inverse associator as deterministic morphism. -/
def associatorInvDet (X Y Z : FinStoch) :
    DetMorphism (X.tensorObj (Y.tensorObj Z)).carrier ((X.tensorObj Y).tensorObj Z).carrier :=
  DetMorphism.ofFunc fun ⟨x, ⟨y, z⟩⟩ => ((x, y), z)

/-- Left unitor as deterministic morphism. -/
def leftUnitorDet (X : FinStoch) :
    DetMorphism (tensorUnit.tensorObj X).carrier X.carrier :=
  DetMorphism.ofFunc fun ⟨_, x⟩ => x

/-- Inverse left unitor as deterministic morphism. -/
def leftUnitorInvDet (X : FinStoch) :
    DetMorphism X.carrier (tensorUnit.tensorObj X).carrier :=
  DetMorphism.ofFunc fun x => ((), x)

/-- Right unitor as deterministic morphism. -/
def rightUnitorDet (X : FinStoch) :
    DetMorphism (X.tensorObj tensorUnit).carrier X.carrier :=
  DetMorphism.ofFunc fun ⟨x, _⟩ => x

/-- Inverse right unitor as deterministic morphism. -/
def rightUnitorInvDet (X : FinStoch) :
    DetMorphism X.carrier (X.tensorObj tensorUnit).carrier :=
  DetMorphism.ofFunc fun x => (x, ())

/-- Swap/braiding as deterministic morphism. -/
def swapDet (X Y : FinStoch) :
    DetMorphism (X.tensorObj Y).carrier (Y.tensorObj X).carrier :=
  DetMorphism.ofFunc fun ⟨x, y⟩ => (y, x)

/-! ### Properties of structural morphisms -/

/-- Associator and its inverse compose to identity. -/
theorem associatorDet_comp_inv (X Y Z : FinStoch) :
    (associatorDet X Y Z).func ∘ (associatorInvDet X Y Z).func = _root_.id := by
  ext ⟨x, ⟨y, z⟩⟩
  rfl

/-- Swap is involutive. -/
theorem swapDet_involutive (X Y : FinStoch) :
    (swapDet X Y).func ∘ (swapDet Y X).func = _root_.id := by
  ext ⟨x, y⟩
  rfl

end Structural

end FinStoch

end CategoryTheory.MarkovCategory
