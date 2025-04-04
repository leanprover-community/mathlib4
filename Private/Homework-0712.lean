import Mathlib.GroupTheory.Coset
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Deprecated.Subgroup
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Algebra.Group.Subgroup.Pointwise

open MulAction Classical
open Pointwise

/-
Let $H$ be a subgroup of $G$ with index $n < \infty$. Then $G$ contains a proper normal subgroup of finite index.
-/
section Special_Example_071201
variable {G α : Type} [Group G] [MulAction G α] [Fintype G] {n : ℕ}
variable {A : Type} [MulAction G A]

def setStabilizer (s : Set A) : Subgroup G := sInf (Set.range (fun a : s => (MulAction.stabilizer G a.1)))

def MulAction.kernel (G A : Type) [Group G] [MulAction G A] : Subgroup G := setStabilizer (@Set.univ A)

--lemma 1. To show the if-if cases of an element in MulAction $\phi$ 's kernel
lemma mem_kernel_iff {x : G} {A : Type} [MulAction G A] : x ∈ MulAction.kernel G A ↔ ∀ a : A, x • a = a := by
  constructor
  · intro h a
    simp [MulAction.kernel,Set.mem_range,setStabilizer] at h
    exact h a
  · intro h
    simp only [MulAction.kernel,setStabilizer]
    simp only [Subgroup.mem_sInf, Set.mem_range, Subtype.exists, Set.mem_univ, exists_const,
      forall_exists_index, forall_apply_eq_imp_iff, MulAction.mem_stabilizer_iff]
    assumption

--lemma 2. Then we use $Noether's first isomorphism theorem$ on the homomoriphism of MulAction $\phi$
lemma kernel_of_permHom : MonoidHom.ker (MulAction.toPermHom G A) = MulAction.kernel G A := by
  ext x
  rw [MonoidHom.mem_ker,mem_kernel_iff]
  constructor
  · simp only [toPermHom_apply]
    intro h a
    rw [←MulAction.toPerm_apply x a, h]
    rfl
  · simp only [MulAction.toPermHom_apply]
    intro h
    ext y
    simp only [MulAction.toPerm_apply]
    exact h y

noncomputable instance quotient_equiv : G ⧸ (MulAction.kernel G A) ≃ (toPermHom G A).range := by
  have := QuotientGroup.quotientKerEquivRange (MulAction.toPermHom G A)
  exact ((Subgroup.quotientEquivOfEq (@kernel_of_permHom G _ A _) ).symm).trans (this.toEquiv)

--The main problem
example (H : Subgroup G)(_ : H.index = n) : ∃ (K : Subgroup G) , ∃ m : ℕ, K.index = m ∧ K.Normal := by
  --Consider the group of $ker \phi$
  let K := MulAction.kernel G (G ⧸ H)
  --We have $G/K \cong S_{G/H}$ by lemma2.
  have : G⧸K ≃ (toPermHom G (G ⧸ H)).range := quotient_equiv
  --So the index of $K$ is finite because $S_{G/H}$ is finite
  use K, Fintype.card (G ⧸ K)
  constructor
  · exact Subgroup.index_eq_card K
  · --Then we show $K$ is normal by $\forall n \in K,g \in G$,we have $g n g ^ {-1} \in K$ and we have done
    have : ∀ n, n ∈ K → ∀ g : G, g * n * g⁻¹ ∈ K := by
      intro n hn g
      show g * n * g⁻¹ ∈ MulAction.kernel G (G ⧸ H)
      have : ∀ x : (G ⧸ H) , n • x = x := mem_kernel_iff.mp hn
      have : ∀ a : (G ⧸ H), (g * n * g⁻¹) • a = a := by
        intro a
        calc
          _ = (g * n) • (g⁻¹ • a) := mul_smul (g * n) g⁻¹ a
          _ = g • (n • (g⁻¹ • a)) := mul_smul g n (g⁻¹ • a)
          _ = g • (g⁻¹ • a) := by rw [this (g⁻¹ • a)]
          _ = _ := smul_inv_smul g a
      exact mem_kernel_iff.mpr this
    exact { conj_mem := this }

end Special_Example_071201
