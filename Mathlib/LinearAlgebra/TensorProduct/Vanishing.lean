/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Vanishing of elements in a tensor product of two modules

Let $M$ and $N$ be modules over a commutative ring $R$. Recall that every element of $M \otimes N$
can be written as a finite sum $\sum_{i} m_i \otimes n_i$ of pure tensors
(`TensorProduct.exists_finset`). We would like to determine under what circumstances such an
expression vanishes.

Let us say that an expression $\sum_{i \in \iota} m_i \otimes n_i$ in $M \otimes N$
*vanishes trivially* (`TensorProduct.VanishesTrivially`) if there exist a finite index type
$\kappa$, elements $(y_j)_{j \in \kappa}$ of $N$, and elements
$(a_{ij})_{i \in \iota, j \in \kappa}$ of $R$ such that for all $i$,
$$n_i = \sum_j a_{ij} y_j$$
and for all $j$,
$$\sum_{i} a_{ij} m_i = 0.$$
(The terminology "trivial" comes from [Stacks 00HK](https://stacks.math.columbia.edu/tag/00HK).)
It is not difficult to show (`TensorProduct.sum_tmul_eq_zero_of_vanishesTrivially`) that if
$\sum_i m_i \otimes n_i$ vanishes trivially, then it vanishes; that is,
$\sum_i m_i \otimes n_i = 0$.

The *equational criterion for vanishing* (`TensorProduct.vanishesTrivially_iff_sum_tmul_eq_zero`),
which appears as
[A. Altman and S. Kleiman, *A term of commutative algebra* (Lemma 8.16)][altman2021term],
states that if the elements $m_i$ generate the module $M$, then $\sum_i m_i \otimes n_i = 0$ if and
only if the expression $\sum_i m_i \otimes n_i$ vanishes trivially.

We also prove the following generalization
(`TensorProduct.vanishesTrivially_iff_sum_tmul_eq_zero_of_rTensor_injective`). If the submodule
$M' \subseteq M$ generated by the $m_i$ satisfies the property that the induced map
$M' \otimes N \to M \otimes N$ is injective, then $\sum_i m_i \otimes n_i = 0$ if and only if the
expression $\sum_i m_i \otimes n_i$ vanishes trivially. (In the case that $M = R$, this yields the
*equational criterion for flatness* `Module.Flat.iff_forall_isTrivialRelation`.)

Conversely (`TensorProduct.rTensor_injective_of_forall_vanishesTrivially`),
suppose that for every equation $\sum_i m_i \otimes n_i = 0$, the expression
$\sum_i m_i \otimes n_i$ vanishes trivially. Then the induced map $M' \otimes N \to M \otimes N$
is injective for every submodule $M' \subseteq M$.

## References

* [A. Altman and S. Kleiman, *A term of commutative algebra* (Lemma 8.16)][altman2021term]

## TODO

* Prove the same theorems with $M$ and $N$ swapped.
* Prove the same theorems with universe polymorphism.

-/

universe u

variable (R : Type u) [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {N : Type u} [AddCommGroup N] [Module R N]

open Classical DirectSum LinearMap Function Submodule

namespace TensorProduct

variable {ι : Type u} [Fintype ι] {m : ι → M} {n : ι → N}

variable (m n) in
/-- An expression $\sum_i m_i \otimes n_i$ in $M \otimes N$
*vanishes trivially* if there exist a finite index type $\kappa$,
elements $(y_j)_{j \in \kappa}$ of $N$, and elements $(a_{ij})_{i \in \iota, j \in \kappa}$ of $R$
such that for all $i$,
$$n_i = \sum_j a_{ij} y_j$$
and for all $j$,
$$\sum_{i} a_{ij} m_i = 0.$$
Note that this condition is not symmetric in $M$ and $N$.
(The terminology "trivial" comes from [Stacks 00HK](https://stacks.math.columbia.edu/tag/00HK).)-/
abbrev VanishesTrivially : Prop :=
  ∃ (κ : Type u) (_ : Fintype κ) (a : ι → κ → R) (y : κ → N),
    (∀ i, n i = ∑ j, a i j • y j) ∧ ∀ j, ∑ i, a i j • m i = 0

/-- **Equational criterion for vanishing**
[A. Altman and S. Kleiman, *A term of commutative algebra* (Lemma 8.16)][altman2021term],
backward direction.

If the expression $\sum_i m_i \otimes n_i$ vanishes trivially, then it vanishes.
That is, $\sum_i m_i \otimes n_i = 0$. -/
theorem sum_tmul_eq_zero_of_vanishesTrivially (hmn : VanishesTrivially R m n) :
    ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N) := by
  obtain ⟨κ, _, a, y, h₁, h₂⟩ := hmn
  simp_rw [h₁, tmul_sum, tmul_smul]
  rw [Finset.sum_comm]
  simp_rw [← tmul_smul, ← smul_tmul, ← sum_tmul, h₂, zero_tmul, Finset.sum_const_zero]

/-- **Equational criterion for vanishing**
[A. Altman and S. Kleiman, *A term of commutative algebra* (Lemma 8.16)][altman2021term],
forward direction.

Assume that the $m_i$ generate $M$. If the expression $\sum_i m_i \otimes n_i$
vanishes, then it vanishes trivially. -/
theorem vanishesTrivially_of_sum_tmul_eq_zero (hm : Submodule.span R (Set.range m) = ⊤)
    (hmn : ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N)) : VanishesTrivially R m n := by
  -- Define a map $G \colon R^\iota \to M$ whose matrix entries are the $m_i$. It is surjective.
  set G : (ι →₀ R) →ₗ[R] M := Finsupp.total ι M R m with hG
  have G_basis_eq (i : ι) : G (Finsupp.single i 1) = m i := by simp [hG, toModule_lof]
  have G_surjective : Surjective G := by
    apply LinearMap.range_eq_top.mp
    apply top_le_iff.mp
    rw [← hm]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    use Finsupp.single i 1, G_basis_eq i
  /- Consider the element $\sum_i e_i \otimes n_i$ of $R^\iota \otimes N$. It is in the kernel of
  $R^\iota \otimes N \to M \otimes N$. -/
  set en : (ι →₀ R) ⊗[R] N := ∑ i, Finsupp.single i 1 ⊗ₜ n i with hen
  have en_mem_ker : en ∈ ker (rTensor N G) := by simp [hen, G_basis_eq, hmn]
  -- We have an exact sequence $\ker G \to R^\iota \to M \to 0$.
  have exact_ker_subtype : Exact (ker G).subtype G := G.exact_subtype_ker_map
  -- Tensor the exact sequence with $N$.
  have exact_rTensor_ker_subtype : Exact (rTensor N (ker G).subtype) (rTensor N G) :=
    rTensor_exact (M := ↥(ker G)) N exact_ker_subtype G_surjective
  /- We conclude that $\sum_i e_i \otimes n_i$ is in the range of
    $\ker G \otimes N \to R^\iota \otimes N$. -/
  have en_mem_range : en ∈ range (rTensor N (ker G).subtype) :=
    exact_rTensor_ker_subtype.linearMap_ker_eq ▸ en_mem_ker
  /- There is an element of in $\ker G \otimes N$ that maps to $\sum_i e_i \otimes n_i$.
  Write it as a finite sum of pure tensors. -/
  obtain ⟨kn, hkn⟩ := en_mem_range
  obtain ⟨ma, rfl : kn = ∑ kj ∈ ma, kj.1 ⊗ₜ[R] kj.2⟩ := exists_finset kn
  use ↑↑ma, FinsetCoe.fintype ma
  /- Let $\sum_j k_j \otimes y_j$ be the sum obtained in the previous step.
  In order to show that $\sum_i m_i \otimes n_i$ vanishes trivially, it suffices to prove that there
  exist $(a_{ij})_{i, j}$ such that for all $i$,
  $$n_i = \sum_j a_{ij} y_j$$
  and for all $j$,
  $$\sum_{i} a_{ij} m_i = 0.$$
  For this, take $a_{ij}$ to be the coefficient of $e_i$ in $k_j$. -/
  use fun i ⟨⟨kj, _⟩, _⟩ ↦ (kj : ι →₀ R) i
  use fun ⟨⟨_, yj⟩, _⟩ ↦ yj
  constructor
  · intro i
    apply_fun finsuppScalarLeft R N ι at hkn
    apply_fun (· i) at hkn
    symm at hkn
    simp only [map_sum, finsuppScalarLeft_apply_tmul, zero_smul, Finsupp.single_zero,
      Finsupp.sum_single_index, one_smul, Finsupp.finset_sum_apply, Finsupp.single_apply,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, rTensor_tmul, coeSubtype, Finsupp.sum_apply,
      Finsupp.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, ite_not, en] at hkn
    simp only [Finset.univ_eq_attach, Finset.sum_attach ma (fun x ↦ (x.1 : ι →₀ R) i • x.2)]
    convert hkn using 2 with x _
    split
    · next h'x => rw [h'x, zero_smul]
    · rfl
  · rintro ⟨⟨⟨k, hk⟩, _⟩, _⟩
    simpa only [hG, Finsupp.total_apply, zero_smul, implies_true, Finsupp.sum_fintype] using
      mem_ker.mp hk

/-- **Equational criterion for vanishing**
[A. Altman and S. Kleiman, *A term of commutative algebra* (Lemma 8.16)][altman2021term].

Assume that the $m_i$ generate $M$. Then the expression $\sum_i m_i \otimes n_i$ vanishes
trivially if and only if it vanishes. -/
theorem vanishesTrivially_iff_sum_tmul_eq_zero (hm : Submodule.span R (Set.range m) = ⊤) :
    VanishesTrivially R m n ↔ ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N) :=
  ⟨sum_tmul_eq_zero_of_vanishesTrivially R, vanishesTrivially_of_sum_tmul_eq_zero R hm⟩

/-- **Equational criterion for vanishing**
[A. Altman and S. Kleiman, *A term of commutative algebra* (Lemma 8.16)][altman2021term],
forward direction, generalization.

Assume that the submodule $M' \subseteq M$ generated by the $m_i$
satisfies the property that the map $M' \otimes N \to M \otimes N$ is injective. If the expression
$\sum_i m_i \otimes n_i$ vanishes, then it vanishes trivially. -/
theorem vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective
    (hm : Injective (rTensor N (span R (Set.range m)).subtype))
    (hmn : ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N)) : VanishesTrivially R m n := by
  -- Restrict `m` on the codomain to $M'$, then apply `vanishesTrivially_of_sum_tmul_eq_zero`.
  have mem_M' i : m i ∈ span R (Set.range m) := subset_span ⟨i, rfl⟩
  set m' : ι → span R (Set.range m) := Subtype.coind m mem_M' with m'_eq
  have hm' : span R (Set.range m') = ⊤ := by
    apply map_injective_of_injective (injective_subtype (span R (Set.range m)))
    rw [Submodule.map_span, Submodule.map_top, range_subtype, coeSubtype, ← Set.range_comp]
    rfl
  have hm'n : ∑ i, m' i ⊗ₜ n i = (0 : span R (Set.range m) ⊗[R] N) := by
    apply hm
    simp only [m'_eq, map_sum, rTensor_tmul, coeSubtype, Subtype.coind_coe, _root_.map_zero, hmn]
  have : VanishesTrivially R m' n := vanishesTrivially_of_sum_tmul_eq_zero R hm' hm'n
  unfold VanishesTrivially at this ⊢
  convert this with κ _ a y j
  convert (injective_iff_map_eq_zero' _).mp (injective_subtype (span R (Set.range m))) _
  simp [m'_eq]

/-- **Equational criterion for vanishing**
[A. Altman and S. Kleiman, *A term of commutative algebra* (Lemma 8.16)][altman2021term],
generalization.

Assume that the submodule $M' \subseteq M$ generated by the $m_i$ satisfies the
property that the map $M' \otimes N \to M \otimes N$ is injective. Then the expression
$\sum_i m_i \otimes n_i$ vanishes trivially if and only if it vanishes. -/
theorem vanishesTrivially_iff_sum_tmul_eq_zero_of_rTensor_injective
    (hm : Injective (rTensor N (span R (Set.range m)).subtype)) :
    VanishesTrivially R m n ↔ ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N) :=
  ⟨sum_tmul_eq_zero_of_vanishesTrivially R,
    vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective R hm⟩

/-- Converse of `TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective`.

Assume that every expression $\sum_i m_i \otimes n_i$ which vanishes also vanishes trivially.
Then, for every submodule $M' \subseteq M$, the map $M' \otimes N \to M \otimes N$ is injective. -/
theorem rTensor_injective_of_forall_vanishesTrivially
    (hMN : ∀ {ι : Type u} [Fintype ι] {m : ι → M} {n : ι → N},
      ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N) → VanishesTrivially R m n)
    (M' : Submodule R M) : Injective (rTensor N M'.subtype) := by
  apply (injective_iff_map_eq_zero _).mpr
  rintro x hx
  obtain ⟨s, rfl⟩ := exists_finset x
  rw [← Finset.sum_attach]
  apply sum_tmul_eq_zero_of_vanishesTrivially
  simp only [map_sum, rTensor_tmul, coeSubtype] at hx
  have := hMN ((Finset.sum_attach s _).trans hx)
  unfold VanishesTrivially at this ⊢
  convert this with κ _ a y j
  symm
  convert (injective_iff_map_eq_zero' _).mp (injective_subtype M') _
  simp

/-- Every expression $\sum_i m_i \otimes n_i$ which vanishes also vanishes trivially if and only if
for every submodule $M' \subseteq M$, the map $M' \otimes N \to M \otimes N$ is injective. -/
theorem forall_vanishesTrivially_iff_forall_rTensor_injective :
    (∀ {ι : Type u} [Fintype ι] {m : ι → M} {n : ι → N},
      ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N) → VanishesTrivially R m n) ↔
    ∀ M' : Submodule R M, Injective (rTensor N M'.subtype) := by
  constructor
  · intro h
    exact rTensor_injective_of_forall_vanishesTrivially R h
  · intro h ι _ m n hmn
    exact vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective R (h _) hmn

/-- Every expression $\sum_i m_i \otimes n_i$ which vanishes also vanishes trivially if and only if
for every finitely generated submodule $M' \subseteq M$, the map $M' \otimes N \to M \otimes N$ is
injective. -/
theorem forall_vanishesTrivially_iff_forall_FG_rTensor_injective :
    (∀ {ι : Type u} [Fintype ι] {m : ι → M} {n : ι → N},
      ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N) → VanishesTrivially R m n) ↔
    ∀ (M' : Submodule R M) (_ : M'.FG), Injective (rTensor N M'.subtype) := by
  constructor
  · intro h M' _
    exact rTensor_injective_of_forall_vanishesTrivially R h M'
  · intro h ι _ m n hmn
    exact vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective R
      (h _ (fg_span (Set.finite_range _))) hmn

/-- If the map $M' \otimes N \to M \otimes N$ is injective for every finitely generated submodule
$M' \subseteq M$, then it is in fact injective for every submodule $M' \subseteq M$. -/
theorem rTensor_injective_of_forall_FG_rTensor_injective
    (hMN : ∀ (M' : Submodule R M) (_ : M'.FG), Injective (rTensor N M'.subtype))
    (M' : Submodule R M) : Injective (rTensor N M'.subtype) :=
  (forall_vanishesTrivially_iff_forall_rTensor_injective R).mp
    ((forall_vanishesTrivially_iff_forall_FG_rTensor_injective R).mpr hMN) M'

end TensorProduct
