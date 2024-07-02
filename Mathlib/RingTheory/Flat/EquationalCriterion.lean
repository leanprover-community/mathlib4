/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.Algebra.Module.FinitePresentation

/-! # The equational criterion for flatness

Let $M$ be a module over a commutative ring $R$. Let us say that a relation
$\sum_{i \in \iota} f_i x_i = 0$ in $M$ is *trivial* (`Module.IsTrivialRelation`) if there exist a
finite index type $\kappa$, elements $(y_j)_{j \in \kappa}$ of $M$,
and elements $(a_{ij})_{i \in \iota, j \in \kappa}$ of $R$ such that for all $i$,
$$x_i = \sum_j a_{ij} y_j$$
and for all $j$,
$$\sum_{i} f_i a_{ij} = 0.$$

The *equational criterion for flatness* [Stacks 00HK](https://stacks.math.columbia.edu/tag/00HK)
(`Module.Flat.iff_forall_isTrivialRelation`) states that $M$ is flat if and only if every relation
in $M$ is trivial.

The equational criterion for flatness can be stated in the following form
(`Module.Flat.iff_forall_exists_factorization`). Let $M$ be an $R$-module. Then the following two
conditions are equivalent:
* $M$ is flat.
* For all finite index types $\iota$, all elements $f \in R^{\iota}$, and all homomorphisms
$x \colon R^{\iota} \to M$ such that $x(f) = 0$, there exist a finite index type $\kappa$ and module
homomorphisms $a \colon R^{\iota} \to R^{\kappa}$ and $y \colon R^{\kappa} \to M$ such
that $x = y \circ a$ and $a(f) = 0$.

Of course, the module $R^\iota$ in this statement can be replaced by an arbitrary free module
(`Module.Flat.exists_factorization_of_apply_eq_zero_of_free`).

We also have the following strengthening of the equational criterion for flatness
(`Module.Flat.exists_factorization_of_comp_eq_zero_of_free`): Let $M$ be a
flat module. Let $K$ and $N$ be finite $R$-modules with $N$ free, and let $f \colon K \to N$ and
$x \colon N \to M$ be homomorphisms such that $x \circ f = 0$. Then there exist a finite index type
$\kappa$ and module homomorphisms $a \colon N \to R^{\kappa}$ and $y \colon R^{\kappa} \to M$ such
that $x = y \circ a$ and $a \circ f = 0$. We recover the usual equational criterion for flatness if
$K = R$ and $N = R^\iota$. This is used in the proof of Lazard's theorem.

We conclude that every homomorphism from a finitely presented module to a flat module factors
through a finite free module (`Module.Flat.exists_factorization_of_isFinitelyPresented`).

## References

* [Stacks: Flat modules and flat ring maps](https://stacks.math.columbia.edu/tag/00H9)
* [Stacks: Characterizing flatness](https://stacks.math.columbia.edu/tag/058C)

-/

universe u

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

open Classical DirectSum LinearMap TensorProduct Finsupp
open scoped BigOperators

namespace Module

variable {ι : Type u} [Fintype ι] (f : ι → R) (x : ι → M)

/-- The proposition that the relation $\sum_i f_i x_i = 0$ in $M$ is trivial.
That is, there exist a finite index type $\kappa$, elements
$(y_j)_{j \in \kappa}$ of $M$, and elements $(a_{ij})_{i \in \iota, j \in \kappa}$ of $R$
such that for all $i$,
$$x_i = \sum_j a_{ij} y_j$$
and for all $j$,
$$\sum_{i} f_i a_{ij} = 0.$$
By `Module.sum_smul_eq_zero_of_isTrivialRelation`, this condition implies $\sum_i f_i x_i = 0$. -/
abbrev IsTrivialRelation : Prop :=
  ∃ (κ : Type u) (_ : Fintype κ) (a : ι → κ → R) (y : κ → M),
    (∀ i, x i = ∑ j, a i j • y j) ∧ ∀ j, ∑ i, f i * a i j = 0

variable {f x}

/-- `Module.IsTrivialRelation` is equivalent to the predicate `TensorProduct.VanishesTrivially`
defined in `Mathlib/LinearAlgebra/TensorProduct/Vanishing.lean`. -/
theorem isTrivialRelation_iff_vanishesTrivially :
    IsTrivialRelation f x ↔ VanishesTrivially R f x := by
  simp only [IsTrivialRelation, VanishesTrivially, smul_eq_mul, mul_comm]


/-- If the relation given by $(f_i)_{i \in \iota}$ and $(x_i)_{i \in \iota}$ is trivial, then
$\sum_{i} f_i x_i$ is actually equal to $0$. -/
theorem sum_smul_eq_zero_of_isTrivialRelation (h : IsTrivialRelation f x) :
    ∑ i, f i • x i = 0 := by
  simpa using
    congr_arg (TensorProduct.lid R M) <|
      sum_tmul_eq_zero_of_vanishesTrivially R (isTrivialRelation_iff_vanishesTrivially.mp h)

end Module

namespace Module.Flat

variable (R M) in
/-- **Equational criterion for flatness** [Stacks 00HK](https://stacks.math.columbia.edu/tag/00HK),
combined form.

Let $M$ be a module over a commutative ring $R$. The following are equivalent:
* $M$ is flat.
* For all ideals $I \subseteq R$, the map $I \otimes M \to M$ is injective.
* Every $\sum_i f_i \otimes x_i$ that vanishes in $R \otimes M$ vanishes trivially.
* Every relation $\sum_i f_i x_i = 0$ in $M$ is trivial.
* For all finite index types $\iota$, all elements $f \in R^{\iota}$, and all homomorphisms
$x \colon R^{\iota} \to M$ such that $x(f) = 0$, there exist a finite index type $\kappa$ and module
homomorphisms $a \colon R^{\iota} \to R^{\kappa}$ and $y \colon R^{\kappa} \to M$ such
that $x = y \circ a$ and $a(f) = 0$.
* For all finite free modules $N$, all elements $f \in N$, and all homomorphisms $x \colon N \to M$
such that $x(f) = 0$, there exist a finite index type $\kappa$ and module homomorphisms
$a \colon N \to R^{\kappa}$ and $y \colon R^{\kappa} \to M$ such that $x = y \circ a$ and
$a(f) = 0$. -/
theorem tfae_equational_criterion : List.TFAE [
    Flat R M,
    ∀ (I : Ideal R), Function.Injective ⇑(rTensor M (Submodule.subtype I)),
    ∀ {ι : Type u} [Fintype ι] {f : ι → R} {x : ι → M}, ∑ i, f i ⊗ₜ x i = (0 : R ⊗[R] M) →
      VanishesTrivially R f x,
    ∀ {ι : Type u} [Fintype ι] {f : ι → R} {x : ι → M}, ∑ i, f i • x i = 0 → IsTrivialRelation f x,
    ∀ {ι : Type u} [Fintype ι] {f : ι →₀ R} {x : (ι →₀ R) →ₗ[R] M}, x f = 0 →
      ∃ (κ : Type u) (_ : Fintype κ) (a : (ι →₀ R) →ₗ[R] (κ →₀ R)) (y : (κ →₀ R) →ₗ[R] M),
        x = y ∘ₗ a ∧ a f = 0,
    ∀ {N : Type u} [AddCommGroup N] [Module R N] [Free R N] [Finite R N] {f : N} {x : N →ₗ[R] M},
      x f = 0 →
        ∃ (κ : Type u) (_ : Fintype κ) (a : N →ₗ[R] (κ →₀ R)) (y : (κ →₀ R) →ₗ[R] M),
          x = y ∘ₗ a ∧ a f = 0] := by
  tfae_have 1 ↔ 2
  · exact iff_rTensor_injective' R M
  tfae_have 3 ↔ 2
  · exact forall_vanishesTrivially_iff_forall_rTensor_injective R
  tfae_have 3 ↔ 4
  · simp [(TensorProduct.lid R M).injective.eq_iff.symm, isTrivialRelation_iff_vanishesTrivially]
  tfae_have 4 → 5
  · intro h₄ ι hι f x hfx
    let f' : ι → R := f
    let x' : ι → M := fun i ↦ x (single i 1)
    have := calc
      ∑ i, f' i • x' i
      _ = ∑ i, f i • x (single i 1)         := rfl
      _ = x (∑ i, f i • Finsupp.single i 1) := by simp_rw [map_sum, map_smul]
      _ = x f                               := by
        simp_rw [smul_single, smul_eq_mul, mul_one, univ_sum_single]
      _ = 0                                 := hfx
    obtain ⟨κ, hκ, a', y', ⟨ha'y', ha'⟩⟩ := h₄ this
    use κ, hκ
    use Finsupp.total ι (κ →₀ R) R (fun i ↦ equivFunOnFinite.symm (a' i))
    use Finsupp.total κ M R y'
    constructor
    · apply Finsupp.basisSingleOne.ext
      intro i
      simpa [total_apply, sum_fintype, single_apply] using ha'y' i
    · ext j
      simp only [total_apply, zero_smul, implies_true, sum_fintype, finset_sum_apply]
      exact ha' j
  tfae_have 5 → 4
  · intro h₅ ι hi f x hfx
    let f' : ι →₀ R := equivFunOnFinite.symm f
    let x' : (ι →₀ R) →ₗ[R] M := Finsupp.total ι M R x
    have : x' f' = 0 := by simpa [x', f', total_apply, sum_fintype] using hfx
    obtain ⟨κ, hκ, a', y', ha'y', ha'⟩ := h₅ this
    refine ⟨κ, hκ, fun i ↦ a' (single i 1), fun j ↦ y' (single j 1), fun i ↦ ?_, fun j ↦ ?_⟩
    · simpa [x', ← map_smul, ← map_sum, smul_single] using
        LinearMap.congr_fun ha'y' (Finsupp.single i 1)
    · simp_rw [← smul_eq_mul, ← Finsupp.smul_apply, ← map_smul, ← finset_sum_apply, ← map_sum,
        smul_single, smul_eq_mul, mul_one,
        ← (fun _ ↦ equivFunOnFinite_symm_apply_toFun _ _ : ∀ x, f' x = f x), univ_sum_single]
      simpa using DFunLike.congr_fun ha' j
  tfae_have 5 → 6
  · intro h₅ N _ _ _ _ f x hfx
    have ϕ := Module.Free.repr R N
    have : (x ∘ₗ ϕ.symm) (ϕ f) = 0 := by simpa
    obtain ⟨κ, hκ, a', y, ha'y, ha'⟩ := h₅ this
    refine ⟨κ, hκ, a' ∘ₗ ϕ, y, ?_, ?_⟩
    · simpa [LinearMap.comp_assoc] using congrArg (fun g ↦ (g ∘ₗ ϕ : N →ₗ[R] M)) ha'y
    · simpa using ha'
  tfae_have 6 → 5
  · intro h₆ _ _ _ _ hfx
    exact h₆ hfx
  tfae_finish

/-- **Equational criterion for flatness** [Stacks 00HK](https://stacks.math.columbia.edu/tag/00HK).

A module $M$ is flat if and only if every relation $\sum_i f_i x_i = 0$ in $M$ is trivial. -/
theorem iff_forall_isTrivialRelation : Flat R M ↔ ∀ {ι : Type u} [Fintype ι] {f : ι → R}
    {x : ι → M}, ∑ i, f i • x i = 0 → IsTrivialRelation f x :=
  (tfae_equational_criterion R M).out 0 3

/-- **Equational criterion for flatness**
[Stacks 00HK](https://stacks.math.columbia.edu/tag/00HK), forward direction.

If $M$ is flat, then every relation $\sum_i f_i x_i = 0$ in $M$ is trivial. -/
theorem isTrivialRelation_of_sum_smul_eq_zero [Flat R M] {ι : Type u} [Fintype ι] {f : ι → R}
    {x : ι → M} (h : ∑ i, f i • x i = 0) : IsTrivialRelation f x :=
  iff_forall_isTrivialRelation.mp ‹Flat R M› h

/-- **Equational criterion for flatness**
[Stacks 00HK](https://stacks.math.columbia.edu/tag/00HK), backward direction.

If every relation $\sum_i f_i x_i = 0$ in $M$ is trivial, then $M$ is flat. -/
theorem of_forall_isTrivialRelation (hfx : ∀ {ι : Type u} [Fintype ι] {f : ι → R} {x : ι → M},
    ∑ i, f i • x i = 0 → IsTrivialRelation f x) : Flat R M :=
  iff_forall_isTrivialRelation.mpr hfx

/-- **Equational criterion for flatness**
[Stacks 00HK](https://stacks.math.columbia.edu/tag/00HK), alternate form.

A module $M$ is flat if and only if for all finite free modules $R^\iota$,
all $f \in R^{\iota}$, and all homomorphisms $x \colon R^{\iota} \to M$ such that $x(f) = 0$, there
exist a finite free module $R^\kappa$ and homomorphisms $a \colon R^{\iota} \to R^{\kappa}$ and
$y \colon R^{\kappa} \to M$ such that $x = y \circ a$ and $a(f) = 0$. -/
theorem iff_forall_exists_factorization : Flat R M ↔
    ∀ {ι : Type u} [Fintype ι] {f : ι →₀ R} {x : (ι →₀ R) →ₗ[R] M}, x f = 0 →
      ∃ (κ : Type u) (_ : Fintype κ) (a : (ι →₀ R) →ₗ[R] (κ →₀ R)) (y : (κ →₀ R) →ₗ[R] M),
        x = y ∘ₗ a ∧ a f = 0 := (tfae_equational_criterion R M).out 0 4

/-- **Equational criterion for flatness**
[Stacks 00HK](https://stacks.math.columbia.edu/tag/00HK), forward direction, alternate form.

Let $M$ be a flat module. Let $R^\iota$ be a finite free module, let $f \in R^{\iota}$ be an
element, and let $x \colon R^{\iota} \to M$ be a homomorphism such that $x(f) = 0$. Then there
exist a finite free module $R^\kappa$ and homomorphisms $a \colon R^{\iota} \to R^{\kappa}$ and
$y \colon R^{\kappa} \to M$ such that $x = y \circ a$ and $a(f) = 0$. -/
theorem exists_factorization_of_apply_eq_zero [Flat R M] {ι : Type u} [Fintype ι]
    {f : ι →₀ R} {x : (ι →₀ R) →ₗ[R] M} (h : x f = 0) :
    ∃ (κ : Type u) (_ : Fintype κ) (a : (ι →₀ R) →ₗ[R] (κ →₀ R)) (y : (κ →₀ R) →ₗ[R] M),
      x = y ∘ₗ a ∧ a f = 0 := iff_forall_exists_factorization.mp ‹Flat R M› h

/-- **Equational criterion for flatness**
[Stacks 00HK](https://stacks.math.columbia.edu/tag/00HK), backward direction, alternate form.

Let $M$ be a module over a commutative ring $R$. Suppose that for all finite free modules $R^\iota$,
all $f \in R^{\iota}$, and all homomorphisms $x \colon R^{\iota} \to M$ such that $x(f) = 0$, there
exist a finite free module $R^\kappa$ and homomorphisms $a \colon R^{\iota} \to R^{\kappa}$ and
$y \colon R^{\kappa} \to M$ such that $x = y \circ a$ and $a(f) = 0$. Then $M$ is flat. -/
theorem of_forall_exists_factorization (h : ∀ {ι : Type u} [Fintype ι] {f : ι →₀ R}
    {x : (ι →₀ R) →ₗ[R] M}, x f = 0 →
      ∃ (κ : Type u) (_ : Fintype κ) (a : (ι →₀ R) →ₗ[R] (κ →₀ R)) (y : (κ →₀ R) →ₗ[R] M),
      x = y ∘ₗ a ∧ a f = 0) : Flat R M := iff_forall_exists_factorization.mpr h

/-- **Equational criterion for flatness** [Stacks 00HK](https://stacks.math.columbia.edu/tag/00HK),
forward direction, second alternate form.

Let $M$ be a flat module over a commutative ring $R$. Let $N$ be a finite free module over $R$,
let $f \in N$, and let $x \colon N \to M$ be a homomorphism such that $x(f) = 0$. Then there exist a
finite index type $\kappa$ and module homomorphisms $a \colon N \to R^{\kappa}$ and
$y \colon R^{\kappa} \to M$ such that $x = y \circ a$ and $a(f) = 0$. -/
theorem exists_factorization_of_apply_eq_zero_of_free [Flat R M] {N : Type u}
    [AddCommGroup N] [Module R N] [Free R N] [Finite R N] {f : N} {x : N →ₗ[R] M} (h : x f = 0) :
    ∃ (κ : Type u) (_ : Fintype κ) (a : N →ₗ[R] (κ →₀ R)) (y : (κ →₀ R) →ₗ[R] M),
      x = y ∘ₗ a ∧ a f = 0 := by
  exact ((tfae_equational_criterion R M).out 0 5 rfl rfl).mp ‹Flat R M› h

/-- Let $M$ be a flat module. Let $K$ and $N$ be finite $R$-modules with $N$
free, and let $f \colon K \to N$ and $x \colon N \to M$ be homomorphisms such that
$x \circ f = 0$. Then there exist a finite index type $\kappa$ and module homomorphisms
$a \colon N \to R^{\kappa}$ and $y \colon R^{\kappa} \to M$ such that $x = y \circ a$ and
$a \circ f = 0$. -/
theorem exists_factorization_of_comp_eq_zero_of_free [Flat R M] {K N : Type u}
    [AddCommGroup K] [Module R K] [Finite R K] [AddCommGroup N] [Module R N] [Free R N] [Finite R N]
    {f : K →ₗ[R] N} {x : N →ₗ[R] M} (h : x ∘ₗ f = 0) :
    ∃ (κ : Type u) (_ : Fintype κ) (a : N →ₗ[R] (κ →₀ R)) (y : (κ →₀ R) →ₗ[R] M),
      x = y ∘ₗ a ∧ a ∘ₗ f = 0 := by
  have (K' : Submodule R K) (hK' : K'.FG) : ∃ (κ : Type u) (_ : Fintype κ) (a : N →ₗ[R] (κ →₀ R))
      (y : (κ →₀ R) →ₗ[R] M), x = y ∘ₗ a ∧ K' ≤ LinearMap.ker (a ∘ₗ f) := by
    revert N
    apply Submodule.fg_induction (P := _) (N := K') (hN := hK')
    · intro k N _ _ _ _ f x hfx
      have : x (f k) = 0 := by simpa using LinearMap.congr_fun hfx k
      simpa using exists_factorization_of_apply_eq_zero_of_free this
    · intro K₁ K₂ ih₁ ih₂ N _ _ _ _ f x hfx
      obtain ⟨κ₁, _, a₁, y₁, rfl, ha₁⟩ := ih₁ hfx
      have : y₁ ∘ₗ (a₁ ∘ₗ f) = 0 := by rw [← comp_assoc, hfx]
      obtain ⟨κ₂, hκ₂, a₂, y₂, rfl, ha₂⟩ := ih₂ this
      use κ₂, hκ₂, a₂ ∘ₗ a₁, y₂
      simp_rw [comp_assoc]
      exact ⟨trivial, sup_le (ha₁.trans (ker_le_ker_comp _ _)) ha₂⟩
  convert this ⊤ Finite.out
  simp only [top_le_iff, ker_eq_top]

/-- Every homomorphism from a finitely presented module to a flat module factors through a finite
free module. -/
theorem exists_factorization_of_isFinitelyPresented [Flat R M] {P : Type u} [AddCommGroup P]
    [Module R P] [FinitePresentation R P] (h₁ : P →ₗ[R] M) :
      ∃ (κ : Type u) (_ : Fintype κ) (h₂ : P →ₗ[R] (κ →₀ R)) (h₃ : (κ →₀ R) →ₗ[R] M),
        h₁ = h₃ ∘ₗ h₂ := by
  obtain ⟨L, _, _, K, ϕ, _, _, hK⟩ := FinitePresentation.equiv_quotient R P
  haveI : Finite R ↥K := Module.Finite.iff_fg.mpr hK
  have : (h₁ ∘ₗ ϕ.symm ∘ₗ K.mkQ) ∘ₗ K.subtype = 0 := by
    simp_rw [comp_assoc, (LinearMap.exact_subtype_mkQ K).linearMap_comp_eq_zero, comp_zero]
  obtain ⟨κ, hκ, a, y, hay, ha⟩ := exists_factorization_of_comp_eq_zero_of_free this
  use κ, hκ, (K.liftQ a (by rwa [← range_le_ker_iff, Submodule.range_subtype] at ha)) ∘ₗ ϕ, y
  apply (cancel_right ϕ.symm.surjective).mp
  apply (cancel_right K.mkQ_surjective).mp
  simpa [comp_assoc]

end Module.Flat
