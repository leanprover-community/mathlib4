/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee, Junyan Xu
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.Flat.Tensor

/-! # The equational criterion for flatness

Let $M$ be a module over a commutative ring $R$. Let us say that a relation
$\sum_{i \in \iota} f_i x_i = 0$ in $M$ is *trivial* (`Module.IsTrivialRelation`) if there exist a
finite index type $\kappa$ = `Fin k`, elements $(y_j)_{j \in \kappa}$ of $M$,
and elements $(a_{ij})_{i \in \iota, j \in \kappa}$ of $R$ such that for all $i$,
$$x_i = \sum_j a_{ij} y_j$$
and for all $j$,
$$\sum_i f_i a_{ij} = 0.$$

The *equational criterion for flatness* [Stacks 00HK](https://stacks.math.columbia.edu/tag/00HK)
(`Module.Flat.iff_forall_isTrivialRelation`) states that $M$ is flat if and only if every relation
in $M$ is trivial.

The equational criterion for flatness can be stated in the following form
(`Module.Flat.iff_forall_exists_factorization`). Let $M$ be an $R$-module. Then the following two
conditions are equivalent:
* $M$ is flat.
* For finite free modules $R^l$, all elements $f \in R^l$, and all linear maps
  $x \colon R^l \to M$ such that $x(f) = 0$, there exist a finite free module $R^k$ and
  linear maps $a \colon R^l \to R^k$ and $y \colon R^k \to M$ such
  that $x = y \circ a$ and $a(f) = 0$.

Of course, the module $R^l$ in this statement can be replaced by an arbitrary free module
(`Module.Flat.exists_factorization_of_apply_eq_zero_of_free`).

We also have the following strengthening of the equational criterion for flatness
(`Module.Flat.exists_factorization_of_comp_eq_zero_of_free`): Let $M$ be a
flat module. Let $K$ and $N$ be finite $R$-modules with $N$ free, and let $f \colon K \to N$ and
$x \colon N \to M$ be linear maps such that $x \circ f = 0$. Then there exist a finite free module
$R^k$ and linear maps $a \colon N \to R^k$ and $y \colon R^k \to M$ such
that $x = y \circ a$ and $a \circ f = 0$. We recover the usual equational criterion for flatness if
$K = R$ and $N = R^l$. This is used in the proof of Lazard's theorem.

We conclude that every linear map from a finitely presented module to a flat module factors
through a finite free module (`Module.Flat.exists_factorization_of_isFinitelyPresented`), and
every finitely presented flat module is projective (`Module.Flat.projective_of_finitePresentation`).

## References

* [Stacks: Flat modules and flat ring maps](https://stacks.math.columbia.edu/tag/00H9)
* [Stacks: Characterizing flatness](https://stacks.math.columbia.edu/tag/058C)

-/

public section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

open LinearMap TensorProduct Finsupp

namespace Module

variable {ι : Type*} [Fintype ι] (f : ι → R) (x : ι → M)

/-- The proposition that the relation $\sum_i f_i x_i = 0$ in $M$ is trivial.
That is, there exist a finite index type $\kappa$ = `Fin k`, elements
$(y_j)_{j \in \kappa}$ of $M$, and elements $(a_{ij})_{i \in \iota, j \in \kappa}$ of $R$
such that for all $i$,
$$x_i = \sum_j a_{ij} y_j$$
and for all $j$,
$$\sum_i f_i a_{ij} = 0.$$
By `Module.sum_smul_eq_zero_of_isTrivialRelation`, this condition implies $\sum_i f_i x_i = 0$. -/
abbrev IsTrivialRelation : Prop :=
  ∃ (k : ℕ) (a : ι → Fin k → R) (y : Fin k → M),
    (∀ i, x i = ∑ j, a i j • y j) ∧ ∀ j, ∑ i, f i * a i j = 0

variable {f x}

/-- `Module.IsTrivialRelation` is equivalent to the predicate `TensorProduct.VanishesTrivially`
defined in `Mathlib/LinearAlgebra/TensorProduct/Vanishing.lean`. -/
theorem isTrivialRelation_iff_vanishesTrivially :
    IsTrivialRelation f x ↔ VanishesTrivially R f x := by
  simp only [IsTrivialRelation, VanishesTrivially, smul_eq_mul, mul_comm]

theorem _root_.Equiv.isTrivialRelation_comp {κ} [Fintype κ] (e : κ ≃ ι) :
    IsTrivialRelation (f ∘ e) (x ∘ e) ↔ IsTrivialRelation f x := by
  simp_rw [isTrivialRelation_iff_vanishesTrivially, e.vanishesTrivially_comp]

/-- If the relation given by $(f_i)_{i \in \iota}$ and $(x_i)_{i \in \iota}$ is trivial, then
$\sum_i f_i x_i$ is actually equal to $0$. -/
theorem sum_smul_eq_zero_of_isTrivialRelation (h : IsTrivialRelation f x) :
    ∑ i, f i • x i = 0 := by
  simpa using
    congr_arg (TensorProduct.lid R M) <|
      sum_tmul_eq_zero_of_vanishesTrivially R (isTrivialRelation_iff_vanishesTrivially.mp h)

end Module

namespace Module.Flat

variable (R M) in
/-- **Equational criterion for flatness**, combined form.

Let $M$ be a module over a commutative ring $R$. The following are equivalent:
* $M$ is flat.
* For all ideals $I \subseteq R$, the map $I \otimes M \to M$ is injective.
* Every $\sum_i f_i \otimes x_i$ that vanishes in $R \otimes M$ vanishes trivially.
* Every relation $\sum_i f_i x_i = 0$ in $M$ is trivial.
* For all finite free modules $R^l$, all elements $f \in R^l$, and all linear maps
  $x \colon R^l \to M$ such that $x(f) = 0$, there exist a finite free module $R^k$ and
  linear maps $a \colon R^l \to R^k$ and $y \colon R^k \to M$ such
  that $x = y \circ a$ and $a(f) = 0$.
-/
@[stacks 00HK, stacks 058D "(1) ↔ (2)"]
theorem tfae_equational_criterion : List.TFAE [
    Flat R M,
    ∀ I : Ideal R, Function.Injective (rTensor M I.subtype),
    ∀ {l : ℕ} {f : Fin l → R} {x : Fin l → M}, ∑ i, f i ⊗ₜ x i = (0 : R ⊗[R] M) →
      VanishesTrivially R f x,
    ∀ {l : ℕ} {f : Fin l → R} {x : Fin l → M}, ∑ i, f i • x i = 0 → IsTrivialRelation f x,
    ∀ {l : ℕ} {f : Fin l →₀ R} {x : (Fin l →₀ R) →ₗ[R] M}, x f = 0 →
      ∃ (k : ℕ) (a : (Fin l →₀ R) →ₗ[R] (Fin k →₀ R)) (y : (Fin k →₀ R) →ₗ[R] M),
        x = y ∘ₗ a ∧ a f = 0] := by
  classical
  tfae_have 1 ↔ 2 := iff_rTensor_injective'
  tfae_have 3 ↔ 2 := forall_vanishesTrivially_iff_forall_rTensor_injective R
  tfae_have 3 ↔ 4 := by
    simp [(TensorProduct.lid R M).injective.eq_iff.symm, isTrivialRelation_iff_vanishesTrivially]
  tfae_have 4 → 5
  | h₄, l, f, x, hfx => by
    let f' : Fin l → R := f
    let x' : Fin l → M := fun i ↦ x (single i 1)
    have := calc
      ∑ i, f' i • x' i
      _ = ∑ i, f i • x (single i 1) := rfl
      _ = x (∑ i, f i • Finsupp.single i 1) := by simp_rw [map_sum, map_smul]
      _ = x f := by simp_rw [smul_single, smul_eq_mul, mul_one, univ_sum_single]
      _ = 0 := hfx
    obtain ⟨k, a', y', ⟨ha'y', ha'⟩⟩ := h₄ this
    use k
    use Finsupp.linearCombination R (fun i ↦ equivFunOnFinite.symm (a' i))
    use Finsupp.linearCombination R y'
    constructor
    · apply Finsupp.basisSingleOne.ext
      intro i
      simpa [linearCombination_apply, sum_fintype, Finsupp.single_apply] using ha'y' i
    · ext j
      simp only [linearCombination_apply, zero_smul, implies_true, sum_fintype, finset_sum_apply]
      exact ha' j
  tfae_have 5 → 4
  | h₅, l, f, x, hfx => by
    let f' : Fin l →₀ R := equivFunOnFinite.symm f
    let x' : (Fin l →₀ R) →ₗ[R] M := Finsupp.linearCombination R x
    have : x' f' = 0 := by simpa [x', f', linearCombination_apply, sum_fintype] using hfx
    obtain ⟨k, a', y', ha'y', ha'⟩ := h₅ this
    refine ⟨k, fun i ↦ a' (single i 1), fun j ↦ y' (single j 1), fun i ↦ ?_, fun j ↦ ?_⟩
    · simpa [x', ← map_smul, ← map_sum, smul_single] using
        LinearMap.congr_fun ha'y' (Finsupp.single i 1)
    · simp_rw [← smul_eq_mul, ← Finsupp.smul_apply, ← map_smul, ← finset_sum_apply, ← map_sum,
        smul_single, smul_eq_mul, mul_one,
        ← (fun _ ↦ equivFunOnFinite_symm_apply_apply _ _ : ∀ x, f' x = f x), univ_sum_single]
      simpa using DFunLike.congr_fun ha' j
  tfae_finish

/-- **Equational criterion for flatness**:
a module $M$ is flat if and only if every relation $\sum_i f_i x_i = 0$ in $M$ is trivial. -/
@[stacks 00HK]
theorem iff_forall_isTrivialRelation : Flat R M ↔ ∀ {l : ℕ} {f : Fin l → R} {x : Fin l → M},
    ∑ i, f i • x i = 0 → IsTrivialRelation f x :=
  (tfae_equational_criterion R M).out 0 3

/-- **Equational criterion for flatness**, forward direction.

If $M$ is flat, then every relation $\sum_i f_i x_i = 0$ in $M$ is trivial. -/
@[stacks 00HK]
theorem isTrivialRelation_of_sum_smul_eq_zero [Flat R M] {ι : Type*} [Fintype ι] {f : ι → R}
    {x : ι → M} (h : ∑ i, f i • x i = 0) : IsTrivialRelation f x :=
  (Fintype.equivFin ι).symm.isTrivialRelation_comp.mp <| iff_forall_isTrivialRelation.mp ‹_› <| by
    simpa only [← (Fintype.equivFin ι).symm.sum_comp] using h

/-- **Equational criterion for flatness**, backward direction.

If every relation $\sum_i f_i x_i = 0$ in $M$ is trivial, then $M$ is flat. -/
@[stacks 00HK]
theorem of_forall_isTrivialRelation (hfx : ∀ {l : ℕ} {f : Fin l → R} {x : Fin l → M},
    ∑ i, f i • x i = 0 → IsTrivialRelation f x) : Flat R M :=
  iff_forall_isTrivialRelation.mpr hfx

/-- **Equational criterion for flatness**, alternate form.

A module $M$ is flat if and only if for all finite free modules $R^l$,
all $f \in R^l$, and all linear maps $x \colon R^l \to M$ such that $x(f) = 0$, there
exist a finite free module $R^k$ and linear maps $a \colon R^l \to R^k$ and
$y \colon R^k \to M$ such that $x = y \circ a$ and $a(f) = 0$. -/
@[stacks 058D "(1) ↔ (2)"]
theorem iff_forall_exists_factorization : Flat R M ↔
    ∀ {l : ℕ} {f : Fin l →₀ R} {x : (Fin l →₀ R) →ₗ[R] M}, x f = 0 →
      ∃ (k : ℕ) (a : (Fin l →₀ R) →ₗ[R] (Fin k →₀ R)) (y : (Fin k →₀ R) →ₗ[R] M),
        x = y ∘ₗ a ∧ a f = 0 := (tfae_equational_criterion R M).out 0 4

/-- **Equational criterion for flatness**, backward direction, alternate form.

Let $M$ be a module over a commutative ring $R$. Suppose that for all finite free modules $R^l$,
all $f \in R^l$, and all linear maps $x \colon R^l \to M$ such that $x(f) = 0$, there
exist a finite free module $R^k$ and linear maps $a \colon R^l \to R^k$ and
$y \colon R^k \to M$ such that $x = y \circ a$ and $a(f) = 0$. Then $M$ is flat. -/
@[stacks 058D "(2) → (1)"]
theorem of_forall_exists_factorization
    (h : ∀ {l : ℕ} {f : Fin l →₀ R} {x : (Fin l →₀ R) →ₗ[R] M}, x f = 0 →
      ∃ (k : ℕ) (a : (Fin l →₀ R) →ₗ[R] (Fin k →₀ R)) (y : (Fin k →₀ R) →ₗ[R] M),
      x = y ∘ₗ a ∧ a f = 0) : Flat R M := iff_forall_exists_factorization.mpr h

/-- **Equational criterion for flatness**, forward direction, second alternate form.

Let $M$ be a flat module over a commutative ring $R$. Let $N$ be a finite free module over $R$,
let $f \in N$, and let $x \colon N \to M$ be a linear map such that $x(f) = 0$. Then there exist a
finite free module $R^k$ and linear maps $a \colon N \to R^k$ and
$y \colon R^k \to M$ such that $x = y \circ a$ and $a(f) = 0$. -/
@[stacks 058D "(1) → (2)"]
theorem exists_factorization_of_apply_eq_zero_of_free [Flat R M] {N : Type*} [AddCommGroup N]
    [Module R N] [Free R N] [Module.Finite R N] {f : N} {x : N →ₗ[R] M} (h : x f = 0) :
    ∃ (k : ℕ) (a : N →ₗ[R] (Fin k →₀ R)) (y : (Fin k →₀ R) →ₗ[R] M), x = y ∘ₗ a ∧ a f = 0 :=
  have e := ((Module.Free.chooseBasis R N).reindex (Fintype.equivFin _)).repr.symm
  have ⟨k, a, y, hya, haf⟩ := iff_forall_exists_factorization.mp ‹Flat R M›
    (f := e.symm f) (x := x ∘ₗ e) (by simpa using h)
  ⟨k, a ∘ₗ e.symm, y, by rwa [← comp_assoc, LinearEquiv.eq_comp_toLinearMap_symm], haf⟩

private theorem exists_factorization_of_comp_eq_zero_of_free_aux [Flat R M] {K : Type*} {n : ℕ}
    [AddCommGroup K] [Module R K] [Module.Finite R K] {f : K →ₗ[R] Fin n →₀ R}
    {x : (Fin n →₀ R) →ₗ[R] M} (h : x ∘ₗ f = 0) :
    ∃ (k : ℕ) (a : (Fin n →₀ R) →ₗ[R] (Fin k →₀ R)) (y : (Fin k →₀ R) →ₗ[R] M),
      x = y ∘ₗ a ∧ a ∘ₗ f = 0 := by
  have (K' : Submodule R K) (hK' : K'.FG) : ∃ (k : ℕ) (a : (Fin n →₀ R) →ₗ[R] (Fin k →₀ R))
      (y : (Fin k →₀ R) →ₗ[R] M), x = y ∘ₗ a ∧ K' ≤ LinearMap.ker (a ∘ₗ f) := by
    induction K', hK' using Submodule.fg_induction generalizing n with
    | singleton k =>
      have : x (f k) = 0 := by simpa using LinearMap.congr_fun h k
      simpa using exists_factorization_of_apply_eq_zero_of_free this
    | sup K₁ K₂ _ _ ih₁ ih₂ =>
      obtain ⟨k₁, a₁, y₁, rfl, ha₁⟩ := ih₁ h
      have : y₁ ∘ₗ (a₁ ∘ₗ f) = 0 := by rw [← comp_assoc, h]
      obtain ⟨k₂, a₂, y₂, rfl, ha₂⟩ := ih₂ this
      use k₂, a₂ ∘ₗ a₁, y₂
      simp_rw [comp_assoc]
      exact ⟨trivial, sup_le (ha₁.trans (ker_le_ker_comp _ _)) ha₂⟩
  convert this ⊤ Finite.fg_top
  simp only [top_le_iff, ker_eq_top]

/-- Let $M$ be a flat module. Let $K$ and $N$ be finite $R$-modules with $N$
free, and let $f \colon K \to N$ and $x \colon N \to M$ be linear maps such that
$x \circ f = 0$. Then there exist a finite free module $R^k$ and linear maps
$a \colon N \to R^k$ and $y \colon R^k \to M$ such that $x = y \circ a$ and
$a \circ f = 0$. -/
@[stacks 058D "(1) → (4)"]
theorem exists_factorization_of_comp_eq_zero_of_free [Flat R M] {K N : Type*} [AddCommGroup K]
    [Module R K] [Module.Finite R K] [AddCommGroup N] [Module R N] [Free R N] [Module.Finite R N]
    {f : K →ₗ[R] N} {x : N →ₗ[R] M} (h : x ∘ₗ f = 0) :
    ∃ (k : ℕ) (a : N →ₗ[R] (Fin k →₀ R)) (y : (Fin k →₀ R) →ₗ[R] M),
      x = y ∘ₗ a ∧ a ∘ₗ f = 0 :=
  have e := ((Module.Free.chooseBasis R N).reindex (Fintype.equivFin _)).repr.symm
  have ⟨k, a, y, hya, haf⟩ := exists_factorization_of_comp_eq_zero_of_free_aux
    (f := e.symm ∘ₗ f) (x := x ∘ₗ e.toLinearMap) (by ext; simpa [comp_assoc] using congr($h _))
  ⟨k, a ∘ₗ e.symm, y, by rwa [← comp_assoc, LinearEquiv.eq_comp_toLinearMap_symm], by
    rwa [comp_assoc]⟩

/-- Every homomorphism from a finitely presented module to a flat module factors through a finite
free module. -/
@[stacks 058E "only if"]
theorem exists_factorization_of_isFinitelyPresented [Flat R M] {P : Type*} [AddCommGroup P]
    [Module R P] [FinitePresentation R P] (h₁ : P →ₗ[R] M) :
      ∃ (k : ℕ) (h₂ : P →ₗ[R] (Fin k →₀ R)) (h₃ : (Fin k →₀ R) →ₗ[R] M), h₁ = h₃ ∘ₗ h₂ := by
  have ⟨_, K, ϕ, hK⟩ := FinitePresentation.exists_fin R P
  haveI : Module.Finite R K := .of_fg hK
  have : (h₁ ∘ₗ ϕ.symm ∘ₗ K.mkQ) ∘ₗ K.subtype = 0 := by
    simp_rw [comp_assoc, (LinearMap.exact_subtype_mkQ K).linearMap_comp_eq_zero, comp_zero]
  obtain ⟨k, a, y, hay, ha⟩ := exists_factorization_of_comp_eq_zero_of_free this
  use k, (K.liftQ a (by rwa [← range_le_ker_iff, Submodule.range_subtype] at ha)) ∘ₗ ϕ, y
  apply (cancel_right ϕ.symm.surjective).mp
  apply (cancel_right K.mkQ_surjective).mp
  simpa [comp_assoc]

@[stacks 00NX "(1) → (2)"]
theorem projective_of_finitePresentation [Flat R M] [FinitePresentation R M] : Projective R M :=
  have ⟨_, f, g, eq⟩ := exists_factorization_of_isFinitelyPresented (.id (R := R) (M := M))
  .of_split f g eq.symm

end Module.Flat
