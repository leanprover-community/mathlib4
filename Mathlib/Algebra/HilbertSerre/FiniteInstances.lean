/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.QuotientNoetherian

/-!
# Some finite result about modules
Let `R` be a noetherian and `A` an `R`-algebra and `S` a finite subset of `A`

- `R[S]` is also a noetherian ring.
- If `M` is an `A`-module, then `M` is also an `A[S]`-module by restricting the scalar action; if
  `M` is finite and annihilated by `S`, then `M` is also finite as an `A[S]`-module.

-/


variable (R A : Type*) [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]

local notation:max R"[" S "]" => (Algebra.adjoin R (S : Finset A) : Subalgebra R A)

section

variable {R A}

lemma Algebra.adjoin_isNoetherian (S : Finset A) :
    IsNoetherianRing R[S] := by
  let P := (MvPolynomial S R)
  haveI : IsNoetherianRing P := MvPolynomial.isNoetherianRing
  have eq1 : (MvPolynomial.aeval Subtype.val).range = R[S] := adjoin_eq_range R S.toSet |>.symm
  have eq2 : (MvPolynomial.aeval Subtype.val : P →ₐ[R] A).toRingHom.range = R[S].toSubring := by
    ext a
    simp only [AlgHom.toRingHom_eq_coe, RingHom.mem_range, RingHom.coe_coe,
      Subalgebra.mem_toSubring]
    rw [← eq1]
    simp only [AlgHom.mem_range]
    rfl
  have eq3 := RingHom.quotientKerEquivRange (MvPolynomial.aeval Subtype.val : P →ₐ[R] A).toRingHom
  rw [eq2] at eq3
  exact isNoetherianRing_of_ringEquiv (f := eq3)

end

section

variable [DecidableEq A]
variable (S : Finset A) (s : A) (hS : Algebra.adjoin R (insert s S) = (⊤ : Subalgebra R A))
variable (M : Type*) [AddCommMonoid M] [Module A M]

instance : IsNoetherianRing R[S] :=
  Algebra.adjoin_isNoetherian (R := R) S

instance : Module R[S] M :=
Module.compHom M ({
  toFun := Subtype.val
  map_one' := rfl
  map_mul' := by intros; rfl
  map_zero' := rfl
  map_add' := by intros; rfl
} : R[S] →+* A)

lemma Algebra.adjoin_smul_def (a : R[S]) (m : M) : a • m = (a : A) • m := rfl

lemma finite_adjoin_module_of_finite_module [Module.Finite A M] :
    Module.Finite R[insert s S] M :=
  let m : Module R[insert s S] M :=
  Module.compHom M
    ({ toFun := fun x ↦ (x : A)
       map_one' := rfl
       map_mul' := by intros; rfl
       map_zero' := rfl
       map_add' := by intros; rfl } : R[insert s S] →+* A)
  let a : Algebra A R[insert s S] :=
  (RingHom.toAlgebra
    { toFun := fun a ↦ ⟨a,  by simp only [Finset.coe_insert, hS, Algebra.mem_top]⟩
      map_one' := by ext; rfl
      map_mul' := by intros; ext; rfl
      map_zero' := by ext; rfl
      map_add' := by intros; ext; rfl })
  @Module.Finite.of_restrictScalars_finite A R[insert s S] M _ _ _ _ m a
    ⟨fun x y z ↦ by
      change (x * (y : A)) • z = x • ((y : A) • z)
      rw [mul_smul]⟩ _

open BigOperators

namespace Algebra.adjoin_module_finite_of_annihilating

variable {A} in
/--
if `f` maps `aᵢ` to `nᵢ`
then `f` represents the monomial `∏ᵢ aᵢ ^ nᵢ`
-/
def evalMonomial (f : A →₀ ℕ) : A :=
  ∏ a in f.support, a ^ (f a)

@[simp] lemma evalMonomial_zero : evalMonomial (A := A) 0 = 1 := by
  simp [evalMonomial]

lemma top_eq_span_monomial :
    (⊤ : Submodule R A) =
    Submodule.span R
      {a | ∃ (f : A →₀ ℕ), f.support ⊆ insert s S ∧ a = evalMonomial f } := by
  classical
  refine le_antisymm ?_ le_top
  rintro x -
  have hx : x ∈ (⊤ : Subalgebra R A) := ⟨⟩
  rw [← hS] at hx
  refine Algebra.adjoin_induction hx ?_ ?_ ?_ ?_
  · intro x hx
    refine Submodule.subset_span ⟨Finsupp.single x 1,
      Finsupp.support_single_subset.trans (by simpa), ?_⟩
    · delta evalMonomial
      have eq1 : (Finsupp.single x 1).support = {x} :=
        le_antisymm Finsupp.support_single_subset (by simp)
      simp [eq1]
  · intro r
    change (algebraMap R A r : A) ∈ Submodule.span R _
    rw [show (algebraMap R A r : A) = (r : R) • (1 : A) by rw [Algebra.smul_def, mul_one]]
    exact Submodule.smul_mem _ _ <| Submodule.subset_span ⟨0, by simp, by simp [evalMonomial]⟩
  · intro a b ha hb
    exact Submodule.add_mem _ ha hb
  · intro a b ha hb
    apply Submodule.span_induction₂ ha hb
    · rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
      refine Submodule.subset_span ⟨(f + g : A →₀ ℕ), ?_, ?_⟩
      · exact Finsupp.support_add (g₁ := f) (g₂ := g) |>.trans <|
          sup_le (α := Finset A) hf hg
      · simp only [evalMonomial, Finsupp.coe_add, Pi.add_apply]
        rw [Finset.prod_subset (h := hf), Finset.prod_subset (h := hg),
          Finset.prod_subset (h := (_ : (f + g).support ⊆ insert s S))]
        rotate_left
        · intro x _ hx2
          simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply, ne_eq, add_eq_zero,
            not_and, not_forall, not_not, exists_prop] at hx2
          rw [pow_add, hx2.1, hx2.2, pow_zero, one_mul]
        · exact Finsupp.support_add (g₁ := f) (g₂ := g) |>.trans <|
            sup_le (α := Finset A) hf hg
        · intro x _ hx2
          simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hx2
          rw [hx2, pow_zero]
        · intro x _ hx2
          simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hx2
          rw [hx2, pow_zero]

        simp_rw [pow_add]
        rw [Finset.prod_mul_distrib]
    · intro y
      rw [zero_mul]
      exact Submodule.zero_mem _
    · intro x
      rw [mul_zero]
      exact Submodule.zero_mem _
    · intro x₁ x₂ y hx₁ hx₂
      rw [add_mul]
      exact Submodule.add_mem _ hx₁ hx₂
    · intro x y₁ y₂ hy₁ hy₂
      rw [mul_add]
      exact Submodule.add_mem _ hy₁ hy₂
    · intro r x y h
      rw [Algebra.smul_mul_assoc]
      exact Submodule.smul_mem _ _ h
    · intro r x y h
      rw [Algebra.mul_smul_comm]
      exact Submodule.smul_mem _ _ h

end Algebra.adjoin_module_finite_of_annihilating

open Algebra.adjoin_module_finite_of_annihilating in
lemma Algebra.adjoin_module_finite_of_annihilating [Module.Finite A M]
    (ann : ∀ (m : M), s • m = 0) : Module.Finite R[S] M := by
  obtain ⟨S', hS'⟩ := (inferInstance : Module.Finite A M)
  use S'
  refine le_antisymm le_top ?_
  rintro x -
  have mem : x ∈ (⊤ : Submodule A M) := ⟨⟩
  rw [← hS', mem_span_set] at mem
  obtain ⟨c, hc, (rfl : ∑ i in c.support, _ • _ = x)⟩ := mem
  refine Submodule.sum_mem _ fun i hi ↦ ?_
  have mem1 : c i ∈ (⊤ : Submodule R A) := ⟨⟩
  rw [top_eq_span_monomial R A S s hS, mem_span_set] at mem1
  obtain ⟨r, hr1, (hr2 : ∑ j in r.support, _ • _ = _)⟩ := mem1
  rw [← hr2, Finset.sum_smul]
  refine Submodule.sum_mem _ fun j hj ↦ ?_

  specialize hr1 hj
  obtain ⟨f, hf, rfl⟩ := hr1
  let f1 : A →₀ ℕ := f.update s 0
  let f2 : A →₀ ℕ := Finsupp.single s (f s)

  have eq2 : evalMonomial f = evalMonomial f1 * evalMonomial f2 := by
    delta evalMonomial
    simp only [Finsupp.support_update_zero, Finsupp.coe_update]
    by_cases mem : s ∈ f.support
    · conv_lhs => rw [← Finset.insert_erase mem]
      rw [Finset.prod_insert (by simp), mul_comm]
      congr 1
      · refine Finset.prod_congr rfl fun i hi ↦ ?_
        rw [Function.update_apply, if_neg]
        rintro rfl
        simp only [Finset.mem_erase, ne_eq, not_true_eq_false, Finsupp.mem_support_iff,
          false_and] at hi

      · have eq1 : (Finsupp.single s (f s)).support = {s} := by
          ext a
          simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_singleton] at mem ⊢
          rw [Finsupp.single_apply]
          split_ifs with h
          · subst h
            aesop
          · aesop
        rw [eq1, Finset.prod_singleton, Finsupp.single_apply, if_pos rfl]
    · have eq1 : (Finsupp.single s (f s)).support = ∅ :=  by aesop
      rw [eq1, Finset.prod_empty, mul_one, Finset.prod_erase]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [Function.update_apply]
      split_ifs with h
      · subst h
        simp only [Finsupp.mem_support_iff, ne_eq, not_not, Finsupp.support_eq_empty,
          Finsupp.single_eq_zero] at mem eq1
        rw [eq1]
      · rfl
      rw [Function.update_apply, if_pos rfl, pow_zero]

  have h1 : evalMonomial f1 ∈ adjoin R S := by
    refine Subalgebra.prod_mem _ fun k hk ↦ Subalgebra.pow_mem _ ?_ _
    rw [mem_adjoin_iff]
    refine Subring.subset_closure <| Or.inr ?_
    simp only [Finsupp.support_update_zero, Finset.mem_erase, ne_eq] at hk
    specialize hf hk.2
    simp only [Finset.mem_insert] at hf
    exact hf.resolve_left hk.1

  rw [Algebra.smul_def, mul_smul,
    show algebraMap R A (r (evalMonomial f)) • evalMonomial f • i =
      (⟨algebraMap R A (r (evalMonomial f)), by
        rw [mem_adjoin_iff]
        exact Subring.subset_closure <| Or.inl ⟨r (evalMonomial f), rfl⟩⟩ : adjoin R S) •
      evalMonomial f • i from rfl]
  refine Submodule.smul_mem _ _ ?_
  rw [eq2, mul_smul,
    show evalMonomial f1 • evalMonomial f2 • i =
      (⟨evalMonomial f1, by exact h1⟩ : adjoin R S) • evalMonomial f2 • i from rfl]
  refine Submodule.smul_mem _ _ ?_

  by_cases mem : s ∈ f.support
  · delta evalMonomial
    have eq1 : (Finsupp.single s (f s)).support = {s} := by
      ext a
      simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_singleton] at mem ⊢
      rw [Finsupp.single_apply]
      split_ifs with h
      · subst h
        aesop
      · aesop
    rw [eq1, Finset.prod_singleton, Finsupp.single_apply, if_pos rfl]
    simp only [Finsupp.mem_support_iff, ne_eq] at mem
    have ineq1 : 0 < f s := by omega
    rw [show f s = (f s - 1) + 1 from Nat.succ_pred_eq_of_pos ineq1 |>.symm, pow_succ', mul_smul,
      ann, smul_zero]
    exact Submodule.zero_mem _
  · delta evalMonomial
    have eq1 : (Finsupp.single s (f s)).support = ∅ := by aesop
    rw [eq1, Finset.prod_empty,
      show (1 : A) • i = (⟨(1 : A), Subalgebra.one_mem _⟩ : adjoin R S) • i from rfl]
    exact Submodule.smul_mem _ _ <| Submodule.subset_span <| hc hi

end
