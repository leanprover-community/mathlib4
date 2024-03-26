/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Combinatorics.Optimization.ConstraintSatisfaction.Basic

/-!

# Expressive power of General-Valued Constraint Satisfaction Problems

In this file, expressive power of General-Valued Constraint Satisfaction Problems is defined and
its relationship with fractional polymorphisms is established.

Note that `ValuedCSP.expressivePower` isn't the standard definition of expressive power of VCSP
from the literature.
Usually, expressive power is defined using a VCSP instance where some variables are exposed and
other variables are minimized.
In this way, the whole instance becomes a cost function that can be used in other VCSP instances.
The standard definition would go as follows:
```
def ValuedCSP.expressivePower (Γ : ValuedCSP D C) : ValuedCSP D C :=
  { ⟨n, fun x => Finset.univ.inf' Finset.univ_nonempty (fun y => I.evalSolution (Sum.elim x y))⟩ |
    (n : ℕ) (μ : Type) (_ : DecidableEq μ) (_ : Fintype μ) (I : Γ.Instance (Fin n ⊕ μ)) }
```
The definition above is not implemented here because it does too many things at the same time.
Instead, we provide an inductive defition below.

-/

variable {D C : Type*} [Fintype D] [Nonempty D] [LinearOrderedAddCommMonoid C]

/-- A new VCSP template made of all functions expressible by `Γ`. -/
inductive ValuedCSP.expressivePower (Γ : ValuedCSP D C) : ValuedCSP D C
/-- Cost functions from `Γ` trivially belong to its expressive power. -/
| single {n : ℕ} {f : (Fin n → D) → C} (hf : ⟨n, f⟩ ∈ Γ) :
    Γ.expressivePower ⟨n, f⟩
/-- Sum of two cost functions from `Γ.expressivePower` belongs to the expressive power as well. -/
| double {n : ℕ} {f g} (hf : ⟨n, f⟩ ∈ Γ.expressivePower) (hg : ⟨n, g⟩ ∈ Γ.expressivePower) :
    Γ.expressivePower ⟨n, f+g⟩
/-- If you take an `n+1`-ary function from `Γ.expressivePower` and minimize its first argument,
    the resulting `n`-ary function belongs to the expressive power as well -/
| minimize {n : ℕ} {f : (Fin n.succ → D) → C} (hf : ⟨n.succ, f⟩ ∈ Γ.expressivePower) :
    Γ.expressivePower ⟨n, fun x : Fin n → D =>
      Finset.univ.inf' Finset.univ_nonempty (fun z : D => f (Matrix.vecCons z x))⟩
/-- Cost functions from `Γ.expressivePower` with remapped arguments belong to the expressive power
    as well. For example, you can define `f' x y = f y x x` for `⟨3, f⟩ ∈ Γ.expressivePower` and
    you get `⟨2, f'⟩ ∈ Γ.expressivePower`. -/
| remap {n n' : ℕ} {f : (Fin n → D) → C} (hf : ⟨n, f⟩ ∈ Γ.expressivePower) (τ : Fin n → Fin n') :
    Γ.expressivePower ⟨n', fun x : Fin n' → D => f (x ∘ τ)⟩

/-- Expressive power of a VCSP template subsumes the template. -/
lemma ValuedCSP.subset_expressivePower (Γ : ValuedCSP D C) :
    Γ ⊆ Γ.expressivePower := by
  intro F hF
  exact ValuedCSP.expressivePower.single hF

/-- Expressive power is an idempotent operation on VCSP templates. -/
lemma ValuedCSP.expressivePower_expressivePower (Γ : ValuedCSP D C) :
    Γ.expressivePower = Γ.expressivePower.expressivePower := by
  apply Set.eq_of_subset_of_subset
  · apply ValuedCSP.subset_expressivePower
  intro F hF
  induction hF with
  | single hf => exact hf
  | double _ _ ihf ihg => exact ValuedCSP.expressivePower.double ihf ihg
  | minimize _ ih => exact ValuedCSP.expressivePower.minimize ih
  | remap _ τ ih => exact ValuedCSP.expressivePower.remap ih τ

lemma Function.AdmitsFractional.minimize {m n : ℕ} {ω : FractionalOperation D m}
    {f : (Fin n.succ → D) → C} (hf : f.AdmitsFractional ω) :
    (fun x : Fin n → D =>
        Finset.univ.inf' Finset.univ_nonempty (fun z : D => f (Matrix.vecCons z x))
      ).AdmitsFractional ω := by
  intro x
  rw [← Multiset.sum_map_nsmul, Finset.smul_sum]
  simp_rw [←Finset.nsmul_inf']
  let z :=
    fun i : Fin m =>
      (Finset.exists_mem_eq_inf' Finset.univ_nonempty
        (fun d : D => ω.size • f (Matrix.vecCons d (x i)))
      ).choose
  specialize hf (fun i j => Matrix.vecCons (z i) (x i) j)
  rw [← Multiset.sum_map_nsmul, Finset.smul_sum] at hf
  convert_to
    ((ω.tt x).map (fun yᵢ : Fin n → D =>
      Finset.univ.inf' Finset.univ_nonempty (fun zᵢ : D => m • f (Matrix.vecCons zᵢ yᵢ)))).sum  ≤
    (Finset.univ.val.map (fun i : Fin m =>
      ω.size • f (fun j : Fin n.succ => Matrix.vecCons (z i) (x i) j))).sum
  · congr
    ext i
    exact (Finset.exists_mem_eq_inf' Finset.univ_nonempty _).choose_spec.right
  refine LE.le.trans ?_ hf
  simp_rw [FractionalOperation.tt, Multiset.map_map, Function.comp_apply]
  apply Multiset.sum_map_le_sum_map
  intro g _
  rw [Finset.nsmul_inf']
  apply nsmul_le_nsmul_right
  simp only [Finset.inf'_le_iff, Finset.mem_univ, true_and]
  use g z
  apply le_of_eq
  apply congr_arg
  ext i
  match i with
  | 0 => rfl
  | ⟨i'+1, _⟩ => rfl

lemma Function.AdmitsFractional.remap {m n n' : ℕ} {ω : FractionalOperation D m}
    {f : (Fin n → D) → C} (hf : f.AdmitsFractional ω) (τ : Fin n → Fin n') :
    (fun x : Fin n' → D => f (x ∘ τ)).AdmitsFractional ω := by
  intro x
  convert hf (fun i j => x i (τ j)) using 3
  unfold FractionalOperation.tt
  rewrite [Multiset.map_map, Multiset.map_map]
  rfl

lemma FractionalOperation.IsFractionalPolymorphismFor.expressivePower
    {Γ : ValuedCSP D C} {m : ℕ} {ω : FractionalOperation D m}
    (frpo : ω.IsFractionalPolymorphismFor Γ) :
    ω.IsFractionalPolymorphismFor Γ.expressivePower := by
  intro F hF
  induction hF with
  | single hf =>
    apply frpo
    exact hf
  | double _ _ ihf ihg =>
    intro x
    have summed := add_le_add (ihf x) (ihg x)
    rw [
      Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib,
      ← Multiset.sum_map_nsmul, ← Multiset.sum_map_nsmul, ← Multiset.sum_map_add
    ] at summed
    rw [Finset.smul_sum, ← Multiset.sum_map_nsmul]
    convert summed using 2 <;> simp
  | minimize _ ih =>
    exact ih.minimize
  | remap _ τ ih =>
    exact ih.remap τ
