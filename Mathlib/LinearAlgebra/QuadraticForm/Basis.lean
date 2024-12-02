/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Constructing a bilinear map from a quadratic map, given a basis

This file provides an alternative to `QuadraticMap.associated`; unlike that definition, this one
does not require `Invertible (2 : R)`. Unlike that definition, this only works in the presence of
a basis.
-/

namespace Finset
section Filter

variable {α β : Type* }
variable (p q : α → Prop) [DecidablePred p] [DecidablePred q] {s t : Finset α}

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β} [AddCommMonoid β]

theorem disjoint_of_not_and_on_set (h : ∀ x ∈ s.filter (fun x => p x ∨ q x), ¬ (p x ∧ q x)) :
    Disjoint (filter p s) (filter q s) := by
  rw [Disjoint]
  intro t htp htq
  simp only [bot_eq_empty, le_eq_subset, subset_empty]
  by_contra hn
  rw [← not_nonempty_iff_eq_empty] at hn
  rw [not_not] at hn
  obtain ⟨x, hx⟩ := hn
  simp at htp
  have e1 : p x := (mem_filter.mp (htp hx)).2
  have e2 : q x := (mem_filter.mp (htq hx)).2
  have e3 : filter p s ⊆ s := filter_subset p s
  have e4 : t ⊆ s := by exact fun ⦃a⦄ a_1 ↦ e3 (htp a_1)
  aesop


/-
theorem test1 (h : ∀ x ∈ s, ¬ (p x ∧ q x)) :
  s.filter (fun x => p x ∨ q x) = (s.filter p).disjUnion (s.filter q) (by
    apply disjoint_of_not_and_on_set
    exact fun x a ↦ h x a) := by
  aesop
-/

theorem sum_disjoint_filters_on_set (h : ∀ x ∈ s.filter (fun x => p x ∨ q x), ¬ (p x ∧ q x)) :
    (∑ x ∈ s with (p x ∨ q x), f x) = (∑ x ∈ s with p x, f x) + (∑ x ∈ s with q x, f x) := by
  rw [← sum_disjUnion (disjoint_of_not_and_on_set (fun x ↦ p x) (fun x ↦ q x) h)]
  apply sum_congr
  · aesop
  · exact fun x a ↦ rfl

end Filter

end Finset

section Prod

theorem xor_iff_or_and_not_and (P Q : Prop) : Xor' P Q ↔ (P ∨ Q) ∧ (¬ (P ∧ Q)) := by
  constructor
  · intro h
    rw [Xor'] at h
    aesop
  · intro h
    aesop

variable {ι₁ : Type*}
variable {ι₂ : Type*}

lemma ne_cases [LinearOrder ι₁] (i₁ j₁ : ι₁) : i₁ ≠ j₁ ↔ i₁ < j₁ ∨ j₁ < i₁ := ne_iff_lt_or_gt


/-- Off the diagonal in both components -/
def symOffDiag : Sym2 (ι₁ × ι₂) → Prop := Sym2.lift ⟨fun (i₁, i₂) (j₁, j₂) => i₁ ≠ j₁ ∧ i₂ ≠ j₂, by
  aesop⟩

theorem mk_symOffDiag_iff {x y : (ι₁ × ι₂)} : symOffDiag s(x, y) ↔ x.1 ≠ y.1 ∧ x.2 ≠ y.2 :=
  Iff.rfl


@[simp]
theorem symOffDiag_iff_proj_eq (z : (ι₁ × ι₂) × (ι₁ × ι₂)) :
    symOffDiag (Sym2.mk z) ↔ z.1.1 ≠ z.2.1 ∧ z.1.2 ≠ z.2.2 :=
  Prod.recOn z fun _ _ => mk_symOffDiag_iff


instance symOffDiag.decidablePred [DecidableEq ι₁] [DecidableEq ι₂] :
    DecidablePred (@symOffDiag ι₁ ι₂) :=
  fun z => z.recOnSubsingleton fun a => decidable_of_iff' _ (symOffDiag_iff_proj_eq a)

/-- Triangular -/
def symOffDiagUpper [LT ι₁] [LT ι₂] : Sym2 (ι₁ × ι₂) → Prop :=
  Sym2.lift ⟨fun (i₁, i₂) (j₁, j₂) => (i₁ < j₁ ∧ i₂ < j₂) ∨ j₁ < i₁ ∧ j₂ < i₂, by aesop⟩

--variable [LT ι₁] [LT ι₂]

theorem mk_symOffDiagUpper_iff [LT ι₁] [LT ι₂] {i j : (ι₁ × ι₂)} :
    symOffDiagUpper s(i, j) ↔ (i.1 < j.1 ∧ i.2 < j.2) ∨ j.1 < i.1 ∧ j.2 < i.2 :=
  Iff.rfl

@[simp]
theorem symOffDiagUpper_iff_proj_eq [LT ι₁] [LT ι₂] (z : (ι₁ × ι₂) × (ι₁ × ι₂)) :
    symOffDiagUpper (Sym2.mk z) ↔ (z.1.1 < z.2.1 ∧ z.1.2 < z.2.2) ∨ z.2.1 < z.1.1 ∧ z.2.2 < z.1.2 :=
  Prod.recOn z fun _ _ => mk_symOffDiagUpper_iff

/- Can probably weaken the hypothesis here -/
instance symOffDiagUpper.decidablePred [LinearOrder ι₁] [LinearOrder ι₂] :
    DecidablePred (@symOffDiagUpper ι₁ ι₂ _ _) :=
  fun z => z.recOnSubsingleton fun a => decidable_of_iff' _ (symOffDiagUpper_iff_proj_eq a)

/-- Triangular -/
def symOffDiagLower [LT ι₁] [LT ι₂] : Sym2 (ι₁ × ι₂) → Prop :=
  Sym2.lift ⟨fun (i₁, i₂) (j₁, j₂) => (i₁ < j₁ ∧ j₂ < i₂) ∨ j₁ < i₁ ∧ i₂ < j₂, by aesop⟩

--variable [LT ι₁] [LT ι₂]

theorem mk_symOffDiagLower_iff [LT ι₁] [LT ι₂] {i j : (ι₁ × ι₂)} :
    symOffDiagLower s(i, j) ↔ (i.1 < j.1 ∧ j.2 < i.2) ∨ j.1 < i.1 ∧ i.2 < j.2 :=
  Iff.rfl

@[simp]
theorem symOffDiagLower_iff_proj_eq [LT ι₁] [LT ι₂] (z : (ι₁ × ι₂) × (ι₁ × ι₂)) :
    symOffDiagLower (Sym2.mk z) ↔ (z.1.1 < z.2.1 ∧ z.2.2 < z.1.2) ∨ z.2.1 < z.1.1 ∧ z.1.2 < z.2.2 :=
  Prod.recOn z fun _ _ => mk_symOffDiagLower_iff

/- Can probably weaken the hypothesis here -/
instance symOffDiagLower.decidablePred [LinearOrder ι₁] [LinearOrder ι₂] :
    DecidablePred (@symOffDiagLower ι₁ ι₂ _ _) :=
  fun z => z.recOnSubsingleton fun a => decidable_of_iff' _ (symOffDiagLower_iff_proj_eq a)

/--
Exactly one pair of coordinates are equal
-/
def symOffDiagXor : Sym2 (ι₁ × ι₂) → Prop :=
  Sym2.lift ⟨fun (i₁, i₂) (j₁, j₂) => Xor' (i₁ = j₁) (i₂ = j₂), by
    intro ⟨i₁, j₁⟩  ⟨i₂, j₂⟩
    simp_all only [eq_iff_iff]
    apply Iff.intro
    · intro a
      apply a.imp
      · aesop
      · aesop
    · intro a
      apply a.imp
      · aesop
      · aesop⟩

theorem mk_symOffDiagXor_iff {i j : (ι₁ × ι₂)} :
    symOffDiagXor s(i, j) ↔ Xor' (i.1 = j.1) (i.2 = j.2) := Iff.rfl


@[simp]
theorem symOffDiagXor_iff_proj_eq (z : (ι₁ × ι₂) × (ι₁ × ι₂)) :
    symOffDiagXor (Sym2.mk z) ↔ Xor' (z.1.1 = z.2.1) (z.1.2 = z.2.2) :=
  Prod.recOn z fun _ _ => mk_symOffDiagXor_iff


instance symOffDiagXor.decidablePred [DecidableEq ι₁] [DecidableEq ι₂] :
    DecidablePred (@symOffDiagXor ι₁ ι₂) :=
  fun z => z.recOnSubsingleton fun a => decidable_of_iff' _ (symOffDiagXor_iff_proj_eq a)

lemma f1 (p : Sym2 (ι₁ × ι₂)) : Xor' p.IsDiag ¬ p.IsDiag :=
  xor_not_right.mpr (Eq.to_iff rfl)

  --Decidable.em p.IsDiag


lemma g1 (p : Sym2 (ι₁ × ι₂)) (h : symOffDiagXor p) : ¬ p.IsDiag := by
  induction' p with i j
  aesop

lemma g2 (p : Sym2 (ι₁ × ι₂)) : ¬ p.IsDiag ∧ symOffDiagXor p ↔ symOffDiagXor p := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨g1 _ h, h⟩

/-
lemma e1 (P Q R : Prop) : ((P ∧ Q) ∨ (P ∧ R)) ↔
    (P ∧ (Q ∨ R)) := by
  exact Iff.symm and_or_left
-/

lemma f2 [DecidableEq ι₁] [DecidableEq ι₂] (p : Sym2 (ι₁ × ι₂)) :
    p.IsDiag ∨ ((¬ p.IsDiag ∧ symOffDiagXor p) ∨ (¬ p.IsDiag ∧ ¬ symOffDiagXor p)) := by
  rw [← and_or_left]
  have e2 : symOffDiagXor p ∨ ¬ symOffDiagXor p := Decidable.em (symOffDiagXor p)
  have e3 : ¬p.IsDiag ∧ (symOffDiagXor p ∨ ¬ symOffDiagXor p) ↔ ¬p.IsDiag :=
    and_iff_left_of_imp fun a ↦ e2
  rw [e3]
  exact Decidable.em _

lemma f2b [DecidableEq ι₁] [DecidableEq ι₂] (p : Sym2 (ι₁ × ι₂)) :
    p.IsDiag ∨ ( symOffDiagXor p ∨ (¬ p.IsDiag ∧ ¬ symOffDiagXor p)) := by
  convert f2 p
  rw [g2]

lemma f3 (p : Sym2 (ι₁ × ι₂)) :
    (¬ p.IsDiag ∧ ¬ symOffDiagXor p) ↔ symOffDiag p := by
  induction' p with i j
  aesop

lemma f4 [DecidableEq ι₁] [DecidableEq ι₂] (p : Sym2 (ι₁ × ι₂)) :
    p.IsDiag ∨ ( symOffDiagXor p ∨ symOffDiag p) := by
  rw [← f3]
  exact f2b p

lemma foo [LinearOrder ι₁] [LinearOrder ι₂] (p : Sym2 (ι₁ × ι₂)) (h : symOffDiagUpper p) :
    symOffDiag p := by
  induction' p with i  j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  aesop

lemma foo2 [LinearOrder ι₁] [LinearOrder ι₂] (p : Sym2 (ι₁ × ι₂)) (h : symOffDiagLower p) :
    symOffDiag p := by
  induction' p with i  j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  aesop

lemma symOffDiag_iff_symOffDiagUpper_xor_symOffDiagLower [LinearOrder ι₁] [LinearOrder ι₂]
    (p : Sym2 (ι₁ × ι₂)) : symOffDiag p ↔ Xor' (symOffDiagUpper p) (symOffDiagLower p) := by
  induction' p with i  j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  constructor
  · intro h
    simp_all only [symOffDiag_iff_proj_eq, ne_eq, symOffDiagUpper_iff_proj_eq,
      symOffDiagLower_iff_proj_eq]
    obtain ⟨left, right⟩ := h
    have ee1 : Xor' (i₁ < j₁) (j₁ < i₁) := by
      rw [xor_iff_or_and_not_and]
      constructor
      · aesop
      · simp
        exact fun a ↦ le_of_lt a
    have ee2 : Xor' (i₂ < j₂) (j₂ < i₂) := by
      rw [xor_iff_or_and_not_and]
      constructor
      · aesop
      · simp
        exact fun a ↦ le_of_lt a
    rcases ee1 with (h | h')
    · rcases ee2 with (g | g')
      · aesop
      · rw [xor_iff_or_and_not_and]
        aesop
    · rcases ee2 with (g | g')
      · rw [xor_iff_or_and_not_and]
        aesop
      · aesop
  · intro h
    aesop

lemma symOffDiag_iff_symOffDiagUpper_xor_symOffDiagLower2 [LinearOrder ι₁] [LinearOrder ι₂]
    (p : Sym2 (ι₁ × ι₂)) : symOffDiag p ↔
    ((symOffDiagUpper p) ∨ (symOffDiagLower p)) ∧
      ¬ ((symOffDiagUpper p) ∧ (symOffDiagLower p)) := by
  rw [symOffDiag_iff_symOffDiagUpper_xor_symOffDiagLower, xor_iff_or_and_not_and]

lemma symOffDiag_iff_symOffDiagUpper_or_symOffDiagLower [LinearOrder ι₁] [LinearOrder ι₂]
    (p : Sym2 (ι₁ × ι₂)) : symOffDiag p ↔ (symOffDiagUpper p) ∨ (symOffDiagLower p) := by
  constructor
  · intro h
    exact ((symOffDiag_iff_symOffDiagUpper_xor_symOffDiagLower2 p).mp h).1
  · intro h
    cases' h with h1 h2
    · apply foo _ h1
    · apply foo2 _ h2

lemma foo3 [LinearOrder ι₁] [LinearOrder ι₂] (p : Sym2 (ι₁ × ι₂)) (h : symOffDiagXor p) :
    ¬ p.IsDiag := by
  induction' p with i  j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  aesop

lemma foo4 [LinearOrder ι₁] [LinearOrder ι₂] (p : Sym2 (ι₁ × ι₂)) (h : symOffDiag p) :
    ¬ p.IsDiag := by
  induction' p with i  j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  aesop


lemma not_IsDiag_iff_symOffDiagXor_xor_symOffDiag [LinearOrder ι₁] [LinearOrder ι₂]
    (p : Sym2 (ι₁ × ι₂)) : ¬ p.IsDiag ↔ Xor' (symOffDiagXor p) (symOffDiag p) := by
  induction' p with i  j
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  rw [xor_iff_or_and_not_and]
  constructor
  · intro h
    simp_all only [Sym2.isDiag_iff_proj_eq, Prod.mk.injEq, not_and,
      symOffDiagXor_iff_proj_eq, symOffDiag_iff_proj_eq, ne_eq, Decidable.not_not]
    apply And.intro
    · rw [xor_iff_or_and_not_and]
      simp_all only [not_and, not_false_eq_true, implies_true, and_true]
      have e1 : i₁ = j₁ ∨ ¬ i₁ = j₁ := eq_or_ne i₁ j₁
      cases' e1 with h1 h2
      · apply Or.inl
        apply Or.inl h1
      · cases' (eq_or_ne i₂ j₂) with h3 h4
        · apply Or.inl
          apply Or.inr h3
        · apply Or.inr
          constructor
          · exact h2
          · apply h4
    · intro h1 h2
      aesop
  · intro h
    aesop

lemma not_IsDiag_iff_symOffDiagXor_xor_symOffDiag2 [LinearOrder ι₁] [LinearOrder ι₂]
    (p : Sym2 (ι₁ × ι₂)) : ¬ p.IsDiag ↔
    ((symOffDiagXor p) ∨ (symOffDiag p)) ∧
      ¬ ((symOffDiagXor p) ∧ (symOffDiag p)) := by
  rw [not_IsDiag_iff_symOffDiagXor_xor_symOffDiag, xor_iff_or_and_not_and]

lemma not_IsDiag_iff_symOffDiagXor_or_symOffDiag [LinearOrder ι₁] [LinearOrder ι₂]
    (p : Sym2 (ι₁ × ι₂)) : ¬ p.IsDiag ↔ (symOffDiagXor p) ∨ (symOffDiag p) := by
  constructor
  · intro h
    apply ((not_IsDiag_iff_symOffDiagXor_xor_symOffDiag2 p).mp h).1
  · intro h
    cases' h with h1 h2
    · apply foo3 _ h1
    · apply foo4 _ h2

lemma filter_partition [LinearOrder ι₁] [LinearOrder ι₂] (p : Sym2 (ι₁ × ι₂)) :
    p.IsDiag ∨ symOffDiagXor p ∨ (Xor' (symOffDiagUpper p) (symOffDiagLower p)) := by
  rw [← symOffDiag_iff_symOffDiagUpper_xor_symOffDiagLower]
  exact f4 p

/-
lemma filterseq [LinearOrder ι₁] [LinearOrder ι₂] (p : Sym2 (ι₁ × ι₂)) :
    ¬ p.IsDiag ∧ ¬symOffDiagUpper p ∧ ¬symOffDiagLower p ↔ symOffDiagXor p := by
  aesop
-/

end Prod

open LinearMap (BilinMap)

namespace QuadraticMap

section

variable {ι R M N}

variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [DecidableEq ι]

open Finsupp in
theorem map_finsupp_sum (Q : QuadraticMap R M N) (f : ι →₀ R) (g : ι → R → M) :
    Q (f.sum g) = (f.sum fun i r => Q (g i r)) +
    ∑ p ∈ f.support.sym2 with ¬ p.IsDiag,
      Sym2.lift
        ⟨fun i j => (polar Q) (g i (f i)) (g j (f j)), fun i j => by simp only [polar_comm]⟩ p := by
  rw [sum, QuadraticMap.map_sum]
  exact congrArg (HAdd.hAdd _) rfl

open Finsupp in
theorem map_finsupp_linearCombination (Q : QuadraticMap R M N) {g : ι → M} (l : ι →₀ R) :
    Q (linearCombination R g l) = (l.sum fun i r => (r * r) • Q (g i)) +
    ∑ p ∈ l.support.sym2 with ¬ p.IsDiag,
      Sym2.lift
        ⟨fun i j => (l i) • (l j) • (polar Q) (g i) (g j), fun i j => by
          simp only [polar_comm]
          rw [smul_comm]⟩ p := by
  simp_rw [linearCombination_apply, map_finsupp_sum,
    polar_smul_left, polar_smul_right, map_smul]

theorem basis_expansion (Q : QuadraticMap R M N) (bm : Basis ι R M) (x : M) :
    Q x = ((bm.repr x).sum fun i r => (r * r) • Q (bm i)) +
    ∑ p ∈ (bm.repr x).support.sym2 with ¬ p.IsDiag,
      Sym2.lift
        ⟨fun i j => ((bm.repr x) i) • ((bm.repr x) j) • (polar Q) (bm i) (bm j), fun i j => by
          simp only [polar_comm]
          rw [smul_comm]⟩ p := by
  rw [← map_finsupp_linearCombination, Basis.linearCombination_repr]

end

section toBilin

variable {ι R M N} [LinearOrder ι]
variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- Given an ordered basis, produce a bilinear form associated with the quadratic form.

Unlike `QuadraticMap.associated`, this is not symmetric; however, as a result it can be used even
in characteristic two. When considered as a matrix, the form is triangular. -/
noncomputable def toBilin (Q : QuadraticMap R M N) (bm : Basis ι R M) : LinearMap.BilinMap R M N :=
  bm.constr (S := R) fun i =>
    bm.constr (S := R) fun j =>
      if i = j then Q (bm i) else if i < j then polar Q (bm i) (bm j) else 0

theorem toBilin_apply (Q : QuadraticMap R M N) (bm : Basis ι R M) (i j : ι) :
    Q.toBilin bm (bm i) (bm j) =
      if i = j then Q (bm i) else if i < j then polar Q (bm i) (bm j) else 0 := by
  simp [toBilin]

theorem toQuadraticMap_toBilin (Q : QuadraticMap R M N) (bm : Basis ι R M) :
    (Q.toBilin bm).toQuadraticMap = Q := by
  ext x
  rw [← bm.linearCombination_repr x, LinearMap.BilinMap.toQuadraticMap_apply,
      Finsupp.linearCombination_apply, Finsupp.sum]
  simp_rw [LinearMap.map_sum₂, map_sum, LinearMap.map_smul₂, _root_.map_smul, toBilin_apply,
    smul_ite, smul_zero, ← Finset.sum_product', ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag, if_true]
  rw [Finset.sum_ite_of_false, QuadraticMap.map_sum, ← Finset.sum_filter]
  · simp_rw [← polar_smul_right _ (bm.repr x <| Prod.snd _),
      ← polar_smul_left _ (bm.repr x <| Prod.fst _)]
    simp_rw [QuadraticMap.map_smul, mul_smul, Finset.sum_sym2_filter_not_isDiag]
    rfl
  · intro x hx
    rw [Finset.mem_offDiag] at hx
    simpa using hx.2.2

/-- From a free module, every quadratic map can be built from a bilinear form.

See `BilinMap.not_forall_toQuadraticMap_surjective` for a counterexample when the module is
not free. -/
theorem _root_.LinearMap.BilinMap.toQuadraticMap_surjective [Module.Free R M] :
    Function.Surjective (LinearMap.BilinMap.toQuadraticMap : LinearMap.BilinMap R M N → _) := by
  intro Q
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  letI : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  exact ⟨_, toQuadraticMap_toBilin _ b⟩

@[simp]
lemma add_toBilin (bm : Basis ι R M) (Q₁ Q₂ : QuadraticMap R M N) :
    (Q₁ + Q₂).toBilin bm = Q₁.toBilin bm + Q₂.toBilin bm := by
  refine bm.ext fun i => bm.ext fun j => ?_
  obtain h | rfl | h := lt_trichotomy i j
  · simp [h.ne, h, toBilin_apply, polar_add]
  · simp [toBilin_apply]
  · simp [h.ne', h.not_lt, toBilin_apply, polar_add]

variable (S) [CommSemiring S] [Algebra S R]
variable [Module S N] [IsScalarTower S R N]

@[simp]
lemma smul_toBilin (bm : Basis ι R M) (s : S) (Q : QuadraticMap R M N) :
    (s • Q).toBilin bm = s • Q.toBilin bm := by
  refine bm.ext fun i => bm.ext fun j => ?_
  obtain h | rfl | h := lt_trichotomy i j
  · simp [h.ne, h, toBilin_apply, polar_smul]
  · simp [toBilin_apply]
  · simp [h.ne', h.not_lt, toBilin_apply]

/-- `QuadraticMap.toBilin` as an S-linear map -/
@[simps]
noncomputable def toBilinHom (bm : Basis ι R M) : QuadraticMap R M N →ₗ[S] BilinMap R M N where
  toFun Q := Q.toBilin bm
  map_add' := add_toBilin bm
  map_smul' := smul_toBilin S bm

lemma toBilin_symm_eq_Polar (Q : QuadraticMap R M N) (bm : Basis ι R M) :
    (Q.toBilin bm) + (Q.toBilin bm).flip = polarBilin Q := by
  ext a b
  conv_rhs => rw [← toQuadraticMap_toBilin Q bm]
  simp only [toQuadraticMap_toBilin]
  symm
  calc Q (a + b) - Q a - Q b = (Q.toBilin bm).toQuadraticMap (a + b) - Q a - Q b := by
        rw [ toQuadraticMap_toBilin Q]
  _ = (((Q.toBilin bm) a a + (Q.toBilin bm) b a) + (Q.toBilin bm) (a + b) b) - Q a - Q b := by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, map_add, map_add, LinearMap.add_apply]
  _ = (((Q.toBilin bm).toQuadraticMap a + (Q.toBilin bm) b a) + (Q.toBilin bm) (a + b) b) - Q a
    - Q b := by rw [LinearMap.BilinMap.toQuadraticMap_apply]
  _ = ((Q a + (Q.toBilin bm) b a) + (Q.toBilin bm) (a + b) b) - Q a - Q b := by
    rw [ toQuadraticMap_toBilin Q]
  _ = ((Q a + (Q.toBilin bm) b a) + ((Q.toBilin bm) a b + (Q.toBilin bm).toQuadraticMap b)) - Q a
    - Q b := by rw [map_add, LinearMap.add_apply,
      LinearMap.BilinMap.toQuadraticMap_apply (Q.toBilin bm) b]
  _ = ((Q a + (Q.toBilin bm) b a) + ((Q.toBilin bm) a b + Q b)) - Q a - Q b := by
    rw [ toQuadraticMap_toBilin Q]
  _ = ((Q.toBilin bm) a) b + ((Q.toBilin bm) b) a := by abel

lemma polar_toQuadraticMap (B : BilinMap R M N) (x y : M) :
    polar B.toQuadraticMap x y = B x y + B y x := by
  simp only [polar, BilinMap.toQuadraticMap_apply, map_add, LinearMap.add_apply]
  abel

lemma below_diag (Q : QuadraticMap R M N) (bm : Basis ι R M) (i j : ι) (h : j < i) :
  (Q.toBilin bm) (bm i) (bm j) = 0 := by
  simp [QuadraticMap.toBilin]
  have p1 : ¬ (i = j) := by exact ne_of_gt h
  have p2: ¬ (i < j) := by exact not_lt_of_gt h
  simp_all only [not_lt, ↓reduceIte, ite_eq_right_iff, isEmpty_Prop, IsEmpty.forall_iff]

lemma above_diag (Q : QuadraticMap R M N) (bm : Basis ι R M) (i j : ι) (h : i < j) :
  (Q.toBilin bm) (bm i) (bm j) = (polar Q) (bm i) (bm j) := by
  simp [QuadraticMap.toBilin]
  have p1 : ¬ (i = j) := by exact ne_of_lt h
  simp_all only [↓reduceIte]

lemma on_diag (Q : QuadraticMap R M N) (bm : Basis ι R M) (i : ι) :
    2 • (Q.toBilin bm) (bm i) (bm i) = (polar Q) (bm i) (bm i) := by
  simp [QuadraticMap.toBilin]

lemma polarBilin_toQuadraticMap (B : BilinMap R M N) :
    polarBilin B.toQuadraticMap = B + B.flip := by
  ext x y
  simp only [polarBilin_apply_apply, polar_toQuadraticMap, LinearMap.add_apply,
    LinearMap.flip_apply]

theorem toBilin_toQuadraticMap (B : BilinMap R M N) (bm : Basis ι R M) (x y : M) :
    let s := (bm.repr x).support ∪ (bm.repr y).support
    B.toQuadraticMap.toBilin bm x y =
      (∑ i ∈ s,
        ((bm.repr x) i) •((bm.repr y) i) • B (bm i) (bm i)) +
      ∑ p ∈ Finset.filter (fun p ↦ p.1 < p.2) s.offDiag,
        ((bm.repr x) p.1) • ((bm.repr y) p.2) • (B + B.flip) (bm p.1) (bm p.2) := by
  simp_rw [toBilin, polar_toQuadraticMap, BilinMap.toQuadraticMap_apply]
  let s := (bm.repr x).support ∪ (bm.repr y).support
  have h1 : (bm.repr x).support ⊆ s := Finset.subset_union_left
  have h2 : (bm.repr y).support ⊆ s := Finset.subset_union_right
  conv_lhs => rw [← bm.linearCombination_repr x, Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset _ h1 _ (fun i _ ↦ zero_smul R (bm i))]
  conv_lhs =>  rw [← bm.linearCombination_repr y, Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset _ h2 _ (fun i _ ↦ zero_smul R (bm i))]
  simp_rw [LinearMap.map_sum₂, map_sum, LinearMap.map_smul₂, _root_.map_smul,
    ← Finset.sum_product', ← Finset.diag_union_offDiag s,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag]
  simp only [Basis.constr_basis, ↓reduceIte, smul_ite, smul_add, smul_zero, add_right_inj]
  rw [Finset.sum_ite_of_false (by aesop) _ _, ← Finset.sum_filter]
  simp_rw [LinearMap.add_apply, LinearMap.flip_apply, smul_add]

end toBilin

/-
c.f `LinearAlgebra/QuadraticForm/TensorProduct`
-/

open TensorProduct

section TensorProduct

universe uR uA uM₁ uM₂ uN₁ uN₂

variable {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂ : Type uM₂} {N₁ : Type uN₁} {N₂ : Type uN₂}

variable [CommRing R] [CommRing A]
variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N₁] [AddCommGroup N₂]
variable [Algebra R A] [Module R M₁] [Module A M₁] [Module R N₁] [Module A N₁]
variable [SMulCommClass R A M₁] [IsScalarTower R A M₁]
variable [SMulCommClass R A N₁] [IsScalarTower R A N₁]
variable [Module R M₂] [Module R N₂]

variable (R A) in
/-- The tensor product of two quadratic maps injects into quadratic maps on tensor products.

Note this is heterobasic; the quadratic map on the left can take values in a module over a larger
ring than the one on the right. -/
-- `noncomputable` is a performance workaround for mathlib4#7103
noncomputable def tensorDistribFree {ι₁ : Type*} [LinearOrder ι₁] (bm₁ : Basis ι₁ A M₁)
    {ι₂ : Type*} [LinearOrder ι₂] (bm₂ : Basis ι₂ R M₂) :
    QuadraticMap A M₁ N₁ ⊗[R] QuadraticMap R M₂ N₂ →ₗ[A] QuadraticMap A (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂) :=
  -- while `letI`s would produce a better term than `let`, they would make this already-slow
  -- definition even slower.
  let toQ := BilinMap.toQuadraticMapLinearMap A A (M₁ ⊗[R] M₂)
  let tmulB := BilinMap.tensorDistrib R A (M₁ := M₁) (M₂ := M₂)
  let toB := AlgebraTensorModule.map
      (QuadraticMap.toBilinHom _ bm₁ : QuadraticMap A M₁ N₁ →ₗ[A] BilinMap A M₁ N₁)
      (QuadraticMap.toBilinHom _ bm₂ : QuadraticMap R M₂ N₂ →ₗ[R] BilinMap R M₂ N₂)
  toQ ∘ₗ tmulB ∘ₗ toB


variable {ι₁ : Type*} [LinearOrder ι₁] (bm₁ : Basis ι₁ A M₁) (Q₁ : QuadraticMap A M₁ N₁)
variable {ι₂ : Type*} [LinearOrder ι₂] (bm₂ : Basis ι₂ R M₂) (Q₂ : QuadraticMap R M₂ N₂)

@[simp]
theorem tensorDistriFree_tmul (m₁ : M₁) (m₂ : M₂) :
    tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂) (m₁ ⊗ₜ m₂) = Q₁ m₁ ⊗ₜ Q₂ m₂ := by
  apply (BilinMap.tensorDistrib_tmul _ _ _ _ _ _).trans
  apply congr_arg₂ _
  · rw [← LinearMap.BilinMap.toQuadraticMap_apply, toBilinHom_apply, toQuadraticMap_toBilin]
  · rw [← LinearMap.BilinMap.toQuadraticMap_apply, toBilinHom_apply, toQuadraticMap_toBilin]

lemma tensorDistribFree_apply
    {ι₁ : Type*} [LinearOrder ι₁] (bm₁ : Basis ι₁ A M₁)
    {ι₂ : Type*} [LinearOrder ι₂] (bm₂ : Basis ι₂ R M₂) :
  tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂) =
    ((Q₁.toBilin bm₁).tmul (Q₂.toBilin bm₂)).toQuadraticMap := rfl

lemma tensorDistriFree_left_self (a : M₁) (b c : M₂):
    polar (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂)) (a ⊗ₜ b) (a ⊗ₜ c) =
    Q₁ a ⊗ₜ polarBilin Q₂ b c := by
  rw [tensorDistribFree_apply, polar_toQuadraticMap, BilinMap.tensorDistrib_tmul,
    BilinMap.tensorDistrib_tmul, ← BilinMap.toQuadraticMap_apply, toQuadraticMap_toBilin,
    ← TensorProduct.tmul_add, ← toBilin_symm_eq_Polar Q₂ bm₂]
  rfl

lemma tensorDistriFree_right_self (a b : M₁) (c : M₂):
    polar (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂)) (a ⊗ₜ c) (b ⊗ₜ c) =
    polarBilin Q₁ a b ⊗ₜ  Q₂ c := by
  rw [tensorDistribFree_apply, polar_toQuadraticMap, BilinMap.tensorDistrib_tmul,
    BilinMap.tensorDistrib_tmul, ← BilinMap.toQuadraticMap_apply, toQuadraticMap_toBilin,
    ← TensorProduct.add_tmul, ← toBilin_symm_eq_Polar Q₁ bm₁]
  rfl

/-
lemma tensorDistriFree_self_self (a : M₁) (b : M₂):
    (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂)) (a ⊗ₜ b) = Q₁ a ⊗ₜ Q₂ b  := by
  rw [tensorDistriFree_tmul]
-/

lemma tensorDistriFree_polar11
    (i₁ j₁ : ι₁) (i₂ j₂ : ι₂) (h₁ : i₁ < j₁) (h₂ : i₂ < j₂) :
    polar (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂)) (bm₁ i₁ ⊗ₜ bm₂ i₂) (bm₁ j₁ ⊗ₜ bm₂ j₂) =
      (polar Q₁) (bm₁ i₁) (bm₁ j₁) ⊗ₜ (polar Q₂) (bm₂ i₂) (bm₂ j₂) := by
  rw [tensorDistribFree_apply, polar_toQuadraticMap, BilinMap.tensorDistrib_tmul,
    BilinMap.tensorDistrib_tmul, below_diag Q₁ bm₁ j₁ i₁ h₁, zero_tmul, add_zero,
    above_diag Q₁ bm₁ i₁ j₁ h₁, above_diag Q₂ bm₂ i₂ j₂ h₂]

lemma tensorDistriFree_polar12
    (i₁ j₁ : ι₁) (i₂ j₂ : ι₂) (h₁ : i₁ < j₁) (h₂ : j₂ < i₂) :
    polar (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂)) (bm₁ i₁ ⊗ₜ bm₂ i₂) (bm₁ j₁ ⊗ₜ bm₂ j₂) = 0 := by
  rw [tensorDistribFree_apply, polar_toQuadraticMap, BilinMap.tensorDistrib_tmul,
    BilinMap.tensorDistrib_tmul, below_diag Q₁ bm₁ j₁ i₁ h₁, zero_tmul, add_zero,
    above_diag Q₁ bm₁ i₁ j₁ h₁, below_diag _ _ _ _ h₂, tmul_zero]

lemma tensorDistriFree_polar21
    (i₁ j₁ : ι₁) (i₂ j₂ : ι₂) (h₁ : j₁ < i₁) (h₂ : i₂ < j₂) :
    polar (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂)) (bm₁ i₁ ⊗ₜ bm₂ i₂) (bm₁ j₁ ⊗ₜ bm₂ j₂) = 0 := by
  rw [tensorDistribFree_apply, polar_toQuadraticMap, BilinMap.tensorDistrib_tmul,
    BilinMap.tensorDistrib_tmul]
  rw [above_diag Q₂ bm₂ i₂ j₂ h₂]
  rw [below_diag _ _ _ _ h₂]
  rw [tmul_zero, add_zero]
  rw [below_diag _ _ _ _ h₁]
  rw [zero_tmul]

lemma tensorDistriFree_polar22
    (i₁ j₁ : ι₁) (i₂ j₂ : ι₂) (h₁ : j₁ < i₁) (h₂ : j₂ < i₂) :
    polar (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂)) (bm₁ i₁ ⊗ₜ bm₂ i₂) (bm₁ j₁ ⊗ₜ bm₂ j₂) =
      (polar Q₁) (bm₁ i₁) (bm₁ j₁) ⊗ₜ (polar Q₂) (bm₂ i₂) (bm₂ j₂) := by
    rw [tensorDistribFree_apply, polar_toQuadraticMap, BilinMap.tensorDistrib_tmul,
    BilinMap.tensorDistrib_tmul, above_diag Q₁ bm₁ j₁ i₁ h₁] --, zero_tmul, add_zero,
    rw [below_diag Q₁ bm₁ i₁ j₁ h₁, below_diag _ _ _ _ h₂, tmul_zero]
    rw [zero_add]
    rw [above_diag _ _ _ _ h₂]
    rw [polar_comm, polar_comm Q₂]


/--
Lift the tensor of two polars
-/
noncomputable def polarnn_lift (x : M₁ ⊗[R] M₂) : Sym2 (ι₁ × ι₂) → N₁ ⊗[R] N₂ :=
  let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
  Sym2.lift ⟨fun (i₁, i₂) (j₁, j₂) =>
    ((bm.repr x) (i₁, i₂)) • ((bm.repr x) (j₁, j₂)) •
      (polar Q₁) (bm₁ i₁) (bm₁ j₁) ⊗ₜ (polar Q₂) (bm₂ i₂) (bm₂ j₂),
    by
      intro _ _
      simp only [polar_comm]
      rw [smul_comm]
      ⟩

lemma tensorDistriFree_polar1 (i₁ j₁ : ι₁) (i₂ j₂ : ι₂) (h₁ : i₁ = j₁) :
    polar (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂)) (bm₁ i₁ ⊗ₜ bm₂ i₂) (bm₁ j₁ ⊗ₜ bm₂ j₂) =
    Q₁ (bm₁ i₁) ⊗ₜ (polarBilin Q₂) (bm₂ i₂) (bm₂ j₂) := by
  rw [← h₁, tensorDistriFree_left_self]

lemma tensorDistriFree_polar2 (i₁ j₁ : ι₁) (i₂ j₂ : ι₂) (h₁ : i₂ = j₂) :
    polar (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂)) (bm₁ i₁ ⊗ₜ bm₂ i₂) (bm₁ j₁ ⊗ₜ bm₂ j₂) =
    (polarBilin Q₁) (bm₁ i₁) (bm₁ j₁) ⊗ₜ Q₂ (bm₂ i₂)   := by
  rw [← h₁, tensorDistriFree_right_self]

--variable (x : M₁ ⊗[R] M₂)

--#check ((bm₁.tensorProduct bm₂).repr x).support.sym2 with ¬ p.IsDiag


variable {α : Type*} (p : α → Prop) [DecidablePred p] (s : Finset α) (f : α → N₁ ⊗[R] N₂)

lemma sum (f g : α → N₁ ⊗[R] N₂) (h : f = g) : ∑ p ∈ s, f p = ∑ p ∈ s, g p := by
  exact congrArg s.sum h

/-
lemma myadd: ∑ x ∈ s, f x = ∑ x ∈ s with p x, f x + ∑ x ∈ s with ¬ p x, f x := by
  exact Eq.symm (Finset.sum_filter_add_sum_filter_not s p f)
-/

/--
Lift the polar
-/
noncomputable def polar_lift (Q : QuadraticMap A (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂))
  (bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂)) (x : M₁ ⊗[R] M₂) := fun p => Sym2.lift
    ⟨fun i j => ((bm.repr x) i) • ((bm.repr x) j) • (polar Q) (bm i) (bm j), fun i j => by
      simp only [polar_comm]
      rw [smul_comm]⟩ p

lemma polar_lift_eq_polarnn_lift_on_symOffDiagUpper
    (s : Finset (Sym2 (ι₁ × ι₂))) (x : M₁ ⊗[R] M₂) (p : Sym2 (ι₁ × ι₂))
    (h: p ∈ Finset.filter symOffDiagUpper s) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    polar_lift Q bm x p =  polarnn_lift bm₁ Q₁ bm₂ Q₂ x p := by
  induction' p with i j
  simp_rw [polar_lift, polarnn_lift, Sym2.lift_mk, Prod.mk.eta]
  rw [Finset.mem_filter, symOffDiagUpper_iff_proj_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [Basis.tensorProduct_apply, Basis.tensorProduct_apply]
  rcases h2 with ⟨c1,c2⟩ | ⟨c3, c4⟩
  · rw [tensorDistriFree_polar11 bm₁ Q₁ bm₂ Q₂ _ _ _ _ c1 c2]
  · rw [tensorDistriFree_polar22 _ _ _ _ _ _ _ _ c3 c4]

lemma polar_lift_eq_zero_on_symOffDiagLower
    (s : Finset (Sym2 (ι₁ × ι₂))) (x : M₁ ⊗[R] M₂) (p : Sym2 (ι₁ × ι₂))
    (h: p ∈ Finset.filter symOffDiagLower s) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    polar_lift Q bm x p = 0 := by
  induction' p with i j
  simp_rw [polar_lift, Sym2.lift_mk]
  rw [Finset.mem_filter, symOffDiagLower_iff_proj_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [Basis.tensorProduct_apply, Basis.tensorProduct_apply]
  rcases h2 with ⟨c1,c2⟩ | ⟨c3, c4⟩
  · rw [tensorDistriFree_polar12 bm₁ Q₁ bm₂ Q₂ _ _ _ _ c1 c2, smul_zero, smul_zero]
  · rw [tensorDistriFree_polar21 bm₁ Q₁ bm₂ Q₂ _ _ _ _ c3 c4, smul_zero, smul_zero]

lemma myadd2
    (s : Finset (Sym2 (ι₁ × ι₂))) (x : M₁ ⊗[R] M₂) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    ∑ p ∈ s with symOffDiagUpper p, polarnn_lift bm₁ Q₁ bm₂ Q₂ x p
      + ∑ p ∈ s with ¬ symOffDiagUpper p, Q.polar_lift bm x p =
      ∑ p ∈ s, polar_lift Q bm x p := by
  let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
  let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
  simp_rw [← Finset.sum_filter_add_sum_filter_not s symOffDiagUpper (Q.polar_lift bm x)]
  simp only [add_left_inj]
  apply Finset.sum_congr rfl
  intro p hp
  rw [polar_lift_eq_polarnn_lift_on_symOffDiagUpper bm₁ Q₁ bm₂ Q₂ s x p hp]

lemma myadd2a
    (x : M₁ ⊗[R] M₂) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    let s := Finset.filter (fun p => ¬ p.IsDiag) (bm.repr x).support.sym2
    ∑ p ∈ s with symOffDiagUpper p, polarnn_lift bm₁ Q₁ bm₂ Q₂ x p
      + ∑ p ∈ s with ¬ symOffDiagUpper p, Q.polar_lift bm x p =
      ∑ p ∈ s, polar_lift Q bm x p := myadd2 _ _ _ _ _ _

lemma myadd3
    (s : Finset (Sym2 (ι₁ × ι₂))) (x : M₁ ⊗[R] M₂) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
      ∑ p ∈ s with ¬ symOffDiagLower p, Q.polar_lift bm x p =
      ∑ p ∈ s, polar_lift Q bm x p := by
  let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
  let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hps hpn
  simp at hpn
  rw [polar_lift_eq_zero_on_symOffDiagLower bm₁ Q₁ bm₂ Q₂ s _ _ (by simp_all only [forall_const,
    Finset.mem_filter, and_self])]

lemma myadd3a
    (x : M₁ ⊗[R] M₂) :
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    let s₁ := Finset.filter (fun p => ¬ p.IsDiag) (bm.repr x).support.sym2
    let s := Finset.filter (fun p => ¬ symOffDiagUpper p) s₁
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
      ∑ p ∈ s with ¬ symOffDiagLower p, Q.polar_lift bm x p =
      ∑ p ∈ s, polar_lift Q bm x p := myadd3 _ _ _ _ _ _

theorem qt_expansion (x : M₁ ⊗[R] M₂) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    ((bm.repr x).sum fun i r => (r * r) • (Q₁ (bm₁ i.1) ⊗ₜ[R] Q₂ (bm₂ i.2))) +
    ∑  p ∈ (bm.repr x).support.sym2 with ¬ p.IsDiag, polar_lift Q bm x p = Q x := by
  let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
  let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
  simp_rw [basis_expansion Q bm x]
  have e1 (i : ι₁ × ι₂) : Q₁ (bm₁ i.1) ⊗ₜ Q₂ (bm₂ i.2) = Q (bm i) := by
    rw [Basis.tensorProduct_apply, tensorDistriFree_tmul]
  simp_rw [polar_lift, e1]

theorem qt_expansion2 (x : M₁ ⊗[R] M₂) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    let s := Finset.filter (fun p => ¬ p.IsDiag) (bm.repr x).support.sym2
    ((bm.repr x).sum fun i r => (r * r) • (Q₁ (bm₁ i.1) ⊗ₜ[R] Q₂ (bm₂ i.2))) +
      ∑ p ∈ s with symOffDiagUpper p, polarnn_lift bm₁ Q₁ bm₂ Q₂ x p
        + ∑ p ∈ s with ¬ symOffDiagUpper p, Q.polar_lift bm x p = Q x := by
  let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
  let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
  let s := Finset.filter (fun p => ¬ p.IsDiag) (bm.repr x).support.sym2
  simp_rw [add_assoc, myadd2a]
  rw [qt_expansion]

theorem qt_expansion3 (x : M₁ ⊗[R] M₂) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    let s := Finset.filter (fun p => ¬ p.IsDiag) (bm.repr x).support.sym2
    let s₂ := Finset.filter (fun p => ¬ symOffDiagUpper p) s
    ((bm.repr x).sum fun i r => (r * r) • (Q₁ (bm₁ i.1) ⊗ₜ[R] Q₂ (bm₂ i.2))) +
      ∑ p ∈ s with symOffDiagUpper p, polarnn_lift bm₁ Q₁ bm₂ Q₂ x p
        + ∑ p ∈ s₂ with ¬ symOffDiagLower p, Q.polar_lift bm x p = Q x := by
  simp_rw [myadd3a]
  rw [qt_expansion2]

-- not_IsDiag_iff_symOffDiagXor_xor_symOffDiag


theorem sum1 (x : M₁ ⊗[R] M₂) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    let s := (bm.repr x).support.sym2
    (∑ p ∈ s with symOffDiagXor p, Q.polar_lift bm x p)
      + (∑ p ∈ s with symOffDiag p, Q.polar_lift bm x p) =
    ∑ p ∈ s with ¬ p.IsDiag, Q.polar_lift bm x p := by
  let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
  let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
  let s := (bm.repr x).support.sym2
  have h1 : ∀ y ∈ s.filter (fun y => symOffDiagXor y ∨ symOffDiag y),
      ¬ (symOffDiagXor y ∧ symOffDiag y) := by
    intro y hy
    apply ((xor_iff_or_and_not_and (symOffDiagXor y) (symOffDiag y)).mp _).2
    rw [← not_IsDiag_iff_symOffDiagXor_xor_symOffDiag]
    simp at hy
    rw [not_IsDiag_iff_symOffDiagXor_or_symOffDiag]
    exact hy.2
  simp_rw [← Finset.sum_disjoint_filters_on_set  _ _ h1]
  simp_rw [not_IsDiag_iff_symOffDiagXor_or_symOffDiag]


theorem sum2 (x : M₁ ⊗[R] M₂) :
    let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
    let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
    let s := (bm.repr x).support.sym2
    (∑ p ∈ s with symOffDiagUpper p, Q.polar_lift bm x p)
      + (∑ p ∈ s with symOffDiagLower p, Q.polar_lift bm x p) =
    ∑ p ∈ s with symOffDiag p, Q.polar_lift bm x p := by
  let Q := (tensorDistribFree R A bm₁ bm₂ (Q₁ ⊗ₜ Q₂))
  let bm : Basis (ι₁ × ι₂) A (M₁ ⊗[R] M₂) := (bm₁.tensorProduct bm₂)
  let s := (bm.repr x).support.sym2
  have h1 : ∀ y ∈ s.filter (fun y => symOffDiagUpper y ∨ symOffDiagLower y),
      ¬ (symOffDiagUpper y ∧ symOffDiagLower y) := by
    intro y hy
    apply ((xor_iff_or_and_not_and (symOffDiagUpper y) (symOffDiagLower y)).mp _).2
    rw [← symOffDiag_iff_symOffDiagUpper_xor_symOffDiagLower]
    simp at hy
    rw [symOffDiag_iff_symOffDiagUpper_or_symOffDiagLower]
    exact hy.2
  simp_rw [← Finset.sum_disjoint_filters_on_set  _ _ h1]
  simp_rw [symOffDiag_iff_symOffDiagUpper_or_symOffDiagLower]




-- #check Finset.sum_disjUnion

-- #check Finset.sum_filter_add_sum_filter_not

/-
lemma filter_change (s : Finset (Sym2 (ι₁ × ι₂))) (x : M₁ ⊗[R] M₂) :
    let s₁ := Finset.filter (fun p => ¬ p.IsDiag) s
    let s₂ := Finset.filter (fun p => ¬ symOffDiagUpper p) s₁
    let s₃ := Finset.filter (fun p => ¬ symOffDiagLower p) s₂
    s₃ = Finset.filter (fun p => ¬ symOffDiagXor p) s := by
  simp only
  rw [Finset.filter_filter]
  rw [Finset.filter_filter]
-/


end TensorProduct

end QuadraticMap
