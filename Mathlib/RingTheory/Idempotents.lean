/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nilpotent.Defs

/-!

## Idempotents in rings

The predicate `IsIdempotentElem` is defined for general monoids in `Algebra/Ring/Idempotents.lean`.
In this file we provide various results regarding idempotent elements in rings.

## Main definitions

- `OrthogonalIdempotents`:
  A family `{ eᵢ }` of idempotent elements is orthogonal if `eᵢ * eⱼ = 0` for all `i ≠ j`.
- `CompleteOrthogonalIdempotents`:
  A family `{ eᵢ }` of orthogonal idempotent elements is complete if `∑ eᵢ = 1`.

## Main results

- `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`:
  If the kernel of `f : R →+* S` consists of nilpotent elements, and `{ eᵢ }` is a family of
  complete orthogonal idempotents in the range of `f`, then `{ eᵢ }` is the image of some
  complete orthogonal idempotents in `R`.
- `existsUnique_isIdempotentElem_eq_of_ker_isNilpotent`:
  If `R` is commutative and the kernel of `f : R →+* S` consists of nilpotent elements,
  then every idempotent in the range of `f` lifts to a unique idempotent in `R`.
- `CompleteOrthogonalIdempotents.bijective_pi`:
  If `R` is commutative, then a family `{ eᵢ }` of complete orthogonal idempotent elements induces
  a ring isomorphism `R ≃ ∏ R ⧸ ⟨1 - eᵢ⟩`.
-/

section Semiring

variable {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
variable {I : Type*} (e : I → R)

/-- A family `{ eᵢ }` of idempotent elements is orthogonal if `eᵢ * eⱼ = 0` for all `i ≠ j`. -/
@[mk_iff]
structure OrthogonalIdempotents : Prop where
  idem : ∀ i, IsIdempotentElem (e i)
  ortho : Pairwise (e · * e · = 0)

variable {e}

lemma OrthogonalIdempotents.mul_eq [DecidableEq I] (he : OrthogonalIdempotents e) (i j) :
    e i * e j = if i = j then e i else 0 := by
  split
  · simp [*, (he.idem j).eq]
  · exact he.ortho ‹_›

lemma OrthogonalIdempotents.iff_mul_eq [DecidableEq I] :
    OrthogonalIdempotents e ↔ ∀ i j, e i * e j = if i = j then e i else 0 :=
  ⟨mul_eq, fun H ↦ ⟨fun i ↦ by simpa using H i i, fun i j e ↦ by simpa [e] using H i j⟩⟩

lemma OrthogonalIdempotents.isIdempotentElem_sum (he : OrthogonalIdempotents e) {s : Finset I} :
    IsIdempotentElem (∑ i ∈ s, e i) := by
  classical
  simp [IsIdempotentElem, Finset.sum_mul, Finset.mul_sum, he.mul_eq]

lemma OrthogonalIdempotents.mul_sum_of_mem (he : OrthogonalIdempotents e)
    {i : I} {s : Finset I} (h : i ∈ s) : e i * ∑ j ∈ s, e j = e i := by
  classical
  simp [Finset.mul_sum, he.mul_eq, h]

lemma OrthogonalIdempotents.mul_sum_of_notMem (he : OrthogonalIdempotents e)
    {i : I} {s : Finset I} (h : i ∉ s) : e i * ∑ j ∈ s, e j = 0 := by
  classical
  simp [Finset.mul_sum, he.mul_eq, h]

@[deprecated (since := "2025-05-23")]
alias OrthogonalIdempotents.mul_sum_of_not_mem := OrthogonalIdempotents.mul_sum_of_notMem

lemma OrthogonalIdempotents.map (he : OrthogonalIdempotents e) :
    OrthogonalIdempotents (f ∘ e) := by
  classical
  simp [iff_mul_eq, he.mul_eq, ← map_mul f, apply_ite f]

lemma OrthogonalIdempotents.map_injective_iff (hf : Function.Injective f) :
    OrthogonalIdempotents (f ∘ e) ↔ OrthogonalIdempotents e := by
  classical
  simp [iff_mul_eq, ← hf.eq_iff, apply_ite]

lemma OrthogonalIdempotents.embedding (he : OrthogonalIdempotents e) {J} (i : J ↪ I) :
    OrthogonalIdempotents (e ∘ i) := by
  classical
  simp [iff_mul_eq, he.mul_eq]

lemma OrthogonalIdempotents.equiv {J} (i : J ≃ I) :
    OrthogonalIdempotents (e ∘ i) ↔ OrthogonalIdempotents e := by
  classical
  simp [iff_mul_eq, i.forall_congr_left]

lemma OrthogonalIdempotents.unique [Unique I] :
    OrthogonalIdempotents e ↔ IsIdempotentElem (e default) := by
  simp only [orthogonalIdempotents_iff, Unique.forall_iff, Subsingleton.pairwise, and_true]

lemma OrthogonalIdempotents.option (he : OrthogonalIdempotents e) [Fintype I] (x)
    (hx : IsIdempotentElem x) (hx₁ : x * ∑ i, e i = 0) (hx₂ : (∑ i, e i) * x = 0) :
    OrthogonalIdempotents (Option.elim · x e) where
  idem i := i.rec hx he.idem
  ortho i j ne := by
    classical
    rcases i with - | i <;> rcases j with - | j
    · cases ne rfl
    · simpa only [mul_assoc, Finset.sum_mul, he.mul_eq, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, zero_mul] using congr_arg (· * e j) hx₁
    · simpa only [Option.elim_some, Option.elim_none, ← mul_assoc, Finset.mul_sum, he.mul_eq,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, mul_zero] using congr_arg (e i * ·) hx₂
    · exact he.ortho (Option.some_inj.ne.mp ne)

variable [Fintype I]

/--
A family `{ eᵢ }` of idempotent elements is complete orthogonal if
1. (orthogonal) `eᵢ * eⱼ = 0` for all `i ≠ j`.
2. (complete) `∑ eᵢ = 1`
-/
@[mk_iff]
structure CompleteOrthogonalIdempotents (e : I → R) : Prop extends OrthogonalIdempotents e where
  complete : ∑ i, e i = 1

/-- If a family is complete orthogonal, it consists of idempotents. -/
lemma CompleteOrthogonalIdempotents.iff_ortho_complete :
    CompleteOrthogonalIdempotents e ↔ Pairwise (e · * e · = 0) ∧ ∑ i, e i = 1 := by
  rw [completeOrthogonalIdempotents_iff, orthogonalIdempotents_iff, and_assoc, and_iff_right_of_imp]
  intro ⟨ortho, complete⟩ i
  apply_fun (e i * ·) at complete
  rwa [Finset.mul_sum, Finset.sum_eq_single i (fun _ _ ne ↦ ortho ne.symm) (by simp at ·), mul_one]
    at complete

lemma CompleteOrthogonalIdempotents.pair_iff'ₛ {x y : R} :
    CompleteOrthogonalIdempotents ![x, y] ↔ x * y = 0 ∧ y * x = 0 ∧ x + y = 1 := by
  simp [iff_ortho_complete, Pairwise, Fin.forall_fin_two, and_assoc]

lemma CompleteOrthogonalIdempotents.pair_iffₛ {R} [CommSemiring R] {x y : R} :
    CompleteOrthogonalIdempotents ![x, y] ↔ x * y = 0 ∧ x + y = 1 := by
  rw [pair_iff'ₛ, and_left_comm, and_iff_right_of_imp]; exact (mul_comm x y ▸ ·.1)

lemma CompleteOrthogonalIdempotents.unique_iff [Unique I] :
    CompleteOrthogonalIdempotents e ↔ e default = 1 := by
  rw [completeOrthogonalIdempotents_iff, OrthogonalIdempotents.unique, Fintype.sum_unique,
    and_iff_right_iff_imp]
  exact (· ▸ IsIdempotentElem.one)

lemma CompleteOrthogonalIdempotents.single {I : Type*} [Fintype I] [DecidableEq I]
    (R : I → Type*) [∀ i, Semiring (R i)] :
    CompleteOrthogonalIdempotents (Pi.single (M := R) · 1) := by
  refine ⟨⟨by simp [IsIdempotentElem, ← Pi.single_mul], ?_⟩, Finset.univ_sum_single 1⟩
  intros i j hij
  ext k
  by_cases hi : i = k
  · subst hi; simp [hij]
  · simp [hi]

lemma CompleteOrthogonalIdempotents.map (he : CompleteOrthogonalIdempotents e) :
    CompleteOrthogonalIdempotents (f ∘ e) where
  __ := he.toOrthogonalIdempotents.map f
  complete := by simp only [Function.comp_apply, ← map_sum, he.complete, map_one]

lemma CompleteOrthogonalIdempotents.map_injective_iff (hf : Function.Injective f) :
    CompleteOrthogonalIdempotents (f ∘ e) ↔ CompleteOrthogonalIdempotents e := by
  simp [completeOrthogonalIdempotents_iff, ← hf.eq_iff,
    OrthogonalIdempotents.map_injective_iff f hf]

lemma CompleteOrthogonalIdempotents.equiv {J} [Fintype J] (i : J ≃ I) :
    CompleteOrthogonalIdempotents (e ∘ i) ↔ CompleteOrthogonalIdempotents e := by
  simp only [completeOrthogonalIdempotents_iff, OrthogonalIdempotents.equiv, Function.comp_apply,
    Fintype.sum_equiv i _ e (fun _ ↦ rfl)]

@[nontriviality]
lemma CompleteOrthogonalIdempotents.of_subsingleton [Subsingleton R] :
    CompleteOrthogonalIdempotents e :=
  ⟨⟨fun _ ↦ Subsingleton.elim _ _, fun _ _ _ ↦ Subsingleton.elim _ _⟩, Subsingleton.elim _ _⟩

end Semiring

section Ring

variable {R S : Type*} [Ring R] [Ring S] (f : R →+* S)

theorem isIdempotentElem_one_sub_one_sub_pow_pow
    (x : R) (n : ℕ) (hx : (x - x ^ 2) ^ n = 0) :
    IsIdempotentElem (1 - (1 - x ^ n) ^ n) := by
  have : (x - x ^ 2) ^ n ∣ (1 - (1 - x ^ n) ^ n) - (1 - (1 - x ^ n) ^ n) ^ 2 := by
    conv_rhs => rw [pow_two, ← mul_one_sub, sub_sub_cancel]
    nth_rw 1 3 [← one_pow n]
    rw [← (Commute.one_left x).mul_geom_sum₂, ← (Commute.one_left (1 - x ^ n)).mul_geom_sum₂]
    simp only [sub_sub_cancel, one_pow, one_mul]
    rw [Commute.mul_pow, Commute.mul_mul_mul_comm, ← Commute.mul_pow, mul_one_sub, ← pow_two]
    · exact ⟨_, rfl⟩
    · simp
    · refine .pow_right (.sub_right (.one_right _) (.sum_left _ _ _ fun _ _ ↦ .pow_left ?_ _)) _
      simp
    · exact .sub_left (.one_left _) (.sum_right _ _ _ fun _ _ ↦ .pow_right rfl _)
  rwa [hx, zero_dvd_iff, sub_eq_zero, eq_comm, pow_two] at this

theorem exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent_aux
    (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    (e₁ : S) (he : e₁ ∈ f.range) (he₁ : IsIdempotentElem e₁)
    (e₂ : R) (he₂ : IsIdempotentElem e₂) (he₁e₂ : e₁ * f e₂ = 0) :
    ∃ e' : R, IsIdempotentElem e' ∧ f e' = e₁ ∧ e' * e₂ = 0 := by
  obtain ⟨e₁, rfl⟩ := he
  cases subsingleton_or_nontrivial R
  · exact ⟨_, Subsingleton.elim _ _, rfl, Subsingleton.elim _ _⟩
  let a := e₁ - e₁ * e₂
  have ha : f a = f e₁ := by rw [map_sub, map_mul, he₁e₂, sub_zero]
  have ha' : a * e₂ = 0 := by rw [sub_mul, mul_assoc, he₂.eq, sub_self]
  have hx' : a - a ^ 2 ∈ RingHom.ker f := by
    simp [RingHom.mem_ker, pow_two, ha, he₁.eq]
  obtain ⟨n, hn⟩ := h _ hx'
  refine ⟨_, isIdempotentElem_one_sub_one_sub_pow_pow _ _ hn, ?_, ?_⟩
  · rcases n with - | n
    · simp at hn
    simp only [map_sub, map_one, map_pow, ha, he₁.pow_succ_eq,
      he₁.one_sub.pow_succ_eq, sub_sub_cancel]
  · obtain ⟨k, hk⟩ := (Commute.one_left (MulOpposite.op <| 1 - a ^ n)).sub_dvd_pow_sub_pow n
    apply_fun MulOpposite.unop at hk
    have : 1 - (1 - a ^ n) ^ n = MulOpposite.unop k * a ^ n := by simpa using hk
    rw [this, mul_assoc]
    rcases n with - | n
    · simp at hn
    rw [pow_succ, mul_assoc, ha', mul_zero, mul_zero]

/-- Orthogonal idempotents lift along nil ideals. -/
theorem exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent
    (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    (e₁ : S) (he : e₁ ∈ f.range) (he₁ : IsIdempotentElem e₁)
    (e₂ : R) (he₂ : IsIdempotentElem e₂) (he₁e₂ : e₁ * f e₂ = 0) (he₂e₁ : f e₂ * e₁ = 0) :
    ∃ e' : R, IsIdempotentElem e' ∧ f e' = e₁ ∧ e' * e₂ = 0 ∧ e₂ * e' = 0 := by
  obtain ⟨e', h₁, rfl, h₂⟩ := exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent_aux
    f h e₁ he he₁ e₂ he₂ he₁e₂
  refine ⟨(1 - e₂) * e', ?_, ?_, ?_, ?_⟩
  · rw [IsIdempotentElem, mul_assoc, ← mul_assoc e', mul_sub, mul_one, h₂, sub_zero, h₁.eq]
  · rw [map_mul, map_sub, map_one, sub_mul, one_mul, he₂e₁, sub_zero]
  · rw [mul_assoc, h₂, mul_zero]
  · rw [← mul_assoc, mul_sub, mul_one, he₂.eq, sub_self, zero_mul]

/-- Idempotents lift along nil ideals. -/
theorem exists_isIdempotentElem_eq_of_ker_isNilpotent (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    (e : S) (he : e ∈ f.range) (he' : IsIdempotentElem e) :
    ∃ e' : R, IsIdempotentElem e' ∧ f e' = e := by
  simpa using exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent f h e he he' 0 .zero (by simp)

lemma OrthogonalIdempotents.lift_of_isNilpotent_ker_aux
    (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    {n} {e : Fin n → S} (he : OrthogonalIdempotents e) (he' : ∀ i, e i ∈ f.range) :
    ∃ e' : Fin n → R, OrthogonalIdempotents e' ∧ f ∘ e' = e := by
  induction' n with n IH
  · refine ⟨0, ⟨finZeroElim, finZeroElim⟩, funext finZeroElim⟩
  · obtain ⟨e', h₁, h₂⟩ := IH (he.embedding (Fin.succEmb n)) (fun i ↦ he' _)
    have h₂' (i) : f (e' i) = e i.succ := congr_fun h₂ i
    obtain ⟨e₀, h₃, h₄, h₅, h₆⟩ :=
      exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent f h _ (he' 0) (he.idem 0) _
      h₁.isIdempotentElem_sum
      (by simp [Finset.mul_sum, h₂', he.mul_eq, eq_comm])
      (by simp [Finset.sum_mul, h₂', he.mul_eq])
    refine ⟨_, (h₁.option _ h₃ h₅ h₆).embedding (finSuccEquiv n).toEmbedding, funext fun i ↦ ?_⟩
    obtain ⟨_ | i, rfl⟩ := (finSuccEquiv n).symm.surjective i <;> simp [*]

variable {I : Type*} {e : I → R}

/-- A family of orthogonal idempotents lift along nil ideals. -/
lemma OrthogonalIdempotents.lift_of_isNilpotent_ker [Finite I]
    (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    {e : I → S} (he : OrthogonalIdempotents e) (he' : ∀ i, e i ∈ f.range) :
    ∃ e' : I → R, OrthogonalIdempotents e' ∧ f ∘ e' = e := by
  cases nonempty_fintype I
  obtain ⟨e', h₁, h₂⟩ := lift_of_isNilpotent_ker_aux f h
    (he.embedding (Fintype.equivFin I).symm.toEmbedding) (fun _ ↦ he' _)
  refine ⟨_, h₁.embedding (Fintype.equivFin I).toEmbedding,
    by ext x; simpa using congr_fun h₂ (Fintype.equivFin I x)⟩

lemma CompleteOrthogonalIdempotents.pair_iff {x y : R} :
    CompleteOrthogonalIdempotents ![x, y] ↔ IsIdempotentElem x ∧ y = 1 - x := by
  rw [pair_iff'ₛ, ← eq_sub_iff_add_eq', ← and_assoc, and_congr_left_iff]
  rintro rfl
  simp [mul_sub, sub_mul, IsIdempotentElem, sub_eq_zero, eq_comm]

lemma CompleteOrthogonalIdempotents.of_isIdempotentElem {e : R} (he : IsIdempotentElem e) :
    CompleteOrthogonalIdempotents ![e, 1 - e] :=
  pair_iff.mpr ⟨he, rfl⟩

variable [Fintype I]

lemma CompleteOrthogonalIdempotents.option (he : OrthogonalIdempotents e) :
    CompleteOrthogonalIdempotents (Option.elim · (1 - ∑ i, e i) e) where
  __ := he.option _ he.isIdempotentElem_sum.one_sub
    (by simp [sub_mul, he.isIdempotentElem_sum.eq]) (by simp [mul_sub, he.isIdempotentElem_sum.eq])
  complete := by
    rw [Fintype.sum_option]
    exact sub_add_cancel _ _

lemma CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker_aux
    (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    {n} {e : Fin n → S} (he : CompleteOrthogonalIdempotents e) (he' : ∀ i, e i ∈ f.range) :
    ∃ e' : Fin n → R, CompleteOrthogonalIdempotents e' ∧ f ∘ e' = e := by
  cases subsingleton_or_nontrivial R
  · choose e' he' using he'
    exact ⟨e', .of_subsingleton, funext he'⟩
  cases subsingleton_or_nontrivial S
  · obtain ⟨n, hn⟩ := h 1 (Subsingleton.elim _ _)
    simp at hn
  rcases n with - | n
  · simpa using he.complete
  obtain ⟨e', h₁, h₂⟩ := OrthogonalIdempotents.lift_of_isNilpotent_ker f h he.1 he'
  refine ⟨_, (equiv (finSuccEquiv n)).mpr
    (CompleteOrthogonalIdempotents.option (h₁.embedding (Fin.succEmb _))), funext fun i ↦ ?_⟩
  have (i : _) : f (e' i) = e i := congr_fun h₂ i
  cases i using Fin.cases with
  | zero => simp [this, Fin.sum_univ_succ, ← he.complete]
  | succ i => simp [this]

/-- A system of complete orthogonal idempotents lift along nil ideals. -/
lemma CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker
    (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    {e : I → S} (he : CompleteOrthogonalIdempotents e) (he' : ∀ i, e i ∈ f.range) :
    ∃ e' : I → R, CompleteOrthogonalIdempotents e' ∧ f ∘ e' = e := by
  obtain ⟨e', h₁, h₂⟩ := lift_of_isNilpotent_ker_aux f h
    ((equiv (Fintype.equivFin I).symm).mpr he) (fun _ ↦ he' _)
  refine ⟨_, ((equiv (Fintype.equivFin I)).mpr h₁),
    by ext x; simpa using congr_fun h₂ (Fintype.equivFin I x)⟩

theorem eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute {e₁ e₂ : R}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) (H : IsNilpotent (e₁ - e₂))
    (H' : Commute e₁ e₂) :
    e₁ = e₂ := by
  have : (e₁ - e₂) ^ 3 = (e₁ - e₂) := by
    simp only [pow_succ, pow_zero, mul_sub, one_mul, sub_mul, he₁.eq, he₂.eq,
      H'.eq, mul_assoc]
    simp only [← mul_assoc, he₂.eq]
    abel
  obtain ⟨n, hn⟩ := H
  have : (e₁ - e₂) ^ (2 * n + 1) = (e₁ - e₂) := by
    clear hn; induction n <;> simp [mul_add, add_assoc, pow_add _ (2 * _) 3, ← pow_succ, *]
  rwa [pow_succ, two_mul, pow_add, hn, zero_mul, zero_mul, eq_comm, sub_eq_zero] at this

theorem CompleteOrthogonalIdempotents.of_ker_isNilpotent_of_isMulCentral
    (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    (he : ∀ i, IsIdempotentElem (e i))
    (he' : ∀ i, IsMulCentral (e i))
    (he'' : CompleteOrthogonalIdempotents (f ∘ e)) :
    CompleteOrthogonalIdempotents e := by
  obtain ⟨e', h₁, h₂⟩ := lift_of_isNilpotent_ker f h he'' (fun _ ↦ ⟨_, rfl⟩)
  obtain rfl : e = e' := by
    ext i
    refine eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute
      (he _) (h₁.idem _) (h _ ?_) ((he' i).comm _)
    simpa [RingHom.mem_ker, sub_eq_zero] using congr_fun h₂.symm i
  exact h₁

end Ring

section CommRing

variable {R S : Type*} [CommRing R] [Ring S] (f : R →+* S)

theorem eq_of_isNilpotent_sub_of_isIdempotentElem {e₁ e₂ : R}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) (H : IsNilpotent (e₁ - e₂)) :
    e₁ = e₂ :=
  eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute he₁ he₂ H (.all _ _)

@[stacks 00J9]
theorem existsUnique_isIdempotentElem_eq_of_ker_isNilpotent (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    (e : S) (he : e ∈ f.range) (he' : IsIdempotentElem e) :
    ∃! e' : R, IsIdempotentElem e' ∧ f e' = e := by
  obtain ⟨e', he₂, rfl⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent f h e he he'
  exact ⟨e', ⟨he₂, rfl⟩, fun x ⟨hx, hx'⟩ ↦
    eq_of_isNilpotent_sub_of_isIdempotentElem hx he₂
      (h _ (by rw [RingHom.mem_ker, map_sub, hx', sub_self]))⟩

/-- A family of orthogonal idempotents induces an surjection `R ≃+* ∏ R ⧸ ⟨1 - eᵢ⟩` -/
lemma OrthogonalIdempotents.surjective_pi {I : Type*} [Finite I] {e : I → R}
    (he : OrthogonalIdempotents e) :
    Function.Surjective (Pi.ringHom fun i ↦ Ideal.Quotient.mk (Ideal.span {1 - e i})) := by
  suffices Pairwise fun i j ↦ IsCoprime (Ideal.span {1 - e i}) (Ideal.span {1 - e j}) by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.quotientInfToPiQuotient_surj this x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨x, by ext i; simp [Ideal.quotientInfToPiQuotient]⟩
  intros i j hij
  rw [Ideal.isCoprime_span_singleton_iff]
  exact ⟨1, e i, by simp [mul_sub, he.ortho hij]⟩

lemma OrthogonalIdempotents.prod_one_sub {I : Type*} {e : I → R}
    (he : OrthogonalIdempotents e) (s : Finset I) :
    ∏ i ∈ s, (1 - e i) = 1 - ∑ i ∈ s, e i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    simp [ih, sub_mul, mul_sub, he.mul_sum_of_notMem has, sub_sub]

variable {I : Type*} [Fintype I] {e : I → R}

theorem CompleteOrthogonalIdempotents.of_ker_isNilpotent (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    (he : ∀ i, IsIdempotentElem (e i))
    (he' : CompleteOrthogonalIdempotents (f ∘ e)) :
    CompleteOrthogonalIdempotents e :=
  of_ker_isNilpotent_of_isMulCentral f h he
    (fun _ ↦ Semigroup.mem_center_iff.mpr (mul_comm · _)) he'

lemma CompleteOrthogonalIdempotents.prod_one_sub
    (he : CompleteOrthogonalIdempotents e) :
    ∏ i, (1 - e i) = 0 := by
  rw [he.1.prod_one_sub, he.complete, sub_self]

lemma CompleteOrthogonalIdempotents.of_prod_one_sub
    (he : OrthogonalIdempotents e) (he' : ∏ i, (1 - e i) = 0) :
    CompleteOrthogonalIdempotents e where
  __ := he
  complete := by rwa [he.prod_one_sub, sub_eq_zero, eq_comm] at he'

/-- A family of complete orthogonal idempotents induces an isomorphism `R ≃+* ∏ R ⧸ ⟨1 - eᵢ⟩` -/
lemma CompleteOrthogonalIdempotents.bijective_pi (he : CompleteOrthogonalIdempotents e) :
    Function.Bijective (Pi.ringHom fun i ↦ Ideal.Quotient.mk (Ideal.span {1 - e i})) := by
  classical
  refine ⟨?_, he.1.surjective_pi⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  simp [funext_iff, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  suffices ∀ s : Finset I, (∏ i ∈ s, (1 - e i)) * x = x by
    rw [← this Finset.univ, he.prod_one_sub, zero_mul]
  refine fun s ↦ Finset.induction_on s (by simp) ?_
  intros a s has e'
  suffices (1 - e a) * x = x by simp [has, mul_assoc, e', this]
  obtain ⟨c, rfl⟩ := hx a
  rw [← mul_assoc, (he.idem a).one_sub.eq]

lemma CompleteOrthogonalIdempotents.bijective_pi' (he : CompleteOrthogonalIdempotents (1 - e ·)) :
    Function.Bijective (Pi.ringHom fun i ↦ Ideal.Quotient.mk (Ideal.span {e i})) := by
  obtain ⟨e', rfl, h⟩ : ∃ e' : I → R, (e' = e) ∧ Function.Bijective (Pi.ringHom fun i ↦
      Ideal.Quotient.mk (Ideal.span {e' i})) := ⟨_, funext (by simp), he.bijective_pi⟩
  exact h

lemma RingHom.pi_bijective_of_isIdempotentElem (e : I → R)
    (he : ∀ i, IsIdempotentElem (e i))
    (he₁ : ∀ i j, i ≠ j → (1 - e i) * (1 - e j) = 0) (he₂ : ∏ i, e i = 0) :
    Function.Bijective (Pi.ringHom fun i ↦ Ideal.Quotient.mk (Ideal.span {e i})) :=
  (CompleteOrthogonalIdempotents.of_prod_one_sub
      ⟨fun i ↦ (he i).one_sub, he₁⟩ (by simpa using he₂)).bijective_pi'

lemma RingHom.prod_bijective_of_isIdempotentElem {e f : R} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (hef₁ : e + f = 1) (hef₂ : e * f = 0) :
    Function.Bijective ((Ideal.Quotient.mk <| Ideal.span {e}).prod
      (Ideal.Quotient.mk <| Ideal.span {f})) := by
  let o (i : Fin 2) : R := match i with
    | 0 => e
    | 1 => f
  change Function.Bijective
    (piFinTwoEquiv _ ∘ Pi.ringHom (fun i : Fin 2 ↦ Ideal.Quotient.mk (Ideal.span {o i})))
  rw [(Equiv.bijective _).of_comp_iff']
  apply pi_bijective_of_isIdempotentElem
  · intro i
    fin_cases i <;> simpa [o]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      simp [o, mul_comm, hef₂, ← hef₁]
  · simpa

variable (R) in
/-- If `e` and `f` are idempotent elements such that `e + f = 1` and `e * f = 0`,
`S` is isomorphic as an `R`-algebra to `S ⧸ (e) × S ⧸ (f)`. -/
@[simps! -isSimp apply, simps! apply_fst apply_snd]
noncomputable def AlgEquiv.prodQuotientOfIsIdempotentElem
    {S : Type*} [CommRing S] [Algebra R S] {e f : S} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (hef₁ : e + f = 1) (hef₂ : e * f = 0) :
    S ≃ₐ[R] (S ⧸ Ideal.span {e}) × S ⧸ Ideal.span {f} :=
  AlgEquiv.ofBijective ((Ideal.Quotient.mkₐ _ _).prod (Ideal.Quotient.mkₐ _ _)) <|
    RingHom.prod_bijective_of_isIdempotentElem he hf hef₁ hef₂

end CommRing

section corner

variable {R : Type*} (e : R)

namespace Subsemigroup

variable [Semigroup R]

/-- The corner associated to an element `e` in a semigroup
is the subsemigroup of all elements of the form `e * r * e`. -/
def corner : Subsemigroup R where
  carrier := Set.range (e * · * e)
  mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * e * e * b, by simp_rw [mul_assoc]⟩

variable {e} (idem : IsIdempotentElem e)
include idem

lemma mem_corner_iff {r : R} : r ∈ corner e ↔ e * r = r ∧ r * e = r :=
  ⟨by rintro ⟨r, rfl⟩; simp_rw [← mul_assoc, idem.eq, mul_assoc, idem.eq, true_and],
    (⟨r, by simp_rw [·]⟩)⟩

lemma mem_corner_iff_mul_left (hc : IsMulCentral e) {r : R} : r ∈ corner e ↔ e * r = r := by
  rw [mem_corner_iff idem, and_iff_left_of_imp]; intro; rwa [← hc.comm]

lemma mem_corner_iff_mul_right (hc : IsMulCentral e) {r : R} : r ∈ corner e ↔ r * e = r := by
  rw [mem_corner_iff_mul_left idem hc, hc.comm]

lemma mem_corner_iff_mem_range_mul_left (hc : IsMulCentral e) {r : R} :
    r ∈ corner e ↔ r ∈ Set.range (e * ·) := by
  simp_rw [corner, mem_mk, Set.mem_range, ← (hc.comm _).eq, ← mul_assoc, idem.eq]

lemma mem_corner_iff_mem_range_mul_right (hc : IsMulCentral e) {r : R} :
    r ∈ corner e ↔ r ∈ Set.range (· * e) := by
  simp_rw [mem_corner_iff_mem_range_mul_left idem hc, (hc.comm _).eq]

/-- The corner associated to an idempotent `e` in a semiring without 1
is the semiring with `e` as 1 consisting of all element of the form `e * r * e`. -/
@[nolint unusedArguments]
def _root_.IsIdempotentElem.Corner (_ : IsIdempotentElem e) : Type _ := Subsemigroup.corner e

end Subsemigroup

/-- The corner associated to an element `e` in a semiring without 1
is the subsemiring without 1 of all elements of the form `e * r * e`. -/
def NonUnitalSubsemiring.corner [NonUnitalSemiring R] : NonUnitalSubsemiring R where
  __ := Subsemigroup.corner e
  add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by simp_rw [mul_add, add_mul]⟩
  zero_mem' := ⟨0, by simp_rw [mul_zero, zero_mul]⟩

/-- The corner associated to an element `e` in a ring without `
is the subring without 1 of all elements of the form `e * r * e`. -/
def NonUnitalRing.corner [NonUnitalRing R] : NonUnitalSubring R where
  __ := NonUnitalSubsemiring.corner e
  neg_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨-a, by simp_rw [mul_neg, neg_mul]⟩

instance [NonUnitalSemiring R] (idem : IsIdempotentElem e) : Semiring idem.Corner where
  __ : NonUnitalSemiring (NonUnitalSubsemiring.corner e) := inferInstance
  one := ⟨e, e, by simp_rw [idem.eq]⟩
  one_mul r := Subtype.ext ((Subsemigroup.mem_corner_iff idem).mp r.2).1
  mul_one r := Subtype.ext ((Subsemigroup.mem_corner_iff idem).mp r.2).2

instance [NonUnitalCommSemiring R] (idem : IsIdempotentElem e) : CommSemiring idem.Corner where
  __ : NonUnitalCommSemiring (NonUnitalSubsemiring.corner e) := inferInstance
  __ : Semiring idem.Corner := inferInstance

instance [NonUnitalRing R] (idem : IsIdempotentElem e) : Ring idem.Corner where
  __ : NonUnitalRing (NonUnitalRing.corner e) := inferInstance
  __ : Semiring idem.Corner := inferInstance

instance [NonUnitalCommRing R] (idem : IsIdempotentElem e) : CommRing idem.Corner where
  __ : NonUnitalCommRing (NonUnitalRing.corner e) := inferInstance
  __ : Semiring idem.Corner := inferInstance

variable {I : Type*} [Fintype I] {e : I → R}

/-- A complete orthogonal family of central idempotents in a semiring
give rise to a direct product decomposition. -/
def CompleteOrthogonalIdempotents.ringEquivOfIsMulCentral [Semiring R]
    (he : CompleteOrthogonalIdempotents e) (hc : ∀ i, IsMulCentral (e i)) :
    R ≃+* Π i, (he.idem i).Corner where
  toFun r i := ⟨_, r, rfl⟩
  invFun r := ∑ i, (r i).1
  left_inv r := by
    simp_rw [((hc _).comm _).eq, mul_assoc, (he.idem _).eq, ← Finset.mul_sum, he.complete, mul_one]
  right_inv r := funext fun i ↦ Subtype.ext <| by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_eq_single i _ (by simp at ·)]
    · have ⟨r', eq⟩ := (r i).2
      rw [← eq]; simp_rw [← mul_assoc, (he.idem i).eq, mul_assoc, (he.idem i).eq]
    · intro j _ ne; have ⟨r', eq⟩ := (r j).2
      rw [← eq]; simp_rw [← mul_assoc, he.ortho ne.symm, zero_mul]
  map_mul' r₁ r₂ := funext fun i ↦ Subtype.ext <|
    calc e i * (r₁ * r₂) * e i
     _ = e i * (r₁ * e i * r₂) * e i := by
       simp_rw [← ((hc i).comm r₁).eq, ← mul_assoc, (he.idem i).eq]
     _ = e i * r₁ * e i * (e i * r₂ * e i) := by
      conv in (r₁ * _ * r₂) => rw [← (he.idem i).eq]
      simp_rw [mul_assoc]
  map_add' r₁ r₂ := funext fun i ↦ Subtype.ext <| by simpa [mul_add] using add_mul ..

/-- A complete orthogonal family of idempotents in a commutative semiring
give rise to a direct product decomposition. -/
def CompleteOrthogonalIdempotents.ringEquivOfComm [CommSemiring R]
    (he : CompleteOrthogonalIdempotents e) : R ≃+* Π i, (he.idem i).Corner :=
  he.ringEquivOfIsMulCentral fun _ ↦ Semigroup.mem_center_iff.mpr fun _ ↦ mul_comm ..

@[deprecated (since := "2025-04-14")] alias CompleteOrthogonalIdempotents.mulEquivOfIsMulCentral :=
  CompleteOrthogonalIdempotents.ringEquivOfIsMulCentral

@[deprecated (since := "2025-04-14")] alias CompleteOrthogonalIdempotents.mulEquivOfComm :=
  CompleteOrthogonalIdempotents.ringEquivOfComm

end corner
