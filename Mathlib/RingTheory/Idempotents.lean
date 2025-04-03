/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Ideal.QuotientOperations
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
section Ring

variable {R S : Type*} [Ring R] [Ring S] (f : R →+* S)

theorem isIdempotentElem_one_sub_one_sub_pow_pow
    (x : R) (n : ℕ) (hx : (x - x ^ 2) ^ n = 0) :
    IsIdempotentElem (1 - (1 - x ^ n) ^ n) := by
  let P : Polynomial ℤ := 1 - (1 - .X ^ n) ^ n
  have : (.X - .X ^ 2) ^ n ∣ P - P ^ 2 := by
    have H₁ : .X ^ n ∣ P := by
      have := sub_dvd_pow_sub_pow 1 ((1 : Polynomial ℤ) - Polynomial.X ^ n) n
      rwa [sub_sub_cancel, one_pow] at this
    have H₂ : (1 - .X) ^ n ∣ 1 - P := by
      simp only [sub_sub_cancel, P]
      simpa using pow_dvd_pow_of_dvd (sub_dvd_pow_sub_pow (α := Polynomial ℤ) 1 Polynomial.X n) n
    have := mul_dvd_mul H₁ H₂
    simpa only [← mul_pow, mul_sub, mul_one, ← pow_two] using this
  have := map_dvd (Polynomial.aeval x) this
  simp only [map_pow, map_sub, Polynomial.aeval_X, hx, map_one, zero_dvd_iff, P] at this
  rwa [sub_eq_zero, eq_comm, pow_two] at this

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
    simp [RingHom.mem_ker, mul_sub, pow_two, ha, he₁.eq]
  obtain ⟨n, hn⟩ := h _ hx'
  refine ⟨_, isIdempotentElem_one_sub_one_sub_pow_pow _ _ hn, ?_, ?_⟩
  · cases' n with n
    · simp at hn
    simp only [map_sub, map_one, map_pow, ha, he₁.pow_succ_eq,
      he₁.one_sub.pow_succ_eq, sub_sub_cancel]
  · obtain ⟨k, hk⟩ := (Commute.one_left (MulOpposite.op <| 1 - a ^ n)).sub_dvd_pow_sub_pow n
    apply_fun MulOpposite.unop at hk
    have : 1 - (1 - a ^ n) ^ n = MulOpposite.unop k * a ^ n := by simpa using hk
    rw [this, mul_assoc]
    cases' n with n
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

variable {I : Type*} (e : I → R)

/-- A family `{ eᵢ }` of idempotent elements is orthogonal if `eᵢ * eⱼ = 0` for all `i ≠ j`. -/
@[mk_iff]
structure OrthogonalIdempotents : Prop where
  idem : ∀ i, IsIdempotentElem (e i)
  ortho : ∀ i j, i ≠ j → e i * e j = 0

variable {e}
variable (he : OrthogonalIdempotents e)

lemma OrthogonalIdempotents.mul_eq [DecidableEq I] (he : OrthogonalIdempotents e) (i j) :
    e i * e j = if i = j then e i else 0 := by
  split
  · simp [*, (he.idem j).eq]
  · exact he.ortho _ _ ‹_›

lemma OrthogonalIdempotents.iff_mul_eq [DecidableEq I] :
    OrthogonalIdempotents e ↔ ∀ i j, e i * e j = if i = j then e i else 0 :=
  ⟨mul_eq, fun H ↦ ⟨fun i ↦ by simpa using H i i, fun i j e ↦ by simpa [e] using H i j⟩⟩

lemma OrthogonalIdempotents.isIdempotentElem_sum [Fintype I] : IsIdempotentElem (∑ i, e i) := by
  classical
  simp [IsIdempotentElem, Finset.sum_mul, Finset.mul_sum, he.mul_eq]

lemma OrthogonalIdempotents.map :
    OrthogonalIdempotents (f ∘ e) := by
  classical
  simp [iff_mul_eq, he.mul_eq, ← map_mul f, apply_ite f]

lemma OrthogonalIdempotents.map_injective_iff (hf : Function.Injective f) :
    OrthogonalIdempotents (f ∘ e) ↔ OrthogonalIdempotents e := by
  classical
  simp [iff_mul_eq, ← hf.eq_iff, apply_ite]

lemma OrthogonalIdempotents.embedding {J} (i : J ↪ I) :
    OrthogonalIdempotents (e ∘ i) := by
  classical
  simp [iff_mul_eq, he.mul_eq]

lemma OrthogonalIdempotents.equiv {J} (i : J ≃ I) :
    OrthogonalIdempotents (e ∘ i) ↔ OrthogonalIdempotents e := by
  classical
  simp [iff_mul_eq, i.forall_congr_left]

lemma OrthogonalIdempotents.unique [Unique I] :
    OrthogonalIdempotents e ↔ IsIdempotentElem (e default) := by
  simp [orthogonalIdempotents_iff, Unique.forall_iff]

lemma OrthogonalIdempotents.option [Fintype I] (x)
    (hx : IsIdempotentElem x) (hx₁ : x * ∑ i, e i = 0) (hx₂ : (∑ i, e i) * x = 0) :
    OrthogonalIdempotents (Option.elim · x e) where
  idem i := i.rec hx he.idem
  ortho i j ne := by
    classical
    cases' i with i <;> cases' j with j
    · cases ne rfl
    · simpa only [mul_assoc, Finset.sum_mul, he.mul_eq, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, zero_mul] using congr_arg (· * e j) hx₁
    · simpa only [Option.elim_some, Option.elim_none, ← mul_assoc, Finset.mul_sum, he.mul_eq,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, mul_zero] using congr_arg (e i * ·) hx₂
    · exact he.ortho i j (Option.some_inj.ne.mp ne)

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
      (by simp [Finset.mul_sum, h₂', he.mul_eq, Fin.succ_ne_zero, eq_comm])
      (by simp [Finset.sum_mul, h₂', he.mul_eq, Fin.succ_ne_zero])
    refine ⟨_, (h₁.option _ h₃ h₅ h₆).embedding (finSuccEquiv n).toEmbedding, funext fun i ↦ ?_⟩
    obtain ⟨_ | i, rfl⟩ := (finSuccEquiv n).symm.surjective i <;> simp [*]

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

variable [Fintype I]

/--
A family `{ eᵢ }` of idempotent elements is complete orthogonal if
1. (orthogonal) `eᵢ * eⱼ = 0` for all `i ≠ j`.
2. (complete) `∑ eᵢ = 1`
-/
@[mk_iff]
structure CompleteOrthogonalIdempotents (e : I → R) extends OrthogonalIdempotents e : Prop where
  complete : ∑ i, e i = 1

variable (he : CompleteOrthogonalIdempotents e)

lemma CompleteOrthogonalIdempotents.unique_iff [Unique I] :
    CompleteOrthogonalIdempotents e ↔ e default = 1 := by
  rw [completeOrthogonalIdempotents_iff, orthogonalIdempotents_iff]
  simp only [Unique.forall_iff, ne_eq, not_true_eq_false, false_implies, and_true,
    Finset.univ_unique, Finset.sum_singleton, and_iff_right_iff_imp]
  exact (· ▸ IsIdempotentElem.one)

lemma CompleteOrthogonalIdempotents.pair_iff {x y : R} :
    CompleteOrthogonalIdempotents ![x, y] ↔ IsIdempotentElem x ∧ y = 1 - x := by
  rw [completeOrthogonalIdempotents_iff, orthogonalIdempotents_iff, and_assoc]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.forall_fin_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ne_eq, not_true_eq_false,
    false_implies, zero_ne_one, not_false_eq_true, true_implies, true_and, one_ne_zero,
    and_true, and_self, Fin.sum_univ_two, eq_sub_iff_add_eq, @add_comm _ _ y]
  constructor
  · exact fun h ↦ ⟨h.1.1, h.2.2⟩
  · rintro ⟨h₁, h₂⟩
    obtain rfl := eq_sub_iff_add_eq'.mpr h₂
    exact ⟨⟨h₁, h₁.one_sub⟩, ⟨by simp [mul_sub, h₁.eq], by simp [sub_mul, h₁.eq]⟩, h₂⟩

lemma CompleteOrthogonalIdempotents.of_isIdempotentElem {e : R} (he : IsIdempotentElem e) :
    CompleteOrthogonalIdempotents ![e, 1 - e] :=
  pair_iff.mpr ⟨he, rfl⟩

lemma CompleteOrthogonalIdempotents.single {I : Type*} [Fintype I] [DecidableEq I]
    (R : I → Type*) [∀ i, Ring (R i)] :
    CompleteOrthogonalIdempotents (Pi.single (f := R) · 1) := by
  refine ⟨⟨by simp [IsIdempotentElem, ← Pi.single_mul], ?_⟩, Finset.univ_sum_single 1⟩
  intros i j hij
  ext k
  by_cases hi : i = k
  · subst hi; simp [hij]
  · simp [hi]

lemma CompleteOrthogonalIdempotents.map :
    CompleteOrthogonalIdempotents (f ∘ e) where
  __ := he.toOrthogonalIdempotents.map f
  complete := by simp only [Function.comp_apply, ← map_sum, he.complete, map_one]

lemma CompleteOrthogonalIdempotents.map_injective_iff (hf : Function.Injective f) :
    CompleteOrthogonalIdempotents (f ∘ e) ↔ CompleteOrthogonalIdempotents e := by
  simp [completeOrthogonalIdempotents_iff, ← hf.eq_iff, apply_ite,
    OrthogonalIdempotents.map_injective_iff f hf]

lemma CompleteOrthogonalIdempotents.equiv {J} [Fintype J] (i : J ≃ I) :
    CompleteOrthogonalIdempotents (e ∘ i) ↔ CompleteOrthogonalIdempotents e := by
  simp only [completeOrthogonalIdempotents_iff, OrthogonalIdempotents.equiv, Function.comp_apply,
    and_congr_right_iff, Fintype.sum_equiv i _ e (fun _ ↦ rfl)]

lemma CompleteOrthogonalIdempotents.option (he : OrthogonalIdempotents e) :
    CompleteOrthogonalIdempotents (Option.elim · (1 - ∑ i, e i) e) where
  __ := he.option _ he.isIdempotentElem_sum.one_sub
    (by simp [sub_mul, he.isIdempotentElem_sum.eq]) (by simp [mul_sub, he.isIdempotentElem_sum.eq])
  complete := by
    rw [Fintype.sum_option]
    exact sub_add_cancel _ _

@[nontriviality]
lemma CompleteOrthogonalIdempotents.of_subsingleton [Subsingleton R] :
    CompleteOrthogonalIdempotents e :=
  ⟨⟨fun _ ↦ Subsingleton.elim _ _, fun _ _ _ ↦ Subsingleton.elim _ _⟩, Subsingleton.elim _ _⟩

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
  cases' n with n
  · simpa using he.complete
  obtain ⟨e', h₁, h₂⟩ := OrthogonalIdempotents.lift_of_isNilpotent_ker f h he.1 he'
  refine ⟨_, (equiv (finSuccEquiv n)).mpr
    (CompleteOrthogonalIdempotents.option (h₁.embedding (Fin.succEmb _))), funext fun i ↦ ?_⟩
  have (i) : f (e' i) = e i := congr_fun h₂ i
  obtain ⟨_ | i, rfl⟩ := (finSuccEquiv n).symm.surjective i
  · simp only [Fin.val_succEmb, Function.comp_apply, finSuccEquiv_symm_none, finSuccEquiv_zero,
      Option.elim_none, map_sub, map_one, map_sum, this, ← he.complete, sub_eq_iff_eq_add,
      Fin.sum_univ_succ]
  · simp [this]

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
    simp only [← mul_assoc, he₁.eq, he₂.eq]
    abel
  obtain ⟨n, hn⟩ := H
  have : (e₁ - e₂) ^ (2 * n + 1) = (e₁ - e₂) := by
    clear hn; induction n <;> simp [mul_add, add_assoc, pow_add _ (2 * _) 3, this, ← pow_succ, *]
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
  exact ⟨1, e i, by simp [mul_sub, sub_mul, he.ortho i j hij]⟩

variable {I : Type*} [Fintype I] {e : I → R}

theorem CompleteOrthogonalIdempotents.of_ker_isNilpotent (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    (he : ∀ i, IsIdempotentElem (e i))
    (he' : CompleteOrthogonalIdempotents (f ∘ e)) :
    CompleteOrthogonalIdempotents e :=
  of_ker_isNilpotent_of_isMulCentral f h he
    (fun _ ↦ Semigroup.mem_center_iff.mpr (mul_comm · _)) he'

lemma OrthogonalIdempotents.prod_one_sub (he : OrthogonalIdempotents e) :
    ∏ i, (1 - e i) = 1 - ∑ i, e i := by
  classical
  induction' (@Finset.univ I _) using Finset.induction_on with a s has ih
  · simp
  · suffices (1 - e a) * (1 - ∑ i in s, e i) = 1 - (e a + ∑ i in s, e i) by simp [*]
    have : e a * ∑ i in s, e i = 0 := by
      rw [Finset.mul_sum, ← Finset.sum_const_zero (s := s)]
      exact Finset.sum_congr rfl fun j hj ↦ he.ortho a j (fun e ↦ has (e ▸ hj))
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, this, sub_zero, sub_sub, add_comm]

lemma CompleteOrthogonalIdempotents.prod_one_sub (he : CompleteOrthogonalIdempotents e) :
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
  simp [Function.funext_iff, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  suffices ∀ s : Finset I, (∏ i in s, (1 - e i)) * x = x by
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

lemma bijective_pi_of_isIdempotentElem (e : I → R)
    (he : ∀ i, IsIdempotentElem (e i))
    (he₁ : ∀ i j, i ≠ j → (1 - e i) * (1 - e j) = 0) (he₂ : ∏ i, e i = 0) :
    Function.Bijective (Pi.ringHom fun i ↦ Ideal.Quotient.mk (Ideal.span {e i})) :=
  (CompleteOrthogonalIdempotents.of_prod_one_sub
      ⟨fun i ↦ (he i).one_sub, he₁⟩ (by simpa using he₂)).bijective_pi'

end CommRing
