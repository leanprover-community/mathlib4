/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Algebra.Polynomial.Div

/-!

# Evaluation of power series

## Main definition
- `PowerSeries.eval`:
  `p.eval x` is the evaluation of `p : R⟦X⟧` at `x`,
  and `0` if the former is not well defined.
- `PowerSeries.evalAlgHom`: The evaluation map as an algebraic homomorphism.

-/

namespace PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S]
variable (x : R)

abbrev _root_.IsHausdorffAt : Prop := IsHausdorff (.span {x}) R
abbrev _root_.IsPrecompleteAt : Prop := IsPrecomplete (.span {x}) R
abbrev _root_.IsAdicCompleteAt : Prop := IsAdicComplete (.span {x}) R

variable {x} in
lemma _root_.isHausdorffAt_iff :
    IsHausdorffAt x ↔ ⨅ i, Ideal.span {x ^ i} = ⊥ := by
  simp [isHausdorff_iff, SModEq.zero, ← le_bot_iff, SetLike.le_def, Ideal.span_singleton_pow]

/--
`p : R⟦X⟧` evaluates to `a` at `x` (`p.EvalEq x a`) if `∑ᵢⁿ⁻¹ pᵢxⁱ ≡ a (mod xⁿ)` for all `n`.
-/
def EvalEq (p : R⟦X⟧) (a : R) : Prop := ∀ i, x ^ i ∣ (p.trunc i).eval x - a

variable {x}

lemma EvalEq.mk_eval_trunc {p : R⟦X⟧} {a : R} (h : p.EvalEq x a) (i) :
    Ideal.Quotient.mk (.span {x ^ i}) ((p.trunc i).eval x) = Ideal.Quotient.mk _ a := by
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_dvd]
  exact h i

lemma EvalEq.of_mk_eval_trunc {p : R⟦X⟧} {a : R}
    (H : ∀ i, Ideal.Quotient.mk (.span {x ^ i}) ((p.trunc i).eval x) = Ideal.Quotient.mk _ a) :
    p.EvalEq x a := by
  intro i
  rw [← Ideal.Quotient.eq_zero_iff_dvd, map_sub, sub_eq_zero]
  exact H i

lemma EvalEq.add {p q : R⟦X⟧} {a b : R} (h₁ : p.EvalEq x a) (h₂ : q.EvalEq x b) :
    (p + q).EvalEq x (a + b) := by
  intro i
  rw [trunc_add, Polynomial.eval_add, add_sub_add_comm]
  exact (h₁ i).add (h₂ i)

lemma EvalEq.mul {p q : R⟦X⟧} {a b : R} (h₁ : p.EvalEq x a) (h₂ : q.EvalEq x b) :
    (p * q).EvalEq x (a * b) := by
  refine .of_mk_eval_trunc fun i ↦ ?_
  rw [map_mul, ← h₁.mk_eval_trunc i, ← h₂.mk_eval_trunc i, ← map_mul, ← sub_eq_zero, ← map_sub,
    Ideal.Quotient.eq_zero_iff_dvd, ← Polynomial.eval_mul, ← Polynomial.eval_sub]
  suffices .X ^ i ∣ trunc i (p * q) - trunc i p * trunc i q by
    obtain ⟨r, hr⟩ := this
    rw [hr, mul_comm, Polynomial.eval_mul_X_pow]
    exact dvd_mul_left _ _
  rw [Polynomial.X_pow_dvd_iff]
  intro d hdi
  simp only [Polynomial.coeff_sub, coeff_trunc, hdi, ↓reduceIte, coeff_mul, Polynomial.coeff_mul,
    mul_ite, ite_mul, zero_mul, mul_zero, sub_eq_zero]
  congr! 1 with r hr
  rw [if_pos ((Finset.antidiagonal.fst_le hr).trans_lt hdi),
    if_pos ((Finset.antidiagonal.snd_le hr).trans_lt hdi)]

variable (x) in
protected
lemma EvalEq.C (r : R) : (C R r).EvalEq x r := by rintro (_ | _) <;> simp

lemma EvalEq.zero_iff {a : R} :
    (0 : R⟦X⟧).EvalEq x a ↔ a ∈ ⨅ i, Ideal.span {x ^ i} := by
  simp [EvalEq, Ideal.mem_span_singleton]

/-- A variant of `EvalEq.zero_iff` that assumes `R` is hausdorff at `x`. -/
lemma EvalEq.zero_iff' [IsHausdorffAt x] {a : R} :
    (0 : R⟦X⟧).EvalEq x a ↔ a = 0 := by
  rw [EvalEq.zero_iff, isHausdorffAt_iff.mp ‹_›, Ideal.mem_bot]

variable (x) in
protected lemma EvalEq.zero : (0 : R⟦X⟧).EvalEq x 0 := by simp [zero_iff]

variable (x) in
protected lemma EvalEq.one : (1 : R⟦X⟧).EvalEq x 1 := by simpa using .C x 1

variable (x) in
protected lemma EvalEq.X : X.EvalEq x x := by rintro (_ | _ | _) <;> simp

lemma EvalEq.C_mul {p : R⟦X⟧} {a : R} (h : p.EvalEq x a) (r : R) :
    (C R r * p).EvalEq x (r * a) := (EvalEq.C x r).mul h

lemma EvalEq.neg {p : R⟦X⟧} {a : R} (h : p.EvalEq x a) :
    (-p).EvalEq x (-a) := by
  simpa using h.C_mul (-1)

lemma EvalEq.sub {p q : R⟦X⟧} {a b : R} (h₁ : p.EvalEq x a) (h₂ : q.EvalEq x b) :
    (p - q).EvalEq x (a - b) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

lemma EvalEq.ext [IsHausdorffAt x]
    {p : R⟦X⟧} {a b : R} (h₁ : p.EvalEq x a) (h₂ : p.EvalEq x b) :
    a = b := by
  rw [← sub_eq_zero, ← zero_iff' (x := x)]
  exact sub_self p ▸ h₁.sub h₂

lemma EvalEq.prod {ι : Type*} (s : Finset ι) (p : ι → R⟦X⟧) (r : ι → R)
    (H : ∀ i ∈ s, (p i).EvalEq x (r i)) : (∏ i ∈ s, p i).EvalEq x (∏ i ∈ s, r i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using .one x
  | @insert i s his IH =>
    rw [Finset.prod_insert his, Finset.prod_insert his]
    exact .mul (H _ (by simp)) (IH (fun i hi ↦ H _ (by simp [hi])))

lemma EvalEq.sum {ι : Type*} (s : Finset ι) (p : ι → R⟦X⟧) (r : ι → R)
    (H : ∀ i ∈ s, (p i).EvalEq x (r i)) : (∑ i ∈ s, p i).EvalEq x (∑ i ∈ s, r i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using .zero x
  | @insert i s his IH =>
    rw [Finset.sum_insert his, Finset.sum_insert his]
    exact .add (H _ (by simp)) (IH (fun i hi ↦ H _ (by simp [hi])))

lemma EvalEq.pow {p : R⟦X⟧} {a : R} (h : p.EvalEq x a) (n : ℕ) :
    (p ^ n).EvalEq x (a ^ n) := by
  simpa using EvalEq.prod (Finset.range n) (fun _ ↦ p) (fun _ ↦ a) (fun _ _ ↦ h)

lemma EvalEq.eval_trunc (p : R⟦X⟧) {n} (hx : x ^ n = 0) :
    (p : R⟦X⟧).EvalEq x ((p.trunc n).eval x) := by
  intro m
  cases' le_total m n with hmn hmn
  · obtain ⟨r, hr⟩ : .X ^ m ∣ trunc m ↑(trunc n p) - trunc n p := by
      simp +contextual [Polynomial.X_pow_dvd_iff, coeff_trunc]
    rw [← trunc_trunc_of_le p hmn, ← Polynomial.eval_sub, hr, mul_comm, Polynomial.eval_mul_X_pow]
    exact dvd_mul_left _ _
  · obtain ⟨k, rfl⟩ := exists_add_of_le hmn
    simp [Polynomial.eval, eval₂_trunc_eq_sum_range, Finset.sum_range_add, pow_add, hx]

variable (x) in
lemma evalEq_coe (p : Polynomial R) :
    (p : R⟦X⟧).EvalEq x (p.eval x) := by
  intro i
  obtain ⟨r, hr⟩ : .X ^ i ∣ trunc i ↑p - p := by
    simp +contextual [Polynomial.X_pow_dvd_iff, coeff_trunc]
  rw [← Polynomial.eval_sub, hr, mul_comm, Polynomial.eval_mul_X_pow]
  exact dvd_mul_left _ _

lemma evalEq_map_C_X (p : R⟦X⟧) : (p.map (C R)).EvalEq X p := by
  intro i
  rw [trunc_map, Polynomial.eval_map, Polynomial.eval₂_C_X_eq_coe, X_pow_dvd_iff]
  simp +contextual [coeff_trunc]

lemma EvalEq.map {p : R⟦X⟧} {a : R} (h : p.EvalEq x a) (f : R →+* S) :
    (p.map f).EvalEq (f x) (f a) := by
  intro i
  rw [trunc_map, Polynomial.eval_map, Polynomial.eval₂_hom, ← map_sub, ← map_pow]
  exact map_dvd f (h i)

lemma evalEq_map_comp_C (f : R⟦X⟧ →+* S) (p : R⟦X⟧) :
    (p.map (f.comp (C R))).EvalEq (f .X) (f p) :=
  (evalEq_map_C_X p).map f

lemma evalEq_map_algebraMap [Algebra R S] (f : R⟦X⟧ →ₐ[R] S) (p : R⟦X⟧) :
    (p.map (algebraMap R S)).EvalEq (f .X) (f p) :=
  f.comp_algebraMap ▸ evalEq_map_comp_C f.toRingHom p

@[ext (iff := false) 1100]
lemma ringHom_ext (f g : R⟦X⟧ →+* S)
    (hC : f.comp (C R) = g.comp (C R))
    (hX : f .X = g .X) (hX' : IsHausdorffAt (f .X) := by infer_instance) :
    f = g :=
  RingHom.ext fun p ↦
    EvalEq.ext (evalEq_map_comp_C f p) (Eq.symm hC ▸ Eq.symm hX ▸ evalEq_map_comp_C g p)

@[ext (iff := false) 1100]
lemma algHom_ext [Algebra R S] (f g : R⟦X⟧ →ₐ[R] S)
    (hX : f .X = g .X) (hX' : IsHausdorffAt (f .X) := by infer_instance) :
    f = g :=
  AlgHom.ext (DFunLike.congr_fun (ringHom_ext f.toRingHom g.toRingHom
    (f.comp_algebraMap.trans g.comp_algebraMap.symm) hX hX') : _)

variable (x) in
/-- `convergesAt x` is the set of power series that converge at `x`. -/
def convergesAt : Subalgebra (Polynomial R) R⟦X⟧ where
  carrier := { p | ∃ a, p.EvalEq x a }
  mul_mem' {p q} hp hq := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := And.intro hp hq
    exact ⟨a * b, ha.mul hb⟩
  add_mem' {p q} hp hq := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := And.intro hp hq
    exact ⟨a + b, ha.add hb⟩
  algebraMap_mem' p := ⟨p.eval x, evalEq_coe x p⟩

lemma convergesAt_eq_top_iff :
    convergesAt x = ⊤ ↔ IsPrecompleteAt x := by
  simp only [IsPrecompleteAt, isPrecomplete_iff, Ideal.span_singleton_pow, smul_eq_mul,
    Ideal.mul_top, SModEq.sub_mem, Ideal.mem_span_singleton, ← top_le_iff, SetLike.le_def,
    Algebra.mem_top, forall_const]
  constructor
  · intro H f hf
    choose g hg using fun i : ℕ ↦ dvd_sub_comm.mp (hf i.le_succ)
    simp_rw [sub_eq_iff_eq_add] at hg
    let p := mk g + C R (f 0)
    obtain ⟨L, hL⟩ := @H p
    have (n) : (trunc (n + 1) p).eval x = f (n + 1) := by
      induction n with
      | zero => simp [p, hg]
      | succ n IH =>
        rw [hg, trunc_succ, Polynomial.eval_add, IH, add_comm]
        simp [p, mul_comm]
    refine ⟨L, fun n ↦ ?_⟩
    cases n
    · simp
    rw [← this]
    exact hL _
  · intro hx p
    refine hx (fun i ↦ (p.trunc i).eval x) (fun {m n} h ↦ ?_)
    obtain ⟨r, hr⟩ : .X ^ m ∣ trunc m p - trunc n p := by
      rw [← trunc_trunc_of_le _ h]
      simp +contextual [Polynomial.X_pow_dvd_iff, coeff_trunc _ m]
    rw [← Polynomial.eval_sub, hr, mul_comm, Polynomial.eval_mul_X_pow]
    exact dvd_mul_left _ _

lemma convergesAt_eq_top (x : R) [IsPrecompleteAt x] :
    convergesAt x = ⊤ := convergesAt_eq_top_iff.mpr ‹_›

/-- `p.eval x` is the evaluation of `p : R⟦X⟧` at `x`, and `0` if the former is not well defined. -/
noncomputable
def eval (p : R⟦X⟧) (x : R) : R :=
  letI := Classical.propDecidable
  if h₁ : ∃ q : Polynomial R, p = q then h₁.choose.eval x
  else if h₂ : p ∈ convergesAt x then h₂.choose else 0

@[simp] lemma eval_coe (p : Polynomial R) (x : R) : (p : R⟦X⟧).eval x = p.eval x := by
  rw [eval, dif_pos ⟨p, rfl⟩]
  congr 1
  apply Polynomial.coe_injective
  exact .symm (Exists.choose_spec (p := fun q : Polynomial R ↦ (p : R⟦X⟧) = q) _)

@[simp] lemma eval_zero : (0 : R⟦X⟧).eval x = 0 := by simpa using eval_coe 0 x
@[simp] lemma eval_one : (1 : R⟦X⟧).eval x = 1 := by simpa using eval_coe 1 x
@[simp] lemma eval_X : (X : R⟦X⟧).eval x = x := by simpa using eval_coe .X x
@[simp] lemma eval_C (r : R) : (C R r : R⟦X⟧).eval x = r := by simpa using eval_coe (.C r) x

@[simp] lemma eval_X_pow (n : ℕ) : (X ^ n : R⟦X⟧).eval x = x ^ n := by
  simpa using eval_coe (Polynomial.X ^ n) x

lemma evalEq_eval_of_mem {p} (hp : p ∈ convergesAt x) :
    p.EvalEq x (p.eval x) := by
  by_cases h : ∃ q : Polynomial R, p = q
  · obtain ⟨q, rfl⟩ := h
    exact eval_coe q x ▸ evalEq_coe x q
  rw [eval, dif_neg h, dif_pos hp]
  exact hp.choose_spec

lemma evalEq_eval (p : R⟦X⟧) (x : R) [IsPrecompleteAt x] :
    p.EvalEq x (p.eval x) :=
  evalEq_eval_of_mem (convergesAt_eq_top x ▸ Algebra.mem_top)

section eval

variable [IsHausdorffAt x]

lemma EvalEq.eval_eq {p : R⟦X⟧} {a : R} (h : p.EvalEq x a) :
    p.eval x = a :=
  (evalEq_eval_of_mem ⟨_, h⟩).ext h

lemma eval_eq_eval_trunc {n} (h : x ^ n = 0) (p : R⟦X⟧) :
    p.eval x = (p.trunc n).eval x :=
  (EvalEq.eval_trunc _ h).eval_eq

variable (x) in
/-- `PowerSeries.eval` as an algebra homomorphism from the subalgebra of converging power series. -/
@[simps]
noncomputable
def convergesAtEval : convergesAt x →ₐ[R] R where
  toFun p := p.1.eval x
  map_one' := by simp
  map_mul' p q := (evalEq_eval_of_mem (mul_mem p.2 q.2)).ext
    ((evalEq_eval_of_mem p.2).mul (evalEq_eval_of_mem q.2))
  map_zero' := by simp
  map_add' p q := (evalEq_eval_of_mem (add_mem p.2 q.2)).ext
    ((evalEq_eval_of_mem p.2).add (evalEq_eval_of_mem q.2))
  commutes' r := by simp

lemma convergesAtEval_algebraMap (p : Polynomial R) :
    convergesAtEval x (algebraMap _ _ p) = p.eval x := by
  rw [convergesAtEval_apply, ← eval_coe]; rfl

end eval

variable (x) in
/-- `PowerSeries.eval` as an algebra homomorphism if `R` is adic-complete at `x`. -/
@[simps] noncomputable
def evalAlgHom [IsAdicCompleteAt x] : R⟦X⟧ →ₐ[R] R where
  toFun := eval (x := x)
  map_one' := by simp
  map_mul' p q := ((p * q).evalEq_eval x).ext ((p.evalEq_eval x).mul (q.evalEq_eval x))
  map_zero' := by simp
  map_add' p q := ((p + q).evalEq_eval x).ext ((p.evalEq_eval x).add (q.evalEq_eval x))
  commutes' := by simp

lemma map_X_mem_jacobson (f : R⟦X⟧ →ₐ[R] R) : f X ∈ Ideal.jacobson ⊥ := by
    rw [Ideal.mem_jacobson_bot]
    intro y
    have : IsUnit (X * C R y + 1) := by simp [isUnit_iff_constantCoeff]
    simpa [← algebraMap_eq] using this.map f

instance _root_.IsAdicCompleteAt.of_algHom [IsNoetherianRing R]
  (f : R⟦X⟧ →ₐ[R] R) : IsAdicCompleteAt (f X) := by
  apply (config := { allowSynthFailures := true }) IsAdicComplete.mk
  · refine .of_le_jacobson _ _ ?_
    rw [Ideal.span_singleton_le_iff_mem]
    exact map_X_mem_jacobson f
  · rw [← IsPrecompleteAt, ← convergesAt_eq_top_iff, ← top_le_iff]
    intro p _
    exact ⟨_, evalEq_map_algebraMap f p⟩

/-- If `R` is a noetherian ring, sections of `R → R⟦X⟧` corresponds bijectively to
evaluating at adic-complete elements. -/
@[simps]
noncomputable
def algHomEquiv [IsNoetherianRing R] :
    (R⟦X⟧ →ₐ[R] R) ≃ { x : R // IsAdicCompleteAt x } where
  toFun f := ⟨f X, IsAdicCompleteAt.of_algHom f⟩
  invFun := fun ⟨x, hx⟩ ↦ evalAlgHom x
  left_inv f := by
    ext
    · simp
    · simpa using (IsAdicCompleteAt.of_algHom f).1
  right_inv x := by simp

end PowerSeries
