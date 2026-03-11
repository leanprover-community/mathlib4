/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Arend Mellendijk, Michael Rothgang
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Field.Power  -- shake: keep (Qq dependency)
public import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
public meta import Mathlib.Util.Qq

/-! # Lemmas for the field_simp tactic

-/

public section

open List

namespace Mathlib.Tactic.FieldSimp
@[expose] public section

section zpow'

variable {α : Type*}

section
variable [GroupWithZero α]

open Classical in
/-- This is a variant of integer exponentiation, defined for internal use in the `field_simp` tactic
implementation. It differs from the usual integer exponentiation in that `0 ^ 0` is `0`, not `1`.
With this choice, the function `n ↦ a ^ n` is always a homomorphism (`a ^ (n + m) = a ^ n * a ^ m`),
even if `a` is zero. -/
noncomputable def zpow' (a : α) (n : ℤ) : α :=
  if a = 0 ∧ n = 0 then 0 else a ^ n

theorem zpow'_add (a : α) (m n : ℤ) :
    zpow' a (m + n) = zpow' a m * zpow' a n := by
  by_cases ha : a = 0
  · simp [zpow', ha]
    by_cases hn : n = 0
    · simp +contextual [hn, zero_zpow]
    · simp +contextual [hn, zero_zpow]
  · simp [zpow', ha, zpow_add₀]

theorem zpow'_of_ne_zero_right (a : α) (n : ℤ) (hn : n ≠ 0) : zpow' a n = a ^ n := by
  simp [zpow', hn]

theorem zpow'_of_ne_zero_left (a : α) (n : ℤ) (ha : a ≠ 0) : zpow' a n = a ^ n := by
  simp [zpow', ha]

@[simp]
lemma zero_zpow' (n : ℤ) : zpow' (0 : α) n = 0 := by
  simp +contextual only [zpow', true_and, ite_eq_left_iff]
  intro hn
  exact zero_zpow n hn

lemma zpow'_eq_zero_iff (a : α) (n : ℤ) : zpow' a n = 0 ↔ a = 0 := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [zpow']
  · simp [zpow', zpow_eq_zero_iff hn]
    tauto

@[simp]
lemma one_zpow' (n : ℤ) : zpow' (1 : α) n = 1 := by
  simp [zpow']

@[simp]
lemma zpow'_one (a : α) : zpow' a 1 = a := by
  simp [zpow']

lemma zpow'_zero_eq_div (a : α) : zpow' a 0 = a / a := by
  simp [zpow']
  by_cases h : a = 0
  · simp [h]
  · simp [h]

lemma zpow'_zero_of_ne_zero {a : α} (ha : a ≠ 0) : zpow' a 0 = 1 := by simp [zpow', ha]

lemma zpow'_neg (a : α) (n : ℤ) : zpow' a (-n) = (zpow' a n)⁻¹ := by
  simp +contextual [zpow', apply_ite]
  split_ifs with h
  · tauto
  · tauto

lemma zpow'_mul (a : α) (m n : ℤ) : zpow' a (m * n) = zpow' (zpow' a m) n := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hn : n = 0
  · rw [hn]
    simp [zpow', ha, zpow_ne_zero ]
  by_cases hm : m = 0
  · rw [hm]
    simp [zpow', ha]
  simpa [zpow', ha, hm, hn] using zpow_mul a m n

lemma zpow'_ofNat (a : α) {n : ℕ} (hn : n ≠ 0) : zpow' a n = a ^ n := by
  rw [zpow'_of_ne_zero_right]
  · simp
  exact_mod_cast hn

end

lemma mul_zpow' [CommGroupWithZero α] (n : ℤ) (a b : α) :
    zpow' (a * b) n = zpow' a n * zpow' b n := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  simpa [zpow', ha, hb] using mul_zpow a b n

theorem list_prod_zpow' [CommGroupWithZero α] {r : ℤ} {l : List α} :
    zpow' (prod l) r = prod (map (fun x ↦ zpow' x r) l) :=
  let fr : α →* α := ⟨⟨fun b ↦ zpow' b r, one_zpow' r⟩, (mul_zpow' r)⟩
  map_list_prod fr l

end zpow'

theorem subst_add {M : Type*} [Semiring M] {x₁ x₂ X₁ X₂ Y y a : M}
    (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ = Y) (hy : a * Y = y) :
    x₁ + x₂ = y := by
  subst h₁ h₂ H_atom hy
  simp [mul_add]

theorem subst_sub {M : Type*} [Ring M] {x₁ x₂ X₁ X₂ Y y a : M}
    (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) (hy : a * Y = y) :
    x₁ - x₂ = y := by
  subst h₁ h₂ H_atom hy
  simp [mul_sub]

theorem eq_div_of_eq_one_of_subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1)
    (hn : l_n = n) :
    l = n := by
  rw [h, hn, div_one]

theorem eq_div_of_eq_one_of_subst' {M : Type*} [DivInvOneMonoid M] {l l_d d : M} (h : l = 1 / l_d)
    (hn : l_d = d) :
    l = d⁻¹ := by
  rw [h, hn, one_div]

theorem eq_div_of_subst {M : Type*} [Div M] {l l_n l_d n d : M} (h : l = l_n / l_d) (hn : l_n = n)
    (hd : l_d = d) :
    l = n / d := by
  rw [h, hn, hd]

theorem eq_mul_of_eq_eq_eq_mul {M : Type*} [Mul M] {a b c D e f : M}
    (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e) (h₄ : e = f) :
    a = D * f := by
  rw [h₁, h₂, h₃, h₄]

theorem eq_eq_cancel_eq {M : Type*} [MonoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M}
    (H₁ : e₁ = L * f₁) (H₂ : e₂ = L * f₂) (HL : L ≠ 0) :
    (e₁ = e₂) = (f₁ = f₂) := by
  subst H₁ H₂
  rw [mul_right_inj' HL]

theorem le_eq_cancel_le {M : Type*} [MonoidWithZero M] [PartialOrder M] [PosMulMono M]
    [PosMulReflectLE M] {e₁ e₂ f₁ f₂ L : M}
    (H₁ : e₁ = L * f₁) (H₂ : e₂ = L * f₂) (HL : 0 < L) :
    (e₁ ≤ e₂) = (f₁ ≤ f₂) := by
  subst H₁ H₂
  apply Iff.eq
  exact mul_le_mul_iff_right₀ HL

theorem lt_eq_cancel_lt {M : Type*} [MonoidWithZero M] [PartialOrder M] [PosMulStrictMono M]
    [PosMulReflectLT M] {e₁ e₂ f₁ f₂ L : M}
    (H₁ : e₁ = L * f₁) (H₂ : e₂ = L * f₂) (HL : 0 < L) :
    (e₁ < e₂) = (f₁ < f₂) := by
  subst H₁ H₂
  apply Iff.eq
  exact mul_lt_mul_iff_of_pos_left HL

/-! ### Theory of lists of pairs (exponent, atom)

This section contains the lemmas which are orchestrated by the `field_simp` tactic
to prove goals in fields.  The basic object which these lemmas concern is `NF M`, a type synonym
for a list of ordered pairs in `ℤ × M`, where typically `M` is a field.
-/

/-- Basic theoretical "normal form" object of the `field_simp` tactic: a type
synonym for a list of ordered pairs in `ℤ × M`, where typically `M` is a field.  This is the
form to which the tactics reduce field expressions. -/
def NF (M : Type*) := List (ℤ × M)

namespace NF
variable {M : Type*}

/-- Augment a `FieldSimp.NF M` object `l`, i.e. a list of pairs in `ℤ × M`, by prepending another
pair `p : ℤ × M`. -/
@[match_pattern]
def cons (p : ℤ × M) (l : NF M) : NF M := p :: l

@[inherit_doc cons] infixl:100 " ::ᵣ " => cons

/-- Evaluate a `FieldSimp.NF M` object `l`, i.e. a list of pairs in `ℤ × M`, to an element of `M`,
by forming the "multiplicative linear combination" it specifies: raise each `M` term to the power of
the corresponding `ℤ` term, then multiply them all together. -/
noncomputable def eval [GroupWithZero M] (l : NF M) : M :=
  (l.map (fun (⟨r, x⟩ : ℤ × M) ↦ zpow' x r)).prod

@[simp] theorem eval_cons [CommGroupWithZero M] (p : ℤ × M) (l : NF M) :
    (p ::ᵣ l).eval = l.eval * zpow' p.2 p.1 := by
  unfold eval cons
  simp [mul_comm]

theorem cons_ne_zero [GroupWithZero M] (r : ℤ) {x : M} (hx : x ≠ 0) {l : NF M} (hl : l.eval ≠ 0) :
    ((r, x) ::ᵣ l).eval ≠ 0 := by
  unfold eval cons
  apply mul_ne_zero ?_ hl
  simp [zpow'_eq_zero_iff, hx]

theorem cons_pos [GroupWithZero M] [PartialOrder M] [PosMulStrictMono M] [PosMulReflectLT M]
    [ZeroLEOneClass M] (r : ℤ) {x : M} (hx : 0 < x) {l : NF M} (hl : 0 < l.eval) :
    0 < ((r, x) ::ᵣ l).eval := by
  unfold eval cons
  apply mul_pos ?_ hl
  simp only
  rw [zpow'_of_ne_zero_left _ _ hx.ne']
  apply zpow_pos hx

theorem atom_eq_eval [GroupWithZero M] (x : M) : x = NF.eval [(1, x)] := by simp [eval]

variable (M) in
theorem one_eq_eval [GroupWithZero M] : (1:M) = NF.eval (M := M) [] := (rfl)

theorem mul_eq_eval₁ [CommGroupWithZero M] (a₁ : ℤ × M) {a₂ : ℤ × M} {l₁ l₂ l : NF M}
    (h : l₁.eval * (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval * (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h]
  ac_rfl

theorem mul_eq_eval₂ [CommGroupWithZero M] (r₁ r₂ : ℤ) (x : M) {l₁ l₂ l : NF M}
    (h : l₁.eval * l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval * ((r₂, x) ::ᵣ l₂).eval = ((r₁ + r₂, x) ::ᵣ l).eval := by
  simp only [eval_cons, ← h, zpow'_add]
  ac_rfl

theorem mul_eq_eval₃ [CommGroupWithZero M] {a₁ : ℤ × M} (a₂ : ℤ × M) {l₁ l₂ l : NF M}
    (h : (a₁ ::ᵣ l₁).eval * l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval * (a₂ ::ᵣ l₂).eval = (a₂ ::ᵣ l).eval := by
  simp only [eval_cons, ← h]
  ac_rfl

theorem mul_eq_eval [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
    (hx₂ : x₂ = l₂.eval) (h : l₁.eval * l₂.eval = l.eval) :
    x₁ * x₂ = l.eval := by
  rw [hx₁, hx₂, h]

theorem div_eq_eval₁ [CommGroupWithZero M] (a₁ : ℤ × M) {a₂ : ℤ × M} {l₁ l₂ l : NF M}
    (h : l₁.eval / (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval / (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, div_eq_mul_inv]
  ac_rfl

theorem div_eq_eval₂ [CommGroupWithZero M] (r₁ r₂ : ℤ) (x : M) {l₁ l₂ l : NF M}
    (h : l₁.eval / l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval / ((r₂, x) ::ᵣ l₂).eval = ((r₁ - r₂, x) ::ᵣ l).eval := by
  simp only [← h, eval_cons, div_eq_mul_inv, mul_inv, ← zpow'_neg, sub_eq_add_neg, zpow'_add]
  ac_rfl

theorem div_eq_eval₃ [CommGroupWithZero M] {a₁ : ℤ × M} (a₂ : ℤ × M) {l₁ l₂ l : NF M}
    (h : (a₁ ::ᵣ l₁).eval / l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval / (a₂ ::ᵣ l₂).eval = ((-a₂.1, a₂.2) ::ᵣ l).eval := by
  simp only [eval_cons, ← h, zpow'_neg, div_eq_mul_inv, mul_inv, mul_assoc]

theorem div_eq_eval [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
    (hx₂ : x₂ = l₂.eval) (h : l₁.eval / l₂.eval = l.eval) :
    x₁ / x₂ = l.eval := by
  rw [hx₁, hx₂, h]

theorem eval_mul_eval_cons [CommGroupWithZero M] (n : ℤ) (e : M) {L l l' : NF M}
    (h : L.eval * l.eval = l'.eval) :
    L.eval * ((n, e) ::ᵣ l).eval = ((n, e) ::ᵣ l').eval := by
  rw [eval_cons, eval_cons, ← h, mul_assoc]

theorem eval_mul_eval_cons_zero [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M}
    (h : L.eval * l.eval = l'.eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval) :
    L.eval * l₀.eval = ((0, e) ::ᵣ l').eval := by
  rw [← eval_mul_eval_cons 0 e h, h']

theorem eval_cons_mul_eval [CommGroupWithZero M] (n : ℤ) (e : M) {L l l' : NF M}
    (h : L.eval * l.eval = l'.eval) :
    ((n, e) ::ᵣ L).eval * l.eval = ((n, e) ::ᵣ l').eval := by
  rw [eval_cons, eval_cons, ← h]
  ac_rfl

theorem eval_cons_mul_eval_cons_neg [CommGroupWithZero M] (n : ℤ) {e : M} (he : e ≠ 0)
    {L l l' : NF M} (h : L.eval * l.eval = l'.eval) :
    ((n, e) ::ᵣ L).eval * ((-n, e) ::ᵣ l).eval = l'.eval := by
  rw [mul_eq_eval₂ n (-n) e h]
  simp [zpow'_zero_of_ne_zero he]

theorem cons_eq_div_of_eq_div [CommGroupWithZero M] (n : ℤ) (e : M) {t t_n t_d : NF M}
    (h : t.eval = t_n.eval / t_d.eval) :
    ((n, e) ::ᵣ t).eval = ((n, e) ::ᵣ t_n).eval / t_d.eval := by
  simp only [eval_cons, h, div_eq_mul_inv]
  ac_rfl

theorem cons_eq_div_of_eq_div' [CommGroupWithZero M] (n : ℤ) (e : M) {t t_n t_d : NF M}
    (h : t.eval = t_n.eval / t_d.eval) :
    ((-n, e) ::ᵣ t).eval = t_n.eval / ((n, e) ::ᵣ t_d).eval := by
  simp only [eval_cons, h, zpow'_neg, div_eq_mul_inv, mul_inv]
  ac_rfl

theorem cons_zero_eq_div_of_eq_div [CommGroupWithZero M] (e : M) {t t_n t_d : NF M}
    (h : t.eval = t_n.eval / t_d.eval) :
    ((0, e) ::ᵣ t).eval = ((1, e) ::ᵣ t_n).eval / ((1, e) ::ᵣ t_d).eval := by
  simp only [eval_cons, h, div_eq_mul_inv, mul_inv, ← zpow'_neg, ← add_neg_cancel (1:ℤ), zpow'_add]
  ac_rfl

instance : Inv (NF M) where
  inv l := l.map fun (a, x) ↦ (-a, x)

theorem eval_inv [CommGroupWithZero M] (l : NF M) : (l⁻¹).eval = l.eval⁻¹ := by
  simp +instances only [NF.eval, List.map_map, NF.instInv, List.prod_inv]
  congr! 2
  ext p
  simp [zpow'_neg]

theorem one_div_eq_eval [CommGroupWithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval := by
  simp [eval_inv]

theorem inv_eq_eval [CommGroupWithZero M] {l : NF M} {x : M} (h : x = l.eval) :
    x⁻¹ = (l⁻¹).eval := by
  rw [h, eval_inv]

instance : Pow (NF M) ℤ where
  pow l r := l.map fun (a, x) ↦ (r * a, x)

@[simp] theorem zpow_apply (r : ℤ) (l : NF M) : l ^ r = l.map fun (a, x) ↦ (r * a, x) := rfl

theorem eval_zpow' [CommGroupWithZero M] (l : NF M) (r : ℤ) :
    (l ^ r).eval = zpow' l.eval r := by
  unfold NF.eval at ⊢
  simp only [zpow_apply, list_prod_zpow', map_map]
  congr! 2
  ext p
  simp [← zpow'_mul, mul_comm]

theorem zpow_eq_eval [CommGroupWithZero M] {l : NF M} {r : ℤ} (hr : r ≠ 0) {x : M}
    (hx : x = l.eval) :
    x ^ r = (l ^ r).eval := by
  rw [← zpow'_of_ne_zero_right x r hr, eval_zpow', hx]

instance : Pow (NF M) ℕ where
  pow l r := l.map fun (a, x) ↦ (r * a, x)

@[simp] theorem pow_apply (r : ℕ) (l : NF M) : l ^ r = l.map fun (a, x) ↦ (r * a, x) :=
  rfl

theorem eval_pow [CommGroupWithZero M] (l : NF M) (r : ℕ) : (l ^ r).eval = zpow' l.eval r :=
  eval_zpow' l r

theorem pow_eq_eval [CommGroupWithZero M] {l : NF M} {r : ℕ} (hr : r ≠ 0) {x : M}
    (hx : x = l.eval) :
    x ^ r = (l ^ r).eval := by
  rw [eval_pow, hx]
  rw [zpow'_ofNat _ hr]

theorem eval_cons_of_pow_eq_zero [CommGroupWithZero M] {r : ℤ} (hr : r = 0) {x : M} (hx : x ≠ 0)
    (l : NF M) :
    ((r, x) ::ᵣ l).eval = NF.eval l := by
  simp [hr, zpow'_zero_of_ne_zero hx]

theorem eval_cons_eq_eval_of_eq_of_eq [CommGroupWithZero M] (r : ℤ) (x : M) {t t' l' : NF M}
    (h : NF.eval t = NF.eval t') (h' : ((r, x) ::ᵣ t').eval = NF.eval l') :
    ((r, x) ::ᵣ t).eval = NF.eval l' := by
  rw [← h', eval_cons, eval_cons, h]

end NF
end

/-! ### Negations of algebraic operations -/

@[expose] public meta section Sign
open Lean Qq

variable {v : Level} {M : Q(Type v)}

/-- Inductive type representing the options for the sign of an element in a type-expression `M`

If the sign is "-", then we also carry an expression for a field instance on `M`, to allow us to
construct that negation when needed. -/
inductive Sign (M : Q(Type v))
  | plus
  | minus (iM : Q(Field $M))

/-- Given an expression `e : Q($M)`, construct an expression which is morally "± `e`", with the
choice between + and - determined by an object `g : Sign M`. -/
def Sign.expr : Sign M → Q($M) → Q($M)
  | plus, a => a
  | minus _, a => q(-$a)

/-- Given an expression `y : Q($M)` with specified sign (either + or -), construct a proof that
the product with `c` of (± `y`) (here taking the specified sign) is ± `c * y`. -/
def Sign.mulRight (iM : Q(CommGroupWithZero $M)) (c y : Q($M)) (g : Sign M) :
    MetaM Q($(g.expr q($c * $y)) = $c * $(g.expr y)) := do
  match g with
  | .plus => pure q(rfl)
  | .minus _ =>
    assumeInstancesCommute
    pure q(Eq.symm (mul_neg $c _))

/-- Given expressions `y₁ y₂ : Q($M)` with specified signs (either + or -), construct a proof that
the product of (± `y₁`) and (± `y₂`) (here taking the specified signs) is ± `y₁ * y₂`; return this
proof and the computed sign. -/
def Sign.mul (iM : Q(CommGroupWithZero $M)) (y₁ y₂ : Q($M)) (g₁ g₂ : Sign M) :
    MetaM (Σ (G : Sign M), Q($(g₁.expr y₁) * $(g₂.expr y₂) = $(G.expr q($y₁ * $y₂)))) := do
  match g₁, g₂ with
  | .plus, .plus => pure ⟨.plus, q(rfl)⟩
  | .plus, .minus i =>
    assumeInstancesCommute
    pure ⟨.minus i, q(mul_neg $y₁ $y₂)⟩
  | .minus i, .plus =>
    assumeInstancesCommute
    pure ⟨.minus i, q(neg_mul $y₁ $y₂)⟩
  | .minus _, .minus _ =>
    assumeInstancesCommute
    pure ⟨.plus, q(neg_mul_neg $y₁ $y₂)⟩

/-- Given an expression `y : Q($M)` with specified sign (either + or -), construct a proof that
the inverse of (± `y`) (here taking the specified sign) is ± `y⁻¹`. -/
def Sign.inv (iM : Q(CommGroupWithZero $M)) (y : Q($M)) (g : Sign M) :
    MetaM (Q($(g.expr y)⁻¹ = $(g.expr q($y⁻¹)))) := do
  match g with
  | .plus => pure q(rfl)
  | .minus _ =>
    assumeInstancesCommute
    pure q(inv_neg (a := $y))

/-- Given expressions `y₁ y₂ : Q($M)` with specified signs (either + or -), construct a proof that
the quotient of (± `y₁`) and (± `y₂`) (here taking the specified signs) is ± `y₁ / y₂`; return this
proof and the computed sign. -/
def Sign.div (iM : Q(CommGroupWithZero $M)) (y₁ y₂ : Q($M)) (g₁ g₂ : Sign M) :
    MetaM (Σ (G : Sign M), Q($(g₁.expr y₁) / $(g₂.expr y₂) = $(G.expr q($y₁ / $y₂)))) := do
  match g₁, g₂ with
  | .plus, .plus => pure ⟨.plus, q(rfl)⟩
  | .plus, .minus i =>
    assumeInstancesCommute
    pure ⟨.minus i, q(div_neg $y₁ (b := $y₂))⟩
  | .minus i, .plus =>
    assumeInstancesCommute
    pure ⟨.minus i, q(neg_div $y₂ $y₁)⟩
  | .minus _, .minus _ =>
    assumeInstancesCommute
    pure ⟨.plus, q(neg_div_neg_eq $y₁ $y₂)⟩

/-- Given an expression `y : Q($M)` with specified sign (either + or -), construct a proof that
the negation of (± `y`) (here taking the specified sign) is ∓ `y`. -/
def Sign.neg (iM : Q(Field $M)) (y : Q($M)) (g : Sign M) :
    MetaM (Σ (G : Sign M), Q(-$(g.expr y) = $(G.expr y))) := do
  match g with
  | .plus => pure ⟨.minus iM, q(rfl)⟩
  | .minus _ =>
    assumeInstancesCommute
    pure ⟨.plus, q(neg_neg $y)⟩

/-- Given an expression `y : Q($M)` with specified sign (either + or -), construct a proof that
the exponentiation to power `s : ℕ` of (± `y`) (here taking the specified signs) is ± `y ^ s`;
return this proof and the computed sign. -/
def Sign.pow (iM : Q(CommGroupWithZero $M)) (y : Q($M)) (g : Sign M) (s : ℕ) :
    MetaM (Σ (G : Sign M), Q($(g.expr y) ^ $s = $(G.expr q($y ^ $s)))) := do
  match g with
  | .plus => pure ⟨.plus, q(rfl)⟩
  | .minus i =>
    assumeInstancesCommute
    if 2 ∣ s then
      let pf_s ← mkDecideProofQ q(Even $s)
      pure ⟨.plus, q(Even.neg_pow $pf_s $y)⟩
    else
      let pf_s ← mkDecideProofQ q(Odd $s)
      pure ⟨.minus i, q(Odd.neg_pow $pf_s $y)⟩

/-- Given an expression `y : Q($M)` with specified sign (either + or -), construct a proof that
the exponentiation to power `s : ℤ` of (± `y`) (here taking the specified signs) is ± `y ^ s`;
return this proof and the computed sign. -/
def Sign.zpow (iM : Q(CommGroupWithZero $M)) (y : Q($M)) (g : Sign M) (s : ℤ) :
    MetaM (Σ (G : Sign M), Q($(g.expr y) ^ $s = $(G.expr q($y ^ $s)))) := do
  match g with
  | .plus => pure ⟨.plus, q(rfl)⟩
  | .minus i =>
    assumeInstancesCommute
    if 2 ∣ s then
      let pf_s ← mkDecideProofQ q(Even $s)
      pure ⟨.plus, q(Even.neg_zpow $pf_s $y)⟩
    else
      let pf_s ← mkDecideProofQ q(Odd $s)
      pure ⟨.minus i, q(Odd.neg_zpow $pf_s $y)⟩

/-- Given a proof that two expressions `y₁ y₂ : Q($M)` are equal, construct a proof that (± `y₁`)
and (± `y₂`) are equal, where the same sign is taken in both expression. -/
def Sign.congr {y y' : Q($M)} (g : Sign M) (pf : Q($y = $y')) : Q($(g.expr y)= $(g.expr y')) :=
  match g with
  | .plus => pf
  | .minus _ => q(congr_arg Neg.neg $pf)

/-- If `a` = ± `b`, `b = C * d`, and `d = e`, construct a proof that `a` = `C` * ± `e`. -/
def Sign.mkEqMul (iM : Q(CommGroupWithZero $M)) {a b C d e : Q($M)} {g : Sign M}
      (pf₁ : Q($a = $(g.expr b))) (pf₂ : Q($b = $C * $d))
      (pf₃ : Q($d = $e)) : MetaM Q($a = $C * $(g.expr e)) := do
    let pf₂' : Q($(g.expr b) = $(g.expr q($C * $d))) := g.congr pf₂
    let pf' ← Sign.mulRight iM C d g
    pure q(eq_mul_of_eq_eq_eq_mul $pf₁ $pf₂' $pf' $(g.congr pf₃))

end Sign

end Mathlib.Tactic.FieldSimp
