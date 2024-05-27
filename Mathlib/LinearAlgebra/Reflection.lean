/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury, Mitchell Lee
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.FiniteSpan
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Reflections in linear algebra

Given an element `x` in a module `M` together with a linear form `f` on `M` such that `f x = 2`, the
map `y ↦ y - (f y) • x` is an involutive endomorphism of `M`, such that:
 1. the kernel of `f` is fixed,
 2. the point `x ↦ -x`.

Such endomorphisms are often called reflections of the module `M`. When `M` carries an inner product
for which `x` is perpendicular to the kernel of `f`, then (with mild assumptions) the endomorphism
is characterised by properties 1 and 2 above, and is a linear isometry.

## Main definitions / results:

 * `Module.preReflection`: the definition of the map `y ↦ y - (f y) • x`. Its main utility lies in
   the fact that it does not require the assumption `f x = 2`, giving the user freedom to defer
   discharging this proof obligation.
 * `Module.reflection`: the definition of the map `y ↦ y - (f y) • x`. This requires the assumption
   that `f x = 2` but by way of compensation it produces a linear equivalence rather than a mere
   linear map.
 * `Module.reflection_mul_reflection_pow_apply`: a formula for $(r_1 r_2)^m z$, where $r_1$ and
   $r_2$ are reflections and $z \in M$. It involves the Chebyshev polynomials and holds over any
   commutative ring. This is used to define reflection representations of Coxeter groups.
 * `Module.Dual.eq_of_preReflection_mapsTo`: a uniqueness result about reflections preserving
   finite spanning sets that is useful in the theory of root data / systems.

## TODO

Related definitions of reflection exists elsewhere in the library. These more specialised
definitions, which require an ambient `InnerProductSpace` structure, are `reflection` (of type
`LinearIsometryEquiv`) and `EuclideanGeometry.reflection` (of type `AffineIsometryEquiv`). We
should connect (or unify) these definitions with `Module.reflecton` defined here.

-/

open Set Function Pointwise
open Module hiding Finite
open Submodule (span)

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (x : M) (f : Dual R M) (y : M)

namespace Module

/-- Given an element `x` in a module `M` and a linear form `f` on `M`, we define the endomorphism
of `M` for which `y ↦ y - (f y) • x`.

One is typically interested in this endomorphism when `f x = 2`; this definition exists to allow the
user defer discharging this proof obligation. See also `Module.reflection`. -/
def preReflection : End R M :=
  LinearMap.id - f.smulRight x

lemma preReflection_apply :
    preReflection x f y = y - (f y) • x := by
  simp [preReflection]

variable {x f}

lemma preReflection_apply_self (h : f x = 2) :
    preReflection x f x = - x := by
  rw [preReflection_apply, h, two_smul]; abel

lemma involutive_preReflection (h : f x = 2) :
    Involutive (preReflection x f) :=
  fun y ↦ by simp [h, smul_sub, two_smul, preReflection_apply]

lemma preReflection_preReflection (g : Dual R M) (h : f x = 2) :
    preReflection (preReflection x f y) (preReflection f (Dual.eval R M x) g) =
    (preReflection x f) ∘ₗ (preReflection y g) ∘ₗ (preReflection x f) := by
  ext m
  simp only [h, preReflection_apply, mul_comm (g x) (f m), mul_two, mul_assoc, Dual.eval_apply,
    LinearMap.sub_apply, LinearMap.coe_comp, LinearMap.smul_apply, smul_eq_mul, smul_sub, sub_smul,
    smul_smul, sub_mul, comp_apply, map_sub, map_smul, add_smul]
  abel

/-- Given an element `x` in a module `M` and a linear form `f` on `M` for which `f x = 2`, we define
the endomorphism of `M` for which `y ↦ y - (f y) • x`.

It is an involutive endomorphism of `M` fixing the kernel of `f` for which `x ↦ -x`. -/
def reflection (h : f x = 2) : M ≃ₗ[R] M :=
  { preReflection x f, (involutive_preReflection h).toPerm with }

lemma reflection_apply (h : f x = 2) :
    reflection h y = y - (f y) • x :=
  preReflection_apply x f y

@[simp]
lemma reflection_apply_self (h : f x = 2) :
    reflection h x = - x :=
  preReflection_apply_self h

lemma involutive_reflection (h : f x = 2) :
    Involutive (reflection h) :=
  involutive_preReflection h

@[simp]
lemma reflection_inv (h : f x = 2) : (reflection h)⁻¹ = reflection h := rfl

@[simp]
lemma reflection_symm (h : f x = 2) :
    (reflection h).symm = reflection h :=
  rfl

/-! ### Powers of the product of two reflections

Let $M$ be a module over a commutative ring $R$. Let $x, y \in M$ and $f, g \in M^*$ with
$f(x) = g(y) = 2$. The corresponding reflections $r_1, r_2 \colon M \to M$ (`Module.reflection`) are
given by $r_1z = z - f(z) x$ and $r_2 z = z - g(z) y$. These are linear automorphisms of $M$.

To define reflection representations of a Coxeter group, it is important to be able to compute the
order of the composition $r_1 r_2$.

Note that if $M$ is a real inner product space and $r_1$ and $r_2$ are both orthogonal
reflections (i.e. $f(z) = 2 \langle x, z \rangle / \langle x, x \rangle$ and
$g(z) = 2 \langle y, z\rangle / \langle y, y\rangle$ for all $z \in M$),
then $r_1 r_2$ is a rotation by the angle
$$\cos^{-1}\left(\frac{f(y) g(x) - 2}{2}\right)$$
and one may determine the order of $r_1 r_2$ accordingly.

However, if $M$ does not have an inner product, and even if $R$ is not $\mathbb{R}$, then we may
instead use the formulas in this section. These formulas all involve evaluating Chebyshev
$S$-polynomials (`Polynomial.Chebyshev.S`) at $t = f(y) g(x) - 2$, and they hold over any
commutative ring. -/
section

open Int Polynomial.Chebyshev

variable {x y : M} {f g : Dual R M} (hf : f x = 2) (hg : g y = 2) (z : M)

local notation:max "t" => f y * g x - 2
local notation:max "S_eval_t" n:max => Polynomial.eval t (S R n)

set_option maxHeartbeats 400000 in
/-- A formula for $(r_1 r_2)^m z$, where $m$ is a natural number and $z \in M$. -/
lemma reflection_mul_reflection_pow_apply (m : ℕ) (z : M) :
    ((reflection hf * reflection hg) ^ m) z =
      z +
        (S_eval_t ((m - 2) / 2) * (S_eval_t ((m - 1) / 2) + S_eval_t ((m - 3) / 2))) •
          ((g x * f z - g z) • y - f z • x) +
        (S_eval_t ((m - 1) / 2) * (S_eval_t (m / 2) + S_eval_t ((m - 2) / 2))) •
          ((f y * g z - f z) • x - g z • y) := by
  induction m with
  | zero => simp
  | succ m ih =>
    /- Now, let us collect two facts about the sequence `S_eval_t`. These easily follow from the
    properties of the `S` polynomials. -/
    have S_eval_t_sub_two (k : ℤ) : S_eval_t (k - 2) = t * S_eval_t (k - 1) - S_eval_t k := by
      simp [S_sub_two]
    have S_eval_t_sq_add_S_eval_t_sq (k : ℤ) :
        S_eval_t k ^ 2 + S_eval_t (k + 1) ^ 2 - t * S_eval_t k * S_eval_t (k + 1) = 1 := by
      simpa using congr_arg (Polynomial.eval t) (S_sq_add_S_sq R k)
    -- Apply the inductive hypothesis.
    rw [pow_succ', LinearEquiv.mul_apply, ih, LinearEquiv.mul_apply]
    /- TODO: Write a tactic that puts module-valued expressions in a normal form. Such a tactic
    would perform most of the next three steps automatically. -/
    -- Expand everything out and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, smul_add, smul_sub, smul_neg,
      smul_smul, add_smul, sub_smul, sub_eq_add_neg, ← neg_smul, ← add_assoc, hf, hg]
    -- Sort the terms so that the multiples of `x` appear first, then `y`, then `z`.
    simp only [add_comm z (_ • x), add_right_comm _ z (_ • x),
      add_comm (_ • y) (_ • x), add_right_comm _ (_ • y) (_ • x),
      add_comm z (_ • y), add_right_comm _ z (_ • y)]
    -- Combine like terms.
    simp only [← add_smul, add_assoc _ (_ • y) (_ • y)]
    -- `m` can either be written in the form `2 * k` or `2 * k + 1`.
    obtain ⟨k, even | odd⟩ := Int.even_or_odd' m
    · /- The goal contains many expressions of the form `S_eval_t n`. We may rewrite all of them as
      `S_eval_t (-2 + k)`, `S_eval_t (-1 + k)`, or `S_eval_t k`. -/
      push_cast
      simp_rw [even, add_assoc (2 * k), add_comm (2 * k),
        add_mul_ediv_left _ k (by norm_num : (2 : ℤ) ≠ 0)]
      norm_num
      /- Now, equate the coefficients of `x` and `y` on both sides. These linear combinations were
      found using `polyrith`. -/
      congr 2
      · linear_combination (norm := ring_nf) (-g z * f y * S_eval_t (-1 + k) +
            f z * S_eval_t (-1 + k)) * S_eval_t_sub_two k +
          (-g z * f y + f z) * S_eval_t_sq_add_S_eval_t_sq (k - 1)
      · linear_combination (norm := ring_nf) g z * S_eval_t (-1 + k) * S_eval_t_sub_two k +
          g z * S_eval_t_sq_add_S_eval_t_sq (k - 1)
    · /- The goal contains many expressions of the form `S_eval_t n`. We may rewrite all of them as
      `S_eval_t (-1 + k)`, `S_eval_t k`, or `S_eval_t (1 + k)`. -/
      push_cast
      simp_rw [odd, add_assoc (2 * k), add_comm (2 * k),
        add_mul_ediv_left _ k (by norm_num : (2 : ℤ) ≠ 0)]
      norm_num
      /- Now, equate the coefficients of `x` and `y` on both sides. These linear combinations were
      found using `polyrith`. -/
      congr 2
      · linear_combination (norm := ring_nf) (-g z * f y * S_eval_t k +
            f z * S_eval_t k) * S_eval_t_sub_two (k + 1) +
          (-g z * f y + f z) * S_eval_t_sq_add_S_eval_t_sq (k - 1)
      · linear_combination (norm := ring_nf) g z * S_eval_t k * S_eval_t_sub_two (k + 1) +
          g z * S_eval_t_sq_add_S_eval_t_sq (k - 1)

/-- A formula for $(r_1 r_2)^m z$, where $m$ is an integer and $z \in M$. -/
lemma reflection_mul_reflection_zpow_apply (m : ℤ) (z : M) :
    ((reflection hf * reflection hg) ^ m) z =
      z +
        (S_eval_t ((m - 2) / 2) * (S_eval_t ((m - 1) / 2) + S_eval_t ((m - 3) / 2))) •
          ((g x * f z - g z) • y - f z • x) +
        (S_eval_t ((m - 1) / 2) * (S_eval_t (m / 2) + S_eval_t ((m - 2) / 2))) •
          ((f y * g z - f z) • x - g z • y) := by
  induction m using Int.negInduction with
  | nat m => exact_mod_cast reflection_mul_reflection_pow_apply hf hg m z
  | neg m _ =>
    rw [zpow_neg, ← inv_zpow, mul_inv_rev, reflection_inv, reflection_inv, zpow_natCast]
    simp only [reflection_mul_reflection_pow_apply]
    rw [add_right_comm z]
    have aux {a b : ℤ} (hab : a + b = -3) : a / 2 = -(b / 2) - 2 := by
      rw [← mul_right_inj' (by norm_num : (2 : ℤ) ≠ 0), mul_sub, mul_neg,
        eq_sub_of_add_eq (Int.ediv_add_emod _ _), eq_sub_of_add_eq (Int.ediv_add_emod _ _)]
      omega
    rw [aux (by omega : (-m - 3) + m = (-3 : ℤ)),
      aux (by omega : (-m - 2) + (m - 1) = (-3 : ℤ)),
      aux (by omega : (-m - 1) + (m - 2) = (-3 : ℤ)),
      aux (by omega : -m + (m - 3) = (-3 : ℤ))]
    simp only [S_neg_sub_two, Polynomial.eval_neg]
    ring_nf

/-- A formula for $(r_1 r_2)^m x$, where $m$ is an integer. This is the special case of
`Module.reflection_mul_reflection_zpow_apply` with $z = x$. -/
lemma reflection_mul_reflection_zpow_apply_self (m : ℤ) :
    ((reflection hf * reflection hg) ^ m) x =
      (S_eval_t m + S_eval_t (m - 1)) • x + (S_eval_t (m - 1) * -g x) • y := by
  /- Even though this is a special case of `Module.reflection_mul_reflection_zpow_apply`, it is
  easier to prove it from scratch. -/
  have S_eval_t_sub_two (k : ℤ) : S_eval_t (k - 2) = t * S_eval_t (k - 1) - S_eval_t k := by
    simp [S_sub_two]
  induction m using Int.induction_on with
  | hz => simp
  | hp m ih =>
    -- Apply the inductive hypothesis.
    rw [add_comm (m : ℤ) 1, zpow_one_add, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih]
    -- Expand everything out and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, smul_add, smul_sub, smul_neg,
      smul_smul, add_smul, sub_smul, sub_eq_add_neg, ← neg_smul, ← add_assoc, hf, hg]
    -- Sort the terms so that the multiples of `x` appear first, then `y`.
    simp only [add_comm (_ • y) (_ • x), add_right_comm _ (_ • y) (_ • x)]
    -- Combine like terms.
    simp only [← add_smul, add_assoc _ (_ • y) (_ • y)]
    -- Equate coefficients of `x` and `y`.
    congr 2
    · linear_combination (norm := ring_nf) -S_eval_t_sub_two (m + 1)
    · ring_nf
  | hn m ih =>
    -- Apply the inductive hypothesis.
    rw [sub_eq_add_neg (-m : ℤ) 1, add_comm (-m : ℤ) (-1), zpow_add, zpow_neg_one, mul_inv_rev,
      reflection_inv, reflection_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih]
    -- Expand everything out and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, smul_add, smul_sub, smul_neg,
      smul_smul, add_smul, sub_smul, sub_eq_add_neg, ← neg_smul, ← add_assoc, hf, hg]
    -- Sort the terms so that the multiples of `x` appear first, then `y`.
    simp only [add_comm (_ • y) (_ • x), add_right_comm _ (_ • y) (_ • x)]
    -- Combine like terms.
    simp only [← add_smul, add_assoc _ (_ • y) (_ • y)]
    -- Equate coefficients of `x` and `y`.
    congr 2
    · linear_combination (norm := ring_nf) -S_eval_t_sub_two (-m)
    · linear_combination (norm := ring_nf) g x * S_eval_t_sub_two (-m)

/-- A formula for $(r_1 r_2)^m x$, where $m$ is a natural number. This is the special case of
`Module.reflection_mul_reflection_pow_apply` with $z = x$. -/
lemma reflection_mul_reflection_pow_apply_self (m : ℕ) :
    ((reflection hf * reflection hg) ^ m) x =
      (S_eval_t m + S_eval_t (m - 1)) • x + (S_eval_t (m - 1) * -g x) • y :=
  mod_cast reflection_mul_reflection_zpow_apply_self hf hg m

/-- A formula for $r_2 (r_1 r_2)^m x$, where $m$ is an integer. -/
lemma reflection_mul_reflection_mul_reflection_zpow_apply_self (m : ℤ) :
    (reflection hg * (reflection hf * reflection hg) ^ m) x =
      (S_eval_t m + S_eval_t (m - 1)) • x + (S_eval_t m * -g x) • y := by
  rw [LinearEquiv.mul_apply, reflection_mul_reflection_zpow_apply_self]
  -- Expand everything out and use `hf`, `hg`.
  simp only [reflection_apply, map_add, map_sub, map_smul, smul_add, smul_sub, smul_neg,
    smul_smul, add_smul, sub_smul, sub_eq_add_neg, ← neg_smul, ← add_assoc, hf, hg]
  -- Sort the terms so that the multiples of `x` appear first, then `y`.
  simp only [add_comm (_ • y) (_ • x), add_right_comm _ (_ • y) (_ • x)]
  -- Combine like terms.
  simp only [← add_smul, add_assoc _ (_ • y) (_ • y)]
  -- Equate coefficients of `x` and `y`.
  ring_nf

/-- A formula for $r_2 (r_1 r_2)^m x$, where $m$ is a natural number. -/
lemma reflection_mul_reflection_mul_reflection_pow_apply_self (m : ℕ) :
    (reflection hg * (reflection hf * reflection hg) ^ m) x =
      (S_eval_t m + S_eval_t (m - 1)) • x + (S_eval_t m * -g x) • y :=
  mod_cast reflection_mul_reflection_mul_reflection_zpow_apply_self hf hg m

end

/-! ### Lemmas used to prove uniqueness results for root data -/

/-- See also `Module.Dual.eq_of_preReflection_mapsTo'` for a variant of this lemma which
applies when `Φ` does not span.

This rather technical-looking lemma exists because it is exactly what is needed to establish various
uniqueness results for root data / systems. One might regard this lemma as lying at the boundary of
linear algebra and combinatorics since the finiteness assumption is the key. -/
lemma Dual.eq_of_preReflection_mapsTo [CharZero R] [NoZeroSMulDivisors R M]
    {x : M} (hx : x ≠ 0) {Φ : Set M} (hΦ₁ : Φ.Finite) (hΦ₂ : span R Φ = ⊤) {f g : Dual R M}
    (hf₁ : f x = 2) (hf₂ : MapsTo (preReflection x f) Φ Φ)
    (hg₁ : g x = 2) (hg₂ : MapsTo (preReflection x g) Φ Φ) :
    f = g := by
  let u := reflection hg₁ * reflection hf₁
  have hu : u = LinearMap.id (R := R) (M := M) + (f - g).smulRight x := by
    ext y
    simp only [u, reflection_apply, hg₁, two_smul, LinearEquiv.coe_toLinearMap_mul,
      LinearMap.id_coe, LinearEquiv.coe_coe, LinearMap.mul_apply, LinearMap.add_apply, id_eq,
      LinearMap.coe_smulRight, LinearMap.sub_apply, map_sub, map_smul, sub_add_cancel_left,
      smul_neg, sub_neg_eq_add, sub_smul]
    abel
  replace hu : ∀ (n : ℕ),
      ↑(u ^ n) = LinearMap.id (R := R) (M := M) + (n : R) • (f - g).smulRight x := by
    intros n
    induction n with
    | zero => simp
    | succ n ih =>
      have : ((f - g).smulRight x).comp ((n : R) • (f - g).smulRight x) = 0 := by
        ext; simp [hf₁, hg₁]
      rw [pow_succ', LinearEquiv.coe_toLinearMap_mul, ih, hu, add_mul, mul_add, mul_add]
      simp_rw [LinearMap.mul_eq_comp, LinearMap.comp_id, LinearMap.id_comp, this, add_zero,
        add_assoc, Nat.cast_succ, add_smul, one_smul]
  suffices IsOfFinOrder u by
    obtain ⟨n, hn₀, hn₁⟩ := isOfFinOrder_iff_pow_eq_one.mp this
    replace hn₁ : (↑(u ^ n) : M →ₗ[R] M) = LinearMap.id := LinearEquiv.toLinearMap_inj.mpr hn₁
    simpa [hn₁, hn₀.ne', hx, sub_eq_zero] using hu n
  exact u.isOfFinOrder_of_finite_of_span_eq_top_of_mapsTo hΦ₁ hΦ₂ (hg₂.comp hf₂)

/-- This rather technical-looking lemma exists because it is exactly what is needed to establish a
uniqueness result for root data. See the doc string of `Module.Dual.eq_of_preReflection_mapsTo` for
further remarks. -/
lemma Dual.eq_of_preReflection_mapsTo' [CharZero R] [NoZeroSMulDivisors R M]
    {x : M} (hx : x ≠ 0) {Φ : Set M} (hΦ₁ : Φ.Finite) (hx' : x ∈ span R Φ) {f g : Dual R M}
    (hf₁ : f x = 2) (hf₂ : MapsTo (preReflection x f) Φ Φ)
    (hg₁ : g x = 2) (hg₂ : MapsTo (preReflection x g) Φ Φ) :
    (span R Φ).subtype.dualMap f = (span R Φ).subtype.dualMap g := by
  set Φ' : Set (span R Φ) := range (inclusion <| Submodule.subset_span (R := R) (s := Φ))
  rw [← finite_coe_iff] at hΦ₁
  have hΦ'₁ : Φ'.Finite := finite_range (inclusion Submodule.subset_span)
  have hΦ'₂ : span R Φ' = ⊤ := by simp [Φ']
  let x' : span R Φ := ⟨x, hx'⟩
  have hx' : x' ≠ 0 := Subtype.coe_ne_coe.1 hx
  have this : ∀ {F : Dual R M}, MapsTo (preReflection x F) Φ Φ →
      MapsTo (preReflection x' ((span R Φ).subtype.dualMap F)) Φ' Φ' := by
    intro F hF ⟨y, hy⟩ hy'
    simp only [Φ', range_inclusion, SetLike.coe_sort_coe, mem_setOf_eq] at hy' ⊢
    exact hF hy'
  exact eq_of_preReflection_mapsTo hx' hΦ'₁ hΦ'₂ hf₁ (this hf₂) hg₁ (this hg₂)

end Module
