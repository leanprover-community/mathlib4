/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury, Mitchell Lee, Johan Commelin
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.Algebra.Module.Torsion
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dual.Defs
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
should connect (or unify) these definitions with `Module.reflection` defined here.

-/

open Function Set
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
  fun y ↦ by simp [map_sub, h, two_smul, preReflection_apply]

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

lemma invOn_reflection_of_mapsTo {Φ : Set M} (h : f x = 2) :
    InvOn (reflection h) (reflection h) Φ Φ :=
  ⟨fun x _ ↦ involutive_reflection h x, fun x _ ↦ involutive_reflection h x⟩

lemma bijOn_reflection_of_mapsTo {Φ : Set M} (h : f x = 2) (h' : MapsTo (reflection h) Φ Φ) :
    BijOn (reflection h) Φ Φ :=
  (invOn_reflection_of_mapsTo h).bijOn h' h'

lemma _root_.Submodule.mem_invtSubmodule_reflection_of_mem (h : f x = 2)
    (p : Submodule R M) (hx : x ∈ p) :
    p ∈ End.invtSubmodule (reflection h) := by
  suffices ∀ y ∈ p, reflection h y ∈ p from
    (End.mem_invtSubmodule _).mpr fun y hy ↦ by simpa using this y hy
  intro y hy
  simpa only [reflection_apply, p.sub_mem_iff_right hy] using p.smul_mem (f y) hx

lemma _root_.Submodule.mem_invtSubmodule_reflection_iff [NeZero (2 : R)] [NoZeroSMulDivisors R M]
    (h : f x = 2) {p : Submodule R M} (hp : Disjoint p (R ∙ x)) :
    p ∈ End.invtSubmodule (reflection h) ↔ p ≤ LinearMap.ker f := by
  refine ⟨fun h' y hy ↦ ?_, fun h' y hy ↦ ?_⟩
  · have hx : x ≠ 0 := by rintro rfl; exact two_ne_zero (α := R) <| by simp [← h]
    suffices f y • x ∈ p by
      have aux : f y • x ∈ p ⊓ (R ∙ x) := ⟨this, Submodule.mem_span_singleton.mpr ⟨f y, rfl⟩⟩
      rw [hp.eq_bot, Submodule.mem_bot, smul_eq_zero] at aux
      exact aux.resolve_right hx
    specialize h' hy
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe, reflection_apply] at h'
    simpa using p.sub_mem h' hy
  · have hy' : f y = 0 := by simpa using h' hy
    simpa [reflection_apply, hy']

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

variable {x y : M} {f g : Dual R M} (hf : f x = 2) (hg : g y = 2)

/-- A formula for $(r_1 r_2)^m z$, where $m$ is a natural number and $z \in M$. -/
lemma reflection_mul_reflection_pow_apply (m : ℕ) (z : M)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m) z =
      z +
        ((S R ((m - 2) / 2)).eval t * ((S R ((m - 1) / 2)).eval t + (S R ((m - 3) / 2)).eval t)) •
          ((g x * f z - g z) • y - f z • x) +
        ((S R ((m - 1) / 2)).eval t * ((S R (m / 2)).eval t + (S R ((m - 2) / 2)).eval t)) •
          ((f y * g z - f z) • x - g z • y) := by
  induction m with
  | zero => simp
  | succ m ih =>
    /- Now, let us collect two facts about the evaluations of `S r k`. These easily follow from the
    properties of the `S` polynomials. -/
    have S_eval_t_sub_two (k : ℤ) :
        (S R (k - 2)).eval t = t * (S R (k - 1)).eval t - (S R k).eval t := by
      simp [S_sub_two]
    have S_eval_t_sq_add_S_eval_t_sq (k : ℤ) :
        (S R k).eval t ^ 2 + (S R (k + 1)).eval t ^ 2 - t * (S R k).eval t * (S R (k + 1)).eval t
        = 1 := by
      simpa using congr_arg (Polynomial.eval t) (S_sq_add_S_sq R k)
    -- Apply the inductive hypothesis.
    rw [pow_succ', LinearEquiv.mul_apply, ih, LinearEquiv.mul_apply]
    -- Expand out all the reflections and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, hf, hg]
    -- `m` can be written in the form `2 * k + e`, where `e` is `0` or `1`.
    push_cast
    rw [← Int.mul_ediv_add_emod m 2]
    set k : ℤ := m / 2
    set e : ℤ := m % 2
    simp_rw [add_assoc (2 * k), add_sub_assoc (2 * k), add_comm (2 * k),
      add_mul_ediv_left _ k (by simp : (2 : ℤ) ≠ 0)]
    have he : e = 0 ∨ e = 1 := by omega
    clear_value e
    /- Now, equate the coefficients on both sides. These linear combinations were
    found using `polyrith`. -/
    match_scalars
    · rfl
    · linear_combination (norm := skip) (-g z * f y * (S R (e - 1 + k)).eval t +
          f z * (S R (e - 1 + k)).eval t) * S_eval_t_sub_two (e + k) +
          (-g z * f y + f z) * S_eval_t_sq_add_S_eval_t_sq (k - 1)
      subst ht
      obtain rfl | rfl : e = 0 ∨ e = 1 := he <;> ring_nf
    · linear_combination (norm := skip)
          g z * (S R (e - 1 + k)).eval t * S_eval_t_sub_two (e + k) +
          g z * S_eval_t_sq_add_S_eval_t_sq (k - 1)
      subst ht
      obtain rfl | rfl : e = 0 ∨ e = 1 := he <;> ring_nf

/-- A formula for $(r_1 r_2)^m$, where $m$ is a natural number. -/
lemma reflection_mul_reflection_pow (m : ℕ)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m).toLinearMap =
      LinearMap.id (R := R) (M := M) +
        ((S R ((m - 2) / 2)).eval t * ((S R ((m - 1) / 2)).eval t + (S R ((m - 3) / 2)).eval t)) •
          ((g x • f - g).smulRight y - f.smulRight x) +
        ((S R ((m - 1) / 2)).eval t * ((S R (m / 2)).eval t + (S R ((m - 2) / 2)).eval t)) •
          ((f y • g - f).smulRight x - g.smulRight y) := by
  ext z
  simpa using reflection_mul_reflection_pow_apply hf hg m z t ht

/-- A formula for $(r_1 r_2)^m z$, where $m$ is an integer and $z \in M$. -/
lemma reflection_mul_reflection_zpow_apply (m : ℤ) (z : M)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m) z =
      z +
        ((S R ((m - 2) / 2)).eval t * ((S R ((m - 1) / 2)).eval t + (S R ((m - 3) / 2)).eval t)) •
          ((g x * f z - g z) • y - f z • x) +
        ((S R ((m - 1) / 2)).eval t * ((S R (m / 2)).eval t + (S R ((m - 2) / 2)).eval t)) •
          ((f y * g z - f z) • x - g z • y) := by
  induction m using Int.negInduction with
  | nat m => exact_mod_cast reflection_mul_reflection_pow_apply hf hg m z t ht
  | neg _ m =>
    have ht' : t = g x * f y - 2 := by rwa [mul_comm (g x)]
    rw [zpow_neg, ← inv_zpow, mul_inv_rev, reflection_inv, reflection_inv, zpow_natCast,
      reflection_mul_reflection_pow_apply hg hf m z t ht', add_right_comm z]
    have aux (a b : ℤ) (hab : a + b = -3 := by omega) : a / 2 = -(b / 2) - 2 := by omega
    rw [aux (-m - 3) m, aux (-m - 2) (m - 1), aux (-m - 1) (m - 2), aux (-m) (m - 3)]
    simp only [S_neg_sub_two, Polynomial.eval_neg]
    ring_nf

/-- A formula for $(r_1 r_2)^m$, where $m$ is an integer. -/
lemma reflection_mul_reflection_zpow (m : ℤ)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m).toLinearMap =
      LinearMap.id (R := R) (M := M) +
        ((S R ((m - 2) / 2)).eval t * ((S R ((m - 1) / 2)).eval t + (S R ((m - 3) / 2)).eval t)) •
          ((g x • f - g).smulRight y - f.smulRight x) +
        ((S R ((m - 1) / 2)).eval t * ((S R (m / 2)).eval t + (S R ((m - 2) / 2)).eval t)) •
          ((f y • g - f).smulRight x - g.smulRight y) := by
  ext z
  simpa using reflection_mul_reflection_zpow_apply hf hg m z t ht

/-- A formula for $(r_1 r_2)^m x$, where $m$ is an integer. This is the special case of
`Module.reflection_mul_reflection_zpow_apply` with $z = x$. -/
lemma reflection_mul_reflection_zpow_apply_self (m : ℤ)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m) x =
      ((S R m).eval t + (S R (m - 1)).eval t) • x + ((S R (m - 1)).eval t * -g x) • y := by
  /- Even though this is a special case of `Module.reflection_mul_reflection_zpow_apply`, it is
  easier to prove it from scratch. -/
  have S_eval_t_sub_two (k : ℤ) :
      (S R (k - 2)).eval t = (f y * g x - 2) * (S R (k - 1)).eval t - (S R k).eval t := by
    simp [S_sub_two, ht]
  induction m with
  | zero => simp
  | succ m ih =>
    -- Apply the inductive hypothesis.
    rw [add_comm (m : ℤ) 1, zpow_one_add, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih]
    -- Expand out all the reflections and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, hf, hg]
    -- Equate coefficients of `x` and `y`.
    match_scalars
    · linear_combination (norm := ring_nf) -S_eval_t_sub_two (m + 1)
    · ring_nf
  | pred m ih =>
    -- Apply the inductive hypothesis.
    rw [sub_eq_add_neg (-m : ℤ) 1, add_comm (-m : ℤ) (-1), zpow_add, zpow_neg_one, mul_inv_rev,
      reflection_inv, reflection_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih]
    -- Expand out all the reflections and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, hf, hg]
    -- Equate coefficients of `x` and `y`.
    match_scalars
    · linear_combination (norm := ring_nf) -S_eval_t_sub_two (-m)
    · linear_combination (norm := ring_nf) g x * S_eval_t_sub_two (-m)

/-- A formula for $(r_1 r_2)^m x$, where $m$ is a natural number. This is the special case of
`Module.reflection_mul_reflection_pow_apply` with $z = x$. -/
lemma reflection_mul_reflection_pow_apply_self (m : ℕ)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m) x =
      ((S R m).eval t + (S R (m - 1)).eval t) • x + ((S R (m - 1)).eval t * -g x) • y :=
  mod_cast reflection_mul_reflection_zpow_apply_self hf hg m t ht

/-- A formula for $r_2 (r_1 r_2)^m x$, where $m$ is an integer. -/
lemma reflection_mul_reflection_mul_reflection_zpow_apply_self (m : ℤ)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    (reflection hg * (reflection hf * reflection hg) ^ m) x =
      ((S R m).eval t + (S R (m - 1)).eval t) • x + ((S R m).eval t * -g x) • y := by
  rw [LinearEquiv.mul_apply, reflection_mul_reflection_zpow_apply_self hf hg m t ht]
  -- Expand out all the reflections and use `hf`, `hg`.
  simp only [reflection_apply, map_add, map_smul, hg]
  -- Equate coefficients of `x` and `y`.
  module

/-- A formula for $r_2 (r_1 r_2)^m x$, where $m$ is a natural number. -/
lemma reflection_mul_reflection_mul_reflection_pow_apply_self (m : ℕ)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    (reflection hg * (reflection hf * reflection hg) ^ m) x =
      ((S R m).eval t + (S R (m - 1)).eval t) • x + ((S R m).eval t * -g x) • y :=
  mod_cast reflection_mul_reflection_mul_reflection_zpow_apply_self hf hg m t ht

end

/-! ### Lemmas used to prove uniqueness results for root data -/

/-- See also `Module.Dual.eq_of_preReflection_mapsTo'` for a variant of this lemma which
applies when `Φ` does not span.

This rather technical-looking lemma exists because it is exactly what is needed to establish various
uniqueness results for root data / systems. One might regard this lemma as lying at the boundary of
linear algebra and combinatorics since the finiteness assumption is the key. -/
lemma Dual.eq_of_preReflection_mapsTo [CharZero R] [NoZeroSMulDivisors R M]
    {x : M} {Φ : Set M} (hΦ₁ : Φ.Finite) (hΦ₂ : span R Φ = ⊤) {f g : Dual R M}
    (hf₁ : f x = 2) (hf₂ : MapsTo (preReflection x f) Φ Φ)
    (hg₁ : g x = 2) (hg₂ : MapsTo (preReflection x g) Φ Φ) :
    f = g := by
  have hx : x ≠ 0 := by rintro rfl; simp at hf₁
  let u := reflection hg₁ * reflection hf₁
  have hu : u = LinearMap.id (R := R) (M := M) + (f - g).smulRight x := by
    ext y
    simp only [u, reflection_apply, hg₁, two_smul, LinearEquiv.coe_toLinearMap_mul,
      LinearMap.id_coe, LinearEquiv.coe_coe, Module.End.mul_apply, LinearMap.add_apply, id_eq,
      LinearMap.coe_smulRight, LinearMap.sub_apply, map_sub, map_smul, sub_add_cancel_left,
      smul_neg, sub_neg_eq_add, sub_smul]
    abel
  replace hu : ∀ (n : ℕ),
      ↑(u ^ n) = LinearMap.id (R := R) (M := M) + (n : R) • (f - g).smulRight x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have : ((f - g).smulRight x).comp ((n : R) • (f - g).smulRight x) = 0 := by
        ext; simp [hf₁, hg₁]
      rw [pow_succ', LinearEquiv.coe_toLinearMap_mul, ih, hu, add_mul, mul_add, mul_add]
      simp_rw [Module.End.mul_eq_comp, LinearMap.comp_id, LinearMap.id_comp, this, add_zero,
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
    {x : M} {Φ : Set M} (hΦ₁ : Φ.Finite) (hx : x ∈ span R Φ) {f g : Dual R M}
    (hf₁ : f x = 2) (hf₂ : MapsTo (preReflection x f) Φ Φ)
    (hg₁ : g x = 2) (hg₂ : MapsTo (preReflection x g) Φ Φ) :
    (span R Φ).subtype.dualMap f = (span R Φ).subtype.dualMap g := by
  set Φ' : Set (span R Φ) := range (inclusion <| Submodule.subset_span (R := R) (s := Φ))
  rw [← finite_coe_iff] at hΦ₁
  have hΦ'₁ : Φ'.Finite := finite_range (inclusion Submodule.subset_span)
  have hΦ'₂ : span R Φ' = ⊤ := by
    simp only [Φ']
    rw [range_inclusion]
    simp
  let x' : span R Φ := ⟨x, hx⟩
  have this : ∀ {F : Dual R M}, MapsTo (preReflection x F) Φ Φ →
      MapsTo (preReflection x' ((span R Φ).subtype.dualMap F)) Φ' Φ' := by
    intro F hF ⟨y, hy⟩ hy'
    simp only [Φ'] at hy' ⊢
    rw [range_inclusion] at hy'
    simp only [SetLike.coe_sort_coe, mem_setOf_eq] at hy' ⊢
    rw [range_inclusion]
    exact hF hy'
  exact eq_of_preReflection_mapsTo hΦ'₁ hΦ'₂ hf₁ (this hf₂) hg₁ (this hg₂)

variable {y}
variable {g : Dual R M}

/-- Composite of reflections in "parallel" hyperplanes is a shear (special case). -/
lemma reflection_reflection_iterate
    (hfx : f x = 2) (hgy : g y = 2) (hgxfy : f y * g x = 4) (n : ℕ) :
    ((reflection hgy).trans (reflection hfx))^[n] y = y + n • (f y • x - (2 : R) • y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz : ∀ z : M, f y • g x • z = 2 • 2 • z := by
      intro z
      rw [smul_smul, hgxfy, smul_smul, ← Nat.cast_smul_eq_nsmul R (2 * 2), show 2 * 2 = 4 from rfl,
        Nat.cast_ofNat]
    simp only [iterate_succ', comp_apply, ih, two_smul, smul_sub, smul_add, map_add,
      LinearEquiv.trans_apply, reflection_apply_self, map_neg, reflection_apply, neg_sub, map_sub,
      map_nsmul, map_smul, smul_neg, hz, add_smul]
    abel

lemma infinite_range_reflection_reflection_iterate_iff [NoZeroSMulDivisors ℤ M]
    (hfx : f x = 2) (hgy : g y = 2) (hgxfy : f y * g x = 4) :
    (range <| fun n ↦ ((reflection hgy).trans (reflection hfx))^[n] y).Infinite ↔
    f y • x ≠ (2 : R) • y := by
  simp only [reflection_reflection_iterate hfx hgy hgxfy, infinite_range_add_nsmul_iff, sub_ne_zero]

lemma eq_of_mapsTo_reflection_of_mem [NoZeroSMulDivisors ℤ M] {Φ : Set M} (hΦ : Φ.Finite)
    (hfx : f x = 2) (hgy : g y = 2) (hgx : g x = 2) (hfy : f y = 2)
    (hxfΦ : MapsTo (preReflection x f) Φ Φ)
    (hygΦ : MapsTo (preReflection y g) Φ Φ)
    (hyΦ : y ∈ Φ) :
    x = y := by
  suffices h : f y • x = (2 : R) • y by
    rw [hfy, two_smul R x, two_smul R y, ← two_zsmul, ← two_zsmul] at h
    exact smul_right_injective _ two_ne_zero h
  rw [← not_infinite] at hΦ
  contrapose! hΦ
  apply ((infinite_range_reflection_reflection_iterate_iff hfx hgy
    (by rw [hfy, hgx]; norm_cast)).mpr hΦ).mono
  rw [range_subset_iff]
  intro n
  rw [← IsFixedPt.image_iterate ((bijOn_reflection_of_mapsTo hfx hxfΦ).comp
    (bijOn_reflection_of_mapsTo hgy hygΦ)).image_eq n]
  exact mem_image_of_mem _ hyΦ

lemma injOn_dualMap_subtype_span_range_range {ι : Type*} [NoZeroSMulDivisors ℤ M]
    {r : ι ↪ M} {c : ι → Dual R M} (hfin : (range r).Finite)
    (h_two : ∀ i, c i (r i) = 2)
    (h_mapsTo : ∀ i, MapsTo (preReflection (r i) (c i)) (range r) (range r)) :
    InjOn (span R (range r)).subtype.dualMap (range c) := by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩ hij
  congr
  suffices ∀ k, c i (r k) = c j (r k) by
    rw [← EmbeddingLike.apply_eq_iff_eq r]
    exact eq_of_mapsTo_reflection_of_mem (f := c i) (g := c j) hfin (h_two i) (h_two j)
      (by rw [← this, h_two]) (by rw [this, h_two]) (h_mapsTo i) (h_mapsTo j) (mem_range_self j)
  intro k
  simpa using LinearMap.congr_fun hij ⟨r k, Submodule.subset_span (mem_range_self k)⟩

end Module
