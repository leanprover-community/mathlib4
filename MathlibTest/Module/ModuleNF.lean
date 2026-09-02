/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ModuleNF

section AddCommMonoid
variable {V : Type*} [AddCommMonoid V]

example (x y : V) : x + y = y + x := by module_nf
example (x : V) : 0 + x = x := by module_nf
example (x y : V) : x + (y + x) = x + x + y := by module_nf
example (x : V) : x + 2 • x = 2 • x + x := by module_nf
example (x : V) : (3 : ℕ) • x = x + (2 : ℕ) • x := by module_nf
example (n : ℕ) (x : V) : n • x = n • x := by module_nf
example (n : ℕ) (x : V) : 0 + n • x = n • x := by module_nf
example (u v x y z : V) :
    x + (y + (x + (z + (x + (u + (x + v)))))) = v + u + z + y + 4 • x := by module_nf

end AddCommMonoid

section CommRing
variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

example (a b : R) (x : M) : a • x + b • x = (a + b) • x := by module_nf
example (a b : R) (x : M) : a • x + b • x = (b + a) • x := by module_nf
example (a b : R) (x : M) : a • x - b • x = (a - b) • x := by module_nf
example (a b : R) (x y : M) : a • x - b • y = a • x + (-b) • y := by module_nf
example (a : R) (x y : M) : a • x - a • x + y = y := by module_nf
example (a b : R) (x : M) : a • b • x = (a * b) • x := by module_nf
example (a : R) (x : M) : 2 • a • x = a • 2 • x := by module_nf
example (a : R) (x : M) : (2 : ℤ) • a • x = a • x + a • x := by module_nf

example (a : R) (v w : M) :
    (1 + a ^ 2) • (v + w) - a • (a • v - w) = v + (1 + a + a ^ 2) • w := by module_nf
example (a b μ ν : R) (x y : M) :
    (μ - ν) • a • x = (a • μ • x + b • ν • y) - ν • (a • x + b • y) := by module_nf
example (a b : R) (x y : M) :
    a • (x, y) + b • (x, y) = (a + b) • ((x, y) : M × M) := by module_nf

example (x : M) : -x + x = 0 := by module_nf
example (x : M) : x - 0 = x := by module_nf
example (x : M) : x - (0 - 0) = x := by module_nf
example (x y : M) : x + (y - x) = y := by module_nf
example (x y : M) : (x + y) - ((y + x) + x) = -x := by module_nf
example (x : M) : (3 : ℤ) • x = x + (2 : ℤ) • x := by module_nf
example (x y z w : M) : x + y + (z + w - x) = y + z + w := by module_nf
example (x y z : M) : -y + (z - x) = z - y - x := by module_nf
example (x y z : M) : x + y + z + (z - x - x) = (-1) • x + y + 2 • z := by module_nf

example (x : M) : x + x = (2 : ℤ) • x := by module_nf
example (x : M) : (2 : ℤ) • x = (2 : ℕ) • x := by module_nf
example (x : M) : (2 : R) • x = (2 : ℕ) • x := by module_nf
example (x : M) : (2 : R) • x - x - x = 0 := by module_nf

example {S : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    (r : R) (x : M) : algebraMap R S r • x = r • x := by module_nf

example {S : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    (r : R) (s : S) (x : M) : r • s • x = s • r • x := by module_nf

example {K : Type*} [Field K] [CharZero K] [Module K M] (x : M) :
    (2 : K)⁻¹ • x + (3 : K)⁻¹ • x + (6 : K)⁻¹ • x = x := by module_nf

example (a b : R) (x : M) (h : a = b) : a • x = b • x := by
  linear_combination (norm := module_nf) h • x

example (a b : R) (x y : M) (h : a • x + b • x = y) : (b + a) • x = y := by
  module_nf at h ⊢
  exact h

example (a b : R) (x y : M) (h : a • x + b • x = y) : (b + a) • x = y := by
  module_nf at *
  exact h

example (x : M) (h : x + (2 : ℤ) • x = 0) : x + x + x = 0 := by
  module_nf at h ⊢
  exact h

-- `module_nf` cannot make progress on `_h2` but it is ignored
example (a b : R) (x y : M) (h : a • x + b • x = y) (_h2 : True) : (b + a) • x = y := by
  module_nf at *
  exact h

example (x y : M) (h : (1 : R) • x + (0 : R) • y = 0) : x = 0 := by
  module_nf at h
  exact h

-- surviving negative unit coefficients are displayed with `-`
example (x y : M) (h : x - y - x = 0) : -y = 0 := by
  module_nf at h
  exact h

example (x : M) (h : x + x + x = 0) : (3 : ℕ) • x = 0 := by
  module_nf at h
  exact h

-- `module_nf` errors if it makes no progress
example (h : True) : True := by
  fail_if_success module_nf at h
  exact h

-- a location built only from atoms is already in normal form: no progress is reported
example (f g : M → M) (x : M) (h : f x = g x) : f x = g x := by
  fail_if_success module_nf at h
  exact h

example (f : M → M) (a b : R) (x : M) : f (a • x + b • x) = f ((a + b) • x) := by
  module_nf

example (f : M → M) (a b : R) (x : M) (h : f ((a + b) • x) = 0) :
    f (a • x + b • x) = 0 := by
  calc f (a • x + b • x) = f ((a + b) • x) := by module_nf
    _ = 0 := h

example (p : M → Prop) (f : M → M) (a b : R) (x : M) (h : p (f (b • x + a • x))) :
    p (f (a • x + b • x)) := by
  module_nf at h ⊢
  guard_target =~ p (f ((_ : R) • x))
  exact h

example [Preorder M] (a b : R) (x y : M) (h : (a + b) • x ≤ y) : a • x + b • x ≤ y := by
  module_nf at h ⊢
  guard_target =~ (_ : R) • x ≤ y
  exact h

-- atoms are identified at `.instances` transparency, like `match_scalars` and `module`:
-- `((2 : ℕ) : R)` and `(2 : R)` are the same atom
example (f : R → M) : f ((2 : ℕ) : R) + f ((2 : ℕ) : R) = f (2 : R) + f ((2 : ℕ) : R) := by
  module_nf

example (s : Set M) (a b : R) (x : M) (h : (a + b) • x ∈ s) : a • x + b • x ∈ s := by
  module_nf at h ⊢
  guard_target =~ (_ : R) • x ∈ s
  exact h

example (a b : R) (h : a + b = 1) (x y : M) :
    a • (x + y) + b • x + b • y = x + y := by
  module_nf
  rw [h, one_smul, one_smul]

example (s : Set M) (a : R) (x v w : M) (h : x + a • (v + w) ∈ s) :
    x + (a • v + a • w) ∈ s := by
  module_nf at h ⊢
  exact h

example (a b : R) : ∀ y : M, a • y + b • y = (a + b) • y := by
  module_nf
  exact fun _ => trivial

example (a b : R) (h : ∀ y : M, a • y + b • y = 0) (x : M) : (a + b) • x = 0 := by
  module_nf at h ⊢
  guard_target =~ (_ : R) • x = 0
  exact h x

example (a b : R) : (fun y : M => a • y + b • y) = (fun y => (a + b) • y) := by module_nf

example (a b : R) (x : M) : (a • x + b • x = 0) ↔ ((a + b) • x = 0) := by module_nf

example (s : Finset ℕ) (v : ℕ → M) (a b : R) :
    ∑ i ∈ s, (a • v i + b • v i) = ∑ i ∈ s, (a + b) • v i := by
  module_nf

example {A : Type*} [Ring A] [Module A M] (a b : A) (x : M) :
    a • x + b • x = (a + b) • x := by
  module_nf

example {S : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    (a b : R) (u : S) (x y : M) (P : M → Prop) (h : P (b • x + y)) :
    P (a • x + u • y + (1 - u) • y - (a - b) • x) := by
  module_nf at h ⊢
  exact h

example {S : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    (a b : R) (u : S) (x y : M) (P : M → Prop) (h : P (b • x + u • y)) :
    P (a • x + 1 • y + (u - 1) • y - (a - b) • x) := by
  module_nf at h ⊢
  exact h

example {S : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    (a b : R) (u v : S) (x y : M) (P : M → Prop) (h : P (b • x + y)) :
    P (a • x + u • y + (1 - u) • y - (a - b) • x + v • x - v • x) := by
  module_nf at h ⊢
  exact h

example {K : Type*} [Field K] [Module K M] (a : K) (ha : a ≠ 0) (x : M) :
    a⁻¹ • a • x = x := by
  module_nf
  rw [mul_inv_cancel₀ ha, one_smul]

example (x : M) (P : M → Prop) (h : P ((2 : ℤ) • x)) :
    P (x + x) ∧ P ((2 : ℤ) • x) := by
  module_nf with ℤ at h ⊢
  guard_target =~ P ((_ : ℤ) • x) ∧ P ((_ : ℤ) • x)
  exact ⟨h, h⟩

-- `with R` requires `R` to be a semiring
example (x : M) : x + x = (2 : ℤ) • x := by
  fail_if_success module_nf with M
  module_nf with ℤ

example (x : M) : ((2 : ℤ) • x = (x + x)) ∧ ((2 : R) • x = (2 : ℤ) • x) := by
  module_nf with R
  exact ⟨trivial, trivial⟩

example {K : Type*} [Field K] [Module K M] (x y : M) (h : x + x = y) : (2 : K) • x = y := by
  module_nf with K at h ⊢
  guard_target =~ (_ : K) • x = y
  exact h

-- `h` cannot use the scalar ring `ℤ` but it falls back to `R`, its own ring
example (a : R) (x y : M) (h : a • x + a • x = y) : (a * 2) • x = y := by
  module_nf with ℤ at h ⊢
  guard_target =~ (_ : R) • x = y
  exact h

example {S T : Type*} [CommRing S] [CommRing T] [Module S M] [Module T M]
    (s : S) (t : T) (x y : M)
    (h₁ : s • x + s • x = 0) (h₂ : t • y + t • y = 0) :
    (s * 2) • x = 0 ∧ (t * 2) • y = 0 := by
  module_nf at h₁ h₂ ⊢
  guard_target =~ (_ : S) • x = 0 ∧ (_ : T) • y = 0
  exact ⟨h₁, h₂⟩

example (f : M → M) (c a b : R) (x : M) :
    c • f (a • x + b • x) + c • f ((a + b) • x) = (2 : ℕ) • c • f ((a + b) • x) := by
  module_nf

example (f : M → R) (x y z : M)
    (h : f (x + y + z + (x - z)) + f (x + y + z - (x - z)) = 0) :
    f (2 • x + y) + f (y + 2 • z) = 0 := by
  module_nf with ℤ at h ⊢
  exact h

example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (f : ℕ → R) (n : ℕ) (y : M)
    (h : (f (n + n) + 1 - 1) • y = 0) : f (n + n) • y = 0 := by
  module_nf at *
  guard_hyp h : f (2 • n) • y = 0
  guard_target = f (2 • n) • y = 0
  exact h

example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (f : M → R) (a b c d: R) (x y : M)
    (_h1 : (f (a • x + b • x) + 1 - 1) • y = 0)
    (h2 : f ((c + d) • x) • y = 0) : f (c • x + d • x) • y = 0 := by
  module_nf at *
  guard_hyp _h1 : f ((a + b) • x) • y = 0
  guard_target = f ((c + d) • x) • y = 0
  exact h2

end CommRing
