/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yury Kudryashov, Lawrence Wu
-/
module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# `Nat.divisors` as a multiplicative homomorphism

The main definition of this file is `Nat.divisorsHom : ℕ →* Finset ℕ`,
exhibiting `Nat.divisors` as a multiplicative homomorphism from `ℕ` to `Finset ℕ`.
-/

@[expose] public section

open Nat Finset
open scoped Pointwise

/-- The divisors of a product of natural numbers are the pointwise product of the divisors of the
factors. -/
lemma Nat.divisors_mul (m n : ℕ) : divisors (m * n) = divisors m * divisors n := by
  ext k
  simp_rw [mem_mul, mem_divisors, Nat.dvd_mul, mul_ne_zero_iff, ← exists_and_left,
    ← exists_and_right]
  simp only [and_assoc, and_comm, and_left_comm]

/-- `Nat.divisors` as a `MonoidHom`. -/
@[simps]
def Nat.divisorsHom : ℕ →* Finset ℕ where
  toFun := Nat.divisors
  map_mul' := divisors_mul
  map_one' := divisors_one

lemma Nat.Prime.divisors_sq {p : ℕ} (hp : p.Prime) : (p ^ 2).divisors = {p ^ 2, p, 1} := by
  simp [divisors_prime_pow hp, range_add_one]

lemma List.nat_divisors_prod (l : List ℕ) : divisors l.prod = (l.map divisors).prod :=
  map_list_prod Nat.divisorsHom l

lemma Multiset.nat_divisors_prod (s : Multiset ℕ) : divisors s.prod = (s.map divisors).prod :=
  map_multiset_prod Nat.divisorsHom s

lemma Finset.nat_divisors_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    divisors (∏ i ∈ s, f i) = ∏ i ∈ s, divisors (f i) :=
  map_prod Nat.divisorsHom f s

/-- Products of divisors taken from coprime naturals are unique. -/
theorem Nat.Coprime.mul_injOn_divisors {m n : ℕ} (hmn : m.Coprime n) :
    Set.InjOn (fun p : ℕ × ℕ ↦ p.1 * p.2) ↑(divisors m ×ˢ divisors n) := by
  rintro ⟨dm₁, dn₁⟩ h₁ ⟨dm₂, dn₂⟩ h₂ hd
  simp only [Finset.mem_coe, Finset.mem_product, mem_divisors] at *
  suffices dm₁ = dm₂ from Prod.ext this <| by
    rwa [this, Nat.mul_right_inj (by simp [·] at h₂)] at hd
  exact dvd_antisymm
    (hmn.coprime_dvd_left h₁.1.1 |>.coprime_dvd_right h₂.2.1
      |>.dvd_of_dvd_mul_right (hd ▸ dm₁.dvd_mul_right dn₁))
    (hmn.coprime_dvd_left h₂.1.1 |>.coprime_dvd_right h₁.2.1
      |>.dvd_of_dvd_mul_right (hd ▸ dm₂.dvd_mul_right dn₂))

/-- A variant of `Nat.divisors_mul` with a more structured RHS. -/
theorem Nat.Coprime.divisors_mul {m n : ℕ} (hmn : m.Coprime n) :
    divisors (m * n) = (divisors m ×ˢ divisors n).attach.map
      ⟨fun p => p.val.1 * p.val.2,
        fun i j hxy => Subtype.ext <| hmn.mul_injOn_divisors i.prop j.prop hxy⟩ := calc
  _ = ((divisors m ×ˢ divisors n).attach.image Subtype.val).image fun p ↦ p.1 * p.2 := by
    rw [Finset.attach_image_val, ← Finset.mul_def, Nat.divisors_mul]
  _ = _ := by rw [Finset.map_eq_image, Finset.image_image]; rfl
