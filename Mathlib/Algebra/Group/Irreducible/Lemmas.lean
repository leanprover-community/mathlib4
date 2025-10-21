/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Yaël Dillies
-/
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Irreducible.Defs
import Mathlib.Algebra.Group.Units.Equiv

/-!
# More lemmas about irreducible elements
-/

assert_not_exists MonoidWithZero OrderedCommMonoid Multiset

variable {F M N : Type*}

section Monoid
variable [Monoid M] [Monoid N] {f : F} {x y : M}

@[to_additive]
lemma not_irreducible_pow : ∀ {n : ℕ}, n ≠ 1 → ¬ Irreducible (x ^ n)
  | 0, _ => by simp
  | n + 2, _ => by
    intro ⟨h₁, h₂⟩
    have := h₂ (pow_succ _ _)
    rw [isUnit_pow_iff n.succ_ne_zero, or_self] at this
    exact h₁ (this.pow _)

@[to_additive]
lemma irreducible_units_mul (u : Mˣ) : Irreducible (u * y) ↔ Irreducible y := by
  simp only [irreducible_iff, Units.isUnit_units_mul, and_congr_right_iff]
  refine fun _ => ⟨fun h A B HAB => ?_, fun h A B HAB => ?_⟩
  · rw [← u.isUnit_units_mul]
    apply h
    rw [mul_assoc, ← HAB]
  · rw [← u⁻¹.isUnit_units_mul]
    apply h
    rw [mul_assoc, ← HAB, Units.inv_mul_cancel_left]

@[to_additive]
lemma irreducible_isUnit_mul (h : IsUnit x) : Irreducible (x * y) ↔ Irreducible y :=
  let ⟨x, ha⟩ := h
  ha ▸ irreducible_units_mul x

@[to_additive]
lemma irreducible_mul_units (u : Mˣ) : Irreducible (y * u) ↔ Irreducible y := by
  simp only [irreducible_iff, Units.isUnit_mul_units, and_congr_right_iff]
  refine fun _ => ⟨fun h A B HAB => ?_, fun h A B HAB => ?_⟩
  · rw [← u.isUnit_mul_units B]
    apply h
    rw [← mul_assoc, ← HAB]
  · rw [← u⁻¹.isUnit_mul_units B]
    apply h
    rw [← mul_assoc, ← HAB, Units.mul_inv_cancel_right]

@[to_additive]
lemma irreducible_mul_isUnit (h : IsUnit x) : Irreducible (y * x) ↔ Irreducible y :=
  let ⟨x, hx⟩ := h
  hx ▸ irreducible_mul_units x

@[to_additive]
lemma irreducible_mul_iff :
    Irreducible (x * y) ↔ Irreducible x ∧ IsUnit y ∨ Irreducible y ∧ IsUnit x := by
  constructor
  · refine fun h => Or.imp (fun h' => ⟨?_, h'⟩) (fun h' => ⟨?_, h'⟩) (h.isUnit_or_isUnit rfl).symm
    · rwa [irreducible_mul_isUnit h'] at h
    · rwa [irreducible_isUnit_mul h'] at h
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
    · rwa [irreducible_mul_isUnit hb]
    · rwa [irreducible_isUnit_mul ha]

section MulEquivClass
variable [EquivLike F M N] [MulEquivClass F M N] (f : F)

@[to_additive]
lemma MulEquiv.irreducible_iff : Irreducible (f x) ↔ Irreducible x := by
  simp [_root_.irreducible_iff, (EquivLike.surjective f).forall, ← map_mul, -isUnit_map_iff]

/-- Irreducibility is preserved by multiplicative equivalences.

Note that surjective + local hom is not enough. Consider the additive monoids `M = ℕ ⊕ ℕ`, `N = ℕ`,
with x surjective local (additive) hom `f : M →+ N` sending `(m, n)` to `2m + n`.
It is local because the only add unit in `N` is `0`, with preimage `{(0, 0)}` also an add unit.
Then `x = (1, 0)` is irreducible in `M`, but `f x = 2 = 1 + 1` is not irreducible in `N`. -/
@[to_additive /-- Irreducibility is preserved by additive equivalences. -/]
alias ⟨_, Irreducible.map⟩ := MulEquiv.irreducible_iff

end MulEquivClass

lemma Irreducible.of_map [FunLike F M N] [MonoidHomClass F M N] [IsLocalHom f]
    (hfx : Irreducible (f x)) : Irreducible x where
  not_isUnit hu := hfx.not_isUnit <| hu.map f
  isUnit_or_isUnit := by
    rintro p q rfl; exact (hfx.isUnit_or_isUnit <| map_mul f p q).imp (.of_map f _) (.of_map f _)

@[to_additive]
lemma Irreducible.not_isSquare (ha : Irreducible x) : ¬IsSquare x := by
  rw [isSquare_iff_exists_sq]
  rintro ⟨y, rfl⟩
  exact not_irreducible_pow (by decide) ha

@[to_additive]
lemma IsSquare.not_irreducible (ha : IsSquare x) : ¬Irreducible x := fun h => h.not_isSquare ha

end Monoid
