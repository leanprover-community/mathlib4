/-
Copyright (c) 2023 Hanneke Wiersema. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Hanneke Wiersema
-/
import Mathlib.Tactic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!

# The cyclotomic character

Let `L` is a field and let `n : ℕ+` be a positive integer. If `μₙ` is the
group of `n`th roots of unity in `L` then any field automorphism `g` of `L`
induces an automorphism of `μₙ` which, being a cyclic group, must be of
the form `ζ ↦ ζ^j` for some integer `j = j(g)`, well-defined in `ZMod d`, with
`d` the cardinality of `μₙ`. The function `j` is a group homomorphism
`(L ≃+* L) →* ZMod d`.

Future work: If `L` is separably closed (e.g. algebraically closed) and `p` is a prime
number such that `p ≠ 0` in `L`, then applying the above construction with
`n = p^i` (noting that the size of `μₙ` is `p^i`) gives a compatible collection of
group homomorphisms `(L ≃+* L) →* ZMod (p^i)` which glue to give
a group homomorphism `(L ≃+* L) →* ℤₚ`; this is the `p`-adic cyclotomic character.

## Important definitions

Let `L` be a field, `g : L ≃+* L` and `n : ℕ+`. Let `d` be the number of `n`th roots of `1` in `L`.

* `ModularCyclotomicCharacter n : L ≃+* L →* ZMod d` sends `g` to the unique `j` such
   that `g(ζ)=ζ^j` for all `ζ : rootsOfUnity n L`.

## Todo

* Prove the compatibility of `ModularCyclotomicCharacter n` and `ModularCyclotomicCharacter m`
if `n ∣ m`.

* Define the cyclotomic character.

* Prove that it's continuous.

## Tags

cyclotomic character
-/

universe u
variable {L : Type u} [Field L]

/-

## The mod n theory

-/

variable (n : ℕ+)

theorem rootsOfUnity.integer_power_of_ringEquiv (g : L ≃+* L) :
    ∃ m : ℤ, ∀ t : rootsOfUnity n L, g (t : Lˣ) = (t ^ m : Lˣ) := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (g.restrictRootsOfUnity n).toMonoidHom
  exact ⟨m, by simp [← hm]⟩

/-- `ModularCyclotomicCharacter_aux g n` is a non-canonical auxiliary integer `j`,
   only well-defined modulo the number of `n`'th roots of unity in `L`, such that `g(ζ)=ζ^j`
   for all `n`'th roots of unity `ζ` in `L`. -/
noncomputable def ModularCyclotomicCharacter_aux (g : L ≃+* L) (n : ℕ+) : ℤ :=
  (rootsOfUnity.integer_power_of_ringEquiv n g).choose

-- the only thing we know about `ModularCyclotomicCharacter_aux g n`
theorem ModularCyclotomicCharacter_aux_spec (g : L ≃+* L) (n : ℕ+) :
    ∀ t : rootsOfUnity n L, g (t : Lˣ) = (t ^ (ModularCyclotomicCharacter_aux g n) : Lˣ) :=
  (rootsOfUnity.integer_power_of_ringEquiv n g).choose_spec

/-- If `g` is a field automorphism of `L`, and `n : ℕ+`, then
  `ModularCyclotomicCharacter.toFun n g` is the `j : ZMod d` such that `g(ζ)=ζ^j` for all
  `n`'th roots of unity. Here `d` is the number of `n`th roots of unity in `L`. -/
noncomputable def ModularCyclotomicCharacter.toFun (n : ℕ+) (g : L ≃+* L) :
    ZMod (Fintype.card (rootsOfUnity n L)) :=
  ModularCyclotomicCharacter_aux g n

-- This appears to be missing from the library. It should not be in this file.
theorem Group.pow_eq_zpow_mod {G : Type _} [Group G] {x : G} (m : ℤ) {n : ℕ} (h : x ^ n = 1) :
    x ^ m = x ^ (m % (n : ℤ)) := by
  have h2 : x ^ m = x ^ ((n : ℤ) * (m / (n : ℤ)) + m % (n : ℤ)) :=
    congr_arg (fun a => x ^ a) ((Int.add_comm _ _).trans (Int.emod_add_ediv _ _)).symm
  simp [h, h2, zpow_add, zpow_mul]

namespace ModularCyclotomicCharacter

local notation "χ" => ModularCyclotomicCharacter.toFun

/-- The formula which characterises the output of `ModularCyclotomicCharacter g n`. -/
theorem spec (g : L ≃+* L) (n : ℕ+) :
    ∀ t : rootsOfUnity n L, g (t : Lˣ) = (t ^ (χ n g).val : Lˣ) := by
  rintro t
  rw [ModularCyclotomicCharacter_aux_spec g n t, ← zpow_ofNat, ModularCyclotomicCharacter.toFun,
      ZMod.val_int_cast, ←Group.pow_eq_zpow_mod _ pow_card_eq_one]

lemma ext {G : Type _} [Group G] [Fintype G] [IsCyclic G]
    {d : ℕ} {a b : ZMod d} (hGcard : Fintype.card G = d) (h : ∀ t : G, t^a.val = t^b.val) :
  a = b := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hgord := orderOf_eq_card_of_forall_mem_zpowers hg
  specialize h g
  rw [pow_eq_pow_iff_modEq, hgord, hGcard, ← ZMod.nat_cast_eq_nat_cast_iff] at h
  subst hGcard
  simpa [ZMod.nat_cast_val, ZMod.cast_id'] using h

lemma id : χ n (RingEquiv.refl L) = 1 := by
  refine ext (G := rootsOfUnity n L) rfl ?_
  intro ζ
  ext
  rw [← spec]
  have : 1 ≤ Fintype.card { x // x ∈ rootsOfUnity n L } := Fin.size_positive'
  obtain (h | h) := this.lt_or_eq
  · have := Fact.mk h
    simp [ZMod.val_one]
  · have := Fintype.card_le_one_iff_subsingleton.mp h.ge
    obtain rfl : ζ = 1 := by apply Subsingleton.elim
    simp

lemma comp (g h : L ≃+* L) : χ n (g * h) =
    χ n g * χ n h := by
  refine ext (G := rootsOfUnity n L) rfl ?_
  intro ζ
  ext
  rw [← spec]
  change g (h (ζ : Lˣ)) = _
  rw [spec, spec, mul_comm, ← pow_mul, eq_comm]
  congr 2
  simp only [pow_eq_pow_iff_modEq, ← ZMod.nat_cast_eq_nat_cast_iff, SubmonoidClass.coe_pow,
    ZMod.nat_cast_val, Nat.cast_mul, ZMod.cast_mul (m := orderOf ζ) orderOf_dvd_card_univ]

end ModularCyclotomicCharacter

/-- Given a positive integer `n`, `ModularCyclotomicCharacter n` is a
multiplicative homomorphism from the automorphisms of a field `L` to `ℤ/dℤ`,
where `d` is the number of `n`'th roots of unity in `L`. It is uniquely
characterised by the property that `g(ζ)=ζ^(ModularCyclotomicCharacter n g)`
for `g` an automorphism of `L` and `ζ` an `n`th root of unity. -/
noncomputable
def ModularCyclotomicCharacter (n : ℕ+) :
    (L ≃+* L) →* ZMod (Fintype.card { x // x ∈ rootsOfUnity n L }) where
      toFun := ModularCyclotomicCharacter.toFun n
      map_one' := ModularCyclotomicCharacter.id n
      map_mul' := ModularCyclotomicCharacter.comp n
