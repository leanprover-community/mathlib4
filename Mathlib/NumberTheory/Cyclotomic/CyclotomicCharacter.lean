/-
Copyright (c) 2023 Hanneke Wiersema. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Hanneke Wiersema
-/
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!

# The cyclotomic character

Let `L` be an integral domain and let `n : ℕ+` be a positive integer. If `μₙ` is the
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

Let `L` be an integral domain, `g : L ≃+* L` and `n : ℕ+`. Let `d` be the number of `n`th roots
of `1` in `L`.

* `ModularCyclotomicCharacter L n hn : (L ≃+* L) →* (ZMod n)ˣ` sends `g` to the unique `j` such
   that `g(ζ)=ζ^j` for all `ζ : rootsOfUnity n L`. Here `hn` is a proof that there
   are `n` `n`th roots of unity in `L`.

## Implementation note

In theory this could be set up as some theory about monoids, being a character
on monoid isomorphisms, but under the hypotheses that the `n`'th roots of unity
are cyclic of order `n`. The advantage of sticking to integral domains is that finite subgroups
are guaranteed to be cyclic, so the weaker assumption that there are `n` `n`th
roots of unity is enough. All the applications I'm aware of are when `L` is a
field anyway.

Although I don't know whether it's of any use, `ModularCyclotomicCharacter'`
is the general case for integral domains, with target in `(ZMod d)ˣ`
where `d` is the number of `n`th roots of unity in `L`.

## Todo

* Prove the compatibility of `ModularCyclotomicCharacter n` and `ModularCyclotomicCharacter m`
if `n ∣ m`.

* Define the cyclotomic character.

* Prove that it's continuous.

## Tags

cyclotomic character
-/

universe u
variable {L : Type u} [CommRing L] [IsDomain L]

/-

## The mod n theory

-/

variable (n : ℕ+)

theorem rootsOfUnity.integer_power_of_ringEquiv (g : L ≃+* L) :
    ∃ m : ℤ, ∀ t : rootsOfUnity n L, g (t : Lˣ) = (t ^ m : Lˣ) := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic ((g : L ≃* L).restrictRootsOfUnity n).toMonoidHom
  exact ⟨m, fun t ↦ Units.ext_iff.1 <| SetCoe.ext_iff.2 <| hm t⟩

theorem rootsOfUnity.integer_power_of_ringEquiv' (g : L ≃+* L) :
    ∃ m : ℤ, ∀ t ∈ rootsOfUnity n L, g (t : Lˣ) = (t ^ m : Lˣ) := by
  simpa using rootsOfUnity.integer_power_of_ringEquiv n g

/-- `ModularCyclotomicCharacter_aux g n` is a non-canonical auxiliary integer `j`,
   only well-defined modulo the number of `n`'th roots of unity in `L`, such that `g(ζ)=ζ^j`
   for all `n`'th roots of unity `ζ` in `L`. -/
noncomputable def ModularCyclotomicCharacter_aux (g : L ≃+* L) (n : ℕ+) : ℤ :=
  (rootsOfUnity.integer_power_of_ringEquiv n g).choose

-- the only thing we know about `ModularCyclotomicCharacter_aux g n`
theorem ModularCyclotomicCharacter_aux_spec (g : L ≃+* L) (n : ℕ+) :
    ∀ t : rootsOfUnity n L, g (t : Lˣ) = (t ^ (ModularCyclotomicCharacter_aux g n) : Lˣ) :=
  (rootsOfUnity.integer_power_of_ringEquiv n g).choose_spec

/-- If `g` is a ring automorphism of `L`, and `n : ℕ+`, then
  `ModularCyclotomicCharacter.toFun n g` is the `j : ZMod d` such that `g(ζ)=ζ^j` for all
  `n`'th roots of unity. Here `d` is the number of `n`th roots of unity in `L`. -/
noncomputable def ModularCyclotomicCharacter.toFun (n : ℕ+) (g : L ≃+* L) :
    ZMod (Fintype.card (rootsOfUnity n L)) :=
  ModularCyclotomicCharacter_aux g n

namespace ModularCyclotomicCharacter

local notation "χ" => ModularCyclotomicCharacter.toFun

/-- The formula which characterises the output of `ModularCyclotomicCharacter g n`. -/
theorem spec (g : L ≃+* L) {n : ℕ+} (t : rootsOfUnity n L) :
    g (t : Lˣ) = (t ^ (χ n g).val : Lˣ) := by
  rw [ModularCyclotomicCharacter_aux_spec g n t, ← zpow_coe_nat, ModularCyclotomicCharacter.toFun,
    ZMod.val_int_cast, ← Subgroup.coe_zpow]
  exact Units.ext_iff.1 <| SetCoe.ext_iff.2 <| zpow_eq_zpow_emod _ pow_card_eq_one

theorem spec' (g : L ≃+* L) {n : ℕ+} {t : Lˣ} (ht : t ∈ rootsOfUnity n L) :
    g t = t ^ (χ n g).val :=
  spec g ⟨t, ht⟩

theorem spec'' (g : L ≃+* L) {n : ℕ+} {t : L} (ht : IsPrimitiveRoot t n) :
    g t = t ^ (χ n g).val :=
  spec' g (SetLike.coe_mem ht.toRootsOfUnity)

lemma id : χ n (RingEquiv.refl L) = 1 := by
  refine IsCyclic.ext (G := rootsOfUnity n L) rfl ?_
  intro ζ
  ext
  rw [Subgroup.coe_pow, ← spec]
  have : 1 ≤ Fintype.card { x // x ∈ rootsOfUnity n L } := Fin.size_positive'
  obtain (h | h) := this.lt_or_eq
  · have := Fact.mk h
    simp [ZMod.val_one]
  · have := Fintype.card_le_one_iff_subsingleton.mp h.ge
    obtain rfl : ζ = 1 := Subsingleton.elim ζ 1
    simp

lemma comp (g h : L ≃+* L) : χ n (g * h) =
    χ n g * χ n h := by
  refine IsCyclic.ext (G := rootsOfUnity n L) rfl ?_
  intro ζ
  ext
  rw [Subgroup.coe_pow, ← spec]
  change g (h (ζ : Lˣ)) = _
  rw [spec, ← Subgroup.coe_pow, spec, mul_comm, Subgroup.coe_pow, ← pow_mul, ← Subgroup.coe_pow]
  congr 2
  simp only [pow_eq_pow_iff_modEq, ← ZMod.nat_cast_eq_nat_cast_iff, SubmonoidClass.coe_pow,
    ZMod.nat_cast_val, Nat.cast_mul, ZMod.cast_mul (m := orderOf ζ) orderOf_dvd_card]

end ModularCyclotomicCharacter

variable (L)

/-- Given a positive integer `n`, `ModularCyclotomicCharacter' n` is a
multiplicative homomorphism from the automorphisms of a field `L` to `ℤ/dℤˣ`,
where `d` is the number of `n`'th roots of unity in `L`. It is uniquely
characterised by the property that `g(ζ)=ζ^(ModularCyclotomicCharacter n g)`
for `g` an automorphism of `L` and `ζ` an `n`th root of unity. -/
noncomputable
def ModularCyclotomicCharacter' (n : ℕ+) :
    (L ≃+* L) →* (ZMod (Fintype.card { x // x ∈ rootsOfUnity n L }))ˣ := MonoidHom.toHomUnits
  { toFun := ModularCyclotomicCharacter.toFun n
    map_one' := ModularCyclotomicCharacter.id n
    map_mul' := ModularCyclotomicCharacter.comp n }

/-- Given a positive integer `n` and a field `L` containing `n` `n`th roots
of unity, `ModularCyclotomicCharacter n` is a multiplicative homomorphism from the
automorphisms of `L` to `ℤ/nℤ`. It is uniquely characterised by the property that
`g(ζ)=ζ^(ModularCyclotomicCharacter n g)` for `g` an automorphism of `L` and `ζ` any `n`th root
of unity. -/
noncomputable def ModularCyclotomicCharacter (n : ℕ+)
    (hn : Fintype.card { x // x ∈ rootsOfUnity n L } = n) :
    (L ≃+* L) →* (ZMod n)ˣ :=
  (Units.mapEquiv <| (ZMod.ringEquivCongr hn).toMulEquiv).toMonoidHom.comp
  (ModularCyclotomicCharacter' L n)

variable {L}

/-- The relationship between `IsPrimitiveRoot.autToPow` and
`ModularCyclotomicCharacter`. Note that `IsPrimitiveRoot.autToPow`
needs an explicit root of unity, and also an auxiliary "base ring" `R`. -/
lemma IsPrimitiveRoot.autToPow_eq_ModularCyclotomicCharacter (n : ℕ+)
    (R : Type*) [CommRing R] [Algebra R L] {μ : L} (hμ : IsPrimitiveRoot μ n) (g : L ≃ₐ[R] L) :
    hμ.autToPow R g = ModularCyclotomicCharacter L n hμ.card_rootsOfUnity g := by
  ext
  apply ZMod.val_injective
  apply hμ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  simpa [autToPow_spec R hμ g, ModularCyclotomicCharacter', ModularCyclotomicCharacter,
    ZMod.ringEquivCongr_val] using ModularCyclotomicCharacter.spec'' g hμ
