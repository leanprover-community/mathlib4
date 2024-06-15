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
are cyclic. The advantage of sticking to integral domains is that finite subgroups
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

local notation "χ₀" => ModularCyclotomicCharacter.toFun

set_option backward.synthInstance.canonInstances false in -- See https://github.com/leanprover-community/mathlib4/issues/12532
/-- The formula which characterises the output of `ModularCyclotomicCharacter g n`. -/
theorem toFun_spec (g : L ≃+* L) {n : ℕ+} (t : rootsOfUnity n L) :
    g (t : Lˣ) = (t ^ (χ₀ n g).val : Lˣ) := by
  rw [ModularCyclotomicCharacter_aux_spec g n t, ← zpow_natCast, ModularCyclotomicCharacter.toFun,
    ZMod.val_intCast, ← Subgroup.coe_zpow]
  exact Units.ext_iff.1 <| SetCoe.ext_iff.2 <| zpow_eq_zpow_emod _ pow_card_eq_one

theorem toFun_spec' (g : L ≃+* L) {n : ℕ+} {t : Lˣ} (ht : t ∈ rootsOfUnity n L) :
    g t = t ^ (χ₀ n g).val :=
  toFun_spec g ⟨t, ht⟩

theorem toFun_spec'' (g : L ≃+* L) {n : ℕ+} {t : L} (ht : IsPrimitiveRoot t n) :
    g t = t ^ (χ₀ n g).val :=
  toFun_spec' g (SetLike.coe_mem ht.toRootsOfUnity)

/-- If g(t)=t^c for all roots of unity, then c=χ(g). -/
theorem toFun_unique (g : L ≃+* L) (c : ZMod (Fintype.card (rootsOfUnity n L)))
    (hc : ∀ t : rootsOfUnity n L, g (t : Lˣ) = (t ^ c.val : Lˣ)) : c = χ₀ n g := by
  apply IsCyclic.ext rfl (fun ζ ↦ ?_)
  specialize hc ζ
  suffices ((ζ ^ c.val : Lˣ) : L) = (ζ ^ (χ₀ n g).val : Lˣ) by exact_mod_cast this
  rw [← toFun_spec g ζ, hc]

theorem toFun_unique' (g : L ≃+* L) (c : ZMod (Fintype.card (rootsOfUnity n L)))
    (hc : ∀ t ∈ rootsOfUnity n L, g t = t ^ c.val) : c = χ₀ n g :=
  toFun_unique n g c (fun ⟨_, ht⟩ ↦ hc _ ht)

set_option backward.synthInstance.canonInstances false in -- See https://github.com/leanprover-community/mathlib4/issues/12532
lemma id : χ₀ n (RingEquiv.refl L) = 1 := by
  refine (toFun_unique n (RingEquiv.refl L) 1 <| fun t ↦ ?_).symm
  have : 1 ≤ Fintype.card { x // x ∈ rootsOfUnity n L } := Fin.size_positive'
  obtain (h | h) := this.lt_or_eq
  · have := Fact.mk h
    simp [ZMod.val_one]
  · have := Fintype.card_le_one_iff_subsingleton.mp h.ge
    obtain rfl : t = 1 := Subsingleton.elim t 1
    simp

set_option backward.synthInstance.canonInstances false in -- See https://github.com/leanprover-community/mathlib4/issues/12532
lemma comp (g h : L ≃+* L) : χ₀ n (g * h) =
    χ₀ n g * χ₀ n h := by
  refine (toFun_unique n (g * h) _ <| fun ζ ↦ ?_).symm
  change g (h (ζ : Lˣ)) = _
  rw [toFun_spec, ← Subgroup.coe_pow, toFun_spec, mul_comm, Subgroup.coe_pow, ← pow_mul,
    ← Subgroup.coe_pow]
  congr 2
  norm_cast
  simp only [pow_eq_pow_iff_modEq, ← ZMod.natCast_eq_natCast_iff, SubmonoidClass.coe_pow,
    ZMod.natCast_val, Nat.cast_mul, ZMod.cast_mul (m := orderOf ζ) orderOf_dvd_card]

end ModularCyclotomicCharacter

variable (L)

/-- Given a positive integer `n`, `ModularCyclotomicCharacter' n` is a
multiplicative homomorphism from the automorphisms of a field `L` to `(ℤ/dℤ)ˣ`,
where `d` is the number of `n`'th roots of unity in `L`. It is uniquely
characterised by the property that `g(ζ)=ζ^(ModularCyclotomicCharacter n g)`
for `g` an automorphism of `L` and `ζ` an `n`th root of unity. -/
noncomputable
def ModularCyclotomicCharacter' (n : ℕ+) :
    (L ≃+* L) →* (ZMod (Fintype.card { x // x ∈ rootsOfUnity n L }))ˣ := MonoidHom.toHomUnits
  { toFun := ModularCyclotomicCharacter.toFun n
    map_one' := ModularCyclotomicCharacter.id n
    map_mul' := ModularCyclotomicCharacter.comp n }

lemma spec' (g : L ≃+* L) {t : Lˣ} (ht : t ∈ rootsOfUnity n L) :
    g t = t ^ ((ModularCyclotomicCharacter' L n g) : ZMod
      (Fintype.card { x // x ∈ rootsOfUnity n L })).val :=
  ModularCyclotomicCharacter.toFun_spec' g ht

lemma unique' (g : L ≃+* L) {c : ZMod (Fintype.card { x // x ∈ rootsOfUnity n L })}
    (hc : ∀ t ∈ rootsOfUnity n L, g t = t ^ c.val) :
    c = ModularCyclotomicCharacter' L n g :=
  ModularCyclotomicCharacter.toFun_unique' _ _ _ hc

/-- Given a positive integer `n` and a field `L` containing `n` `n`th roots
of unity, `ModularCyclotomicCharacter n` is a multiplicative homomorphism from the
automorphisms of `L` to `(ℤ/nℤ)ˣ`. It is uniquely characterised by the property that
`g(ζ)=ζ^(ModularCyclotomicCharacter n g)` for `g` an automorphism of `L` and `ζ` any `n`th root
of unity. -/
noncomputable def ModularCyclotomicCharacter {n : ℕ+}
    (hn : Fintype.card { x // x ∈ rootsOfUnity n L } = n) :
    (L ≃+* L) →* (ZMod n)ˣ :=
  (Units.mapEquiv <| (ZMod.ringEquivCongr hn).toMulEquiv).toMonoidHom.comp
  (ModularCyclotomicCharacter' L n)

namespace ModularCyclotomicCharacter

variable {n : ℕ+} (hn : Fintype.card { x // x ∈ rootsOfUnity n L } = n)

lemma spec (g : L ≃+* L) {t : Lˣ} (ht : t ∈ rootsOfUnity n L) :
    g t = t ^ ((ModularCyclotomicCharacter L hn g) : ZMod n).val := by
  rw [toFun_spec' g ht]
  congr 1
  exact (ZMod.ringEquivCongr_val _ _).symm

lemma unique (g : L ≃+* L) {c : ZMod n}  (hc : ∀ t ∈ rootsOfUnity n L, g t = t ^ c.val) :
    c = ModularCyclotomicCharacter L hn g := by
  change c = (ZMod.ringEquivCongr hn) (toFun n g)
  rw [← toFun_unique' n g (ZMod.ringEquivCongr hn.symm c)
    (fun t ht ↦ by rw [hc t ht, ZMod.ringEquivCongr_val]), ← ZMod.ringEquivCongr_symm hn,
    RingEquiv.apply_symm_apply]

end ModularCyclotomicCharacter

variable {L}

/-- The relationship between `IsPrimitiveRoot.autToPow` and
`ModularCyclotomicCharacter`. Note that `IsPrimitiveRoot.autToPow`
needs an explicit root of unity, and also an auxiliary "base ring" `R`. -/
lemma IsPrimitiveRoot.autToPow_eq_ModularCyclotomicCharacter (n : ℕ+)
    (R : Type*) [CommRing R] [Algebra R L] {μ : L} (hμ : IsPrimitiveRoot μ n) (g : L ≃ₐ[R] L) :
    hμ.autToPow R g = ModularCyclotomicCharacter L hμ.card_rootsOfUnity g := by
  ext
  apply ZMod.val_injective
  apply hμ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  simpa [autToPow_spec R hμ g, ModularCyclotomicCharacter', ModularCyclotomicCharacter,
    ZMod.ringEquivCongr_val] using ModularCyclotomicCharacter.toFun_spec'' g hμ
