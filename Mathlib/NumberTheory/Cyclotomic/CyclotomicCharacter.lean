/-
Copyright (c) 2023 Hanneke Wiersema. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Hanneke Wiersema, Andrew Yang
-/
import Mathlib.Algebra.Ring.Aut
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.FieldTheory.KrullTopology

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

## TODO

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

variable (n : ℕ) [NeZero n]

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
noncomputable def ModularCyclotomicCharacter.aux (g : L ≃+* L) (n : ℕ) [NeZero n] : ℤ :=
  (rootsOfUnity.integer_power_of_ringEquiv n g).choose

-- the only thing we know about `ModularCyclotomicCharacter_aux g n`
theorem ModularCyclotomicCharacter.aux_spec (g : L ≃+* L) (n : ℕ) [NeZero n] :
    ∀ t : rootsOfUnity n L, g (t : Lˣ) = (t ^ (ModularCyclotomicCharacter.aux g n) : Lˣ) :=
  (rootsOfUnity.integer_power_of_ringEquiv n g).choose_spec

theorem ModularCyclotomicCharacter.pow_dvd_aux_pow_sub_aux_pow
    (g : L ≃+* L) (p : ℕ) [Fact p.Prime] [∀ i, HasEnoughRootsOfUnity L (p ^ i)]
    {i k : ℕ} (hi : k ≤ i) : (p : ℤ) ^ k ∣ aux g (p ^ i) - aux g (p ^ k) := by
  obtain ⟨i, rfl⟩ := exists_add_of_le hi
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (p ^ (k + i))
  have h := hζ.pow (a := p ^ i) (Nat.pos_of_neZero _) (Nat.pow_add' _ _ _)
  have h_unit : (h.isUnit (Nat.pos_of_neZero _)).unit =
      (hζ.isUnit (Nat.pos_of_neZero _)).unit ^ (p ^ i) := by ext; rfl
  have H₁ := aux_spec g (p ^ (k + i))
    ⟨_, (hζ.isUnit_unit (Nat.pos_of_neZero _)).mem_rootsOfUnity⟩
  have H₂ := aux_spec g (p ^ k)
    ⟨_, (h.isUnit_unit (Nat.pos_of_neZero _)).mem_rootsOfUnity⟩
  simp only [IsUnit.unit_spec, map_pow] at H₁ H₂
  rw [H₁, ← Units.val_pow_eq_pow_val, ← Units.ext_iff, h_unit, ← div_eq_one] at H₂
  simp only [← zpow_natCast, ← zpow_mul, div_eq_mul_inv, ← zpow_sub] at H₂
  rw [(hζ.isUnit_unit (Nat.pos_of_neZero _)).zpow_eq_one_iff_dvd, mul_comm, ← mul_sub] at H₂
  conv_lhs at H₂ => rw [Nat.pow_add', Nat.cast_mul]
  rwa [mul_dvd_mul_iff_left (by simp [NeZero.ne p]), Nat.cast_pow] at H₂

/-- If `g` is a ring automorphism of `L`, and `n : ℕ+`, then
  `ModularCyclotomicCharacter.toFun n g` is the `j : ZMod d` such that `g(ζ)=ζ^j` for all
  `n`'th roots of unity. Here `d` is the number of `n`th roots of unity in `L`. -/
noncomputable def ModularCyclotomicCharacter.toFun (n : ℕ) [NeZero n] (g : L ≃+* L) :
    ZMod (Fintype.card (rootsOfUnity n L)) :=
  ModularCyclotomicCharacter.aux g n

namespace ModularCyclotomicCharacter

local notation "χ₀" => ModularCyclotomicCharacter.toFun

/-- The formula which characterises the output of `ModularCyclotomicCharacter g n`. -/
theorem toFun_spec (g : L ≃+* L) {n : ℕ} [NeZero n] (t : rootsOfUnity n L) :
    g (t : Lˣ) = (t ^ (χ₀ n g).val : Lˣ) := by
  rw [ModularCyclotomicCharacter.aux_spec g n t, ← zpow_natCast, ModularCyclotomicCharacter.toFun,
    ZMod.val_intCast, ← Subgroup.coe_zpow]
  exact Units.ext_iff.1 <| SetCoe.ext_iff.2 <|
    zpow_eq_zpow_emod _ pow_card_eq_one (G := rootsOfUnity n L)

theorem toFun_spec' (g : L ≃+* L) {n : ℕ} [NeZero n] {t : Lˣ} (ht : t ∈ rootsOfUnity n L) :
    g t = t ^ (χ₀ n g).val :=
  toFun_spec g ⟨t, ht⟩

theorem toFun_spec'' (g : L ≃+* L) {n : ℕ} [NeZero n] {t : L} (ht : IsPrimitiveRoot t n) :
    g t = t ^ (χ₀ n g).val :=
  toFun_spec' g (SetLike.coe_mem ht.toRootsOfUnity)

/-- If g(t)=t^c for all roots of unity, then c=χ(g). -/
theorem toFun_unique (g : L ≃+* L) (c : ZMod (Fintype.card (rootsOfUnity n L)))
    (hc : ∀ t : rootsOfUnity n L, g (t : Lˣ) = (t ^ c.val : Lˣ)) : c = χ₀ n g := by
  apply IsCyclic.ext Nat.card_eq_fintype_card (fun ζ ↦ ?_)
  specialize hc ζ
  suffices ((ζ ^ c.val : Lˣ) : L) = (ζ ^ (χ₀ n g).val : Lˣ) by exact_mod_cast this
  rw [← toFun_spec g ζ, hc]

theorem toFun_unique' (g : L ≃+* L) (c : ZMod (Fintype.card (rootsOfUnity n L)))
    (hc : ∀ t ∈ rootsOfUnity n L, g t = t ^ c.val) : c = χ₀ n g :=
  toFun_unique n g c (fun ⟨_, ht⟩ ↦ hc _ ht)

lemma id : χ₀ n (RingEquiv.refl L) = 1 := by
  refine (toFun_unique n (RingEquiv.refl L) 1 <| fun t ↦ ?_).symm
  have : 1 ≤ Fintype.card { x // x ∈ rootsOfUnity n L } := Fin.size_positive'
  obtain (h | h) := this.lt_or_eq
  · have := Fact.mk h
    simp [ZMod.val_one]
  · have := Fintype.card_le_one_iff_subsingleton.mp h.ge
    obtain rfl : t = 1 := Subsingleton.elim t 1
    simp

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
def ModularCyclotomicCharacter' (n : ℕ) [NeZero n] :
    (L ≃+* L) →* (ZMod (Fintype.card { x // x ∈ rootsOfUnity n L }))ˣ := MonoidHom.toHomUnits
  { toFun := ModularCyclotomicCharacter.toFun n
    map_one' := ModularCyclotomicCharacter.id n
    map_mul' := ModularCyclotomicCharacter.comp n }

lemma ModularCyclotomicCharacter'.spec' (g : L ≃+* L) {t : Lˣ} (ht : t ∈ rootsOfUnity n L) :
    g t = t ^ ((ModularCyclotomicCharacter' L n g) : ZMod
      (Fintype.card { x // x ∈ rootsOfUnity n L })).val :=
  ModularCyclotomicCharacter.toFun_spec' g ht

lemma ModularCyclotomicCharacter'.unique' (g : L ≃+* L)
    {c : ZMod (Fintype.card { x // x ∈ rootsOfUnity n L })}
    (hc : ∀ t ∈ rootsOfUnity n L, g t = t ^ c.val) :
    c = ModularCyclotomicCharacter' L n g :=
  ModularCyclotomicCharacter.toFun_unique' _ _ _ hc

/-- Given a positive integer `n` and a field `L` containing `n` `n`th roots
of unity, `ModularCyclotomicCharacter n` is a multiplicative homomorphism from the
automorphisms of `L` to `(ℤ/nℤ)ˣ`. It is uniquely characterised by the property that
`g(ζ)=ζ^(ModularCyclotomicCharacter n g)` for `g` an automorphism of `L` and `ζ` any `n`th root
of unity. -/
noncomputable def ModularCyclotomicCharacter {n : ℕ} [NeZero n]
    (hn : Fintype.card { x // x ∈ rootsOfUnity n L } = n) :
    (L ≃+* L) →* (ZMod n)ˣ :=
  (Units.mapEquiv <| (ZMod.ringEquivCongr hn).toMulEquiv).toMonoidHom.comp
  (ModularCyclotomicCharacter' L n)

namespace ModularCyclotomicCharacter

variable {n : ℕ} [NeZero n] (hn : Fintype.card { x // x ∈ rootsOfUnity n L } = n)

lemma spec (g : L ≃+* L) {t : Lˣ} (ht : t ∈ rootsOfUnity n L) :
    g t = t ^ ((ModularCyclotomicCharacter L hn g) : ZMod n).val := by
  rw [toFun_spec' g ht]
  congr 1
  exact (ZMod.ringEquivCongr_val _ _).symm

lemma unique (g : L ≃+* L) {c : ZMod n} (hc : ∀ t ∈ rootsOfUnity n L, g t = t ^ c.val) :
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
lemma IsPrimitiveRoot.autToPow_eq_ModularCyclotomicCharacter (n : ℕ) [NeZero n]
    (R : Type*) [CommRing R] [Algebra R L] {μ : L} (hμ : IsPrimitiveRoot μ n) (g : L ≃ₐ[R] L) :
    hμ.autToPow R g = ModularCyclotomicCharacter L hμ.card_rootsOfUnity g := by
  ext
  apply ZMod.val_injective
  apply hμ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  simpa only [autToPow_spec R hμ g, ModularCyclotomicCharacter, RingEquiv.toMulEquiv_eq_coe,
    MulEquiv.toMonoidHom_eq_coe, ModularCyclotomicCharacter', MonoidHom.coe_comp, MonoidHom.coe_coe,
    Function.comp_apply, Units.coe_mapEquiv, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk,
    OneHom.coe_mk, RingEquiv.coe_toMulEquiv, ZMod.ringEquivCongr_val, AlgEquiv.coe_ringEquiv]
    using ModularCyclotomicCharacter.toFun_spec'' g hμ

/-

## The p-adic theory

-/

open ModularCyclotomicCharacter in
open scoped Classical in
/-- The underlying function of the cyclotomic character. See `CyclotomicCharacter`. -/
noncomputable def CyclotomicCharacter.toFun (p : ℕ) [Fact p.Prime] (g : L ≃+* L) : ℤ_[p] :=
  if H : ∀ (i : ℕ), ∃ ζ : L, IsPrimitiveRoot ζ (p ^ i) then
    haveI (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
    PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
      (aux g <| p ^ ·) _ fun i ↦ pow_dvd_aux_pow_sub_aux_pow g p i.le_succ)
  else 1

namespace CyclotomicCharacter

local notation "χ" => CyclotomicCharacter.toFun

variable (p : ℕ) [Fact p.Prime] (g : L ≃+* L) [∀ i, HasEnoughRootsOfUnity L (p ^ i)]

open ModularCyclotomicCharacter in
theorem toFun_apply :
    CyclotomicCharacter.toFun p g =
      PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
        (aux g <| p ^ ·) _ fun i ↦ pow_dvd_aux_pow_sub_aux_pow g p i.le_succ) :=
  dif_pos fun _ ↦ HasEnoughRootsOfUnity.exists_primitiveRoot _ _

open ModularCyclotomicCharacter in
theorem toZModPow_toFun (n : ℕ) :
    (χ p g).toZModPow n =
      (ModularCyclotomicCharacter _ (Fintype.card_eq_nat_card.trans
        (HasEnoughRootsOfUnity.natCard_rootsOfUnity L (p ^ n))) g).val := by
  rw [toFun_apply]
  refine (PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (aux g <| p ^ ·) _ (fun i ↦
    pow_dvd_aux_pow_sub_aux_pow g p i.le_succ) n).trans ?_
  simp [ModularCyclotomicCharacter, ModularCyclotomicCharacter', ModularCyclotomicCharacter.toFun]

theorem toFun_spec (g : L ≃+* L) {n : ℕ} (t : rootsOfUnity (p ^ n) L) :
    g (t : Lˣ) = t.1 ^ ((χ p g).toZModPow n).val := by
  rw [toZModPow_toFun, ← ModularCyclotomicCharacter.spec (ht := t.2)]

end CyclotomicCharacter

variable (L) in
/--
Suppose `L` is a domain containing all `pⁱ`-th primitive roots with `p` a (rational) prime.
If `g` is a ring automorphism of `L`, then `CyclotomicCharacter L p g` is the unique `j : ℤₚ` such
that `g(ζ) = ζ ^ (j mod pⁱ)` for all `pⁱ`'th roots of unity `ζ`.

Note: This is the trivial character when `L` does not contain all `pⁱ`-th primitive roots.
-/
noncomputable def CyclotomicCharacter (p : ℕ) [Fact p.Prime] :
    (L ≃+* L) →* ℤ_[p]ˣ := .toHomUnits
  { toFun g := CyclotomicCharacter.toFun p g
    map_one' := by
      by_cases H : ∀ (i : ℕ), ∃ ζ : L, IsPrimitiveRoot ζ (p ^ i)
      · haveI (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
        refine PadicInt.ext_of_toZModPow.mp fun n ↦ ?_
        simp [CyclotomicCharacter.toZModPow_toFun]
      · simp [CyclotomicCharacter.toFun, dif_neg H]
    map_mul' f g := by
      by_cases H : ∀ (i : ℕ), ∃ ζ : L, IsPrimitiveRoot ζ (p ^ i)
      · haveI (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
        refine PadicInt.ext_of_toZModPow.mp fun n ↦ ?_
        simp [CyclotomicCharacter.toZModPow_toFun]
      · simp [CyclotomicCharacter.toFun, dif_neg H] }

theorem CyclotomicCharacter.spec (p : ℕ) [Fact p.Prime] {n : ℕ}
    [∀ i, HasEnoughRootsOfUnity L (p ^ i)] (g : L ≃+* L) (t : L) (ht : t ^ p ^ n = 1) :
    g t = t ^ ((CyclotomicCharacter L p g).val.toZModPow n).val :=
  toFun_spec p g (rootsOfUnity.mkOfPowEq _ ht)

theorem CyclotomicCharacter.toZModPow (p : ℕ) [Fact p.Prime] {n : ℕ}
    [∀ i, HasEnoughRootsOfUnity L (p ^ i)] (g : L ≃+* L) :
    (CyclotomicCharacter L p g).val.toZModPow n =
      (ModularCyclotomicCharacter _ (Fintype.card_eq_nat_card.trans
        (HasEnoughRootsOfUnity.natCard_rootsOfUnity L (p ^ n))) g).val :=
  toZModPow_toFun _ _ _

open IntermediateField in
lemma CyclotomicCharacter.continuous (p : ℕ) [Fact p.Prime]
    (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Continuous ((CyclotomicCharacter L p).comp (MulSemiringAction.toRingAut (L ≃ₐ[K] L) L)) := by
  by_cases H : ∀ (i : ℕ), ∃ ζ : L, IsPrimitiveRoot ζ (p ^ i); swap
  · simp only [CyclotomicCharacter, CyclotomicCharacter.toFun, dif_neg H, MonoidHom.coe_comp]
    exact continuous_const (y := 1)
  haveI (i) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
  choose ζ hζ using H
  refine Continuous.of_coeHom_comp ?_
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one, (galGroupBasis K L).nhds_one_hasBasis.tendsto_iff
    (Metric.nhds_basis_ball (α := ℤ_[p]) (x := 1))]
  intro ε hε
  obtain ⟨k, hk', hk⟩ : ∃ k : ℕ, k ≠ 0 ∧ p ^ (-k : ℤ) < ε := by
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
    exact ⟨k + 1, by simp, lt_of_le_of_lt (by gcongr <;> simp [‹Fact p.Prime›.1.one_le]) hk⟩
  refine ⟨_, ⟨_, ⟨(K⟮ζ k⟯), adjoin.finiteDimensional ?_, rfl⟩, rfl⟩, ?_⟩
  · exact ((hζ k).isIntegral (Nat.pos_of_neZero _)).tower_top
  · intro σ hσ
    refine lt_of_le_of_lt ?_ hk
    dsimp
    rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
      RingHom.mem_ker, map_sub, map_one, CyclotomicCharacter.toZModPow,
      sub_eq_zero, eq_comm]
    apply ModularCyclotomicCharacter.unique
    intro t ht
    obtain ⟨i, hi, rfl⟩ := ((hζ k).isUnit_unit (Nat.pos_of_neZero _)).eq_pow_of_mem_rootsOfUnity ht
    rw [ZMod.val_one'', pow_one]
    · exact hσ ⟨ζ k ^ i, pow_mem (mem_adjoin_simple_self K (ζ k)) _⟩
    · exact (one_lt_pow₀ ‹Fact p.Prime›.1.one_lt hk').ne'
