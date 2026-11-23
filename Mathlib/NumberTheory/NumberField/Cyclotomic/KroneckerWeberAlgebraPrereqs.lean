/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.StickelbergerPrereqs

/-!
# Algebraic prerequisites for the Kronecker-Weber theorem

This file gathers results on groups, ideals, cotangent spaces and fractional ideals that are used
in the proof of the Kronecker-Weber theorem in
`Mathlib.NumberTheory.NumberField.Cyclotomic.KroneckerWeber`.
-/

@[expose] public section

section

/-- Version of `ClassGroup.mk_eq_mk` for any fraction field `K` of `R`. -/
theorem ClassGroup.mk_eq_mk' {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] {I J : (FractionalIdeal (nonZeroDivisors R) K)ˣ} :
    ClassGroup.mk K I = ClassGroup.mk K J ↔ ∃ x : Kˣ, I * toPrincipalIdeal R K x = J := by
  rw [← inv_mul_eq_one (a := mk K I), ← map_inv, ← map_mul, mk_eq_one_iff,
    FractionalIdeal.isPrincipal_iff]
  simp_rw [← eq_inv_mul_iff_mul_eq (b := I), ← MonoidHom.mem_range, mem_principal_ideals_iff,
    eq_comm]

end

section

open Function nonZeroDivisors in
/-- The map of fraction fields induced by an injective `algebraMap A B` is `algebraMap K L`. -/
@[simp]
theorem IsFractionRing.map_algebraMap_apply {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [CommRing K] [Algebra A K] [IsFractionRing A K] [CommRing L] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    (hj : Injective (algebraMap A B)) (x : K) :
    map hj x = algebraMap K L x :=
  RingHom.congr_fun (IsLocalization.ringHom_ext A⁰ <| RingHom.ext fun a ↦ by
    simp [map, ← IsScalarTower.algebraMap_apply]) x

/-- Analogue of `IsPrimitiveRoot.pow` for `orderOf`: if `orderOf x = a * b` then
`orderOf (x ^ a) = b`. -/
theorem orderOf_pow_of_orderOf_eq_mul {G : Type*} [Monoid G] {x : G} {a b : ℕ}
    (hn : 0 < orderOf x) (h : orderOf x = a * b) : orderOf (x ^ a) = b := by
  have ha : a ≠ 0 := left_ne_zero_of_mul (h ▸ hn.ne')
  rw [orderOf_pow_of_dvd ha ⟨b, h⟩, h, Nat.mul_div_cancel_left b (Nat.pos_of_ne_zero ha)]

/-- The group-theoretic heart of the tame Abhyankar lemma: a cyclic group that embeds into a product
`A × B` of finite groups has order dividing `Nat.lcm (Nat.card A) (Nat.card B)`. (A generator maps
  to
some `(a, b)` of order `lcm (orderOf a) (orderOf b)`, and each component order divides the
corresponding cardinality.) -/
theorem Subgroup.card_dvd_lcm_of_isCyclic_of_injective {G A B : Type*} [Group G] [Group A] [Group B]
    [IsCyclic G] {f : G →* A × B} (hf : Function.Injective f) :
    Nat.card G ∣ Nat.lcm (Nat.card A) (Nat.card B) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  rw [← Subgroup.card_top, ← (Subgroup.eq_top_iff' _).mpr hg, Nat.card_zpowers g,
    ← orderOf_injective f hf g, Prod.orderOf]
  exact Nat.lcm_dvd ((_root_.orderOf_dvd_natCard _).trans (Nat.dvd_lcm_left _ _))
      ((_root_.orderOf_dvd_natCard _).trans (Nat.dvd_lcm_right _ _))

/-- In a cyclic group, the lcm of the indices of two subgroups of trivial intersection is the order
of the group. -/
theorem Subgroup.lcm_index_eq_card_of_isCyclic_of_inf_eq_bot {G : Type*} [Group G] [IsCyclic G]
    {H₁ H₂ : Subgroup G} (h : H₁ ⊓ H₂ = ⊥) :
    Nat.lcm H₁.index H₂.index = Nat.card G :=
  dvd_antisymm (Nat.lcm_dvd H₁.index_dvd_card H₂.index_dvd_card) <|
    card_dvd_lcm_of_isCyclic_of_injective (f := (QuotientGroup.mk' H₁).prod (QuotientGroup.mk' H₂))
      (by rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_prod, QuotientGroup.ker_mk',
        QuotientGroup.ker_mk', h])

/-- `subgroupOf` distributes over `⊓` (the general case of `inf_subgroupOf_left`/`_right`); this is
`Subgroup.comap_inf` for the inclusion `C.subtype`. -/
@[to_additive /-- `addSubgroupOf` distributes over `⊓`; this is `AddSubgroup.comap_inf` for the
inclusion `C.subtype`. -/]
theorem Subgroup.subgroupOf_inf {G : Type*} [Group G] (A B C : Subgroup G) :
    (A ⊓ B).subgroupOf C = A.subgroupOf C ⊓ B.subgroupOf C :=
  Subgroup.comap_inf A B C.subtype

/-- `A.subgroupOf B` and `B.subgroupOf A` are isomorphic (both realize `A ⊓ B`). Mathlib only has
`subgroupOfEquivOfLe`; this composes two copies of it through `A ⊓ B`. -/
@[to_additive /-- `A.addSubgroupOf B` and `B.addSubgroupOf A` are isomorphic (both realize
  `A ⊓ B`). -/]
def Subgroup.subgroupOfEquivComm {G : Type*} [Group G] (A B : Subgroup G) :
    A.subgroupOf B ≃* B.subgroupOf A :=
  ((MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_right A B).symm).trans
      (Subgroup.subgroupOfEquivOfLe inf_le_right)).trans
    ((MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_left B A).symm).trans
      (Subgroup.subgroupOfEquivOfLe inf_le_left)).symm

/-- Division-free companion to `Subgroup.card_mul_index`: `d` is the index of `H` iff
`Nat.card H * d = Nat.card G`. -/
@[to_additive AddSubgroup.index_eq_iff_card_mul_eq_card /-- Division-free companion to
`AddSubgroup.card_mul_index`: `d` is the index of `H` iff `Nat.card H * d = Nat.card G`. -/]
theorem Subgroup.index_eq_iff_card_mul_eq_card {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    {d : ℕ} : H.index = d ↔ Nat.card H * d = Nat.card G :=
  ⟨fun h ↦ h ▸ H.card_mul_index,
    fun h ↦ Nat.eq_of_mul_eq_mul_left Nat.card_pos (H.card_mul_index.trans h.symm)⟩

/-- In a commutative group, conjugation acts trivially on a normal subgroup. -/
@[simp]
theorem MulAut.conjNormal_apply_of_isMulCommutative {G : Type*} [Group G] [IsMulCommutative G]
    {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    conjNormal g h = h := by
  rw [Subtype.ext_iff, conjNormal_apply, mul_comm', inv_mul_cancel_left]

section
variable {G R : Type*} [CommGroup G] [Finite G] [CommRing R] [IsDomain R]

/-- The quotient of `G` by the kernel of a character with values in a domain is cyclic. -/
instance (φ : G →* Rˣ) : IsCyclic (G ⧸ φ.ker) :=
  haveI : Finite φ.range := Finite.Set.finite_range _
  isCyclic_of_injective (QuotientGroup.quotientKerEquivRange φ).toMonoidHom (MulEquiv.injective _)

/-- The order of a character `φ : G →* Rˣ` (`R` a domain) equals the cardinality of the quotient of
`G` by its kernel (equivalently, of its cyclic image). -/
theorem MonoidHom.card_quotient_ker_eq_orderOf (φ : G →* Rˣ) :
    Nat.card (G ⧸ φ.ker) = orderOf φ := by
  have : Finite φ.range := Finite.Set.finite_range _
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, ← IsCyclic.exponent_eq_card]
  refine dvd_antisymm (Monoid.exponent_dvd_of_forall_pow_eq_one ?_)
    (orderOf_dvd_iff_pow_eq_one.mpr ?_)
  · rintro ⟨_, ⟨g, rfl⟩⟩
    simp [Subtype.ext_iff, ← MonoidHom.pow_apply]
  · ext g
    simpa [Subtype.ext_iff, Units.ext_iff] using
      Monoid.pow_exponent_eq_one (G := φ.range) ⟨φ g, ⟨g, rfl⟩⟩
end

end

section
open Module

/-- Two modules have the same rank if they are related by an additive isomorphism that is
semilinear with respect to a bijection of the scalars. -/
theorem finrank_eq_of_equiv_equiv {R R' M M₁ : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [Semiring R'] [AddCommMonoid M₁] [Module R' M₁] (i : R → R') (j : M ≃+ M₁)
    (hi : Function.Bijective i) (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    Module.finrank R M = Module.finrank R' M₁ := by
  simpa using! congr_arg Cardinal.toNat <| lift_rank_eq_of_equiv_equiv i j hi hc

/-- The linear map underlying `DistribMulAction.toLinearEquiv R M s` is
`DistribSMul.toLinearMap R M s`. -/
@[simp]
theorem DistribMulAction.coe_toLinearEquiv (R : Type*) {S : Type*} (M : Type*) [Semiring R]
    [AddCommMonoid M] [Module R M] [Group S] [DistribMulAction S M] [SMulCommClass S R M] (s : S) :
    (DistribMulAction.toLinearEquiv R M s : M →ₗ[R] M) = DistribSMul.toLinearMap R M s := rfl

end

section

/-- If `a` and `b` are coprime, then `g` lies in the subgroup generated by `g ^ a` and `g ^ b`
(a special case of `Subgroup.zpowers_zpow_sup`, since `Nat.gcd a b = 1`). -/
theorem mem_sup_zpowers_pow_of_coprime {G : Type*} [Group G] {a b : ℕ}
    (h : Nat.Coprime a b) (g : G) :
    g ∈ Subgroup.zpowers (g ^ a) ⊔ Subgroup.zpowers (g ^ b) := by
  rw [← zpow_natCast g a, ← zpow_natCast g b, Subgroup.zpowers_zpow_sup,
    Int.gcd_natCast_natCast, h.gcd_eq_one, Nat.cast_one, zpow_one]
  exact Subgroup.mem_zpowers g

namespace CommGroup
variable {G : Type*} [CommGroup G]

/-- Auxiliary form of `mem_iSup_primaryComponent_primeFactors`, with `orderOf x` abstracted as `n`,
so that the proof can recurse on the prime-power factorization of `n`. -/
theorem mem_iSup_primaryComponent_primeFactors_aux {n : ℕ} {x : G} (hn : 0 < n)
    (hx : orderOf x = n) :
    x ∈ ⨆ q ∈ n.primeFactors, primaryComponent G q := by
  induction n using Nat.recOnPrimePow generalizing x with
  | zero =>
      exact False.elim <| Nat.not_succ_le_zero 0 hn
  | one => simpa using hx
  | prime_pow_mul m p k hp hpm hk h_ind =>
      have : Fact p.Prime := ⟨hp⟩
      have hm : 0 < m := by
        contrapose! hn
        simp_all
      have hcop : m.Coprime (p ^ k) := by
        rw [Nat.coprime_pow_right_iff hk, Nat.coprime_comm]
        exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
      rw [hcop.symm.primeFactors_mul, Nat.primeFactors_prime_pow (ne_of_gt hk) hp,
        Finset.singleton_union, Finset.iSup_insert]
      refine mem_of_le_of_mem (sup_le_sup ?_ ?_) (mem_sup_zpowers_pow_of_coprime hcop x)
      · refine Subgroup.zpowers_le.mpr ?_
        rw [CommGroup.mem_primaryComponent_iff_orderOf,
          orderOf_pow_of_orderOf_eq_mul (by linarith) (by rwa [mul_comm])]
        exact ⟨k, rfl⟩
      · refine Subgroup.zpowers_le.mpr <| h_ind hm ?_
        rw [orderOf_pow_of_orderOf_eq_mul (by linarith) hx]

/-- A finite-order element lies in the join of the `p`-primary components, for `p` ranging over the
primes dividing its order. -/
theorem mem_iSup_primaryComponent_primeFactors {x : G} (hx : IsOfFinOrder x) :
    x ∈ ⨆ q ∈ (orderOf x).primeFactors, primaryComponent G q :=
  mem_iSup_primaryComponent_primeFactors_aux hx.orderOf_pos rfl

/-- Every element of a torsion commutative group lies in the join of its `p`-primary components. -/
theorem mem_iSup_primaryComponent (hG : IsMulTorsion G) (g : G) :
    g ∈ ⨆ p : Nat.Primes, primaryComponent G p := by
  refine mem_of_le_of_mem ?_ <| mem_iSup_primaryComponent_primeFactors (hG g)
  rw [show ⨆ p : Nat.Primes, primaryComponent G p = ⨆ p ∈ {n | Nat.Prime n}, primaryComponent G p
    from iSup_subtype]
  exact biSup_mono fun h hp ↦ (Nat.mem_primeFactors.mp hp).1

/-- In a torsion commutative group, the primary components generate the whole group. -/
theorem iSup_primaryComponent_eq_top (hG : IsMulTorsion G) :
    ⨆ p : Nat.Primes, primaryComponent G p = ⊤ :=
  eq_top_iff.mpr fun g _ ↦ mem_iSup_primaryComponent hG g

/-- In a torsion commutative group, the elements of prime power order generate the whole group. -/
theorem closure_isPrimePow_orderOf_eq_top (hG : IsMulTorsion G) :
    Subgroup.closure {x : G | IsPrimePow (orderOf x)} = ⊤ := by
  rw [eq_top_iff, ← iSup_primaryComponent_eq_top hG,  iSup_le_iff]
  intro p x hx
  have : Fact p.val.Prime := ⟨p.prop⟩
  obtain ⟨k, hx'⟩ := mem_primaryComponent_iff_orderOf.mp hx
  by_cases hk : 0 < k
  · exact Subgroup.mem_closure_of_mem ⟨p, k, Nat.prime_iff.mp p.prop, hk, hx'.symm⟩
  · simp_all
end CommGroup

end

section
open NumberField

/-- The isomorphism between the semirings of ideals of `R` and `S` induced by a ring isomorphism
`e : R ≃+* S`. -/
@[simps]
def Ideal.mapEquiv {R S F : Type*} [CommSemiring R] [CommSemiring S] [EquivLike F R S]
    [RingHomClass F R S] (e : F) : Ideal R ≃+* Ideal S where
  toFun := Ideal.map e
  invFun := Ideal.comap e
  __ := Ideal.mapHom e
  left_inv _ := by simpa using comap_map_of_bijective _ (EquivLike.bijective e)
  right_inv _ := by simpa using Ideal.map_comap_of_surjective _ (EquivLike.surjective e) _

/-- The image of `I` under `Ideal.mapEquiv e` is `⊥` if and only if `I = ⊥`. -/
theorem Ideal.mapEquiv_eq_bot_iff {R S F : Type*} [CommSemiring R] [CommSemiring S]
    [EquivLike F R S] [RingHomClass F R S] (e : F) (I : Ideal R) :
    I.mapEquiv e = ⊥ ↔ I = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rwa [← RingEquiv.eq_symm_apply, mapEquiv_symm_apply,
    comap_bot_of_injective _ (EquivLike.injective e)] at h

/-- The ideal underlying `equivOfRingEquiv f v` is the image of `v` under `f`. -/
theorem IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv_apply_asIdeal {R S : Type*}
    [CommRing R] [CommRing S] (f : R ≃+* S) (v : HeightOneSpectrum R) :
    (equivOfRingEquiv f v).asIdeal = v.asIdeal.map f := by
  simp only [equivOfRingEquiv_apply, ← RingEquiv.toRingHom_eq_coe, comap_asIdeal]
  exact Ideal.comap_symm f

/-- Every height one prime of `R` lies below a height one prime of `S`. -/
theorem IsDedekindDomain.HeightOneSpectrum.under_surjective {R S : Type*} [CommRing R]
    [CommRing S] [IsDedekindDomain R] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S]
    [Module.IsTorsionFree R S] :
    Function.Surjective
      (HeightOneSpectrum.under R : HeightOneSpectrum S → HeightOneSpectrum R) := by
  intro v
  obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := S) v.asIdeal
  exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
    HeightOneSpectrum.ext <| by simp [under_asIdeal, (Ideal.liesOver_iff _ _).mp hQ']⟩

/-- For a maximal ideal `I`, `R ⧸ I` is already its own fraction field, so the canonical map to
the residue field `κ(I) = ResidueField R_I` of the localization is an isomorphism. -/
noncomputable def Ideal.residueFieldEquiv {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal] :
    R ⧸ I ≃+* I.ResidueField :=
  RingEquiv.ofBijective _ I.bijective_algebraMap_quotient_residueField

/-- The isomorphism `Ideal.residueFieldEquiv` maps the class of `x` to the image of `x`. -/
@[simp]
theorem Ideal.residueFieldEquiv_mk {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal] (x : R) :
    I.residueFieldEquiv (Ideal.Quotient.mk I x) = algebraMap R I.ResidueField x := rfl

open Pointwise in
/-- The pointwise action of `a` on an ideal is its image under the ring isomorphism given by `a`. -/
theorem Ideal.pointwise_smul_def' {M R : Type*} [Group M] [CommSemiring R] [MulSemiringAction M R]
    {a : M} (S : Ideal R) :
    a • S = mapEquiv (MulSemiringAction.toRingEquiv M R a) S := rfl

/-- Let `w` be a prime of `S` above a nonzero prime `v` of `R`. The multiplicity of `w` in the
extension of an ideal `I` is the ramification index of `w` times the multiplicity of `v` in `I`. -/
theorem Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul' {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] [IsDedekindDomain S] [IsDedekindDomain R]
    [FaithfulSMul R S] {v : Ideal R} {w : Ideal S} (I : Ideal R) (hv : v ≠ ⊥) [w.IsPrime]
    (hw : w ≠ ⊥) [w.LiesOver v] :
    emultiplicity w (map (algebraMap R S) I) = w.ramificationIdx R * emultiplicity v I := by
  have := isPrime_of_liesOver w v
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx v w hv]
  by_cases hI : I = ⊥
  · rw [hI, map_bot, ← zero_eq_bot, ← zero_eq_bot, emultiplicity_zero_right,
    emultiplicity_zero_right, ENat.mul_top]
    simp only [ne_eq, Nat.cast_eq_zero]
    apply ramificationIdx'_ne_zero (map_ne_bot_of_ne_bot hv) ‹_›
    rw [map_le_iff_le_comap, over_def w v]
  · exact emultiplicity_map_eq_ramificationIdx'_mul hI
      (irreducible_iff_prime.mpr ((prime_iff_isPrime hv).mpr ‹_›))
      (irreducible_iff_prime.mpr ((prime_iff_isPrime hw).mpr ‹_›)) hw

/-- Version of `Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul'` for
`multiplicity`. -/
theorem Ideal.IsDedekindDomain.multiplicity_map_eq_ramificationIdx_mul {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] [IsDedekindDomain S] [IsDedekindDomain R]
    [FaithfulSMul R S] {v : Ideal R} {w : Ideal S} (I : Ideal R) (hv : v ≠ ⊥) [w.IsPrime]
    (hw : w ≠ ⊥) [w.LiesOver v] :
    multiplicity w (map (algebraMap R S) I) = w.ramificationIdx R * multiplicity v I := by
  by_cases hI : I = ⊥
  · simp [hI]
  have := isPrime_of_liesOver w v
  have h := emultiplicity_map_eq_ramificationIdx_mul' I hv hw
  rw [(FiniteMultiplicity.of_not_isUnit (isUnit_iff.not.mpr IsPrime.ne_top')
      (map_ne_bot_of_ne_bot hI)).emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_not_isUnit (isUnit_iff.not.mpr IsPrime.ne_top')
      hI).emultiplicity_eq_multiplicity] at h
  exact mod_cast h

/-- Version of `Ideal.IsDedekindDomain.multiplicity_map_eq_ramificationIdx_mul` with the prime
below `w` written as `under R w`. -/
theorem Ideal.IsDedekindDomain.ramificationIdx_mul_multiplicity_under_eq {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] [IsDedekindDomain S] [IsDedekindDomain R]
    [FaithfulSMul R S] [Algebra.IsIntegral R S] {w : Ideal S} [w.IsPrime] (hw : w ≠ ⊥)
    {I : Ideal R} :
    w.ramificationIdx R * multiplicity (under R w) I = multiplicity w (map (algebraMap R S) I) :=
  (multiplicity_map_eq_ramificationIdx_mul I (under_ne_bot R hw) hw).symm

open Pointwise in
/-- The image of an ideal under a group element is `⊥` if and only if the ideal is `⊥`. -/
@[simp]
theorem Ideal.smul_eq_bot_iff {M : Type*} {R : Type*} [Group M] [Semiring R] [MulSemiringAction M R]
    {m : M} {I : Ideal R} : m • I = ⊥ ↔ I = ⊥ := by
  rw [smul_eq_iff_eq_inv_smul, smul_bot]

open Pointwise in
/-- An element of the stabilizer of `I` preserves `I`. -/
theorem Ideal.smul_mem_of_mem_stabilizer {M R : Type*} [Group M] [CommRing R]
    [MulSemiringAction M R] (I : Ideal R) (σ : MulAction.stabilizer M I) {x : R} (hx : x ∈ I) :
    σ • x ∈ I := by
  nth_rewrite 1 [← MulAction.mem_stabilizer_iff.mp σ.prop]
  exact smul_mem_pointwise_smul σ x I hx

open Pointwise in
/-- An element of the stabilizer of `I` preserves `I ^ k`. -/
theorem Ideal.smul_mem_pow_of_mem_stabilizer {M R : Type*} [Group M] [CommRing R]
    [MulSemiringAction M R] (I : Ideal R) (σ : MulAction.stabilizer M I) {x : R} {k : ℕ}
    (hx : x ∈ I ^ k) : σ • x ∈ I ^ k := by
  nth_rewrite 1 [← MulAction.mem_stabilizer_iff.mp σ.prop, ← smul_pow']
  exact smul_mem_pointwise_smul σ x _ hx

/-- Ideal version of `AddSubgroup.subgroupOf_inertia`: the inertia of `I` in a subgroup `H ≤ G` is
the restriction to `H` of the inertia in `G`. -/
theorem Ideal.subgroupOf_inertia {R : Type*} [Ring R] (I : Ideal R) {G : Type*} [Group G]
    [MulAction G R] (H : Subgroup G) : (I.inertia G).subgroupOf H = I.inertia H :=
  AddSubgroup.subgroupOf_inertia I.toAddSubgroup H

namespace Ideal

section dvd_finrank
variable {A : Type*} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]
  (B : Type*) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Module.Flat A B]
  [FaithfulSMul A B] (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
  [IsGaloisGroup G A B]

include G in
/-- The ramification index of `p` in a Galois extension divides the degree of the extension. -/
theorem ramificationIdxIn_dvd_finrank : p.ramificationIdxIn B ∣ Module.finrank A B := by
  rw [← IsGaloisGroup.card_eq_finrank' G,
    ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G]
  exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
end dvd_finrank
end Ideal

end

section
open Module
open IsLocalization.AtPrime IsLocalRing
variable {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal]
local notation3 "R_I" => Localization.AtPrime I

/-- The natural map `I ⧸ I ^ 2 → 𝔪 ⧸ 𝔪 ^ 2` induced by `algebraMap R R_I`, landing directly in
`CotangentSpace R_I`, built as `Submodule.mapQ` of `algebraMap R R_I` corestricted to
`maximalIdeal R_I` (`to_map_mem_maximal_iff`). It is `R`-linear (the `R`-action on the target
factors through `algebraMap`), with apply lemma
`cotangentMap (toCotangent x) = toCotangent ⟨algebraMap x, _⟩`. -/
noncomputable def Ideal.cotangentMap : I.Cotangent →ₗ[R] CotangentSpace R_I :=
  let g := Submodule.mapQ (I • ⊤) (maximalIdeal R_I • ⊤)
    ((algebraMap R R_I).toSemilinearMap.restrict
      (fun x hx ↦ (to_map_mem_maximal_iff R_I I x).mpr hx)) (fun x hx ↦ by
        refine Submodule.smul_induction_on hx (fun a ha _ _ ↦ ?_) (fun _ _ ↦ add_mem)
        rw [Submodule.mem_comap, map_smulₛₗ]
        exact Submodule.smul_mem_smul ((to_map_mem_maximal_iff R_I I a).mpr ha) Submodule.mem_top)
  { toAddHom := g.toAddHom
    map_smul' := fun r c ↦ (map_smulₛₗ g r c).trans (algebraMap_smul _ r (g c)) }

/-- The map `Ideal.cotangentMap` is linear for the action of `R ⧸ I` through `R`. -/
theorem cotangentMap_mk_smul (r : R) (x : I.Cotangent) :
    I.cotangentMap (Ideal.Quotient.mk I r • x) = r • I.cotangentMap x :=
  LinearMap.map_smul I.cotangentMap r x

/-- The map `Ideal.cotangentMap` sends the class of `x` to the class of its image in `R_I`. -/
@[simp]
theorem Ideal.cotangentMap_toCotangent (x : I) :
    I.cotangentMap (I.toCotangent x)
      = (maximalIdeal R_I).toCotangent
        ⟨algebraMap R R_I x, (to_map_mem_maximal_iff R_I I x).mpr x.property⟩ := rfl

/-- **Injectivity** (kernel `I ^ 2`): `cotangentMap (toCotangent x) = 0 ↔ algebraMap x ∈ 𝔪 ^ 2 ↔
x ∈ I ^ 2` (`under_maximalIdeal_pow`). -/
theorem Ideal.cotangentMap_injective : Function.Injective I.cotangentMap := by
  refine (injective_iff_map_eq_zero _).mpr fun a ha ↦ ?_
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective a
  rw [cotangentMap_toCotangent, toCotangent_eq_zero] at ha
  rwa [toCotangent_eq_zero, ← under_maximalIdeal_pow I R_I 2, mem_under]

/-- **Surjectivity**: a class in `𝔪 ⧸ 𝔪 ^ 2` is `toCotangent ⟨y, _⟩` with `y ∈ 𝔪`; pulling the
class of `y` back along `R ⧸ I ^ 2 ≃ Rₚ ⧸ 𝔪 ^ 2` (`equivQuotMaximalIdealPow`) gives `a ∈ R` with
`algebraMap a ≡ y` mod `𝔪 ^ 2` (so the same cotangent class) and `algebraMap a ∈ 𝔪` (so `a ∈ I`). -/
theorem Ideal.cotangentMap_surjective :
    Function.Surjective I.cotangentMap := by
  intro z
  obtain ⟨⟨y, hy⟩, rfl⟩ := (maximalIdeal R_I).toCotangent_surjective z
  obtain ⟨a, ha⟩ := Quotient.mk_surjective ((equivQuotMaximalIdealPow I R_I 2).symm y)
  replace ha : Quotient.mk (maximalIdeal R_I ^ 2) (algebraMap R R_I a)
      = Quotient.mk (maximalIdeal R_I ^ 2) y := by
    rw [← equivQuotMaximalIdealPow_apply_mk I R_I 2 a, ha, AlgEquiv.apply_symm_apply]
  refine ⟨I.toCotangent ⟨a, ?_⟩, ?_⟩
  · rw [← to_map_mem_maximal_iff R_I I, ← mk_mem_cotangentIdeal, ha]
    exact mk_mem_cotangentIdeal.mpr hy
  · simpa [cotangentMap_toCotangent, toCotangent_eq, ← Quotient.mk_eq_mk_iff_sub_mem]

/-- The cotangent line `I ⧸ I ^ 2` is intrinsic to the local ring at `I`: it is additively
isomorphic to the cotangent space of `R_I`, as `AddEquiv.ofBijective` of `cotangentMap`. -/
noncomputable def Ideal.cotangentEquivCotangentSpace : I.Cotangent ≃+ CotangentSpace R_I :=
  AddEquiv.ofBijective I.cotangentMap.toAddMonoidHom
    ⟨I.cotangentMap_injective, I.cotangentMap_surjective⟩

/-- The isomorphism `Ideal.cotangentEquivCotangentSpace` is given by `Ideal.cotangentMap`. -/
@[simp]
theorem Ideal.cotangentEquivCotangentSpace_apply (z : I.Cotangent) :
    I.cotangentEquivCotangentSpace z = I.cotangentMap z := rfl

/-- `Ideal.cotangentEquivCotangentSpace` is semilinear over the residue-field identification
`Ideal.residueFieldEquiv : R ⧸ I ≃+* κ(I)`: `cotangentMap` is `R`-linear, and `R` acts on
`CotangentSpace R_I` through `κ(I)`. -/
theorem Ideal.cotangentEquivCotangentSpace_smul (c : R ⧸ I) (x : I.Cotangent) :
    I.cotangentEquivCotangentSpace (c • x)
      = I.residueFieldEquiv c • I.cotangentEquivCotangentSpace x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  simp only [cotangentEquivCotangentSpace_apply, cotangentMap_mk_smul, residueFieldEquiv_mk,
    IsScalarTower.algebraMap_apply R R_I I.ResidueField, algebraMap_smul]

/-- If the localization `R_I` of `R` at a maximal ideal `I` is a discrete valuation ring, then the
cotangent space `I ⧸ I ^ 2` is a one-dimensional vector space over the residue field `R ⧸ I` (its
cotangent line). This is a local statement: only the local ring at `I` matters. -/
theorem Ideal.finrank_cotangent_eq_one [IsDomain R] [IsDiscreteValuationRing R_I] :
    finrank (R ⧸ I) I.Cotangent = 1 := by
  rw [finrank_eq_of_equiv_equiv I.residueFieldEquiv I.cotangentEquivCotangentSpace
    I.residueFieldEquiv.bijective I.cotangentEquivCotangentSpace_smul]
  exact IsLocalRing.finrank_CotangentSpace_eq_one R_I

section Action

namespace Ideal
open scoped Pointwise
variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [Group M] [MulSemiringAction M R]

/-- The stabilizer of `I` acts on the cotangent space `I.Cotangent` -/
instance : SMul (MulAction.stabilizer M I) I.Cotangent where
  smul m v :=
    Submodule.mapQ (I • ⊤) (I • ⊤)
      ((MulSemiringAction.toRingHom M R (m : M)).toSemilinearMap.restrict
        (fun x hx ↦ Ideal.smul_mem_of_mem_stabilizer I m hx))
        (fun x hx ↦ by
          rw [Submodule.mem_smul_top_iff, smul_eq_mul, ← pow_two] at hx
          simp only [Submodule.mem_comap, Submodule.mem_smul_top_iff,
            smul_eq_mul, ← pow_two]
          exact Ideal.smul_mem_pow_of_mem_stabilizer I m hx) v

/-- An element of the stabilizer of `I` acts on the class of `x` by acting on `x`. -/
theorem smul_toCotangent (m : MulAction.stabilizer M I) (x : I) :
    m • I.toCotangent x = I.toCotangent ⟨m • x, I.smul_mem_of_mem_stabilizer m x.prop⟩ := rfl

/-- The stabilizer of `I` acts additively on the cotangent space `I.Cotangent` -/
instance : DistribMulAction (MulAction.stabilizer M I) I.Cotangent where
  mul_smul m n v := by
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective v
    simp [smul_toCotangent, smul_smul]
  one_smul v := by
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective v
    simp [smul_toCotangent]
  smul_zero m := by
    rw [← LinearMap.map_zero I.toCotangent, smul_toCotangent, toCotangent_eq]
    simp
  smul_add m v w := by
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective v
    obtain ⟨y, rfl⟩ := I.toCotangent_surjective w
    simp [← map_add, smul_toCotangent]

/-- The stabilizer of `I` acts on the residue ring `R ⧸ I`. -/
instance : SMul (MulAction.stabilizer M I) (R ⧸ I) where
  smul m x := Ideal.quotientMap I (MulSemiringAction.toRingHom M R (m : M))
    (fun _ hy ↦ Ideal.smul_mem_of_mem_stabilizer I m hy) x

/-- An element of the stabilizer of `I` acts on the class of `x` by acting on `x`. -/
theorem stabilizer_smul_mk (m : MulAction.stabilizer M I) (x : R) :
    m • Ideal.Quotient.mk I x = Ideal.Quotient.mk I (m • x) := rfl

/-- The stabilizer of `I` acts on the residue ring `R ⧸ I` by ring automorphisms. -/
instance : MulSemiringAction (MulAction.stabilizer M I) (R ⧸ I) where
  one_smul q := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp [stabilizer_smul_mk]
  mul_smul m n q := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp [stabilizer_smul_mk, mul_smul]
  smul_zero m := by
    rw [← map_zero (Ideal.Quotient.mk I), stabilizer_smul_mk, smul_zero]
  smul_add m q r := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp [stabilizer_smul_mk, ← map_add, smul_add]
  smul_one m := by rw [← map_one (Ideal.Quotient.mk I), stabilizer_smul_mk, smul_one]
  smul_mul m q r := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp [stabilizer_smul_mk, ← map_mul]

/-- The stabilizer action on `R ⧸ I` is compatible with the `R`-algebra structure:
`g • (r • c) = (g • r) • (g • c)`. -/
instance : SMulDistribClass (MulAction.stabilizer M I) R (R ⧸ I) where
  smul_distrib_smul g r s := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective s
    simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, stabilizer_smul_mk, ← map_mul]

/-- The cotangent action is semilinear over the residue action. -/
theorem stabilizer_smul_smul (g : MulAction.stabilizer M I) (c : R ⧸ I) (v : I.Cotangent) :
    g • (c • v) = (g • c) • (g • v) := by
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective v
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [stabilizer_smul_mk, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul, ← map_smul,
    smul_toCotangent, smul_toCotangent, algebraMap_smul, ← map_smul, toCotangent_eq]
  simp

/-- An inertia element acts trivially on the residue ring `R ⧸ I`. -/
theorem inertia_smul_residue (τ : I.inertia (MulAction.stabilizer M I)) (c : R ⧸ I) :
    (τ : MulAction.stabilizer M I) • c = c := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [stabilizer_smul_mk, Ideal.Quotient.eq]
  exact τ.prop x

/-- The inertia action on the cotangent space is `R ⧸ I`-linear: it commutes with the residue
scalar action. This makes `DistribMulAction.toModuleAut (R ⧸ I) I.Cotangent` an `R ⧸ I`-linear
action of the inertia group (a replacement for `cotangentInertiaAction`). -/
instance : SMulCommClass (I.inertia (MulAction.stabilizer M I)) (R ⧸ I) I.Cotangent where
  smul_comm τ c v := by
    rw [MulAction.subgroup_smul_def, stabilizer_smul_smul, inertia_smul_residue,
      ← MulAction.subgroup_smul_def]
end Ideal
end Action

end

section

/-- The numerator of a nonzero fractional ideal is nonzero. -/
theorem FractionalIdeal.num_ne_bot_of_ne_zero {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*}
    [CommRing P] [Algebra R P] [IsDomain R] [Module.IsTorsionFree R P] (hS : 0 ∉ S)
    {I : FractionalIdeal S P} (hI : I ≠ 0) :
    I.num ≠ ⊥ :=
  (zero_of_num_eq_bot hS).mt hI

namespace IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise
variable {G R : Type*} [Group G] [CommRing R] [MulSemiringAction G R]

/-- A group acting on `R` by ring automorphisms acts on the height one primes of `R`. -/
instance : MulAction G (HeightOneSpectrum R) where
  smul g v := ⟨g • v.asIdeal, inferInstance, by simpa [Ideal.smul_eq_bot_iff] using v.ne_bot⟩
  one_smul v := HeightOneSpectrum.ext (one_smul G v.asIdeal)
  mul_smul g h v := HeightOneSpectrum.ext (mul_smul g h v.asIdeal)

/-- The ideal underlying `g • v` is `g • v.asIdeal`. -/
@[simp]
theorem smul_asIdeal (g : G) (v : HeightOneSpectrum R) : (g • v).asIdeal = g • v.asIdeal := rfl

/-- The action of `g` on height one primes is `equivOfRingEquiv` of the ring isomorphism given
by `g`. -/
theorem smul_eq_equivOfRingEquiv (g : G) (v : HeightOneSpectrum R) :
    g • v = equivOfRingEquiv (MulSemiringAction.toRingEquiv G R g) v := by
  apply HeightOneSpectrum.ext
  rw [smul_asIdeal, equivOfRingEquiv_apply_asIdeal, Ideal.pointwise_smul_def', Ideal.mapEquiv_apply]
end IsDedekindDomain.HeightOneSpectrum

section count
open scoped nonZeroDivisors
open IsDedekindDomain HeightOneSpectrum FractionalIdeal Associates UniqueFactorizationMonoid
variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- The `v`-adic valuation of an ideal `J` is the multiplicity of `v` in `J`. -/
theorem FractionalIdeal.count_coe_eq_multiplicity (J : Ideal R) :
    count K v J = multiplicity v.asIdeal J := by
  obtain rfl | hJ := eq_or_ne J 0
  · simp [FractionalIdeal.count_zero]
  rw [count_coeIdeal K v hJ, Ideal.count_associates_factors_eq hJ v.isPrime v.ne_bot,
    count_normalizedFactors_eq_multiplicity hJ]

/-- The `v`-adic valuation of `I * J⁻¹`, for nonzero ideals `I` and `J`, is the difference of the
multiplicities of `v` in `I` and `J`. -/
theorem FractionalIdeal.count_coe_mul_inv_eq_multiplicity_sub {I J : Ideal R} (hI : I ≠ 0)
    (hJ : J ≠ 0) :
    count K v (I * (J : FractionalIdeal R⁰ K)⁻¹) =
      multiplicity v.asIdeal I - multiplicity v.asIdeal J := by
  rw [count_mul K v (coeIdeal_ne_zero.mpr hI) (inv_ne_zero (coeIdeal_ne_zero.mpr hJ)), count_inv,
    count_coe_eq_multiplicity, count_coe_eq_multiplicity, sub_eq_add_neg]

/-- The `v`-adic valuation of a nonzero fractional ideal `I` is the difference of the
multiplicities of `v` in `I.num` and in the ideal spanned by `I.den`. -/
theorem FractionalIdeal.count_eq_multiplicity_num_sub {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    count K v I =
      multiplicity v.asIdeal I.num - multiplicity v.asIdeal (Ideal.span {(I.den : R)}) := by
  rw [← count_coe_mul_inv_eq_multiplicity_sub K v (num_eq_zero_iff.not.mpr hI) (by simp),
    coeIdeal_span_singleton, ← den_mul_self_eq_num', mul_comm, inv_mul_cancel_left₀ (by simp)]

/-- Two nonzero fractional ideals are equal if and only if they have the same valuation at every
height one prime. -/
theorem FractionalIdeal.eq_iff_count_eq {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I = J ↔ ∀ v : HeightOneSpectrum R, count K v I = count K v J := by
  refine ⟨fun h _ ↦ h ▸ rfl, fun h ↦ ?_⟩
  rw [← finprod_heightOneSpectrum_factorization' K hI,
    ← finprod_heightOneSpectrum_factorization' K hJ]
  simp_rw [h]
end count

section CountExtended
open Ideal IsDedekindDomain nonZeroDivisors
variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [Algebra.IsIntegral R S] (K L : Type*) [Field K] [Field L] [Algebra R K]
  [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]

/-- The `w`-adic valuation of the extension of a fractional ideal `I` is the ramification index of
`w` times the valuation of `I` at the prime below `w`. -/
theorem FractionalIdeal.count_extendedHom [Module.IsTorsionFree R S] (w : HeightOneSpectrum S)
    (I : FractionalIdeal R⁰ K) :
    count L w (extendedHom L S I) = w.asIdeal.ramificationIdx R * count K (w.under R) I := by
  by_cases hI : I = 0
  · simp [hI, count_zero]
  have h' : Ideal.map (algebraMap R S) (span {↑I.den}) ≠ 0 := by simp [map_ne_bot_of_ne_bot]
  rw [FractionalIdeal.count_eq_multiplicity_num_sub _ _ hI, HeightOneSpectrum.under_asIdeal,
    mul_sub, ← Nat.cast_mul, ← Nat.cast_mul, ramificationIdx_mul_multiplicity_under_eq w.ne_bot,
    ramificationIdx_mul_multiplicity_under_eq w.ne_bot,
    ← FractionalIdeal.count_coe_mul_inv_eq_multiplicity_sub L _ _ h']
  · congr
    rw [eq_mul_inv_iff_mul_eq₀ (by simpa using h'), ← extendedHom_coeIdeal_eq_map _ S (K := K),
      ← map_mul, mul_comm, coeIdeal_span_singleton, den_mul_self_eq_num', extendedHom'_apply,
      extended_coeIdeal_eq_map]
  · apply map_ne_bot_of_ne_bot
    exact FractionalIdeal.num_ne_bot_of_ne_zero zero_notMem_nonZeroDivisors hI
end CountExtended

section FractionalIdealCount
open scoped nonZeroDivisors
open IsDedekindDomain HeightOneSpectrum
variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S]
  (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
  [IsFractionRing S L]

/-- The extension of a fractional ideal `I` is the image of its numerator divided by the image of
its denominator. -/
theorem FractionalIdeal.extended_eq_map_num_mul_inv {f : R →+* S} (hf : R⁰ ≤ S⁰.comap f)
    (I : FractionalIdeal R⁰ K) :
    I.extended L hf = (I.num.map f) * (Ideal.span {f I.den} : FractionalIdeal S⁰ L)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq₀, mul_comm]
  · rw [← Set.image_singleton, ← Ideal.map_span, ← extended_coeIdeal_eq_map (K := K) L hf,
      ← extended_mul, coeIdeal_span_singleton, den_mul_self_eq_num', extended_coeIdeal_eq_map]
  · rw [coeIdeal_ne_zero, ne_eq, Ideal.span_singleton_eq_bot, ← ne_eq]
    exact nonZeroDivisors.ne_zero (hf I.den.property)

/-- The image of a fractional ideal under `ringEquivOfRingEquiv` is its extension. -/
theorem FractionalIdeal.ringEquivOfRingEquiv_eq_extended [IsDomain R] (f : R ≃+* S)
    (I : FractionalIdeal R⁰ K) :
    ringEquivOfRingEquiv K L f I =
      I.extended L (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (f : R →+* S)
        fun _ _ h ↦ f.injective h) := by
  rw [← coeToSubmodule_inj, coeToSubmodule_extended_eq_span, ringEquivOfRingEquiv_apply,
    coeToSubmodule_mk, ← Submodule.span_eq (Submodule.map _ _), Submodule.map_coe]
  rfl

/-- The image of a fractional ideal `I` under `ringEquivOfRingEquiv` is the image of its numerator
divided by the image of its denominator. -/
theorem FractionalIdeal.ringEquivOfRingEquiv_eq_map_num_mul_inv [IsDomain R] (f : R ≃+* S)
    (I : FractionalIdeal R⁰ K) :
    ringEquivOfRingEquiv K L f I =
      (I.num.map f) * (Ideal.span {f I.den} : FractionalIdeal S⁰ L)⁻¹ := by
  rw [ringEquivOfRingEquiv_eq_extended, extended_eq_map_num_mul_inv, Ideal.map_coe,
    RingEquiv.coe_toRingHom]

/-- The valuation of `ringEquivOfRingEquiv K L f I` at the image of `v` is the valuation of `I`
at `v`. -/
theorem FractionalIdeal.count_ringEquivOfRingEquiv [IsDedekindDomain R] (f : R ≃+* S)
    (v : HeightOneSpectrum R) (I : FractionalIdeal R⁰ K) :
    count L (equivOfRingEquiv f v) (ringEquivOfRingEquiv K L f I) = count K v I := by
  by_cases hI : I = 0
  · simp [hI, count_zero]
  rw [ringEquivOfRingEquiv_eq_map_num_mul_inv, ← Ideal.mapEquiv_apply, count_mul, count_inv,
    count_coe_eq_multiplicity, count_coe_eq_multiplicity, equivOfRingEquiv_apply_asIdeal,
    ← Set.image_singleton, ← Ideal.map_span, ← Ideal.mapEquiv_apply, ← Ideal.mapEquiv_apply,
    multiplicity_map_eq, multiplicity_map_eq, Int.add_neg_eq_sub,
    ← count_eq_multiplicity_num_sub _ _ hI]
  · rw [coeIdeal_ne_zero, ne_eq, Ideal.mapEquiv_eq_bot_iff]
    exact num_eq_zero_iff.not.mpr hI
  · simp

/-- The action of `g` on fractional ideals is `ringEquivOfRingEquiv` of the ring isomorphism given
by `g`. -/
theorem FractionalIdeal.smul_eq_ringEquivOfRingEquiv [IsDedekindDomain R] {G : Type*} [Group G]
    [MulSemiringAction G R] (g : G) (I : FractionalIdeal R⁰ K) :
    g • I = ringEquivOfRingEquiv K K (MulSemiringAction.toRingEquiv G R g) I := by
  rw [FractionalIdeal.smul_def, ringEquivOfRingEquiv_eq_extended]
  rfl

/-- The valuation of `σ • I` at `σ • v` is the valuation of `I` at `v`. -/
theorem FractionalIdeal.count_smul [IsDedekindDomain R] {G : Type*} [Group G]
    [MulSemiringAction G R] (v : HeightOneSpectrum R) (I : FractionalIdeal R⁰ K) (σ : G) :
    count K (σ • v) (σ • I) = count K v I := by
  rw [smul_eq_ringEquivOfRingEquiv, smul_eq_equivOfRingEquiv, count_ringEquivOfRingEquiv]
end FractionalIdealCount

end
