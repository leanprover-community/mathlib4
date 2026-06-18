/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Invariant.Basic

/-!
# Predicate for Galois Groups

Given an action of a group `G` on an extension of fields `L/K`, we introduce a predicate
`IsGaloisGroup G K L` saying that `G` acts faithfully on `L` with fixed field `K`. In particular,
we do not assume that `L` is an algebraic extension of `K`.

## Implementation notes

We actually define `IsGaloisGroup G A B` for extensions of rings `B/A`, with the same definition
(faithful action on `B` with fixed ring `A`). This definition turns out to axiomatize a common
setup in algebraic number theory where a Galois group `Gal(L/K)` acts on an extension of subrings
`B/A` (e.g., rings of integers). In particular, there are theorems in algebraic number theory that
naturally assume `[IsGaloisGroup G A B]` and whose statements would otherwise require assuming
`(K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L]` (along with predicates relating
`K` and `L` to the rings `A` and `B`) despite `K` and `L` not appearing in the conclusion.

Unfortunately, this definition of `IsGaloisGroup G A B` for extensions of rings `B/A` is
nonstandard and clashes with other notions such as the étale fundamental group. In particular, if
`G` is finite and `A` is integrally closed, then  `IsGaloisGroup G A B` is equivalent to `B/A`
being integral and the fields of fractions `Frac(B)/Frac(A)` being Galois with Galois group `G`
(see `IsGaloisGroup.iff_isFractionRing`), rather than `B/A` being étale for instance.

But in the absence of a more suitable name, the utility of the predicate `IsGaloisGroup G A B` for
extensions of rings `B/A` seems to outweigh these terminological issues.
-/

@[expose] public section

open Module

section CommRing

variable (G A A' B : Type*) [Group G] [CommSemiring A] [Semiring B] [Algebra A B]
  [MulSemiringAction G B]

/-- `G` is a Galois group for `L/K` if the action of `G` on `L` is faithful with fixed field `K`.
In particular, we do not assume that `L` is an algebraic extension of `K`.

See the implementation notes in this file for the meaning of this definition in the case of rings.
-/
class IsGaloisGroup where
  faithful : FaithfulSMul G B
  commutes : SMulCommClass G A B
  isInvariant : Algebra.IsInvariant A B G

variable {G A B} in
theorem IsGaloisGroup.of_mulEquiv [hG : IsGaloisGroup G A B] {H : Type*} [Group H]
    [MulSemiringAction H B] (e : H ≃* G) (he : ∀ h (x : B), (e h) • x = h • x) :
    IsGaloisGroup H A B where
  faithful := ⟨fun h ↦ e.injective <| hG.faithful.eq_of_smul_eq_smul <| by simpa only [he]⟩
  commutes := ⟨fun x a b ↦ by simpa [he] using hG.commutes.smul_comm (e x) a b⟩
  isInvariant := ⟨fun b h ↦
    have he' : ∀ (g : G) (x : B), e.symm g • x = g • x := fun g x ↦ by simp [← he]
    hG.isInvariant.isInvariant b (fun g ↦ by simpa [he'] using h (e.symm g))⟩

variable {G A B} in
theorem IsGaloisGroup.iff_of_mulEquiv {H : Type*} [Group H] [MulSemiringAction H B]
    (e : H ≃* G) (he : ∀ h (x : B), e h • x = h • x) :
    IsGaloisGroup H A B ↔ IsGaloisGroup G A B := by
  refine ⟨fun h ↦ h.of_mulEquiv e.symm fun g x ↦ ?_, fun h ↦ h.of_mulEquiv e he⟩
  rw [← he, e.apply_symm_apply]

variable {G A B} in
@[simp]
theorem IsGaloisGroup.top_iff : IsGaloisGroup (⊤ : Subgroup G) A B ↔ IsGaloisGroup G A B :=
  iff_of_mulEquiv Subgroup.topEquiv fun _ _ ↦ rfl

instance [IsGaloisGroup G A B] : IsGaloisGroup (⊤ : Subgroup G) A B :=
  IsGaloisGroup.top_iff.mpr ‹_›

theorem IsGaloisGroup.of_algEquiv [hG : IsGaloisGroup G A B] (B' : Type*) [Semiring B']
    [Algebra A B'] [MulSemiringAction G B'] (e : B ≃ₐ[A] B')
    (he : ∀ (g : G) (x : B), e (g • x) = g • (e x)) :
    IsGaloisGroup G A B' where
  faithful := ⟨fun h ↦ hG.faithful.eq_of_smul_eq_smul fun b ↦ by simpa [← he] using h (e b)⟩
  commutes := ⟨fun g a b' ↦ by
    have h' {x'} : e.symm (g • x') = g • e.symm x' := by
      apply e.injective
      simp [he]
    apply e.symm.injective
    simpa [h', map_smul] using hG.commutes.smul_comm g a (e.symm b')⟩
  isInvariant := ⟨fun x' hx' ↦ by
    obtain ⟨a, ha⟩ := hG.isInvariant.isInvariant (e.symm x') (fun g ↦ by
      apply e.injective
      simp [he, hx'])
    exact ⟨a, by rw [← e.commutes, ha, AlgEquiv.apply_symm_apply]⟩⟩

theorem IsGaloisGroup.of_ringEquiv [hG : IsGaloisGroup G A B] [CommSemiring A'] [Algebra A' B]
    (e : A ≃+* A') (he : ∀ a, algebraMap A' B (e a) = algebraMap A B a) :
    IsGaloisGroup G A' B where
  faithful := hG.faithful
  commutes := ⟨by
    intro g a' b
    obtain ⟨a, rfl⟩ : ∃ a, e a = a' := e.surjective a'
    rw [Algebra.smul_def, Algebra.smul_def, he, ← Algebra.smul_def, ← Algebra.smul_def]
    exact hG.commutes.smul_comm g a b⟩
  isInvariant := ⟨by
    intro b h
    obtain ⟨a, ha⟩ := hG.isInvariant.isInvariant b h
    exact ⟨e a, by rw [he, ha]⟩⟩

attribute [instance low] IsGaloisGroup.commutes IsGaloisGroup.isInvariant

variable {C : Type*} [CommSemiring C] [Algebra C B]

variable {G} in
protected theorem Subgroup.smul_algebraMap {H : Subgroup G} [SMulCommClass H C B] {g : G}
    (hg : g ∈ H) (x : C) :
    g • algebraMap C B x = algebraMap C B x :=
  smul_algebraMap (⟨g, hg⟩ : H) x

theorem IsGaloisGroup.smul_mem_of_normal (N : Subgroup G) [hN : N.Normal]
    [hC : IsGaloisGroup N C B] (g : G) (x : C) :
    g • algebraMap C B x ∈ Set.range (algebraMap C B) := by
  apply hC.isInvariant.isInvariant (g • algebraMap C B x)
  intro n
  rw [← inv_smul_eq_iff, Subgroup.smul_def, ← mul_smul, ← mul_smul]
  exact Subgroup.smul_algebraMap B (hN.conj_mem' n n.prop g) x

@[deprecated (since := "2026-05-28")] alias smul_eq_self := Subgroup.smul_algebraMap
@[deprecated (since := "2026-05-28")] alias smul_mem_of_normal := IsGaloisGroup.smul_mem_of_normal

variable [hA : IsGaloisGroup G A B] [FaithfulSMul A B]

/--
If `B/A` is Galois with Galois group `G`, then `A` is isomorphic to the subring of elements of `B`
fixed by `G`.
-/
@[simps apply_coe]
noncomputable def IsGaloisGroup.ringEquivFixedPoints :
    A ≃+* FixedPoints.subsemiring B G where
  toFun x := ⟨algebraMap A B x, fun _ ↦ by rw [smul_algebraMap]⟩
  invFun x := (hA.isInvariant.isInvariant x x.prop).choose
  map_mul' _ _ := by simp [Subtype.ext_iff]
  map_add' _ _ := by simp [Subtype.ext_iff]
  left_inv _ := by simp
  right_inv x := by simpa [Subtype.ext_iff] using (hA.isInvariant.isInvariant x x.prop).choose_spec

@[simp]
theorem IsGaloisGroup.algebraMap_ringEquivFixedPoints_symm_apply (x : FixedPoints.subsemiring B G) :
    algebraMap A B ((ringEquivFixedPoints G A B).symm x) = x :=
 (hA.isInvariant.isInvariant x x.prop).choose_spec

variable [CommSemiring A'] [Algebra A' B] [FaithfulSMul A' B] [hA' : IsGaloisGroup G A' B]

/--
If `B/A` and `B/A'` are Galois with the same Galois group, then `A ≃+* A'`.
-/
noncomputable def IsGaloisGroup.ringEquiv :
    A ≃+* A' :=
  (ringEquivFixedPoints G A B).trans (ringEquivFixedPoints G A' B).symm

@[simp]
theorem IsGaloisGroup.algebraMap_ringEquiv_apply (x : A) :
    algebraMap A' B (IsGaloisGroup.ringEquiv G A A' B x) = algebraMap A B x := by
  simp [ringEquiv]

@[simp]
theorem IsGaloisGroup.algebraMap_ringEquiv_symm_apply (x : A') :
    algebraMap A B ((IsGaloisGroup.ringEquiv G A A' B).symm x) = algebraMap A' B x := by
  simp [ringEquiv]

end CommRing

section Field

variable (G A B K L : Type*) [Group G] [CommRing A] [CommRing B] [MulSemiringAction G B]
  [Algebra A B] [Field K] [Field L] [Algebra K L] [Algebra A K] [Algebra B L] [Algebra A L]
  [IsFractionRing A K] [IsFractionRing B L] [IsScalarTower A K L] [IsScalarTower A B L]
  [MulSemiringAction G L] [SMulDistribClass G B L]

instance [IsGaloisGroup G A B] : IsGaloisGroup G (algebraMap A B).range B where
  faithful := IsGaloisGroup.faithful A
  commutes := ⟨fun g ⟨a', ⟨a, ha⟩⟩ b ↦ by simp [Subring.smul_def, ← ha]⟩
  isInvariant := ⟨fun b hb ↦ by
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) b hb
    exact ⟨⟨algebraMap A B a, ⟨a, rfl⟩⟩, ha⟩⟩

/-- `IsGaloisGroup` for rings implies `IsGaloisGroup` for their fraction fields. -/
theorem IsGaloisGroup.to_isFractionRing_of_isIntegral
    [Algebra.IsIntegral A B] [hGAB : IsGaloisGroup G A B] :
    IsGaloisGroup G K L where
  faithful :=
    have := hGAB.faithful
    IsFractionRing.faithfulSMul G B L
  commutes := IsFractionRing.smulCommClass G A B K L
  isInvariant := IsFractionRing.isInvariant_of_isIntegral G A B K L

/-- `IsGaloisGroup` for rings implies `IsGaloisGroup` for their fraction fields. -/
theorem IsGaloisGroup.to_isFractionRing [Finite G] [hGAB : IsGaloisGroup G A B] :
    IsGaloisGroup G K L :=
  have := hGAB.isInvariant.isIntegral
  IsGaloisGroup.to_isFractionRing_of_isIntegral G A B K L

/-- If `B` is an integral extension of an integrally closed domain `A`, then `IsGaloisGroup` for
their fraction fields implies `IsGaloisGroup` for these rings. -/
theorem IsGaloisGroup.of_isFractionRing [hGKL : IsGaloisGroup G K L]
    [IsIntegrallyClosed A] [Algebra.IsIntegral A B] : IsGaloisGroup G A B := by
  have hc (a : A) : (algebraMap K L) (algebraMap A K a) = (algebraMap B L) (algebraMap A B a) := by
    simp_rw [← IsScalarTower.algebraMap_apply]
  refine ⟨⟨fun h ↦ ?_⟩, ⟨fun g x y ↦ IsFractionRing.injective B L ?_⟩, ⟨fun x h ↦ ?_⟩⟩
  · have := hGKL.faithful
    refine eq_of_smul_eq_smul fun (y : L) ↦ ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective B y
    simp only [smul_div₀', ← algebraMap.coe_smul', h]
  · simp [Algebra.smul_def, algebraMap.coe_smul', ← hc]
  · obtain ⟨b, hb⟩ := hGKL.isInvariant.isInvariant (algebraMap B L x)
      (by simpa [← algebraMap.coe_smul'])
    have hx : IsIntegral A (algebraMap B L x) := (Algebra.IsIntegral.isIntegral x).algebraMap
    rw [← hb, isIntegral_algebraMap_iff (algebraMap K L).injective,
      IsIntegrallyClosedIn.isIntegral_iff] at hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, by rwa [hc, IsFractionRing.coe_inj] at hb⟩

/-- If `G` is finite and `A` is integrally closed then `IsGaloisGroup G A B` is equivalent to `B/A`
being integral and the fields of fractions `Frac(B)/Frac(A)` being Galois with Galois group `G`. -/
theorem IsGaloisGroup.iff_isFractionRing [Finite G] [IsIntegrallyClosed A] :
    IsGaloisGroup G A B ↔ Algebra.IsIntegral A B ∧ IsGaloisGroup G K L :=
  ⟨fun h ↦ ⟨h.isInvariant.isIntegral, h.to_isFractionRing G A B K L⟩,
    fun ⟨_, h⟩ ↦ h.of_isFractionRing G A B K L⟩

@[deprecated (since := "2026-04-20")] alias FractionRing.mulSemiringAction_of_isGaloisGroup :=
  IsFractionRing.mulSemiringAction

attribute [local instance] FractionRing.liftAlgebra in
/--
If `G` is finite and `IsGaloisGroup G A B` with `A` and `B` domains, then `G` is also
a Galois group for `FractionRing B / FractionRing A` for the action defined by
`IsFractionRing.mulSemiringAction`.
-/
theorem IsGaloisGroup.toFractionRing [IsDomain A] [IsDomain B] [IsTorsionFree A B] [Finite G]
    [IsGaloisGroup G A B] :
    letI := IsFractionRing.mulSemiringAction G A B (FractionRing A) (FractionRing B)
    IsGaloisGroup G (FractionRing A) (FractionRing B) := by
  let := IsFractionRing.mulSemiringAction G A B (FractionRing A) (FractionRing B)
  have : SMulDistribClass G B (FractionRing B) := ⟨fun g b x ↦ by
    rw [Algebra.smul_def', Algebra.smul_def', smul_mul']
    congr
    exact IsFractionRing.fieldEquivOfAlgEquiv_algebraMap (FractionRing A) _ _ _ b⟩
  apply IsGaloisGroup.to_isFractionRing G A B _ _

open NumberField

instance (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (G : Type*) [Group G] [MulSemiringAction G L] [IsGaloisGroup G K L] :
    IsGaloisGroup G (𝓞 K) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing G (𝓞 K) (𝓞 L) K L

instance (L : Type*) [Field L] [NumberField L]
    (G : Type*) [Group G] [MulSemiringAction G L] [IsGaloisGroup G ℚ L] :
    IsGaloisGroup G ℤ (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing G ℤ (𝓞 L) ℚ L

end Field

variable (G G' K L : Type*) [Group G] [Group G'] [Field K] [Field L] [Algebra K L]
  [MulSemiringAction G L] [MulSemiringAction G' L]

namespace IsGaloisGroup

attribute [instance low] commutes isInvariant

theorem fixedPoints_eq_bot [IsGaloisGroup G K L] :
    FixedPoints.intermediateField G = (⊥ : IntermediateField K L) := by
  rw [eq_bot_iff]
  exact Algebra.IsInvariant.isInvariant

/-- If `G` is a finite Galois group for `L/K`, then `L/K` is a Galois extension. -/
theorem isGalois [Finite G] [IsGaloisGroup G K L] : IsGalois K L := by
  rw [← isGalois_iff_isGalois_bot, ← fixedPoints_eq_bot G]
  exact IsGalois.of_fixed_field L G

/-- If `L/K` is a Galois extension, then `Gal(L/K)` is a Galois group for `L/K`. -/
instance of_isGalois [IsGalois K L] : IsGaloisGroup Gal(L/K) K L where
  faithful := inferInstance
  commutes := inferInstance
  isInvariant := ⟨fun x ↦ (InfiniteGalois.mem_bot_iff_fixed x).mpr⟩

/-- The cardinality of a Galois group equals the degree of the field extension.

See `IsGaloisGroup.card_eq_finrank'` for a ring-theoretic generalization assuming finiteness. -/
theorem card_eq_finrank [IsGaloisGroup G K L] : Nat.card G = Module.finrank K L := by
  rcases fintypeOrInfinite G with _ | hG
  · have : FaithfulSMul G L := faithful K
    rw [← IntermediateField.finrank_bot', ← fixedPoints_eq_bot G, Nat.card_eq_fintype_card]
    exact (FixedPoints.finrank_eq_card G L).symm
  · rw [Nat.card_eq_zero_of_infinite, eq_comm]
    contrapose! hG
    have : FiniteDimensional K L := FiniteDimensional.of_finrank_pos (Nat.zero_lt_of_ne_zero hG)
    exact Finite.of_injective (MulSemiringAction.toAlgAut G K L)
      (fun _ _ ↦ (faithful K).eq_of_smul_eq_smul ∘ DFunLike.ext_iff.mp)

theorem finiteDimensional [Finite G] [IsGaloisGroup G K L] : FiniteDimensional K L :=
  FiniteDimensional.of_finrank_pos (card_eq_finrank G K L ▸ Nat.card_pos)

protected theorem finite (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] [Module.Finite R B]
  [IsDomain B] [MulSemiringAction G B] [IsGaloisGroup G R B] : Finite G := by
  let A : Subring B := (algebraMap R B).range
  let := FractionRing.liftAlgebra A (FractionRing B)
  let := IsFractionRing.mulSemiringAction G A B (FractionRing A) (FractionRing B)
  let : Algebra R A := (algebraMap R B).rangeRestrict.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite A B := Module.Finite.of_restrictScalars_finite R A B
  have := IsGaloisGroup.to_isFractionRing_of_isIntegral G A B (FractionRing A) (FractionRing B)
  apply Nat.finite_of_card_ne_zero
  rw [card_eq_finrank G (FractionRing A) (FractionRing B)]
  exact Module.finrank_pos.ne'

/-- The cardinality of a Galois group of `B/A` equals the rank of `B` as an `A`-module.

See `IsGaloisGroup.card_eq_finrank` a field-theoretic version that does not assume finiteness. -/
theorem card_eq_finrank' (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Finite G]
    [IsDomain B] [FaithfulSMul A B] [MulSemiringAction G B] [IsGaloisGroup G A B] :
    Nat.card G = Module.finrank A B := by
  have := IsDomain.of_faithfulSMul A B
  let := FractionRing.liftAlgebra A (FractionRing B)
  let := IsFractionRing.mulSemiringAction G A B (FractionRing A) (FractionRing B)
  have : Algebra.IsIntegral A B := IsGaloisGroup.isInvariant.isIntegral A B G
  rw [(IsGaloisGroup.toFractionRing G A B).card_eq_finrank,
    Algebra.IsAlgebraic.finrank_of_isFractionRing A (FractionRing A) B (FractionRing B)]

/-- If `G` is a finite Galois group for `L/K`, then `G` is isomorphic to `Gal(L/K)`. -/
@[simps!] noncomputable def mulEquivAlgEquiv [IsGaloisGroup G K L] [Finite G] : G ≃* Gal(L/K) :=
  MulEquiv.ofBijective (MulSemiringAction.toAlgAut G K L) (by
    have := isGalois G K L
    have := finiteDimensional G K L
    rw [Nat.bijective_iff_injective_and_card, card_eq_finrank G K L,
      IsGalois.card_aut_eq_finrank K L]
    exact ⟨fun _ _ ↦ (faithful K).eq_of_smul_eq_smul ∘ DFunLike.ext_iff.mp, rfl⟩)

@[simp]
theorem map_mulEquivAlgEquiv_fixingSubgroup
    [IsGaloisGroup G K L] [Finite G] (F : IntermediateField K L) :
    (fixingSubgroup G (F : Set L)).map (mulEquivAlgEquiv G K L) = F.fixingSubgroup := by
  ext g
  obtain ⟨g, rfl⟩ := (mulEquivAlgEquiv G K L).surjective g
  simp [mem_fixingSubgroup_iff]

/-- If `G` and `G'` are finite Galois groups for `L/K`, then `G` is isomorphic to `G'`.
See `mulEquivCongr` for a more general version. -/
private noncomputable def mulEquivCongr' [IsGaloisGroup G K L] [Finite G]
    [IsGaloisGroup G' K L] [Finite G'] : G ≃* G' :=
  (mulEquivAlgEquiv G K L).trans (mulEquivAlgEquiv G' K L).symm

@[simp]
private theorem mulEquivCongr'_apply_smul [IsGaloisGroup G K L] [Finite G] [IsGaloisGroup G' K L]
    [Finite G'] (g : G) (x : L) : mulEquivCongr' G G' K L g • x = g • x :=
  AlgEquiv.ext_iff.mp ((mulEquivAlgEquiv G' K L).apply_symm_apply (mulEquivAlgEquiv G K L g)) x

attribute [local instance] FractionRing.liftAlgebra in
/-- If `G` and `G'` are finite Galois groups for `B/A` with `B` a domain, then `G` is
isomorphic to `G'`. -/
@[no_expose] noncomputable def mulEquivCongr [Finite G] [Finite G'] (A B : Type*) [CommRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [MulSemiringAction G B]
    [MulSemiringAction G' B] [IsGaloisGroup G A B] [IsGaloisGroup G' A B] :
    G ≃* G' :=
  haveI : IsDomain A := (FaithfulSMul.algebraMap_injective A B).isDomain
  letI K := FractionRing A
  letI L := FractionRing B
  letI : MulSemiringAction G L := IsFractionRing.mulSemiringAction G A B K L
  letI : MulSemiringAction G' L := IsFractionRing.mulSemiringAction G' A B K L
  haveI : IsGaloisGroup G K L := IsGaloisGroup.toFractionRing G A B
  haveI : IsGaloisGroup G' K L := IsGaloisGroup.toFractionRing G' A B
  mulEquivCongr' G G' K L

attribute [local instance] FractionRing.liftAlgebra in
@[simp]
theorem mulEquivCongr_apply_smul [Finite G] [Finite G'] (A B : Type*) [CommRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [MulSemiringAction G B]
    [MulSemiringAction G' B] [IsGaloisGroup G A B] [IsGaloisGroup G' A B] (g : G) (x : B) :
    mulEquivCongr G G' A B g • x = g • x := by
  haveI : IsDomain A := (FaithfulSMul.algebraMap_injective A B).isDomain
  letI K := FractionRing A
  letI L := FractionRing B
  letI : MulSemiringAction G L := IsFractionRing.mulSemiringAction G A B K L
  letI : MulSemiringAction G' L := IsFractionRing.mulSemiringAction G' A B K L
  haveI : IsGaloisGroup G K L := IsGaloisGroup.toFractionRing G A B
  haveI : IsGaloisGroup G' K L := IsGaloisGroup.toFractionRing G' A B
  apply FaithfulSMul.algebraMap_injective B L
  rw [algebraMap.smul', algebraMap.smul']
  exact mulEquivCongr'_apply_smul G G' K L g _

@[simp]
theorem mulEquivCongr_symm_apply_smul [Finite G] [Finite G'] (A B : Type*) [CommRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [MulSemiringAction G B]
    [MulSemiringAction G' B] [IsGaloisGroup G A B] [IsGaloisGroup G' A B] (g : G') (x : B) :
    (mulEquivCongr G G' A B).symm g • x = g • x := by
  rw [← mulEquivCongr_apply_smul G G' A B, MulEquiv.apply_symm_apply]

theorem mulEquivCongr_mapSubgroup_fixingSubgroup (F : Set L) [IsGaloisGroup G K L] [Finite G]
    [IsGaloisGroup G' K L] [Finite G'] :
    (fixingSubgroup G F).map (mulEquivCongr G G' K L) = fixingSubgroup G' F := by
  ext g
  simp [Subgroup.map_equiv_eq_comap_symm, mem_fixingSubgroup_iff]

variable (H H' : Subgroup G) (F F' : IntermediateField K L)

instance (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [MulSemiringAction G S] [hGKL : IsGaloisGroup G R S] :
    IsGaloisGroup H (FixedPoints.subalgebra R S H) S where
  faithful := have := hGKL.faithful; inferInstance
  commutes := inferInstance
  isInvariant := ⟨fun x h ↦ ⟨⟨x, h⟩, rfl⟩⟩

instance subgroup [hGKL : IsGaloisGroup G K L] :
    IsGaloisGroup H (FixedPoints.intermediateField H : IntermediateField K L) L :=
  inferInstanceAs (IsGaloisGroup H (FixedPoints.subalgebra K L H) L)

open IntermediateField in
theorem fixedPoints_of_isGaloisGroup [hGKL : IsGaloisGroup G K L] [hHFL : IsGaloisGroup H F L] :
    FixedPoints.intermediateField H = F := by
  refine IntermediateField.ext_iff.mpr fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := hHFL.isInvariant.isInvariant x hx
    exact a.prop
  · have := congr_arg (restrictScalars K) <| IsGaloisGroup.fixedPoints_eq_bot H F L
    rw [restrictScalars_bot_eq_self] at this
    rwa [← this] at hx

theorem of_fixedPoints_eq [hGKL : IsGaloisGroup G K L] (hF : FixedPoints.intermediateField H = F) :
    IsGaloisGroup H F L := by
  rw [eq_comm] at hF
  convert! IsGaloisGroup.subgroup G K L H

variable {G K L H F} in
theorem subgroup_iff [hGKL : IsGaloisGroup G K L] :
    IsGaloisGroup H F L ↔ FixedPoints.intermediateField H = F :=
  ⟨fun _ ↦ fixedPoints_of_isGaloisGroup G K L H F, fun h ↦ of_fixedPoints_eq G K L H F h⟩

@[simp]
theorem finrank_fixedPoints_eq_card_subgroup [IsGaloisGroup G K L] :
    Module.finrank (FixedPoints.intermediateField H : IntermediateField K L) L = Nat.card H :=
  (card_eq_finrank H (FixedPoints.intermediateField H) L).symm

variable {G K L} in
theorem of_mulEquiv_algEquiv [IsGalois K L] (e : G ≃* Gal(L/K)) (he : ∀ g x, e g x = g • x) :
    IsGaloisGroup G K L := .of_mulEquiv e he

instance fixedPoints [Finite G] [FaithfulSMul G L] :
    IsGaloisGroup G (FixedPoints.subfield G L) L :=
  of_mulEquiv_algEquiv (FixedPoints.toAlgAutMulEquiv _ _) fun _ _ ↦ rfl

instance intermediateField [Finite G] [hGKL : IsGaloisGroup G K L] :
    IsGaloisGroup (fixingSubgroup G (F : Set L)) F L :=
  let e := ((mulEquivAlgEquiv G K L).subgroupMap (fixingSubgroup G (F : Set L))).trans <|
    (MulEquiv.subgroupCongr (map_mulEquivAlgEquiv_fixingSubgroup ..)).trans <|
    IntermediateField.fixingSubgroupEquiv F
  have := hGKL.isGalois
  .of_mulEquiv_algEquiv e fun _ _ ↦ rfl

include K in
/-- If `G` is a Galois group on `L/K` and `L/E/K` is a tower of field extensions,
then the fixing subgroup of the image of `E` in `L` is a Galois group on `L/E`. -/
theorem of_isScalarTower [Finite G] [IsGaloisGroup G K L] (E : Type*) [Field E] [Algebra K E]
    [Algebra E L] [IsScalarTower K E L] :
    IsGaloisGroup (fixingSubgroup G (Set.range (algebraMap E L))) E L := by
  rw [← IsScalarTower.toAlgHom_fieldRange K E L]
  refine IsGaloisGroup.of_ringEquiv _ _ _ L
    (AlgHom.equivFieldRange (IsScalarTower.toAlgHom K E L)).toRingEquiv.symm fun ⟨_, ⟨x, rfl⟩⟩ ↦ ?_
  simp [AlgEquiv.symm_apply_eq, Subtype.ext_iff]

@[simp]
theorem card_fixingSubgroup_eq_finrank [Finite G] [IsGaloisGroup G K L] :
    Nat.card (fixingSubgroup G (F : Set L)) = Module.finrank F L :=
  card_eq_finrank ..

section GaloisCorrespondence

theorem fixingSubgroup_le_of_le (h : F ≤ F') :
    fixingSubgroup G (F' : Set L) ≤ fixingSubgroup G (F : Set L) :=
  fun _ hσ ⟨x, hx⟩ ↦ hσ ⟨x, h hx⟩

section SMulCommClass

variable [SMulCommClass G K L]

@[simp]
theorem fixingSubgroup_bot : fixingSubgroup G ((⊥ : IntermediateField K L) : Set L) = ⊤ := by
  simp [Subgroup.ext_iff, mem_fixingSubgroup_iff, IntermediateField.mem_bot]

@[simp]
theorem fixedPoints_bot :
    (FixedPoints.intermediateField (⊥ : Subgroup G) : IntermediateField K L) = ⊤ := by
  simp [IntermediateField.ext_iff]

theorem le_fixedPoints_iff_le_fixingSubgroup :
    F ≤ FixedPoints.intermediateField H ↔ H ≤ fixingSubgroup G (F : Set L) :=
  ⟨fun h g hg x ↦ h x.2 ⟨g, hg⟩, fun h x hx g ↦ h g.2 ⟨x, hx⟩⟩

theorem fixedPoints_le_of_le (h : H ≤ H') :
    FixedPoints.intermediateField H' ≤ (FixedPoints.intermediateField H : IntermediateField K L) :=
  fun _ hσ ⟨x, hx⟩ ↦ hσ ⟨x, h hx⟩

end SMulCommClass

attribute [local instance] FractionRing.liftAlgebra in
/-- If `K` is the fraction field of `A` and `L` is the fraction field of `B` with `A ⊆ B`,
then for `G` acting on `B` and `L`, the fixing subgroup of `A` in `B` equals the fixing subgroup
of `K` in `L`. -/
theorem fixingSubgroup_range_algebraMap_isFractionRing (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [IsScalarTower A K L]
    [IsScalarTower A B L] [MulSemiringAction G B] [SMulDistribClass G B L] [IsFractionRing A K]
    [IsFractionRing B L] :
    fixingSubgroup G (Set.range (algebraMap A B)) =
      fixingSubgroup G (Set.range (algebraMap K L)) := by
  ext g
  simp only [mem_fixingSubgroup_iff, Set.mem_range]
  refine ⟨?_, ?_⟩
  · rintro h _ ⟨x, rfl⟩
    have {x} : g • (algebraMap A L) x = (algebraMap A L) x := by
      rw [IsScalarTower.algebraMap_apply A B L, ← algebraMap.smul', h _ ⟨x, rfl⟩]
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective A x
    simp only [map_div₀, ← IsScalarTower.algebraMap_apply, smul_div₀', this]
  · rintro h _ ⟨x, rfl⟩
    apply FaithfulSMul.algebraMap_injective B L
    rw [algebraMap.smul']
    apply h
    use algebraMap A K x
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

/-- If `H` is a Galois group on `L/E`, then `H` is also a Galois group on
`L/(IsScalarTower.toAlgHom K E L).fieldRange`. -/
theorem of_toAlgHom_fieldRange (E : Type*) [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L] [IsGaloisGroup H E L] :
    IsGaloisGroup H (IsScalarTower.toAlgHom K E L).fieldRange L :=
  IsGaloisGroup.of_ringEquiv H E ((IsScalarTower.toAlgHom K E L).fieldRange) L
    (IsScalarTower.toAlgHom K E L).equivFieldRange.toRingEquiv fun _ ↦ by simp

section IsGaloisGroup

variable [hGKL : IsGaloisGroup G K L]

-- this can't be a simp-lemma since the left-hand side is not in simp normal form
-- and if the theorem was `fixingSubgroup G Set.univ = ⊥` then `K` couldn't be inferred
theorem fixingSubgroup_top : fixingSubgroup G ((⊤ : IntermediateField K L) : Set L) = ⊥ := by
  have := hGKL.faithful
  ext; simpa [mem_fixingSubgroup_iff, Set.ext_iff] using MulAction.fixedBy_eq_univ_iff_eq_one

@[simp]
theorem fixedPoints_top :
    (FixedPoints.intermediateField (⊤ : Subgroup G) : IntermediateField K L) = ⊥ := by
  convert! IsGaloisGroup.fixedPoints_eq_bot G K L
  ext; simp

/-- The Galois correspondence from intermediate fields to subgroups. -/
noncomputable def intermediateFieldEquivSubgroup [Finite G] :
    IntermediateField K L ≃o (Subgroup G)ᵒᵈ :=
  have := isGalois G K L
  have := finiteDimensional G K L
  IsGalois.intermediateFieldEquivSubgroup.trans <| (mulEquivAlgEquiv G K L).comapSubgroup.dual

@[simp] theorem intermediateFieldEquivSubgroup_apply [Finite G] {F} :
    intermediateFieldEquivSubgroup G K L F = .toDual (fixingSubgroup G (F : Set L)) := rfl

theorem ofDual_intermediateFieldEquivSubgroup_apply [Finite G] {F} :
    (intermediateFieldEquivSubgroup G K L F).ofDual = fixingSubgroup G (F : Set L) := rfl

@[simp] theorem intermediateFieldEquivSubgroup_symm_apply [Finite G] {H} :
    (intermediateFieldEquivSubgroup G K L).symm H = FixedPoints.intermediateField H.ofDual := by
  obtain ⟨H, rfl⟩ := OrderDual.toDual.surjective H
  simp [IntermediateField.ext_iff, intermediateFieldEquivSubgroup,
    (mulEquivAlgEquiv G K L).surjective.forall, -mulEquivAlgEquiv_symm_apply]

theorem intermediateFieldEquivSubgroup_symm_apply_toDual [Finite G] {H} :
    (intermediateFieldEquivSubgroup G K L).symm (.toDual H) = FixedPoints.intermediateField H :=
  intermediateFieldEquivSubgroup_symm_apply ..

@[simp]
theorem fixingSubgroup_fixedPoints [Finite G] :
    fixingSubgroup G ((FixedPoints.intermediateField H : IntermediateField K L) : Set L) = H := by
  rw [← intermediateFieldEquivSubgroup_symm_apply_toDual,
    ← ofDual_intermediateFieldEquivSubgroup_apply,
    OrderIso.apply_symm_apply, OrderDual.ofDual_toDual]

@[simp]
theorem fixedPoints_fixingSubgroup [Finite G] :
    FixedPoints.intermediateField (fixingSubgroup G (F : Set L)) = F := by
  rw [← ofDual_intermediateFieldEquivSubgroup_apply, ← intermediateFieldEquivSubgroup_symm_apply,
    OrderIso.symm_apply_apply]

/-- If `G` acts as a Galois group on `L/K` and the subgroup `H` acts as a Galois group on `L/B`,
then the fixed points of `H` equals the range of `algebraMap B L`. -/
theorem fixedPoints_eq_range_algebraMap [Finite G] (B : Type*)
    [CommSemiring B] [Algebra B L] [IsGaloisGroup H B L] :
    (FixedPoints.intermediateField H : IntermediateField K L) = Set.range (algebraMap B L) := by
  ext
  rw [SetLike.mem_coe, FixedPoints.mem_intermediateField_iff, Set.mem_range]
  refine ⟨IsGaloisGroup.isInvariant.isInvariant _, ?_⟩
  rintro ⟨x, rfl⟩ h
  exact smul_algebraMap h x

include K in
/-- If `G` acts as a Galois group on `L/K` and the subgroup `H` acts as a Galois group on `L/B`,
then the fixing subgroup of `algebraMap B L` inside `G` equals `H`.
See `fixingSubgroup_range_algebraMap` for a more general version. -/
theorem fixingSubgroup_range_algebraMap' [Finite G] (B : Type*) [CommSemiring B] [Algebra B L]
    [IsGaloisGroup H B L] :
    fixingSubgroup G (Set.range (algebraMap B L)) = H := by
  rw [← fixedPoints_eq_range_algebraMap G K L H, fixingSubgroup_fixedPoints]

attribute [local instance] FractionRing.liftAlgebra in
/-- If `G` acts on a domain `C` with `IsGaloisGroup G A C`, and a subgroup `H` acts on `C` with
`IsGaloisGroup H B C`, then the fixing subgroup of `algebraMap B C` equals `H`. -/
theorem fixingSubgroup_range_algebraMap [Finite G] (A B C : Type*) (H : Subgroup G)
    [CommRing A] [CommRing B] [CommRing C] [IsDomain C]
    [Algebra A C] [MulSemiringAction G C] [hGAC : IsGaloisGroup G A C]
    [Algebra B C] [FaithfulSMul B C] [hH : IsGaloisGroup H B C] :
    fixingSubgroup G (Set.range (algebraMap B C)) = H := by
  have : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  let A' : Subring C := (algebraMap A C).range
  let K := FractionRing A'
  let L := FractionRing C
  let : MulSemiringAction G L := IsFractionRing.mulSemiringAction G A' C K L
  have : IsGaloisGroup G K L := IsGaloisGroup.to_isFractionRing G A' C _ _
  have : IsGaloisGroup H (FractionRing B) L := IsGaloisGroup.toFractionRing H B C
  rw [← fixingSubgroup_range_algebraMap' G K L H (FractionRing B)]
  ext g
  simp only [mem_fixingSubgroup_iff, Set.mem_range]
  refine ⟨?_, ?_⟩
  · rintro h _ ⟨x, rfl⟩
    have {x} : g • (algebraMap B L) x = (algebraMap B L) x := by
      rw [IsScalarTower.algebraMap_apply B C L, ← algebraMap.smul', h _ ⟨x, rfl⟩]
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective B x
    simp only [map_div₀, ← IsScalarTower.algebraMap_apply, smul_div₀', this]
  · rintro h _ ⟨x, rfl⟩
    apply FaithfulSMul.algebraMap_injective C L
    rw [algebraMap.smul']
    apply h
    use algebraMap B (FractionRing B) x
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

attribute [local instance] FractionRing.liftAlgebra in
/-- If `G` acts on a domain `C` with `IsGaloisGroup G A C` and `B` is an intermediate domain,
then the fixing subgroup of `algebraMap B C` is a Galois group on
`FractionRing C / FractionRing B`. -/
theorem isGaloisGroup_fixingSubgroup_range_algebraMap [Finite G] (A B C : Type*) [CommRing A]
    [CommRing B] [CommRing C] [IsDomain C] [Algebra A B] [Algebra A C] [Algebra B C]
    [FaithfulSMul B C] [FaithfulSMul A B] [IsScalarTower A B C] [MulSemiringAction G C]
    [IsGaloisGroup G A C] :
    letI : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
    letI : IsDomain A := (FaithfulSMul.algebraMap_injective A B).isDomain
    letI : FaithfulSMul A C := FaithfulSMul.trans A B C
    letI : MulSemiringAction G (FractionRing C) :=
      IsFractionRing.mulSemiringAction G A C (FractionRing A) (FractionRing C)
    IsGaloisGroup (fixingSubgroup G (Set.range (algebraMap B C)))
      (FractionRing B) (FractionRing C) := by
  letI : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  letI : IsDomain A := (FaithfulSMul.algebraMap_injective A B).isDomain
  haveI : FaithfulSMul A C := FaithfulSMul.trans A B C
  letI : MulSemiringAction G (FractionRing C) :=
    IsFractionRing.mulSemiringAction G A C (FractionRing A) (FractionRing C)
  let K := FractionRing A
  let L := FractionRing C
  let F := FractionRing B
  have : IsGaloisGroup G K L := IsGaloisGroup.toFractionRing G A C
  rw [fixingSubgroup_range_algebraMap_isFractionRing G F L]
  exact of_isScalarTower G K L F

open Pointwise in
/-- If `G` is a finite Galois group for `L/K`, `H` is a Galois group for `L/E`, and `E/K` is
Galois, then `H` is a normal subgroup of `G`. -/
theorem normal_of_isGalois (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]
    [Finite G] [IsGaloisGroup H E L] [IsGalois K E] : H.Normal := by
  let F := (IsScalarTower.toAlgHom K E L).fieldRange
  have : IsGalois K F := .of_algEquiv (IsScalarTower.toAlgHom K E L).equivFieldRange
  have hFL : IsGaloisGroup H F L := of_toAlgHom_fieldRange G K L H E
  have := isGalois G K L
  have : Finite Gal(L/K) := Finite.of_equiv _ (mulEquivAlgEquiv G K L).toEquiv
  rw [← fixingSubgroup_fixedPoints G K L H, subgroup_iff.mp hFL,
    ← mulEquivCongr_mapSubgroup_fixingSubgroup Gal(L/K) G K, MulEquiv.normal_map_iff ]
  exact IsGalois.fixingSubgroup_normal_of_isGalois F

end IsGaloisGroup

end GaloisCorrespondence

section Quotient

section Semiring

variable (A B C : Type*) [CommSemiring A] [Semiring C] [Algebra A C] [MulSemiringAction G C]
variable (N : Subgroup G) [CommSemiring B] [Algebra B C]

/-- If `N` is a normal subgroup of `G` and `IsGaloisGroup N B C`, then `G` acts on `B`.
For `g : G` and `x : B`, `g • x` is the unique element of `B` whose image in `C` is
`g • algebraMap B C x`, see `algebraMap_smulOfNormal`. -/
@[implicit_reducible]
noncomputable def smulOfNormal [N.Normal] [IsGaloisGroup N B C] : SMul G B where
  smul g x := (smul_mem_of_normal G C N g x).choose

@[simp]
theorem algebraMap_smulOfNormal [N.Normal] [IsGaloisGroup N B C] (g : G) (x : B) :
    letI := smulOfNormal G B C
    algebraMap B C (g • x) = g • algebraMap B C x :=
  (smul_mem_of_normal G C N g x).choose_spec

/-- If `N` is normal and `IsGaloisGroup N B C`, the action `smulOfNormal G B C` satisfies
`SMulDistribClass G B C`. -/
instance smulDistribClass_smulOfNormal [N.Normal] [IsGaloisGroup N B C] :
    letI := smulOfNormal G B C
    SMulDistribClass G B C :=
  let := smulOfNormal G B C
  ⟨fun g b c ↦ by simp [Algebra.smul_def]⟩

variable [FaithfulSMul B C]

/-- If `N` is a normal subgroup of `G` and `IsGaloisGroup N B C`, then `G` acts on `B` as a
`MulSemiringAction`, via the action defined in `smulOfNormal`. -/
@[implicit_reducible]
noncomputable def mulSemiringActionOfNormal [IsGaloisGroup N B C] [N.Normal] :
    MulSemiringAction G B := by
  let : SMul G B := smulOfNormal G B C N
  have : SMulDistribClass G B C := smulDistribClass_smulOfNormal G B C N
  exact mulSemiringActionOfSmulDistribClass B C G

/-- If `N` is a normal subgroup of `G` and `IsGaloisGroup N B C`, then the quotient group `G ⧸ N`
acts on `B` by `(g : G ⧸ N) • x = g • x`. -/
@[implicit_reducible]
noncomputable def mulSemiringActionQuotient [IsGaloisGroup N B C] [N.Normal] :
    MulSemiringAction (G ⧸ N) B :=
  letI := mulSemiringActionOfNormal G B C N
  { smul q x :=
      Quotient.liftOn' q (· • x) fun g₁ g₂ h ↦ by
      apply FaithfulSMul.algebraMap_injective B C
      rw [algebraMap.smul', algebraMap.smul', smul_eq_iff_eq_inv_smul, ← smul_assoc, smul_eq_mul,
        Subgroup.smul_algebraMap C (by rwa [← QuotientGroup.leftRel_apply])]
    one_smul x := one_smul G x
    mul_smul q₁ q₂ x := Quotient.inductionOn₂' q₁ q₂ fun g h ↦ mul_smul g h x
    smul_add q x y := Quotient.inductionOn' q fun g ↦ smul_add g x y
    smul_zero q := Quotient.inductionOn' q fun g ↦ smul_zero g
    smul_one q := Quotient.inductionOn' q fun g ↦ smul_one g
    smul_mul q x y := Quotient.inductionOn' q fun g ↦ smul_mul' g x y }

theorem mulSemiringActionQuotient_smul_def [MulSemiringAction G B] [SMulDistribClass G B C]
    [IsGaloisGroup N B C] [N.Normal] (g : G) (b : B) :
    letI := mulSemiringActionQuotient G B C N
    (g : G ⧸ N) • b = g • b := by
  let := mulSemiringActionOfNormal G B C N
  refine (Quotient.liftOn'_mk'' (· • b) _ g).trans (FaithfulSMul.algebraMap_injective B C ?_)
  rw [algebraMap.smul', algebraMap.smul']

instance isScalarTower_mulSemiringActionQuotient [MulSemiringAction G B] [SMulDistribClass G B C]
    [IsGaloisGroup N B C] [N.Normal] :
    letI := mulSemiringActionQuotient G B C N
    IsScalarTower G (G ⧸ N) B :=
  let := mulSemiringActionQuotient G B C N
  ⟨fun g q b ↦ Quotient.inductionOn' q fun h ↦ by
    simp [mul_smul, mulSemiringActionQuotient_smul_def]⟩

/-- If `G` acts on `C` commuting with `A`, then the action of `G ⧸ N` on `B` commutes with `A`. -/
@[implicit_reducible]
def smulCommClassQuotient [N.Normal] [Algebra A B] [IsScalarTower A B C] [SMulCommClass G A C]
    [MulSemiringAction G B] [MulAction (G ⧸ N) B] [SMulDistribClass G B C]
    [IsScalarTower G (G ⧸ N) B] :
    SMulCommClass (G ⧸ N) A B :=
  ⟨fun g k x ↦ Quotient.inductionOn' g fun g ↦
    FaithfulSMul.algebraMap_injective B C (by
      simp [algebraMap.smul, algebraMap.smul', smul_comm])⟩

end Semiring

section Domain

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [IsDomain C] [Algebra A B]
    [Algebra A C] [Algebra B C] [FaithfulSMul A B] [FaithfulSMul B C] [IsScalarTower A B C]

omit [FaithfulSMul A B] in
/-- If `G` is a Galois group for `C/A`, and the normal subgroup `N ≤ G` is a Galois group for
`C/B`, then the quotient `G ⧸ N` is a Galois group for `B/A`. -/
theorem quotient [Finite G] (N : Subgroup G) [N.Normal] [MulSemiringAction G C]
    [hG : IsGaloisGroup G A C] [MulSemiringAction G B] [MulSemiringAction (G ⧸ N) B]
    [SMulCommClass (G ⧸ N) A B] [SMulDistribClass G B C] [IsScalarTower G (G ⧸ N) B]
    [IsGaloisGroup N B C] :
    IsGaloisGroup (G ⧸ N) A B where
  faithful.eq_of_smul_eq_smul := fun {g₁} {g₂} ↦ Quotient.inductionOn₂' g₁ g₂ fun g₁ g₂ h ↦ by
    have h' : ∀ g : G, (∀ x : B, g • x = x) → g ∈ N := by
      simp [← fixingSubgroup_range_algebraMap G A B C N, mem_fixingSubgroup_iff, ← algebraMap.smul',
        (FaithfulSMul.algebraMap_injective B C).eq_iff]
    have {g : G} : Quotient.mk'' g = QuotientGroup.mk' N g := rfl
    simp_rw [← inv_smul_eq_iff, this, ← map_inv, smul_smul, ← map_mul,
      QuotientGroup.mk'_apply, MulAction.coe_quotient_smul] at h
    have := h' _ h
    rwa [QuotientGroup.eq, ← Subgroup.inv_mem_iff, mul_inv_rev, inv_inv]
  commutes := inferInstance
  isInvariant.isInvariant x h := by
    simp_rw [← (FaithfulSMul.algebraMap_injective B C).eq_iff, ← IsScalarTower.algebraMap_apply]
    apply hG.isInvariant.isInvariant (algebraMap B C x)
    intro g
    have := (FaithfulSMul.algebraMap_injective B C).eq_iff.mpr <| h g
    rwa [MulAction.coe_quotient_smul, algebraMap.smul'] at this

/-- If `G` is a Galois group for `C/A`, the normal subgroup `N ≤ G` is a Galois group for `C/B`,
and `G'` is a Galois group for `B/A`, then `G ⧸ N ≃* G'`. -/
noncomputable def quotientMulEquiv [Finite G] [Finite G'] (N : Subgroup G) [N.Normal]
    [MulSemiringAction G C] [IsGaloisGroup G A C] [IsGaloisGroup N B C] [MulSemiringAction G' B]
    [IsGaloisGroup G' A B] :
    G ⧸ N ≃* G' :=
  haveI : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  letI := mulSemiringActionOfNormal G B C N
  letI := mulSemiringActionQuotient G B C N
  haveI := smulCommClassQuotient G A B C N
  haveI := quotient G A B C N
  mulEquivCongr (G ⧸ N) G' A B

@[simp]
theorem algebraMap_quotientMulEquiv_smul [Finite G] [Finite G'] (N : Subgroup G) [N.Normal]
    [MulSemiringAction G C] [IsGaloisGroup G A C] [IsGaloisGroup N B C] [MulSemiringAction G' B]
    [IsGaloisGroup G' A B] (g : G) (x : B) :
    algebraMap B C (quotientMulEquiv G G' A B C N g • x) = g • algebraMap B C x := by
  haveI : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  letI := mulSemiringActionOfNormal G B C N
  letI := mulSemiringActionQuotient G B C N
  haveI := smulCommClassQuotient G A B C N
  haveI := quotient G A B C N
  rw [show quotientMulEquiv G G' A B C N ↑g • x = ↑g • x from mulEquivCongr_apply_smul ..]
  exact algebraMap_smulOfNormal G B C N g x

attribute [local instance] FractionRing.liftAlgebra in
/-- The restriction homomorphism from the Galois group of `C/A` to the Galois group of `B/A` where
`C/B/A` is a tower of domains with `C/A` and `B/A` Galois. -/
noncomputable def restrictHom [Finite G] [Finite G'] [MulSemiringAction G C] [IsGaloisGroup G A C]
    [MulSemiringAction G' B] [IsGaloisGroup G' A B] :
    G →* G' :=
  letI N := fixingSubgroup G (Set.range (algebraMap B C))
  haveI : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  haveI : IsDomain A := (FaithfulSMul.algebraMap_injective A B).isDomain
  haveI : FaithfulSMul A C := FaithfulSMul.trans A B C
  letI : MulSemiringAction G (FractionRing C) :=
    IsFractionRing.mulSemiringAction G A C (FractionRing A) (FractionRing C)
  haveI : IsGaloisGroup N (FractionRing B) (FractionRing C) :=
    isGaloisGroup_fixingSubgroup_range_algebraMap G A B C
  letI : MulSemiringAction G' (FractionRing B) :=
    IsFractionRing.mulSemiringAction G' A B (FractionRing A) (FractionRing B)
  haveI : IsGaloisGroup G' (FractionRing A) (FractionRing B) := to_isFractionRing G' A B _ _
  haveI : IsGaloisGroup G (FractionRing A) (FractionRing C) := toFractionRing G A C
  haveI := isGalois G' (FractionRing A) (FractionRing B)
  haveI : N.Normal := normal_of_isGalois G (FractionRing A) (FractionRing C) N (FractionRing B)
  (quotientMulEquiv G G' (FractionRing A) (FractionRing B) (FractionRing C) N).toMonoidHom.comp
    (QuotientGroup.mk' N)

attribute [local instance] FractionRing.liftAlgebra in
@[simp]
theorem algebraMap_restrictHom_smul [Finite G] [Finite G'] [MulSemiringAction G C]
    [IsGaloisGroup G A C] [MulSemiringAction G' B] [IsGaloisGroup G' A B] (g : G) (x : B) :
    algebraMap B C (restrictHom G G' A B C g • x) = g • algebraMap B C x := by
  have : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  have : IsDomain A := (FaithfulSMul.algebraMap_injective A B).isDomain
  have : FaithfulSMul A C := FaithfulSMul.trans A B C
  let : MulSemiringAction G (FractionRing C) :=
    IsFractionRing.mulSemiringAction G A C (FractionRing A) (FractionRing C)
  let : MulSemiringAction G' (FractionRing B) :=
    IsFractionRing.mulSemiringAction G' A B (FractionRing A) (FractionRing B)
  apply FaithfulSMul.algebraMap_injective C (FractionRing C)
  rw [← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply B (FractionRing B) (FractionRing C)]
  simp only [restrictHom, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe,
    QuotientGroup.coe_mk', Function.comp_apply]
  rw [algebraMap.smul', algebraMap_quotientMulEquiv_smul, ← IsScalarTower.algebraMap_apply,
    algebraMap.smul', ← IsScalarTower.algebraMap_apply]

attribute [local instance] FractionRing.liftAlgebra in
theorem restrictHom_surjective [Finite G] [Finite G'] [MulSemiringAction G C]
    [IsGaloisGroup G A C] [MulSemiringAction G' B] [IsGaloisGroup G' A B] :
    Function.Surjective (restrictHom G G' A B C) := by
  let N := fixingSubgroup G (Set.range (algebraMap B C))
  have : IsDomain B := (FaithfulSMul.algebraMap_injective B C).isDomain
  have : IsDomain A := (FaithfulSMul.algebraMap_injective A B).isDomain
  have : FaithfulSMul A C := FaithfulSMul.trans A B C
  let : MulSemiringAction G (FractionRing C) :=
    IsFractionRing.mulSemiringAction G A C (FractionRing A) (FractionRing C)
  have : IsGaloisGroup N (FractionRing B) (FractionRing C) :=
    isGaloisGroup_fixingSubgroup_range_algebraMap G A B C
  let : MulSemiringAction G' (FractionRing B) :=
    IsFractionRing.mulSemiringAction G' A B (FractionRing A) (FractionRing B)
  have : IsGaloisGroup G' (FractionRing A) (FractionRing B) := to_isFractionRing G' A B _ _
  have : IsGaloisGroup G (FractionRing A) (FractionRing C) := toFractionRing G A C
  have := isGalois G' (FractionRing A) (FractionRing B)
  have : N.Normal := normal_of_isGalois G (FractionRing A) (FractionRing C) N (FractionRing B)
  simpa [restrictHom] using QuotientGroup.mk_surjective

end Domain

noncomputable section IntermediateField

variable (N : Subgroup G) [N.Normal] [IsGaloisGroup N F L]

instance : MulSemiringAction (G ⧸ N) F :=
  letI := smulOfNormal G F L N
  haveI := smulDistribClass_smulOfNormal G F L N
  letI := mulSemiringActionOfSmulDistribClass F L G
  mulSemiringActionQuotient G F L N

instance [SMulCommClass G K L] [MulSemiringAction G F] [SMulDistribClass G F L]
    [IsScalarTower G (G ⧸ N) F] : SMulCommClass (G ⧸ N) K F :=
  smulCommClassQuotient G K F L N

/-- If `G` is a finite Galois group for `L/K` and `N` is a normal subgroup of `G` that is a
Galois group for `L/F`, then the quotient group `G ⧸ N` is a Galois group for `F/K`. -/
instance [Finite G] [IsGaloisGroup G K L] : IsGaloisGroup (G ⧸ N) K F :=
  letI := smulOfNormal G F L N
  haveI := smulDistribClass_smulOfNormal G F L N
  letI := mulSemiringActionOfSmulDistribClass F L G
  haveI := isScalarTower_mulSemiringActionQuotient G F L N
  quotient G K F L N

variable (E : IntermediateField K L) [hE : IsGaloisGroup H E L]

/-- If `G` is a finite Galois group for `L/K`, `N` is a normal subgroup that is a Galois group for
`L/F`, and `H` is a subgroup that is a Galois group for `L/E` with `E ≤ F`, then the image of `H`
under the canonical quotient map `G → G ⧸ N` is a Galois group for `F/E`. -/
theorem map_quotientMk' [Finite G] [IsGaloisGroup G K L] (h : E ≤ F) :
    letI : Algebra E F := (IntermediateField.inclusion h).toAlgebra
    IsGaloisGroup (H.map (QuotientGroup.mk' N)) E F :=
  let : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  let : SMul G F := smulOfNormal G F L N
  have : SMulDistribClass G F L := smulDistribClass_smulOfNormal G F L N
  let := mulSemiringActionOfSmulDistribClass F L G
  have : IsScalarTower E F L := IsScalarTower.of_algebraMap_eq' rfl
  have := isScalarTower_mulSemiringActionQuotient G F L N
  { faithful := have := (inferInstance : IsGaloisGroup (G ⧸ N) K F).faithful; inferInstance
    commutes := ⟨by
      intro ⟨_, g, hg, rfl⟩ x y
      apply FaithfulSMul.algebraMap_injective F L
      simpa [MulAction.subgroup_smul_def, algebraMap.coe_smul', algebraMap.coe_smul]
        using hE.commutes.smul_comm ⟨g, hg⟩ x (y : L)⟩
    isInvariant := ⟨fun x h ↦ by
      obtain ⟨a, ha⟩ := hE.isInvariant.isInvariant (algebraMap F L x) (by
        rintro ⟨g, hg⟩
        rw [MulAction.subgroup_smul_def, ← algebraMap.smul']
        exact congr_arg (algebraMap F L) <| h ⟨g, ⟨g, hg, rfl⟩⟩)
      exact ⟨a, FaithfulSMul.algebraMap_injective F L
        (by rw [← IsScalarTower.algebraMap_apply, ha])⟩⟩ }

@[deprecated (since := "2026-04-21")] alias quotientMap := map_quotientMk'

end IntermediateField

end Quotient

end IsGaloisGroup
