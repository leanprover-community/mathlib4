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

attribute [instance low] IsGaloisGroup.commutes IsGaloisGroup.isInvariant

variable [FaithfulSMul A B] [hA : IsGaloisGroup G A B]

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

/-- `IsGaloisGroup` for rings implies `IsGaloisGroup` for their fraction fields. -/
theorem IsGaloisGroup.to_isFractionRing [Finite G] [hGAB : IsGaloisGroup G A B] :
    IsGaloisGroup G K L where
  faithful :=
    have := hGAB.faithful
    IsFractionRing.faithfulSMul G B L
  commutes := IsFractionRing.smulCommClass G A B K L
  isInvariant := IsFractionRing.isInvariant G A B K L

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
`FractionRing.mulSemiringAction_of_isGaloisGroup`.
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

protected theorem finite [FiniteDimensional K L] [IsGaloisGroup G K L] : Finite G :=
  Nat.finite_of_card_ne_zero (card_eq_finrank G K L ▸ Module.finrank_pos.ne')

/-- If `G` is a finite Galois group for `L/K`, then `G` is isomorphic to `Gal(L/K)`. -/
@[simps!] noncomputable def mulEquivAlgEquiv [IsGaloisGroup G K L] [Finite G] : G ≃* Gal(L/K) :=
  MulEquiv.ofBijective (MulSemiringAction.toAlgAut G K L) (by
    have := isGalois G K L
    have := finiteDimensional G K L
    rw [Nat.bijective_iff_injective_and_card, card_eq_finrank G K L,
      IsGalois.card_aut_eq_finrank K L]
    exact ⟨fun _ _ ↦ (faithful K).eq_of_smul_eq_smul ∘ DFunLike.ext_iff.mp, rfl⟩)

/-- If `G` and `G'` are finite Galois groups for `L/K`, then `G` is isomorphic to `G'`. -/
noncomputable def mulEquivCongr [IsGaloisGroup G K L] [Finite G]
    [IsGaloisGroup G' K L] [Finite G'] : G ≃* G' :=
  (mulEquivAlgEquiv G K L).trans (mulEquivAlgEquiv G' K L).symm

@[simp]
theorem mulEquivCongr_apply_smul [IsGaloisGroup G K L] [Finite G] [IsGaloisGroup G' K L] [Finite G']
    (g : G) (x : L) : mulEquivCongr G G' K L g • x = g • x :=
  AlgEquiv.ext_iff.mp ((mulEquivAlgEquiv G' K L).apply_symm_apply (mulEquivAlgEquiv G K L g)) x

@[simp]
theorem map_mulEquivAlgEquiv_fixingSubgroup
    [IsGaloisGroup G K L] [Finite G] (F : IntermediateField K L) :
    (fixingSubgroup G (F : Set L)).map (mulEquivAlgEquiv G K L) = F.fixingSubgroup := by
  ext g
  obtain ⟨g, rfl⟩ := (mulEquivAlgEquiv G K L).surjective g
  simp [mem_fixingSubgroup_iff]

variable (H H' : Subgroup G) (F F' : IntermediateField K L)

instance subgroup [hGKL : IsGaloisGroup G K L] :
    IsGaloisGroup H (FixedPoints.intermediateField H : IntermediateField K L) L where
  faithful := have := hGKL.faithful; inferInstance
  commutes := inferInstanceAs <| SMulCommClass H (FixedPoints.subfield H L) L
  isInvariant := ⟨fun x h ↦ ⟨⟨x, h⟩, rfl⟩⟩

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
  convert IsGaloisGroup.subgroup G K L H

variable {G K L H F} in
theorem subgroup_iff [hGKL : IsGaloisGroup G K L] :
    IsGaloisGroup H F L ↔ FixedPoints.intermediateField H = F :=
  ⟨fun _ ↦ fixedPoints_of_isGaloisGroup G K L H F, fun h ↦ of_fixedPoints_eq G K L H F h⟩

theorem smul_eq_self [IsGaloisGroup H F L] (g : G) (hg : g ∈ H) (x : F) :
    g • (x : L) = x :=
  smul_algebraMap (⟨g, hg⟩ : H) x

theorem smul_mem_of_normal (N : Subgroup G) [hN : N.Normal] [hF : IsGaloisGroup N F L] (g : G)
    (x : F) : g • (x : L) ∈ F := by
  have : ∀ (n : N), n • g • (x : L) = g • x := by
    intro n
    rw [← smul_assoc, MulAction.subgroup_smul_def, smul_eq_mul,
      show n * g = g * (g⁻¹ * n * g) by group, ← smul_eq_mul, smul_assoc,
      IsGaloisGroup.smul_eq_self G K L N F (g⁻¹ * (n : G) * g)]
    exact hN.conj_mem' n n.prop g
  obtain ⟨y, hy⟩ := hF.isInvariant.isInvariant (g • x) this
  simp [← hy]

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
  convert IsGaloisGroup.fixedPoints_eq_bot G K L
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

/-- If `G` acts as a Galois group on `L/K` and the subgroup `H` acts as a Galois group on `L/R`,
then the fixed points of `H` equals the range of `algebraMap R L`. -/
theorem fixedPoints_eq_range_algebraMap [Finite G] (R : Type*)
    [CommSemiring R] [Algebra R L] [IsGaloisGroup H R L] :
    (FixedPoints.intermediateField H : IntermediateField K L) = Set.range (algebraMap R L) := by
  ext
  rw [SetLike.mem_coe, FixedPoints.mem_intermediateField_iff, Set.mem_range]
  refine ⟨IsGaloisGroup.isInvariant.isInvariant _, ?_⟩
  rintro ⟨x, rfl⟩ h
  exact smul_algebraMap h x

include K in
/-- If `G` acts as a Galois group on `L/K` and the subgroup `H` acts as a Galois group on `L/R`,
then the fixing subgroup of `algebraMap R L` inside `G` equals `H`. -/
theorem fixingSubgroup_range_algebraMap [Finite G] (R : Type*) [CommSemiring R] [Algebra R L]
    [IsGaloisGroup H R L] :
    fixingSubgroup G (Set.range (algebraMap R L)) = H := by
  rw [← fixedPoints_eq_range_algebraMap G K L H, fixingSubgroup_fixedPoints]

attribute [local instance] FractionRing.liftAlgebra in
/-- The ring analogue of `fixingSubgroup_range_algebraMap`: if `G` acts on a domain `T`
with `IsGaloisGroup G R T`, and a subgroup `H` acts on `T` with `IsGaloisGroup H S T`,
then the fixing subgroup of `algebraMap S T` equals `H`. -/
theorem fixingSubgroup_range_algebraMap_of_isDomain [Finite G] (R S T : Type*) [CommRing R]
    [CommRing T] [IsDomain T] [Algebra R T] [FaithfulSMul R T] [MulSemiringAction G T]
    (H : Subgroup G) [hGRT : IsGaloisGroup G R T] [CommRing S] [Algebra S T] [FaithfulSMul S T]
    [hH : IsGaloisGroup H S T] :
    fixingSubgroup G (Set.range (algebraMap S T)) = H := by
  have : IsDomain S := (FaithfulSMul.algebraMap_injective S T).isDomain
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R T).isDomain
  let K := FractionRing R
  let L := FractionRing T
  let : MulSemiringAction G L := IsFractionRing.mulSemiringAction G R T K L
  have : IsGaloisGroup G K L := IsGaloisGroup.toFractionRing G R T
  have : IsGaloisGroup H (FractionRing S) L := IsGaloisGroup.toFractionRing H S T
  suffices h : fixingSubgroup G (Set.range (algebraMap S T)) =
               fixingSubgroup G (Set.range (algebraMap (FractionRing S) L)) by
    rw [h]
    exact fixingSubgroup_range_algebraMap G K L H (FractionRing S)
  ext g
  simp only [mem_fixingSubgroup_iff, Set.mem_range]
  refine ⟨?_, ?_⟩
  · rintro h _ ⟨x, rfl⟩
    have {x} : g • (algebraMap S L) x = (algebraMap S L) x := by
      rw [IsScalarTower.algebraMap_apply S T L, ← algebraMap.smul', h _ ⟨x, rfl⟩]
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective S x
    simp only [map_div₀, ← IsScalarTower.algebraMap_apply, smul_div₀', this]
  · rintro h _ ⟨x, rfl⟩
    apply FaithfulSMul.algebraMap_injective T L
    rw [algebraMap.smul']
    apply h
    use algebraMap S (FractionRing S) x
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

end IsGaloisGroup

end GaloisCorrespondence

section Quotient

variable (N : Subgroup G) [N.Normal] [hF : IsGaloisGroup N F L]

instance : SMul (G ⧸ N) F where
  smul g x := Quotient.liftOn' g (fun g ↦ ⟨g • (x : L), smul_mem_of_normal G K L F N g x⟩)
    fun g g' h ↦ Subtype.ext <| by
      rw [smul_eq_iff_eq_inv_smul, ← smul_assoc, smul_eq_mul, smul_eq_self G K L N]
      rwa [← QuotientGroup.leftRel_apply]

@[simp]
lemma coe_quotient_smul (g : G) (x : F) :
    ((g : G ⧸ N) • x : F) = g • (x : L) := rfl

instance : MulSemiringAction (G ⧸ N) F where
  one_smul _ := Subtype.ext <| by rw [← QuotientGroup.mk_one, coe_quotient_smul, one_smul]
  smul_zero g := Quotient.inductionOn' g fun g ↦ Subtype.ext <| by simp
  mul_smul g g' x := Quotient.inductionOn₂' g g' fun g g' ↦ Subtype.ext <| by
    simp [← QuotientGroup.mk_mul, coe_quotient_smul, mul_smul]
  smul_add g x y := Quotient.inductionOn' g fun g ↦ Subtype.ext <| by simp [smul_add]
  smul_one g := Quotient.inductionOn' g fun g ↦ Subtype.ext <| by simp
  smul_mul g x y := Quotient.inductionOn' g fun g ↦ Subtype.ext <| by simp [smul_mul']

instance [SMulCommClass G K L] : SMulCommClass (G ⧸ N) K F :=
  ⟨fun g k x ↦ Quotient.inductionOn' g fun g ↦ Subtype.ext <| by simp [smul_comm]⟩

variable [hK : IsGaloisGroup G K L] [Finite G]

instance quotient : IsGaloisGroup (G ⧸ N) K F where
  faithful.eq_of_smul_eq_smul := fun {g₁} {g₂} ↦ Quotient.inductionOn₂' g₁ g₂ fun g₁ g₂ h ↦ by
    rw [QuotientGroup.eq, ← fixingSubgroup_fixedPoints G K L N, subgroup_iff.mp hF,
      mem_fixingSubgroup_iff]
    intro x hx
    rw [mul_smul, inv_smul_eq_iff]
    simpa [eq_comm, coe_quotient_smul] using congr_arg Subtype.val <| h ⟨x, hx⟩
  commutes := inferInstance
  isInvariant.isInvariant := fun x h ↦ by
    have : ∀ (g : G), g • (x : L) = x := fun g ↦ by
      simpa [coe_quotient_smul] using congr_arg Subtype.val (h g)
    obtain ⟨a, ha⟩ := hK.isInvariant.isInvariant x this
    refine ⟨a, FaithfulSMul.algebraMap_injective F L ?_⟩
    rw [← IsScalarTower.algebraMap_apply, ha, IntermediateField.algebraMap_apply]

variable (E : IntermediateField K L) [hE : IsGaloisGroup H E L]

theorem quotientMap (h : E ≤ F) :
    letI : Algebra E F := (IntermediateField.inclusion h).toAlgebra
    IsGaloisGroup (H.map (QuotientGroup.mk' N)) E F :=
  have hFN : IsGaloisGroup (G ⧸ N) K F := inferInstance
  let : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  { faithful := by have := hFN.faithful; infer_instance
    commutes := ⟨by
      intro ⟨_, g, hg, rfl⟩ x y
      exact FaithfulSMul.algebraMap_injective F L (hE.commutes.smul_comm ⟨g, hg⟩ x (y : L))⟩
    isInvariant := ⟨fun x h ↦ by
      obtain ⟨a, ha⟩ := hE.isInvariant.isInvariant x
        fun ⟨g, hg⟩ ↦ congr_arg Subtype.val (h ⟨g, g, hg, rfl⟩)
      have : IsScalarTower E F L := IsScalarTower.of_algebraMap_eq' rfl
      exact ⟨a, FaithfulSMul.algebraMap_injective F L
        (by rw [← IsScalarTower.algebraMap_apply, ha, IntermediateField.algebraMap_apply])⟩⟩ }

end Quotient

end IsGaloisGroup
