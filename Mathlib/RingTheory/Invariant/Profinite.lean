/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
import Mathlib.CategoryTheory.CofilteredSystem

/-!
# Invariant Extensions of Rings

In this file we generalize the results in `Mathlib/RingTheory/Invariant/Basic.lean` to profinite
groups.

## Main statements

Let `G` be a profinite group acting continuously on a
  commutative ring `B` (with the discrete topology) satisfying `Algebra.IsInvariant A B G`.

* `Algebra.IsInvariant.isIntegral_of_profinite`: `B/A` is an integral extension.
* `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`:
  `G` acts transitivity on the prime ideals of `B` lying above a given prime ideal of `A`.
* `Ideal.Quotient.stabilizerHom_surjective_of_profinite`: if `Q` is a prime ideal of `B` lying over
  a prime ideal `P` of `A`, then the stabilizer subgroup of `Q` surjects onto `Aut((B/Q)/(A/P))`.

-/

open scoped Pointwise

section ProfiniteGrp

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
variable {P : Ideal A}
variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]

open Pointwise CategoryTheory

include G in
lemma Algebra.IsInvariant.isIntegral_of_profinite
    [Algebra.IsInvariant A B G] : Algebra.IsIntegral A B := by
  constructor
  intro x
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (stabilizer_isOpen G x) (one_mem _)
  have := (Algebra.IsInvariant.isIntegral A (FixedPoints.subalgebra A B N.1.1) (G ⧸ N.1.1)).1
    ⟨x, fun g ↦ hN g.2⟩
  exact this.map (FixedPoints.subalgebra A B N.1.1).val

/-- `G` acts transitively on the prime ideals of `B` above a given prime ideal of `A`. -/
lemma Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    [Algebra.IsInvariant A B G] (P Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (hPQ : P.under A = Q.under A) :
    ∃ g : G, Q = g • P := by
  let B' := FixedPoints.subalgebra A B
  let F : OpenNormalSubgroup G ⥤ Type _ :=
  { obj N := { g : G ⧸ N.1.1 // Q.under (B' N.1.1) = g • P.under (B' N.1.1) }
    map {N N'} f x := ⟨(QuotientGroup.map _ _ (.id _) (leOfHom f)) x.1, by
      have h : B' N'.1.1 ≤ B' N.1.1 := fun x hx n ↦ hx ⟨_, f.le n.2⟩
      obtain ⟨x, hx⟩ := x
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      simpa only [Ideal.comap_comap, Ideal.pointwise_smul_eq_comap, ← Ideal.comap_coe
        (F := RingEquiv _ _)] using congr(Ideal.comap (Subalgebra.inclusion h).toRingHom $hx)⟩
    map_id N := by ext ⟨⟨x⟩, hx⟩; rfl
    map_comp f g := by ext ⟨⟨x⟩, hx⟩; rfl }
  have (N : _) : Nonempty (F.obj N) := by
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A
      (B' N.1.1) (G ⧸ N.1.1) (P.under _) (Q.under _) hPQ
    exact ⟨g, hg⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system F
  let a := (ProfiniteGrp.of G).isoLimittoFiniteQuotientFunctor.inv.hom
    ⟨fun N ↦ (s N).1, (fun {N N'} f ↦ congr_arg Subtype.val (hs f))⟩
  have (N : OpenNormalSubgroup G) : QuotientGroup.mk (s := N.1.1) a = s N := by
    change ((ProfiniteGrp.of G).isoLimittoFiniteQuotientFunctor.hom.hom a).1 N = _
    simp only [a]
    rw [← ProfiniteGrp.comp_apply, Iso.inv_hom_id]
    simp
  refine ⟨a, ?_⟩
  ext x
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (stabilizer_isOpen G x) (one_mem _)
  lift x to B' N.1.1 using fun g ↦ hN g.2
  change x ∈ Q.under (B' N.1.1) ↔ x ∈ Ideal.under (B' N.1.1) ((_ : G) • P)
  rw [(s N).2]
  simp only [Ideal.comap_comap, Ideal.pointwise_smul_eq_comap, ← Ideal.comap_coe
        (F := RingEquiv _ _)]
  congr! 2
  ext y
  simp [← this]
  rfl

attribute [local instance] Subgroup.finiteIndex_of_finite_quotient

omit
  [CompactSpace G]
  [TotallyDisconnectedSpace G]
  [IsTopologicalGroup G]
  [TopologicalSpace B]
  [DiscreteTopology B]
  [ContinuousSMul G B] in
lemma Ideal.Quotient.stabilizerHomSurjectiveAuxFunctor_aux
    (Q : Ideal B)
    {N N' : OpenNormalSubgroup G} (e : N ≤ N')
    (x : G ⧸ N.1.1)
    (hx : x ∈ MulAction.stabilizer (G ⧸ N.1.1) (Q.under (FixedPoints.subalgebra A B N.1.1))) :
    QuotientGroup.map _ _ (.id _) e x ∈
      MulAction.stabilizer (G ⧸ N'.1.1) (Q.under (FixedPoints.subalgebra A B N'.1.1)) := by
  change _ = _
  have h : FixedPoints.subalgebra A B N'.1.1 ≤ FixedPoints.subalgebra A B N.1.1 :=
    fun x hx n ↦ hx ⟨_, e n.2⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  replace hx := congr(Ideal.comap (Subalgebra.inclusion h) $hx)
  simpa only [Ideal.pointwise_smul_eq_comap,
    ← Ideal.comap_coe (F := RingEquiv _ _), Ideal.comap_comap] using hx

/-- (Implementation)
The functor taking an open normal subgroup `N ≤ G` to the set of lifts of `σ` in `G ⧸ N`.
We will show that its inverse limit is nonempty to conclude that there exists a lift in `G`. -/
def Ideal.Quotient.stabilizerHomSurjectiveAuxFunctor
    (P : Ideal A) (Q : Ideal B) [Q.LiesOver P] (σ : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q) :
    OpenNormalSubgroup G ⥤ Type _ where
  obj N :=
    letI B' := FixedPoints.subalgebra A B N.1.1
    letI f : (B' ⧸ Q.under B') →ₐ[A ⧸ P] B ⧸ Q :=
    { toRingHom := Ideal.quotientMap _ B'.subtype le_rfl,
      commutes' := Quotient.ind fun _ ↦ rfl }
    { σ' // f.comp (Ideal.Quotient.stabilizerHom
      (Q.under B') P (G ⧸ N.1.1) σ') = σ.toAlgHom.comp f }
  map {N N'} i x := ⟨⟨(QuotientGroup.map _ _ (.id _) (leOfHom i)) x.1,
    Ideal.Quotient.stabilizerHomSurjectiveAuxFunctor_aux Q i.le x.1.1 x.1.2⟩, by
    have h : FixedPoints.subalgebra A B N'.1.1 ≤ FixedPoints.subalgebra A B N.1.1 :=
      fun x hx n ↦ hx ⟨_, i.le n.2⟩
    obtain ⟨⟨x, hx⟩, hx'⟩ := x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    ext g
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g
    exact DFunLike.congr_fun hx' (Ideal.Quotient.mk _ (Subalgebra.inclusion h g))⟩
  map_id N := by ext ⟨⟨⟨x⟩, hx⟩, hx'⟩; rfl
  map_comp f g := by ext ⟨⟨⟨x⟩, hx⟩, hx'⟩; rfl

open Ideal.Quotient in
instance (P : Ideal A) (Q : Ideal B) [Q.LiesOver P]
    (σ : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q) (N : OpenNormalSubgroup G) :
    Finite ((stabilizerHomSurjectiveAuxFunctor P Q σ).obj N) := by
  dsimp [stabilizerHomSurjectiveAuxFunctor]
  infer_instance

open Ideal.Quotient in
instance (P : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]
    [Algebra.IsInvariant A B G] (σ : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q) (N : OpenNormalSubgroup G) :
    Nonempty ((stabilizerHomSurjectiveAuxFunctor P Q σ).obj N) := by
  have : IsScalarTower (A ⧸ P) (FixedPoints.subalgebra A B N.1.1 ⧸
    Q.under (FixedPoints.subalgebra A B N.1.1)) (B ⧸ Q) := IsScalarTower.of_algebraMap_eq
    (Quotient.ind fun x ↦ rfl)
  obtain ⟨σ', hσ'⟩ := Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under (G ⧸ N.1.1) P
    (Q.under (FixedPoints.subalgebra A B N.1.1)) σ
  obtain ⟨τ, rfl⟩ := Ideal.Quotient.stabilizerHom_surjective (G ⧸ N.1.1) P
    (Q.under (FixedPoints.subalgebra A B N.1.1)) σ'
  refine ⟨τ, ?_⟩
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hσ' x

/-- The stabilizer subgroup of `Q` surjects onto `Aut((B/Q)/(A/P))`. -/
theorem Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (P : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]
    [Algebra.IsInvariant A B G] :
    Function.Surjective (Ideal.Quotient.stabilizerHom Q P G) := by
  intro σ
  let B' := FixedPoints.subalgebra A B
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system
    (stabilizerHomSurjectiveAuxFunctor (G := G) P Q σ)
  let a := (ProfiniteGrp.of G).isoLimittoFiniteQuotientFunctor.inv.hom
    ⟨fun N ↦ (s N).1.1, (fun {N N'} f ↦ congr($(hs f).1.1))⟩
  have (N : OpenNormalSubgroup G) : QuotientGroup.mk (s := N.1.1) a = (s N).1 :=
    congr_fun (congr_arg Subtype.val (ConcreteCategory.congr_hom (ProfiniteGrp.of
      G).isoLimittoFiniteQuotientFunctor.inv_hom_id (Subtype.mk (fun N ↦ (s N).1.1) _))) N
  refine ⟨⟨a, ?_⟩, ?_⟩
  · ext x
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (stabilizer_isOpen G x) (one_mem _)
    lift x to B' N.1.1 using fun g ↦ hN g.2
    change x ∈ (a • Q).under (B' N.1.1) ↔ x ∈ Q.under (B' N.1.1)
    rw [← (s N).1.2]
    simp only [Ideal.comap_comap, Ideal.pointwise_smul_eq_comap, ← Ideal.comap_coe
          (F := RingEquiv _ _)]
    congr! 2
    ext y
    rw [← this]
    rfl
  · ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (stabilizer_isOpen G x) (one_mem _)
    lift x to B' N.1.1 using fun g ↦ hN g.2
    change Ideal.Quotient.mk Q (QuotientGroup.mk (s := N) a • x).1 = _
    rw [this]
    exact DFunLike.congr_fun (s N).2 (Ideal.Quotient.mk _ x)

end ProfiniteGrp
