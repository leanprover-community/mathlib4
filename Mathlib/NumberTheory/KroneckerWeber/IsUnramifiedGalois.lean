import Mathlib.NumberTheory.KroneckerWeber.IsInvariant
import Mathlib.NumberTheory.KroneckerWeber.Unramified

namespace Algebra

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
variable (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B] [IsInvariant A B G]
variable (p : Ideal A) (hp : p ≠ ⊥) [p.IsMaximal]
    [Finite G] [FaithfulSMul G B]
    (P : Ideal B) [P.LiesOver p] [P.IsMaximal]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B] [NoZeroSMulDivisors A B]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]

attribute [local instance] Ideal.Quotient.field in
instance (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsMaximal]
    (P : Ideal B) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] : Algebra.IsSeparable p.ResidueField P.ResidueField := by
  letI := ((algebraMap (B ⧸ P) P.ResidueField).comp (algebraMap (A ⧸ p) (B ⧸ P))).toAlgebra
  haveI : IsScalarTower (A ⧸ p) p.ResidueField P.ResidueField := by
    refine .of_algebraMap_eq fun x ↦ ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [RingHom.algebraMap_toAlgebra, Algebra.ofId_apply]
    rfl
  haveI : IsScalarTower (A ⧸ p) (B ⧸ P) P.ResidueField := .of_algebraMap_eq' rfl
  have : Algebra.IsSeparable (B ⧸ P) P.ResidueField :=
    .of_algHom _ _ (AlgEquiv.ofBijective (Algebra.ofId (B ⧸ P) _)
      P.bijective_algebraMap_quotient_residueField).symm.toAlgHom
  have : Algebra.IsSeparable (A ⧸ p) P.ResidueField := .trans (A ⧸ p) (B ⧸ P) _
  refine Algebra.isSeparable_tower_top_of_isSeparable (A ⧸ p) _ _

include hp in
lemma IsInvariant.isUnramifiedAt_iff_inertia_eq_bot :
    IsUnramifiedAt A P ↔ P.toAddSubgroup.inertia G = ⊥ := by
  let p' := P.under A
  obtain rfl : p = p' := ‹P.LiesOver p›.over
  rw [isUnramifiedAt_iff_map_eq2 (p := p'), ← Ideal.ramificationIdx_eq_one_iff_of_isDedekindDomain
    (hp := Ideal.ne_bot_of_liesOver_of_ne_bot hp _), ← IsInvariant.card_inertia (G := G) (hp := hp),
    and_iff_right (by infer_instance), Subgroup.card_eq_one]

-- omit [FaithfulSMul G B] in
-- include hp in
-- lemma IsInvariant.isUnramifiedAt_iff_inertia_eq_ker :
--     IsUnramifiedAt A P ↔ P.toAddSubgroup.inertia G = (MulSemiringAction.toRingAut G B).ker := by

end Algebra
