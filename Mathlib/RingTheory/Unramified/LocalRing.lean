/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Locus

/-!
# Unramified algebras over local rings

## Main results
- `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`:
  Let `R` be a local ring, `A` be a local `R`-algebra essentially of finite type.
  Then `A/R` is unramified if and only if `κA/κR` is separable, and `m_R S = m_S`.
- `Algebra.isUnramifiedAt_iff_map_eq`:
  Let `A` be an essentially of finite type `R`-algebra, `q` be a prime over `p`.
  Then `A` is unramified at `p` if and only if `κ(q)/κ(p)` is separable, and `pS_q = qS_q`.
-/

open IsLocalRing

namespace Algebra

section IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

instance : FormallyUnramified S (ResidueField S) := .quotient _

instance [FormallyUnramified R S] :
    FormallyUnramified (ResidueField R) (ResidueField S) :=
  have : FormallyUnramified R (ResidueField S) := .comp _ S _
  .of_comp R _ _

variable [EssFiniteType R S]

@[stacks 00UW "(2)"]
instance [FormallyUnramified R S] :
    Module.Finite (ResidueField R) (ResidueField S) :=
  have : EssFiniteType R (ResidueField S) := .comp _ S _
  have : EssFiniteType (ResidueField R) (ResidueField S) := .of_comp R _ _
  FormallyUnramified.finite_of_free _ _

@[stacks 00UW "(2)"]
instance [FormallyUnramified R S] :
    Algebra.IsSeparable (ResidueField R) (ResidueField S) :=
  FormallyUnramified.isSeparable _ _

lemma FormallyUnramified.isField_quotient_map_maximalIdeal [FormallyUnramified R S] :
    IsField (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  let mR := (maximalIdeal R).map (algebraMap R S)
  have hmR : mR ≤ maximalIdeal S := ((local_hom_TFAE (algebraMap R S)).out 0 2 rfl rfl).mp ‹_›
  letI : Algebra (ResidueField R) (S ⧸ mR) := inferInstanceAs (Algebra (R ⧸ _) _)
  have : IsScalarTower R (ResidueField R) (S ⧸ mR) := inferInstanceAs (IsScalarTower R (R ⧸ _) _)
  have : FormallyUnramified (ResidueField R) (S ⧸ mR) := .of_comp R _ _
  have : EssFiniteType (ResidueField R) (S ⧸ mR) := .of_comp R _ _
  have : Module.Finite (ResidueField R) (S ⧸ mR) := FormallyUnramified.finite_of_free _ _
  have : IsReduced (S ⧸ mR) := FormallyUnramified.isReduced_of_field (ResidueField R) (S ⧸ mR)
  have : IsArtinianRing (S ⧸ mR) := isArtinian_of_tower (ResidueField R) inferInstance
  have : Nontrivial (S ⧸ mR) := Ideal.Quotient.nontrivial fun e ↦
    (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp <| e.symm.trans_le hmR)
  have : IsLocalRing (S ⧸ mR) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : maximalIdeal (S ⧸ mR) = ⊥ := by
    rw [← jacobson_eq_maximalIdeal _ bot_ne_top, IsArtinianRing.jacobson_eq_radical,
      ← Ideal.zero_eq_bot, ← nilradical, nilradical_eq_zero]
  rwa [← isField_iff_maximalIdeal_eq] at this

@[stacks 00UW "(1)"]
lemma FormallyUnramified.map_maximalIdeal [FormallyUnramified R S] :
    (maximalIdeal R).map (algebraMap R S) = maximalIdeal S := by
  apply eq_maximalIdeal
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact isField_quotient_map_maximalIdeal

@[stacks 02FM]
lemma FormallyUnramified.of_map_maximalIdeal
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    (H : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    Algebra.FormallyUnramified R S := by
  constructor
  have : FormallyUnramified (ResidueField R) (ResidueField S) := .of_isSeparable _ _
  have : FormallyUnramified R (ResidueField S) := .comp _ (ResidueField R) _
  rw [← subsingleton_tensorProduct (R := S)]
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨x, rfl⟩ := (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R S
    (ResidueField S) Ideal.Quotient.mk_surjective x).mp (Subsingleton.elim _ _)
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  simp only [KaehlerDifferential.kerCotangentToTensor_toCotangent]
  replace hx : x ∈ Ideal.map (algebraMap R S) (maximalIdeal R) := by simpa [H] using hx
  induction hx using Submodule.span_induction with
  | zero => simp
  | mem x h => obtain ⟨x, hx, rfl⟩ := h; simp
  | add x y hx hy _ _ => simp [*, TensorProduct.tmul_add]
  | smul a x hx _ =>
    have : residue S x = 0 := by rwa [residue_eq_zero_iff, ← H]
    simp [*, TensorProduct.tmul_add, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]

lemma FormallyUnramified.iff_map_maximalIdeal_eq :
    Algebra.FormallyUnramified R S ↔
      Algebra.IsSeparable (ResidueField R) (ResidueField S) ∧
      (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
  ⟨fun _ ↦ ⟨inferInstance, map_maximalIdeal⟩, fun ⟨_, e⟩ ↦ of_map_maximalIdeal e⟩

end IsLocalRing

section IsUnramifiedAt

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

noncomputable
instance (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    Algebra p.ResidueField q.ResidueField :=
  (Ideal.ResidueField.mapₐ p q Ideal.LiesOver.over).toAlgebra

/-- Let `A` be an essentially of finite type `R`-algebra, `q` be a prime over `p`.
Then `A` is unramified at `p` if and only if `κ(q)/κ(p)` is separable, and `pS_q = qS_q`. -/
lemma isUnramifiedAt_iff_map_eq [EssFiniteType R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    Algebra.IsUnramifiedAt R q ↔
      Algebra.IsSeparable p.ResidueField q.ResidueField ∧
      p.map (algebraMap R (Localization.AtPrime q)) = maximalIdeal _ := by
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q (algebraMap R S) Ideal.LiesOver.over).toAlgebra
  have : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) := .of_algebraMap_eq
    fun x ↦ (Localization.localRingHom_to_map p q (algebraMap R S) Ideal.LiesOver.over x).symm
  letI : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom _ _ _ Ideal.LiesOver.over
  have : EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) := .of_comp R _ _
  trans Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q)
  · exact ⟨fun _ ↦ .of_comp R _ _,
      fun _ ↦ Algebra.FormallyUnramified.comp _ (Localization.AtPrime p) _⟩
  rw [FormallyUnramified.iff_map_maximalIdeal_eq]
  congr!
  rw [RingHom.algebraMap_toAlgebra, ← Localization.AtPrime.map_eq_maximalIdeal,
    Ideal.map_map, Localization.localRingHom,
    IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]

end IsUnramifiedAt

end Algebra
