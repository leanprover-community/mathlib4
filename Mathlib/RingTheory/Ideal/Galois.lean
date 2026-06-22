/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!

# Restriction of the Galois action on ideals to a subextension

Let `R ⊆ A ⊆ B` be a tower of commutative rings, with `G` a Galois group for `B / R` and `H` a
Galois group for `A / R`. The restriction homomorphism `IsGaloisGroup.restrictHom : G →* H` then
sends the decomposition (resp. inertia) group of a prime `P` of `B` into the decomposition
(resp. inertia) group of the prime `p = P ∩ A` of `A`. This file packages these as group
homomorphisms and proves they are surjective with kernel coming from `restrictHom`.

## Main definitions

* `Ideal.stabilizerMapOfLiesOver`: the homomorphism `stabilizer G P →* stabilizer H p`.
* `Ideal.inertiaMapOfLiesOver`: the homomorphism `inertia G P →* inertia H p`.

## Main results

* `Ideal.stabilizerMapOfLiesOver_surjective`, `Ideal.inertiaMapOfLiesOver_surjective`.
* `Ideal.stabilizerMapOfLiesOver_ker`, `Ideal.inertiaMapOfLiesOver_ker`.

-/

@[expose] public section

open MulAction Pointwise IsGaloisGroup

namespace Ideal

variable (G H : Type*) [Group G] [Group H] [Finite G] [Finite H] (R : Type*) {A B : Type*}
  [CommRing R] [CommRing A] [CommRing B] [IsDomain B] [Algebra R A] [Algebra A B] [Algebra R B]
  [IsScalarTower R A B] [FaithfulSMul R A] [FaithfulSMul A B] [MulSemiringAction G B]
  [IsGaloisGroup G R B] [MulSemiringAction H A] [IsGaloisGroup H R A]
  (P : Ideal B) (p : Ideal A) [hPp : P.LiesOver p]

theorem restrictHom_smul_eq_under (g : G) :
    (restrictHom G H R A B g) • P.under A = (g • P).under A := by
  ext
  rw [mem_under, mem_pointwise_smul_iff_inv_smul_mem, mem_pointwise_smul_iff_inv_smul_mem,
    mem_under, ← algebraMap_restrictHom_smul G H R, map_inv]

/--
The natural group homomorphism from the decomposition group of `P` to the decomposition group of
`p`, induced by the restriction homomorphism `IsGaloisGroup.restrictHom : G →* H`.
-/
@[simps!]
noncomputable def stabilizerMapOfLiesOver : stabilizer G P →* stabilizer H p :=
  ((restrictHom G H R A B).restrict _).codRestrict _ fun ⟨g, hg⟩ ↦ by
    rw [MonoidHom.restrict_apply, mem_stabilizer_iff, (liesOver_iff P p).mp hPp,
      restrictHom_smul_eq_under G H R P, hg]

theorem stabilizerMapOfLiesOver_ker :
    (stabilizerMapOfLiesOver G H R P p).ker =
      (restrictHom G H R A B).ker.subgroupOf (stabilizer G P) := by
  simp [stabilizerMapOfLiesOver]

theorem stabilizerMapOfLiesOver_surjective [IsIntegrallyClosed A] [P.IsPrime] :
    Function.Surjective (stabilizerMapOfLiesOver G H R P p) := by
  intro ⟨h, h_mem⟩
  obtain ⟨g, hg⟩ := restrictHom_surjective G H R A B h
  have : (g⁻¹ • P).LiesOver p := by
    rw [liesOver_iff, ← restrictHom_smul_eq_under G H R P, map_inv, eq_inv_smul_iff, hg, h_mem,
      (liesOver_iff P p).mp hPp]
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p P (g⁻¹ • P) (restrictHom G H R A B).ker
  rw [eq_inv_smul_iff] at hτ
  refine ⟨⟨g * τ, by rwa [mem_stabilizer_iff, mul_smul, ← subgroup_smul_def]⟩, ?_⟩
  simp [Subtype.ext_iff, hg, ← MonoidHom.mem_ker]

/--
The natural group homomorphism from the inertia group of `P` to the inertia group of `p`,
induced by the restriction homomorphism `IsGaloisGroup.restrictHom : G →* H`.
-/
@[simps!]
noncomputable def inertiaMapOfLiesOver : inertia G P →* inertia H p :=
  ((restrictHom G H R A B).restrict _).codRestrict _ fun ⟨g, hg⟩ ↦ by
    rw [over_def P p, under_def, MonoidHom.restrict_apply, AddSubgroup.mem_inertia]
    intro x
    simpa using hg _

theorem inertiaMapOfLiesOver_ker :
    (inertiaMapOfLiesOver G H R P p).ker =
      (restrictHom G H R A B).ker.subgroupOf (inertia G P) := by
  simp [inertiaMapOfLiesOver]

attribute [local instance] Ideal.Quotient.field in
theorem inertiaMapOfLiesOver_surjective [IsIntegrallyClosed A] [P.IsMaximal] :
    Function.Surjective (inertiaMapOfLiesOver G H R P p) := by
  intro ⟨h, hmem⟩
  obtain ⟨⟨g, hg⟩, hg'⟩ :=
    stabilizerMapOfLiesOver_surjective G H R P p ⟨h, inertia_le_stabilizer _ hmem⟩
  have hgh : (restrictHom G H R A B) g = h := congr_arg Subtype.val hg'
  have hfix (a : A) : g • algebraMap A B a - algebraMap A B a ∈ P := by
    rw [← algebraMap_restrictHom_smul G H R A B, ← map_sub, ← Ideal.mem_comap, ← Ideal.under_def,
      ← (liesOver_iff P p).mp hPp, hgh]
    exact AddSubgroup.mem_inertia.mp hmem a
  let σ' := Quotient.stabilizerAlgEquiv P p G ⟨g, hg⟩ hfix
  obtain ⟨⟨τ, hτ⟩, hτ'⟩ := Quotient.stabilizerHom_surjective (restrictHom G H R A B).ker p P σ'⁻¹
  have hτx (x : B) : Quotient.mk P ((τ : G) • x) = σ'⁻¹ (Quotient.mk P x) :=
    hτ' ▸ (Quotient.stabilizerHom_apply P p _ ⟨τ, hτ⟩ x).symm
  refine ⟨⟨g * τ, fun x ↦ ?_⟩, ?_⟩
  · rw [Submodule.mem_toAddSubgroup, ← Quotient.mk_eq_mk_iff_sub_mem, mul_smul,
      ← Quotient.stabilizerAlgEquiv_mk P p G ⟨g, hg⟩ hfix, hτx]
    exact σ'.apply_symm_apply _
  · ext
    simp [hgh, MonoidHom.mem_ker.mp τ.2]

end Ideal
