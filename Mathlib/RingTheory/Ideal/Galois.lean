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

variable (G H : Type*) [Group G] [Group H] [Finite G] [Finite H] (R A : Type*) {B : Type*}
  [CommRing R] [CommRing A] [CommRing B] [IsDomain B] [Algebra R A] [Algebra A B] [Algebra R B]
  [IsScalarTower R A B] [FaithfulSMul R A] [FaithfulSMul A B] [MulSemiringAction G B]
  [IsGaloisGroup G R B] [MulSemiringAction H A] [IsGaloisGroup H R A]
  (P : Ideal B) (p : Ideal A) [hPp : P.LiesOver p]

theorem toto (g : G) :
    (restrictHom G H R A B g) • p = (g • P).under A := by
  ext
  rw [mem_under, mem_pointwise_smul_iff_inv_smul_mem, mem_pointwise_smul_iff_inv_smul_mem,
    ← algebraMap_restrictHom_smul G H R, ← mem_comap, map_inv,
    (liesOver_iff P p).mp hPp]

/--
The natural group homomorphism from the decomposition group of `P` to the decomposition group of
`p`, induced by the restriction homomorphism `IsGaloisGroup.restrictHom : G →* H`.
-/
@[simps!]
noncomputable def stabilizerMapOfLiesOver : stabilizer G P →* stabilizer H p :=
  ((restrictHom G H R A B).restrict _).codRestrict _ fun ⟨g, hg⟩ ↦ by
    rw [MonoidHom.restrict_apply, mem_stabilizer_iff, toto G H R A P, (liesOver_iff P p).mp hPp, hg]

theorem stabilizerMapOfLiesOver_surjective [P.IsPrime] :
    Function.Surjective (stabilizerMapOfLiesOver G H R A P p) := by
  intro ⟨h, h_mem⟩
  obtain ⟨g, hg⟩ := restrictHom_surjective G H R A B h
  have : (g⁻¹ • P).LiesOver p := sorry
  
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p P (g⁻¹ • P) G
  refine ⟨⟨g, ?_⟩, ?_⟩
  ·
    sorry
  · rw [Subtype.ext_iff]
    simpa



theorem stabilizerMapOfLiesOver_ker :
    (stabilizerMapOfLiesOver G H R A P p).ker =
      (IsGaloisGroup.restrictHom G H R A B).ker.subgroupOf (stabilizer G P) := by
  sorry

/--
The natural group homomorphism from the inertia group of `P` to the inertia group of `p`,
induced by the restriction homomorphism `IsGaloisGroup.restrictHom : G →* H`.
-/
noncomputable def inertiaMapOfLiesOver : inertia G P →* inertia H p :=
  ((IsGaloisGroup.restrictHom G H R A B).restrict _).codRestrict _ fun ⟨g, hg⟩ ↦ by
    sorry

theorem inertiaMapOfLiesOver_surjective :
    Function.Surjective (inertiaMapOfLiesOver G H R A P p) := by
  sorry

theorem inertiaMapOfLiesOver_ker :
    (inertiaMapOfLiesOver G H R A P p).ker =
      (IsGaloisGroup.restrictHom G H R A B).ker.subgroupOf (inertia G P) := by
  sorry

end Ideal
