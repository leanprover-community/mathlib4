/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury, Scott Carnahan
-/
import Mathlib.LinearAlgebra.PerfectPairing
import Mathlib.LinearAlgebra.Reflection

/-!
# Root data and root systems

This file contains basic definitions for root systems and root data.

## Main definitions:

 * `RootPairing`: Given two perfectly-paired `R`-modules `M` and `N` (over some commutative ring
   `R`) a root pairing with indexing set `ι` is the data of an `ι`-indexed subset of `M`
   ("the roots") an `ι`-indexed subset of `N` ("the coroots"), and an `ι`-indexed set of
   permutations of `ι` such that each root-coroot pair
   evaluates to `2`, and the permutation attached to each element of `ι` is compatible with the
   reflections on the corresponding roots and coroots.
 * `RootDatum`: A root datum is a root pairing for which the roots and coroots take values in
   finitely-generated free Abelian groups.
 * `RootSystem`: A root system is a root pairing for which the roots span their ambient module.
 * `RootPairing.IsCrystallographic`: A root pairing is said to be crystallographic if the pairing
   between a root and coroot is always an integer.
 * `RootPairing.IsReduced`: A root pairing is said to be reduced if it never contains the double of
   a root.

## Todo

* Put more API theorems in the Defs file.
* Introduce the Weyl Group, and its action on the indexing set.
* Base change of root pairings (may need flatness).
* Isomorphism of root pairings.
* Crystallographic root systems are isomorphic to base changes of root systems over `ℤ`: Take
  `M₀` and `N₀` to be the `ℤ`-span of roots and coroots.

## Implementation details

A root datum is sometimes defined as two subsets: roots and coroots, together with a bijection
between them, subject to hypotheses. However the hypotheses ensure that the bijection is unique and
so the question arises of whether this bijection should be part of the data of a root datum or
whether one should merely assert its existence. For root systems, things are even more extreme: the
coroots are uniquely determined by the roots. Furthermore a root system induces a canonical
non-degenerate bilinear form on the ambient space and many informal accounts even include this form
as part of the data.

We have opted for a design in which some of the uniquely-determined data is included: the bijection
between roots and coroots is (implicitly) included and the coroots are included for root systems.
Empirically this seems to be by far the most convenient design and by providing extensionality
lemmas expressing the uniqueness we expect to get the best of both worlds.


Furthermore, we require roots and coroots to be injections from a base indexing type `ι` rather than
subsets of their codomains. This design was chosen to avoid the bijection between roots and coroots
being a dependently-typed object. A third option would be to have the roots and coroots be subsets
but to avoid having a dependently-typed bijection by defining it globally with junk value `0`
outside of the roots and coroots. This would work but lacks the convenient symmetry that the chosen
design enjoys: by introducing the indexing type `ι`, one does not have to pick a direction
(`roots → coroots` or `coroots → roots`) for the forward direction of the bijection. Besides,
providing the user with the additional definitional power to specify an indexing type `ι` is a
benefit and the junk-value pattern is a cost.

As a final point of divergence from the classical literature, we make the reflection permutation on
roots and coroots explicit, rather than specifying only that reflection preserves the sets of roots
and coroots. This is necessary when working with infinite root systems, where the coroots are not
uniquely determined by the roots, because without it, the reflection permutations on roots and
coroots may not correspond. For this purpose, we define a map from `ι` to permutations on `ι`, and
require that it is compatible with reflections and coreflections.

-/

open Set Function
open Module hiding reflection
open Submodule (span)
open AddSubgroup (zmultiples)

noncomputable section

variable (ι R M N : Type*)
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Given two perfectly-paired `R`-modules `M` and `N`, a root pairing with indexing set `ι`
is the data of an `ι`-indexed subset of `M` ("the roots"), an `ι`-indexed subset of `N`
("the coroots"), and an `ι`-indexed set of permutations of `ι`, such that each root-coroot pair
evaluates to `2`, and the permutation attached to each element of `ι` is compatible with the
reflections on the corresponding roots and coroots.

It exists to allow for a convenient unification of the theories of root systems and root data. -/
structure RootPairing extends PerfectPairing R M N :=
  /-- A parametrized family of vectors, called roots. -/
  root : ι ↪ M
  /-- A parametrized family of dual vectors, called coroots. -/
  coroot : ι ↪ N
  root_coroot_two : ∀ i, toLin (root i) (coroot i) = 2
  /-- A parametrized family of permutations, induced by reflection. -/
  reflection_perm : ι → (ι ≃ ι)
  reflection_perm_root : ∀ i j,
    (preReflection (root i) (toLin.flip (coroot i))) (root j) = root ((reflection_perm i) j)
  reflection_perm_coroot : ∀ i j,
    (preReflection (coroot i) (toLin (root i))) (coroot j) = coroot ((reflection_perm i) j)

/-- A root datum is a root pairing with coefficients in the integers and for which the root and
coroot spaces are finitely-generated free Abelian groups.

Note that the latter assumptions `[Free ℤ X₁] [Finite ℤ X₁] [Free ℤ X₂] [Finite ℤ X₂]` should be
supplied as mixins. -/
abbrev RootDatum (X₁ X₂ : Type*) [AddCommGroup X₁] [AddCommGroup X₂] := RootPairing ι ℤ X₁ X₂

/-- A root system is a root pairing for which the roots span their ambient module.

Note that this is slightly more general than the usual definition in the sense that `N` is not
required to be the dual of `M`. -/
structure RootSystem extends RootPairing ι R M N :=
  span_eq_top : span R (range root) = ⊤

namespace RootPairing

variable {ι R M N}
variable (P : RootPairing ι R M N) (i j : ι)

lemma eq_of_root (h : P.root i = P.root j) : i = j :=
  (EmbeddingLike.apply_eq_iff_eq P.root).mp h

lemma root_ne (h: i ≠ j) : P.root i ≠ P.root j :=
  fun h' ↦ h (eq_of_root P i j h')

lemma ne_zero [CharZero R] : (P.root i : M) ≠ 0 :=
  fun h ↦ by simpa [h] using P.root_coroot_two i

lemma ne_zero' [CharZero R] : (P.coroot i : N) ≠ 0 :=
  fun h ↦ by simpa [h] using P.root_coroot_two i

/-- If we interchange the roles of `M` and `N`, we still have a root pairing. -/
protected def flip : RootPairing ι R N M :=
  { P.toPerfectPairing.flip with
    root := P.coroot
    coroot := P.root
    root_coroot_two := P.root_coroot_two
    reflection_perm := P.reflection_perm
    reflection_perm_root := P.reflection_perm_coroot
    reflection_perm_coroot := P.reflection_perm_root }

@[simp]
lemma flip_flip : P.flip.flip = P :=
  rfl

/-- This is the pairing between roots and coroots. -/
def pairing : R :=
    P.toLin (P.root i) (P.coroot j)

@[simp]
lemma root_coroot_eq_pairing : P.toLin (P.root i) (P.coroot j) = P.pairing i j :=
  rfl

lemma coroot_root_eq_pairing : P.toLin.flip (P.coroot i) (P.root j) = P.pairing j i := by
  simp

@[simp]
lemma pairing_same : P.pairing i i = 2 := P.root_coroot_two i

lemma coroot_root_two :
    P.toLin.flip (P.coroot i) (P.root i) = 2 := by
  simp

/-- The reflection associated to a root. -/
def reflection : M ≃ₗ[R] M :=
  Module.reflection (P.flip.root_coroot_two i)

@[simp]
lemma prereflection_eq_reflection :
    (Module.preReflection (P.root i) (P.toLin.flip (P.coroot i))) = P.reflection i := rfl

@[simp]
lemma root_reflection_perm (j : ι) :
    P.root ((P.reflection_perm i) j) = (P.reflection i) (P.root j) :=
  (P.reflection_perm_root i j).symm

theorem reflection_mapsto_root : MapsTo (P.reflection i) (range P.root) (range P.root) := by
  intro x hx
  obtain ⟨j, hj⟩ := hx
  rw [← hj, ← P.root_reflection_perm i j]
  exact mem_range_self ((P.reflection_perm i) j)

lemma reflection_apply (x : M) :
    P.reflection i x = x - (P.toLin x (P.coroot i)) • P.root i :=
  rfl

lemma reflection_apply_root :
    P.reflection i (P.root j) = P.root j - (P.pairing j i) • P.root i :=
  rfl

@[simp]
lemma reflection_apply_self :
    P.reflection i (P.root i) = - P.root i :=
  Module.reflection_apply_self (P.coroot_root_two i)

@[simp]
lemma reflection_same (x : M) : P.reflection i (P.reflection i x) = x :=
  Module.involutive_reflection (P.coroot_root_two i) x

lemma reflection_mul (x : M) :
    (P.reflection i * P.reflection j) x = P.reflection i (P.reflection j x) := rfl

lemma reflection_invOn_self : InvOn (P.reflection i) (P.reflection i) (range P.root)
    (range P.root) := by
  constructor <;>
    exact fun x _ => Module.involutive_reflection (P.coroot_root_two i) x

lemma bijOn_reflection_root : BijOn (P.reflection i) (range P.root) (range P.root) := InvOn.bijOn
  (reflection_invOn_self P i) (P.reflection_mapsto_root i) (P.reflection_mapsto_root i)

@[simp]
lemma reflection_image_eq :
    P.reflection i '' (range P.root) = range P.root :=
  (P.bijOn_reflection_root i).image_eq

/-- The reflection associated to a coroot. -/
def coreflection : N ≃ₗ[R] N :=
  Module.reflection (P.root_coroot_two i)


lemma coreflection_apply (f : N) :
    P.coreflection i f = f - (P.toLin (P.root i) f) • P.coroot i :=
  rfl

@[simp]
lemma coreflection_apply_self :
    P.coreflection i (P.coroot i) = - P.coroot i :=
  Module.reflection_apply_self (P.flip.coroot_root_two i)

lemma coreflection_eq_flip_reflection (f : N) : P.coreflection i f = P.flip.reflection i f :=
  rfl

@[simp]
lemma coreflection_self (x : N) : P.coreflection i (P.coreflection i x) = x :=
  reflection_same P.flip i x

lemma coreflection_invOn_self : InvOn (P.coreflection i) (P.coreflection i) (range P.coroot)
    (range P.coroot) := reflection_invOn_self P.flip i

lemma bijOn_coreflection_coroot : BijOn (P.coreflection i) (range P.coroot) (range P.coroot) :=
  bijOn_reflection_root P.flip i

@[simp]
lemma coreflection_image_eq :
    P.coreflection i '' (range P.coroot) = range P.coroot :=
  (P.bijOn_coreflection_coroot i).image_eq

lemma reflection_dualMap_eq_coreflection :
    (P.reflection i).dualMap ∘ₗ P.toLin.flip = P.toLin.flip ∘ₗ P.coreflection i := by
  ext n m
  simp [coreflection_apply, reflection_apply, mul_comm (P.toLin m (P.coroot i))]

/-- A root pairing is said to be crystallographic if the pairing between a root and coroot is
always an integer. -/
def IsCrystallographic : Prop :=
  ∀ i, MapsTo (P.toLin (P.root i)) (range P.coroot) (zmultiples (1 : R))

lemma isCrystallographic_iff :
    P.IsCrystallographic ↔ ∀ i j, ∃ z : ℤ, z = P.pairing i j := by
  rw [IsCrystallographic]
  refine ⟨fun h i j ↦ ?_, fun h i _ ⟨j, hj⟩ ↦ ?_⟩
  · simpa [AddSubgroup.mem_zmultiples_iff] using h i (mem_range_self j)
  · simpa [← hj, AddSubgroup.mem_zmultiples_iff] using h i j

/-- A root pairing is said to be reduced if any linearly dependent pair of roots is related by a
sign. -/
def IsReduced : Prop :=
  ∀ i j, ¬ LinearIndependent R ![P.root i, P.root j] → (P.root i = P.root j ∨ P.root i = - P.root j)

lemma isReduced_iff : P.IsReduced ↔ ∀ (i j : ι), i ≠ j →
    ¬ LinearIndependent R ![P.root i, P.root j] → P.root i = - P.root j := by
  rw [IsReduced]
  refine ⟨fun h i j hij hLin ↦ ?_, fun h i j hLin  ↦ ?_⟩
  · specialize h i j hLin
    simp_all only [ne_eq, EmbeddingLike.apply_eq_iff_eq, false_or]
  · by_cases h' : i = j
    · exact Or.inl (congrArg (⇑P.root) h')
    · exact Or.inr (h i j h' hLin)

/-- The Coxeter Weight of a pair gives the weight of an edge in a Coxeter diagram, when it is
finite.  It is `4 cos² θ`, where `θ` describes the dihedral angle between hyperplanes. -/
def coxeterWeight : R := pairing P i j * pairing P j i

lemma coxeterWeight_swap : coxeterWeight P i j = coxeterWeight P j i := by
  simp only [coxeterWeight, mul_comm]

/-- Two roots are orthogonal when they are fixed by each others' reflections. -/
def IsOrthogonal : Prop := pairing P i j = 0 ∧ pairing P j i = 0

lemma IsOrthogonal.symm : IsOrthogonal P i j ↔ IsOrthogonal P j i := by
  simp only [IsOrthogonal, and_comm]

lemma IsOrthogonal_comm (h : IsOrthogonal P i j) : Commute (P.reflection i) (P.reflection j) := by
  rw [Commute, SemiconjBy]
  ext v
  simp_all only [IsOrthogonal, reflection_mul, reflection_apply, smul_sub]
  simp_all only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    root_coroot_eq_pairing, smul_eq_mul, mul_zero, sub_zero]
  exact sub_right_comm v ((P.toLin v) (P.coroot j) • P.root j)
      ((P.toLin v) (P.coroot i) • P.root i)

end RootPairing

section reflection_perm

variable {ι R M N}
variable (P : PerfectPairing R M N) (root : ι ↪ M) (coroot : ι ↪ N) (i j : ι)

theorem preReflection_self (hp : ∀ i, P.toLin (root i) (coroot i) = 2) :
    (preReflection (root i) (P.toLin.flip (coroot i)))
      ((preReflection (root i) (P.toLin.flip (coroot i))) (root j)) = root j := by
  have hpf : ∀ i, P.flip.toLin (coroot i) (root i) = 2 := hp
  have h : preReflection (root i) (P.toLin.flip (coroot i)) = Module.reflection (hpf i) := rfl
  rw [h, LinearEquiv.coe_toLinearMap]
  exact (LinearEquiv.eq_symm_apply (Module.reflection (hpf i))).mp rfl

theorem exist_root_reflection
    (h : ∀ i, MapsTo (preReflection (root i) (P.toLin.flip (coroot i))) (range root) (range root)) :
    ∃ k, (preReflection (root i) (P.toLin.flip (coroot i))) (root j) = root k := by
  refine exists_range_iff.mp <| exists_eq_right'.mpr ?_
  simp_all only [mapsTo_range_iff, mem_range]

theorem root_reflection_comp_self (hp : ∀ i, P.toLin (root i) (coroot i) = 2)
    (h : ∀ i, MapsTo (preReflection (root i) (P.toLin.flip (coroot i))) (range root) (range root)) :
    (exist_root_reflection P root coroot i
      (exist_root_reflection P root coroot i j h).choose h).choose = j := by
  refine (Embedding.injective root) ?_
  rw [← (exist_root_reflection P root coroot i _ h).choose_spec,
    ← (exist_root_reflection P root coroot i j h).choose_spec]
  simp_all only [mapsTo_range_iff, mem_range]
  exact preReflection_self P root coroot i j hp

/-- The bijection on the indexing set induced by reflection. -/
@[simps]
def reflection_in (P : PerfectPairing R M N) (root : ι ↪ M) (coroot : ι ↪ N)
    (hp : ∀ i, P.toLin (root i) (coroot i) = 2) (hs : ∀ i, MapsTo (preReflection (root i)
    (P.toLin.flip (coroot i))) (range root) (range root)) : ι ≃ ι where
  toFun j := (exist_root_reflection P root coroot i j hs).choose
  invFun j := (exist_root_reflection P root coroot i j hs).choose
  left_inv j := root_reflection_comp_self P root coroot i j hp hs
  right_inv j := root_reflection_comp_self P root coroot i j hp hs

end reflection_perm
