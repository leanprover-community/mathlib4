/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Antoine Labelle

! This file was ported from Lean 3 source module algebra.module.projective
! leanprover-community/mathlib commit 405ea5cee7a7070ff8fb8dcb4cfb003532e34bce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.LinearAlgebra.Finsupp
import Mathbin.LinearAlgebra.FreeModule.Basic

/-!

# Projective modules

This file contains a definition of a projective module, the proof that
our definition is equivalent to a lifting property, and the
proof that all free modules are projective.

## Main definitions

Let `R` be a ring (or a semiring) and let `M` be an `R`-module.

* `is_projective R M` : the proposition saying that `M` is a projective `R`-module.

## Main theorems

* `is_projective.lifting_property` : a map from a projective module can be lifted along
  a surjection.

* `is_projective.of_lifting_property` : If for all R-module surjections `A →ₗ B`, all
  maps `M →ₗ B` lift to `M →ₗ A`, then `M` is projective.

* `is_projective.of_free` : Free modules are projective

## Implementation notes

The actual definition of projective we use is that the natural R-module map
from the free R-module on the type M down to M splits. This is more convenient
than certain other definitions which involve quantifying over universes,
and also universe-polymorphic (the ring and module can be in different universes).

We require that the module sits in at least as high a universe as the ring:
without this, free modules don't even exist,
and it's unclear if projective modules are even a useful notion.

## References

https://en.wikipedia.org/wiki/Projective_module

## TODO

- Direct sum of two projective modules is projective.
- Arbitrary sum of projective modules is projective.

All of these should be relatively straightforward.

## Tags

projective module

-/


universe u v

open LinearMap Finsupp

/- The actual implementation we choose: `P` is projective if the natural surjection
   from the free `R`-module on `P` to `P` splits. -/
/-- An R-module is projective if it is a direct summand of a free module, or equivalently
  if maps from the module lift along surjections. There are several other equivalent
  definitions. -/
class Module.Projective (R : Type _) [Semiring R] (P : Type _) [AddCommMonoid P] [Module R P] :
  Prop where
  out : ∃ s : P →ₗ[R] P →₀ R, Function.LeftInverse (Finsupp.total P P R id) s
#align module.projective Module.Projective

namespace Module

section Semiring

variable {R : Type _} [Semiring R] {P : Type _} [AddCommMonoid P] [Module R P] {M : Type _}
  [AddCommMonoid M] [Module R M] {N : Type _} [AddCommMonoid N] [Module R N]

theorem projective_def :
    Projective R P ↔ ∃ s : P →ₗ[R] P →₀ R, Function.LeftInverse (Finsupp.total P P R id) s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align module.projective_def Module.projective_def

theorem projective_def' : Projective R P ↔ ∃ s : P →ₗ[R] P →₀ R, Finsupp.total P P R id ∘ₗ s = id :=
  by simp_rw [projective_def, FunLike.ext_iff, Function.LeftInverse, coe_comp, id_coe, id.def]
#align module.projective_def' Module.projective_def'

/-- A projective R-module has the property that maps from it lift along surjections. -/
theorem projective_lifting_property [h : Projective R P] (f : M →ₗ[R] N) (g : P →ₗ[R] N)
    (hf : Function.Surjective f) : ∃ h : P →ₗ[R] M, f.comp h = g :=
  by
  /-
    Here's the first step of the proof.
    Recall that `X →₀ R` is Lean's way of talking about the free `R`-module
    on a type `X`. The universal property `finsupp.total` says that to a map
    `X → N` from a type to an `R`-module, we get an associated R-module map
    `(X →₀ R) →ₗ N`. Apply this to a (noncomputable) map `P → M` coming from the map
    `P →ₗ N` and a random splitting of the surjection `M →ₗ N`, and we get
    a map `φ : (P →₀ R) →ₗ M`.
    -/
  let φ : (P →₀ R) →ₗ[R] M := Finsupp.total _ _ _ fun p => Function.surjInv hf (g p)
  -- By projectivity we have a map `P →ₗ (P →₀ R)`;
  cases' h.out with s hs
  -- Compose to get `P →ₗ M`. This works.
  use φ.comp s
  ext p
  conv_rhs => rw [← hs p]
  simp [φ, Finsupp.total_apply, Function.surjInv_eq hf]
#align module.projective_lifting_property Module.projective_lifting_property

variable {Q : Type _} [AddCommMonoid Q] [Module R Q]

instance [hP : Projective R P] [hQ : Projective R Q] : Projective R (P × Q) :=
  by
  rw [Module.projective_def']
  cases' hP.out with sP hsP
  cases' hQ.out with sQ hsQ
  use coprod (lmap_domain R R (inl R P Q)) (lmap_domain R R (inr R P Q)) ∘ₗ sP.prod_map sQ
  ext <;>
    simp only [coe_inl, coe_inr, coe_comp, Function.comp_apply, prod_map_apply, map_zero,
      coprod_apply, lmap_domain_apply, map_domain_zero, add_zero, zero_add, id_comp,
      total_map_domain]
  · rw [← fst_apply _, apply_total R]
    exact hsP x
  · rw [← snd_apply _, apply_total R]
    exact Finsupp.total_zero_apply _ (sP x)
  · rw [← fst_apply _, apply_total R]
    exact Finsupp.total_zero_apply _ (sQ x)
  · rw [← snd_apply _, apply_total R]
    exact hsQ x

variable {ι : Type _} (A : ι → Type _) [∀ i : ι, AddCommMonoid (A i)] [∀ i : ι, Module R (A i)]

instance [h : ∀ i : ι, Projective R (A i)] : Projective R (Π₀ i, A i) := by
  classical
    rw [Module.projective_def']
    simp_rw [projective_def] at h
    choose s hs using h
    letI : ∀ i : ι, AddCommMonoid (A i →₀ R) := fun i => by infer_instance
    letI : ∀ i : ι, Module R (A i →₀ R) := fun i => by infer_instance
    letI : AddCommMonoid (Π₀ i : ι, A i →₀ R) := @Dfinsupp.addCommMonoid ι (fun i => A i →₀ R) _
    letI : Module R (Π₀ i : ι, A i →₀ R) := @Dfinsupp.module ι R (fun i => A i →₀ R) _ _ _
    let f i := lmap_domain R R (Dfinsupp.single i : A i → Π₀ i, A i)
    use Dfinsupp.coprodMap f ∘ₗ Dfinsupp.mapRange.linearMap s
    ext (i x j)
    simp only [Dfinsupp.coprodMap, DirectSum.lof, total_map_domain, coe_comp, coe_lsum, id_coe,
      LinearEquiv.coe_toLinearMap, finsuppLequivDfinsupp_symm_apply, Function.comp_apply,
      Dfinsupp.lsingle_apply, Dfinsupp.mapRange.linearMap_apply, Dfinsupp.mapRange_single,
      lmap_domain_apply, Dfinsupp.toFinsupp_single, Finsupp.sum_single_index, id.def,
      Function.comp.left_id, Dfinsupp.single_apply]
    rw [← Dfinsupp.lapply_apply j, apply_total R]
    obtain rfl | hij := eq_or_ne i j
    · convert(hs i) x
      · ext
        simp
      · simp
    · convert Finsupp.total_zero_apply _ ((s i) x)
      · ext
        simp [hij]
      · simp [hij]

end Semiring

section Ring

variable {R : Type _} [Ring R] {P : Type _} [AddCommGroup P] [Module R P]

/-- Free modules are projective. -/
theorem projectiveOfBasis {ι : Type _} (b : Basis ι R P) : Projective R P :=
  by
  -- need P →ₗ (P →₀ R) for definition of projective.
  -- get it from `ι → (P →₀ R)` coming from `b`.
  use b.constr ℕ fun i => Finsupp.single (b i) (1 : R)
  intro m
  simp only [b.constr_apply, mul_one, id.def, Finsupp.smul_single', Finsupp.total_single,
    LinearMap.map_finsupp_sum]
  exact b.total_repr m
#align module.projective_of_basis Module.projectiveOfBasis

instance (priority := 100) projectiveOfFree [Module.Free R P] : Module.Projective R P :=
  projectiveOfBasis <| Module.Free.chooseBasis R P
#align module.projective_of_free Module.projectiveOfFree

end Ring

--This is in a different section because special universe restrictions are required.
section OfLiftingProperty

/-- A module which satisfies the universal property is projective. Note that the universe variables
in `huniv` are somewhat restricted. -/
theorem projectiveOfLiftingProperty' {R : Type u} [Semiring R] {P : Type max u v} [AddCommMonoid P]
    [Module R P]
    -- If for all surjections of `R`-modules `M →ₗ N`, all maps `P →ₗ N` lift to `P →ₗ M`,
    (huniv :
      ∀ {M : Type max v u} {N : Type max u v} [AddCommMonoid M] [AddCommMonoid N],
        ∀ [Module R M] [Module R N],
          ∀ (f : M →ₗ[R] N) (g : P →ₗ[R] N),
            Function.Surjective f → ∃ h : P →ₗ[R] M, f.comp h = g) :-- then `P` is projective.
      Projective
      R P :=
  by
  -- let `s` be the universal map `(P →₀ R) →ₗ P` coming from the identity map `P →ₗ P`.
  obtain ⟨s, hs⟩ : ∃ s : P →ₗ[R] P →₀ R, (Finsupp.total P P R id).comp s = LinearMap.id :=
    huniv (Finsupp.total P P R (id : P → P)) (LinearMap.id : P →ₗ[R] P) _
  -- This `s` works.
  · use s
    rwa [LinearMap.ext_iff] at hs
  · intro p
    use Finsupp.single p 1
    simp
#align module.projective_of_lifting_property' Module.projectiveOfLiftingProperty'

/-- A variant of `of_lifting_property'` when we're working over a `[ring R]`,
which only requires quantifying over modules with an `add_comm_group` instance. -/
theorem projectiveOfLiftingProperty {R : Type u} [Ring R] {P : Type max u v} [AddCommGroup P]
    [Module R P]
    -- If for all surjections of `R`-modules `M →ₗ N`, all maps `P →ₗ N` lift to `P →ₗ M`,
    (huniv :
      ∀ {M : Type max v u} {N : Type max u v} [AddCommGroup M] [AddCommGroup N],
        ∀ [Module R M] [Module R N],
          ∀ (f : M →ₗ[R] N) (g : P →ₗ[R] N),
            Function.Surjective f → ∃ h : P →ₗ[R] M, f.comp h = g) :-- then `P` is projective.
      Projective
      R P :=
  by
  -- We could try and prove this *using* `of_lifting_property`,
  -- but this quickly leads to typeclass hell,
  -- so we just prove it over again.
  -- let `s` be the universal map `(P →₀ R) →ₗ P` coming from the identity map `P →ₗ P`.
  obtain ⟨s, hs⟩ : ∃ s : P →ₗ[R] P →₀ R, (Finsupp.total P P R id).comp s = LinearMap.id :=
    huniv (Finsupp.total P P R (id : P → P)) (LinearMap.id : P →ₗ[R] P) _
  -- This `s` works.
  · use s
    rwa [LinearMap.ext_iff] at hs
  · intro p
    use Finsupp.single p 1
    simp
#align module.projective_of_lifting_property Module.projectiveOfLiftingProperty

end OfLiftingProperty

end Module

