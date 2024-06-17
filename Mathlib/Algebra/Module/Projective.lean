/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Antoine Labelle
-/
import Mathlib.Algebra.Module.Defs
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

#align_import algebra.module.projective from "leanprover-community/mathlib"@"405ea5cee7a7070ff8fb8dcb4cfb003532e34bce"

/-!

# Projective modules

This file contains a definition of a projective module, the proof that
our definition is equivalent to a lifting property, and the
proof that all free modules are projective.

## Main definitions

Let `R` be a ring (or a semiring) and let `M` be an `R`-module.

* `Module.Projective R M` : the proposition saying that `M` is a projective `R`-module.

## Main theorems

* `Module.projective_lifting_property` : a map from a projective module can be lifted along
  a surjection.

* `Module.Projective.of_lifting_property` : If for all R-module surjections `A →ₗ B`, all
  maps `M →ₗ B` lift to `M →ₗ A`, then `M` is projective.

* `Module.Projective.of_free` : Free modules are projective

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

open LinearMap hiding id
open Finsupp

/- The actual implementation we choose: `P` is projective if the natural surjection
   from the free `R`-module on `P` to `P` splits. -/
/-- An R-module is projective if it is a direct summand of a free module, or equivalently
  if maps from the module lift along surjections. There are several other equivalent
  definitions. -/
class Module.Projective (R : Type*) [Semiring R] (P : Type*) [AddCommMonoid P] [Module R P] :
    Prop where
  out : ∃ s : P →ₗ[R] P →₀ R, Function.LeftInverse (Finsupp.total P P R id) s
#align module.projective Module.Projective

namespace Module

section Semiring

variable {R : Type*} [Semiring R] {P : Type*} [AddCommMonoid P] [Module R P] {M : Type*}
  [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]

theorem projective_def :
    Projective R P ↔ ∃ s : P →ₗ[R] P →₀ R, Function.LeftInverse (Finsupp.total P P R id) s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align module.projective_def Module.projective_def

theorem projective_def' :
    Projective R P ↔ ∃ s : P →ₗ[R] P →₀ R, Finsupp.total P P R id ∘ₗ s = .id := by
  simp_rw [projective_def, DFunLike.ext_iff, Function.LeftInverse, comp_apply, id_apply]
#align module.projective_def' Module.projective_def'

/-- A projective R-module has the property that maps from it lift along surjections. -/
theorem projective_lifting_property [h : Projective R P] (f : M →ₗ[R] N) (g : P →ₗ[R] N)
    (hf : Function.Surjective f) : ∃ h : P →ₗ[R] M, f.comp h = g := by
  /-
    Here's the first step of the proof.
    Recall that `X →₀ R` is Lean's way of talking about the free `R`-module
    on a type `X`. The universal property `Finsupp.total` says that to a map
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
  simp [φ, Finsupp.total_apply, Function.surjInv_eq hf, map_finsupp_sum]
#align module.projective_lifting_property Module.projective_lifting_property

/-- A module which satisfies the universal property is projective: If all surjections of
`R`-modules `(P →₀ R) →ₗ[R] P` have `R`-linear left inverse maps, then `P` is
projective. -/
theorem Projective.of_lifting_property'' {R : Type u} [Semiring R] {P : Type v} [AddCommMonoid P]
    [Module R P] (huniv : ∀ (f : (P →₀ R) →ₗ[R] P), Function.Surjective f →
      ∃ h : P →ₗ[R] (P →₀ R), f.comp h = .id) :
    Projective R P :=
  projective_def'.2 <| huniv (Finsupp.total P P R (id : P → P))
    (total_surjective _ Function.surjective_id)

variable {Q : Type*} [AddCommMonoid Q] [Module R Q]

instance [Projective R P] [Projective R Q] : Projective R (P × Q) := by
  refine .of_lifting_property'' fun f hf ↦ ?_
  rcases projective_lifting_property f (.inl _ _ _) hf with ⟨g₁, hg₁⟩
  rcases projective_lifting_property f (.inr _ _ _) hf with ⟨g₂, hg₂⟩
  refine ⟨coprod g₁ g₂, ?_⟩
  rw [LinearMap.comp_coprod, hg₁, hg₂, LinearMap.coprod_inl_inr]

variable {ι : Type*} (A : ι → Type*) [∀ i : ι, AddCommMonoid (A i)] [∀ i : ι, Module R (A i)]

instance [h : ∀ i : ι, Projective R (A i)] : Projective R (Π₀ i, A i) :=
  .of_lifting_property'' fun f hf ↦ by
    classical
      choose g hg using fun i ↦ projective_lifting_property f (DFinsupp.lsingle i) hf
      replace hg : ∀ i x, f (g i x) = DFinsupp.single i x := fun i ↦ DFunLike.congr_fun (hg i)
      refine ⟨DFinsupp.coprodMap g, ?_⟩
      ext i x j
      simp only [comp_apply, id_apply, DFinsupp.lsingle_apply, DFinsupp.coprodMap_apply_single, hg]

end Semiring

section Ring

variable {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module R P]

/-- Free modules are projective. -/
theorem Projective.of_basis {ι : Type*} (b : Basis ι R P) : Projective R P := by
  -- need P →ₗ (P →₀ R) for definition of projective.
  -- get it from `ι → (P →₀ R)` coming from `b`.
  use b.constr ℕ fun i => Finsupp.single (b i) (1 : R)
  intro m
  simp only [b.constr_apply, mul_one, id, Finsupp.smul_single', Finsupp.total_single,
    map_finsupp_sum]
  exact b.total_repr m
#align module.projective_of_basis Module.Projective.of_basis

instance (priority := 100) Projective.of_free [Module.Free R P] : Module.Projective R P :=
  .of_basis <| Module.Free.chooseBasis R P
#align module.projective_of_free Module.Projective.of_free

variable {R₀ M N} [CommRing R₀] [Algebra R₀ R] [AddCommGroup M] [Module R₀ M] [Module R M]
variable [IsScalarTower R₀ R M] [AddCommGroup N] [Module R₀ N]

theorem Projective.of_split [Module.Projective R M]
    (i : P →ₗ[R] M) (s : M →ₗ[R] P) (H : s.comp i = LinearMap.id) : Module.Projective R P := by
  obtain ⟨g, hg⟩ := projective_lifting_property (Finsupp.total P P R id) s
    (fun x ↦ ⟨Finsupp.single x 1, by simp⟩)
  refine ⟨g.comp i, fun x ↦ ?_⟩
  rw [LinearMap.comp_apply, ← LinearMap.comp_apply, hg,
    ← LinearMap.comp_apply, H, LinearMap.id_apply]

theorem Projective.of_equiv [Module.Projective R M]
    (e : M ≃ₗ[R] P) : Module.Projective R P :=
  Projective.of_split e.symm e.toLinearMap (by ext; simp)

/-- A module is projective iff it is the direct summand of a free module. -/
theorem Projective.iff_split : Module.Projective R P ↔
    ∃ (M : Type max u v) (_ : AddCommGroup M) (_ : Module R M) (_ : Module.Free R M)
      (i : P →ₗ[R] M) (s : M →ₗ[R] P), s.comp i = LinearMap.id :=
  ⟨fun ⟨i, hi⟩ ↦ ⟨P →₀ R, _, _, inferInstance, i, Finsupp.total P P R id, LinearMap.ext hi⟩,
    fun ⟨_, _, _, _, i, s, H⟩ ↦ Projective.of_split i s H⟩

/-- A quotient of a projective module is projective iff it is a direct summand. -/
theorem Projective.iff_split_of_projective [Module.Projective R M] (s : M →ₗ[R] P)
    (hs : Function.Surjective s) :
    Module.Projective R P ↔ ∃ i, s ∘ₗ i = LinearMap.id :=
  ⟨fun _ ↦ projective_lifting_property _ _ hs, fun ⟨i, H⟩ ↦ Projective.of_split i s H⟩

set_option maxSynthPendingDepth 2 in
open TensorProduct in
instance Projective.tensorProduct [hM : Module.Projective R M] [hN : Module.Projective R₀ N] :
    Module.Projective R (M ⊗[R₀] N) := by
  obtain ⟨sM, hsM⟩ := hM
  obtain ⟨sN, hsN⟩ := hN
  have : Module.Projective R (M ⊗[R₀] (N →₀ R₀)) := by
    fapply Projective.of_split (R := R) (M := ((M →₀ R) ⊗[R₀] (N →₀ R₀)))
    · exact (AlgebraTensorModule.map sM (LinearMap.id (R := R₀) (M := N →₀ R₀)))
    · exact (AlgebraTensorModule.map
        (Finsupp.total M M R id) (LinearMap.id (R := R₀) (M := N →₀ R₀)))
    · ext; simp [hsM _]
  fapply Projective.of_split (R := R) (M := (M ⊗[R₀] (N →₀ R₀)))
  · exact (AlgebraTensorModule.map (LinearMap.id (R := R) (M := M)) sN)
  · exact (AlgebraTensorModule.map (LinearMap.id (R := R) (M := M)) (Finsupp.total N N R₀ id))
  · ext; simp [hsN _]

end Ring

--This is in a different section because special universe restrictions are required.
section OfLiftingProperty

-- Porting note (#11215): TODO: generalize to `P : Type v`?
/-- A module which satisfies the universal property is projective. Note that the universe variables
in `huniv` are somewhat restricted. -/
theorem Projective.of_lifting_property' {R : Type u} [Semiring R] {P : Type max u v}
    [AddCommMonoid P] [Module R P]
    -- If for all surjections of `R`-modules `M →ₗ N`, all maps `P →ₗ N` lift to `P →ₗ M`,
    (huniv : ∀ {M : Type max v u} {N : Type max u v} [AddCommMonoid M] [AddCommMonoid N]
      [Module R M] [Module R N] (f : M →ₗ[R] N) (g : P →ₗ[R] N),
        Function.Surjective f → ∃ h : P →ₗ[R] M, f.comp h = g) :
    -- then `P` is projective.
    Projective R P :=
  .of_lifting_property'' (huniv · _)
#align module.projective_of_lifting_property' Module.Projective.of_lifting_property'

-- Porting note (#11215): TODO: generalize to `P : Type v`?
/-- A variant of `of_lifting_property'` when we're working over a `[Ring R]`,
which only requires quantifying over modules with an `AddCommGroup` instance. -/
theorem Projective.of_lifting_property {R : Type u} [Ring R] {P : Type max u v} [AddCommGroup P]
    [Module R P]
    -- If for all surjections of `R`-modules `M →ₗ N`, all maps `P →ₗ N` lift to `P →ₗ M`,
    (huniv : ∀ {M : Type max v u} {N : Type max u v} [AddCommGroup M] [AddCommGroup N]
      [Module R M] [Module R N] (f : M →ₗ[R] N) (g : P →ₗ[R] N),
        Function.Surjective f → ∃ h : P →ₗ[R] M, f.comp h = g) :
    -- then `P` is projective.
    Projective R P :=
  .of_lifting_property'' (huniv · _)
#align module.projective_of_lifting_property Module.Projective.of_lifting_property

end OfLiftingProperty

end Module
