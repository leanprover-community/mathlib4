/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Will Sawin
-/
import Mathlib.Topology.Algebra.Module.Basic

/-!
# An "action topology" for modules over a topological ring

If `R` is a topological group (or even just a topological space) acting on an additive
abelian group `A`, we define the *action topology* to be the finest topology on `A`
making `• : R × A → A` and `+ : A × A → A` continuous (with all the products having the
product topology).

This topology was suggested by Will Sawin [here](https://mathoverflow.net/a/477763/1384).

## Mathematical details

I (buzzard) don't know of any reference for this other than Sawin's mathoverflow answer,
so I expand some of the details here.

First note that there *is* a finest topology with this property! Indeed, topologies on a fixed
type form a complete lattice (infinite infs and sups exist). So if `τ` is the Inf of all
the topologies on `A` which make `+` and `•` continuous, then the claim is that `+` and `•`
are still continuous for `τ` (note that topologies are ordered so that finer topologies
are smaller). To show `+ : A × A → A` is continuous we equivalently need to show
that the pushforward of the product topology `τ × τ` along `+` is `≤ τ`, and because `τ` is
the greatest lower bound of the topologies making `•` and `+` continuous,
it suffices to show that it's `≤ σ` for any topology `σ` on `A` which makes `+` and `•` continuous.
However pushforward and products are monotone, so `τ × τ ≤ σ × σ`, and the pushforward of
`σ × σ` is `≤ σ` because that's precisely the statement that `+` is continuous for `σ`.
The proof for `•` follows mutatis mutandis.

A *topological module* for a topological ring `R` is an `R`-module `A` with a topology
making `+` and `•` continuous. The discussion so far has shown that the action topology makes `A`
into a topological module, and moreover is the finest topology with this property.

A crucial observation is that if `M` is a topological `R`-module, if `A` is an `R`-module with no
topology, and if `φ : A → M` is linear, then the pullback of `M`'s topology to `A` is a topology
making `A` into a topological module. Let's for example check that `•` is continuous.
If `U ⊆ A` is open then by definition of the pullback topology, `U = φ⁻¹(V)` for some open `V ⊆ M`,
and now the pullback of `U` under `•` is just the pullback along the continuous map
`id × φ : R × A → R × M` of the preimage of `V` under the continuous map `• : R × M → M`,
so it's open. The proof for `+` is similar.

As a consequence of this, we see that if `φ : A → M` is a linear map between topological `R`-modules
modules and if `A` has the action topology, then `φ` is automatically continuous.
Indeed the argument above shows that if `A → M` is linear then the action
topology on `A` is `≤` the pullback of the action topology on `M` (because it's the inf of a set
containing this topology) which is the definition of continuity.

We also deduce that the action topology is a functor from the category of `R`-modules
(`R` a topological ring) to the category of topological `R`-modules, and it is perhaps
unsurprising that this is an adjoint to the forgetful functor. Indeed, if `A` is an `R`-module
and `M` is a topological `R`-module, then the previous paragraph shows that
the linear maps `A → M` are precisely the continuous linear maps
from (`A` with its action topology) to `M`, so the action topology is a left adjoint
to the forgetful functor.

This file develops the theory of the action topology. We prove that the action topology on
`R` as a module over itself is `R`'s original topology, and that the action topology
is isomorphism-invariant.

## Main theorems

* `ActionTopology.instSelf : IsActionTopology R R`. The action topology on `R` is `R`'s topology.
* `ActionTopology.iso [IsActionTopology R A] (e : A ≃L[R] B) : IsActionTopology R B`. If `A` and
    `B` are `R`-modules with topologies, if `e` is a topological isomorphism between them,
    and if `A` has the action topology, then `B` has the action topology.

## TODO

Forthcoming PRs from the FLT repo will show that the action topology on a (binary or finite) product
of modules is the product of the action topologies, and that the action topology on the quotient
of a module `M` is the quotient topology when `M` is equipped with the action topology.

We will also show the slightly more subtle result that if `M`, `N` and `P` are `R`-modules
equipped with the action topology and if furthermore `M` is finite as an `R`-module,
then any bilinear map `M × N → P` is continuous.

As a consequence of this, we deduce that if `R` is a commutative topological ring
and `A` is an `R`-algebra of finite type as `R`-module, then `A` with its action
topology becomes a topological ring (i.e., multiplication is continuous).

Other TODOs (not done in the FLT repo):

* The action topology is a functor from the category of `R`-modules
  to the category of topological `R`-modules, and it's an adjoint to the forgetful functor.

-/

section basics

/-
This section is just boilerplate, defining the action topology and making
some infrastructure.
-/
variable (R : Type*) [TopologicalSpace R] (A : Type*) [Add A] [SMul R A]

/-- The action topology, for a module `A` over a topological ring `R`. It's the finest topology
making addition and the `R`-action continuous, or equivalently the finest topology making `A`
into a topological `R`-module. More precisely it's the Inf of the set of
topologies with these properties; theorems `continuousSMul` and `continuousAdd` show
that the action topology also has these properties. -/
abbrev actionTopology : TopologicalSpace A :=
  sInf {t | @ContinuousSMul R A _ _ t ∧ @ContinuousAdd A t _}

/-- A class asserting that the topology on a module over a topological ring `R` is
the action topology. See `actionTopology` for more discussion of the action topology. -/
class IsActionTopology [τA : TopologicalSpace A] : Prop where
  /-- Note that this should not be used directly, and `eq_actionTopology`, which takes `R` and `A` explicitly, should be used instead. -/
  eq_actionTopology' : τA = actionTopology R A

theorem eq_actionTopology [τA : TopologicalSpace A] [IsActionTopology R A] :
    τA = actionTopology R A :=
  IsActionTopology.eq_actionTopology' (R := R) (A := A)

/-- Scalar multiplication `• : R × A → A` is continuous if `R` is a topological
ring, and `A` is an `R` module with the action topology. -/
theorem ActionTopology.continuousSMul : @ContinuousSMul R A _ _ (actionTopology R A) :=
  /- Proof: We need to prove that the product topology is finer than the pullback
     of the action topology. But the action topology is an Inf and thus a limit,
     and pullback is a right adjoint, so it preserves limits.
     We must thus show that the product topology is finer than an Inf, so it suffices
     to show it's a lower bound, which is not hard. All this is wrapped into
     `continuousSMul_sInf`.
  -/
  continuousSMul_sInf <| fun _ _ ↦ by simp_all only [Set.mem_setOf_eq]

/-- Addition `+ : A × A → A` is continuous if `R` is a topological
ring, and `A` is an `R` module with the action topology. -/
theorem ActionTopology.continuousAdd : @ContinuousAdd A (actionTopology R A) _ :=
  continuousAdd_sInf <| fun _ _ ↦ by simp_all only [Set.mem_setOf_eq]

instance IsActionTopology.toContinuousSMul [TopologicalSpace A] [IsActionTopology R A] :
    ContinuousSMul R A := eq_ActionTopology R A ▸ ActionTopology.continuousSMul R A

-- this can't be an instance because typclass inference can't be expected to find `R`.
theorem IsActionTopology.toContinuousAdd [TopologicalSpace A] [IsActionTopology R A] :
    ContinuousAdd A := eq_ActionTopology R A ▸ ActionTopology.continuousAdd R A

/-- The action topology is `≤` any topology making `A` into a topological module. -/
theorem actionTopology_le [τA : TopologicalSpace A] [ContinuousSMul R A] [ContinuousAdd A] :
    actionTopology R A ≤ τA := sInf_le ⟨inferInstance, inferInstance⟩

end basics

namespace ActionTopology

section zero

instance instSubsingleton (R : Type*) [TopologicalSpace R] (A : Type*) [Add A] [SMul R A]
    [Subsingleton A] [TopologicalSpace A] : IsActionTopology R A where
  eq_actionTopology' := by
    ext U
    simp only [isOpen_discrete]

end zero

section one

/-

We now fix once and for all a topological semiring `R`.

We first prove that the action topology on `R` considered as a module over itself,
is `R`'s topology.

-/
instance instSelf (R : Type*) [Semiring R] [τR : TopologicalSpace R] [TopologicalSemiring R] :
    IsActionTopology R R := by
  constructor
  /- Let `R` be a topological ring with topology τR. To prove that `τR` is the action
  topology, it suffices to prove inclusions in both directions.
  One way is obvious: addition and multiplication are continuous for `R`, so the
  action topology is finer than `R` because it's the finest topology with these properties.-/
  refine le_antisymm ?_ (actionTopology_le R R)
  /- The other way is more interesting. We can interpret the problem as proving that
  the identity function is continuous from `R` with the action topology to `R` with
  its usual topology to `R` with the action topology.
  -/
  rw [← continuous_id_iff_le]
  /-
  The idea needed here is to rewrite the identity function as the composite of `r ↦ (r,1)`
  from `R` to `R × R`, and multiplication on `R × R`, where we topologise `R × R`
  by giving the first `R` the usual topology and the second `R` the action topology.
  -/
  rw [show (id : R → R) = (fun rs ↦ rs.1 • rs.2) ∘ (fun r ↦ (r, 1)) by ext; simp]
  /-
  It thus suffices to show that each of these maps are continuous.
  -/
  apply @Continuous.comp R (R × R) R τR (@instTopologicalSpaceProd R R τR (actionTopology R R))
      (actionTopology R R)
  · /-
    The map R × R → R is `•`, so by a fundamental property of the action topology,
    this is continuous. -/
    exact @continuous_smul _ _ _ _ (actionTopology R R) <| ActionTopology.continuousSMul ..
  · /-
    The map `R → R × R` sending `r` to `(r,1)` is a map into a product, so it suffices to show
    that each of the two factors is continuous. But the first is the identity function and the
    second is a constant function. -/
    exact @Continuous.prod_mk _ _ _ _ (actionTopology R R) _ _ _ continuous_id <|
      @continuous_const _ _ _ (actionTopology R R) _

end one

section iso

variable {R : Type*} [τR : TopologicalSpace R] [Semiring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [τA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [τB : TopologicalSpace B]

/-- If `A` and `B` are homeomorphic via a homeomorphism which is also `R`-linear, and if
`A` has the action topology, then so does `B`. -/
theorem iso (e : A ≃L[R] B) : IsActionTopology R B where
  eq_actionTopology' := by
    -- get these in before I start putting new topologies on A and B and have to use `@`
    let g : A →ₗ[R] B := e.toLinearMap
    let g' : B →ₗ[R] A := e.symm.toLinearMap
    let h : A →+ B := e
    let h' : B →+ A := e.symm
    simp_rw [e.toHomeomorph.symm.inducing.1, eq_ActionTopology R A, actionTopology, induced_sInf]
    apply congr_arg
    ext τ
    rw [Set.mem_image]
    constructor
    · rintro ⟨σ, ⟨hσ1, hσ2⟩, rfl⟩
      exact ⟨continuousSMul_induced g', continuousAdd_induced h'⟩
    · rintro ⟨h1, h2⟩
      use τ.induced e
      rw [induced_compose]
      refine ⟨⟨continuousSMul_induced g, continuousAdd_induced h⟩, ?_⟩
      nth_rw 2 [← induced_id (t := τ)]
      simp

end iso

end ActionTopology
