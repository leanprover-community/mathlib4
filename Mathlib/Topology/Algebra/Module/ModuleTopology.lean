/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Will Sawin
-/
import Mathlib.Topology.Algebra.Module.Basic

/-!
# A "module topology" for modules over a topological ring

If `R` is a topological ring acting on an additive abelian group `A`, we define the
*module topology* to be the finest topology on `A` making both the maps
`• : R × A → A` and `+ : A × A → A` continuous (with all the products having the
product topology). Note that `- : A → A` is also automatically continuous as it is `a ↦ (-1) • a`.

This topology was suggested by Will Sawin [here](https://mathoverflow.net/a/477763/1384).


## Mathematical details

I (buzzard) don't know of any reference for this other than Sawin's mathoverflow answer,
so I expand some of the details here.

First note that the definition makes sense in far more generality (for example `R` just needs to
be a topological space acting on an additive monoid).

Next note that there *is* a finest topology with this property! Indeed, topologies on a fixed
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
making `+` and `•` continuous. The discussion so far has shown that the module topology makes
an `R`-module `A` into a topological module, and moreover is the finest topology with this property.

A crucial observation is that if `M` is a topological `R`-module, if `A` is an `R`-module with no
topology, and if `φ : A → M` is linear, then the pullback of `M`'s topology to `A` is a topology
making `A` into a topological module. Let's for example check that `•` is continuous.
If `U ⊆ A` is open then by definition of the pullback topology, `U = φ⁻¹(V)` for some open `V ⊆ M`,
and now the pullback of `U` under `•` is just the pullback along the continuous map
`id × φ : R × A → R × M` of the preimage of `V` under the continuous map `• : R × M → M`,
so it's open. The proof for `+` is similar.

As a consequence of this, we see that if `φ : A → M` is a linear map between topological `R`-modules
modules and if `A` has the module topology, then `φ` is automatically continuous.
Indeed the argument above shows that if `A → M` is linear then the module
topology on `A` is `≤` the pullback of the module topology on `M` (because it's the inf of a set
containing this topology) which is the definition of continuity.

We also deduce that the module topology is a functor from the category of `R`-modules
(`R` a topological ring) to the category of topological `R`-modules, and it is perhaps
unsurprising that this is an adjoint to the forgetful functor. Indeed, if `A` is an `R`-module
and `M` is a topological `R`-module, then the previous paragraph shows that
the linear maps `A → M` are precisely the continuous linear maps
from (`A` with its module topology) to `M`, so the module topology is a left adjoint
to the forgetful functor.

This file develops the theory of the module topology. We prove that the module topology on
`R` as a module over itself is `R`'s original topology, and that the module topology
is isomorphism-invariant.

## Main theorems

* `TopologicalSemiring.toIsModuleTopology : IsModuleTopology R R`. The module
    topology on `R` is `R`'s topology.
* `IsModuleTopology.iso [IsModuleTopology R A] (e : A ≃L[R] B) : IsModuleTopology R B`. If `A` and
    `B` are `R`-modules with topologies, if `e` is a topological isomorphism between them,
    and if `A` has the module topology, then `B` has the module topology.

## TODO

Forthcoming PRs from the FLT repo will show that the module topology on a (binary or finite) product
of modules is the product of the module topologies, and that the module topology on the quotient
of a module `M` is the quotient topology when `M` is equipped with the module topology.

We will also show the slightly more subtle result that if `M`, `N` and `P` are `R`-modules
equipped with the module topology and if furthermore `M` is finite as an `R`-module,
then any bilinear map `M × N → P` is continuous.

As a consequence of this, we deduce that if `R` is a commutative topological ring
and `A` is an `R`-algebra of finite type as `R`-module, then `A` with its module
topology becomes a topological ring (i.e., multiplication is continuous).

Other TODOs (not done in the FLT repo):

* The module topology is a functor from the category of `R`-modules
  to the category of topological `R`-modules, and it's an adjoint to the forgetful functor.

-/

section basics

/-
This section is just boilerplate, defining the module topology and making
some infrastructure. Note that we don't even need that `R` is a ring
in the main definitions, just that it acts on `A`.
-/
variable (R : Type*) [TopologicalSpace R] (A : Type*) [Add A] [SMul R A]

/-- The module topology, for a module `A` over a topological ring `R`. It's the finest topology
making addition and the `R`-action continuous, or equivalently the finest topology making `A`
into a topological `R`-module. More precisely it's the Inf of the set of
topologies with these properties; theorems `continuousSMul` and `continuousAdd` show
that the module topology also has these properties. -/
abbrev moduleTopology : TopologicalSpace A :=
  sInf {t | @ContinuousSMul R A _ _ t ∧ @ContinuousAdd A t _}

/-- A class asserting that the topology on a module over a topological ring `R` is
the module topology. See `moduleTopology` for more discussion of the module topology. -/
class IsModuleTopology [τA : TopologicalSpace A] : Prop where
  /-- Note that this should not be used directly, and `eq_moduleTopology`, which takes `R` and `A`
  explicitly, should be used instead. -/
  eq_moduleTopology' : τA = moduleTopology R A

theorem eq_moduleTopology [τA : TopologicalSpace A] [IsModuleTopology R A] :
    τA = moduleTopology R A :=
  IsModuleTopology.eq_moduleTopology' (R := R) (A := A)

/-- Scalar multiplication `• : R × A → A` is continuous if `R` is a topological
ring, and `A` is an `R` module with the module topology. -/
theorem ModuleTopology.continuousSMul : @ContinuousSMul R A _ _ (moduleTopology R A) :=
  /- Proof: We need to prove that the product topology is finer than the pullback
     of the module topology. But the module topology is an Inf and thus a limit,
     and pullback is a right adjoint, so it preserves limits.
     We must thus show that the product topology is finer than an Inf, so it suffices
     to show it's a lower bound, which is not hard. All this is wrapped into
     `continuousSMul_sInf`.
  -/
  continuousSMul_sInf fun _ h ↦ h.1

/-- Addition `+ : A × A → A` is continuous if `R` is a topological
ring, and `A` is an `R` module with the module topology. -/
theorem ModuleTopology.continuousAdd : @ContinuousAdd A (moduleTopology R A) _ :=
  continuousAdd_sInf fun _ h ↦ h.2

instance IsModuleTopology.toContinuousSMul [TopologicalSpace A] [IsModuleTopology R A] :
    ContinuousSMul R A := eq_moduleTopology R A ▸ ModuleTopology.continuousSMul R A

-- this can't be an instance because typclass inference can't be expected to find `R`.
theorem IsModuleTopology.toContinuousAdd [TopologicalSpace A] [IsModuleTopology R A] :
    ContinuousAdd A := eq_moduleTopology R A ▸ ModuleTopology.continuousAdd R A

/-- The module topology is `≤` any topology making `A` into a topological module. -/
theorem moduleTopology_le [τA : TopologicalSpace A] [ContinuousSMul R A] [ContinuousAdd A] :
    moduleTopology R A ≤ τA := sInf_le ⟨inferInstance, inferInstance⟩

end basics

namespace IsModuleTopology

section basics

variable {R : Type*} [TopologicalSpace R]
  {A : Type*} [Add A] [SMul R A] [τA : TopologicalSpace A]

/-- If `A` is a topological `R`-module and the identity map from (`A` with its given
topology) to (`A` with the module topology) is continuous, then the topology on `A` is
the module topology. -/
theorem of_continuous_id [ContinuousAdd A] [ContinuousSMul R A]
    (h : @Continuous A A τA (moduleTopology R A) id):
    IsModuleTopology R A where
  -- The topologies are equal because each is finer than the other. One inclusion
  -- follows from the continuity hypothesis; the other is because the module topology
  -- is the inf of all the topologies making `A` a topological module.
  eq_moduleTopology' := le_antisymm (continuous_id_iff_le.1 h) (moduleTopology_le _ _)

/-- The zero module has the module topology. -/
instance instSubsingleton [Subsingleton A] : IsModuleTopology R A where
  eq_moduleTopology' := Subsingleton.elim _ _

end basics

section iso

variable {R : Type*} [τR : TopologicalSpace R] [Semiring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [τA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [τB : TopologicalSpace B]

/-- If `A` and `B` are `R`-modules, homeomorphic via an `R`-linear homeomorphism, and if
`A` has the module topology, then so does `B`. -/
theorem iso (e : A ≃L[R] B) : IsModuleTopology R B where
  eq_moduleTopology' := by
    -- get these in before I start putting new topologies on A and B and have to use `@`
    let g : A →ₗ[R] B := e
    let g' : B →ₗ[R] A := e.symm
    let h : A →+ B := e
    let h' : B →+ A := e.symm
    simp_rw [e.toHomeomorph.symm.isInducing.1, eq_moduleTopology R A, moduleTopology, induced_sInf]
    apply congr_arg
    ext τ -- from this point on the definitions of `g`, `g'` etc above don't work without `@`.
    rw [Set.mem_image]
    constructor
    · rintro ⟨σ, ⟨hσ1, hσ2⟩, rfl⟩
      exact ⟨continuousSMul_induced g'.toMulActionHom, continuousAdd_induced h'⟩
    · rintro ⟨h1, h2⟩
      use τ.induced e
      rw [induced_compose]
      refine ⟨⟨continuousSMul_induced g.toMulActionHom, continuousAdd_induced h⟩, ?_⟩
      nth_rw 2 [← induced_id (t := τ)]
      simp

end iso

section self

variable (R : Type*) [Semiring R] [τR : TopologicalSpace R] [TopologicalSemiring R]

/-!
We now fix once and for all a topological semiring `R`.

We first prove that the module topology on `R` considered as a module over itself,
is `R`'s topology.
-/

/-- The topology on a topological semiring `R` agrees with the module topology when considering
`R` as an `R`-module in the obvious way (i.e., via `Semiring.toModule`). -/
instance _root_.TopologicalSemiring.toIsModuleTopology : IsModuleTopology R R := by
  /- By a previous lemma it suffices to show that the identity from (R,usual) to
  (R, module topology) is continuous. -/
  apply of_continuous_id
  /-
  The idea needed here is to rewrite the identity function as the composite of `r ↦ (r,1)`
  from `R` to `R × R`, and multiplication `R × R → R`.
  -/
  rw [show (id : R → R) = (fun rs ↦ rs.1 • rs.2) ∘ (fun r ↦ (r, 1)) by ext; simp]
  /-
  It thus suffices to show that each of these maps are continuous. For this claim to even make
  sense, we need to topologise `R × R`. The trick is to do this by giving the first `R` the usual
  topology `τR` and the second `R` the module topology. To do this we have to "fight mathlib"
  a bit with `@`, because there is more than one topology on `R` here.
  -/
  apply @Continuous.comp R (R × R) R τR (@instTopologicalSpaceProd R R τR (moduleTopology R R))
      (moduleTopology R R)
  · /-
    The map R × R → R is `•`, so by a fundamental property of the module topology,
    this is continuous. -/
    exact @continuous_smul _ _ _ _ (moduleTopology R R) <| ModuleTopology.continuousSMul ..
  · /-
    The map `R → R × R` sending `r` to `(r,1)` is a map into a product, so it suffices to show
    that each of the two factors is continuous. But the first is the identity function
    on `(R, usual topology)` and the second is a constant function. -/
    exact @Continuous.prod_mk _ _ _ _ (moduleTopology R R) _ _ _ continuous_id <|
      @continuous_const _ _ _ (moduleTopology R R) _

end self

section MulOpposite

variable (R : Type*) [Semiring R] [τR : TopologicalSpace R] [TopologicalSemiring R]

/-- The module topology coming from the action of the topological ring `Rᵐᵒᵖ` on `R`
  (via `Semiring.toOppositeModule`, i.e. via `(op r) • m = m * r`) is `R`'s topology. -/
instance _root_.TopologicalSemiring.toOppositeIsModuleTopology : IsModuleTopology Rᵐᵒᵖ R :=
  .iso (MulOpposite.opContinuousLinearEquiv Rᵐᵒᵖ).symm

end MulOpposite

section function

variable {R : Type*} [τR : TopologicalSpace R] [Semiring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B]
    [ContinuousAdd B] [ContinuousSMul R B]

/-- Every `R`-linear map between two topological `R`-modules, where the source has the module
topology, is continuous. -/
@[fun_prop, continuity]
theorem continuous_of_distribMulActionHom (φ : A →+[R] B) : Continuous φ := by
  -- the proof: We know that `+ : B × B → B` and `• : R × B → B` are continuous for the module
  -- topology on `B`, and two earlier theorems (`continuousSMul_induced` and
  -- `continuousAdd_induced`) say that hence `+` and `•` on `A` are continuous if `A`
  -- is given the topology induced from `φ`. Hence the module topology is finer than
  -- the induced topology, and so the function is continuous.
  rw [eq_moduleTopology R A, continuous_iff_le_induced]
  exact sInf_le <| ⟨continuousSMul_induced (φ.toMulActionHom),
    continuousAdd_induced φ.toAddMonoidHom⟩

@[fun_prop, continuity]
theorem continuous_of_linearMap (φ : A →ₗ[R] B) : Continuous φ :=
  continuous_of_distribMulActionHom φ.toDistribMulActionHom

variable (R) in
theorem continuous_neg (C : Type*) [AddCommGroup C] [Module R C] [TopologicalSpace C]
    [IsModuleTopology R C] : Continuous (fun a ↦ -a : C → C) :=
  haveI : ContinuousAdd C := IsModuleTopology.toContinuousAdd R C
  continuous_of_linearMap (LinearEquiv.neg R).toLinearMap

@[fun_prop, continuity]
theorem continuous_of_ringHom {R A B} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B]
    [TopologicalSpace R] [TopologicalSpace A] [IsModuleTopology R A] [TopologicalSpace B]
    [TopologicalSemiring B]
    (φ : A →+* B) (hφ : Continuous (φ.comp (algebraMap R A))) : Continuous φ := by
  let inst := Module.compHom B (φ.comp (algebraMap R A))
  let φ' : A →ₗ[R] B := ⟨φ, fun r m ↦ by simp [Algebra.smul_def]; rfl⟩
  have : ContinuousSMul R B := ⟨(hφ.comp continuous_fst).mul continuous_snd⟩
  exact continuous_of_linearMap φ'

end function

end IsModuleTopology
