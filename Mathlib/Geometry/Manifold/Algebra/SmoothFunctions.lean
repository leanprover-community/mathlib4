/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Algebraic structures over `C^n` functions

In this file, we define instances of algebraic structures over `C^n` functions.
-/

@[expose] public section


noncomputable section

open scoped Manifold ContDiff

open TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {N' : Type*} [TopologicalSpace N'] [ChartedSpace H'' N']
  {n : WithTop ℕ∞}

namespace ContMDiffMap

@[to_additive]
protected instance instMul {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : Mul C^n⟮I, N; I', G⟯ :=
  ⟨fun f g => ⟨f * g, f.contMDiff.mul g.contMDiff⟩⟩

@[to_additive (attr := simp)]
theorem coe_mul {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [ContMDiffMul I' n G]
    (f g : C^n⟮I, N; I', G⟯) : ⇑(f * g) = f * g :=
  rfl

@[to_additive (attr := simp)]
theorem mul_comp {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [ContMDiffMul I' n G]
    (f g : C^n⟮I'', N'; I', G⟯) (h : C^n⟮I, N; I'', N'⟯) : (f * g).comp h = f.comp h * g.comp h :=
  rfl

@[to_additive]
protected instance instOne {G : Type*} [One G] [TopologicalSpace G] [ChartedSpace H' G] :
    One C^n⟮I, N; I', G⟯ :=
  ⟨ContMDiffMap.const (1 : G)⟩

@[to_additive (attr := simp)]
theorem coe_one {G : Type*} [One G] [TopologicalSpace G] [ChartedSpace H' G] :
    ⇑(1 : C^n⟮I, N; I', G⟯) = 1 :=
  rfl

@[to_additive]
instance instPow {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] :
    Pow C^n⟮I, N; I', G⟯ ℕ where
  pow f n := ⟨(f : N → G) ^ n, (contMDiff_pow n).comp f.contMDiff⟩

@[to_additive (attr := simp)]
theorem coe_pow {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] (f : C^n⟮I, N; I', G⟯) (n : ℕ) :
    ⇑(f ^ n) = (f : N → G) ^ n :=
  rfl

section GroupStructure

/-!
### Group structure

In this section we show that `C^n` functions valued in a Lie group inherit a group structure
under pointwise multiplication.
-/

@[to_additive]
instance semigroup {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : Semigroup C^n⟮I, N; I', G⟯ :=
  DFunLike.coe_injective.semigroup _ coe_mul

@[to_additive]
instance monoid {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : Monoid C^n⟮I, N; I', G⟯ :=
  DFunLike.coe_injective.monoid _ coe_one coe_mul coe_pow

/-- Coercion to a function as a `MonoidHom`. Similar to `MonoidHom.coeFn`. -/
@[to_additive (attr := simps) /-- Coercion to a function as an `AddMonoidHom`.
  Similar to `AddMonoidHom.coeFn`. -/]
def coeFnMonoidHom {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : C^n⟮I, N; I', G⟯ →* N → G where
  toFun := DFunLike.coe
  map_one' := coe_one
  map_mul' := coe_mul

variable (I N)

/-- For a manifold `N` and a `C^n` homomorphism `φ` between Lie groups `G'`, `G''`, the
'left-composition-by-`φ`' group homomorphism from `C^n⟮I, N; I', G'⟯` to `C^n⟮I, N; I'', G''⟯`. -/
@[to_additive /-- For a manifold `N` and a `C^n` homomorphism `φ` between additive Lie groups `G'`,
`G''`, the 'left-composition-by-`φ`' group homomorphism from `C^n⟮I, N; I', G'⟯` to
`C^n⟮I, N; I'', G''⟯`. -/]
def compLeftMonoidHom {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H' G']
    [ContMDiffMul I' n G'] {G'' : Type*} [Monoid G''] [TopologicalSpace G''] [ChartedSpace H'' G'']
    [ContMDiffMul I'' n G''] (φ : G' →* G'') (hφ : CMDiff n φ) :
    C^n⟮I, N; I', G'⟯ →* C^n⟮I, N; I'', G''⟯ where
  toFun f := ⟨φ ∘ f, hφ.comp f.contMDiff⟩
  map_one' := by ext; change φ 1 = 1; simp
  map_mul' f g := by ext x; change φ (f x * g x) = φ (f x) * φ (g x); simp

variable (I') {N}

-- TODO: generalize to any `C^n` map instead of `Set.inclusion`
/-- For a Lie group `G` and open sets `U ⊆ V` in `N`, the 'restriction' group homomorphism from
`C^n⟮I, V; I', G⟯` to `C^n⟮I, U; I', G⟯`. -/
@[to_additive /-- For an additive Lie group `G` and open sets `U ⊆ V` in `N`, the 'restriction'
group homomorphism from `C^n⟮I, V; I', G⟯` to `C^n⟮I, U; I', G⟯`. -/]
def restrictMonoidHom (G : Type*) [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] {U V : Opens N} (h : U ≤ V) : C^n⟮I, V; I', G⟯ →* C^n⟮I, U; I', G⟯ where
  toFun f := ⟨f ∘ Set.inclusion h, f.contMDiff.comp (contMDiff_inclusion h)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable {I I'}

@[to_additive]
instance commMonoid {G : Type*} [CommMonoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : CommMonoid C^n⟮I, N; I', G⟯ :=
  DFunLike.coe_injective.commMonoid _ coe_one coe_mul coe_pow

@[to_additive]
instance group {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' n G] :
    Group C^n⟮I, N; I', G⟯ :=
  { ContMDiffMap.monoid with
    inv := fun f => ⟨fun x => (f x)⁻¹, f.contMDiff.inv⟩
    inv_mul_cancel := fun a => by ext; exact inv_mul_cancel _
    div := fun f g => ⟨f / g, f.contMDiff.div g.contMDiff⟩
    div_eq_mul_inv := fun f g => by ext; exact div_eq_mul_inv _ _ }

@[to_additive (attr := simp)]
theorem coe_inv {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' n G]
    (f : C^n⟮I, N; I', G⟯) : ⇑f⁻¹ = (⇑f)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem coe_div {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' n G]
    (f g : C^n⟮I, N; I', G⟯) : ⇑(f / g) = f / g :=
  rfl

@[to_additive]
instance commGroup {G : Type*} [CommGroup G] [TopologicalSpace G] [ChartedSpace H' G]
    [LieGroup I' n G] : CommGroup C^n⟮I, N; I', G⟯ :=
  { ContMDiffMap.group, ContMDiffMap.commMonoid with }

end GroupStructure

section RingStructure

/-!
### Ring structure

In this section we show that `C^n` functions valued in a `C^n` ring `R` inherit a ring structure
under pointwise multiplication.
-/


instance semiring {R : Type*} [Semiring R] [TopologicalSpace R] [ChartedSpace H' R]
    [ContMDiffRing I' n R] : Semiring C^n⟮I, N; I', R⟯ :=
  { ContMDiffMap.addCommMonoid,
    ContMDiffMap.monoid with
    left_distrib := fun a b c => by ext; exact left_distrib _ _ _
    right_distrib := fun a b c => by ext; exact right_distrib _ _ _
    zero_mul := fun a => by ext; exact zero_mul _
    mul_zero := fun a => by ext; exact mul_zero _ }

instance ring {R : Type*} [Ring R] [TopologicalSpace R] [ChartedSpace H' R] [ContMDiffRing I' n R] :
    Ring C^n⟮I, N; I', R⟯ :=
  { ContMDiffMap.semiring, ContMDiffMap.addCommGroup with }

instance commRing {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
    [ContMDiffRing I' n R] : CommRing C^n⟮I, N; I', R⟯ :=
  { ContMDiffMap.semiring, ContMDiffMap.addCommGroup, ContMDiffMap.commMonoid with }

variable (I N)

/-- For a manifold `N` and a `C^n` homomorphism `φ` between `C^n` rings `R'`, `R''`, the
'left-composition-by-`φ`' ring homomorphism from `C^n⟮I, N; I', R'⟯` to `C^n⟮I, N; I'', R''⟯`. -/
def compLeftRingHom {R' : Type*} [Ring R'] [TopologicalSpace R'] [ChartedSpace H' R']
    [ContMDiffRing I' n R'] {R'' : Type*} [Ring R''] [TopologicalSpace R''] [ChartedSpace H'' R'']
    [ContMDiffRing I'' n R''] (φ : R' →+* R'') (hφ : CMDiff n φ) :
    C^n⟮I, N; I', R'⟯ →+* C^n⟮I, N; I'', R''⟯ :=
  { ContMDiffMap.compLeftMonoidHom I N φ.toMonoidHom hφ,
    ContMDiffMap.compLeftAddMonoidHom I N φ.toAddMonoidHom hφ with
    toFun := fun f => ⟨φ ∘ f, hφ.comp f.contMDiff⟩ }

variable (I') {N}

/-- For a "`C^n` ring" `R` and open sets `U ⊆ V` in `N`, the "restriction" ring homomorphism from
`C^n⟮I, V; I', R⟯` to `C^n⟮I, U; I', R⟯`. -/
def restrictRingHom (R : Type*) [Ring R] [TopologicalSpace R] [ChartedSpace H' R]
    [ContMDiffRing I' n R] {U V : Opens N} (h : U ≤ V) :
    C^n⟮I, V; I', R⟯ →+* C^n⟮I, U; I', R⟯ :=
  { ContMDiffMap.restrictMonoidHom I I' R h, ContMDiffMap.restrictAddMonoidHom I I' R h with
    toFun := fun f => ⟨f ∘ Set.inclusion h, f.contMDiff.comp (contMDiff_inclusion h)⟩ }

variable {I I'}

/-- Coercion to a function as a `RingHom`. -/
@[simps]
def coeFnRingHom {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
    [ContMDiffRing I' n R] : C^n⟮I, N; I', R⟯ →+* N → R :=
  { (coeFnMonoidHom : C^n⟮I, N; I', R⟯ →* _), (coeFnAddMonoidHom : C^n⟮I, N; I', R⟯ →+ _) with
    toFun := (↑) }

/-- `Function.eval` as a `RingHom` on the ring of `C^n` functions. -/
def evalRingHom {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
    [ContMDiffRing I' n R] (m : N) : C^n⟮I, N; I', R⟯ →+* R :=
  (Pi.evalRingHom _ m : (N → R) →+* R).comp ContMDiffMap.coeFnRingHom

end RingStructure

section ModuleStructure

/-!
### Semimodule structure

In this section we show that `C^n` functions valued in a vector space `M` over a normed
field `𝕜` inherit a vector space structure.
-/


instance instSMul {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    SMul 𝕜 C^n⟮I, N; 𝓘(𝕜, V), V⟯ :=
  ⟨fun r f => ⟨r • ⇑f, f.contMDiff.const_smul r⟩⟩

@[simp]
theorem coe_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (r : 𝕜)
    (f : C^n⟮I, N; 𝓘(𝕜, V), V⟯) : ⇑(r • f) = r • ⇑f :=
  rfl

@[simp]
theorem smul_comp {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (r : 𝕜)
    (g : C^n⟮I'', N'; 𝓘(𝕜, V), V⟯) (h : C^n⟮I, N; I'', N'⟯) : (r • g).comp h = r • g.comp h :=
  rfl

instance module {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    Module 𝕜 C^n⟮I, N; 𝓘(𝕜, V), V⟯ :=
  Function.Injective.module 𝕜 coeFnAddMonoidHom ContMDiffMap.coe_injective coe_smul

/-- Coercion to a function as a `LinearMap`. -/
@[simps]
def coeFnLinearMap {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    C^n⟮I, N; 𝓘(𝕜, V), V⟯ →ₗ[𝕜] N → V :=
  { (coeFnAddMonoidHom : C^n⟮I, N; 𝓘(𝕜, V), V⟯ →+ _) with
    toFun := (↑)
    map_smul' := coe_smul }

end ModuleStructure

section AlgebraStructure

/-!
### Algebra structure

In this section we show that `C^n` functions valued in a normed algebra `A` over a normed field `𝕜`
inherit an algebra structure.
-/


variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [ContMDiffRing 𝓘(𝕜, A) n A]

/-- `C^n` constant functions as a `RingHom`. -/
def C : 𝕜 →+* C^n⟮I, N; 𝓘(𝕜, A), A⟯ where
  toFun := fun c : 𝕜 => ⟨fun _ => (algebraMap 𝕜 A) c, contMDiff_const⟩
  map_one' := by ext; exact (algebraMap 𝕜 A).map_one
  map_mul' c₁ c₂ := by ext; exact (algebraMap 𝕜 A).map_mul _ _
  map_zero' := by ext; exact (algebraMap 𝕜 A).map_zero
  map_add' c₁ c₂ := by ext; exact (algebraMap 𝕜 A).map_add _ _

instance algebra : Algebra 𝕜 C^n⟮I, N; 𝓘(𝕜, A), A⟯ where
  smul := fun r f => ⟨r • f, f.contMDiff.const_smul r⟩
  algebraMap := ContMDiffMap.C
  commutes' := fun c f => by ext x; exact Algebra.commutes' _ _
  smul_def' := fun c f => by ext x; exact Algebra.smul_def' _ _

/-- Coercion to a function as an `AlgHom`. -/
@[simps]
def coeFnAlgHom : C^n⟮I, N; 𝓘(𝕜, A), A⟯ →ₐ[𝕜] N → A where
  toFun := (↑)
  commutes' _ := rfl
  -- `(ContMDiffMap.coeFnRingHom : C^n⟮I, N; 𝓘(𝕜, A), A⟯ →+* _) with` times out for some reason
  map_zero' := ContMDiffMap.coe_zero
  map_one' := ContMDiffMap.coe_one
  map_add' := ContMDiffMap.coe_add
  map_mul' := ContMDiffMap.coe_mul

end AlgebraStructure

section ModuleOverContinuousFunctions

/-!
### Structure as module over scalar functions

If `V` is a module over `𝕜`, then we show that the space of `C^n` functions from `N` to `V`
is naturally a vector space over the ring of `C^n` functions from `N` to `𝕜`. -/

/-- `C^n` scalar-valued functions act by left-multiplication on `C^n` functions. -/
instance instSMul' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    SMul C^n⟮I, N; 𝕜⟯ C^n⟮I, N; 𝓘(𝕜, V), V⟯ :=
  ⟨fun f g => ⟨fun x => f x • g x, ContMDiff.smul f.2 g.2⟩⟩

/-- The left multiplication with a `C^n` scalar function commutes with composition. -/
@[simp]
theorem smul_comp' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (f : C^n⟮I'', N'; 𝕜⟯)
    (g : C^n⟮I'', N'; 𝓘(𝕜, V), V⟯) (h : C^n⟮I, N; I'', N'⟯) :
    (f • g).comp h = f.comp h • g.comp h :=
  rfl

/-- The space of `C^n` functions with values in a space `V` is a module over the space of `C^n`
functions with values in `𝕜`. -/
instance module' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    Module C^n⟮I, N; 𝓘(𝕜), 𝕜⟯ C^n⟮I, N; 𝓘(𝕜, V), V⟯ where
  smul_add c f g := by ext x; exact smul_add (c x) (f x) (g x)
  add_smul c₁ c₂ f := by ext x; exact add_smul (c₁ x) (c₂ x) (f x)
  mul_smul c₁ c₂ f := by ext x; exact mul_smul (c₁ x) (c₂ x) (f x)
  one_smul f := by ext x; exact one_smul 𝕜 (f x)
  zero_smul f := by ext x; exact zero_smul _ _
  smul_zero r := by ext x; exact smul_zero _

end ModuleOverContinuousFunctions

end ContMDiffMap
