/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Algebraic structures over `C^n` functions

In this file, we define instances of algebraic structures over `C^n` functions.
-/


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

protected instance instMul {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : Mul C^n⟮I, N; I', G⟯ :=
  ⟨fun f g => ⟨f * g, f.contMDiff.mul g.contMDiff⟩⟩

@[simp]
theorem coe_mul {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [ContMDiffMul I' n G]
    (f g : C^n⟮I, N; I', G⟯) : ⇑(f * g) = f * g :=
  rfl

@[simp]
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

instance instNSMul {G : Type*} [AddMonoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffAdd I' n G] : SMul ℕ C^n⟮I, N; I', G⟯ where
  smul n f := ⟨n • (f : N → G), sorry⟩

@[to_additive existing]
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

instance semigroup {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : Semigroup C^n⟮I, N; I', G⟯ :=
  DFunLike.coe_injective.semigroup _ coe_mul

instance monoid {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : Monoid C^n⟮I, N; I', G⟯ :=
  DFunLike.coe_injective.monoid _ coe_one coe_mul coe_pow

/-- Coercion to a function as a `MonoidHom`. Similar to `MonoidHom.coeFn`. -/
@[simp]
def coeFnMonoidHom {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : C^n⟮I, N; I', G⟯ →* N → G where
  toFun := DFunLike.coe
  map_one' := coe_one
  map_mul' := coe_mul

variable (I N)

/-- For a manifold `N` and a `C^n` homomorphism `φ` between Lie groups `G'`, `G''`, the
'left-composition-by-`φ`' group homomorphism from `C^n⟮I, N; I', G'⟯` to `C^n⟮I, N; I'', G''⟯`. -/
def compLeftMonoidHom {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H' G']
    [ContMDiffMul I' n G'] {G'' : Type*} [Monoid G''] [TopologicalSpace G''] [ChartedSpace H'' G'']
    [ContMDiffMul I'' n G''] (φ : G' →* G'') (hφ : ContMDiff I' I'' n φ) :
    C^n⟮I, N; I', G'⟯ →* C^n⟮I, N; I'', G''⟯ where
  toFun f := ⟨φ ∘ f, hφ.comp f.contMDiff⟩
  map_one' := by ext; change φ 1 = 1; simp
  map_mul' f g := by ext x; change φ (f x * g x) = φ (f x) * φ (g x); simp

variable (I') {N}

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215):
-- TODO: generalize to any `C^n` map instead of `Set.inclusion`
/-- For a Lie group `G` and open sets `U ⊆ V` in `N`, the 'restriction' group homomorphism from
`C^n⟮I, V; I', G⟯` to `C^n⟮I, U; I', G⟯`. -/
def restrictMonoidHom (G : Type*) [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] {U V : Opens N} (h : U ≤ V) : C^n⟮I, V; I', G⟯ →* C^n⟮I, U; I', G⟯ where
  toFun f := ⟨f ∘ Set.inclusion h, f.contMDiff.comp (contMDiff_inclusion h)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable {I I'}

instance commMonoid {G : Type*} [CommMonoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : CommMonoid C^n⟮I, N; I', G⟯ :=
  DFunLike.coe_injective.commMonoid _ coe_one coe_mul coe_pow

instance group {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' n G] :
    Group C^n⟮I, N; I', G⟯ :=
  { ContMDiffMap.monoid with
    inv := fun f => ⟨fun x => (f x)⁻¹, f.contMDiff.inv⟩
    inv_mul_cancel := fun a => by ext; exact inv_mul_cancel _
    div := fun f g => ⟨f / g, f.contMDiff.div g.contMDiff⟩
    div_eq_mul_inv := fun f g => by ext; exact div_eq_mul_inv _ _ }

theorem coe_inv {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' n G]
    (f : C^n⟮I, N; I', G⟯) : ⇑f⁻¹ = (⇑f)⁻¹ :=
  rfl

theorem coe_div {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' n G]
    (f g : C^n⟮I, N; I', G⟯) : ⇑(f / g) = f / g :=
  rfl

instance commGroup {G : Type*} [CommGroup G] [TopologicalSpace G] [ChartedSpace H' G]
    [LieGroup I' n G] : CommGroup C^n⟮I, N; I', G⟯ :=
  { ContMDiffMap.group, ContMDiffMap.commMonoid with }

end GroupStructure


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

end ModuleOverContinuousFunctions

end ContMDiffMap
