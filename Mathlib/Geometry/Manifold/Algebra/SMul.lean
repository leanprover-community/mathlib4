/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# Cⁿ monoid actions

In this file we define Cⁿ actions (e.g. by Lie groups or monoids) on manifolds: we say
`ContMDiffSMul I I' n G M` if `G` acts multiplicatively on `M` and the action map
`fun p : G × M ↦ p.1 • p.2` is Cⁿ. We also provide API for additive actions using `@[to_additive]`.

We also define `ContMDiffConstSMul I n Γ M`, stating that for each `γ : Γ`, the map
`fun x : M ↦ γ • x` is Cⁿ. Unlike `ContMDiffSMul`, this requires no topology or charted space
structure on `Γ`, so it applies for example to actions of discrete groups by Cⁿ maps, such as the
properly discontinuous actions used to construct quotient manifolds.

TODO: For actions of Lie groups the two classes are close: a continuous action of a Lie group `G` on
a finite-dimensional manifold `M` is `C^n` provided it is `C^n` in the second variable.)

We also provide `ContMDiffSMul` instances for scalar multiplication in normed spaces and for
the action of the monoid `E →L[𝕜] E` of continuous linear maps on any normed space `E`.

See also:
* `ContMDiffMul I n G` for continuous differentiability of multiplication `G × G → G` in a single
  type `G`,
* `ContinuousSMul G M` for continuity of an action `G × M → M`,
* `ContinuousConstSMul Γ M` for continuity of `fun x ↦ γ • x` for each `γ : Γ`.
-/

open scoped Manifold ContDiff

public section

/-- Basic typeclass stating that the additive action of `G` on `M` is Cⁿ as a function `G × M → M`.
Unlike with `ContMDiffAdd` (the class stating that addition `G × G → G` within a single type `G` is
Cⁿ), we do not extend `IsManifold` because `ContMDiffVAdd` contains more
explicit arguments than `IsManifold` and so `ContMDiffVAdd.toIsManifold` could not be an instance
anyway: this means that in order for `ContMDiffVAdd` to be meaningful, smoothness of `G` and `M`
have to be required separately. For example, to state that `G` is a Cⁿ additive Lie group with a Cⁿ
additive action on a Cⁿ manifold `M`, one can use the typeclasses
`[LieAddGroup I n G] [IsManifold I' n M] [ContMDiffVAdd I I' n G M]`. -/
class ContMDiffVAdd {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (I' : ModelWithCorners 𝕜 E' H') (n : ℕ∞ω)
    (G : Type*) [TopologicalSpace G] [ChartedSpace H G]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H' M] [VAdd G M] : Prop where
  contMDiff_vadd : CMDiff n fun p : G × M ↦ p.1 +ᵥ p.2

/-- Basic typeclass stating that the action of `G` on `M` is Cⁿ as a function `G × M → M`.
Unlike with `ContMDiffMul` (the class stating that multiplication `G × G → G` within a single type
`G` is Cⁿ), we do not extend `IsManifold` because `ContMDiffSMul` contains more
explicit arguments than `IsManifold` and so `ContMDiffSMul.toIsManifold` could not be an instance
anyway: this means that in order for `ContMDiffSMul` to be meaningful, smoothness of `G` and `M`
have to be required separately. For example, to state that `G` is a Cⁿ Lie group with a Cⁿ action on
a Cⁿ manifold `M`, one can use the typeclasses
`[LieGroup I n G] [IsManifold I' n M] [ContMDiffSMul I I' n G M]`. -/
@[to_additive]
class ContMDiffSMul {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (I' : ModelWithCorners 𝕜 E' H') (n : ℕ∞ω)
    (G : Type*) [TopologicalSpace G] [ChartedSpace H G]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H' M] [SMul G M] : Prop where
  contMDiff_smul : CMDiff n fun p : G × M ↦ p.1 • p.2


/-- Typeclass stating that for each `γ : Γ`, the additive action `fun x : M ↦ γ +ᵥ x` is Cⁿ.
Unlike `ContMDiffVAdd` (which requires the action to be Cⁿ jointly as a map `Γ × M → M`), no
topology or manifold structure on `Γ` is required, so this class also covers additive actions of
discrete groups by Cⁿ maps. -/
class ContMDiffConstVAdd {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (Γ : Type*) (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [VAdd Γ M] : Prop where
  /-- For each `γ : Γ`, the map `fun x : M ↦ γ +ᵥ x` is Cⁿ. -/
  contMDiff_const_vadd : ∀ γ : Γ, CMDiff n fun x : M ↦ γ +ᵥ x

/-- Typeclass stating that for each `γ : Γ`, the scalar multiplication `fun x : M ↦ γ • x` is Cⁿ.
Unlike `ContMDiffSMul` (which requires the action to be Cⁿ jointly as a map `Γ × M → M`), no
topology or manifold structure on `Γ` is required, so this class also covers actions of discrete
groups by Cⁿ maps, e.g. the properly discontinuous actions used to construct quotient manifolds. -/
@[to_additive]
class ContMDiffConstSMul {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (Γ : Type*) (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [SMul Γ M] : Prop where
  /-- For each `γ : Γ`, the map `fun x : M ↦ γ • x` is Cⁿ. -/
  contMDiff_const_smul : ∀ γ : Γ, CMDiff n fun x : M ↦ γ • x

export ContMDiffVAdd (contMDiff_vadd)

export ContMDiffSMul (contMDiff_smul)

export ContMDiffConstVAdd (contMDiff_const_vadd)

export ContMDiffConstSMul (contMDiff_const_smul)

section ContMDiffSMul

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {I' : ModelWithCorners 𝕜 E' H'} {H'' : Type*} [TopologicalSpace H''] {E'' : Type*}
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N]

@[to_additive]
protected theorem ContMDiffSMul.of_le [SMul G M] {n m : ℕ∞ω} (h : n ≤ m)
    [ContMDiffSMul I I' m G M] : ContMDiffSMul I I' n G M := ⟨contMDiff_smul.of_le h⟩

@[to_additive]
instance [SMul G M] {n : ℕ∞ω} [ContMDiffSMul I I' ∞ G M] [ENat.LEInfty n] :
    ContMDiffSMul I I' n G M :=
  .of_le ENat.LEInfty.out

@[to_additive]
instance [SMul G M] {n : ℕ∞ω} [ContMDiffSMul I I' ω G M] : ContMDiffSMul I I' n G M :=
  .of_le le_top

@[to_additive]
instance [SMul G M] [ContinuousSMul G M] : ContMDiffSMul I I' 0 G M :=
  ⟨contMDiff_zero_iff.2 continuous_smul⟩

@[to_additive]
instance [SMul G M] [ContMDiffSMul I I' 2 G M] : ContMDiffSMul I I' 1 G M :=
  .of_le one_le_two

/-- If an action is Cⁿ for some `n`, it is also continuous. This has to be a theorem instead of an
instance because `ContMDiffSMul` depends on parameters `I`, `I'` and `n` that `ContinuousSMul`
doesn't. -/
@[to_additive]
lemma ContMDiffSMul.continuousSMul [SMul G M] (n : ℕ∞ω) [ContMDiffSMul I I' n G M] :
    ContinuousSMul G M :=
  ⟨(contMDiff_smul (I := I) (I' := I') (n := n)).continuous⟩

/-- For any `G` in which multiplication is Cⁿ, the action of `G` on itself via left multiplication
is Cⁿ too. -/
instance ContMDiffMul.contMDiffSMul [Mul G] {n : ℕ∞ω} [ContMDiffMul I n G] :
    ContMDiffSMul I I n G G where
  contMDiff_smul := contMDiff_mul

section

variable [SMul G M] {n : ℕ∞ω} [ContMDiffSMul I I' n G M]
  {f : N → G} {g : N → M} {s : Set N} {x : N}

@[to_additive]
theorem ContMDiffWithinAt.smul (hf : CMDiffAt[s] n f x) (hg : CMDiffAt[s] n g x) :
    CMDiffAt[s] n (f • g) x :=
  (contMDiff_smul (I := I) (I' := I')).contMDiffAt.comp_contMDiffWithinAt x (hf.prodMk hg)

@[to_additive]
nonrec theorem ContMDiffAt.smul (hf : CMDiffAt n f x) (hg : CMDiffAt n g x) :
    CMDiffAt n (f • g) x :=
  hf.smul hg

@[to_additive]
theorem ContMDiffOn.smul (hf : CMDiff[s] n f) (hg : CMDiff[s] n g) :
    CMDiff[s] n (f • g) := fun x hx ↦ (hf x hx).smul (hg x hx)

@[to_additive]
theorem ContMDiff.smul (hf : CMDiff n f) (hg : CMDiff n g) :
    CMDiff n (f • g) := fun x ↦ (hf x).smul (hg x)

end

@[to_additive prod]
instance Prod.contMDiffSMul [SMul G M] [SMul G N] {n : ℕ∞ω} [ContMDiffSMul I I' n G M]
    [ContMDiffSMul I I'' n G N] : ContMDiffSMul I (I'.prod I'') n G (M × N) where
  contMDiff_smul := (contMDiff_fst.smul <| contMDiff_fst.comp contMDiff_snd).prodMk <|
      contMDiff_fst.smul <| contMDiff_snd.comp contMDiff_snd

/-- If `G` acts continuously differentiably on `G'` and `G'` acts continuously differentiably on
`M`, then `G` acts continuously differentiably on `M`. -/
lemma IsScalarTower.contMDiffSMul (G' : Type*) [TopologicalSpace G'] [ChartedSpace H'' G']
    [Monoid G'] [SMul G G'] [MulAction G' M] [SMul G M] [IsScalarTower G G' M] {n : ℕ∞ω}
    [ContMDiffSMul I I'' n G G'] [ContMDiffSMul I'' I' n G' M] : ContMDiffSMul I I' n G M where
  contMDiff_smul := by
    suffices CMDiff n (fun p : G × M ↦ (p.1 • (1 : G')) • p.2) by simpa
    exact (contMDiff_fst.smul contMDiff_const).smul (I := I'') contMDiff_snd

/-- If an action is continuously differentiable, then post-composing this action with a continuously
differentiable homomorphism gives again a continuously differentiable action. -/
@[to_additive]
theorem MulAction.contMDiffSMul_compHom [Monoid G] [MulAction G M] {n : ℕ∞ω}
    [ContMDiffSMul I I' n G M] {G' : Type*} [TopologicalSpace G'] [ChartedSpace H'' G'] [Monoid G']
    {f : G' →* G} (hf : CMDiff n f) :
    letI : MulAction G' M := MulAction.compHom _ f
    ContMDiffSMul I'' I' n G' M := by
  let _ : MulAction G' M := MulAction.compHom _ f
  exact ⟨(hf.comp contMDiff_fst).smul contMDiff_snd⟩

/-- The scalar multiplication `𝕜 × E → E` of any normed vector space `E` over `𝕜` is smooth. -/
instance {n : ℕ∞ω} : ContMDiffSMul 𝓘(𝕜) 𝓘(𝕜, E) n 𝕜 E where
  contMDiff_smul := by
    have h : ContMDiff (𝓘(𝕜).prod 𝓘(𝕜, E)) 𝓘(𝕜, 𝕜 × E) n (@id (𝕜 × E)) := by
      rw [contMDiff_prod_module_iff, ← contMDiff_prod_iff]; exact contMDiff_id
    exact contDiff_smul.contMDiff.comp h

/-- The monoid `E →L[𝕜] E` of continuous linear endomorphisms of `E` acts smoothly on `E`. -/
instance {n : ℕ∞ω} : ContMDiffSMul 𝓘(𝕜, E →L[𝕜] E) 𝓘(𝕜, E) n (E →L[𝕜] E) E where
  contMDiff_smul := by
    have h : ContMDiff (𝓘(𝕜, E →L[𝕜] E).prod 𝓘(𝕜, E)) 𝓘(𝕜, (E →L[𝕜] E) × E) n
        (@id ((E →L[𝕜] E) × E)) := by
      rw [contMDiff_prod_module_iff, ← contMDiff_prod_iff]; exact contMDiff_id
    exact isBoundedBilinearMap_apply.contDiff.contMDiff.comp h

end ContMDiffSMul

section ContMDiffConstSMul

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {Γ : Type*} [SMul Γ M]

@[to_additive]
protected theorem ContMDiffConstSMul.of_le {n m : ℕ∞ω} (h : n ≤ m)
    [ContMDiffConstSMul I m Γ M] : ContMDiffConstSMul I n Γ M  :=
  ⟨fun γ ↦ (contMDiff_const_smul γ).of_le h⟩

@[to_additive]
instance {n : ℕ∞ω} [ContMDiffConstSMul I ∞ Γ M] [ENat.LEInfty n] :
    ContMDiffConstSMul I n Γ M :=
  .of_le ENat.LEInfty.out

@[to_additive]
instance {n : ℕ∞ω} [ContMDiffConstSMul I ω Γ M] : ContMDiffConstSMul I n Γ M :=
  .of_le le_top

@[to_additive]
instance [ContinuousConstSMul Γ M] : ContMDiffConstSMul I 0 Γ M :=
  ⟨sorry⟩

/-- If an action is Cⁿ for some `n`, it is also continuous. This has to be a theorem instead of an
instance because `ContMDiffSMul` depends on parameters `I`, `I'` and `n` that `ContinuousSMul`
doesn't. -/
@[to_additive]
lemma ContMDiffConstSMul.continuousConstSMul (n : ℕ∞ω) [ContMDiffConstSMul I n Γ M] :
    ContinuousConstSMul Γ M :=
  ⟨sorry⟩

section

variable {n : ℕ∞ω} [ContMDiffConstSMul I n Γ M] {f : N → M} {s : Set N} {x : N}

/- Let `M` be a charted space being acted on by `Γ : Type*`. Given another charted space `N`, a
differentiable map `f : N → M`, and `γ : Γ` , then the map `γ • f : N → M` is also differentiable -/
@[to_additive]
theorem ContMDiffWithinAt.const_smul (hf : CMDiffAt[s] n f x) (γ : Γ) :
    CMDiffAt[s] n (γ • f) x :=
  (contMDiff_const_smul γ).contMDiffAt.comp_contMDiffWithinAt x hf

@[to_additive]
nonrec theorem ContMDiffAt.const_smul (hf : CMDiffAt n f x) (γ : Γ) :
    CMDiffAt n (γ • f) x :=
  hf.const_smul γ

@[to_additive]
theorem ContMDiffOn.const_smul (hf : CMDiff[s] n f) (γ : Γ) :
    CMDiff[s] n (γ • f) := fun x hx ↦ (hf x hx).const_smul γ

@[to_additive]
theorem ContMDiff.smul (hf : CMDiff n f) (hg : CMDiff n g) :
    CMDiff n (f • g) := fun x ↦ (hf x).smul (hg x)

end


end ContMDiffConstSMul
