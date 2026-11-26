/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig, Pepa Montero, Enrique Díaz Blanco
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Geometry.Manifold.Diffeomorph

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

For a group `G` acting smoothly on `M`, we define `Diffeomorph.smul`, scalar multiplication by a
fixed `g : G` as a diffeomorphism of `M` (in analogy to `Homeomorph.smul`).

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

-- TODO: after #41534 is merged, weaken the hypothesis to `ContMDiffConstSMul`
@[to_additive]
theorem ContMDiffSMul.contMDiff_const_smul {n : ℕ∞ω} [ContMDiffSMul I I' n G M] (g : G) :
    CMDiff n fun x : M ↦ g • x :=
  contMDiff_const.smul (I := I) contMDiff_id

end

@[to_additive prod]
instance Prod.contMDiffSMul [SMul G M] [SMul G N] {n : ℕ∞ω} [ContMDiffSMul I I' n G M]
    [ContMDiffSMul I I'' n G N] : ContMDiffSMul I (I'.prod I'') n G (M × N) where
  contMDiff_smul := (contMDiff_fst.smul <| contMDiff_fst.comp contMDiff_snd).prodMk <|
      contMDiff_fst.smul <| contMDiff_snd.comp contMDiff_snd

/-- If `G` acts continuously differentiably on `G'` and `G'` acts continuously differentiably on
`M`, then `G` acts continuously differentiably on `M`. -/
@[to_additive]
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
  {Γ : Type*} [SMul Γ M] {n : ℕ∞ω}

@[to_additive]
protected theorem ContMDiffConstSMul.of_le {m : ℕ∞ω} (h : n ≤ m)
    [ContMDiffConstSMul I m Γ M] : ContMDiffConstSMul I n Γ M  :=
  ⟨fun γ ↦ (contMDiff_const_smul γ).of_le h⟩

@[to_additive]
instance [ContMDiffConstSMul I ∞ Γ M] [ENat.LEInfty n] :
    ContMDiffConstSMul I n Γ M :=
  .of_le ENat.LEInfty.out

@[to_additive]
instance [ContMDiffConstSMul I ω Γ M] : ContMDiffConstSMul I n Γ M :=
  .of_le le_top

@[to_additive]
instance [ContinuousConstSMul Γ M] : ContMDiffConstSMul I 0 Γ M :=
  ⟨fun γ ↦ contMDiff_zero_iff.2 (continuous_const_smul γ)⟩

@[to_additive]
instance [ContMDiffConstSMul I 2 Γ M] : ContMDiffConstSMul I 1 Γ M :=
  .of_le one_le_two

/-- If an action is Cⁿ for some `n`, it is also continuous. This has to be a theorem instead of an
instance because `ContMDiffConstSMul` depends on parameters `I` and `n` that `ContinuousConstSMul`
doesn't. -/
@[to_additive]
lemma ContMDiffConstSMul.continuousConstSMul (n : ℕ∞ω) [ContMDiffConstSMul I n Γ M] :
    ContinuousConstSMul Γ M :=
  ⟨fun γ ↦ (contMDiff_const_smul (I := I) (n := n) γ).continuous⟩

section

variable [ContMDiffConstSMul I n Γ M] {f : N → M} {s : Set N} {x : N}

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
theorem ContMDiff.const_smul (hf : CMDiff n f) (γ : Γ) :
    CMDiff n (γ • f) := fun x ↦ (hf x).const_smul γ

end

@[to_additive]
instance Prod.contMDiffConstSMul [SMul Γ N] [ContMDiffConstSMul I n Γ M]
    [ContMDiffConstSMul I' n Γ N] : ContMDiffConstSMul (I.prod I') n Γ (M × N) where
  contMDiff_const_smul γ := ContMDiff.prodMk
    (ContMDiff.const_smul contMDiff_fst γ) (ContMDiff.const_smul contMDiff_snd γ)

/-- If the action on `M` by any element of `Γ'` is continuously differentiable, and `Γ` acts on `Γ'`
such that `Γ`, `Γ'` and `M` form a scalar tower, then the induced action on `M` by any element of
`Γ` is continuously differentiable as well. -/
@[to_additive]
lemma IsScalarTower.contMDiffConstSMul (Γ' : Type*) [Monoid Γ'] [SMul Γ Γ'] [MulAction Γ' M]
    [IsScalarTower Γ Γ' M] [ContMDiffConstSMul I n Γ' M] : ContMDiffConstSMul I n Γ M where
  contMDiff_const_smul γ := by
    suffices h : CMDiff n (fun x : M ↦ (γ • (1 : Γ')) • x) by
      rwa [show (fun x : M ↦ (γ • (1 : Γ')) • x) = fun x : M ↦ γ • x by simp] at h
    exact contMDiff_const_smul (γ • (1 : Γ'))

/-- If the action on `M` by any element of `Γ` is continuously differentiable, then post-composing
this action with any homomorphism `f : Γ' →* Γ` makes again the action on `M` by any element of `Γ'`
continuously differentiable . -/
@[to_additive]
theorem MulAction.contMDiffConstSMul_compHom {Γ Γ' : Type*} [Monoid Γ] [MulAction Γ M]
    [ContMDiffConstSMul I n Γ M] [Monoid Γ'] {f : Γ' →* Γ} :
    letI : MulAction Γ' M := MulAction.compHom _ f
    ContMDiffConstSMul I n Γ' M := by
  let _ : MulAction Γ' M := MulAction.compHom _ f
  exact ⟨fun g ↦ contMDiff_id.const_smul (f g)⟩

end ContMDiffConstSMul

section Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H']
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {I' : ModelWithCorners 𝕜 E' H'}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  [Group G] [MulAction G M] {n : ℕ∞ω} [ContMDiffSMul I I' n G M] (g : G)

variable (I I' n) in
/-- The diffeomorphism given by scalar multiplication by an element of a group `G` acting
Cⁿ-differentiably on a manifold `M` is a diffeomorphism from `M` to itself. Its inverse is scalar
multiplication by `g⁻¹`. -/
@[expose, to_additive
/-- The diffeomorphism given by affine-addition of an element of an additive group `G` acting
Cⁿ-differentiably on a manifold `M` is a diffeomorphism from `M` to itself. Its inverse is
addition of `-g`. -/]
def Diffeomorph.smul : M ≃ₘ^n⟮I', I'⟯ M where
  toEquiv := MulAction.toPerm g
  contMDiff_toFun := ContMDiffSMul.contMDiff_const_smul (I := I) g
  contMDiff_invFun := ContMDiffSMul.contMDiff_const_smul (I := I) g⁻¹

@[to_additive (attr := simp)]
lemma Diffeomorph.smul_toHomeomorph :
    haveI : ContinuousSMul G M := ContMDiffSMul.continuousSMul (I := I) (I' := I') n
    (Diffeomorph.smul I I' n g).toHomeomorph = Homeomorph.smul (α := M) g :=
  rfl

@[to_additive (attr := simp)]
lemma Diffeomorph.smul_apply (x : M) : Diffeomorph.smul I I' n g x = g • x := rfl

@[to_additive (attr := simp)]
lemma Diffeomorph.smul_symm_apply (x : M) : (Diffeomorph.smul I I' n g).symm x = g⁻¹ • x := rfl

@[to_additive]
lemma Diffeomorph.smul_symm :
    (Diffeomorph.smul I I' n g : M ≃ₘ^n⟮I', I'⟯ M).symm = Diffeomorph.smul I I' n g⁻¹ :=
  Diffeomorph.ext fun _ ↦ rfl

end Diffeomorph
