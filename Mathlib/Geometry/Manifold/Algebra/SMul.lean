/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-!
# Cⁿ monoid actions
In this file we define Cⁿ actions on manifolds: we say `ContMDiffSMul I I' n G M` if `G` acts
multiplicatively on `M` and the action map `fun p : G × M ↦ p.1 • p.2` is Cⁿ. We also provide API
for additive actions using `@[to_additive]`.
-/

open scoped Manifold ContDiff

@[expose] public section

/-- Basic typeclass stating that the additive action of `G` on `M` has smoothness degree `n`.
Unlike with `ContMDiffAdd`, we do not extend `IsManifold` because `ContMDiffVAdd` contains more
explicit arguments than `IsManifold` and so `ContMDiffVAdd.toIsManifold` could not be an instance
anyway: this means that in order for `ContMDiffVAdd` to be meaningful, smoothness of `G` and `M` has
to be required separately. For example, to state that `G` is a Cⁿ additive Lie group with a Cⁿ
additive action on a Cⁿ manifold `M`, one can use the typeclasses
`[LieAddGroup I n G] [IsManifold I' n M] [ContMDiffVAdd I I' n G M]`. -/
class ContMDiffVAdd {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (I' : ModelWithCorners 𝕜 E' H') (n : ℕ∞ω)
    (G : Type*) [TopologicalSpace G] [ChartedSpace H G]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H' M] [VAdd G M] : Prop where
  contMDiff_vadd : ContMDiff (I.prod I') I' n fun p : G × M ↦ p.1 +ᵥ p.2

/-- Basic typeclass stating that the action of `G` on `M` has smoothness degree `n`.
Unlike with `ContMDiffMul`, we do not extend `IsManifold` because `ContMDiffSMul` contains more
explicit arguments than `IsManifold` and so `ContMDiffSMul.toIsManifold` could not be an instance
anyway: this means that in order for `ContMDiffSMul` to be meaningful, smoothness of `G` and `M` has
to be required separately. For example, to state that `G` is a Cⁿ Lie group with a Cⁿ action on a Cⁿ
manifold `M`, one can use the typeclasses
`[LieGroup I n G] [IsManifold I' n M] [ContMDiffSMul I I' n G M]`. -/
@[to_additive]
class ContMDiffSMul {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (I' : ModelWithCorners 𝕜 E' H') (n : ℕ∞ω)
    (G : Type*) [TopologicalSpace G] [ChartedSpace H G]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H' M] [SMul G M] : Prop where
  contMDiff_smul : ContMDiff (I.prod I') I' n fun p : G × M ↦ p.1 • p.2

export ContMDiffVAdd (contMDiff_vadd)

export ContMDiffSMul (contMDiff_smul)

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
instance for technical reasons. -/
@[to_additive]
lemma ContMDiffSMul.continuousSMul [SMul G M] (n : ℕ∞ω) [ContMDiffSMul I I' n G M] :
    ContinuousSMul G M :=
  ⟨(contMDiff_smul (I := I) (I' := I') (n := n)).continuous⟩

section

variable [SMul G M] {n : ℕ∞ω} [ContMDiffSMul I I' n G M]
  {f : N → G} {g : N → M} {s : Set N} {x : N}

@[to_additive]
theorem ContMDiffWithinAt.smul (hf : ContMDiffWithinAt I'' I n f s x)
    (hg : ContMDiffWithinAt I'' I' n g s x) : ContMDiffWithinAt I'' I' n (f • g) s x :=
  (contMDiff_smul (I := I) (I' := I')).contMDiffAt.comp_contMDiffWithinAt x (hf.prodMk hg)

@[to_additive]
nonrec theorem ContMDiffAt.smul (hf : ContMDiffAt I'' I n f x) (hg : ContMDiffAt I'' I' n g x) :
    ContMDiffAt I'' I' n (f • g) x :=
  hf.smul hg

@[to_additive]
theorem ContMDiffOn.smul (hf : ContMDiffOn I'' I n f s) (hg : ContMDiffOn I'' I' n g s) :
    ContMDiffOn I'' I' n (f • g) s := fun x hx => (hf x hx).smul (hg x hx)

@[to_additive]
theorem ContMDiff.smul (hf : ContMDiff I'' I n f) (hg : ContMDiff I'' I' n g) :
    ContMDiff I'' I' n (f • g) := fun x => (hf x).smul (hg x)

end

@[to_additive prod]
instance ContMDiffSMul.prod [SMul G M] [SMul G N] {n : ℕ∞ω} [ContMDiffSMul I I' n G M]
    [ContMDiffSMul I I'' n G N] : ContMDiffSMul I (I'.prod I'') n G (M × N) where
  contMDiff_smul := (contMDiff_fst.smul <| contMDiff_fst.comp contMDiff_snd).prodMk <|
      contMDiff_fst.smul <| contMDiff_snd.comp contMDiff_snd

/-- If `G` acts continuously differentiably on `G'` and `G'` acts continuously differentiably on
`M`, then `G` acts continuously differentiably on `M`. -/
lemma IsScalarTower.contMDiffSMul (G' : Type*) [TopologicalSpace G'] [ChartedSpace H'' G']
    [Monoid G'] [SMul G G'] [MulAction G' M] [SMul G M] [IsScalarTower G G' M] {n : ℕ∞ω}
    [ContMDiffSMul I I'' n G G'] [ContMDiffSMul I'' I' n G' M] : ContMDiffSMul I I' n G M where
  contMDiff_smul := by
    suffices ContMDiff (I.prod I') I' n (fun p : G × M ↦ (p.1 • (1 : G')) • p.2) by simpa
    exact (contMDiff_fst.smul contMDiff_const).smul (I := I'') contMDiff_snd

/-- If an action is continuously differentiable, then composing this action with a continuously
differentiable homomorphism gives again a continuous action. -/
@[to_additive]
theorem MulAction.contMDiffSMul_compHom [Monoid G] [MulAction G M] {n : ℕ∞ω}
    [ContMDiffSMul I I' n G M] {G' : Type*} [TopologicalSpace G'] [ChartedSpace H'' G'] [Monoid G']
    {f : G' →* G} (hf : ContMDiff I'' I n f) :
    letI : MulAction G' M := MulAction.compHom _ f
    ContMDiffSMul I'' I' n G' M := by
  let _ : MulAction G' M := MulAction.compHom _ f
  exact ⟨(hf.comp contMDiff_fst).smul contMDiff_snd⟩

/-- If a complete normed ring acts continuously differentiably on a manifold `M`, its submanifold
of units does as well. -/
instance Units.contMDiffSMul {R : Type*} [NormedRing R] [CompleteSpace R] [NormedAlgebra 𝕜 R]
    [MulAction R M] {n : ℕ∞ω} [ContMDiffSMul 𝓘(𝕜, R) I' n R M] :
    ContMDiffSMul 𝓘(𝕜, R) I' n Rˣ M :=
  MulAction.contMDiffSMul_compHom (f := coeHom R) contMDiff_val

@[simps!]
def Diffeomorph.modelWithCornersSelfProdComparison {n : ℕ∞ω} :
    Diffeomorph 𝓘(𝕜, E × E') (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (E × E') (E × E') n where
  toEquiv := .refl _
  contMDiff_toFun :=
    (ContinuousLinearMap.fst 𝕜 E E').contMDiff.prodMk (ContinuousLinearMap.snd 𝕜 E E').contMDiff
  contMDiff_invFun := by
    rw [contMDiff_prod_module_iff, ← contMDiff_prod_iff]
    exact contMDiff_id

/-- The scalar multiplication `𝕜 × E → E` of any normed vector space `E` over `𝕜` is smooth. -/
instance {n : ℕ∞ω} : ContMDiffSMul 𝓘(𝕜) 𝓘(𝕜, E) n 𝕜 E where
  contMDiff_smul := by
    rw [← Diffeomorph.modelWithCornersSelfProdComparison.contMDiff_comp_diffeomorph_iff le_rfl]
    exact contDiff_smul.contMDiff

/-- The monoid `E →L[𝕜] E` of continuous linear endomorphisms of `E` acts smoothly on `E`. -/
instance [CompleteSpace E] {n : ℕ∞ω} :
    ContMDiffSMul 𝓘(𝕜, E →L[𝕜] E) 𝓘(𝕜, E) n (E →L[𝕜] E) E where
  contMDiff_smul := by
    rw [← Diffeomorph.modelWithCornersSelfProdComparison.contMDiff_comp_diffeomorph_iff le_rfl]
    exact isBoundedBilinearMap_apply.contDiff.contMDiff

/-- The general linear group `(E →L[𝕜] E)ˣ` on `E` acts smoothly on `E`. -/
example [CompleteSpace E] (n : ℕ∞ω) :
    ContMDiffSMul 𝓘(𝕜, E →L[𝕜] E) 𝓘(𝕜, E) n (E →L[𝕜] E)ˣ E :=
  inferInstance
