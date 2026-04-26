/-
Copyright (c) 2026 Archibald Browne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archibald Browne
-/
module


public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic

/-!
# Continuously differentiable monoid actions

In this file we define the class `ContDiffSMul`. `ContDiffSMul 𝕜 M X n` holds if `M` acts on `X` and
the map `(c, x) ↦ c • x` is `n` times continuously differentiable on `M × X`.

## Main definitions

* `ContDiffSMul 𝕜 M X n` : typeclass saysing that the map `(c, x) ↦ c • x` is `n` times continuously
  differentiable on `M × X`

## Main results

`ContDiffSMul.of_retraction`, `ContinuousLinearEquiv.contDiffSMul` and `ContDiffSMul.comp` prove
results about pullbacks of continuously differentiable actions. `ContDiff.contdiff_smul`
provides dot-syntax for `ContDiffSMul`. Many of the results here are the continuously differentiable
analogues of the results in the module `Mathlib.Topology.Algebra.MulAction`.
-/

@[expose] public section

open Topology Pointwise
open Filter

/-- The class `ContDiffSMul 𝕜 M X n` says that the scalar multiplication `(•) : M → X → X` is `n`
times continuously differentiable in both arguments. -/
class ContDiffSMul (𝕜 M X : Type*) (n : WithTop ℕ∞) [SMul M X] [NormedAddCommGroup X]
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup M] [NormedSpace 𝕜 M]
    [NormedSpace 𝕜 X] : Prop where
  /-- The scalar multiplication `(•)` is contiuously differnentiable. -/
  contdiff_smul : ContDiff 𝕜 n fun p : M × X => p.1 • p.2

export ContDiffSMul (contdiff_smul)

/-- The class `ContDiffVAdd 𝕜 M X n` says that the additive action `(+ᵥ) : M → X → X`
is `n` times continuously differentiable in both arguments. -/
class ContDiffVAdd (𝕜 M X : Type*) (n : WithTop ℕ∞) [VAdd M X] [NormedAddCommGroup X]
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup M] [NormedSpace 𝕜 M]
    [NormedSpace 𝕜 X] : Prop where
  /-- The additive action `(+ᵥ)` is continuous. -/
  contdiff_vadd : ContDiff 𝕜 n fun p : M × X => p.1 +ᵥ p.2

export ContDiffVAdd (contdiff_vadd)

attribute [to_additive] ContDiffSMul

attribute [continuity, fun_prop] contdiff_smul contdiff_vadd

@[to_additive]
-- Cannot be an instance: `𝕜` and `n` don't appear in the conclusion
theorem ContDiffSMul.toContinuousSMul (𝕜 : Type*) {M X : Type*} (n : WithTop ℕ∞)
    [NontriviallyNormedField 𝕜] [SMul M X]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [ContDiffSMul 𝕜 M X n] : ContinuousSMul M X where
  continuous_smul := (contdiff_smul (𝕜 := 𝕜) (n := n)).continuous

section Main

variable {𝕜 M X Y α : Type*} {n : WithTop ℕ∞} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem ContDiffSMul.of_le {m : WithTop ℕ∞} [SMul M X] [ContDiffSMul 𝕜 M X n] (h : m ≤ n) :
    ContDiffSMul 𝕜 M X m where
  contdiff_smul := contdiff_smul.of_le h


section SMul

variable [SMul M X] [ContDiffSMul 𝕜 M X n]

@[to_additive]
lemma IsScalarTower.contdiffSMul {M : Type*} (N : Type*) {α : Type*} [Monoid N] [SMul M N]
    [MulAction N α] [SMul M α] [IsScalarTower M N α]
    [NormedAddCommGroup α] [NormedAddCommGroup M] [NormedAddCommGroup N] [NormedSpace 𝕜 M]
    [NormedSpace 𝕜 N] [NormedSpace 𝕜 α] [ContDiffSMul 𝕜 M N n]
    [ContDiffSMul 𝕜 N α n] : ContDiffSMul 𝕜 M α n where
  contdiff_smul := by
    suffices ContDiff 𝕜 n (fun p : M × α ↦ (p.1 • (1 : N)) • p.2) by
      simpa [smul_one_smul N]
    have h1 : ContDiff 𝕜 n (fun p : M × α ↦ p.1 • (1 : N)) :=
      (ContDiffSMul.contdiff_smul (𝕜 := 𝕜) (M := M) (X := N) (n := n)).comp
        (ContDiff.prodMk contDiff_fst contDiff_const)
    exact (ContDiffSMul.contdiff_smul (𝕜 := 𝕜) (M := N) (X := α) (n := n)).comp
      (ContDiff.prodMk h1 contDiff_snd)

@[to_additive]
lemma MulOpposite.contDiff_op : ContDiff 𝕜 n (op : M → Mᵐᵒᵖ) :=
  (MulOpposite.opContinuousLinearEquiv 𝕜 : M ≃L[𝕜] Mᵐᵒᵖ).contDiff

lemma MulOpposite.contDiff_unop : ContDiff 𝕜 n (unop : Mᵐᵒᵖ → M) :=
  (MulOpposite.opContinuousLinearEquiv 𝕜 : M ≃L[𝕜] Mᵐᵒᵖ).symm.contDiff

@[to_additive]
instance ContDiffSMul.op [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] : ContDiffSMul 𝕜 Mᵐᵒᵖ X n :=
  ⟨by
    suffices ContDiff 𝕜 n fun p : M × X => MulOpposite.op p.fst • p.snd from
      this.comp ((MulOpposite.contDiff_unop (n := n)).prodMap contDiff_id)
    simpa only [op_smul_eq_smul] using (contdiff_smul : ContDiff 𝕜 n fun p : M × X => _)⟩

@[to_additive]
instance MulOpposite.contDiffSMul : ContDiffSMul 𝕜 M Xᵐᵒᵖ n :=
  ⟨(MulOpposite.contDiff_op (n := n)).comp <|
    contdiff_smul.comp <| contDiff_id.prodMap (MulOpposite.contDiff_unop (n := n))⟩

section Transfer

variable {N Y : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]


/-- Transfer `ContDiffSMul` along a `ContinuousLinearEquiv`.
Analogue of `Topology.IsInducing.continuousSMul` for the smooth setting. -/
@[to_additive]
lemma ContinuousLinearEquiv.contDiffSMul [SMul N Y] {f : N → M}
    (g : Y ≃L[𝕜] X) (hf : ContDiff 𝕜 n f)
    (hsmul : ∀ {c y}, g (c • y) = f c • g y) :
    ContDiffSMul 𝕜 N Y n := ⟨by
  set F := fun (p : N × Y) => p.1 • p.2 with hF
  have hF' : F = (fun p ↦ g.symm (g (p.1 • p.2))) := by
    ext p; simp only [symm_apply_apply, hF]
  simp_rw [hsmul] at hF'
  rw [hF']
  exact g.symm.contDiff.comp
    (contdiff_smul.comp (ContDiff.prodMk (hf.comp contDiff_fst)
      (g.contDiff.comp contDiff_snd)))⟩

/-- Transfer `ContDiffSMul` via a retraction (continuous linear left inverse).
Analogue of `SMulMemClass.continuousSMul` for complemented subspaces. -/
@[to_additive]
lemma ContDiffSMul.of_retraction [SMul M N]
    (ι : N →L[𝕜] X) (π : X →L[𝕜] N) (hπι : ∀ x, π (ι x) = x)
    (hsmul : ∀ (m : M) (x : N), ι (m • x) = m • ι x) : ContDiffSMul 𝕜 M N n := ⟨by
  set F := fun (p : M × N) => p.1 • p.2 with hF
  have hF' : F = fun p ↦ π (p.1 • ι p.2) := by
    ext p; rw [← hsmul p.1 p.2, hπι (p.1 • p.2)]
  rw [hF']
  exact π.contDiff.comp (contdiff_smul.comp
    (ContDiff.prodMk contDiff_fst (ι.contDiff.comp contDiff_snd)))⟩

/-- Transfer `ContDiffSMul` along a smooth map on the acting type. -/
@[to_additive]
lemma ContDiffSMul.comp [SMul N X] {f : N → M}
    (hf : ContDiff 𝕜 n f)
    (hsmul : ∀ (c : N) (x : X), c • x = f c • x) :
    ContDiffSMul 𝕜 N X n := ⟨by
  set F := fun p : N × X => p.1 • p.2 with hF
  have : F = fun p => f p.1 • p.2 := by
    ext p; rw [← hsmul p.1 p.2]
  simpa [this] using
    contdiff_smul.comp (ContDiff.prodMk (hf.comp contDiff_fst) contDiff_snd)⟩

end Transfer

variable {f : Y → M} {g : Y → X} {b : Y} {s : Set Y} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

@[to_additive]
theorem ContDiffWithinAt.contdiff_smul'
    (hf : ContDiffWithinAt 𝕜 n f s b) (hg : ContDiffWithinAt 𝕜 n g s b) :
    ContDiffWithinAt 𝕜 n (fun x => f x • g x) s b :=
  ContDiffSMul.contdiff_smul.comp_contDiffWithinAt (ContDiffWithinAt.prodMk hf hg)

@[to_additive]
theorem ContDiffAt.contdiff_smul (hf : ContDiffAt 𝕜 n f b)
    (hg : ContDiffAt 𝕜 n g b) :
    ContDiffAt 𝕜 n (fun x => f x • g x) b :=
  ContDiffSMul.contdiff_smul.comp_contDiffAt _ (ContDiffAt.prodMk hf hg)

@[to_additive]
theorem ContDiffOn.contdiff_smul (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) :
    ContDiffOn 𝕜 n (fun x => f x • g x) s :=
  fun x hx => (hf x hx).contdiff_smul' (hg x hx)

@[to_additive]
theorem ContDiff.contdiff_smul (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun x => f x • g x) :=
  ContDiffSMul.contdiff_smul.comp (ContDiff.prodMk hf hg)

end SMul

section Monoid

variable [Monoid M] [MulAction M X] [ContDiffSMul 𝕜 M X n]

theorem MulAction.contDiffSMul_compHom {N} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
    [Monoid N] {f : N →* M} (hf : ContDiff 𝕜 n f) :
    letI := MulAction.compHom X f
    ContDiffSMul 𝕜 N X n := by
  letI := MulAction.compHom X f
  exact ⟨(hf.comp contDiff_fst).contdiff_smul contDiff_snd⟩


end Monoid


variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

instance Prod.contDiffSMul [SMul M X] [SMul M Y] [ContDiffSMul 𝕜 M X n] [ContDiffSMul 𝕜 M Y n] :
    ContDiffSMul 𝕜 M (X × Y) n where
  contdiff_smul := by
    suffices ContDiff 𝕜 n (fun p : M × (X × Y) => p.1 • p.2) by
      simpa only [Prod.smul_def] using this
    refine ContDiff.prodMk ?_ ?_
    · exact ContDiff.contdiff_smul contDiff_fst (ContDiff.snd' contDiff_fst)
    · exact ContDiff.contdiff_smul contDiff_fst (ContDiff.snd' contDiff_snd)

instance {ι : Type*} [Fintype ι] {γ : ι → Type*} [∀ i, SMul M (γ i)]
    [∀ i, NormedAddCommGroup (γ i)]
    [∀ i, NormedSpace 𝕜 (γ i)] [∀ i, ContDiffSMul 𝕜 M (γ i) n] :
    ContDiffSMul 𝕜 M (∀ i, γ i) n :=
  ⟨contDiff_pi.mpr fun i => by
    simp only [Pi.smul_apply]
    have hi : ContDiff 𝕜 n (fun x : M × (∀ i, γ i) => x.2 i) :=
      (ContinuousLinearMap.proj (R := 𝕜) (ι := ι) (φ := γ) i).contDiff.comp contDiff_snd
    exact contDiff_fst.contdiff_smul hi⟩

end Main

section Tendsto

variable {𝕜 M X α : Type*}

@[to_additive]
theorem Filter.Tendsto.contdiff_smul (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [SMul M X] (n : WithTop ℕ∞) [ContDiffSMul 𝕜 M X n]
    {f : α → M} {g : α → X} {l : Filter α} {c : M} {a : X}
    (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) :
    Tendsto (fun x => f x • g x) l (𝓝 <| c • a) :=
  (ContDiffSMul.contdiff_smul (𝕜 := 𝕜) (n := n) |>.continuous.tendsto _).comp
    (hf.prodMk_nhds hg)

@[to_additive]
theorem Filter.Tendsto.contdiff_smul_const (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [SMul M X] (n : WithTop ℕ∞) [ContDiffSMul 𝕜 M X n]
    {f : α → M} {l : Filter α} {c : M}
    (hf : Tendsto f l (𝓝 c)) (a : X) :
    Tendsto (fun x => f x • a) l (𝓝 (c • a)) :=
  hf.contdiff_smul 𝕜 n tendsto_const_nhds

end Tendsto
