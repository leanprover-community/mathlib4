/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Prelim
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial

/-!
# Covariant derivatives

TODO: add a more complete doc-string

-/

open Bundle Filter Module Topology Set
open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

@[expose] public section -- TODO: think if we want to expose all definitions!

section real

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]
  -- `V` vector bundle

--- TODO FROM HERE!

namespace IsCovariantDerivativeOn

section projection_trivial_bundle

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    [IsManifold I 1 M]

local notation "TM" => TangentSpace I

variable {cov : (M → F) → (Π x : M, TangentSpace I x →L[𝕜] F)} {s : Set M}

noncomputable
def projection (hcov : IsCovariantDerivativeOn F cov s) (x : M) (f : F) : (TM x) × F →L[𝕜] F :=
  .snd 𝕜 (TM x) F + (hcov.one_form x f ∘L .fst 𝕜 (TM x) F)

@[simp]
lemma projection_apply (hcov : IsCovariantDerivativeOn F cov s) (x : M) (f : F) (v : TM x) (w : F) :
  hcov.projection x f (v, w) = w + hcov.one_form x f v := rfl

lemma cov_eq_proj (hcov : IsCovariantDerivativeOn F cov s) (σ : M → F)
    {x : M} (X₀ : TM x) (hσ : MDiffAt (T% σ) x) (hx : x ∈ s := by trivial) :
    cov σ x X₀ = hcov.projection x (σ x) (X₀, mfderiv I 𝓘(𝕜, F) σ x X₀) := by
  simpa using congr($(hcov.eq_one_form hσ) X₀)

noncomputable def horiz (hcov : IsCovariantDerivativeOn F cov s) (x : M) (f : F) :
    Submodule 𝕜 (TM x × F) :=
  (hcov.projection x f).ker

lemma horiz_vert_direct_sum (hcov : IsCovariantDerivativeOn F cov s) (x : M) (f : F) :
    IsCompl (hcov.horiz x f) (.prod ⊥ ⊤) := by
  refine IsCompl.of_eq ?_ ?_
  · refine (Submodule.eq_bot_iff _).mpr ?_
    rintro ⟨u, w⟩ ⟨huw, hu, hw⟩
    simp_all [horiz]
  · apply Submodule.sup_eq_top_iff _ _ |>.2
    intro u
    use u - (0, hcov.projection x f u), ?_, (0, hcov.projection x f u), ?_, ?_
    all_goals simp [horiz]

set_option backward.isDefEq.respectTransparency false in
lemma mem_horiz_iff_exists [FiniteDimensional 𝕜 E] (hcov : IsCovariantDerivativeOn F cov s) {x : M}
    {f : F} {u : TM x} {v : F} (hx : x ∈ s := by trivial) : (u, v) ∈ hcov.horiz x f ↔
    ∃ σ : M → F, MDiffAt (T% σ) x ∧
                 σ x = f ∧
                 mfderiv I 𝓘(𝕜, F) σ x u = v ∧
                 cov σ x u = 0 := by
  constructor
  · intro huv
    simp only [horiz, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, projection_apply] at huv
    let w : TangentSpace 𝓘(𝕜, F) f := v
    by_cases hu : u = 0
    · subst hu
      replace huv : v = 0 := by simpa using huv
      subst huv
      use fun x ↦ f
      simp [mdifferentiableAt_section,  mdifferentiableAt_const]
    rcases map_of_one_jet_spec u w (by tauto) with ⟨h, h', h''⟩
    use map_of_one_jet u w, ?_, h, h''
    · rw [hcov.eq_one_form]
      · simp only [w, h]
        convert huv
        convert ContinuousLinearMap.add_apply (M₁ := TangentSpace I x) (M₂ := F) _
          (hcov.one_form x f) u
        exact h''.symm
      · rwa [mdifferentiableAt_section]
    · rwa [mdifferentiableAt_section]
  · rintro ⟨σ, σ_diff, rfl, rfl, covσ⟩
    simp only [horiz, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, projection_apply, ← covσ]
    rw [hcov.eq_one_form σ_diff]
    rfl

end projection_trivial_bundle

end IsCovariantDerivativeOn

--end real

namespace Bundle.Trivialization

section to_trivialization

variable (e : Trivialization F (π F V)) [VectorBundle 𝕜 F V] [MemTrivializationAtlas e]
  [IsManifold I 1 M]

noncomputable
def pushCovDer
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)) :
    (M → F) → (Π x : M, TangentSpace I x →L[𝕜] F) :=
  fun σ x ↦ e.continuousLinearMapAt 𝕜 x ∘L (cov (e.funToSec σ) x)

lemma pushCovDer_ofSect [FiniteDimensional 𝕜 F]
    [IsManifold I 1 M]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [ContMDiffVectorBundle 1 F V I]
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hcov : IsCovariantDerivativeOn F cov e.baseSet)
    {X₀ : TangentSpace I x} {σ : Π x : M, V x} {x : M}
    (hσ : MDiffAt T%σ x)
    (hx : x ∈ e.baseSet := by assumption) :
    (e.pushCovDer cov) (fun x ↦ (e (σ x)).2) x X₀ = (e (cov σ x X₀)).2 := by
  have : cov (fun x' ↦ e.symm x' (e (T% σ x')).2) x = cov σ x := by
    apply hcov.congr_σ_of_eqOn _ hσ (e.baseSet_mem_nhds hx)
    · exact fun y hy ↦ symm_apply_apply_mk e hy (σ y) --FIXME extract as lemma?
    · stop
      rw [(e.symm_apply_apply_mk_eventuallyEq hx σ).mdifferentiableAt_iff]
      exact hσ
  unfold pushCovDer
  stop
  rw [this]
  simp [coe_linearMapAt, hx]


variable {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    -- {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)

lemma pushCovDer_isCovariantDerivativeOn
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [ContMDiffVectorBundle 1 F V I]
    {u : Set M} (hu : u ⊆ e.baseSet)
    (hcov : IsCovariantDerivativeOn F cov u) :
    IsCovariantDerivativeOn F (e.pushCovDer cov) u where
  addσ {σ σ' x} hσ hσ' hx := by
    set s := (fun x' ↦ e.symm x' (σ x'))
    have hs : MDiffAt (T% s) x := by
      sorry -- e.mdifferentiableAt_section_of_function (hu hx) <|
        --mdifferentiableAt_section_trivial_iff.1 hσ
    set s' := (fun x' ↦ e.symm x' (σ' x'))
    have hs' : MDiffAt (T% s') x :=
      sorry -- e.mdifferentiableAt_section_of_function (hu hx) <|
        --mdifferentiableAt_section_trivial_iff.1 hσ'
    unfold Trivialization.pushCovDer
    stop
    rw [← ContinuousLinearMap.comp_add, ← hcov.addσ hs hs' hx]
    congr
    ext y
    simp [e.symm_map_add 𝕜, s, s']
  leibniz {σ g x} hσ hg hx := by
    set s := (fun x' ↦ e.symm x' (σ x'))
    have hs : MDiffAt (T% s) x :=
      sorry -- e.mdifferentiableAt_section_of_function (hu hx) <|
        --mdifferentiableAt_section_trivial_iff.1 hσ
    unfold Trivialization.pushCovDer
    have : (fun x' ↦ e.symm x' ((g • σ) x')) = g • s := by
      ext y
      simp [s, e.symm_map_smul]
    stop
    rw [this, hcov.leibniz hs hg hx]
    ext X₀
    simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
      continuousLinearMapAt_apply, Pi.smul_apply, Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.toSpanSingleton_apply, _root_.map_smul,
      add_right_inj, s]
    congr! 1
    exact e.linearMapAt_symmₗ (R := 𝕜) (hu hx) (σ x)

variable {e} in
lemma coordChangeL_pushCovDer
    [IsManifold I 1 M]
    {e' : Trivialization F (π F V)} [MemTrivializationAtlas e']
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [ContMDiffVectorBundle 1 F V I]
    (hcov : IsCovariantDerivativeOn F cov <| e.baseSet ∩ e'.baseSet)
    {x : M} (hx : x ∈ e.baseSet ∩ e'.baseSet)
    {s : M → F} (hs : MDiffAt s x) :
    e.coordChangeL 𝕜 e' x ∘L (e.pushCovDer cov s x) =
      e'.pushCovDer cov (fun x ↦ e.coordChangeL 𝕜 e' x (s x)) x := by
  ext1 X₀
  simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  unfold pushCovDer
  let σ := (fun x' ↦ e.symm x' (s x'))
  rw [coordChangeL_apply e e' hx]
  simp only [ContinuousLinearMap.coe_comp', continuousLinearMapAt_apply, coe_linearMapAt, hx.1,
    ↓reduceIte, Function.comp_apply, hx.2]
  refold_let σ
  have : e.symm x (e ⟨x, cov σ x X₀⟩).2 = cov σ x X₀ := by
    simp [hx.1]
  stop
  rw [this]
  -- TODO: extract lemma?
  have : ∀ x' ∈ e.baseSet ∩ e'.baseSet, σ x' =
      e'.symm x' ((fun x ↦ (coordChangeL 𝕜 e e' x) (s x)) x') := by
    rintro x' ⟨hx'e, hx'e'⟩
    simp only
    rw [coordChangeL_apply e e' ⟨hx'e, hx'e'⟩]
    -- simp [hx'e'] -- TODO doesn’t work
    rw [symm_apply_apply_mk e' hx'e']
  have mem : e.baseSet ∩ e'.baseSet ∈ 𝓝 x := by
    -- FIXME: make sure grind can do this proof
    exact inter_mem (baseSet_mem_nhds e (mem_of_mem_inter_left hx))
        (baseSet_mem_nhds e' (mem_of_mem_inter_right hx))
  have hσ : MDiffAt (T% σ) x :=
    mdifferentiableAt_section_of_function e hx.1 hs
  rw [hcov.congr_σ_of_eqOn hσ ?_ mem this]
  -- TODO have automatation doing the next three lines…
  apply mdifferentiableAt_section_of_function e' hx.2
  have := contMDiffAt_coordChangeL (n := 1) (IB := I) hx.1 hx.2
  exact this.mdifferentiableAt (zero_ne_one.symm) |>.clm_apply hs

variable [CompleteSpace 𝕜]

variable {e} in
lemma coordChangeL_mem_horiz [FiniteDimensional 𝕜 E]
    [IsManifold I 1 M] [FiniteDimensional 𝕜 F]
    {e' : Trivialization F (π F V)} [MemTrivializationAtlas e']
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [ContMDiffVectorBundle 1 F V I]
    (hcov : IsCovariantDerivativeOn F cov <| e.baseSet ∩ e'.baseSet)
    {x : M} (hx : x ∈ e.baseSet ∩ e'.baseSet) {u : TangentSpace I x} {v w : F} :
    haveI hcove := e.pushCovDer_isCovariantDerivativeOn inter_subset_left hcov
    haveI hcove' := e'.pushCovDer_isCovariantDerivativeOn inter_subset_right hcov
    (u, w) ∈ hcove.horiz x v →
    (u, e.coordChangeL 𝕜 e' x w) ∈ hcove'.horiz x (e.coordChangeL 𝕜 e' x v) := by
  have hcove := e.pushCovDer_isCovariantDerivativeOn inter_subset_left hcov
  have hcove' := e'.pushCovDer_isCovariantDerivativeOn inter_subset_right hcov
  rw [hcove.mem_horiz_iff_exists, hcove'.mem_horiz_iff_exists]
  rintro ⟨s, sdiff, sxv, sxuw, covs⟩
  use fun x ↦ e.coordChangeL 𝕜 e' x (s x), ?_, ?_, ?_
  · let X := extend E u
    -- have hX : MDiffAt (T% X) x := mdifferentiableAt_extend I E u
    -- TODO: investigate whether the following line comes from inconsistent ways to
    -- state assumptions
    rw [mdifferentiableAt_section_trivial_iff] at sdiff
    rw [← e.coordChangeL_pushCovDer hcov hx sdiff]
    simp [covs]
  · sorry
  · congr
  · rw [← sxuw]
    sorry

-- This is PAIIIIINNNN
variable {e} in
lemma coordChangeL_coordChangeL
    {e' : Trivialization F (π F V)} [MemTrivializationAtlas e']
    {x : M} (hx : x ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    e'.coordChangeL 𝕜 e x (e.coordChangeL 𝕜 e' x v) = v := by
  have hx' := inter_comm _ _ ▸ hx
  change ((coordChangeL 𝕜 e' e x) ∘ (coordChangeL 𝕜 e e' x)) v = v
  rw [coe_coordChangeL _ _ hx]
  rw [coe_coordChangeL _ _ hx']
  change
    ((linearEquivAt 𝕜 e x hx'.2 ∘ (linearEquivAt 𝕜 e' x hx'.1).symm)  ∘
    (linearEquivAt 𝕜 e' x hx'.1 ∘ (linearEquivAt 𝕜 e x hx'.2).symm))
     v = v
  rw [Function.comp_assoc]
  conv =>
    congr
    congr
    rfl
    rw [← Function.comp_assoc]
  change
    ((linearEquivAt 𝕜 e x _) ∘
    (↑(linearEquivAt 𝕜 e' x hx'.1).symm ∘ₗ (linearEquivAt 𝕜 e' x hx'.1).toLinearMap) ∘ _)
    v = v
  rw [(linearEquivAt 𝕜 e' x hx'.1).symm_comp]
  simp only [LinearMap.id_coe, CompTriple.comp_eq]
  change (↑(linearEquivAt 𝕜 e x hx'.2) ∘ₗ (linearEquivAt 𝕜 e x _).symm.toLinearMap) v = v
  rw [(linearEquivAt 𝕜 e x hx'.2).comp_symm]
  simp

variable {e} in
lemma coordChangeL_mem_horiz_iff [FiniteDimensional 𝕜 E]
    [IsManifold I 1 M] [FiniteDimensional 𝕜 F]
    {e' : Trivialization F (π F V)} [MemTrivializationAtlas e']
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [ContMDiffVectorBundle 1 F V I]
    (hcov : IsCovariantDerivativeOn F cov <| e.baseSet ∩ e'.baseSet)
    {x : M} (hx : x ∈ e.baseSet ∩ e'.baseSet) {u : TangentSpace I x} {v w : F} :
    haveI hcove := e.pushCovDer_isCovariantDerivativeOn inter_subset_left hcov
    haveI hcove' := e'.pushCovDer_isCovariantDerivativeOn inter_subset_right hcov
    (u, w) ∈ hcove.horiz x v ↔
    (u, e.coordChangeL 𝕜 e' x w) ∈ hcove'.horiz x (e.coordChangeL 𝕜 e' x v) := by
  refine ⟨e.coordChangeL_mem_horiz hcov hx, fun hu ↦ ?_⟩
  let v' := e.coordChangeL 𝕜 e' x v
  let w' := e.coordChangeL 𝕜 e' x w
  rw [inter_comm] at hx hcov
  have hx' := inter_comm _ _ ▸ hx
  have hvv' : v = e'.coordChangeL 𝕜 e x v' := (coordChangeL_coordChangeL hx' v).symm
  have hww' : w = e'.coordChangeL 𝕜 e x w' := (coordChangeL_coordChangeL hx' w).symm
  have key := e'.coordChangeL_mem_horiz hcov hx (w := w') (u := u) (v := v') ?_
  · rw [← hvv', ← hww'] at key
    convert key using 2
    apply inter_comm
  · convert hu using 2
    apply inter_comm

end to_trivialization

end Bundle.Trivialization

section horiz
namespace CovariantDerivative

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    [IsManifold I 1 M]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]

local notation "TM" => TangentSpace I

-- FIXME the statement of CovariantDerivative.isCovariantDerivativeOn should work on any set

noncomputable
def proj (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    TangentSpace (I.prod 𝓘(𝕜, F)) v →L[𝕜] V v.proj :=
  letI t := trivializationAt F V v.proj
  haveI d_covDerOn := t.pushCovDer_isCovariantDerivativeOn (u := t.baseSet) subset_rfl
    (cov.isCovariantDerivativeOn.mono fun _ _ ↦ mem_univ _)
  letI tproj := d_covDerOn.projection v.proj (t v).2
  letI Tvt := t.deriv I v
  t.symmL 𝕜 v.proj ∘L tproj ∘L Tvt

omit [FiniteDimensional 𝕜 F] in
lemma isCovariantDerivativeOn_pushCovDer
    (cov : CovariantDerivative I F V) (e : Trivialization F (π F V)) [MemTrivializationAtlas e] :
    IsCovariantDerivativeOn F (e.pushCovDer cov) e.baseSet :=
  e.pushCovDer_isCovariantDerivativeOn subset_rfl
      (cov.isCovariantDerivativeOn.mono fun _ _ ↦ mem_univ _)

lemma snd_triv_proj (cov : CovariantDerivative I F V) (v : TotalSpace F V) (u : TangentSpace (I.prod
  𝓘(𝕜, F)) v) :
    letI t := trivializationAt F V v.proj
    haveI d_covDerOn := cov.isCovariantDerivativeOn_pushCovDer t
    letI tproj := d_covDerOn.projection v.proj (t v).2
    letI Tvt := t.deriv I v
    (t <| cov.proj v u).2 = tproj (Tvt u) := by
  simp [CovariantDerivative.proj, (mem_baseSet_trivializationAt F V v.proj)]

noncomputable def horiz (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    Submodule 𝕜 (TangentSpace (I.prod 𝓘(𝕜, F)) v) :=
  (cov.proj v).ker

lemma mem_horiz_iff_proj {cov : CovariantDerivative I F V} {v : TotalSpace F V}
    (u : TangentSpace (I.prod 𝓘(𝕜, F)) v) :
    u ∈ cov.horiz v ↔ cov.proj v u = 0 := by
  simp [horiz]

lemma comap_trivializationAt_horiz (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    letI t := trivializationAt F V v.proj
    haveI d_covDerOn := cov.isCovariantDerivativeOn_pushCovDer t
    horiz cov v = Submodule.comap (t.deriv I v).toLinearMap
      (d_covDerOn.horiz v.proj (t v).2) := by
  -- FIXME: needing all those lets and the change is awful
  let t := trivializationAt F V v.proj
  let Tvt := t.deriv I v
  haveI hcov := cov.isCovariantDerivativeOn_pushCovDer t
  let tproj := hcov.projection v.proj (t v).2
  let t' := t.continuousLinearEquivAt 𝕜 v.proj (mem_baseSet_trivializationAt F V v.proj)
  ext u
  change t'.symm (tproj (Tvt u)) = 0 ↔ tproj (Tvt u) = 0
  simp

omit [ContMDiffVectorBundle 1 F V I] in
lemma horiz_vert_direct_sum [ContMDiffVectorBundle 1 F V I]
    (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    IsCompl (cov.horiz v) (vert v) := by
  let t := trivializationAt F V v.proj
  let Tvt := t.deriv I v
  have hcov := cov.isCovariantDerivativeOn_pushCovDer t
  rw [t.comap_vert (mem_baseSet_trivializationAt F V v.proj), comap_trivializationAt_horiz]
  apply LinearMap.comap_isCompl
  · apply t.bijective_deriv
    exact FiberBundle.mem_baseSet_trivializationAt' v.proj
  · apply hcov.horiz_vert_direct_sum

variable [IsManifold I 1 M]
variable {cov : CovariantDerivative I F V}

set_option backward.isDefEq.respectTransparency false in
omit [ContMDiffVectorBundle 1 F V I] in
lemma proj_mderiv [ContMDiffVectorBundle 1 F V I]
    {σ : Π x : M, V x} (x : M)
    (hσ : MDiffAt (T% σ) x) :
    cov σ x = cov.proj (σ x) ∘L
      (mfderiv I (I.prod 𝓘(𝕜, F)) (T% σ) x) := by
  stop
  let t := trivializationAt F V x
  let s := fun x ↦ (t (σ x)).2
  let Tσx := mfderiv% (T% σ) x
  -- FIXME `mfderiv%` fails in next line (fixed on master?)
  let Ttσx := mfderiv (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) t (σ x)
  ext1 X₀
  change cov σ x X₀ = (cov.proj (T% σ x)) ((mfderiv% (T% σ) x) X₀)
  have hcov := cov.isCovariantDerivativeOn_pushCovDer t
  have hx := mem_baseSet_trivializationAt F V x
  have hs : MDiffAt (T% s) x := by
    rw [t.mdifferentiableAt_section_iff I σ hx] at hσ
    exact (mdifferentiableAt_section I s).mpr hσ
  apply t.eq_of hx
  erw  [cov.snd_triv_proj (T% σ x),
       ← t.pushCovDer_ofSect (cov.isCovariantDerivativeOn.mono fun _ _ ↦ mem_univ _) hσ,
       hcov.cov_eq_proj s X₀ hs, t.mfderiv_comp_section hσ _ hx]

end CovariantDerivative
end horiz

end real

-- variable (E E') in
-- /-- The trivial connection on a trivial bundle, given by the directional derivative -/
-- @[simps]
-- noncomputable def trivial : CovariantDerivative 𝓘(𝕜, E) E'
--   (Bundle.Trivial E E') where
--   toFun X s := fun x ↦ fderiv 𝕜 s x (X x)
--   isCovariantDerivativeOn :=
--   { addX X X' σ x _ := by simp
--     smulX X σ c' x _ := by simp
--     addσ X σ σ' x hσ hσ' hx := by
--       rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ hσ'
--       rw [fderiv_add hσ hσ']
--       rfl
--     smul_const_σ X σ a x hx := by simp [fderiv_const_smul_of_field a]
--     leibniz X σ f x hσ hf hx := by
--       have : fderiv 𝕜 (f • σ) x = f x • fderiv 𝕜 σ x + (fderiv 𝕜 f x).smulRight (σ x) :=
--         fderiv_smul (by simp_all) (by simp_all)
--       simp [this, bar]
--       rfl }

end
