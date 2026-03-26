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

lemma Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R : Type*) {B : Type*} {F : Type*}
    {E : B → Type*} [NontriviallyNormedField R] [(x : B) → AddCommMonoid (E x)]
    [(x : B) → Module R (E x)]
    [NormedAddCommGroup F] [NormedSpace R F]
    [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
    [(x : B) → TopologicalSpace (E x)] [FiberBundle F E] (e : Trivialization F TotalSpace.proj)
    [Trivialization.IsLinear R e] {b : B} (hb : b ∈ e.baseSet) (y : E b) :
    (continuousLinearMapAt R e b) y = (e ⟨b, y⟩).2 := by
  simp [coe_linearMapAt_of_mem e hb]

attribute [simp] Bundle.Trivialization.coe_linearMapAt_of_mem

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

@[expose] public section -- TODO: think if we want to expose all definitions!

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
    ∃ s : M → F, MDiffAt s x ∧
                 s x = f ∧
                 mfderiv I 𝓘(𝕜, F) s x u = v ∧
                 cov s x u = 0 := by
  constructor
  · intro huv
    simp only [horiz, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, projection_apply] at huv
    let w : TangentSpace 𝓘(𝕜, F) f := v
    by_cases hu : u = 0
    · subst hu
      replace huv : v = 0 := by simpa using huv
      subst huv
      use fun x ↦ f
      simp [mdifferentiableAt_const]
    rcases map_of_one_jet_spec u w (by tauto) with ⟨h, h', h''⟩
    use map_of_one_jet u w, h', h, h''
    · rw [hcov.eq_one_form]
      · simp only [w, h]
        convert huv
        convert ContinuousLinearMap.add_apply (M₁ := TangentSpace I x) (M₂ := F) _
          (hcov.one_form x f) u
        exact h''.symm
      · rwa [mdifferentiableAt_section]
  · rintro ⟨s, s_diff, rfl, rfl, covs⟩
    simp only [horiz, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, projection_apply, ← covs]
    rw [hcov.eq_one_form (mdifferentiableAt_section_trivial_iff.mpr s_diff)]
    rfl

end projection_trivial_bundle

end IsCovariantDerivativeOn

namespace Bundle.Trivialization

section to_trivialization

variable (e : Trivialization F (π F V)) [VectorBundle 𝕜 F V] [MemTrivializationAtlas e]
  [IsManifold I 1 M]

noncomputable
def pushCovDer
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)) :
    (M → F) → (Π x : M, TangentSpace I x →L[𝕜] F) :=
  fun σ x ↦ e.continuousLinearMapAt 𝕜 x ∘L (cov (e.funToSec σ) x)


-- FIXME Decide whether we want to add enough assumption to use the commented out statement
omit [IsManifold I 1 M] in
lemma pushCovDer_secToFun -- [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 F] [IsManifold I 1 M]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [ContMDiffVectorBundle 1 F V I]
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hcov : IsCovariantDerivativeOn F cov e.baseSet)
    {u : TangentSpace I x} {σ : Π x : M, V x} {x : M}
    (hσ : MDiffAt T%σ x)
    (hx : x ∈ e.baseSet := by assumption) :
--  e.pushCovDer cov (e.secToFun σ) x = (e.linearEquivAt 𝕜 x hx).toContinuousLinearMap ∘L (cov σ x)
    e.pushCovDer cov (e.secToFun σ) x u = (e (cov σ x u)).2 := by
  have : cov (e.funToSec (e.secToFun σ)) x = cov σ x := by
    apply hcov.congr_of_eqOn _ hσ (e.baseSet_mem_nhds hx)
    · simp +contextual
    · rw [(e.total_funToSec_secToFun_eventuallyEq hx σ).mdifferentiableAt_iff]
      exact hσ
  unfold pushCovDer
  simp [this, hx]

omit [IsManifold I 1 M] in
lemma pushCovDer_funToSec [FiniteDimensional 𝕜 F]
    [IsManifold I 1 M]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [ContMDiffVectorBundle 1 F V I]
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    {x : M} {s : M → F}
    (hx : x ∈ e.baseSet := by assumption) :
    cov (e.funToSec s) x = e.symmL 𝕜 x ∘L (e.pushCovDer cov s x) := by
  ext u
  simp [pushCovDer, hx]

variable {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    -- {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)

lemma pushCovDer_isCovariantDerivativeOn
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [ContMDiffVectorBundle 1 F V I]
    {u : Set M} (hu : u ⊆ e.baseSet)
    (hcov : IsCovariantDerivativeOn F cov u) :
    IsCovariantDerivativeOn F (e.pushCovDer cov) u where
  add {σ σ' x} hσ hσ' hx := by
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
    rw [← ContinuousLinearMap.comp_add, ← hcov.add hs hs' hx]
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

-- This is PAIIIIINNNN and currently unused
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

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
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

lemma mem_horiz_iff_exists [FiniteDimensional 𝕜 E]
    {cov : CovariantDerivative I F V} {v : TotalSpace F V}
    (w : TangentSpace (I.prod 𝓘(𝕜, F)) v) :
    letI u := mfderiv (I.prod 𝓘(𝕜, F)) I TotalSpace.proj v w
    w ∈ cov.horiz v ↔ ∃ σ : Π x, V x,
                        MDiffAt (T% σ) v.proj ∧
                        σ v.proj = v ∧
                        mfderiv% (T% σ) v.proj u = w ∧
                        cov σ v.proj u = 0
    := by
  set u := mfderiv (I.prod 𝓘(𝕜, F)) I TotalSpace.proj v w with u_def
  set t := trivializationAt F V v.proj with t_def
  set Tvt := t.deriv I v with Tvt_def
  have hcov := cov.isCovariantDerivativeOn_pushCovDer t
  have hvproj : v.proj ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' v.proj
  have hTvtw : (Tvt w).1 = u :=
    t.mfderiv_proj_fst_deriv hvproj w |>.symm
  simp_rw [cov.comap_trivializationAt_horiz v, ← t_def, ← Tvt_def, Submodule.mem_comap,
           hcov.mem_horiz_iff_exists]
  constructor
  · rintro ⟨s, sdiff, sval, mfderivs, covs⟩
    use t.funToSec s, ?_, ?_, ?_
    · rw [ContinuousLinearMap.coe_coe] at covs
      simp [t.pushCovDer_funToSec cov, ← hTvtw, covs, t.symm_map_zero 𝕜]
    · exact t.mdifferentiableAt_funToSec hvproj sdiff
    · simp [sval, hvproj]

    · -- TODO needs a lot of cleanup here
      -- TODO cleanup those erw by understanding why we sometimes have Tvt and
      -- sometimes Tvt.toLinerMap
      erw [hTvtw] at mfderivs
      rw [u_def, t.mfderiv_total_funToSec hvproj]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.coe_id', id_eq]
      erw [mfderivs]
      rw [t.mfderiv_proj_fst_deriv hvproj]
      have : (((Trivialization.deriv I t v) w).1, (Tvt w).2) = Tvt w := rfl
      erw [this, Tvt_def, t.funToSec_proj_eq hvproj sval]
      exact t.derivInv_deriv_apply hvproj w

  · rintro ⟨σ, σdiff, σval, mfderivσ, covσ⟩
    use t.secToFun σ, ?_, ?_, ?_
    · rw [t.pushCovDer_secToFun cov.isCovariantDerivativeOn σdiff]
      -- TODO cleanup those erw by understanding why we sometimes have Tvt and
      -- sometimes Tvt.toLinerMap
      erw [hTvtw, covσ]
      exact t.map_zero 𝕜 hvproj
    · exact Trivialization.mdifferentiableAt_secToFun t hvproj σdiff
    · exact t.secToFun_apply_of_eq σval
    · erw [hTvtw]
      rw [t.mfderiv_secToFun_apply hvproj, mfderivσ, σval]
      rfl

end CovariantDerivative
end horiz

-- variable (E E') in
-- /-- The trivial connection on a trivial bundle, given by the directional derivative -/
-- @[simps]
-- noncomputable def trivial : CovariantDerivative 𝓘(𝕜, E) E'
--   (Bundle.Trivial E E') where
--   toFun X s := fun x ↦ fderiv 𝕜 s x (X x)
--   isCovariantDerivativeOn :=
--   { addX X X' σ x _ := by simp
--     smulX X σ c' x _ := by simp
--     add X σ σ' x hσ hσ' hx := by
--       rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ hσ'
--       rw [fderiv_add hσ hσ']
--       rfl
--     smul_constX σ a x hx := by simp [fderiv_const_smul_of_field a]
--     leibniz X σ f x hσ hf hx := by
--       have : fderiv 𝕜 (f • σ) x = f x • fderiv 𝕜 σ x + (fderiv 𝕜 f x).smulRight (σ x) :=
--         fderiv_smul (by simp_all) (by simp_all)
--       simp [this, bar]
--       rfl }

end
