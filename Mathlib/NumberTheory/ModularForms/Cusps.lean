/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
--import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Cusps
-/

open Matrix SpecialLinearGroup UpperHalfPlane Filter

open scoped MatrixGroups LinearAlgebra.Projectivization OnePoint ModularForm

namespace LinearMap.GeneralLinearGroup

variable {K L V W : Type*} [Semiring K] [Semiring L]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]
  {σ : K →+* L} {σ' : L →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

/-- A semilinear equivalence from `V` to `W` determines an isomorphism of general linear
groups. -/
def compLinearEquiv (e : V ≃ₛₗ[σ] W) : GeneralLinearGroup K V ≃* GeneralLinearGroup L W where
  toFun g := ofLinearEquiv (e.symm.trans <| g.toLinearEquiv.trans e)
  invFun h := ofLinearEquiv (e.trans <| h.toLinearEquiv.trans e.symm)
  map_mul' g g' := Units.ext <| LinearMap.ext <| by simp [ofLinearEquiv, toLinearEquiv]
  left_inv g := Units.ext <| LinearMap.ext <| by simp [ofLinearEquiv, toLinearEquiv]
  right_inv h := by
    rw [← (generalLinearEquiv _ _).toEquiv.injective.eq_iff]
    ext v : 1
    simp [ofLinearEquiv, toLinearEquiv]

end LinearMap.GeneralLinearGroup

namespace Projectivization

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- The general linear group of `V` acts on `ℙ V`. -/
instance instGLAction : MulAction (LinearMap.GeneralLinearGroup K V) (ℙ K V) where
  smul g x := x.map g.toLinearEquiv.toLinearMap g.toLinearEquiv.injective
  one_smul := congr_fun Projectivization.map_id
  mul_smul g g' x := congr_fun (Projectivization.map_comp
    g'.toLinearEquiv.toLinearMap _ g.toLinearEquiv.toLinearMap _ _) x

lemma smul_apply
    (g : LinearMap.GeneralLinearGroup K V) (x : ℙ K V) :
    g • x = x.map g.toLinearEquiv.toLinearMap g.toLinearEquiv.injective := by
  rfl

lemma smul_mk (g : LinearMap.GeneralLinearGroup K V) {v : V} (hv : v ≠ 0) :
    g • Projectivization.mk K v hv =
      Projectivization.mk K (g • v) ((smul_ne_zero_iff_ne _).mpr hv) := by
  rfl

/-- For a field `K`, the group `GL(2, K)` acts on `ℙ K (K × K)`. -/
instance instGLFinAction {K : Type*} [Field K] : MulAction (GL n K) (ℙ K (n → K)) :=
  .compHom _ <| Matrix.GeneralLinearGroup.toLin.toMonoidHom

/-- For a field `K`, the group `GL(2, K)` acts on `ℙ K (K × K)`. -/
instance instGLFinTwoAction {K : Type*} [Field K] : MulAction (GL (Fin 2) K) (ℙ K (K × K)) :=
  .compHom _ <| (Matrix.GeneralLinearGroup.toLin.trans
    <| LinearMap.GeneralLinearGroup.compLinearEquiv <| LinearEquiv.finTwoArrow K K).toMonoidHom

end Projectivization

namespace OnePoint

variable {K : Type*} [Field K] [DecidableEq K]

/-- For a field `K`, the group `GL(2, K)` acts on `OnePoint K`. -/
instance instGLAction : MulAction (GL (Fin 2) K) (OnePoint K) :=
  (equivProjectivization K).mulAction (GL (Fin 2) K)

lemma smul_infty_def (g : GL (Fin 2) K) :
    g • ∞ = (equivProjectivization K).symm (.mk K (g 0 0, g 1 0) (fun h ↦ by
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at h
      simpa [det_fin_two, h] using g.det_ne_zero)) := by
  by_cases h : g 1 0 = 0 <;>
  simp [h, Equiv.smul_def, MulAction.compHom_smul_def, Projectivization.smul_mk,
    LinearMap.GeneralLinearGroup.compLinearEquiv, mulVec_eq_sum,
    LinearMap.GeneralLinearGroup.toLinearEquiv, LinearMap.GeneralLinearGroup.ofLinearEquiv]

@[simp]
lemma smul_infty_eq_ite (g : GL (Fin 2) K) :
    (g • ∞ : OnePoint K) = if g 1 0 = 0 then ∞ else g 0 0 / g 1 0 := by
  by_cases h : g 1 0 = 0 <;>
  simp [h, div_eq_inv_mul, smul_infty_def]

lemma smul_infty_eq_iff (g : GL (Fin 2) K) :
    g • (∞ : OnePoint K) = ∞ ↔ g 1 0 = 0 := by
  simp

/-- The modular group `SL(2, A)` acts transitively on `OnePoint K`, if `A` is a PID whose fraction
field is `K`. (This includes the case `A = ℤ`, `K = ℚ`.) -/
lemma exists_mem_SL2 (A : Type*) [CommRing A] [IsDomain A] [Algebra A K] [IsFractionRing A K]
    [IsPrincipalIdealRing A] (c : OnePoint K) :
    ∃ g : SL(2, A), mapGL K g • ∞ = c := by
  cases c with
  | infty => use 1; simp
  | coe q =>
    obtain ⟨g, hg0, hg1⟩ := (IsFractionRing.num_den_reduced A q).isCoprime.exists_SL2_col 0
    use g
    have : mapGL K g 1 0 ≠ 0 := by simp [hg1]
    simp [hg0, hg1]

end OnePoint

lemma tendsto_smul_atImInfty {g : GL (Fin 2) ℝ} (hg : g 1 0 = 0) :
    Tendsto (fun τ ↦ g • τ) atImInfty atImInfty := by
  suffices Tendsto (fun τ ↦ |g 0 0 / g 1 1| * τ.im) atImInfty atTop by
    simpa [atImInfty, Function.comp_def, im_smul, num, denom, hg, abs_div, abs_mul,
      abs_of_pos (UpperHalfPlane.im_pos _), mul_div_right_comm]
  apply tendsto_comap.const_mul_atTop
  simpa [Matrix.det_fin_two, hg] using g.det_ne_zero

/-- The type of cusps of `Γ`, i.e. orbits for the action of `Γ` on `ℚ ∪ ∞`. -/
def Cusp (Γ : Subgroup SL(2, ℤ)) := MulAction.orbitRel.Quotient (Γ.map (mapGL ℚ)) (OnePoint ℚ)

/-- Surjection from `SL(2, ℤ) / Γ` to cusps of `Γ`. Mostly useful for showing that `Cusp Γ` is
finite for finite-index subgroups. -/
noncomputable def cosetToCusp (Γ : Subgroup SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ → Cusp Γ :=
  Quotient.lift fun g ↦ ⟦mapGL ℚ g⁻¹ • ∞⟧ (by
    intro a b hab
    rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    use ⟨_, Γ.mem_map_of_mem _ (QuotientGroup.leftRel_apply.mp hab)⟩
    rw [Subgroup.smul_def, Subgroup.coe_mk, ← MulAction.mul_smul, ← map_mul, mul_inv_cancel_right])

lemma cosetToCusp_apply (Γ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    cosetToCusp Γ ⟦g⟧ = ⟦mapGL ℚ g⁻¹ • ∞⟧ :=
  rfl

lemma surjective_cosetToCusp (Γ : Subgroup SL(2, ℤ)) : (cosetToCusp Γ).Surjective := by
  rintro ⟨c⟩
  obtain ⟨g, rfl⟩ := c.exists_mem_SL2 ℤ
  use ⟦g⁻¹⟧
  rw [cosetToCusp_apply, inv_inv, Quotient.mk]

/-- A finite-index subgroup has finitely many cusps. -/
instance instFiniteOfFiniteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : Finite (Cusp Γ) :=
  .of_surjective _ (surjective_cosetToCusp Γ)

section IsBoundedAtImInfty

lemma UpperHalfPlane.IsZeroAtImInfty.slash {g : GL (Fin 2) ℝ} (hg : g 1 0 = 0) {f : ℍ → ℂ}
    (hf : IsZeroAtImInfty f) (k : ℤ) : IsZeroAtImInfty (f ∣[k] g) := by
  simp only [IsZeroAtImInfty, ZeroAtFilter] at hf ⊢
  rw [tendsto_zero_iff_norm_tendsto_zero] at hf ⊢
  have (z : ℂ) : ‖σ g z‖ = ‖z‖ := by simp only [σ]; split_ifs <;> simp
  simpa [this, ModularForm.slash_def, denom, hg, mul_assoc]
    using (hf.comp <| tendsto_smul_atImInfty hg).mul_const _

lemma UpperHalfPlane.IsBoundedAtImInfty.slash {g : GL (Fin 2) ℝ} (hg : g 1 0 = 0) {f : ℍ → ℂ}
    (hf : IsBoundedAtImInfty f) (k : ℤ) : IsBoundedAtImInfty (f ∣[k] g) := by
  simp only [IsBoundedAtImInfty, BoundedAtFilter] at hf ⊢
  rw [← Asymptotics.isBigO_norm_left] at hf ⊢
  have (z : ℂ) : ‖σ g z‖ = ‖z‖ := by simp only [σ]; split_ifs <;> simp
  simp only [this, ModularForm.slash_def, denom, hg, Complex.ofReal_zero, zero_mul, zero_add,
    norm_mul, mul_assoc]
  simpa only [mul_comm (‖f _‖)] using
    (hf.comp_tendsto (tendsto_smul_atImInfty hg)).const_mul_left _

end IsBoundedAtImInfty

section IsBoundedAt

/-- We say `f` is bounded at `c` if, for all `g` with `g • ∞ = c`, the function `f ∣[k] g` is
bounded at `∞`. -/
def OnePoint.IsBoundedAt (c : OnePoint ℚ) (f : ℍ → ℂ) (k : ℤ) : Prop :=
    ∀ (g : GL (Fin 2) ℚ), g • ∞ = c → IsBoundedAtImInfty (f ∣[k] (g.map <| algebraMap ℚ ℝ))

/-- We say `f` is zero at `c` if, for all `g` with `g • ∞ = c`, the function `f ∣[k] g` is
zero at `∞`. -/
def OnePoint.IsZeroAt (c : OnePoint ℚ) (f : ℍ → ℂ) (k : ℤ) : Prop :=
    ∀ (g : GL (Fin 2) ℚ), g • ∞ = c → IsZeroAtImInfty (f ∣[k] (g.map <| algebraMap ℚ ℝ))

lemma OnePoint.isBoundedAt_iff_forall_GL2Q (c : OnePoint ℚ) (f : ℍ → ℂ) (k : ℤ) :
    IsBoundedAt c f k ↔ ∀ (g : GL (Fin 2) ℚ), g • ∞ = c
      → IsBoundedAtImInfty (f ∣[k] (g.map <| algebraMap ℚ ℝ)) :=
  Iff.rfl

lemma OnePoint.isZeroAt_iff_forall_GL2Q (c : OnePoint ℚ) (f : ℍ → ℂ) (k : ℤ) :
    IsZeroAt c f k ↔ ∀ (g : GL (Fin 2) ℚ), g • ∞ = c
      → IsZeroAtImInfty (f ∣[k] (g.map <| algebraMap ℚ ℝ)) :=
  Iff.rfl

/-- Tedious lemma: if `γ ∈ SL(2, ℤ)` and `g ∈ GL(2, ℝ)` both map . -/
private lemma OnePoint.SL2Z_trans_eq_GL2Z_trans {c : OnePoint ℚ} {γ : SL(2, ℤ)} {g : GL (Fin 2) ℚ}
    (hγ : (mapGL ℚ) γ • ∞ = c) (hg : g • ∞ = c) :
    ((mapGL ℝ γ)⁻¹ * (g.map (algebraMap ℚ ℝ))) 1 0 = 0 := by
  have h1 : g.map (algebraMap ℚ ℝ) • ∞ = (g • ∞).map (algebraMap ℚ ℝ) := by
    by_cases h : g 1 0 = 0 <;> simp [h]
  have h2 : mapGL ℝ γ • ∞ = (mapGL ℚ γ • ∞).map (algebraMap ℚ ℝ) := by
    by_cases h : γ 1 0 = 0 <;> simp [h]
  rw [← OnePoint.smul_infty_eq_iff, MulAction.mul_smul, inv_smul_eq_iff, h1, h2, hg, hγ]

lemma OnePoint.isBoundedAt_iff_exists_SL2Z {c : OnePoint ℚ} {f : ℍ → ℂ} {k : ℤ}:
    IsBoundedAt c f k ↔ ∃ γ : SL(2, ℤ), mapGL ℚ γ • ∞ = c ∧ IsBoundedAtImInfty (f ∣[k] γ) := by
  refine ⟨fun h ↦ match c.exists_mem_SL2 ℤ with | ⟨γ, hγ⟩ => ⟨γ, hγ, by simpa using h _ hγ⟩, ?_⟩
  rintro ⟨γ, hγ, hf⟩ g hg
  replace hf : IsBoundedAtImInfty (f ∣[k] (mapGL ℝ γ)) := by
    simpa only [ModularForm.SL_slash] using hf
  simpa [← SlashAction.slash_mul] using hf.slash (c.SL2Z_trans_eq_GL2Z_trans hγ hg) k

lemma OnePoint.isZeroAt_iff_exists_SL2Z {c : OnePoint ℚ} {f : ℍ → ℂ} {k : ℤ} :
    IsZeroAt c f k ↔ ∃ γ : SL(2, ℤ), mapGL ℚ γ • ∞ = c ∧ IsZeroAtImInfty (f ∣[k] γ) := by
  refine ⟨fun h ↦ match c.exists_mem_SL2 ℤ with | ⟨γ, hγ⟩ => ⟨γ, hγ, by simpa using h _ hγ⟩, ?_⟩
  rintro ⟨γ, hγ, hf⟩ g hg
  replace hf : IsZeroAtImInfty (f ∣[k] (mapGL ℝ γ)) := by
    simpa only [ModularForm.SL_slash] using hf
  simpa [← SlashAction.slash_mul] using hf.slash (c.SL2Z_trans_eq_GL2Z_trans hγ hg) k

lemma OnePoint.isBoundedAt_iff_forall_SL2Z {c : OnePoint ℚ} {f : ℍ → ℂ} {k : ℤ} :
    IsBoundedAt c f k ↔ ∀ γ : SL(2, ℤ), (mapGL ℚ γ) • ∞ = c → IsBoundedAtImInfty (f ∣[k] γ) :=
  ⟨fun hc _ hγ ↦ by simpa using hc _ hγ, fun hc ↦ match c.exists_mem_SL2 ℤ with
    | ⟨γ, hγ⟩ => c.isBoundedAt_iff_exists_SL2Z.mpr ⟨γ, hγ, hc _ hγ⟩⟩

lemma OnePoint.isZeroAt_iff_forall_SL2Z {c : OnePoint ℚ} {f : ℍ → ℂ} {k : ℤ} :
    IsZeroAt c f k ↔ ∀ γ : SL(2, ℤ), (mapGL ℚ γ) • ∞ = c → IsZeroAtImInfty (f ∣[k] γ) :=
  ⟨fun hc _ hγ ↦ by simpa using hc _ hγ, fun hc ↦ match c.exists_mem_SL2 ℤ with
    | ⟨γ, hγ⟩ => c.isZeroAt_iff_exists_SL2Z.mpr ⟨γ, hγ, hc _ hγ⟩⟩

lemma OnePoint.IsBoundedAt.slash {c : OnePoint ℚ} {f : ℍ → ℂ} {k : ℤ} {g : GL (Fin 2) ℚ} :
    IsBoundedAt c (f ∣[k] (g.map <| algebraMap ℚ ℝ)) k ↔ IsBoundedAt (g • c) f k := by
  simp only [isBoundedAt_iff_forall_GL2Q]
  rw [(Equiv.mulLeft g).forall_congr_left]
  simp [-smul_infty_eq_ite, MulAction.mul_smul, inv_smul_eq_iff, ← SlashAction.slash_mul]

lemma OnePoint.IsZeroAt.slash {c : OnePoint ℚ} {f : ℍ → ℂ} {k : ℤ} {g : GL (Fin 2) ℚ} :
    IsZeroAt c (f ∣[k] (g.map <| algebraMap ℚ ℝ)) k ↔ IsZeroAt (g • c) f k := by
  simp only [isZeroAt_iff_forall_GL2Q]
  rw [(Equiv.mulLeft g).forall_congr_left]
  simp [-smul_infty_eq_ite, MulAction.mul_smul, inv_smul_eq_iff, ← SlashAction.slash_mul]

end IsBoundedAt
