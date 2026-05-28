/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Group actions on projectivization

Show that (among other groups), the general linear group
and the special linear groups of `V` act on `ℙ K V`.

Prove that these actions are 2-transitive.

## TODO

Generalize to the special linear group over a division ring.

-/

@[expose] public section

open scoped LinearAlgebra.Projectivization Matrix

namespace Projectivization

section DivisionRing

variable {G K V : Type*} [AddCommGroup V] [DivisionRing K] [Module K V]
  [Group G] [DistribMulAction G V] [SMulCommClass G K V]

/-- Any group acting `K`-linearly on `V` (such as the general linear group) acts on `ℙ V`. -/
@[simps -isSimp]
instance : MulAction G (ℙ K V) where
  smul g x := x.map (DistribMulAction.toModuleEnd _ _ g)
    (DistribMulAction.toLinearEquiv _ _ g).injective
  one_smul x := show map _ _ _ = _ by simp [map_one, Module.End.one_eq_id]
  mul_smul g g' x := show map _ _ _ = map _ _ (map _ _ _) by
    simp_rw [map_mul, Module.End.mul_eq_comp]
    rw [map_comp, Function.comp_apply]

lemma generalLinearGroup_smul_def (g : LinearMap.GeneralLinearGroup K V) (x : ℙ K V) :
    g • x = x.map g.toLinearEquiv.toLinearMap g.toLinearEquiv.injective := by
  rfl

lemma matrixSpecialLinearGroup_smul_def {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    (g : Matrix.SpecialLinearGroup ι F) (x : ℙ F (ι → F)) :
    g • x = g.toLin'_equiv • x := by
  rfl

@[simp]
lemma smul_mk (g : G) {v : V} (hv : v ≠ 0) :
    g • mk K v hv = mk K (g • v) ((smul_ne_zero_iff_ne g).mpr hv) :=
  rfl

section transitivity

open MulAction FiniteDimensional LinearEquiv

variable (K V) in
instance linearEquiv_is_two_pretransitive :
    IsMultiplyPretransitive (V ≃ₗ[K] V) (ℙ K V) 2 := by
  rw [is_two_pretransitive_iff]
  intro D D' E E' hD hE
  have qD {D D' : ℙ K V} (hD : LinearIndependent K ![D.rep, D'.rep]) :
    hD.linearCombinationEquiv (Finsupp.single 0 1) = D.rep := by simp
  have qD' {D D' : ℙ K V} (hD : LinearIndependent K ![D.rep, D'.rep]) :
    hD.linearCombinationEquiv (Finsupp.single 1 1) = D'.rep := by simp
  rw [← linearIndependent_pair_iff_ne] at hD hE
  let f := hD.linearCombinationEquiv.symm ≪≫ₗ hE.linearCombinationEquiv
  have : FiniteDimensional K (Submodule.span K (Set.range ![D.rep, D'.rep])) :=
    span_of_finite K (Set.finite_range _)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  use g
  constructor
  · rw [← mk_rep D, ← mk_rep E, smul_mk, mk_eq_mk_iff]
    use 1
    simp only [one_smul, LinearEquiv.smul_def, ← qD hD, ← hg, ← qD hE]
    simp [f]
  · rw [← mk_rep D', ← mk_rep E', smul_mk, mk_eq_mk_iff]
    use 1
    simp only [one_smul, LinearEquiv.smul_def, ← qD' hD, ← hg, ← qD' hE]
    simp [f]

variable (K V) in
instance generalLinearGroup_is_two_pretransitive :
    IsMultiplyPretransitive (LinearMap.GeneralLinearGroup K V) (ℙ K V) 2 := by
  let f : ℙ K V →ₑ[LinearMap.GeneralLinearGroup.ofLinearEquiv (R := K) (M := V)] ℙ K V := {
    toFun := id
    map_smul' e D := by
      simp only [id_eq]
      rw [← mk_rep D, smul_mk, smul_mk]
      dsimp }
  exact IsPretransitive.of_embedding (f := f) Function.surjective_id

end transitivity

end DivisionRing

section Field

open MulAction LinearEquiv SpecialLinearGroup

variable {K V : Type*} [AddCommGroup V] [Field K] [Module K V]

theorem specialLinearGroup_smul_def (g : SpecialLinearGroup K V) (D : ℙ K V) :
    g • D = g.toLinearEquiv • D := rfl

variable (K V) in
instance specialLinearGroup_is_two_pretransitive :
    IsMultiplyPretransitive (SpecialLinearGroup K V) (ℙ K V) 2 := by
  have := linearEquiv_is_two_pretransitive K V
  rw [is_two_pretransitive_iff] at this ⊢
  intro D D' E E' hD hE
  obtain ⟨g, gD, gE⟩ := this hD hE
  by_cases hV : FiniteDimensional K V
  · suffices ∀ a : Kˣ, ∃ h : V ≃ₗ[K] V, h.det = a ∧ h • D = D ∧ h • D' = D' by
      obtain ⟨h, hdet, hD, hE⟩ := this (g.det)⁻¹
      use ⟨g * h, by simp [hdet]⟩
      simp [specialLinearGroup_smul_def, toLinearEquiv_eq_coe, mul_smul, gD, hD, gE, hE]
    intro a
    rw [← linearIndependent_pair_iff_ne] at hD
    have := linearIndepOn_pair D D'
    let s := (linearIndepOn_pair D D').extend (Set.subset_univ _)
    let b : Module.Basis s K V := Module.Basis.extend this
    rw [← mk_rep D, ← mk_rep D']
    have hD_mem : D.rep ∈ s := LinearIndepOn.subset_extend _ _ (by simp)
    have hD'_mem : D'.rep ∈ s := LinearIndepOn.subset_extend _ _ (by simp)
    refine ⟨dilatransvection (f := b.coord ⟨D.rep, hD_mem⟩)
      (v := (a.val - 1) • b ⟨D.rep, hD_mem⟩) (by simp), ?_, ?_, ?_⟩
    · simp [← Units.val_inj, coe_det, LinearMap.transvection.det]
    · rw [smul_mk, mk_eq_mk_iff, LinearEquiv.smul_def]
      use a
      rw [← coe_coe, dilatransvection.coe_toLinearMap,
        LinearMap.transvection.apply, Module.Basis.coord_apply]
      suffices (b.repr D.rep) ⟨D.rep, hD_mem⟩ = 1 by
        rw [this, Module.Basis.extend_apply_self, Units.smul_def]
        module
      nth_rewrite 1 [show D.rep = (⟨D.rep, hD_mem⟩ : s) from by rfl]
      rw [← Module.Basis.extend_apply_self, Module.Basis.repr_self]
      simp
    · rw [smul_mk, mk_eq_mk_iff, LinearEquiv.smul_def]
      use 1
      rw [one_smul, ← coe_coe, dilatransvection.coe_toLinearMap,
        LinearMap.transvection.apply, Module.Basis.coord_apply]
      suffices (b.repr D'.rep) ⟨D.rep, hD_mem⟩ = 0 by
        rw [Module.Basis.extend_apply_self]
        simp [this]
      nth_rewrite 1 [show D'.rep = (⟨D'.rep, hD'_mem⟩ : s) from by rfl]
      rw [← Module.Basis.extend_apply_self, Module.Basis.repr_self]
      apply Finsupp.single_eq_of_ne
      simp only [ne_eq, ← Subtype.coe_inj]
      intro h
      apply Fin.zero_ne_one
      apply hD.injective
      simp [h]
  use ⟨g, by
    rw [← Units.val_inj, coe_det]
    apply LinearMap.det_eq_one_of_not_module_finite hV⟩
  simp [← gD, ← gE, specialLinearGroup_smul_def, toLinearEquiv_eq_coe]

/-- The special linear group `SpecialLinearGroup K V` acts primitively on `ℙ K V`. -/
instance : IsPreprimitive (SpecialLinearGroup K V) (ℙ K V) :=
  isPreprimitive_of_is_two_pretransitive inferInstance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

instance : IsMultiplyPretransitive (Matrix.SpecialLinearGroup ι K) (ℙ K (ι → K)) 2 :=
  let φ : SpecialLinearGroup K (ι → K) →* Matrix.SpecialLinearGroup ι K :=
    Matrix.SpecialLinearGroup.toLin'_equiv.symm.toMonoidHom
  let f : ℙ K (ι → K) →ₑ[φ] ℙ K (ι → K) :=
    { toFun := id
      map_smul' g D := by simp [φ, matrixSpecialLinearGroup_smul_def]}
  IsPretransitive.of_embedding (f := f) Function.surjective_id

instance prePrimitive_SL : IsPreprimitive (Matrix.SpecialLinearGroup ι K) (ℙ K (ι → K)) :=
  isPreprimitive_of_is_two_pretransitive inferInstance

lemma SL_mulAction_ker :
    (MulAction.toPermHom (Matrix.SpecialLinearGroup ι K) (ℙ K (ι → K))).ker =
      Subgroup.center (Matrix.SpecialLinearGroup ι K) := by
  ext m
  simp only [MonoidHom.mem_ker, toPermHom_apply, Equiv.Perm.one_def, DFunLike.ext_iff, toPerm_apply,
    Equiv.refl_apply, Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨fun hm ↦ ?_, fun ⟨r, hr1, hr2⟩ l ↦ ?_⟩
  · if hι : IsEmpty ι then simp [← Matrix.ext_iff] else
    have (i : ι) := by
      simpa [mk_eq_mk_iff'] using hm (.mk K (Pi.single i 1) (by simp : Pi.single i 1 ≠ 0))
    obtain ⟨i⟩ := by simpa using hι
    simp only [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec_single,
      MulOpposite.op_one, one_smul, funext_iff, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Matrix.col_apply] at this
    have hm1 (i j : ι) (h : i ≠ j) : m i j = 0 := by
      simpa [h] using ((this j).choose_spec i).symm
    have hm2 (i j : ι) : m i i = m j j := by
      by_cases hij : i = j
      · rw [hij]
      replace hm (v : ι → K) (hv : v ≠ 0) := hm (.mk K v hv)
      simp only [ne_eq, smul_mk, mk_eq_mk_iff'] at hm
      have hv : (Pi.single i 1 + Pi.single j 1 : ι → K) ≠ 0 := by
        intro h
        have h1 := congr_fun h i
        simp [hij] at h1
      obtain ⟨a, ha⟩ := hm _ hv
      have hi := congr_fun ha i
      have hj := congr_fun ha j
      simp only [Pi.smul_apply, Pi.add_apply, Pi.single_eq_same, ne_eq, hij, not_false_eq_true,
        Pi.single_eq_of_ne, add_zero, smul_eq_mul, mul_one, smul_add,
        Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec_single,
        MulOpposite.op_one, one_smul, Matrix.col_apply, hm1 i j hij, Ne.symm hij, zero_add,
        hm1 j i (Ne.symm hij)] at hi hj
      rw [← hi, ← hj]
    use m i i
    have := m.2
    rw [← Matrix.IsDiag.diagonal_diag hm1, Matrix.det_diagonal] at this
    simp only [Matrix.diag_apply] at this
    rw [Finset.prod_eq_pow_card (b := m i i) (fun j _ ↦ hm2 j i), Finset.card_univ] at this
    nth_rw 3 [← Matrix.IsDiag.diagonal_diag hm1]
    simpa [this, funext_iff] using hm2 i
  · induction l using Projectivization.ind with | _ v hv =>
    simp only [smul_mk, mk_eq_mk_iff']
    use r
    change _ = m.1 • v
    simp [← hr2]

/-- The action of the special linear group on `ℙ F (ι → F)` factors through the
projective special linear group `PSL = SL ⧸ Z(SL)`. -/
def PSLAction.toPermHom :
    Matrix.ProjectiveSpecialLinearGroup ι K →* Equiv.Perm (ℙ K (ι → K)) :=
  QuotientGroup.lift _ (MulAction.toPermHom _ _) (le_of_eq SL_mulAction_ker.symm)

instance : MulAction (Matrix.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι → K)) :=
  MulAction.compHom _ PSLAction.toPermHom

lemma _root_.Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk (g : Matrix.SpecialLinearGroup ι K)
    (p : ℙ K (ι → K)) : (g : Matrix.ProjectiveSpecialLinearGroup ι K) • p = g • p := rfl

theorem Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective :
    Function.Injective (PSLAction.toPermHom (K := K) (ι := ι)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rwa [← MonoidHom.mem_ker, PSLAction.toPermHom,
    QuotientGroup.ker_lift, SL_mulAction_ker, QuotientGroup.map_mk'_self,
    Subgroup.mem_bot] at hg

instance : FaithfulSMul (Matrix.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι → K)) :=
  faithfulSMul_iff.2 fun g hg ↦
    Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective <| Equiv.ext fun x ↦ by
      simpa using hg x

instance : IsPreprimitive (Matrix.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι → K)) :=
  @MulAction.IsPreprimitive.of_surjective _ _ _ _ _ _ _ _ (QuotientGroup.mk' _)
    {toFun := id, map_smul' := by intros; simp; rfl} (prePrimitive_SL (ι := ι) (K := K))
    Function.surjective_id

end Field

end Projectivization
