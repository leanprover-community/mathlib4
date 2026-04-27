/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Matrix.Action
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Transvection.Basic

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

variable {K V : Type*} [AddCommGroup V] [Field K] [Module K V]

/-- The fixed points of an invertible linear map acting on the projectivization of a vector
space are precisely the eigenspaces. -/
theorem smul_eq_self_iff' {M : Type*} [AddCommGroup M] [Module K M]
    {g : LinearMap.GeneralLinearGroup K M} {y : Projectivization K M} :
    g • y = y ↔ ∃ a, y.submodule ≤ Module.End.eigenspace g a := by
  induction y with | h y hy =>
  simp only [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff,
    SetLike.le_def, Module.End.mem_eigenspace_iff, Projectivization.submodule_mk,
    Submodule.mem_span_singleton, forall_exists_index]
  constructor
  · refine fun ⟨a, hay⟩ ↦ ⟨a, fun x b hxb ↦ ?_⟩
    simp [← hxb, smul_comm _ b, ← a.smul_def, g.smul_def, hay]
  · rintro ⟨a, ha⟩
    refine ⟨.mk0 a (fun ha' ↦ hy ?_), (ha 1 (one_smul ..)).symm⟩
    specialize ha 1 rfl
    exact (smul_eq_zero_iff_eq g).mp (by aesop)

theorem smul_eq_self_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : GL ι K} {y : Projectivization K (ι → K)} :
    g • y = y ↔ ∃ a, y.submodule ≤ Module.End.eigenspace g.toLin a :=
  smul_eq_self_iff' (g := g.toLin)
open MulAction LinearEquiv SpecialLinearGroup

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

end Field

end Projectivization
