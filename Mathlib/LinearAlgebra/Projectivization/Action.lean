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

theorem linearIndependent_pair_iff_ne {D D' : ℙ K V} :
  LinearIndependent K ![D.rep, D'.rep] ↔ D ≠ D' := by
    rw [LinearIndependent.pair_iff' (rep_nonzero _)]
    refine ⟨fun h hD ↦ h 1 (by simp [hD]), fun h a hD ↦ h ?_⟩
    rw [eq_comm, ← mk_rep D, ← mk_rep D', mk_eq_mk_iff]
    suffices a ≠ 0 by refine ⟨(Ne.isUnit this).unit, by simp [← hD]⟩
    exact fun ha ↦ D'.rep_nonzero (by simp [← hD, ha])

theorem linearIndependentOn_pair (D D' : ℙ K V) :
    LinearIndepOn K id {D.rep, D'.rep} := by
  by_cases h : D = D'
  · simpa [h] using D'.rep_nonzero
  rw [← ne_eq, ← linearIndependent_pair_iff_ne, LinearIndependent.pair_symm_iff,
    ← linearIndepOn_id_range_iff] at h
  · simpa using h
  · simpa [injective_pair_iff_ne, injective_pair_iff_ne, ne_eq] using h.injective
theorem LinearEquiv.exists_restrict_eq
    {W W' : Submodule K V} [FiniteDimensional K W] (f : W ≃ₗ[K] W') :
    ∃ g : V ≃ₗ[K] V, ∀ x : W, f x = g x := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl W
  let eQ := W.prodEquivOfIsCompl Q hQ
  obtain ⟨Q', hQ'⟩ := Submodule.exists_isCompl W'
  let eQ' := W'.prodEquivOfIsCompl Q' hQ'
  suffices Nonempty (Q ≃ₗ[K] Q') by
    let ⟨h⟩ := this
    refine ⟨eQ.symm ≪≫ₗ (LinearEquiv.prodCongr f h) ≪≫ₗ eQ', by aesop⟩
  refine LinearEquiv.nonempty_equiv_iff_rank_eq.mpr ?_
  rw [← Cardinal.add_right_inj_of_lt_aleph0 (γ := Module.rank K W),
    add_comm, ← rank_prod', LinearEquiv.nonempty_equiv_iff_rank_eq.mp ⟨eQ⟩,
    add_comm, LinearEquiv.nonempty_equiv_iff_rank_eq.mp ⟨f⟩,
    ← rank_prod', LinearEquiv.nonempty_equiv_iff_rank_eq.mp ⟨eQ'⟩]
  exact Module.rank_lt_aleph0 K ↥W

variable (K V) in
instance linearEquiv_is_two_pretransitive :
    MulAction.IsMultiplyPretransitive (V ≃ₗ[K] V) (ℙ K V) 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro D D' E E' hD hE
  have qD {D D' : ℙ K V} (hD : LinearIndependent K ![D.rep, D'.rep]) :
    hD.linearCombinationEquiv (Finsupp.single 0 1) = D.rep := by simp
  have qD' {D D' : ℙ K V} (hD : LinearIndependent K ![D.rep, D'.rep]) :
    hD.linearCombinationEquiv (Finsupp.single 1 1) = D'.rep := by simp
  rw [← linearIndependent_pair_iff_ne] at hD hE
  let f := hD.linearCombinationEquiv.symm ≪≫ₗ hE.linearCombinationEquiv
  have : FiniteDimensional K (Submodule.span K (Set.range ![D.rep, D'.rep])) :=
    FiniteDimensional.span_of_finite K (Set.finite_range _)
  obtain ⟨g, hg⟩ := LinearEquiv.exists_restrict_eq f
  use g
  constructor
  · rw [← Projectivization.mk_rep D, ← Projectivization.mk_rep E, smul_mk,
      mk_eq_mk_iff]
    use 1
    simp only [one_smul, LinearEquiv.smul_def, ← qD hD, ← hg, ← qD hE]
    simp [f]
  · rw [← Projectivization.mk_rep D', ← Projectivization.mk_rep E', smul_mk,
      mk_eq_mk_iff]
    use 1
    simp only [one_smul, LinearEquiv.smul_def, ← qD' hD, ← hg, ← qD' hE]
    simp [f]

variable (K V) in
instance generalLinearGroup_is_two_pretransitive :
    MulAction.IsMultiplyPretransitive (LinearMap.GeneralLinearGroup K V) (ℙ K V) 2 := by
  let f : ℙ K V →ₑ[LinearMap.GeneralLinearGroup.ofLinearEquiv (R := K) (M := V)] ℙ K V := {
    toFun := id
    map_smul' e D := by
      simp only [id_eq]
      rw [← mk_rep D, smul_mk, smul_mk]
      congr }
  exact MulAction.IsPretransitive.of_embedding (f := f) Function.surjective_id

end DivisionRing

section Field

variable {K V : Type*} [AddCommGroup V] [Field K] [Module K V]

/-- The natural action of `SpecialLinearGroup K V` on `V`. -/
instance : DistribMulAction (SpecialLinearGroup K V) V :=
  DistribMulAction.compHom  _ (SpecialLinearGroup.toLinearEquiv)

theorem _root_.SpecialLinearGroup.smul_def (g : SpecialLinearGroup K V) (v : V) :
    g • v = g.toLinearEquiv • v := rfl

theorem _root_.SpecialLinearGroup.toLinearEquiv_eq_coe (g : SpecialLinearGroup K V) :
    g.toLinearEquiv = (g : V ≃ₗ[K] V) := rfl

instance : SMulCommClass (SpecialLinearGroup K V) K V where
  smul_comm g a v := by
    simp [SpecialLinearGroup.smul_def]

theorem specialLinearGroup_smul_def (g : SpecialLinearGroup K V) (D : ℙ K V) :
    g • D = g.toLinearEquiv • D := rfl

def _root_.LinearEquiv.dilatransvection_of_isUnit
    (f : Module.Dual K V) (v : V) (ha : IsUnit (1 + f v)) :
    V ≃ₗ[K] V where
  toLinearMap := LinearMap.transvection f v
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

theorem _root_.LinearEquiv.coe_dilatransvection_of_isUnit
    {f : Module.Dual K V} {v : V} {hfv : IsUnit (1 + f v)} :
    LinearEquiv.dilatransvection_of_isUnit f v hfv = LinearMap.transvection f v :=
  rfl

theorem _root_.LinearMap.transvection.det (f : Module.Dual K V) (v : V) :
    (LinearMap.transvection f v).det = 1 + f v := sorry

variable (K V) in
instance specialLinearGroup_is_two_pretransitive :
    MulAction.IsMultiplyPretransitive (SpecialLinearGroup K V) (ℙ K V) 2 := by
  have := linearEquiv_is_two_pretransitive K V
  rw [MulAction.is_two_pretransitive_iff] at this ⊢
  intro D D' E E' hD hE
  obtain ⟨g, gD, gE⟩ := this hD hE
  by_cases hV : FiniteDimensional K V
  · suffices ∀ a : Kˣ, ∃ h : V ≃ₗ[K] V, h.det = a ∧ h • D = D ∧ h • D' = D' by
      obtain ⟨h, hdet, hD, hE⟩ := this (g.det)⁻¹
      use ⟨g * h, by simp [hdet]⟩
      simp [specialLinearGroup_smul_def,
        SpecialLinearGroup.toLinearEquiv_eq_coe, mul_smul, gD, hD, gE, hE]
    intro a
    rw [← linearIndependent_pair_iff_ne] at hD
    have := linearIndependentOn_pair D D'
    let s := (linearIndependentOn_pair D D').extend (Set.subset_univ _)
    let b : Module.Basis s K V := Module.Basis.extend this
    rw [← Projectivization.mk_rep D, ← Projectivization.mk_rep D']
    have hD_mem : D.rep ∈ s := LinearIndepOn.subset_extend _ _ (by simp)
    have hD'_mem : D'.rep ∈ s := LinearIndepOn.subset_extend _ _ (by simp)
    refine ⟨LinearEquiv.dilatransvection_of_isUnit (b.coord ⟨D.rep, hD_mem⟩)
      ((a.val - 1) • b ⟨D.rep, hD_mem⟩) (by simp), ?_, ?_, ?_⟩
    · simp [← Units.val_inj, LinearEquiv.coe_det,
        LinearEquiv.coe_dilatransvection_of_isUnit, LinearMap.transvection.det]
    · rw [Projectivization.smul_mk, mk_eq_mk_iff, LinearEquiv.smul_def]
      use a
      rw [← LinearEquiv.coe_coe, LinearEquiv.coe_dilatransvection_of_isUnit,
        LinearMap.transvection.apply]
      rw [Module.Basis.coord_apply]
      suffices (b.repr D.rep) ⟨D.rep, hD_mem⟩ = 1 by
        rw [this, Module.Basis.extend_apply_self, Units.smul_def]
        module
      nth_rewrite 1 [show D.rep = (⟨D.rep, hD_mem⟩ : s) from by rfl]
      rw [← Module.Basis.extend_apply_self, Module.Basis.repr_self]
      simp
    · rw [Projectivization.smul_mk, mk_eq_mk_iff, LinearEquiv.smul_def]
      use 1
      rw [one_smul, ← LinearEquiv.coe_coe,
        LinearEquiv.coe_dilatransvection_of_isUnit, LinearMap.transvection.apply]
      rw [Module.Basis.coord_apply]
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
    rw [← Units.val_inj, LinearEquiv.coe_det]
    apply LinearMap.det_eq_one_of_not_module_finite hV⟩
  simp [← gD, ← gE, specialLinearGroup_smul_def, SpecialLinearGroup.toLinearEquiv_eq_coe]

/-- The special linear group `SpecialLinearGroup K V` acts primitively on `ℙ K V`. -/
instance : MulAction.IsPreprimitive (SpecialLinearGroup K V) (ℙ K V) :=
  MulAction.isPreprimitive_of_is_two_pretransitive inferInstance

end Field

end Projectivization
