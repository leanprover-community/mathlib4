/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Data.Matrix.Action
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Group actions on projectivization

Show that (among other groups), the general linear group of `V` acts on `ℙ K V`.
-/

@[expose] public section

open LinearAlgebra.Projectivization Matrix

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

end DivisionRing

section Field

variable {K : Type*} [Field K]

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

end Field

end Projectivization
