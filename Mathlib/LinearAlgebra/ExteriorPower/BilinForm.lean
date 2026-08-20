/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Kirill Kondrashov
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Bilinear forms on exterior powers

For a bilinear form `B` on a module `M`, we define the bilinear form induced by `B`
on each exterior power.

For finite free modules, we also prove that bijectivity of `B` implies
bijectivity of the induced linear map.

## Definitions

* `exteriorPower.BilinForm`: the bilinear form induced on an exterior power.

## Theorems

* `exteriorPower.bilinForm_nondegenerate`: bijectivity of `B` is preserved on exterior powers.

-/

noncomputable section

open Function
open Module
open scoped Matrix

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (k : ℕ)
  (B : LinearMap.BilinForm R M)

-- TODO: Generalize `matrixOf_updateCol` and `matrixOf_updateRow` beyond bilinear forms.
lemma matrixOf_updateCol {ι : Type*} [DecidableEq ι] (v w : ι → M) (z : M) (l : ι) :
    (Matrix.of fun i j ↦ B (v i) (Function.update w l z j)) =
      (Matrix.of fun i j ↦ B (v i) (w j)).updateCol l (fun i ↦ B (v i) z) := by
  ext i j
  simp only [update_apply, Matrix.of_apply, Matrix.updateCol_apply]
  aesop

lemma matrixOf_updateRow {ι : Type*} [DecidableEq ι] (v w : ι → M) (z : M) (l : ι) :
    (Matrix.of fun i j ↦ B (Function.update v l z i) (w j)) =
      (Matrix.of fun i j ↦ B (v i) (w j)).updateRow l (fun j ↦ B z (w j)) := by
  ext i j
  simp only [update_apply, Matrix.of_apply, Matrix.updateRow_apply]
  aesop

def pairingMatrix (v w : Fin k → M) : Matrix (Fin k) (Fin k) R :=
  Matrix.of fun i j ↦ B (v i) (w j)

/--
TODO: Remove the explicit `DecidableEq` argument from `MultilinearMap`; then the
`Subsingleton.elim` cases below should disappear. The current API requires them because
the alternating-map laws carry an implicit decidability instance.
-/
def BilinFormAux :
    M [⋀^Fin k]→ₗ[R] M [⋀^Fin k]→ₗ[R] R where
  toFun v :=
    { toFun := fun w ↦ (pairingMatrix k B v w).det
      map_update_add' := fun {_i} w l x y ↦ by
        cases Subsingleton.elim _i (by clear _i; infer_instance)
        simp only [pairingMatrix, matrixOf_updateCol, map_add,
          ← Matrix.det_updateCol_add _ l _ _]
        congr
      map_update_smul' := fun {_i} w l t x ↦ by
        cases Subsingleton.elim _i (by clear _i; infer_instance)
        simp only [pairingMatrix, matrixOf_updateCol, map_smul, smul_eq_mul,
          ← Matrix.det_updateCol_smul _ l t _]
        congr
      map_eq_zero_of_eq' := fun w l₁ l₂ hl hl' ↦
        Matrix.det_zero_of_column_eq hl' <| by simp [pairingMatrix, hl] }
  map_update_add' {_i} v l x y := by
    cases Subsingleton.elim _i (by clear _i; infer_instance)
    ext w
    simp only [AlternatingMap.coe_mk, MultilinearMap.coe_mk, AlternatingMap.add_apply,
      pairingMatrix, matrixOf_updateRow, map_add, LinearMap.add_apply,
      ← Matrix.det_updateRow_add _ l _ _]
    congr
  map_update_smul' {_i} v l t x := by
    cases Subsingleton.elim _i (by clear _i; infer_instance)
    ext w
    simp only [AlternatingMap.coe_mk, MultilinearMap.coe_mk, AlternatingMap.smul_apply, smul_eq_mul,
      pairingMatrix, matrixOf_updateRow, map_smul, LinearMap.smul_apply, smul_eq_mul,
      ← Matrix.det_updateRow_smul _ l t _]
    congr
  map_eq_zero_of_eq' v l₁ l₂ hl hl' :=
    AlternatingMap.ext fun w ↦ Matrix.det_zero_of_row_eq hl' <| funext fun i ↦
      by simp [pairingMatrix, hl]

/-- A bilinear form on `M` induces a bilinear form on each exterior power.

TODO: `exteriorPower.alternatingMapLinearEquiv` should be renamed to
`exteriorPower.liftAlternatingEquiv` for consistency with `ExteriorAlgebra.liftAlternatingEquiv`
(and to fit our naming scheme better). -/
public protected def BilinForm : LinearMap.BilinForm R (⋀[R]^k M) :=
  exteriorPower.alternatingMapLinearEquiv (R := R) (M := M) (N := R) (n := k) ∘ₗ
    exteriorPower.alternatingMapLinearEquiv (BilinFormAux k B)

lemma bijective_pairingDual [Module.Finite R M] [Module.Free R M] (k : ℕ) :
    Bijective (pairingDual R M k) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton (⋀[R]^k (Dual R M)) := Module.subsingleton R _
    exact bijective_of_subsingleton' _
  · classical
    obtain ⟨I, b⟩ := Module.Free.exists_basis R M
    let : LinearOrder I := linearOrderOfSTO WellOrderingRel
    have : Finite I := Module.Finite.finite_basis b
    let e := b.dualBasis.exteriorPower k
    let d := (b.exteriorPower k).dualBasis
    have hpairingDual_eq_constr : pairingDual R M k = e.constr R d := by
      apply e.ext
      intro s
      simp only [Basis.constr_basis]
      simpa [e, d] using pairingDual_apply_dualBasis_exteriorPower R b k s
    rw [hpairingDual_eq_constr]
    refine ⟨e.injective_constr_of_linearIndependent d.linearIndependent, ?_⟩
    rw [← LinearMap.range_eq_top, Basis.constr_range, d.span_eq]

@[simp] lemma bilinForm_ιMulti_ιMulti {k : ℕ} (C : LinearMap.BilinForm R M)
    (v w : Fin k → M) :
    exteriorPower.BilinForm k C (ιMulti R k v) (ιMulti R k w) =
      (Matrix.of fun i j ↦ C (v i) (w j)).det := by
  simp [exteriorPower.BilinForm, BilinFormAux, pairingMatrix]

lemma bilinForm_eq_pairingDual_comp_map {k : ℕ} (C : LinearMap.BilinForm R M) :
    exteriorPower.BilinForm k C =
      (pairingDual R M k).comp (exteriorPower.map k C) := by
  apply exteriorPower.linearMap_ext
  ext v w
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
  rw [bilinForm_ιMulti_ιMulti C v w]
  simp only [map_apply_ιMulti, pairingDual_ιMulti_ιMulti]
  rw [← Matrix.det_transpose]
  rfl

section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

public lemma bilinForm_nondegenerate [Module.Free R M] [Module.Finite R M] (k : ℕ)
    (B : LinearMap.BilinForm R M) (hB : Bijective B) :
    Bijective (exteriorPower.BilinForm k B) := by
  rw [bilinForm_eq_pairingDual_comp_map (k := k) B, LinearMap.coe_comp]
  refine (bijective_pairingDual k).comp ⟨?_, ?_⟩
  · exact exteriorPower.map_injective (LinearEquiv.ofBijective _ hB).symm (by ext; simp)
  · exact exteriorPower.map_surjective hB.surjective

end

end exteriorPower
