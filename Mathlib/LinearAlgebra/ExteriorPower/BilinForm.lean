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

The main definition in this file is basis-independent: it constructs the bilinear form induced on
an exterior power by a bilinear form.

## Definitions

* `exteriorPower.BilinForm`: the bilinear form induced on an exterior power.

## Theorems

* `exteriorPower.bilinForm_nondegenerate`: nondegeneracy is preserved over a field.
-/

noncomputable section

open Function
open Module
open scoped Matrix

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (k : ℕ)
  (B : LinearMap.BilinForm R M)

-- TODO: Generalize `matrixOf_updateCol` and `matrixOf_updateRow` beyond bilinear forms.
-- In `BilinFormAux` we use these identities when one of the two families is updated,
-- so that the determinant update lemmas apply.
/-- Updating `w` at `l` replaces column `l` by `fun i ↦ B (v i) z`. -/
lemma matrixOf_updateCol {ι : Type*} [DecidableEq ι] (v w : ι → M) (z : M) (l : ι) :
    (Matrix.of fun i j ↦ B (v i) (Function.update w l z j)) =
      (Matrix.of fun i j ↦ B (v i) (w j)).updateCol l (fun i ↦ B (v i) z) := by
  ext i j
  simp only [update_apply, Matrix.of_apply, Matrix.updateCol_apply]
  aesop

/-- Updating `v` at `l` replaces row `l` by `fun j ↦ B z (w j)`. -/
lemma matrixOf_updateRow {ι : Type*} [DecidableEq ι] (v w : ι → M) (z : M) (l : ι) :
    (Matrix.of fun i j ↦ B (Function.update v l z i) (w j)) =
      (Matrix.of fun i j ↦ B (v i) (w j)).updateRow l (fun j ↦ B z (w j)) := by
  ext i j
  simp only [update_apply, Matrix.of_apply, Matrix.updateRow_apply]
  aesop

/-- The matrix whose `(i, j)` entry is `B (v i) (w j)`. -/
def pairingMatrix (v w : Fin k → M) : Matrix (Fin k) (Fin k) R :=
  Matrix.of fun i j ↦ B (v i) (w j)

/-- The nested alternating map `(v, w) ↦ det (fun i j ↦ B (v i) (w j))` used to define `BilinForm`.

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

-- `BilinFormAux` is an implementation detail and is intentionally hidden from the public API.
/-- A bilinear form on `M` induces a bilinear form on each exterior power.

TODO: `exteriorPower.alternatingMapLinearEquiv` should be renamed to
`exteriorPower.liftAlternatingEquiv` for consistency with `ExteriorAlgebra.liftAlternatingEquiv`
(and to fit our naming scheme better). -/
public protected def BilinForm : LinearMap.BilinForm R (⋀[R]^k M) :=
  exteriorPower.alternatingMapLinearEquiv (R := R) (M := M) (N := R) (n := k) ∘ₗ
    exteriorPower.alternatingMapLinearEquiv (BilinFormAux k B)

lemma bijective_pairingDual [Module.Finite R M] [Module.Free R M] (k : ℕ) :
    Bijective (pairingDual R M k) := by
  -- Split into the subsingleton and nontrivial cases for the coefficient ring.
  rcases subsingleton_or_nontrivial R with hR | hR
  · -- If `R` is subsingleton, every `R`-module is subsingleton.
    let : Subsingleton R := hR
    -- The source of `pairingDual` is subsingleton.
    have : Subsingleton (⋀[R]^k (Module.Dual R M)) := Module.subsingleton R _
    -- Its target is subsingleton as well.
    have : Subsingleton (Module.Dual R (⋀[R]^k M)) := Module.subsingleton R _
    -- Hence every map between these modules is injective and surjective, which is bijectivity.
    exact ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩
  · -- In the nontrivial case, use the finite basis argument below.
    let : Nontrivial R := hR
    classical
    -- Choose a finite ordered basis of `M`.
    obtain ⟨I, b⟩ := Module.Free.exists_basis R M
    let : LinearOrder I := linearOrderOfSTO WellOrderingRel
    have : Finite I := Module.Finite.finite_basis b
    let e := b.dualBasis.exteriorPower k
    let d := (b.exteriorPower k).dualBasis
    -- Express `pairingDual` as the map sending the basis `e` to the basis `d`.
    have hpairingDual_eq_constr : pairingDual R M k = e.constr R d := by
      -- It suffices to compare the two maps on the basis `e`.
      apply e.ext
      intro s
      -- On the basis vector indexed by `s`, both maps give the corresponding vector `d s`.
      simp only [Basis.constr_basis]
      simpa [e, d] using pairingDual_apply_dualBasis_exteriorPower R b k s
    rw [hpairingDual_eq_constr]
    refine ⟨e.injective_constr_of_linearIndependent d.linearIndependent, ?_⟩
    rw [← LinearMap.range_eq_top, Basis.constr_range, d.span_eq]

/-- On wedges of `k` vectors, `BilinForm` is the determinant of the matrix of pairings. -/
@[simp] public lemma bilinForm_ιMulti_ιMulti {k : ℕ} (C : LinearMap.BilinForm R M)
    (v w : Fin k → M) :
    exteriorPower.BilinForm k C (ιMulti R k v) (ιMulti R k w) =
      (Matrix.of fun i j ↦ C (v i) (w j)).det := by
  -- Unfold the composition defining `BilinForm`.
  simp only [exteriorPower.BilinForm, LinearMap.comp_apply]
  -- Evaluate the inner alternating map on `ιMulti v`.
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (BilinFormAux k C) v]
  -- Evaluate the outer alternating map on `ιMulti w`.
  calc
    (exteriorPower.alternatingMapLinearEquiv (BilinFormAux k C v)) (ιMulti R k w) =
        (BilinFormAux k C v) w :=
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (BilinFormAux k C v) w
    (BilinFormAux k C v) w = (Matrix.of fun i j ↦ C (v i) (w j)).det := by
      rfl

/-- `BilinForm` is the composition of `exteriorPower.map` with `pairingDual`.

This auxiliary lemma is used in `bilinForm_nondegenerate`. -/
lemma bilinForm_eq_pairingDual_comp_map {k : ℕ} (C : LinearMap.BilinForm R M) :
    exteriorPower.BilinForm k C =
      (pairingDual R M k).comp (exteriorPower.map k C) := by
  -- It suffices to check the equality on wedges of `k` vectors.
  apply exteriorPower.linearMap_ext
  ext v w
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
  rw [bilinForm_ιMulti_ιMulti C v w]
  simp only [map_apply_ιMulti, pairingDual_ιMulti_ιMulti]
  -- The second matrix is the transpose of the first one.
  rw [← Matrix.det_transpose]
  rfl

/-- Swapping the arguments of `BilinForm` gives the form induced by `C.flip`.

This auxiliary lemma is used in `bilinForm_nondegenerate`. -/
lemma bilinForm_flip {k : ℕ} (C : LinearMap.BilinForm R M) :
    (exteriorPower.BilinForm k C).flip = exteriorPower.BilinForm k C.flip := by
  -- It suffices to check the equality on wedges of `k` vectors.
  apply exteriorPower.linearMap_ext
  ext v w
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.BilinForm.flip_apply]
  rw [bilinForm_ιMulti_ιMulti C w v, bilinForm_ιMulti_ιMulti C.flip v w]
  -- The second matrix is the transpose of the first one.
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
