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

/-- If `b` is a finite ordered basis of `M`, then `pairingDual` on the `k`th exterior power is
injective.

This auxiliary lemma is used in `bilinForm_nondegenerate`. -/
lemma pairingDual_injective_of_basis {I : Type*} [Finite I] [LinearOrder I]
    (b : Basis I R M) (k : ℕ) :
    Function.Injective (pairingDual R M k) := by
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
  -- The basis map is injective because `d` is linearly independent.
  rw [hpairingDual_eq_constr]
  exact e.injective_constr_of_linearIndependent d.linearIndependent

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

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]

/-- The determinant-induced form on every exterior power is nondegenerate over a field when `B` is.

The assumptions `[Module.Free R M] [Module.Finite R M]` provide the finite basis used below. The
field assumption is used to lift injectivity of `B` and `B.flip` to their exterior powers. -/
public lemma bilinForm_nondegenerate (k : ℕ) (B : LinearMap.BilinForm R M)
    [Module.Free R M] [Module.Finite R M]
    (hB : B.Nondegenerate) :
    (exteriorPower.BilinForm k B).Nondegenerate := by
  classical
  -- 1. Choose a finite ordered basis of `M`.
  obtain ⟨I, b⟩ := Module.Free.exists_basis R M
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  have : Finite I := Module.Finite.finite_basis b
  -- 2. Obtain injectivity of `B`, `B.flip`, and their exterior-power maps.
  -- The left-separating part of `hB` gives `LinearMap.ker B = ⊥`.
  have hB_left : Function.Injective B := LinearMap.ker_eq_bot.mp hB.ker_eq_bot
  -- The same kernel argument applies to `B.flip`.
  have hB_flip : Function.Injective B.flip := LinearMap.ker_eq_bot.mp hB.flip.ker_eq_bot
  have hB_exteriorPower : Function.Injective (exteriorPower.map k B) :=
    exteriorPower.map_injective_field hB_left
  have hB_flip_exteriorPower : Function.Injective (exteriorPower.map k B.flip) :=
    exteriorPower.map_injective_field hB_flip
  -- 3. Use the chosen basis to prove injectivity of `pairingDual`.
  have hpairingDual : Function.Injective (pairingDual R M k) :=
    pairingDual_injective_of_basis b k
  -- 4. Use the auxiliary identities to express the induced form and its flip as compositions.
  constructor
  · -- 5. Check left-separation using the two injectivity results.
    rw [LinearMap.separatingLeft_iff_linear_nontrivial]
    intro x hx
    apply hB_exteriorPower
    apply hpairingDual
    -- Rewrite the vanishing of the induced form using the composition identity.
    simpa only [bilinForm_eq_pairingDual_comp_map (k := k) B, LinearMap.comp_apply, map_zero]
      using hx
  · -- 6. Check right-separation by applying the same argument to `B.flip`.
    rw [LinearMap.separatingRight_iff_linear_flip_nontrivial]
    intro x hx
    have hBilinForm_flip_x : exteriorPower.BilinForm k B.flip x = 0 := by
      -- Rewrite the flip of the induced form using the flip identity.
      rw [← bilinForm_flip (k := k) B]
      exact hx
    apply hB_flip_exteriorPower
    apply hpairingDual
    -- Rewrite the vanishing condition using the composition lemma.
    simpa only [bilinForm_eq_pairingDual_comp_map (k := k) B.flip, LinearMap.comp_apply, map_zero]
      using hBilinForm_flip_x

end

end exteriorPower
