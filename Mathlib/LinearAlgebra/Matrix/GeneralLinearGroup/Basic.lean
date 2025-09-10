/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Ring.Action.ConjAct

/-!
# Basic lemmas about the general linear group $GL(n, R)$

This file lists various basic lemmas about the general linear group $GL(n, R)$. For the definitions,
see `LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`.
-/

namespace Matrix

open Matrix LinearMap

variable {R n : Type*} [Fintype n]

/-- This takes in a non-unital algebra homomorphism `f` and vectors `y, z : n → R`
and constructs a linear operator on `(n → R)` such that `x ↦ f (vecMulVec x y) *ᵥ z`. -/
private def auxLinear [Semiring R] (f : Matrix n n R →ₗ[R] Matrix n n R) (y z : n → R) :
    (n → R) →ₗ[R] (n → R) :=
  (mulVecBilin R ℕ).flip z ∘ₗ (f : Matrix n n R →ₗ[R] Matrix n n R) ∘ₗ (vecMulVecBilin R ℕ).flip y

@[simp]
private theorem auxLinear_apply [Semiring R]
    (f : Matrix n n R →ₙₐ[R] Matrix n n R) (x y z : n → R) :
  auxLinear f y z x = f (vecMulVec x y) *ᵥ z := rfl

theorem auxLinear_mulVec [CommSemiring R]
    (f : Matrix n n R →ₙₐ[R] Matrix n n R) (y z : n → R) (A : Matrix n n R) (x : n → R) :
    auxLinear f y z (A *ᵥ x) = f A *ᵥ auxLinear f y z x := by
  let T := auxLinear f y z
  calc
    _ = f (vecMulVec (A *ᵥ x) y) *ᵥ z := by simp [auxLinear_apply]
    _ = f (A * vecMulVec x y) *ᵥ z := by
      simp_rw [vecMulVec_eq Unit, replicateCol_mulVec, ← Matrix.mul_assoc]
    _ = (f A * f (vecMulVec x y)) *ᵥ z := by simp_rw [map_mul]
    _ = f A *ᵥ T x := by simp only [← mulVec_mulVec]; rfl

variable [DecidableEq n]

private theorem toMatrix'_auxLinear_mul [CommSemiring R]
    (f : Matrix n n R →ₙₐ[R] Matrix n n R) (y z : n → R) (A : Matrix n n R) :
    (auxLinear f y z).toMatrix' * A = f A * (auxLinear f y z).toMatrix' :=
  toLin'.injective <| LinearMap.ext fun x => by simpa using auxLinear_mulVec f y z A x

/-- Given an algebra automorphism `f` on `Matrix n n R`, there exists an invertible matrix `T`
such that `f` is given by `x ↦ T * x * T⁻¹`. -/
theorem AlgEquiv.coe_eq_generalLinearGroup_conjugate [Field R]
    (f : Matrix n n R ≃ₐ[R] Matrix n n R) :
    ∃ T : GL n R, ⇑f = fun x => T * x * ((T⁻¹ : GL n R) : Matrix n n R) := by
  obtain hn | hn := isEmpty_or_nonempty n
  · exact ⟨1, Subsingleton.elim _ _⟩
  simp_rw [funext_iff, @eq_comm _ (f _), Units.mul_inv_eq_iff_eq_mul, @eq_comm _ _ (f _ * _)]
  obtain ⟨u, v, hu, hv⟩ : ∃ u v : n → R, u ≠ 0 ∧ v ≠ 0 := ⟨1, 1, one_ne_zero, one_ne_zero⟩
  obtain ⟨z, hz⟩ : ∃ z : n → R, f (vecMulVec u v) *ᵥ z ≠ 0 := by
    simp_rw [ne_eq, ← not_forall]
    suffices ¬ f (vecMulVec u v) = 0 by
      rwa [← toMatrix'_toLin' (f _), EmbeddingLike.map_eq_zero_iff, LinearMap.ext_iff] at this
    rw [← ne_eq, EmbeddingLike.map_ne_zero_iff]
    exact vecMulVec_ne_zero hu hv
  let T := auxLinear f.toAlgHom v z
  have this A : T.toMatrix' * A = f A * T.toMatrix' :=
    toMatrix'_auxLinear_mul f.toAlgHom.toNonUnitalAlgHom v z A
  suffices hM : IsUnit T.toMatrix' from ⟨hM.unit, fun A => this A |>.symm⟩
  simp_rw [← isUnit_toLin'_iff, toLin'_toMatrix', isUnit_iff_range_eq_top, range_eq_top]
  intro w
  obtain ⟨q, hq : T u q ≠ 0⟩ := Function.ne_iff.mp hz
  let d : n → R := Pi.single q (T u q)⁻¹
  have hd : T u ⬝ᵥ d = 1 := by rw [dotProduct_single, mul_inv_cancel₀ hq]
  use f.symm (vecMulVec w d) *ᵥ u
  have h : f (f.symm (vecMulVec w d)) *ᵥ T u = w := by
    rw [f.apply_symm_apply, vecMulVec_mulVec, dotProduct_comm, hd, MulOpposite.op_one, one_smul]
  simp_rw [← toMatrix'_mulVec, mulVec_mulVec, this, ← mulVec_mulVec, toMatrix'_mulVec, h]

/-- Alternate statement of `coe_eq_generalLinearGroup_conjugate`. -/
theorem mulSemiringActionToAlgEquiv_conjAct_surjective [Field R] :
    Function.Surjective (MulSemiringAction.toAlgEquiv (G := ConjAct (GL n R)) R (Matrix n n R)) :=
  fun f => f.coe_eq_generalLinearGroup_conjugate.imp fun _ h => (DFunLike.coe_injective h).symm

/-- Algebra automorphisms on matrices preserve the trace. -/
theorem trace_algEquiv_apply [Field R] (f : Matrix n n R ≃ₐ[R] Matrix n n R) (x : Matrix n n R) :
    trace (f x) = trace x := by
  obtain ⟨T, hT⟩ := f.coe_eq_generalLinearGroup_conjugate
  simp [hT, trace_mul_cycle (T : Matrix n n R)]

section Examples

/-- The matrix [a, -b; b, a] (inspired by multiplication by a complex number); it is an element of
$GL_2(R)$ if `a ^ 2 + b ^ 2` is nonzero. -/
@[simps! -fullyApplied val]
def planeConformalMatrix {R} [Field R] (a b : R) (hab : a ^ 2 + b ^ 2 ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) R :=
  GeneralLinearGroup.mkOfDetNeZero !![a, -b; b, a] (by simpa [det_fin_two, sq] using hab)

/- TODO: Add Iwasawa matrices `n_x=!![1,x; 0,1]`, `a_t=!![exp(t/2),0;0,exp(-t/2)]` and
  `k_θ=!![cos θ, sin θ; -sin θ, cos θ]`
-/
end Examples

namespace GeneralLinearGroup

section Center

variable {R n : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The center of `GL n R` consists of scalar matrices. -/
lemma mem_center_iff_val_eq_scalar {g : GL n R} :
    g ∈ Subgroup.center (GL n R) ↔ g.val ∈ Set.range (scalar _) := by
  rcases isEmpty_or_nonempty n
  · simpa [Subsingleton.elim (Subgroup.center _) ⊤] using ⟨1, Subsingleton.elim _ _⟩
  constructor
  · intro hg
    refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun t ↦ ?_
    simpa [Units.ext_iff] using Subgroup.mem_center_iff.mp hg (.mk _ _ t.mul_inv t.inv_mul)
  · refine fun ⟨a, ha⟩ ↦ Subgroup.mem_center_iff.mpr fun h ↦ ?_
    simpa [Units.ext_iff, ← ha] using (scalar_commute a (mul_comm a ·) h.val).symm

/-- The center of `GL n R` is the image of `Rˣ`. -/
lemma center_eq_range_units :
    Subgroup.center (GL n R) = (Units.map (algebraMap R _).toMonoidHom).range := by
  ext g
  -- eliminate tedious case `n = ∅`
  rcases isEmpty_or_nonempty n
  · simpa [Subsingleton.elim (Subgroup.center _) ⊤] using ⟨1, Subsingleton.elim _ _⟩
  constructor
  · -- previous lemma shows the underlying matrix is scalar, but now need to show
    -- the scalar is a unit; so we apply argument both to `g` and `g⁻¹`
    intro hg
    obtain ⟨a, ha⟩ := mem_center_iff_val_eq_scalar.mp hg
    obtain ⟨b, hb⟩ := mem_center_iff_val_eq_scalar.mp (Subgroup.inv_mem _ hg)
    have hab : a * b = 1 := by
      simpa [-mul_inv_cancel, ← ha, ← hb, ← diagonal_one, Units.ext_iff] using mul_inv_cancel g
    refine ⟨⟨a, b, hab, mul_comm a b ▸ hab⟩, ?_⟩
    simp [Units.ext_iff, ← ha, algebraMap_eq_diagonal]
  · rintro ⟨a, rfl⟩
    exact mem_center_iff_val_eq_scalar.mpr ⟨a, rfl⟩

end Center

end GeneralLinearGroup

end Matrix
