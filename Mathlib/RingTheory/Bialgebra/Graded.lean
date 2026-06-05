/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Bialgebra.Primitive
public import Mathlib.RingTheory.Coalgebra.Graded
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Graded bialgebras

Structural lemmas about graded connected bialgebras.

## References

* [Grinberg, D. and Reiner, V., *Hopf Algebras in Combinatorics*][grinberg-reiner-2020],
  Exercise 1.3.20(h) and the proof of Proposition 1.4.16.
-/

@[expose] public section

/-! ### Connectedness of a graded algebra -/

/-- A graded algebra is *connected* (in the Hopf-algebra sense) if its degree-zero part is
spanned by the unit element `1 : A`. -/
class Coalgebra.IsConnected {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {ι : Type*} [DecidableEq ι] [AddMonoid ι] (𝒜 : ι → Submodule R A) : Prop where
  /-- The degree-zero part is the `R`-span of `1`. -/
  eq_span_one : 𝒜 0 = Submodule.span R {(1 : A)}

namespace Coalgebra.IsConnected

variable {R A : Type*} [CommSemiring R] [Ring A] [Bialgebra R A]
variable (𝒜 : ℕ → Submodule R A) [Coalgebra.IsConnected 𝒜]

open Coalgebra TensorProduct

/-- Every element of the degree-zero part equals its counit times the unit. -/
theorem coe_eq_counit_smul_one {a : A} (ha : a ∈ 𝒜 0) : a = counit (R := R) a • 1 := by
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp (eq_span_one (𝒜 := 𝒜) ▸ ha)
  simp [Bialgebra.counit_one]

/-- The degree-zero submodule of a connected graded bialgebra is canonically isomorphic to
the base ring via the counit. -/
noncomputable def zeroLEquiv : 𝒜 0 ≃ₗ[R] R where
  toFun a := counit (a : A)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  invFun r := ⟨r • 1, eq_span_one (𝒜 := 𝒜) ▸ Submodule.smul_mem _ r (Submodule.subset_span rfl)⟩
  left_inv := fun ⟨a, ha⟩ => Subtype.ext (coe_eq_counit_smul_one 𝒜 ha).symm
  right_inv _ := by simp [Bialgebra.counit_one]

@[simp]
theorem zeroLEquiv_apply (a : 𝒜 0) : zeroLEquiv 𝒜 a = counit (a : A) := rfl

@[simp]
theorem zeroLEquiv_symm_apply_coe (r : R) : ((zeroLEquiv 𝒜).symm r : A) = r • 1 := rfl

end Coalgebra.IsConnected

namespace Bialgebra

variable {R A : Type*} [CommSemiring R] [Ring A] [Bialgebra R A]
variable (𝒜 : ℕ → Submodule R A)

open Coalgebra DirectSum LinearMap TensorProduct

/-- A linear map on `A ⊗[R] A` that carries each pure tensor of the bigraded part into a
submodule `S` carries the whole `⨆_{p+q=n} 𝒜 p ⊗ 𝒜 q` into `S`. -/
theorem apply_mem_of_mem_bigradedPart {M : Type*} [AddCommMonoid M] [Module R M]
    (f : A ⊗[R] A →ₗ[R] M) (S : Submodule R M) {n : ℕ}
    (h : ∀ {p q : ℕ}, p + q = n → ∀ (a : 𝒜 p) (b : 𝒜 q), f ((a : A) ⊗ₜ[R] (b : A)) ∈ S)
    {z : A ⊗[R] A}
    (hz : z ∈ ⨆ p, ⨆ q, ⨆ (_ : p + q = n),
      LinearMap.range (TensorProduct.map (𝒜 p).subtype (𝒜 q).subtype)) :
    f z ∈ S := by
  refine Submodule.mem_comap.mp <|
    (show (⨆ p, ⨆ q, ⨆ (_ : p + q = n),
        LinearMap.range (TensorProduct.map (𝒜 p).subtype (𝒜 q).subtype)) ≤
        Submodule.comap f S from ?_) hz
  refine iSup_le fun p => iSup_le fun q => iSup_le fun hpq => ?_
  rw [LinearMap.range_le_iff_comap, Submodule.eq_top_iff']
  intro w
  simp only [Submodule.mem_comap]
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact h hpq a b
  | add y₁ y₂ ih₁ ih₂ => simp only [map_add]; exact add_mem ih₁ ih₂

variable [GradedAlgebra 𝒜] [GradedCoalgebra 𝒜]

/-- The counit factors through the degree-zero projection. -/
theorem counit_eq_counit_comp_projZero (a : A) :
    counit (R := R) a = counit (GradedAlgebra.proj 𝒜 0 a) := by
  classical
  rw [GradedAlgebra.proj_apply]
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum]
  exact Finset.sum_eq_single 0
    (fun i _ hi => GradedCoalgebra.counit_eq_zero_of_ne_zero hi (DirectSum.decompose 𝒜 a i).2)
    (fun h => by simp [DFinsupp.notMem_support_iff.mp h])

variable [Coalgebra.IsConnected 𝒜]

/-- Under connectedness, the degree-zero projection equals `algebraMap ∘ counit`. -/
theorem proj_zero_eq_algebraMap_comp_counit :
    (GradedAlgebra.proj 𝒜 0 : A →ₗ[R] A) = Algebra.linearMap R A ∘ₗ counit := by
  ext x
  have hmem : GradedAlgebra.proj 𝒜 0 x ∈ 𝒜 0 := by
    rw [GradedAlgebra.proj_apply]; exact SetLike.coe_mem _
  rw [LinearMap.comp_apply, Algebra.linearMap_apply,
    Coalgebra.IsConnected.coe_eq_counit_smul_one 𝒜 hmem,
    ← counit_eq_counit_comp_projZero, ← Algebra.algebraMap_eq_smul_one]

/-- Applying `id ⊗ q_0` to `Δ(x)` gives `x ⊗ 1`, where `q_0 = GradedAlgebra.proj 𝒜 0`. -/
@[simp]
theorem lTensor_projZero_comul (x : A) :
    (LinearMap.lTensor A (GradedAlgebra.proj 𝒜 0)) (comul x) = x ⊗ₜ[R] (1 : A) := by
  rw [proj_zero_eq_algebraMap_comp_counit, LinearMap.lTensor_comp_apply,
    Coalgebra.lTensor_counit_comul]
  simp

/-- Applying `q_0 ⊗ id` to `Δ(x)` gives `1 ⊗ x`, where `q_0 = GradedAlgebra.proj 𝒜 0`. -/
@[simp]
theorem rTensor_projZero_comul (x : A) :
    (LinearMap.rTensor A (GradedAlgebra.proj 𝒜 0)) (comul x) = (1 : A) ⊗ₜ[R] x := by
  rw [proj_zero_eq_algebraMap_comp_counit, LinearMap.rTensor_comp_apply,
    Coalgebra.rTensor_counit_comul]
  simp

/-- In a connected graded bialgebra, every homogeneous element of degree 1 is primitive. -/
theorem isPrimitiveElem_of_mem_one {x : A} (hx : x ∈ 𝒜 1) : IsPrimitiveElem R x where
  counit_eq_zero := GradedCoalgebra.counit_eq_zero_of_ne_zero one_ne_zero hx
  comul_eq_tmul_one_add_one_tmul := by
    classical
    have hL : ((LinearMap.id - LinearMap.lTensor A (GradedAlgebra.proj 𝒜 0) -
        LinearMap.rTensor A (GradedAlgebra.proj 𝒜 0) :
        A ⊗[R] A →ₗ[R] A ⊗[R] A)) (comul x) = 0 := by
      refine (Submodule.mem_bot R).mp <| apply_mem_of_mem_bigradedPart 𝒜 _ ⊥
        (fun {p q} hpq a b => (Submodule.mem_bot R).mpr ?_) (GradedCoalgebra.comul_mem hx)
      simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq,
        LinearMap.lTensor_tmul, LinearMap.rTensor_tmul]
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : p = 0 ∧ q = 1 ∨ p = 1 ∧ q = 0 := by omega
      · rw [show GradedAlgebra.proj 𝒜 0 (a : A) = a from
              DirectSum.decompose_of_mem_same _ a.2,
            show GradedAlgebra.proj 𝒜 0 (b : A) = 0 from
              DirectSum.decompose_of_mem_ne _ b.2 one_ne_zero,
            TensorProduct.tmul_zero, sub_zero, sub_self]
      · rw [show GradedAlgebra.proj 𝒜 0 (a : A) = 0 from
              DirectSum.decompose_of_mem_ne _ a.2 one_ne_zero,
            show GradedAlgebra.proj 𝒜 0 (b : A) = b from
              DirectSum.decompose_of_mem_same _ b.2,
            TensorProduct.zero_tmul, sub_zero, sub_self]
    simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq] at hL
    rw [sub_sub, sub_eq_zero, lTensor_projZero_comul, rTensor_projZero_comul] at hL
    exact hL

/-- For `x ∈ 𝒜 n`, `Δ(x) - x ⊗ 1` lies in the part of `A ⊗ A` whose left tensor factor has degree
strictly less than `n`. -/
theorem comul_sub_tmul_one_mem_lower {n : ℕ} {x : A} (hx : x ∈ 𝒜 n) :
    comul x - x ⊗ₜ[R] (1 : A) ∈
      ⨆ p : ℕ, ⨆ q : ℕ, ⨆ (_ : p + q = n), ⨆ (_ : p < n),
        LinearMap.range (TensorProduct.map (𝒜 p).subtype (𝒜 q).subtype) := by
  classical
  rw [show comul x - x ⊗ₜ[R] (1 : A) =
    ((LinearMap.id - LinearMap.lTensor A (GradedAlgebra.proj 𝒜 0) :
        A ⊗[R] A →ₗ[R] A ⊗[R] A)) (comul x) from by simp]
  refine apply_mem_of_mem_bigradedPart 𝒜 _ _ (fun {p q} hpq a b => ?_)
    (GradedCoalgebra.comul_mem hx)
  simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.lTensor_tmul]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have hqb : GradedAlgebra.proj 𝒜 0 (b : A) = 0 :=
      DirectSum.decompose_of_mem_ne _ b.2 (Nat.pos_iff_ne_zero.mp hq)
    rw [hqb, TensorProduct.tmul_zero, sub_zero]
    exact Submodule.mem_iSup_of_mem p <| Submodule.mem_iSup_of_mem q <|
      Submodule.mem_iSup_of_mem hpq <| Submodule.mem_iSup_of_mem (by omega)
        ⟨a ⊗ₜ[R] b, by simp⟩

end Bialgebra
