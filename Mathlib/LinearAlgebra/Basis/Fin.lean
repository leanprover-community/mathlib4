/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Kevin H. Wilson
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Bases indexed by `Fin`
-/

@[expose] public section

assert_not_exists Ordinal

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

namespace Module

open LinearMap

variable {v : ι → M}
variable [Ring R] [CommRing R₂] [AddCommGroup M]
variable [Module R M] [Module R₂ M]
variable {x y : M}
variable (b : Basis ι R M)

namespace Basis

section Fin

/-- Let `b` be a basis for a submodule `N` of `M`. If `y : M` is linear independent of `N`
and `y` and `N` together span the whole of `M`, then there is a basis for `M`
whose basis vectors are given by `Fin.cons y b`. -/
noncomputable def mkFinCons {n : ℕ} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    Basis (Fin (n + 1)) R M :=
  have span_b : N = Submodule.span R (Set.range (N.subtype ∘ b)) := by
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  Basis.mk (v := Fin.cons y (N.subtype ∘ b))
    ((b.linearIndependent.map' N.subtype (Submodule.ker_subtype _)).finCons' _ _
      (by
        intro c x hx hc
        rw [← span_b] at hx
        exact hli c x hx hc))
    fun x _ => by simpa [Submodule.mem_span_insert', span_b] using hsp x

@[simp]
theorem coe_mkFinCons {n : ℕ} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    (mkFinCons y b hli hsp : Fin (n + 1) → M) = Fin.cons y ((↑) ∘ b) := by
  unfold mkFinCons
  exact coe_mk (v := Fin.cons y (N.subtype ∘ b)) _ _

section DivisionRing

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- Let `b` be a basis for a submodule `N` of `V`. If `K ∙ y` is complementary to `N`,
then `y` followed by `b` is a basis of `V`. -/
noncomputable def mkFinConsOfIsCompl {n : ℕ} {N : Submodule K V} (y : V)
    (b : Basis (Fin n) K N) (hy : y ≠ 0) (hN : IsCompl (K ∙ y) N) :
    Basis (Fin (n + 1)) K V :=
  mkFinCons y b
    (fun c x hx hcx => by
      have hcyN : c • y ∈ N := by
        rw [add_eq_zero_iff_eq_neg] at hcx
        rw [hcx]
        exact N.neg_mem hx
      have hcyL : c • y ∈ K ∙ y :=
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)
      have hcy0 : c • y = 0 := by
        simpa using hN.disjoint.le_bot ⟨hcyL, hcyN⟩
      by_contra hc
      exact hy <| by
        calc
          y = c⁻¹ • (c • y) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
          _ = 0 := by rw [hcy0, smul_zero])
    (fun z => by
      have hz : z ∈ K ∙ y ⊔ N := by
        rw [hN.sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨u, hu, w, hw, huz⟩ := Submodule.mem_sup.mp hz
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
      refine ⟨-a, ?_⟩
      rw [← huz]
      simpa [add_assoc, add_comm, add_left_comm] using hw)

@[simp]
theorem coe_mkFinConsOfIsCompl {n : ℕ} {N : Submodule K V} (y : V)
    (b : Basis (Fin n) K N) (hy : y ≠ 0) (hN : IsCompl (K ∙ y) N) :
    (mkFinConsOfIsCompl y b hy hN : Fin (n + 1) → V) = Fin.cons y ((↑) ∘ b) :=
  coe_mkFinCons _ _ _ _

end DivisionRing

/-- Let `b` be a basis for a submodule `N ≤ O`. If `y ∈ O` is linear independent of `N`
and `y` and `N` together span the whole of `O`, then there is a basis for `O`
whose basis vectors are given by `Fin.cons y b`. -/
noncomputable def mkFinConsOfLE {n : ℕ} {N O : Submodule R M} (y : M) (yO : y ∈ O)
    (b : Basis (Fin n) R N) (hNO : N ≤ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) : Basis (Fin (n + 1)) R O :=
  mkFinCons ⟨y, yO⟩ (b.map (Submodule.comapSubtypeEquivOfLe hNO).symm)
    (fun c x hc hx => hli c x (Submodule.mem_comap.mp hc) (congr_arg ((↑) : O → M) hx))
    fun z => hsp z z.2

@[simp]
theorem coe_mkFinConsOfLE {n : ℕ} {N O : Submodule R M} (y : M) (yO : y ∈ O) (b : Basis (Fin n) R N)
    (hNO : N ≤ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) :
    (mkFinConsOfLE y yO b hNO hli hsp : Fin (n + 1) → O) =
      Fin.cons ⟨y, yO⟩ (Submodule.inclusion hNO ∘ b) :=
  coe_mkFinCons _ _ _ _

/-- Let `b` be a basis for a submodule `N` of `M`. If `y : M` is linear independent of `N`
and `y` and `N` together span the whole of `M`, then there is a basis for `M`
whose basis vectors are given by `Fin.snoc b y`. -/
noncomputable def mkFinSnoc {n : ℕ} {N : Submodule R M} (b : Basis (Fin n) R N) (y : M)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    Basis (Fin (n + 1)) R M :=
  have span_b : N = Submodule.span R (Set.range (N.subtype ∘ b)) := by
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  Basis.mk (v := Fin.snoc (N.subtype ∘ b) y)
    ((b.linearIndependent.map' N.subtype (Submodule.ker_subtype _)).finSnoc' _ _
      (by
        intro c x hx hc
        rw [← span_b] at hx
        exact hli c x hx hc))
    fun x _ ↦ by simpa [Submodule.mem_span_insert', span_b] using hsp x

@[simp]
theorem coe_mkFinSnoc {n : ℕ} {N : Submodule R M} (b : Basis (Fin n) R N) (y : M)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    (mkFinSnoc b y hli hsp : Fin (n + 1) → M) = Fin.snoc ((↑) ∘ b) y := by
  unfold mkFinSnoc
  exact coe_mk (v := Fin.snoc (N.subtype ∘ b) y) _ _

/-- Let `b` be a basis for a submodule `N ≤ O`. If `y ∈ O` is linear independent of `N`
and `y` and `N` together span the whole of `O`, then there is a basis for `O`
whose basis vectors are given by `Fin.snoc b y`. -/
noncomputable def mkFinSnocOfLE {n : ℕ} {N O : Submodule R M} (b : Basis (Fin n) R N)
    (hNO : N ≤ O) (y : M) (yO : y ∈ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) : Basis (Fin (n + 1)) R O :=
  mkFinSnoc (b.map (Submodule.comapSubtypeEquivOfLe hNO).symm) ⟨y, yO⟩
    (fun c x hc hx => hli c x (Submodule.mem_comap.mp hc) (congr_arg ((↑) : O → M) hx))
    fun z => hsp z z.2

@[simp]
theorem coe_mkFinSnocOfLE {n : ℕ} {N O : Submodule R M} (b : Basis (Fin n) R N)
    (hNO : N ≤ O) (y : M) (yO : y ∈ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) :
    (mkFinSnocOfLE b hNO y yO hli hsp : Fin (n + 1) → O) =
      Fin.snoc (Submodule.inclusion hNO ∘ b) ⟨y, yO⟩ :=
  coe_mkFinSnoc _ _ _ _

/-- The basis of `R × R` given by the two vectors `(1, 0)` and `(0, 1)`. -/
protected def finTwoProd (R : Type*) [Semiring R] : Basis (Fin 2) R (R × R) :=
  Basis.ofEquivFun (LinearEquiv.finTwoArrow R R).symm

@[simp]
theorem finTwoProd_zero (R : Type*) [Semiring R] : Basis.finTwoProd R 0 = (1, 0) := by
  simp [Basis.finTwoProd, LinearEquiv.finTwoArrow]

@[simp]
theorem finTwoProd_one (R : Type*) [Semiring R] : Basis.finTwoProd R 1 = (0, 1) := by
  simp [Basis.finTwoProd, LinearEquiv.finTwoArrow]

@[simp]
theorem coe_finTwoProd_repr {R : Type*} [Semiring R] (x : R × R) :
    ⇑((Basis.finTwoProd R).repr x) = ![x.fst, x.snd] :=
  rfl

end Fin

end Basis

end Module
