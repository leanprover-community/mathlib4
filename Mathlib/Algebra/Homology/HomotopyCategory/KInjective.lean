/-
<<<<<<< HEAD
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
=======
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexInduction
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
>>>>>>> origin/master

/-!
# K-injective cochain complexes

<<<<<<< HEAD
-/

open CategoryTheory Category Preadditive Limits

namespace CochainComplex

variable {C : Type*} [Category C] [Abelian C]
  (K L : CochainComplex C ℤ)

class IsKInjective : Prop where
  nonempty_homotopy_zero (K : CochainComplex C ℤ) (hK : ∀ (n : ℤ), K.ExactAt n) (f : K ⟶ L) :
    Nonempty (Homotopy f 0)

variable {K L}

noncomputable irreducible_def homotopyZero (f : K ⟶ L)
    (hK : ∀ (n : ℤ), K.ExactAt n) [L.IsKInjective] :
    Homotopy f 0 :=
  (IsKInjective.nonempty_homotopy_zero K hK f).some

variable (L)

lemma isKInjective_iff_mem_rightOrthogonal :
    L.IsKInjective ↔
      (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
        ((HomotopyCategory.quotient _ _).obj L) := by
  constructor
  · intro _ ⟨(K : CochainComplex C ℤ)⟩ f hK
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    erw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_exactAt] at hK
    rw [HomotopyCategory.eq_of_homotopy f 0 (homotopyZero f hK), Functor.map_zero]
  · intro hL
    refine ⟨fun K hK f => ?_⟩
    erw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_exactAt] at hK
    refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
    rw [hL ((HomotopyCategory.quotient _ _).map f) hK, Functor.map_zero]

variable {L}

lemma isKInjective_iff_of_iso (e : K ≅ L) :
    K.IsKInjective ↔ L.IsKInjective := by
  simp only [isKInjective_iff_mem_rightOrthogonal]
  exact ObjectProperty.prop_iff_of_iso _ ((HomotopyCategory.quotient _ _).mapIso e)

lemma isKInjective_of_iso (e : K ≅ L) [K.IsKInjective] : L.IsKInjective := by
  rw [← isKInjective_iff_of_iso e]
  infer_instance

variable (K)

instance isKInjective_shift [hK : K.IsKInjective] (n : ℤ) : K⟦n⟧.IsKInjective := by
  simp only [isKInjective_iff_mem_rightOrthogonal] at hK ⊢
  erw [((HomotopyCategory.subcategoryAcyclic C)).rightOrthogonal.prop_iff_of_iso
    ((((HomotopyCategory.quotient C (ComplexShape.up ℤ))).commShiftIso n).app K)]
  exact ObjectProperty.le_shift _ n _ hK

lemma isKInjective_shift_iff (n : ℤ) :
    K⟦n⟧.IsKInjective ↔ K.IsKInjective := by
  constructor
  · intro
    exact isKInjective_of_iso (show K⟦n⟧⟦-n⟧ ≅ K from (shiftEquiv _ n).unitIso.symm.app K)
  · intro
    infer_instance

lemma Qh_map_bijective_of_isKInjective [HasDerivedCategory C]
    (K : HomotopyCategory C (ComplexShape.up ℤ)) (L : CochainComplex C ℤ) [L.IsKInjective] :
    Function.Bijective (DerivedCategory.Qh.map :
      (K ⟶ (HomotopyCategory.quotient _ _).obj L) → _ ) := by
  apply (HomotopyCategory.subcategoryAcyclic C).map_bijective_of_rightOrthogonal
  rw [← isKInjective_iff_mem_rightOrthogonal]
  infer_instance

variable (L)

open HomComplex

lemma homComplex_exactAt_of_KInjective [L.IsKInjective] (hK : ∀ (n : ℤ), K.ExactAt n) (n : ℤ) :
    (HomComplex K L).ExactAt n := by
  rw [(HomComplex K L).exactAt_iff' (n-1) n (n+1) (by simp) (by simp), ShortComplex.ab_exact_iff]
  intro (x₂ : Cochain K L n) hx₂
  obtain ⟨α, hα⟩ := (Cochain.equivHomotopy _ _) (homotopyZero ((Cocycle.equivHom _ _).symm
    ((Cocycle.mk x₂ (n+1) (by simp) hx₂).rightShift n 0 (zero_add n))) hK)
  simp only [Cocycle.equivHom_symm_apply, Cocycle.cochain_ofHom_homOf_eq_coe,
    Cocycle.rightShift_coe, Cocycle.mk_coe, Cochain.ofHom_zero, add_zero] at hα
  refine ⟨n.negOnePow • α.rightUnshift (n-1) (by linarith), ?_⟩
  apply (Cochain.rightShiftAddEquiv K L n n 0 (zero_add n)).injective
  dsimp [HomComplex]
  simp only [hα, δ_smul, Cochain.rightShift_smul,
    α.δ_rightUnshift (n-1) (by linarith) n 0 (by linarith),
    Cochain.rightShift_rightUnshift, smul_smul, δ_units_smul,
    Int.units_mul_self, one_smul]

namespace HomComplex

namespace Cochain

variable {K L}

def EqUpTo {n : ℤ} (α β : Cochain K L n) (p₀ : ℤ) : Prop :=
  ∀ (p q : ℤ) (hpq : p + n = q), p ≤ p₀ → α.v p q hpq = β.v p q hpq

namespace Induction

variable {d : ℤ} {X : ℕ → Set (Cochain K L d)} (φ : ∀ (n : ℕ), X n → X (n + 1))
   {p₀ : ℤ} (hφ : ∀ (n : ℕ) (x : X n), (φ n x).1.EqUpTo x.1 (p₀ + n)) (x₀ : X 0)

def sequence : ∀ n, X n
  | 0 => x₀
  | n+1 => φ n (sequence n)

include hφ in
lemma sequence_eqUpTo (n₁ n₂ : ℕ) (h : n₁ ≤ n₂) :
    (sequence φ x₀ n₁).1.EqUpTo (sequence φ x₀ n₂).1 (p₀ + n₁) := by
  obtain ⟨k, rfl⟩ : ∃ (k : ℕ), n₂ = n₁ + k := Nat.exists_eq_add_of_le h
  clear h
  revert n₁
  induction' k with k hk
  · intro n₁ p q hpq _
    simp only [Nat.zero_eq, Nat.add_zero]
  · intro n₁ p q hpq hp
    rw [hk n₁ p q hpq hp, ← hφ (n₁ + k) (sequence φ x₀ (n₁ + k)) p q hpq
      (by rw [Nat.cast_add, ← add_assoc]; linarith)]
    rfl

def limitSequence (_ : ∀ (n : ℕ) (x : X n), (φ n x).1.EqUpTo x.1 (p₀ + n)) (x₀ : X 0) :
    Cochain K L d :=
  Cochain.mk (fun p q hpq => (sequence φ x₀ (p-p₀).toNat).1.v p q hpq)

lemma limitSequence_eqUpTo (n : ℕ) :
    (limitSequence φ hφ x₀).EqUpTo (sequence φ x₀ n).1 (p₀ + n) := by
  intro p q hpq hp
  dsimp [limitSequence]
  refine sequence_eqUpTo φ hφ _ _ _ ?_ _ _ _ ?_
  · rw [Int.toNat_le]
    linarith
  · linarith [Int.self_le_toNat (p - p₀)]

end Induction

end Cochain

end HomComplex

variable {K L}

lemma isKInjective_of_injective_aux
    (f : K ⟶ L) (α : Cochain K L (-1)) (n m : ℤ) (hnm : n + 1 = m)
    (hK : K.ExactAt m) [Injective (L.X m)]
    (hα : (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) n) :
    ∃ (h : K.X (n + 2) ⟶ L.X (n+1)),
    (δ (-1) 0 (α + Cochain.single h (-1))).EqUpTo (Cochain.ofHom f) m := by
  subst hnm
  let u := f.f (n + 1) - α.v (n+1) n (by linarith) ≫ L.d n (n+1) -
    K.d (n+1) (n+2) ≫ α.v (n+2) (n+1) (by linarith)
  have hu : K.d n (n+1) ≫ u = 0 := by
    dsimp [u]
    have eq := hα n n (add_zero n) (by rfl)
    simp only [δ_v (-1) 0 (neg_add_cancel 1) α n n (add_zero _) (n-1) (n+1)
      (by linarith) (by linarith),
      neg_add_cancel, Int.negOnePow_zero, one_smul, Cochain.ofHom_v] at eq
    simp only [comp_sub, HomologicalComplex.d_comp_d_assoc, zero_comp, sub_zero,
      ← f.comm, ← eq, add_comp, assoc, L.d_comp_d, comp_zero, zero_add, sub_self]
  rw [K.exactAt_iff' n (n+1) (n+2) (by simp) (by simp; linarith)] at hK
  obtain ⟨h, hh⟩ : ∃ (h : K.X (n+2) ⟶ L.X (n+1)), K.d (n+1) (n+2) ≫ h = u :=
    ⟨hK.descToInjective _ hu, hK.comp_descToInjective _ _⟩
  refine ⟨h, ?_⟩
  intro p q hpq hp
  obtain rfl : p = q := by linarith
  obtain hp | rfl := hp.lt_or_eq
  · rw [Int.lt_add_one_iff] at hp
    rw [δ_add, Cochain.add_v, hα p p (by linarith) (by linarith), add_eq_left,
      δ_v (-1) 0 (neg_add_cancel 1) _ p p hpq (p-1) (p+1) rfl rfl]
    simp only [neg_add_cancel, Int.negOnePow_zero, one_smul]
    rw [Cochain.single_v_eq_zero _ _ _ _ _ (by linarith),
      Cochain.single_v_eq_zero _ _ _ _ _ (by linarith), zero_comp, comp_zero,
      add_zero]
  · rw [δ_v (-1) 0 (neg_add_cancel 1) _ (n+1) (n+1) (by linarith) n (n+2)
      (by linarith) (by linarith)]
    simp only [neg_add_cancel, Int.negOnePow_zero, one_smul, Cochain.add_v, add_comp,
      comp_add, Cochain.ofHom_v, Cochain.single_v]
    rw [Cochain.single_v_eq_zero _ _ _ _ _ (by linarith)]
    simp only [ComplexShape.up_Rel, not_true, zero_comp, add_zero, Cochain.single_v,
      Cochain.ofHom_v, hh, u]
    abel

variable (L)

lemma isKInjective_of_injective (d : ℤ) [L.IsStrictlyGE d] [∀ (n : ℤ), Injective (L.X n)] :
    L.IsKInjective := ⟨fun K hK f => by
  let X : ℕ → Set (Cochain K L (-1)) := fun n α => (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) (n + d - 1)
  let x₀ : X 0 := ⟨0, fun p q hpq hp => by
    apply IsZero.eq_of_tgt
    apply L.isZero_of_isStrictlyGE d
    simp only [Nat.cast_zero, zero_add] at hp
    linarith⟩
  let φ : ∀ n, X n → X (n+1) := fun n α =>
    ⟨_, (isKInjective_of_injective_aux f α.1 (n + d - 1) ((n + 1 : ℕ) + d - 1)
      (by simp; linarith) (hK _) α.2).choose_spec⟩
  have hφ : ∀ (k : ℕ) (x : X k), (φ k x).1.EqUpTo x.1 (d + k) := fun k x p q hpq hp => by
    dsimp [φ]
    rw [add_eq_left]
    apply Cochain.single_v_eq_zero
    omega
  refine ⟨(Cochain.equivHomotopy f 0).symm ⟨Cochain.Induction.limitSequence φ hφ x₀, ?_⟩⟩
  rw [Cochain.ofHom_zero, add_zero]
  ext n
  let k₀ : ℕ := (n - d + 1).toNat
  have := Int.self_le_toNat (n - d + 1)
  rw [← (Cochain.Induction.sequence φ x₀ k₀).2 n n (add_zero n) (by linarith),
    δ_v (-1) 0 (neg_add_cancel 1) _ n n (by linarith) (n-1) (n+1) rfl (by linarith),
    δ_v (-1) 0 (neg_add_cancel 1) _ n n (by linarith) (n-1) (n+1) rfl (by linarith),
    Cochain.Induction.limitSequence_eqUpTo φ hφ x₀ k₀ n (n-1) (by linarith) (by linarith),
    Cochain.Induction.limitSequence_eqUpTo φ hφ x₀ k₀ (n+1) n (by linarith) (by linarith)]⟩
=======
We define the notion of K-injective cochain complex in an abelian category,
and show that bounded below complexes of injective objects are K-injective.

## TODO (@joelriou)
* Provide an API for computing `Ext`-groups using an injective resolution

## References
* [N. Spaltenstein, *Resolutions of unbounded complexes*][spaltenstein1998]

-/

@[expose] public section

namespace CochainComplex

open CategoryTheory Limits HomComplex Preadditive

variable {C : Type*} [Category* C] [Abelian C]

-- TODO (@joelriou): show that this definition is equivalent to the
-- original definition by Spaltenstein saying that whenever `K`
-- is acyclic, then `HomComplex K L` is acyclic. (The condition below
-- is equivalent to the acyclicity of `HomComplex K L` in degree
-- `0`, and the general case follows by shifting `K`.)
/-- A cochain complex `L` is K-injective if any morphism `K ⟶ L`
with `K` acyclic is homotopic to zero. -/
class IsKInjective (L : CochainComplex C ℤ) : Prop where
  nonempty_homotopy_zero {K : CochainComplex C ℤ} (f : K ⟶ L) :
    K.Acyclic → Nonempty (Homotopy f 0)

/-- A choice of homotopy to zero for a morphism from an acyclic
cochain complex to a K-injective cochain complex. -/
noncomputable irreducible_def IsKInjective.homotopyZero {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : K.Acyclic) [L.IsKInjective] :
    Homotopy f 0 :=
  (IsKInjective.nonempty_homotopy_zero f hK).some

lemma _root_.HomotopyEquiv.isKInjective {L₁ L₂ : CochainComplex C ℤ}
    (e : HomotopyEquiv L₁ L₂)
    [L₁.IsKInjective] : L₂.IsKInjective where
  nonempty_homotopy_zero {K} f hK :=
    ⟨Homotopy.trans (Homotopy.trans (.ofEq (by simp))
      ((e.homotopyInvHomId.symm.compLeft f).trans (.ofEq (by simp))))
        (((IsKInjective.homotopyZero (f ≫ e.inv) hK).compRight e.hom).trans (.ofEq (by simp)))⟩

lemma isKInjective_of_iso {L₁ L₂ : CochainComplex C ℤ} (e : L₁ ≅ L₂)
    [L₁.IsKInjective] :
    L₂.IsKInjective :=
  (HomotopyEquiv.ofIso e).isKInjective

lemma isKInjective_iff_of_iso {L₁ L₂ : CochainComplex C ℤ} (e : L₁ ≅ L₂) :
    L₁.IsKInjective ↔ L₂.IsKInjective :=
  ⟨fun _ ↦ isKInjective_of_iso e, fun _ ↦ isKInjective_of_iso e.symm⟩

lemma isKInjective_iff_rightOrthogonal (L : CochainComplex C ℤ) :
    L.IsKInjective ↔
      (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
        ((HomotopyCategory.quotient _ _).obj L) := by
  refine ⟨fun _ K f hK ↦ ?_,
      fun hL ↦ ⟨fun {K} f hK ↦ ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩⟩
  · obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    rw [HomotopyCategory.eq_of_homotopy f 0 (IsKInjective.homotopyZero f hK), Functor.map_zero]
  · rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    rw [hL ((HomotopyCategory.quotient _ _).map f) hK, Functor.map_zero]

lemma IsKInjective.rightOrthogonal (L : CochainComplex C ℤ) [L.IsKInjective] :
    (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
        ((HomotopyCategory.quotient _ _).obj L) := by
  rwa [← isKInjective_iff_rightOrthogonal]

instance (L : CochainComplex C ℤ) [hL : L.IsKInjective] (n : ℤ) :
    (L⟦n⟧).IsKInjective := by
  rw [isKInjective_iff_rightOrthogonal] at hL ⊢
  exact ObjectProperty.prop_of_iso _
    (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).symm.app L)
    ((HomotopyCategory.subcategoryAcyclic C).rightOrthogonal.le_shift n _ hL)

lemma isKInjective_shift_iff (L : CochainComplex C ℤ) (n : ℤ) :
    (L⟦n⟧).IsKInjective ↔ L.IsKInjective :=
  ⟨fun _ ↦ isKInjective_of_iso (show L⟦n⟧⟦-n⟧ ≅ L from (shiftEquiv _ n).unitIso.symm.app L),
    fun _ ↦ inferInstance⟩

lemma isKInjective_of_injective_aux {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (α : Cochain K L (-1)) (n m : ℤ) (hnm : n + 1 = m)
    (hK : K.ExactAt m) [Injective (L.X m)]
    (hα : (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) n) :
    ∃ (h : K.X (n + 2) ⟶ L.X (n + 1)),
      (δ (-1) 0 (α + Cochain.single h (-1))).EqUpTo (Cochain.ofHom f) m := by
  subst hnm
  let u := f.f (n + 1) - α.v (n + 1) n (by lia) ≫ L.d n (n + 1) -
    K.d (n + 1) (n + 2) ≫ α.v (n + 2) (n + 1) (by lia)
  have hu : K.d n (n + 1) ≫ u = 0 := by
    have eq := hα n n (add_zero n) (by rfl)
    simp only [δ_v (-1) 0 (neg_add_cancel 1) α n n (add_zero _) (n - 1) (n + 1)
      (by lia) (by lia), Int.negOnePow_zero, one_smul, Cochain.ofHom_v] at eq
    simp only [u, comp_sub, HomologicalComplex.d_comp_d_assoc, zero_comp,
      ← f.comm, ← eq, add_comp, Category.assoc, L.d_comp_d, comp_zero, zero_add, sub_self]
  rw [K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp; lia)] at hK
  obtain ⟨β, hβ⟩ : ∃ (β : K.X (n + 2) ⟶ L.X (n + 1)), K.d (n + 1) (n + 2) ≫ β = u :=
    ⟨hK.descToInjective _ hu, hK.comp_descToInjective _ _⟩
  refine ⟨β, ?_⟩
  intro p q hpq hp
  obtain rfl : p = q := by lia
  obtain hp | rfl := hp.lt_or_eq
  · rw [δ_add, Cochain.add_v, hα p p (by lia) (by lia), add_eq_left,
      δ_v (-1) 0 (neg_add_cancel 1) _ p p hpq (p - 1) (p + 1) rfl rfl,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia),
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp
  · rw [δ_v (-1) 0 (neg_add_cancel 1) _ (n + 1) (n + 1) (by lia) n (n + 2)
      (by lia) (by lia), Cochain.add_v,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp [hβ, u]

open Cochain.InductionUp in
lemma isKInjective_of_injective (L : CochainComplex C ℤ) (d : ℤ)
    [L.IsStrictlyGE d] [∀ (n : ℤ), Injective (L.X n)] :
    L.IsKInjective where
  nonempty_homotopy_zero {K} f hK := by
    /- The strategy of the proof is express the `0`-cocycle in `Cochain K L 0`
    corresponding to `f` as the coboundary of a `-1`-cochain. An approximate
    solution for some `n : ℕ` is an element in the subset `X n` consisting
    of the `-1`-cochains such that `δ (-1) 0 α` coincide with `Cochain.ofHom f`
    up to the degree `n + d - 1`. The assumption on `L` implies that
    the zero `-1`-cochain belongs to `X 0`, and we use the lemma
    `isKInjective_of_injective_aux` in order to get better approximations,
    and we pass to the limit. -/
    let X (n : ℕ) : Set (Cochain K L (-1)) :=
      setOf (fun α => (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) (n + d - 1))
    let x₀ : X 0 := ⟨0, fun p q hpq hp ↦
      IsZero.eq_of_tgt (L.isZero_of_isStrictlyGE d _ (by lia)) _ _⟩
    let φ (n : ℕ) (α : X n) : X (n + 1) :=
      ⟨_, (isKInjective_of_injective_aux f α.1 (n + d - 1) ((n + 1 : ℕ) + d - 1)
        (by lia) (hK _) α.2).choose_spec⟩
    have hφ (k : ℕ) (x : X k) : (φ k x).1.EqUpTo x.1 (d + k) := fun p q hpq hp => by
      dsimp [φ]
      rw [add_eq_left, Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    refine ⟨(Cochain.equivHomotopy f 0).symm ⟨limitSequence φ hφ x₀, ?_⟩⟩
    rw [Cochain.ofHom_zero, add_zero]
    ext n
    let k₀ := (n - d + 1).toNat
    rw [← (sequence φ x₀ k₀).2 n n (add_zero n) (by lia),
      δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n - 1) (n + 1) rfl (by lia),
      δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n - 1) (n + 1) rfl (by lia),
      limitSequence_eqUpTo φ hφ x₀ k₀ n (n - 1) (by lia) (by lia),
      limitSequence_eqUpTo φ hφ x₀ k₀ (n + 1) n (by lia) (by lia)]
>>>>>>> origin/master

end CochainComplex
