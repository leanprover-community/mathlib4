/-
Copyright (c) 2025 Fabian Odermatt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Odermatt
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.SimplicialHomotopy
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Simplicial homotopies induce chain homotopies

Given a simplicial homotopy between morphisms of simplicial objects in a preadditive category,
we construct a chain homotopy between the induced morphisms on the alternating face map complexes.

Concretely, if `H : SimplicialHomotopy f g` gives maps
`H.h i : X _⦋n⦌ ⟶ Y _⦋n+1⦌` indexed by `i : Fin (n+1)`, we define the degree-`n` component
of the chain homotopy as the alternating sum `∑ i, (-1)^i • H.h i`.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.SimplicialObject
open SimplexCategory Simplicial Opposite AlgebraicTopology

namespace CategoryTheory.SimplicialObject.Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X Y : SimplicialObject C} {f g : X ⟶ Y}
variable (H : Homotopy f g)

namespace ToChainHomotopy

/-- The family of components of the induced chain homotopy -/
noncomputable def hom (p q : ℕ) : X _⦋p⦌ ⟶ Y _⦋q⦌ :=
  if h : p + 1 = q then
    -∑ k : Fin (p + 1), ((-1 : ℤ) ^ (k : ℕ)) • H.h k ≫ eqToHom (by simp [h])
  else 0

@[simp]
lemma hom_eq (p : ℕ) :
    hom H p (p + 1) = -∑ k : Fin (p + 1), ((-1 : ℤ) ^ (k : ℕ)) • H.h k := by
  simp [hom]

@[simp]
lemma hom_eq_zero (p q : ℕ) (hpq : p + 1 ≠ q) :
    hom H p q = 0 :=
  dif_neg hpq

private lemma comm_zero :
    letI d : Y _⦋1⦌ ⟶ Y _⦋0⦌ := ((alternatingFaceMapComplex C).obj Y).d 1 0
    f.app (op ⦋0⦌) = hom H 0 1 ≫ d + g.app (op ⦋0⦌) := by
  simp [← H.h_last_comp_δ_last 0]

lemma Finset.compl_eq_of_disjoint_of_card_add_eq
    {ι : Type*} [DecidableEq ι] [Fintype ι] {S₁ S₂ : Finset ι} (h : Disjoint S₁ S₂)
    (h' : S₁.card + S₂.card = Finset.card (.univ : Finset ι)) :
    S₁ᶜ = S₂ :=
  (Finset.eq_of_subset_of_card_le
    (by rwa [Finset.subset_compl_iff_disjoint_left])
    (by simp [← add_le_add_iff_left S₁.card, h'])).symm

private lemma comm_succ (n : ℕ) :
    letI α : X _⦋n + 1⦌ ⟶ Y _⦋n + 1⦌ :=
      ((alternatingFaceMapComplex C).obj X).d (n + 1) n ≫ ToChainHomotopy.hom H n (n + 1)
    letI β : X _⦋n + 1⦌ ⟶ Y _⦋n + 1⦌ := hom H (n + 1) (n + 1 + 1) ≫
      ((alternatingFaceMapComplex C).obj Y).d (n + 1 + 1) (n + 1)
    f.app (op ⦋n + 1⦌) = α + β + g.app (op ⦋n + 1⦌) := by
  rw [← H.h_zero_comp_δ_zero, ← H.h_last_comp_δ_last]
  dsimp
  simp only [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD, hom_eq,
    Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_sum,
    Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    smul_neg, Finset.sum_neg_distrib, ← Finset.sum_zsmul, smul_smul, ← pow_add]
  let α (x : Fin (n + 1) × Fin (n + 2)) := (-1) ^ ((x.1 + x.2 : ℕ)) • X.δ x.2 ≫ H.h x.1
  let β (x : Fin (n + 3) × Fin (n + 2)) := (-1) ^ ((x.1 + x.2 : ℕ)) • H.h x.2 ≫ Y.δ x.1
  have h₂ (x : Fin (n + 1) × Fin (n + 2)) (hx : x.1.castSucc < x.2) :
      α x = -β ⟨x.2.succ, x.1.castSucc⟩ := by
    dsimp [α, β]
    simp only [← H.h_castSucc_comp_δ_succ_of_lt x.2 x.1 hx,
      pow_add, pow_one, mul_neg, mul_one, neg_mul, neg_smul, neg_neg]
    rw [mul_comm]
  rw [← Finset.sum_product .univ .univ α, ← Finset.sum_product .univ .univ β,
    Finset.univ_product_univ, Finset.univ_product_univ]
  let S : Finset (Fin (n + 1) × Fin (n + 2)) := { x | x.1.castSucc < x.2 }
  let γ₁ (x : Fin (n + 1) × Fin (n + 2)) := (x.2.castSucc, x.1.succ)
  let γ₂ (x : Fin (n + 1) × Fin (n + 2)) := (x.2.succ, x.1.castSucc)
  let γ₃ (i : Fin (n + 1)) := (i.castSucc.succ, i.succ)
  let γ₄ (i : Fin (n + 1)) := (i.castSucc.succ, i.castSucc)
  have hγ₁ : Function.Injective γ₁ := fun _ _ ↦ by aesop
  have hγ₂ : Function.Injective γ₂ := fun _ _ ↦ by aesop
  have hγ₃ : Function.Injective γ₃ := fun _ _ ↦ by aesop
  have hγ₄ : Function.Injective γ₄ := fun _ _ ↦ by aesop
  have eq₁ : H.h 0 ≫ Y.δ 0 = β ⟨0, 0⟩ := by simp [β]
  have eq₂ : H.h (Fin.last _) ≫ Y.δ (Fin.last _) = - β ⟨Fin.last _, Fin.last _⟩ := by
    dsimp [β]
    simp only [pow_add, even_two, Even.neg_pow, one_pow, mul_one,
      pow_one, mul_neg, neg_smul, neg_neg]
    rw [← pow_add, (Even.add_self n).neg_one_pow, one_smul]
  have eq₃ : ∑ x ∈ Sᶜ, α x = - ∑ y ∈ Finset.image γ₁ Sᶜ, β y := by
    rw [← Finset.sum_neg_distrib, Finset.sum_image hγ₁.injOn]
    refine Finset.sum_congr rfl (fun x hx ↦ ?_)
    dsimp [α, β, γ₁]
    simp only [← H.h_succ_comp_δ_castSucc_of_lt x.2 x.1 (by simpa [S] using hx),
      pow_add, pow_one, mul_neg, mul_one, neg_smul, neg_neg]
    rw [mul_comm]
  have eq₄ : ∑ x ∈ S, α x = - ∑ y ∈ Finset.image γ₂ S, β y := by
    rw [← Finset.sum_neg_distrib, Finset.sum_image hγ₂.injOn]
    refine Finset.sum_congr rfl (fun x hx ↦ ?_)
    dsimp [α, β, γ₂]
    simp only [← H.h_castSucc_comp_δ_succ_of_lt x.2 x.1 (by simpa [S] using hx),
      pow_add, pow_one, mul_neg, mul_one, neg_mul, neg_smul, neg_neg]
    rw [mul_comm]
  have eq₅ : ∑ x, β (γ₄ x) = - ∑ x, β (γ₃ x) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x hx ↦ by simp [β, γ₃, γ₄])
  have h₁ : Disjoint (Finset.image γ₁ Sᶜ) (Finset.image γ₂ S) := by
    rw [Finset.disjoint_iff_ne]
    simp only [Finset.compl_filter, not_lt, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Prod.exists, ne_eq, forall_exists_index, and_imp, Prod.forall, Prod.mk.injEq,
      not_and, γ₁, S, γ₂]
    rintro _ _ ⟨a, _⟩ ⟨b, _⟩ h₁ rfl rfl _ _ ⟨a', _⟩ ⟨b', _⟩ h₂ rfl rfl h₃ h₄
    simp only [Fin.castSucc_mk, Fin.mk_le_mk, Fin.mk_lt_mk,
      Fin.succ_mk, Fin.mk.injEq] at h₁ h₂ h₃ h₄
    grind
  have h₂ : Disjoint (Finset.image γ₃ .univ) (Finset.image γ₄ .univ) := by
    rw [Finset.disjoint_iff_ne]
    grind
  have h₃ : Disjoint (Finset.disjUnion _ _ h₂) {(0, 0), (Fin.last _, Fin.last _)} := by
    rw [Finset.disjoint_iff_ne]
    grind
  have h₄ : Disjoint (Finset.disjUnion _ _ h₁) (Finset.disjUnion _ _ h₃) := by
    rw [Finset.disjoint_iff_ne]
    simp only [Finset.compl_filter, not_lt, Finset.disjUnion_eq_union, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists, ne_eq,
      Finset.mem_insert, Finset.mem_singleton, Prod.forall, Prod.mk.injEq, not_and,
      S, γ₁, γ₂, γ₃, γ₄]
    rintro _ _ (⟨⟨j, _⟩, ⟨k, _⟩, h₁, h₂, h₃⟩ | ⟨⟨j, _⟩, ⟨k, _⟩, h₁, h₂, h₃⟩) _ _
      ((⟨⟨i, _⟩, h₄, h₅⟩ | ⟨⟨i, _⟩, h₄, h₅⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)) <;>
      simp at h₁ h₂ h₃ <;> grind
  have H : (Finset.disjUnion _ _ h₁)ᶜ = Finset.disjUnion _ _ h₃ :=
    Finset.compl_eq_of_disjoint_of_card_add_eq h₄ (by
      rw [Finset.card_disjUnion, Finset.card_disjUnion, Finset.card_disjUnion,
        Finset.card_image_of_injective _ hγ₁, Finset.card_image_of_injective _ hγ₂,
        Finset.card_image_of_injective _ hγ₃, Finset.card_image_of_injective _ hγ₄]
      simp only [Finset.card_compl_add_card, Fintype.card_prod, Fintype.card_fin,
        Finset.card_univ]
      grind)
  rw [eq₁, eq₂, ← S.sum_add_sum_compl, eq₃, eq₄,
    neg_add_rev, neg_neg, neg_neg, ← Finset.sum_disjUnion h₁,
    ← (Finset.disjUnion _ _ h₁).sum_add_sum_compl, neg_add,
    ← add_assoc, add_neg_cancel, zero_add, H,
    Finset.sum_disjUnion, Finset.sum_disjUnion,
    Finset.sum_image hγ₃.injOn, Finset.sum_image hγ₄.injOn,
    Finset.sum_insert (by simp), Finset.sum_singleton,
    neg_add_rev, neg_add_rev, neg_add_rev, eq₅]
  simp

end ToChainHomotopy

/-- A simplicial homotopy between `f` and `g` induces a chain homotopy
between the induced morphisms on the alternating face map complexes. -/
noncomputable def toChainHomotopy (H : Homotopy f g) :
    _root_.Homotopy
      ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g) where
  hom := ToChainHomotopy.hom H
  zero i j hij := ToChainHomotopy.hom_eq_zero _ _ _ hij
  comm n := by
    cases n with
    | zero =>
      rw [prevD_eq (j' := 1) (w := by simp), dNext_eq_zero _ _ (by simp), zero_add]
      simp [ToChainHomotopy.comm_zero H]
    | succ n =>
      rw [dNext_eq (i' := n) (w := by simp), prevD_eq (j' := n + 1 + 1) (w := by simp)]
      simp [ToChainHomotopy.comm_succ H]

theorem map_homology_eq [CategoryWithHomology C] (H : Homotopy f g) (n : ℕ) :
    (HomologicalComplex.homologyFunctor C _ n).map ((alternatingFaceMapComplex C).map f) =
    (HomologicalComplex.homologyFunctor C _ n).map ((alternatingFaceMapComplex C).map g) := by
  simpa using (H.toChainHomotopy).homologyMap_eq n

end CategoryTheory.SimplicialObject.Homotopy
