/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.QuotientGroup

variable {ι : Type*} (G : ι → Type*) [∀ i, Group (G i)] (H : Type*) [Group H]
  (φ : ∀ i, H →* G i) {K : Type*} [Group K]

open Monoid CoprodI Subgroup

def AmalgamatedProduct : Type _ :=
  CoprodI G ⧸ normalClosure
    (⋃ (i : ι) (j : ι), Set.range (fun g => of (φ i g) * (of (φ j g))⁻¹))

namespace AmalgamatedProduct

variable {G H φ}

instance : Group (AmalgamatedProduct G H φ) :=
  QuotientGroup.Quotient.group _

def of {i : ι} : G i →* AmalgamatedProduct G H φ :=
  (QuotientGroup.mk' _).comp CoprodI.of

def lift (f : ∀ i, G i →* K) (hf : ∀ i, (f i).comp (φ i) = 1) :
    AmalgamatedProduct G H φ →* K :=
  QuotientGroup.lift _ (CoprodI.lift f)
    (show normalClosure _ ≤ (CoprodI.lift f).ker
      from normalClosure_le_normal <| by
        simp only [FunLike.ext_iff, MonoidHom.coe_comp, Function.comp_apply,
          MonoidHom.one_apply] at hf
        simp [Set.iUnion_subset_iff, Set.range_subset_iff, SetLike.mem_coe, MonoidHom.mem_ker, hf])

@[simp]
theorem lift_of (f : ∀ i, G i →* K) (hf : ∀ i, (f i).comp (φ i) = 1) {i : ι} (g : G i) :
    (lift f hf) (of g : AmalgamatedProduct G H φ) = f i g := by
  delta AmalgamatedProduct
  simp [lift, of]

@[ext high]
theorem hom_ext {f g : AmalgamatedProduct G H φ →* K}
    (h : ∀ i, f.comp (of : G i →* _) = g.comp of) : f = g := by
  delta AmalgamatedProduct
  ext i x
  simp only [FunLike.ext_iff] at h
  exact h _ _

section Word

noncomputable def rangeEquiv (h : ∀ i, Function.Injective (φ i)) (i j) :
    (φ i).range ≃* (φ j).range :=
  MulEquiv.trans
    (MulEquiv.subgroupCongr (MonoidHom.range_eq_map _)) <|
  MulEquiv.trans
    (equivMapOfInjective _ _ (h _)).symm <|
  MulEquiv.trans
    (equivMapOfInjective _ _ (h j))
    (MulEquiv.subgroupCongr (MonoidHom.range_eq_map _)).symm

open Coset

variable [Inhabited ι] (φ) (hφ : ∀ i, Function.Injective (φ i))


noncomputable def normalizeSingle {i : ι} (g : G i) : H × G i :=
  letI := Classical.propDecidable (g ∈ (φ i).range )
  if hg : g ∈ (φ i).range
  then ⟨Classical.choose hg, 1⟩
  else
    let s : Set (G i) := rightCoset (φ i).range g
    have hs : s.Nonempty := ⟨g, mem_own_rightCoset _ _⟩
    let g' := Classical.choose hs
    let h' := Classical.choose (Classical.choose_spec (Classical.choose_spec hs)).1
    ⟨h'⁻¹, g'⟩

theorem normalizeSingle_fst_mul_normalizeSingle_snd {i : ι} (g : G i) :
    φ i (normalizeSingle φ g).1 * (normalizeSingle φ g).2 = g := by
  let s : Set (G i) := rightCoset (φ i).range g
  have hs : s.Nonempty := ⟨g, mem_own_rightCoset _ _⟩
  dsimp [normalizeSingle]
  split_ifs with hg
  · simp [Classical.choose_spec hg]
  · simp only [normalizeSingle, MonoidHom.coe_range, Set.mem_range, map_inv,
      Eq.ndrec, id_eq]
    rw [Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hs)).1,
      inv_mul_eq_iff_eq_mul]
    have := Classical.choose_spec (Classical.choose_spec hs)
    dsimp at this
    rw [this.2]

theorem normalizeSingle_snd_eq_of_rightCosetEquivalence {i : ι} {g₁ g₂ : G i}
    (h : RightCosetEquivalence (φ i).range g₁ g₂) :
    (normalizeSingle φ g₁).2 = (normalizeSingle φ g₂).2 := by
  simp [normalizeSingle]
  by_cases hg₁ : g₁ ∈ (φ i).range
  · have hg₂ : g₂ ∈ (φ i).range := by
      rwa [RightCosetEquivalence, rightCoset_eq_iff, mul_mem_cancel_right
        (inv_mem hg₁)] at h
    rw [dif_pos hg₁, dif_pos hg₂]
  · have hg₂ : g₂ ∉ (φ i).range := by
      intro hg₂
      rw [RightCosetEquivalence, rightCoset_eq_iff, mul_mem_cancel_left hg₂,
        inv_mem_iff (x := g₁)] at h
      exact hg₁ h
    rw [dif_neg hg₁, dif_neg hg₂]
    dsimp
    congr

theorem rightCosetEquivalence_normalizeSingle_snd {i : ι} (g : G i) :
    RightCosetEquivalence (φ i).range g (normalizeSingle φ g).2 := by
  dsimp only [normalizeSingle]
  split_ifs with hg
  · rwa [RightCosetEquivalence, rightCoset_eq_iff, _root_.one_mul,
      inv_mem_iff (x := g)]
  · let s : Set (G i) := rightCoset (φ i).range g
    have hs : s.Nonempty := ⟨g, mem_own_rightCoset _ _⟩
    erw [RightCosetEquivalence, rightCoset_eq_iff,
      ← mem_rightCoset_iff (s := (φ i).range) g]
    exact Classical.choose_spec hs

@[simp]
theorem normalizeSingle_snd_normalize_single_snd {i : ι} {g : G i} :
    (normalizeSingle φ (normalizeSingle φ g).2).2 = (normalizeSingle φ g).2 :=
  normalizeSingle_snd_eq_of_rightCosetEquivalence _
    (rightCosetEquivalence_normalizeSingle_snd _ _).symm

theorem normalizeSingle_mul (hφ : ∀ i, Function.Injective (φ i))
    {i : ι} (h : H) (g : G i) :
    normalizeSingle φ (φ i h * g) = ⟨h * (normalizeSingle φ g).1,
      (normalizeSingle φ g).2⟩ := by
  have : (normalizeSingle φ (φ i h * g)).2 = (normalizeSingle φ g).2 :=
    normalizeSingle_snd_eq_of_rightCosetEquivalence _
      ((rightCoset_eq_iff _).2 (by simp))
  ext
  · apply hφ _
    erw [← mul_left_inj ((normalizeSingle φ (φ i h * g)).2),
      normalizeSingle_fst_mul_normalizeSingle_snd, this,
      map_mul, mul_assoc, normalizeSingle_fst_mul_normalizeSingle_snd]
  · exact this

theorem normalize_single_mem_range {i : ι} (hφ : ∀ i, Function.Injective (φ i)) (h : H) :
    (normalizeSingle φ (φ i h)) = (h, 1)  := by
  rw [normalizeSingle, dif_pos (MonoidHom.mem_range.2 ⟨_, rfl⟩)]
  simp only [Prod.mk.injEq, and_true]
  apply hφ i
  rw [Classical.choose_spec (MonoidHom.mem_range.2 ⟨_, rfl⟩)]

theorem normalizeSingle_one {i : ι} (hφ : ∀ i, Function.Injective (φ i)) :
    (normalizeSingle (i := i) φ 1) = (1, 1)  := by
  have h1 : 1 ∈ (φ i).range := one_mem  _
  rw [normalizeSingle, dif_pos (one_mem _)]
  simp only [Prod.mk.injEq, and_true]
  apply hφ i
  rw [Classical.choose_spec h1, map_one]

structure Word extends CoprodI.Word G where
  left : H
  normalized : ∀ i g, ⟨i, g⟩ ∈ toList → (normalizeSingle φ g).2 = g

open List

/- Inspired by a similar structure in `CoprodI` -/
structure Pair (i : ι) where
  head : G i
  /-- The remaining letters of the word, excluding the first letter -/
  tail : Word φ
  /-- The index first letter of tail of a `Pair M i` is not equal to `i` -/
  fstIdx_ne : tail.fstIdx ≠ some i

variable [DecidableEq ι] [∀ i, DecidableEq (G i)]

theorem eq_one_of_smul_normalized (w : CoprodI.Word G) {i : ι} (h : H)
    (hφ : ∀ i, Function.Injective (φ i))
    (hw : ∀ i g, ⟨i, g⟩ ∈ w.toList → (normalizeSingle φ g).2 = g)
    (hφw : ∀ j g, ⟨j, g⟩ ∈ (φ i h • w).toList → (normalizeSingle φ g).2 = g) :
    h = 1 := by
  have hhead : (normalizeSingle φ (Word.equivPair i w).head).2 =
      (Word.equivPair i w).head := by
    rw [Word.equivPair_head]
    split_ifs with h
    · rcases h with ⟨_, rfl⟩
      dsimp
      exact hw _ _ (List.head_mem _)
    · rw [normalizeSingle_one _ hφ]
  by_contra hh1
  have := hφw i (φ i h * (Word.equivPair i w).head) ?_
  · apply hh1
    simpa [normalizeSingle_mul _ hφ, hhead, ((injective_iff_map_eq_one' _).1 (hφ i))] using this
  . simp only [Word.mem_smul_iff, not_true, false_and, ne_eq, Option.mem_def, mul_right_inj,
      exists_eq_right', mul_right_eq_self, exists_prop, true_and, false_or]
    constructor
    · intro h
      apply_fun (normalizeSingle φ) at h
      rw [normalizeSingle_one _ hφ, normalizeSingle_mul _ hφ, hhead,
        Prod.ext_iff] at h
      rcases h with ⟨h₁, h₂⟩
      dsimp at h₁ h₂
      rw [h₂, normalizeSingle_one _ hφ, _root_.mul_one] at h₁
      contradiction
    · rw [Word.equivPair_head]
      dsimp
      split_ifs with hep
      · rcases hep with ⟨hnil, rfl⟩
        rw [head?_eq_head _ hnil]
        simp_all
      · push_neg at hep
        by_cases hw : w.toList = []
        · simp [hw, Word.fstIdx]
        · simp [head?_eq_head _ hw, Word.fstIdx, hep hw]

theorem Word.ext {w₁ w₂ : Word φ} (i : ι)
    (h : φ i w₁.left • w₁.toWord = φ i w₂.left • w₂.toWord) :
    w₁ = w₂ := by
  rcases w₁ with ⟨w₁, h₁, hw₁⟩
  rcases w₂ with ⟨w₂, h₂, hw₂⟩
  dsimp at *
  rw [smul_eq_iff_eq_inv_smul, ← mul_smul, ← map_inv, ← map_mul] at h
  subst h
  have : h₁⁻¹ * h₂ = 1 := eq_one_of_smul_normalized φ _ (h₁⁻¹ * h₂) hφ hw₂ hw₁
  rw [inv_mul_eq_one] at this; subst this
  simp

noncomputable def rcons {i : ι} (p : Pair φ i) : Word φ :=
  let n := normalizeSingle φ (p.head * φ i p.tail.left)
  { toWord := n.2 • p.tail.toWord,
    left := n.1,
    normalized := by
      intro j g₂ hg₂
      rw [Word.mem_smul_iff] at hg₂
      rcases hg₂ with ⟨_, hg₂⟩ | ⟨hg1, rfl, hg₂⟩
      · exact p.tail.normalized _ _ hg₂
      · rcases hg₂ with hg₂ | ⟨m', hm', rfl⟩ | hg₂
        · exact p.tail.normalized _ _ (List.mem_of_mem_tail hg₂)
        · have := p.fstIdx_ne
          intros
          simp_all [Word.fstIdx]
        · cases hg₂.2
          simp }

noncomputable def toPair (i) (w : Word φ) : Pair φ i :=
  let p := Word.equivPair i w.toWord
  { p with
    --This is wrong
    tail :=
    { toWord := p.tail
      left := w.left
      normalized := fun _ _ h =>
        w.normalized _ _ (Word.mem_of_mem_equivPair_tail_toList _ h) } }

noncomputable def summandAction {i : ι} : MulAction (G i) (Word φ) :=
  { smul := fun g w => rcons φ { toPair φ i w with head := g * (toPair φ i w).head }
    one_smul := sorry
    mul_smul := by
      intro g₁ g₂ w
      simp only [instHSMul]
      apply Word.ext _ hφ i
      simp only [rcons, toPair, ← mul_smul,
        normalizeSingle_fst_mul_normalizeSingle_snd, _root_.mul_one,
        Word.equivPair_smul_same, Word.equivPair_equivPair_tail]



  }



end Word

end AmalgamatedProduct
