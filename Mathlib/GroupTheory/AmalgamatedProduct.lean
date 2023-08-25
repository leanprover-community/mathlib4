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
  let s : Set (G i) := rightCoset (φ i).range g
  have hs : s.Nonempty := ⟨g, mem_own_rightCoset _ _⟩
  let g' := Classical.choose hs
  let h' := Classical.choose (Classical.choose_spec (Classical.choose_spec hs)).1
  ⟨h'⁻¹, g'⟩

theorem normalizeSingle_fst_mul_normalizeSingle_snd {i : ι} (g : G i) :
    φ i (normalizeSingle φ g).1 * (normalizeSingle φ g).2 = g := by
  let s : Set (G i) := rightCoset (φ i).range g
  have hs : s.Nonempty := ⟨g, mem_own_rightCoset _ _⟩
  simp only [normalizeSingle, MonoidHom.coe_range, Set.mem_range, map_inv, Eq.ndrec, id_eq]
  rw [Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hs)).1,
    inv_mul_eq_iff_eq_mul]
  have := Classical.choose_spec (Classical.choose_spec hs)
  dsimp at this
  rw [this.2]

theorem normalizeSingle_snd_eq_of_rightCosetEquivalence {i : ι} {g₁ g₂ : G i}
    (h : RightCosetEquivalence (φ i).range g₁ g₂) :
    (normalizeSingle φ g₁).2 = (normalizeSingle φ g₂).2 := by
  simp [normalizeSingle]
  congr

theorem rightCosetEquivalence_normalizeSingle_snd {i : ι} (g : G i) :
    RightCosetEquivalence (φ i).range g (normalizeSingle φ g).2 := by
  let s : Set (G i) := rightCoset (φ i).range g
  have hs : s.Nonempty := ⟨g, mem_own_rightCoset _ _⟩
  erw [RightCosetEquivalence, rightCoset_eq_iff,
    ← mem_rightCoset_iff (s := (φ i).range) g]
  exact Classical.choose_spec hs

@[simp]
theorem normalizeSingle_snd_normalize_single_snd {i : ι} {g : G i} :
    (normalizeSingle φ (normalizeSingle φ g).2).2 = (normalizeSingle φ g).2 :=
  normalizeSingle_snd_eq_of_rightCosetEquivalence _
    (rightCosetEquivalence_normalizeSingle_snd _ _).symm

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

noncomputable def rcons {i : ι} (p : Pair φ i) : Word φ :=
  { toWord := (normalizeSingle φ p.head).2 • p.tail.toWord,
    left := p.tail.left * (normalizeSingle φ p.head).1,
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
    tail :=
    { toWord := p.tail
      left := w.left
      normalized := fun _ _ h =>
        w.normalized _ _ (Word.mem_of_mem_equivPair_tail_toList _ h) } }

noncomputable def summandAction {i : ι} (g : G i) (w : Word φ) : Word φ :=
  rcons φ { toPair φ i w with head := g * (toPair φ i w).head }



end Word

end AmalgamatedProduct
