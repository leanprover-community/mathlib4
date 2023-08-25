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


variable [Inhabited ι]

variable (φ)

variable (hφ : ∀ i, Function.Injective (φ i))

noncomputable def normalizeSingle [DecidableEq ι]
    {i : ι} (g : G i) [Decidable (g ∈ (φ i).range)] : Σ (j : ι), G j :=
  letI := Classical.propDecidable
  if hg : g ∈ (φ i).range
  then ⟨default, rangeEquiv hφ i default ⟨g, hg⟩⟩
  else ⟨i, g⟩

theorem normalizeSingle_fst_eq_iff [DecidableEq ι]
    {i : ι} (g : G i) [Decidable (g ∈ (φ i).range)] :
    (normalizeSingle φ hφ g).1 = default ↔
      i ≠ default → (normalizeSingle φ hφ g) = ⟨i, g⟩
      → g ∈ (φ i).range := by
  rw [normalizeSingle]
  split_ifs with h
  · simp only [ne_eq, MonoidHom.mem_range, true_iff] at h
    simp_all
  · simp_all (config := { contextual := true }) [iff_iff_implies_and_implies, imp_false]


structure Word extends CoprodI.Word G where
  normalized : ∀ i g, ⟨i, g⟩ ∈ toList → g ∈ (φ i).range → i = default

open List

/- Inspired by a similar structure in `CoprodI` -/
structure Pair (i : ι) where
  head : G i
  /-- The remaining letters of the word, excluding the first letter -/
  tail : Word φ
  /-- The index first letter of tail of a `Pair M i` is not equal to `i` -/
  fstIdx_ne : tail.fstIdx ≠ some i

variable [DecidableEq ι] [∀ i, DecidableEq (G i)]

noncomputable def rcons {i : ι} (hφ : ∀ i, Function.Injective (φ i))
    [∀ i g, Decidable (g ∈ (φ i).range)] (p : Pair φ i) : Word φ :=
  { toWord := (normalizeSingle φ hφ p.head).2 • p.tail.toWord,
    normalized := by
      intro j g₂ hg₂ hrange
      rw [Word.mem_smul_iff] at hg₂
      rcases hg₂ with ⟨_, hg₂⟩ | ⟨hg1, rfl, hg₂⟩
      · exact p.tail.normalized _ _ hg₂ hrange
      · rcases hg₂ with hg₂ | ⟨m', hm', rfl⟩ | hg₂
        · exact p.tail.normalized _ _ (List.mem_of_mem_tail hg₂) hrange
        · have := p.fstIdx_ne
          rw [normalizeSingle_fst_eq_iff, Sigma.ext_iff, and_imp]
          intro hin hnorm _
          rw [Option.mem_def] at hm'
          apply_fun Option.map Sigma.fst at hm'
          rw [Word.fstIdx] at this
          simp_all
        · rw [normalizeSingle_fst_eq_iff, Sigma.ext_iff, and_imp]
          intro _ _ _
          cases hg₂.2
          convert hrange <;> simp_all [HEq.symm] }

end Word

end AmalgamatedProduct
