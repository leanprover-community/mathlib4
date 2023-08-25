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

variable (φ)

variable (hφ : ∀ i, Function.Injective (φ i))

noncomputable def normalizeSingle2 [DecidableEq ι] (n : ι)
    {i : ι} (g : G i) [Decidable (g ∈ (φ i).range)] : Σ (j : ι), G j :=
  letI := Classical.propDecidable
  if hg : g ∈ (φ i).range
  then ⟨n, rangeEquiv hφ i n ⟨g, hg⟩⟩
  else ⟨i, g⟩

theorem normalizeSingle2_fst_eq_iff [DecidableEq ι] (n : ι)
    {i : ι} (g : G i) [Decidable (g ∈ (φ i).range)] :
    (normalizeSingle2 φ hφ n g).1 = n ↔
      i ≠ n → (normalizeSingle2 φ hφ n g) = ⟨i, g⟩
      → g ∈ (φ i).range := by
  rw [normalizeSingle2]
  split_ifs with h
  · simp only [ne_eq, MonoidHom.mem_range, true_iff] at h
    simp_all
  · simp_all (config := { contextual := true }) [iff_iff_implies_and_implies, imp_false]


-- theorem normalizeSingle_snd_eq_of_rightCosetEquivalence
--     {i : ι} {g₁ g₂ : G i} (hg : RightCosetEquivalence (φ i).range g₁ g₂) :
--     (normalizeSingle φ g₁).2 = (normalizeSingle φ g₂).2 := by
--   simp [normalizeSingle]
--   congr

-- theorem rightCosetEquivalence_normalizeSingle_snd {i : ι} {g : G i} :
--     RightCosetEquivalence (φ i).range g (normalizeSingle φ g).2 := by
--   let s : Set (G i) := (φ i).range *r g
--   have hs : s.Nonempty := ⟨g, mem_own_rightCoset _ _⟩
--   rw [RightCosetEquivalence, rightCoset_eq_iff]
--   exact (mem_rightCoset_iff _).1 (Classical.choose_spec hs)

-- theorem normalizeSingle_fst_mul_normalizeSingle_snd
--     {i : ι} {g : G i} : ((normalizeSingle φ g).1 : G i) * (normalizeSingle φ g).2 = g :=
--   let s : Set (G i) := (φ i).range *r g
--   let hs : s.Nonempty := ⟨g, mem_own_rightCoset _ _⟩
--   inv_mul_eq_of_eq_mul (Classical.choose_spec (Classical.choose_spec hs)).2.symm

-- @[simp]
-- theorem normalizeSingle_normalizeSingle_snd {i : ι} (g : G i) :
--     (normalizeSingle φ (normalizeSingle φ g).2).2 = (normalizeSingle φ g).2 :=
--   normalizeSingle_snd_eq_of_rightCosetEquivalence
--      _ (rightCosetEquivalence_normalizeSingle_snd φ).symm


variable (n : ι)

structure Word extends CoprodI.Word G where
  normalized : ∀ i g, ⟨i, g⟩ ∈ toList → g ∈ (φ i).range → i = n

open List

/- Inspired by a similar structure in `CoprodI` -/
structure Pair (i : ι) where
  head : G i
  /-- The remaining letters of the word, excluding the first letter -/
  tail : Word φ n
  /-- The index first letter of tail of a `Pair M i` is not equal to `i` -/
  fstIdx_ne : tail.fstIdx ≠ some i

variable [DecidableEq ι] [∀ i, DecidableEq (G i)]

noncomputable def rcons {i : ι} (hφ : ∀ i, Function.Injective (φ i))
    [∀ i g, Decidable (g ∈ (φ i).range)] (p : Pair φ n i) : Word φ n :=
  { toWord := (normalizeSingle2 φ hφ n p.head).2 • p.tail.toWord,
    normalized := by
      intro j g₂ hg₂ hrange
      rw [Word.mem_smul_iff] at hg₂
      rcases hg₂ with ⟨_, hg₂⟩ | ⟨hg1, rfl, hg₂⟩
      · exact p.tail.normalized _ _ hg₂ hrange
      · rcases hg₂ with hg₂ | ⟨m', hm', rfl⟩ | hg₂
        · exact p.tail.normalized _ _ (List.mem_of_mem_tail hg₂) hrange
        · have := p.fstIdx_ne
          rw [normalizeSingle2_fst_eq_iff, Sigma.ext_iff, and_imp]
          intro hin hnorm _
          dsimp at hrange
          rw [Option.mem_def] at hm'
          apply_fun Option.map Sigma.fst at hm'
          rw [Word.fstIdx] at this
          simp_all
        · rw [normalizeSingle2_fst_eq_iff, Sigma.ext_iff, and_imp]
          intro _ _ _
          cases hg₂.2
          convert hrange <;> simp_all [HEq.symm] }


#print List.head?
noncomputable def smul {i : ι} (hφ : ∀ i, Function.Injective (φ i))
    (g : G i) [∀ i g, Decidable (g ∈ (φ i).range)] (w : Word φ n) : Word φ n :=
  let g' := normalizeSingle2 φ hφ n g
  ⟨ (normalizeSingle2 φ hφ n (g * (Word.equivPair i w.toWord).head)).2 •
      (Word.equivPair i w.toWord).tail, by
    rintro j g₂ hg₂ hrange
    dsimp at *
    rw [Word.mem_smul_iff] at hg₂
    rcases hg₂ with ⟨hji, hg₂⟩ | ⟨hg1, rfl, hg₂⟩
    · have := Word.mem_of_mem_equivPair_tail_toList _ hg₂
      exact w.normalized _ _ this hrange
    · rcases hg₂ with hg₂ | ⟨m', hm', rfl⟩ | hg₂
      · have := w.normalized _ _
           (Word.mem_of_mem_equivPair_tail_toList _
             (List.mem_of_mem_tail hg₂)) hrange
        exact this
      · dsimp at *
        by_cases hin : i = n
        · subst hin
          simp [normalizeSingle2]
          split_ifs <;> simp
        · have := w.toWord.fstIdx_ne
      · simp at hg₂
        cases (hg₂ g₂).2
        refine w.normalized _ _ ?_ hrange
        simp


      ⟩



noncomputable def rcons (hφ : ∀ i, Function.Injective (φ i))
    {i : ι} (p : Pair φ n i) : Word φ n :=
  let g := normalizeSingle φ p.head
  let w : CoprodI.Word G := CoprodI.Word.rcons ⟨g.2, p.tail.toWord, p.3⟩
  ⟨(rangeEquiv hφ i n g.1 : G n) • w, by
    rintro ⟨j, g'⟩ h1 h2
    rw [Word.mem_smul_iff_of_ne h2, Word.mem_rcons_toList_iff] at h1
    dsimp only at h1 ⊢
    rcases h1 with h1 | ⟨h1, rfl, rfl⟩
    · exact p.tail.normalized _ h1 h2
    · simp⟩

/-- The equivalence between words and pairs. Given a word, it decomposes it as a pair by removing
the first letter if it comes from `M i`. Given a pair, it prepends the head to the tail. -/
nonrec def toPair (i) (w : Word φ n) : Pair φ n i :=
  let p := Word.equivPair i w.toWord
  { head := p.head,
    tail := ⟨p.tail, by
      rintro ⟨i, g⟩ h hn
      exact w.normalized _
        (Word.mem_of_mem_equivPair_tail_toList _ h) hn⟩,
    fstIdx_ne := p.fstIdx_ne }

def summandAction {i : ι} (hφ : ∀ i, Function.Injective (φ i)) :
    (G i) →* Equiv.Perm (Word φ n) :=
  let smul : G i → Word φ n → Word φ n :=
    fun g w => rcons φ n hφ
      { toPair φ n i w with
        head := g * (toPair φ n i w).head }
  { toFun := fun g => _ }

-- noncomputable def normalizeWord : (w : CoprodI.Word G) →
--     { w' : Word G H φ n // w'.toList.length ≤ w.toList.length }
--   | ⟨[], _, _⟩ => ⟨⟨⟨[], by simp, by simp⟩, by simp⟩, le_refl 0⟩
--   | ⟨⟨i, g⟩::l, ne_one, chain_ne⟩ =>
--     if hg : (∃ x : H, φ i x = g) ∧ i ≠ n
--     then _
--     else _


-- def Word.single {i : ι} (g : G i) : Word G H φ n :=
--   if hg1 : g = 1
--   then ⟨⟨[], by simp, by simp⟩, by simp⟩
--   else ⟨⟨[⟨i, g⟩], by simp, by simp⟩, by simp⟩

-- noncomputable def smulWord {i : ι} (g : G i)
--     (w : Word G H φ n) : Word G H φ n :=
--   letI := Classical.propDecidable
--   if hg1 : g = 1 then w
--   else if hg : (∃ x : H, φ i x = g) ∧ i ≠ n then
--     have _ : 0 < if i = n then 0 else 1 := by simp [hg.2]
--     smulWord (φ n (Classical.choose hg.1)) w
--   else
--     match w with
--     | ⟨⟨[], _, _⟩,_⟩ =>
--       ⟨⟨[⟨i, g⟩], by simp_all, by simp_all⟩, by
--         simpa using hg⟩
--     | ⟨⟨⟨j, h⟩::l, ne_one, chain_ne⟩, normalized⟩ =>
--       if hij : i = j
--       then smulWord (g * hij ▸ h)
--         ⟨⟨l,
--           fun x hx => ne_one x (List.mem_cons_of_mem _ hx),
--           (List.chain'_cons'.1 chain_ne).2⟩,
--           by simp_all; tauto⟩
--       else ⟨⟨⟨i, g⟩ :: ⟨j, h⟩ :: l,
--         by simp; simp at ne_one; tauto,
--         by simp only [ne_eq, List.chain'_cons, hij,
--             not_false_eq_true, chain_ne, and_self]⟩,
--         by
--           simp only [ne_eq, not_and, not_not, forall_exists_index] at hg
--           simp only [List.find?, List.mem_cons, MonoidHom.mem_range,
--             forall_exists_index, forall_eq_or_imp] at normalized ⊢
--           exact ⟨hg, normalized⟩⟩
-- termination_by smulWord i g w => (w.toList.length,
--   letI := Classical.decEq ι; if i = n then 0 else 1)

-- noncomputable def smulWord {i : ι} (g : G i)
--     (w : Word G H φ n) : Word G H φ n :=
--   letI := Classical.propDecidable
--   if hg1 : g = 1 then w
--   else if hg : (∃ x : H, φ i x = g) ∧ i ≠ n then
--     have _ : 0 < if i = n then 0 else 1 := by simp [hg.2]
--     smulWord (φ n (Classical.choose hg.1)) w
--   else
--     match w with
--     | ⟨⟨[], _, _⟩,_⟩ =>
--       ⟨⟨[⟨i, g⟩], by simp_all, by simp_all⟩, by
--         simpa using hg⟩
--     | ⟨⟨⟨j, h⟩::l, ne_one, chain_ne⟩, normalized⟩ =>
--       if hij : i = j
--       then smulWord (g * hij ▸ h)
--         ⟨⟨l,
--           fun x hx => ne_one x (List.mem_cons_of_mem _ hx),
--           (List.chain'_cons'.1 chain_ne).2⟩,
--           by simp_all; tauto⟩
--       else ⟨⟨⟨i, g⟩ :: ⟨j, h⟩ :: l,
--         by simp; simp at ne_one; tauto,
--         by simp only [ne_eq, List.chain'_cons, hij,
--             not_false_eq_true, chain_ne, and_self]⟩,
--         by
--           simp only [ne_eq, not_and, not_not, forall_exists_index] at hg
--           simp only [List.find?, List.mem_cons, MonoidHom.mem_range,
--             forall_exists_index, forall_eq_or_imp] at normalized ⊢
--           exact ⟨hg, normalized⟩⟩
-- termination_by smulWord i g w => (w.toList.length,
--   letI := Classical.decEq ι; if i = n then 0 else 1)

-- @[simp] theorem one_smulWord {i : ι} (w : Word G H φ n) : smulWord (1 : G i) w = w := by
--   unfold smulWord; rw [dif_pos rfl]

-- theorem smul_world_nil {i : ι} (g : G i) : smulWord g ⟨⟨[], by simp, by simp⟩, by simp⟩ =
--     if hg : (∃ x : H, φ i x = g) ∧ i ≠ n then  := by
--   unfold smulWord; rw [dif_neg]; simp

-- theorem smulWord_eq_same (i j : ι) (g : H) (w : Word G H φ n) :
--     smulWord (φ i g) w = smulWord (φ j g) w := sorry

-- theorem mul_smulWord {i : ι} (g₁ g₂ : G i) (w : Word G H φ n) :
--     smulWord g₁ (smulWord g₂ w) = smulWord (g₁ * g₂) w :=
--   letI := Classical.propDecidable
--   if hg₁1 : g₁ = 1
--   then by simp [hg₁1]
--   else if hg₂1 : g₂ = 1
--   then by simp [hg₂1]
--   else by
--     rcases w with ⟨⟨l, ne_one, chain_ne⟩, normalized⟩
--     by_cases hg₁ : (∃ x : H, φ i x = g₁) ∧ i ≠ n
--     · have _ : 0 < if i = n then 0 else 1 := by simp [hg₁]
--       rw [smulWord._unfold g₁]
--       rw [dif_neg hg₁1, dif_pos hg₁]
--       dsimp
--       by_cases hg₂ : (∃ x : H, φ i x = g₂) ∧ i ≠ n
--       · rw [smulWord._unfold g₂]
--         rw [dif_neg hg₂1, dif_pos hg₂, mul_smulWord, ← map_mul,
--           smulWord_eq_same n i, map_mul,
--           Classical.choose_spec hg₁.1, Classical.choose_spec hg₂.1]
--       · rw [smulWord._unfold g₂]
--         rw [dif_neg hg₂1, dif_neg hg₂]
--         cases l with
--         | nil =>
--           simp

--         | cons a l => sorry
--       · dsimp
--     ·


-- end Word

end AmalgamatedProduct
