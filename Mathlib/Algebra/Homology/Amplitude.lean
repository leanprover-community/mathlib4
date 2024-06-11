/-
Copyright (c) 2024 Brendan Seamas Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Seamas Murphy
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Int.ConditionallyCompleteOrder

/-!
# Support and amplitude of homological complexes.

Given `C : HomologicalComplex V c` of shape `c : ComplexShape ι`
the *strict support* of `C` is the set of indices `i : ι` such that `C.X i`
is not a zero object. We write this `C.indexSupport` or `indexSupport C`.

-/

section ToMove

open Classical

variable {α} {motive : Set α → Sort*}
    {motive₂ : (s : Set α) → motive s → Prop}
    [ConditionallyCompleteLattice α] (empty : motive ∅)
    (bounded : (s : Set α) → s.Nonempty → (x y : α) →
      IsGLB s x → IsLUB s y → motive s)
    (boundedBelow : (s : Set α) → s.Nonempty → (x : α) →
      IsGLB s x → ¬ BddAbove s → motive s)
    (boundedAbove : (s : Set α) → s.Nonempty → (x : α) →
      ¬ BddBelow s → IsLUB s x → motive s)
    (unbounded : (s : Set α) → s.Nonempty →
      ¬ BddBelow s → ¬ BddAbove s → motive s)

noncomputable def boundedCases (s : Set α) : motive s :=
  if h₁ : s = ∅ then h₁ ▸ empty else
  have h₁ : s.Nonempty := Set.nonempty_iff_ne_empty.mpr h₁
  if h₂ : BddBelow s then if h₃ : BddAbove s
    then bounded s h₁ (sInf s) (sSup s) (isGLB_csInf h₁ h₂) (isLUB_csSup h₁ h₃)
    else boundedBelow s h₁ (sInf s) (isGLB_csInf h₁ h₂) h₃
  else if h₃ : BddAbove s
  then boundedAbove s h₁ (sSup s) h₂ (isLUB_csSup h₁ h₃)
  else unbounded s h₁ h₂ h₃

variable {empty bounded boundedBelow boundedAbove unbounded}
    (emptyH : motive₂ ∅ empty)
    (boundedH : (s : Set α) → (h₁ : s.Nonempty) → (x y : α) →
      (h₂ : IsGLB s x) → (h₃ : IsLUB s y) → motive₂ s (bounded s h₁ x y h₂ h₃))
    (boundedBelowH : (s : Set α) → (h₁ : s.Nonempty) → (x : α) →
      (h₂ : IsGLB s x) → (h₃ : ¬ BddAbove s) → motive₂ s (boundedBelow s h₁ x h₂ h₃))
    (boundedAboveH : (s : Set α) → (h₁ : s.Nonempty) → (x : α) →
      (h₂ : ¬ BddBelow s) → (h₃ : IsLUB s x) → motive₂ s (boundedAbove s h₁ x h₂ h₃))
    (unboundedH : (s : Set α) → (h₁ : s.Nonempty) → (h₂ : ¬ BddBelow s) →
      (h₃ : ¬ BddAbove s) → motive₂ s (unbounded s h₁ h₂ h₃))

lemma boundedCases.induct (s : Set α) :
    motive₂ s (boundedCases empty bounded boundedBelow boundedAbove unbounded s) := by
  dsimp only [boundedCases]
  split_ifs with h₁ h₂ h₃ h₄
  · convert emptyH using 1
    exact eqRec_heq h₁.symm empty
  · exact boundedH _ _ _ _ _ _
  · exact boundedBelowH _ _ _ _ _
  · exact boundedAboveH _ _ _ _ _
  · exact unboundedH _ _ _ _

end ToMove

open CategoryTheory Category Limits HomologicalComplex

universe w v u

variable {ι : Type w} {V : Type u} {c : ComplexShape ι}
    [AddCommSemigroup ι] [ConditionallyCompleteLattice ι] [ExistsAddOfLE ι]
    [CovariantClass ι ι (· + ·) (· ≤ ·)] [Sub ι] [OrderedSub ι]
    [Category.{v} V] [HasZeroMorphisms V] (C : HomologicalComplex V c)
    [∀ i, HasHomology C i]

namespace HomologicalComplex

def indexSupport := { i : ι | ¬ IsZero (C.X i) }

def indexHSupport := { i : ι | ¬ IsZero (C.homology i) }

noncomputable def inf : WithBot (WithTop ι) := ⨅ i ∈ C.indexSupport, i

noncomputable def sup : WithBot (WithTop ι) := ⨆ i ∈ C.indexSupport, i

noncomputable def infH : WithBot (WithTop ι) := ⨅ i ∈ C.indexHSupport, i

noncomputable def supH : WithBot (WithTop ι) := ⨆ i ∈ C.indexHSupport, i

noncomputable def amplitude : WithBot (WithTop ι) :=
  boundedCases (motive := fun _ => WithBot (WithTop ι)) ⊥
    (fun _ _ x y _ _ => (y - x : ι)) (fun _ _ _ _ _ => ⊤) (fun _ _ _ _ _ => ⊥)
    (fun _ _ _ _ => ⊤) C.indexSupport

lemma amplitude_spec : C.sup = C.inf + C.amplitude :=
  boundedCases.induct (motive₂ := fun (s : Set ι) w =>
    (⨆ i ∈ s, (i : WithBot (WithTop ι))) = (⨅ i ∈ s, (i : WithBot (WithTop ι))) + w)
    (emptyH := by simp only [Set.mem_empty_iff_false, not_false_eq_true,
      iSup_neg, iSup_bot, iInf_neg, iInf_top, WithBot.add_bot])
    (boundedH := fun s hs x y hx hy => show _ = _ + _ by
      rw [← sInf_image, ← sSup_image, ← s.image_image,
        ← WithBot.coe_sInf' (WithTop.coe_mono.map_bddBelow hx.bddBelow),
        ← WithTop.coe_sInf' hs, ← WithBot.coe_sSup' (hs.image _),
        ← WithTop.coe_sSup' (hy.bddAbove), ← WithBot.coe_add, ← WithTop.coe_add,
        hy.csSup_eq hs, hx.csInf_eq hs, add_tsub_cancel_of_le]
      obtain ⟨t, ht⟩ := hs
      exact le_trans (hx.left ht) (hy.left ht))
    (boundedBelowH := fun s hs₁ x hx hs₂ => show _ = _ + _ by
      rw [← sSup_image, ← sInf_image, ← s.image_image,
        ← WithBot.coe_sSup' (hs₁.image _), WithTop.sSup_coe_eq_top hs₂,
        ← WithBot.coe_sInf' (WithTop.coe_mono.map_bddBelow hx.bddBelow)]
      exact congrArg _ (WithTop.add_top _).symm)
    (boundedAboveH := fun s hs₁ x hs₂ hx => show _ = _ + _ by
      rw [← sSup_image, ← sInf_image, ← s.image_image, WithBot.add_bot,
        -- ← WithBot.coe_sSup' (hs.image _), WithTop.sSup_coe_eq_top hy,
        -- ← WithBot.coe_sInf' (WithTop.coe_mono.map_bddBelow hx.bddBelow)
        ]
      simp only [sSup_eq_bot, Set.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, WithBot.coe_ne_bot, imp_false]
      -- exact congrArg _ (WithTop.add_top _).symm
      admit)
    (unboundedH := fun s hs₁ hs₂ hs₃ => by
      admit)
    C.indexSupport

  -- have H₁ : ⨆ i ∈ (∅ : Set ι), (i : WithBot (WithTop ι)) = ⊥ := by
  --   simp only [Set.mem_empty_iff_false, not_false_eq_true, iSup_neg, iSup_bot]
  -- have H₂ s (hs : s.Nonempty) (x y : ι) (hx : IsGLB s x) (hy : IsLUB s y) :
  --     False := sorry
  -- @boundedCases.induct _ (fun _ => WithBot (WithTop ι))
  --   (fun (s : Set ι) w => (⨆ i ∈ s, (i : WithBot (WithTop ι))) =
  --                           w + (⨅ i ∈ s, (i : WithBot (WithTop ι))))
  --   _ ⊥ (fun _ _ x y _ _ => (y - x : ι)) (fun _ _ _ _ _ => ⊤)
  --   (fun _ _ _ _ _ => ⊥) (fun _ _ _ _ => ⊤)
  --   H₁
  --   (by dsimp
  --       admit)
  --   _
  --   _
  --   _
  --   _

lemma amplitude.induct
    {motive : HomologicalComplex V c → WithBot (WithTop ι) → Prop}
    (C : HomologicalComplex V c) : motive C (amplitude C) := by

  admit

end HomologicalComplex

lemma sup_eq_inf_add_amplitude (C : ChainComplex V ℕ) :
    C.sup = C.inf + C.amplitude := by
  dsimp only [amplitude]
  match C.sup, C.inf with
  | ⊤, x =>
    -- dsimp only [Top.top]
    change WithBot.some none = x + _ --(⊤ : WithBot (WithTop ℕ))
    admit
  | _, ⊥ => sorry
  | _, ⊤ => sorry
  | ⊥, _ => sorry
  | .some (.some x), .some (.some y) => sorry


lemma amplitude_eq_iff (C : ChainComplex V ℕ) (i : WithBot (WithTop ℕ)) :
    C.amplitude = i ↔ C.sup = C.inf + i := by
  refine ⟨(· ▸ sup_eq_inf_add_amplitude C), ?_⟩


  -- generalize Hs : sup C = s
  -- cases' s with s; on_goal 2 => cases' s with s
  -- · have H : C.inf = ⊤ :=
  --     haveI := Subtype.isEmpty_of_false fun j hj =>
  --       WithBot.coe_ne_bot <| iSup₂_eq_bot.mp Hs j hj
  --     (iInf_subtype'' _ _).symm.trans ((iInf_of_isEmpty _).trans sInf_empty)
  --   rw [amplitude, H, Hs]
  --   dsimp

  --   cases' i with i; on_goal 2 => cases' i with i
  --   · exact iff_of_true rfl rfl
  --   · exact Iff.rfl
  --   · exact iff_of_false WithBot.bot_ne_coe bot_ne_top
  -- ·

  --   admit
  -- ·

  --   admit
