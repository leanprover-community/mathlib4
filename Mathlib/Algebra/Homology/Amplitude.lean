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

open CategoryTheory Category Limits HomologicalComplex

universe w v u

variable {ι : Type w} {V : Type u} {c : ComplexShape ι}
    [ConditionallyCompleteLattice ι] [Sub ι] [Category.{v} V]
    [HasZeroMorphisms V] (C : HomologicalComplex V c) [∀ i, HasHomology C i]

namespace HomologicalComplex

def indexSupport := { i : ι | ¬ IsZero (C.X i) }

def indexHSupport := { i : ι | ¬ IsZero (C.homology i) }

noncomputable def inf : WithBot (WithTop ι) := ⨅ i ∈ C.indexSupport, i

noncomputable def sup : WithBot (WithTop ι) := ⨆ i ∈ C.indexSupport, i

noncomputable def infH : WithBot (WithTop ι) := ⨅ i ∈ C.indexHSupport, i

noncomputable def supH : WithBot (WithTop ι) := ⨆ i ∈ C.indexHSupport, i

noncomputable def amplitude : WithBot (WithTop ι) :=
  match C.sup, C.inf with
  | ⊤, _ => ⊤
  | _, ⊥ => ⊤
  | _, ⊤ => ⊥
  | ⊥, _ => ⊥
  | .some (.some x), .some (.some y) => x - y

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
