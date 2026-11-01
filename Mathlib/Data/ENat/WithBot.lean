/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Data.ENat.Basic

/-!

# Lemmas for WithBot ENat

-/

namespace ENat.WithBot

lemma eq_natCast_of_ne_bot_of_ne_top {x : WithBot ℕ∞} (ne1 : x ≠ ⊥) (ne2 : x ≠ ⊤) :
    ∃ n : ℕ, x = n := by
  obtain ⟨m, rfl⟩ := WithBot.ne_bot_iff_exists.mp ne1
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp (WithBot.coe_inj.not.mp ne2)
  exact ⟨n, coe_eq_natCast n⟩

end ENat.WithBot
