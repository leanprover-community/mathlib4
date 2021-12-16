/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

noncomputable def skipLeft {β : α → Sort _}
  (w : (a : α) → WellFoundedRelation (β a)) : WellFoundedRelation ((a : α) ×' β a) :=
  ⟨_, PSigma.lex emptyWf.2 fun b => (w b).2⟩

noncomputable def generalizeRight {β : α → Sort _}
  (w : WellFoundedRelation α) : WellFoundedRelation ((a : α) ×' β a) :=
  invImage PSigma.fst w

noncomputable def generalizeLeft
  (w : WellFoundedRelation β) : WellFoundedRelation ((a : α) ×' β) :=
  invImage PSigma.snd w
