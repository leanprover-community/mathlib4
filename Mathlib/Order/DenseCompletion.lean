/-
Copyright (c) 2026 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.Completion
public import Mathlib.Order.Hom.WithTopBot

/-!
# `OrderEmbedding` of a partial order into a dense and complete linear order

* `DedekindCut.embedLex`: given `b : β`,
  embeds a partial order `α` into `DedekindCut (α ×ₗ β)`.

* `DedekindCut.embedBotTopLex`: given `b : β`,
  embeds a partial order `α` into `WithBot (WithTop (DedekindCut (α ×ₗ β)))`.

The interest of these definitions is that when `β` is linearly ordered, densely ordered
and has no extremal elements, the target orders is dense and,
in the second case, complete. It suffices to take `β := ℚ`.

-/

@[expose] public section

namespace DedekindCut

open Set Concept

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

noncomputable def embedLex (b : β) :
    α ↪o DedekindCut (Lex (α × β)) :=
  RelEmbedding.trans principalEmbedding (factorEmbedding (
    ({toFun c := toLex (c, b),
      inj' x y h := by simpa using h,
      map_rel_iff' {x y} := by
        simp [Prod.Lex.toLex_le_toLex, ← le_iff_lt_or_eq] } : α ↪o Lex (α × β)).trans
        principalEmbedding))

noncomputable def embedBotTopLex (b : β) :
    α ↪o WithBot (WithTop (DedekindCut (Lex (α × β)))) :=
  (RelEmbedding.trans WithTop.coeOrderHom WithBot.coeOrderHom).trans
    (embedLex b).withTopMap.withBotMap

end DedekindCut
