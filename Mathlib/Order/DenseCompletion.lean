/-
Copyright (c) 2026 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.Completion
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Topology.Order.Basic

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

variable {α β : Type*}

noncomputable def embedLex [PartialOrder α] [PartialOrder β] (b : β) :
    α ↪o DedekindCut (Lex (α × β)) :=
  RelEmbedding.trans principalEmbedding (factorEmbedding (
    ({toFun c := toLex (c, b),
      inj' x y h := by simpa using h,
      map_rel_iff' {x y} := by
        simp [Prod.Lex.toLex_le_toLex, ← le_iff_lt_or_eq] } : α ↪o Lex (α × β)).trans
        principalEmbedding))

variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
variable [LinearOrder β] [TopologicalSpace β] [OrderTopology β]
  [DenselyOrdered β] [NoMinOrder β]

#synth DenselyOrdered (DedekindCut (α ×ₗβ))
#synth CompleteLinearOrder (DedekindCut (α ×ₗβ))

example : @OrderTopology (DedekindCut (α ×ₗ β)) (Preorder.topology _) _ :=
  let := Preorder.topology (DedekindCut (Lex (α × β)))
  { topology_eq_generate_intervals := rfl }

variable [TopologicalSpace (DedekindCut (α ×ₗ β))]
  [OrderTopology (DedekindCut (α ×ₗ β))]

variable {b : β} {ι : α ↪o DedekindCut (α ×ₗ β)}
    (hι : ι = embedLex b)

example : Continuous ι := by
  rw [OrderTopology.continuous_iff]
  intro c
  constructor
  · have H (a : α) : a ∈ ι ⁻¹' Ioi c ↔ toLex (a, b) ∉ c.left := by
      conv_lhs =>
        rw [mem_preimage, mem_Ioi]
        simp [hι, embedLex]
        rw [← not_le, DedekindCut.principal_le_iff]
    rw [← DedekindCut.lowerBounds_right] at H
    simp only [mem_lowerBounds] at H
    push Not at H
    rw [isOpen_iff_nhds]
    intro a ha
    rw [H] at ha
    obtain ⟨x, hx⟩ := ha
    have : ∃ u v, x = toLex (u, v)   := sorry
    rcases this with ⟨u, v, rfl⟩
    simp only [Prod.Lex.lt_iff, ofLex_toLex] at hx
    intro F hF
    simp only [Filter.mem_principal] at hF
    rcases hx.2 with (h | h)
    · sorry
    · sorry
  · sorry

/-
noncomputable def embedBotTopLex (b : β) :
    α ↪o WithBot (WithTop (DedekindCut (Lex (α × β)))) :=
  (RelEmbedding.trans WithTop.coeOrderHom WithBot.coeOrderHom).trans
    (embedLex b).withTopMap.withBotMap
-/

end DedekindCut
