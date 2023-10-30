import Mathlib.Order.Hom.Bounded
import Mathlib.Order.Hom.Lattice
import Mathlib.Order.Zorn

universe u
variable {α : Type} [Lattice α] [BoundedOrder α] [DistribLattice α]

variable (F : InfTopHom α Prop) (G : SupBotHom α Prop)

variable (h : (setOf F) ∩ (setOf G) = ∅)

-- A typical proof using Zorn could look like this (TODO: update to mathlib4)
-- ```lean
-- lemma zorny_lemma : zorny_statement :=
-- begin
--   let s : Set α := {x | whatever x},
--   suffices : ∃ x ∈ s, ∀ y ∈ s, y ⊆ x → y = x, -- or with another operator
--   { exact proof_post_zorn },
--   apply zorn_subset, -- or another variant
--   rintro c hcs hc,
--   obtain rfl | hcnemp := c.eq_empty_or_nonempty, -- you might need to disjunct on c empty or not
--   { exact ⟨edge_case_construction,
--       proof_that_edge_case_construction_respects_whatever,
--       proof_that_edge_case_construction_contains_all_stuff_in_c⟩ },
--   exact ⟨construction,
--     proof_that_construction_respects_whatever,
--     proof_that_construction_contains_all_stuff_in_c⟩,
-- end
-- ```
-- TODO: introduce LatticeFilter α as alias for InfTopHom α Prop
def pure_separator : InfTopHom α Prop  := by
  let s : Set (InfTopHom α Prop) := {X | F ≤ X ∧ (setOf X) ∩ (setOf G) = ∅}
  suffices post_zorn : ∃ X ∈ s, ∀ Y ∈ s, Y ≤ X → Y = X
  {
    use post_zorn.choose
    apply map_top
  }
  have todo : ∀ (c : Set ↑s), IsChain (fun x x_1 ↦ x ≤ x_1) c → BddAbove c := by sorry
  let z := zorn_partialOrder (α := s) todo
  set m := z.choose with hm
  have hm' := z.choose_spec
  rw [←hm] at hm'
  use m
  constructor
  { simp }
  -- TODO

-- prove afterwards that pure_separator is a bounded lattice homomorphism:

theorem separator_contains_filter : setOf F.1 ⊆ setOf (pure_separator F G).1 := by sorry

theorem separator_disjoint_from_ideal  : setOf (pure_separator F G).1 ∩ setOf G.1 = ∅ := by sorry
