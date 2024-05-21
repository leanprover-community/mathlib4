-- import Mathlib.Data.ZMod.Defs
-- import Mathlib.FieldTheory.Finite.Basic
-- import Mathlib.Tactic.Ring.RingNF

-- import Mathlib.GroupTheory.Abelianization
-- import Mathlib.Order.CompleteSublattice

-- variable {G Ω:Type*} [Group G] [MulAction G Ω]

-- abbrev t : Ω → Ω → Prop := fun _ _ => True
-- abbrev b : Ω → Ω → Prop := (. = .)


-- section
-- variable (G Ω)
-- class PrimitiveActionClass : Prop where
--   is_primitive : ∀ ⦃r : Setoid Ω⦄,
--     (∀ (g : G), ∀ (x y : Ω),  r.r x y ↔ r.r (g • x) (g • y)) ↔ r = ⊤ ∨ r = ⊥
-- end

-- section
-- variable (M α : Type*) [Group M] [MulAction M α]
-- open BigOperators Pointwise


-- -- structure IwasawaStructure' where
-- --   a : α
-- --   A : Subgroup G
-- --   hAComm : sorry -- A.commutative
-- --   ha : a ∈ A
-- --   hconj : g • a
-- --   * A := T a, sous-groupe commutatif de G
-- --   * g • a = a → mul_aut.conj g A = A
-- --   * stabilizer M a ≤ normalizer A
-- --   * subgroup.normal_closure A = ⊤

-- structure IwasawaStructure where
-- /-- The subgroups of the Iwasawa structure -/
--   T : α → Subgroup M
-- /-- The commutativity property of the subgroups -/
--   is_comm : ∀ x : α, (T x).IsCommutative
-- /-- The conjugacy property of the subgroups -/
--   is_conj : ∀ g : M, ∀ x : α, T (g • x) = MulAut.conj g • T x
-- /-- The subgroups generate the group -/
--   is_generator : iSup T = ⊤

-- theorem is_simple_iwasawa
--     (is_nontrivial : Nontrivial M) (is_perfect : commutator M = ⊤)
--     (IwaS : IwasawaStructure M α) : IsSimpleGroup M := sorry

-- lemma is_primitive_of_normal ⦃N : Subgroup M⦄ (nN : N.Normal)
--     (hNX : MulAction.fixedPoints N α ≠ ⊤) : PrimitiveActionClass N Ω := sorry


-- theorem commutator_le_iwasawa' ⦃N : Subgroup M⦄ (nN : N.Normal)
--   (hNX : MulAction.fixedPoints N α ≠ ⊤):
--     commutator M ≤ N := by
--   have : PrimitiveActionClass N Ω := is_primitive_of_normal nN hNX

--   sorry
