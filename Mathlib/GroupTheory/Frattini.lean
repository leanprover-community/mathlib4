/-
Copyright (c) 2024 Colva Roney-Dougal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colva Roney-Dougal, Inna Capdeboscq, Susanna Fishel, Kim Morrison
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.Radical

/-!
# The Frattini subgroup

We give the definition of the Frattini subgroup of a group, and three elementary results:
* The Frattini subgroup is characteristic.
* If every subgroup of a group is contained in a maximal subgroup, then
the Frattini subgroup consists of the non-generating elements of the group.
* The Frattini subgroup of a finite group is nilpotent.
-/

/-- The Frattini subgroup of a group is the intersection of the maximal subgroups. -/
def frattini (G : Type*) [Group G] : Subgroup G :=
  Order.radical (Subgroup G)

variable {G H : Type*} [Group G] [Group H]

open Subgroup


variable (G)

/-- The Frattini subgroup is characteristic. -/
instance frattini_characteristic : (frattini G).Characteristic := by
  rw [characteristic_iff_comap_eq]
  intro φ
  apply φ.comapSubgroup.map_radical

variable {G}

lemma frattini_le_coatom {K : Subgroup G} (h : IsCoatom K) : frattini G ≤ K :=
  Order.radical_le_coatom h

/--
The Frattini subgroup consists of "non-generating" elements in the following sense:

If a subgroup together with the Frattini subgroup generates the whole group,
then the subgroup is already the whole group.
-/
theorem frattini_nongenerating [IsCoatomic (Subgroup G)] {K : Subgroup G} (h : K ⊔ frattini G = ⊤) :
    K = ⊤ :=
  Order.radical_nongenerating h

noncomputable section

-- The Sylow files unnecessarily use `Fintype` (computable) where often `Finite` would suffice,
-- so wwe need this:
attribute [local instance] Fintype.ofFinite

-- This is surely in Mathlib?!
-- Asked at https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/normal.20subgroups/near/441573924
-- No answer, so it is apparently not in Mathlib.
theorem normal_of_map_subtype_normal {K : Subgroup G} {L : Subgroup K}
    (n : (map K.subtype L).Normal) : L.Normal := by
  obtain ⟨conj_mem⟩ := n
  simp only [mem_map, coeSubtype, Subtype.exists, exists_and_right, exists_eq_right,
    forall_exists_index] at conj_mem
  exact ⟨fun l l_mem k => (conj_mem l l.2 l_mem k).2⟩

/-- When `G` is finite, the Frattini subgroup is nilpotent. -/
theorem frattini_nilpotent [Fintype G] : Group.IsNilpotent (frattini G) := by
  -- We use the characterisation of nilpotency in terms of all Sylow subgroups being normal.
  have q := (isNilpotent_of_finite_tFAE (G := frattini G)).out 0 3
  rw [q]; clear q
  -- Consider each prime `p` and Sylow `p`-subgroup `P` of `frattini G`.
  intro p p_prime P
  -- The Frattini argument shows that the normalizer of `P` in `G`
  -- together with `frattini G` generates `G`.
  have frattini_argument := Sylow.normalizer_sup_eq_top P
  -- and hence by the nongenerating property of the Frattini subgroup that
  -- the normalizer of `P` in `G` is `G`.
  have normalizer_P := frattini_nongenerating frattini_argument
  -- This means that `P` is normal as a subgroup of `G`
  have P_normal_in_G : (map (frattini G).subtype ↑P).Normal := normalizer_eq_top.mp normalizer_P
  -- and hence also as a subgroup of `frattini G`, which was the remaining goal.
  exact normal_of_map_subtype_normal P_normal_in_G
