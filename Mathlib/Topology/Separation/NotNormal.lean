/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Tian Chen
-/
module

public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.Topology.Separation.Regular

/-!
# Not normal topological spaces

In this file we prove (see `IsClosed.not_normal_of_continuum_le_mk`) that a separable space with a
discrete subspace of cardinality continuum is not a normal topological space.

## References

* [Willard's *General Topology*][zbMATH02107988]
-/

public section

open Set Function Cardinal TopologicalSpace

universe u
variable {X : Type u} [TopologicalSpace X]

namespace IsClosed

/-- Let `s` be a closed set in a normal space and `d` be a dense set. If the induced topology on `s`
is discrete, then `𝒫 s` has cardinality less than or equal to `𝒫 d`. -/
theorem two_pow_mk_le_two_pow_mk_dense [NormalSpace X] {s d : Set X} (hs : IsClosed s)
    [DiscreteTopology s] (hd : Dense d) : (2 : Cardinal) ^ #s ≤ 2 ^ #d := by
  have h_closed (t) (ht : t ∈ 𝒫 s) : IsClosed t := by
    rw [← inter_eq_self_of_subset_right ht, ← Subtype.image_preimage_val]
    exact hs.isClosedMap_subtype_val _ (isClosed_discrete _)
  choose U V hU hV hUs hVs hUV using fun t : 𝒫 s ↦
    normal_separation (h_closed t t.2) (h_closed _ diff_subset) disjoint_sdiff_right
  have hUd {t₁ t₂} (h : U t₁ ∩ d = U t₂ ∩ d) : t₁.1 ⊆ t₂.1 := by
    by_contra ht
    rw [← diff_nonempty] at ht
    have hUVd := hd.inter_open_nonempty _ ((hU t₁).inter (hV t₂)) <| ht.mono <|
      subset_inter (diff_subset.trans (hUs t₁)) ((diff_subset_diff_left t₁.2).trans (hVs t₂))
    rw [inter_right_comm, h] at hUVd
    exact hUVd.not_disjoint <| disjoint_of_subset_left inter_subset_left (hUV t₂)
  have h_inj : Injective (U · ∩ d) := fun _ _ h ↦ SetCoe.ext <| (hUd h).antisymm (hUd h.symm)
  rw [← mk_powerset, ← mk_powerset, ← mk_range_eq _ h_inj]
  apply mk_le_mk_of_subset
  rw [range_subset_iff]
  intro
  exact inter_subset_right

theorem mk_lt_two_pow_mk_dense [NormalSpace X] {s d : Set X} (hs : IsClosed s)
    [DiscreteTopology s] (hd : Dense d) : #s < 2 ^ #d :=
  (#s).cantor.trans_le <| hs.two_pow_mk_le_two_pow_mk_dense hd

variable [SeparableSpace X]

theorem two_pow_mk_lt_continuum [NormalSpace X] {s : Set X} (hs : IsClosed s)
    [DiscreteTopology s] : 2 ^ #s ≤ 𝔠 :=
  have ⟨d, hd_countable, hd_dense⟩ := exists_countable_dense X
  calc
    2 ^ #s ≤ 2 ^ #d := hs.two_pow_mk_le_two_pow_mk_dense hd_dense
    _ ≤ 2 ^ ℵ₀ := power_le_power_left two_ne_zero hd_countable.le_aleph0
    _ = 𝔠 := two_power_aleph0

/-- Let `s` be a closed set in a separable normal space. If the induced topology on `s` is discrete,
then `s` has cardinality less than continuum. -/
theorem mk_lt_continuum [NormalSpace X] {s : Set X} (hs : IsClosed s)
  [DiscreteTopology s] : #s < 𝔠 := (#s).cantor.trans_le hs.two_pow_mk_lt_continuum

/-- Let `s` be a closed set in a separable space. If the induced topology on `s` is discrete and `s`
has cardinality at least continuum, then the ambient space is not a normal space. -/
theorem not_normal_of_continuum_le_mk {s : Set X} (hs : IsClosed s) [DiscreteTopology s]
    (hmk : 𝔠 ≤ #s) : ¬NormalSpace X := fun _ ↦ hs.mk_lt_continuum.not_ge hmk

end IsClosed
