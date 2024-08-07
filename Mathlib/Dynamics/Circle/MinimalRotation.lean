import Mathlib.Topology.Instances.AddCircle
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
-/

open Set Filter
open scoped Pointwise

namespace AddCircle

theorem dense_addSubmonoid_of_accPt_zero {p : ℝ} {S : Type*} [SetLike S (AddCircle p)]
    [AddSubmonoidClass S (AddCircle p)] {s : S} (hp : p ≠ 0)
    (h : AccPt (0 : AddCircle p) (𝓟 s)) : Dense (s : Set (AddCircle p)) := by
  rw [← QuotientAddGroup.dense_preimage_mk, dense_iff_exists_between]
  intro a b hlt
  wlog ha : 0 ≤ a generalizing a b
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, 0 ≤ a + m * p := by
      -- TODO: add `exists_lt_zsmul`
      cases hp.lt_or_lt with
      | inl hp =>
        obtain ⟨m, hm⟩ := Archimedean.arch (-a) (neg_pos.2 hp)
        use -m
        simpa using hm
      | inr hp =>   
        obtain ⟨m, hm⟩ := Archimedean.arch (-a) hp
        use m
        simpa [neg_le_iff_add_nonneg'] using hm
    rcases this (a + m * p) (b + m * p) (by simpa) hm with ⟨c, hcs, hac, hcb⟩
    refine ⟨c - m * p, ?_, by linarith, by linarith⟩
    simpa using hcs


  -- have ho : IsOpen (QuotientAddGroup.mk '' Ioo 0 (b - a : ℝ) : Set (AddCircle p)) :=
  --   QuotientAddGroup.isOpenMap_coe _ _ isOpen_Ioo
  -- have hne : 

theorem dense_zmultiples_tfae (a p : ℝ) :
    List.TFAE [
      Dense (AddSubmonoid.multiples (a : AddCircle p) : Set (AddCircle p)),
      Dense (AddSubgroup.zmultiples (a : AddCircle p) : Set (AddCircle p)),
      Dense (AddSubgroup.closure {a, p} : Set ℝ),
      Irrational (a / p)
    ] := by
  tfae_have 1 → 2
  · refine fun h ↦ h.mono <| range_subset_iff.2 fun k ↦ ?_
    exact ⟨k, mod_cast rfl⟩
  tfae_have 2 ↔ 3
  · rw [← QuotientAddGroup.coe_mk', ← AddMonoidHom.map_zmultiples, AddSubgroup.coe_map,
      QuotientAddGroup.coe_mk', QuotientAddGroup.dense_image_mk,
      insert_eq, AddSubgroup.closure_union, AddSubgroup.zmultiples_eq_closure,
      AddSubgroup.zmultiples_eq_closure, AddSubgroup.add_normal]
  tfae_have 3 → 4
  · rintro h ⟨q, hq⟩
    obtain ⟨r, har, hpr⟩ : ∃ r, a ∈ AddSubgroup.zmultiples r ∧ p ∈ AddSubgroup.zmultiples r := by
      rcases eq_or_ne p 0 with rfl | hp
      · use a
        simp [zero_mem]
      · refine ⟨p / q.den, ⟨q.num, ?_⟩, q.den, ?_⟩
        · rw [← Rat.num_div_den q, Rat.cast_div] at hq
          field_simp [mul_comm] at *
          exact hq
        · field_simp
    have : AddSubgroup.closure {a, p} ≤ AddSubgroup.zmultiples r := by
      simp [pair_subset_iff, AddSubgroup.mem_zmultiples_iff, har, hpr]
    exact not_denseRange_zsmul r (h.mono this)
  tfae_have 4 → 1
  · intro h
    
    

end AddCircle
