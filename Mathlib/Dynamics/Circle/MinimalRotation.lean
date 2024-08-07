import Mathlib.Topology.Instances.AddCircle
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
-/

open Set Filter
open scoped Pointwise Topology

namespace AddCircle

theorem dense_addSubmonoid_of_accPt_zero {p : ℝ} {S : Type*} [SetLike S (AddCircle p)]
    [AddSubmonoidClass S (AddCircle p)] {s : S} (hp : p ≠ 0)
    (h : AccPt (0 : AddCircle p) (𝓟 s)) : Dense (s : Set (AddCircle p)) := by
  rw [← QuotientAddGroup.dense_preimage_mk, dense_iff_exists_between]
  intro a b hlt
  obtain ⟨x, hx₀, hxs, hx⟩ : ∃ x ≠ (0 : ℝ), ↑x ∈ s ∧ |x| < b - a := by
    set t : Set (AddCircle p) := QuotientAddGroup.mk '' Ioo (a - b) (b - a)
    have ht : t ∈ 𝓝 0 :=
      (QuotientAddGroup.isOpenMap_coe _ _ isOpen_Ioo).mem_nhds ⟨0, by simp [hlt], rfl⟩
    rcases (accPt_iff_nhds ..).1 h t ht with ⟨_, ⟨⟨x, hx, rfl⟩, hxs⟩, hx₀⟩
    refine ⟨x, ne_of_apply_ne QuotientAddGroup.mk hx₀, hxs, ?_⟩
    rwa [abs_lt, neg_sub]
  obtain ⟨c, hc, n, hna, hnb⟩ :
      ∃ c ∈ AddSubgroup.zmultiples p, ∃ n : ℕ, n • x ∈ Ioo (a + c) (b + c) := by
    clear! s
    wlog hltx : 0 < x generalizing a b x
    · obtain ⟨c, hc, n, hn⟩ :=
        this (-b) (-a) (by gcongr) (-x) (neg_ne_zero.2 hx₀) (by rw [abs_neg]; linarith)
          (neg_pos.2 <| hx₀.lt_or_lt.resolve_right hltx)
      refine ⟨-c, neg_mem hc, n, ?_⟩
      simpa [add_comm, and_comm] using hn
    obtain ⟨c, hc, hc₀⟩ : ∃ c ∈ AddSubgroup.zmultiples p, 0 ≤ a + c := by
      rcases Archimedean.arch (-a) (abs_pos.2 hp) with ⟨n, hn⟩
      refine ⟨n • |p|, nsmul_mem (abs_mem_iff.2 <| AddSubgroup.mem_zmultiples _) _, ?_⟩
      linarith
    use c, hc
    obtain ⟨n, hna, hn⟩ : ∃ n : ℤ, n • x ∈ Ioc (a + c) (a + c + x) := by
      simpa only [zero_add] using (existsUnique_add_zsmul_mem_Ioc hltx 0 (a + c)).exists
    have hn₀ : 0 ≤ n := by
      contrapose! hna
      exact (smul_nonpos_of_nonpos_of_nonneg hna.le hltx.le).trans hc₀
    lift n to ℕ using hn₀
    refine ⟨n, mod_cast hna, mod_cast (hn.trans_lt ?_)⟩
    rw [abs_of_pos hltx] at hx
    linarith
  refine ⟨n • x - c, ?_, by linarith, by linarith⟩
  simp only [mem_preimage, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_nsmul,
    (QuotientAddGroup.eq_zero_iff _).2 hc, sub_zero]
  exact nsmul_mem hxs _

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
    have hp₀ : p ≠ 0 := by rintro rfl; simp at h
    apply dense_addSubmonoid_of_accPt_zero hp₀
    
    
    

end AddCircle
