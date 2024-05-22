import Mathlib.LinearAlgebra.FiniteDimensional

open scoped Classical

universe u v

variable {V : Type v} {K : Type u} [Field K] [AddCommGroup V] [Module K V]

noncomputable def isoThing (r : {X : Submodule K (V × K) | ¬ Submodule.map (LinearMap.inr K V K) ⊤ ≤ X}) :
  r ≃ₗ[K] Submodule.map (LinearMap.fst K V K) r := by
  apply Equiv.toLinearEquiv (Equiv.ofBijective ((LinearMap.fst K V K).restrict (λ x (hx : x ∈ r.1) =>
    Submodule.mem_map_of_mem hx)) ⟨?_, ?_⟩)
  apply IsLinearMap.mk (λ x y => rfl) (λ c x => rfl)
  intros x y hxy
  by_contra hxy2
  simp [LinearMap.restrict_apply] at hxy
  have h2 : x.1.2 ≠ y.1.2 := by
    by_contra hxy3
    apply hxy2 (Subtype.val_inj.1 (Prod.eq_iff_fst_eq_snd_eq.2 ⟨hxy, hxy3⟩))
  apply r.2
  intros z hz
  simp only [Submodule.map_top, LinearMap.mem_range, LinearMap.coe_inr] at hz
  obtain ⟨a, rfl⟩ := hz
  have h3 : ⟨0, x.1.2 - y.1.2⟩ ∈ r.1 := by
    rw [← sub_self (y.1.1)]
    nth_rewrite 1 [← hxy]
    rw [← Prod.mk_sub_mk]
    apply Submodule.sub_mem _ x.2 y.2
  rw [← sub_ne_zero] at h2
  have h4 := Submodule.smul_mem r (x.1.2 - y.1.2)⁻¹ h3
  simp at h4
  rw [inv_mul_cancel h2] at h4
  have h5 := Submodule.smul_mem r a h4
  simp at h5
  apply h5
  intros b
  obtain ⟨y, hy⟩ := (Submodule.mem_map.1 b.2)
  refine ⟨⟨y, hy.1⟩, ?_⟩
  rw [LinearMap.restrict_apply (λ x (hx : x ∈ r.1) => Submodule.mem_map_of_mem hx) ⟨y, hy.1⟩]
  simp
  simp at hy
  simp [hy.2]
