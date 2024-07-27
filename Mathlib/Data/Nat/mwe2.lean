import Mathlib.LinearAlgebra.FiniteDimensional

open scoped Classical

universe u v

variable {V : Type v} {K : Type u} [Field K] [AddCommGroup V] [Module K V]

def submoduleMapThing {W₁ : Type*} [AddCommGroup W₁] [Module K W₁] {W₂ : Type*} [AddCommGroup W₂]
[Module K W₂] (f : W₁ →ₗ[K] W₂) (r : Submodule K W₁) :
  Submodule.map (LinearMap.domRestrict f r) ⊤ = Submodule.map f r := by
  refine (Submodule.ext ?h).symm
  intros X
  simp only [Submodule.mem_map, Submodule.map_top, LinearMap.mem_range, LinearMap.domRestrict_apply,
    Subtype.exists, exists_prop]

-- use linearequiv.ofinjective, it will give linear map if you use linear map as argument
noncomputable def isoThing'' (r : {X : Submodule K (V × K) | ¬ Submodule.map (LinearMap.inr K V K) ⊤ ≤ X}) :
  r ≃ₗ[K] Submodule.map (LinearMap.fst K V K) r := by
  have h2 := LinearEquiv.ofInjective ((LinearMap.fst K V K).domRestrict r.1) ?_
  rw [LinearMap.range_eq_map, submoduleMapThing (LinearMap.fst K V K) r] at h2
  apply h2

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
