/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.JacobsonIdeal

/-!
# Further theory of Jacobson radicals of modules and rings

This file connects Jacobson radicals to finiteness conditions.

We show that an Artinian module is semisimple iff its Jacobson radical is zero.

Show that an Artinian ring `R` is semi-primary, i.e. `Ring.jacobson R` is nilpotent and
`R ⧸ Ring.jacobson R` is semisimple.

In particular, we prove the Hopkins–Levitzki theorem which says that for a module over a
semi-primary ring (in particular, an Artinian ring), `Module.Finite`, `IsNoetherian`,
`IsArtinian` and `IsFiniteLength` are all equivalent. In particular, a (left) Artinian ring
is also (left) Noetherian.
-/

variable (R R₂ M M₂ : Type*) [Ring R] [Ring R₂]
variable [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂] (f : F)

theorem IsSimpleModule.jacobson_eq_bot [IsSimpleModule R M] : Module.jacobson R M = ⊥ :=
  le_bot_iff.mp <| sInf_le isCoatom_bot

theorem IsSemisimpleModule.jacobson_eq_bot [IsSemisimpleModule R M] :
    Module.jacobson R M = ⊥ := by
  _

theorem IsSemisimpleModule.jacobson_le_ker [IsSemisimpleModule R₂ M₂] :
    Module.jacobson R M ≤ LinearMap.ker f :=
  (Module.le_comap_jacobson f).trans <| by simp_rw [jacobson_eq_bot, LinearMap.ker, le_rfl]

/-- The Jacobson radical of a ring annihilates every semisimple module. -/
theorem IsSemisimpleModule.jacobson_le_annihilator [IsSemisimpleModule R M] :
    Ring.jacobson R ≤ Module.annihilator R M :=
  fun r hr ↦ Module.mem_annihilator.mpr fun m ↦ by
    have := Module.le_comap_jacobson (LinearMap.toSpanSingleton R M m) hr
    rwa [jacobson_eq_bot] at this

theorem IsArtinian.isSemisimpleModule_iff_jacobson [IsArtinian R M] :
    IsSemisimpleModule R M ↔ Module.jacobson R M = ⊥ :=
  ⟨fun _ ↦ IsSemisimpleModule.jacobson_eq_bot R M, fun h ↦
    have ⟨s, hs⟩ := Finset.exists_inf_le (Subtype.val (p := fun m : Submodule R M ↦ IsCoatom m))
    have _ (m : s) : IsSimpleModule R (M ⧸ m.1.1) := isSimpleModule_iff_isCoatom.mpr m.1.2
    let f : M →ₗ[R] ∀ m : s, M ⧸ m.1.1 := LinearMap.pi fun m ↦ m.1.1.mkQ
    .of_injective f <| LinearMap.ker_eq_bot.mp <| le_bot_iff.mp fun x hx ↦ by
      rw [← h, Module.jacobson, Submodule.mem_sInf]
      exact fun m hm ↦ hs ⟨m, hm⟩ <| Submodule.mem_finset_inf.mpr fun i hi ↦
        (Submodule.Quotient.mk_eq_zero i.1).mp <| congr_fun hx ⟨i, hi⟩⟩

theorem IsArtinianRing.isSemisimpleRing_iff_jacobson [IsArtinianRing R] :
    IsSemisimpleRing R ↔ Ring.jacobson R = ⊥ :=
  IsArtinian.isSemisimpleModule_iff_jacobson R R

class IsSemiPrimaryRing : Prop where
  isSemisimpleRing : IsSemisimpleRing (R ⧸ Ring.jacobson R)
  isNilpotent : IsNilpotent (Ring.jacobson R)

attribute [instance] IsSemiPrimaryRing.isSemisimpleRing

instance [IsArtinianRing R] : IsSemiPrimaryRing R where
  isSemisimpleRing :=
    (IsArtinianRing.isSemisimpleRing_iff_jacobson _).mpr (Ring.jacobson_quotient_jacobson R)
  isNilpotent := by
    let I := Ring.jacobson R
    have ⟨n, hn⟩ := IsArtinian.monotone_stabilizes ⟨(I ^ ·), @Ideal.pow_le_pow_right _ _ _⟩
    use n; by_contra ne
    have : I ^ (n + 1) = I ^ n := (hn _ n.le_succ).symm
    have hn : I * I ^ n = I ^ n := by
      obtain rfl | hn := eq_or_ne n 0
      · simp_rw [I.pow_zero, zero_add, I.pow_one] at this ⊢
        rw [this, Submodule.one_mul]
      · rwa [I.pow_succ' hn] at this
    have ⟨N, ⟨eq, ne⟩, min⟩ := wellFounded_lt.has_min {N | I * N = N ∧ N ≠ ⊥} ⟨_, hn, ne⟩
    have : I ^ n * N = N := n.rec (by rw [I.pow_zero, N.one_mul])
      fun n hn ↦ by rwa [I.pow_succ, mul_assoc, eq]
    let In x := Submodule.map (LinearMap.toSpanSingleton R R x) (I ^ n)
    have hIn x : In x ≤ Ideal.span {x} := by
      rw [Ideal.span, LinearMap.span_singleton_eq_range]; exact LinearMap.map_le_range
    have ⟨x, hx⟩ : ∃ x ∈ N, In x ≠ ⊥ := by
      contrapose! ne
      rw [← this, ← le_bot_iff, Ideal.mul_le]
      refine fun ri hi rn hn ↦ ?_
      rw [← ne rn hn]
      exact ⟨ri, hi, rfl⟩
    rw [← Ideal.span_singleton_le_iff_mem] at hx
    have : In x = N := by
      refine ((hIn x).trans hx.1).eq_of_not_lt (min _ ⟨?_, hx.2⟩)
      rw [← smul_eq_mul, ← Submodule.map_smul'', smul_eq_mul, hn]
    have : Ideal.span {x} = N := le_antisymm hx.1 (this.symm.trans_le <| hIn x)
    refine (this ▸ ne) ((Submodule.fg_span <| Set.finite_singleton x).eq_bot_of_le_jacobson_smul ?_)
    rw [← Ideal.span, this, smul_eq_mul, eq]

theorem IsArtinianRing.isNilpotent_jacobson [IsArtinianRing R] : IsNilpotent (Ring.jacobson R) := by
  _
