import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortExact.Preadditive
import Mathlib.LinearAlgebra.FreeModule.Basic

namespace ModuleCat

variable {I : Type _} {J : Type _} {R : Type _} [Ring R] {N P : ModuleCat R} {v : I → N}-- {w : J → P}

open CategoryTheory

section LinearIndependent

variable (hv : LinearIndependent R v)  {M : ModuleCat R}
  {u : I ⊕ J → M}  {f : N ⟶ M} {g : M ⟶ P}
  (hw : LinearIndependent R (g ∘ u ∘ Sum.inr)) (hu : Function.Injective u)
  (hm : Mono f) (he : Exact f g) (huv : u ∘ Sum.inl = f ∘ v)

lemma disjoint_span_aux : Disjoint (Submodule.span R (Set.range f))
    (Submodule.span R (Set.range (u ∘ Sum.inr))) := by
  rw [← LinearMap.range_coe, (Submodule.span_eq (LinearMap.range f)), (exact_iff _ _).mp he]
  exact Submodule.ker_range_disjoint (Function.Injective.comp hu Sum.inr_injective) hw

lemma disjoint_span : Disjoint (Submodule.span R (Set.range (u ∘ Sum.inl)))
    (Submodule.span R (Set.range (u ∘ Sum.inr))) := by
  rw [huv]
  exact Disjoint.mono_left (Submodule.span_mono (Set.range_comp_subset_range _ _))
    (disjoint_span_aux hw hu he)

theorem linearIndependent_leftExact : LinearIndependent R u :=
  linearIndependent_sum.mpr
  ⟨(congr_arg (fun f ↦ LinearIndependent R f) huv).mpr
    ((LinearMap.linearIndependent_iff (f : N →ₗ[R] M)
    (LinearMap.ker_eq_bot.mpr ((mono_iff_injective _).mp hm))).mpr hv),
    LinearIndependent.of_comp g hw, disjoint_span hw hu he huv⟩

end LinearIndependent

section Span

variable {M : ModuleCat R} {u : I ⊕ J → M} {f : N ⟶ M} {g : M ⟶ P}

theorem span_exact (he : Exact f g) (huv : u ∘ Sum.inl = f ∘ v)
    (huw : g ∘ u ∘ Sum.inr = w) (hv : ⊤ ≤ Submodule.span R (Set.range v))
    (hw : ⊤ ≤ Submodule.span R (Set.range w)) : ⊤ ≤ Submodule.span R (Set.range u) := by
  intro m _
  have hgm : g m ∈ Submodule.span R (Set.range w) := hw Submodule.mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hgm
  obtain ⟨cm, hm⟩ := hgm
  rw [← huw] at hm
  set m' : M := Finsupp.sum cm fun j a ↦ a • (u (Sum.inr j)) with hm'
  have hsub : m - m' ∈ LinearMap.range f
  · rw [(exact_iff _ _).mp he]
    simp only [LinearMap.mem_ker, map_sub, sub_eq_zero]
    rw [← hm, map_finsupp_sum]
    simp only [Function.comp_apply, map_smul]
  obtain ⟨n, hnm⟩ := hsub
  have hn : n ∈ Submodule.span R (Set.range v) := hv Submodule.mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn
  obtain ⟨cn, hn⟩ := hn
  rw [← hn, map_finsupp_sum] at hnm
  have hmmm : m = m - m' + m'
  · simp only [sub_add_cancel]
  rw [hmmm, ← hnm, hm']
  simp only [map_smul]
  have hn' : (Finsupp.sum cn fun a b ↦ b • f (v a)) = (Finsupp.sum cn fun a b ↦ b • u (Sum.inl a))
  · congr
    ext a _
    rw [(by rfl : f (v a) = (f ∘ v) a), ← huv]
    rfl
  rw [hn']
  apply Submodule.add_mem
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cn.mapDomain (Sum.inl)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inl_injective]
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cm.mapDomain (Sum.inr)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inr_injective]

end Span

theorem free_shortExact {M : ModuleCat R} {f : (ModuleCat.free R).obj I ⟶ M}
  {g : M ⟶ (ModuleCat.free R).obj} (h : ShortExact f g) : Module.Free R M := sorry

end ModuleCat
