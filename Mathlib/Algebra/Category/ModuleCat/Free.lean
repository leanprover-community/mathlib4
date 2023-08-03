import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
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

def family_shortExact [Nontrivial R] {w : J → P} (hE : Epi g) (hw : LinearIndependent R w) :
    Function.Injective (Sum.elim (f ∘ v) (g.toFun.invFun ∘ w)) := by
  apply Function.Injective.sum_elim
  · rw [mono_iff_injective] at hm
    exact Function.Injective.comp hm hv.injective
  · rw [epi_iff_surjective] at hE
    exact Function.Injective.comp (Function.rightInverse_invFun hE).injective hw.injective
  · intro a b h
    apply_fun g at h
    rw [epi_iff_surjective] at hE
    dsimp at h
    rw [Function.rightInverse_invFun hE] at h
    have : g (f (v a)) = (f ≫ g) (v a) := rfl
    rw [this, he.w] at h
    sorry

theorem linearIndependent_shortExact [Nontrivial R] {w : J → P} (hse : ShortExact f g)
    (hw : LinearIndependent R w) :
    LinearIndependent R (Sum.elim (f ∘ v) (g.toFun.invFun ∘ w)) := by
  refine' linearIndependent_leftExact hv _ (family_shortExact hv hse.mono hse.epi hw)
      hse.mono hse.exact _
  · simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inr]
    have hg := hse.epi
    rw [ModuleCat.epi_iff_surjective] at hg
    rwa [← Function.comp.assoc, Function.RightInverse.comp_eq_id (Function.rightInverse_invFun hg),
      Function.comp.left_id]
  · simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inl]

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

-- def map_of_shortExact {M : ModuleCat R} {f : N ⟶ M}
--     {g : M ⟶ P} (h : ShortExact f g) (hN : Module.Free R N) (hP : Module.Free R P) :

-- #exit

theorem free_shortExact' {M : ModuleCat R} {f : N ⟶ M}
    {g : M ⟶ P} (h : ShortExact f g) (hN : Module.Free R N) (hP : Module.Free R P) :
    Module.Free R M := by
  let ginv : P → M := g.toFun.invFun
  obtain ⟨I, hI⟩ := hN
  have hlI := hI.linearIndependent
  have hsI := le_of_eq hI.span_eq.symm
  obtain ⟨J, hJ⟩ := hP
  have hlJ := hJ.linearIndependent
  have hsJ := le_of_eq hJ.span_eq.symm
  refine' @Module.Free.of_basis _ _ _ _ _ (I ⊕ J) _
  refine' Basis.mk _ _
  · exact Sum.elim (f ∘ hI) (ginv ∘ hJ)
  · sorry
  · sorry

end ModuleCat
