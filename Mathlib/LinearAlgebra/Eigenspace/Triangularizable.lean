/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Triangularizable linear endomorphisms

This file contains basic results relevant to the triangularizability of linear endomorphisms.

## Main definitions / results

 * `Module.End.exists_eigenvalue`: in finite dimensions, over an algebraically closed field, every
   linear endomorphism has an eigenvalue.
 * `Module.End.iSup_genEigenspace_eq_top`: in finite dimensions, over an algebraically
   closed field, the generalized eigenspaces of any linear endomorphism span the whole space.
 * `Module.End.iSup_genEigenspace_restrict_eq_top`: in finite dimensions, if the
   generalized eigenspaces of a linear endomorphism span the whole space then the same is true of
   its restriction to any invariant submodule.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2015]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## TODO

Define triangularizable endomorphisms (e.g., as existence of a maximal chain of invariant subspaces)
and prove that in finite dimensions over a field, this is equivalent to the property that the
generalized eigenspaces span the whole space.

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/

open Set Function Module Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
   {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Module.End

theorem exists_hasEigenvalue_of_unifEigenspace_eq_top [Nontrivial M] {f : End R M} (k : ℕ∞)
    (hf : ⨆ μ, f.unifEigenspace μ k = ⊤) :
    ∃ μ, f.HasEigenvalue μ := by
  by_contra! contra
  suffices ∀ μ, f.unifEigenspace μ k = ⊥ by simp [this] at hf
  contrapose! contra
  peel contra with μ hμ
  exact HasUnifEigenvalue.lt zero_lt_one hμ

@[deprecated exists_hasEigenvalue_of_unifEigenspace_eq_top (since := "2024-10-11")]
theorem exists_hasEigenvalue_of_iSup_genEigenspace_eq_top [Nontrivial M] {f : End R M}
    (hf : ⨆ μ, ⨆ k, f.genEigenspace μ k = ⊤) :
    ∃ μ, f.HasEigenvalue μ := by
  simp_rw [← maxGenEigenspace_def] at hf
  apply exists_hasEigenvalue_of_unifEigenspace_eq_top _ hf

-- This is Lemma 5.21 of [axler2015], although we are no longer following that proof.
/-- In finite dimensions, over an algebraically closed field, every linear endomorphism has an
eigenvalue. -/
theorem exists_eigenvalue [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) :
    ∃ c : K, f.HasEigenvalue c := by
  simp_rw [hasEigenvalue_iff_mem_spectrum]
  exact spectrum.nonempty_of_isAlgClosed_of_finiteDimensional K f

noncomputable instance [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) :
    Inhabited f.Eigenvalues :=
  ⟨⟨f.exists_eigenvalue.choose, f.exists_eigenvalue.choose_spec⟩⟩

-- Lemma 8.21 of [axler2015]
/-- In finite dimensions, over an algebraically closed field, the generalized eigenspaces of any
linear endomorphism span the whole space. -/
theorem iSup_maxGenEigenspace_eq_top [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    ⨆ (μ : K), f.maxGenEigenspace μ = ⊤ := by
  -- We prove the claim by strong induction on the dimension of the vector space.
  induction' h_dim : finrank K V using Nat.strong_induction_on with n ih generalizing V
  cases' n with n
  -- If the vector space is 0-dimensional, the result is trivial.
  · rw [← top_le_iff]
    simp only [Submodule.finrank_eq_zero.1 (Eq.trans (finrank_top _ _) h_dim), bot_le]
  -- Otherwise the vector space is nontrivial.
  · haveI : Nontrivial V := finrank_pos_iff.1 (by rw [h_dim]; apply Nat.zero_lt_succ)
    -- Hence, `f` has an eigenvalue `μ₀`.
    obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀, f.HasEigenvalue μ₀ := exists_eigenvalue f
    -- We define `ES` to be the generalized eigenspace
    let ES := f.genEigenspace μ₀ (finrank K V)
    -- and `ER` to be the generalized eigenrange.
    let ER := f.genEigenrange μ₀ (finrank K V)
    -- `f` maps `ER` into itself.
    have h_f_ER : ∀ x : V, x ∈ ER → f x ∈ ER := fun x hx =>
      map_genEigenrange_le (Submodule.mem_map_of_mem hx)
    -- Therefore, we can define the restriction `f'` of `f` to `ER`.
    let f' : End K ER := f.restrict h_f_ER
    -- The dimension of `ES` is positive
    have h_dim_ES_pos : 0 < finrank K ES := by
      dsimp only [ES]
      rw [h_dim]
      apply pos_finrank_genEigenspace_of_hasEigenvalue hμ₀ (Nat.zero_lt_succ n)
    -- and the dimensions of `ES` and `ER` add up to `finrank K V`.
    have h_dim_add : finrank K ER + finrank K ES = finrank K V := by
      dsimp only [ER, ES]
      rw [Module.End.genEigenspace_def, Module.End.genEigenrange_def]
      apply LinearMap.finrank_range_add_finrank_ker
    -- Therefore the dimension `ER` mus be smaller than `finrank K V`.
    have h_dim_ER : finrank K ER < n.succ := by linarith
    -- This allows us to apply the induction hypothesis on `ER`:
    have ih_ER : ⨆ (μ : K), f'.maxGenEigenspace μ = ⊤ :=
      ih (finrank K ER) h_dim_ER f' rfl
    -- The induction hypothesis gives us a statement about subspaces of `ER`. We can transfer this
    -- to a statement about subspaces of `V` via `Submodule.subtype`:
    have ih_ER' : ⨆ (μ : K), (f'.maxGenEigenspace μ).map ER.subtype = ER := by
      simp only [(Submodule.map_iSup _ _).symm, ih_ER, Submodule.map_subtype_top ER]
    -- Moreover, every generalized eigenspace of `f'` is contained in the corresponding generalized
    -- eigenspace of `f`.
    have hff' :
      ∀ μ, (f'.maxGenEigenspace μ).map ER.subtype ≤ f.maxGenEigenspace μ := by
      intros
      rw [maxGenEigenspace, unifEigenspace_restrict]
      apply Submodule.map_comap_le
    -- It follows that `ER` is contained in the span of all generalized eigenvectors.
    have hER : ER ≤ ⨆ (μ : K), f.maxGenEigenspace μ := by
      rw [← ih_ER']
      exact iSup_mono hff'
    -- `ES` is contained in this span by definition.
    have hES : ES ≤ ⨆ (μ : K), f.maxGenEigenspace μ :=
      ((f.unifEigenspace μ₀).mono le_top).trans (le_iSup f.maxGenEigenspace μ₀)
    -- Moreover, we know that `ER` and `ES` are disjoint.
    have h_disjoint : Disjoint ER ES := generalized_eigenvec_disjoint_range_ker f μ₀
    -- Since the dimensions of `ER` and `ES` add up to the dimension of `V`, it follows that the
    -- span of all generalized eigenvectors is all of `V`.
    show ⨆ (μ : K), f.maxGenEigenspace μ = ⊤
    rw [← top_le_iff, ← Submodule.eq_top_of_disjoint ER ES h_dim_add h_disjoint]
    apply sup_le hER hES

-- Lemma 8.21 of [axler2015]
/-- In finite dimensions, over an algebraically closed field, the generalized eigenspaces of any
linear endomorphism span the whole space. -/
@[deprecated iSup_maxGenEigenspace_eq_top (since := "2024-10-11")]
theorem iSup_genEigenspace_eq_top [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    ⨆ (μ : K) (k : ℕ), f.genEigenspace μ k = ⊤ := by
  simp_rw [← maxGenEigenspace_def]
  apply iSup_maxGenEigenspace_eq_top

end Module.End

namespace Submodule

variable {p : Submodule K V} {f : Module.End K V}

-- move this
theorem _root_.Finset.supIndep_antimono_fun {α ι : Type*} [Lattice α] [OrderBot α] {s : Finset ι}
    {f g : ι → α} (h : ∀ x ∈ s, f x ≤ g x) (h : s.SupIndep g) : s.SupIndep f := by
  classical
  induction s using Finset.induction_on
  case empty => apply Finset.supIndep_empty
  case insert i s his IH hle =>
  rw [Finset.supIndep_iff_disjoint_erase] at h ⊢
  intro j hj
  simp_all only [Finset.mem_insert, or_true, implies_true, true_implies, forall_eq_or_imp,
    Finset.erase_insert_eq_erase, not_false_eq_true, Finset.erase_eq_of_not_mem]
  obtain rfl | hj := hj
  · simp only [Finset.erase_insert_eq_erase]
    apply h.left.mono hle.left
    apply (Finset.sup_mono _).trans (Finset.sup_mono_fun hle.right)
    apply Finset.erase_subset
  · apply (h.right j hj).mono (hle.right j hj) (Finset.sup_mono_fun _)
    intro k hk
    simp_all only [Finset.mem_erase, ne_eq, Finset.mem_insert]
    obtain ⟨-, rfl | hk⟩ := hk
    · exact hle.left
    · exact hle.right k hk

theorem inf_iSup_unifEigenspace [FiniteDimensional K V] (h : ∀ x ∈ p, f x ∈ p) (k : ℕ∞) :
    p ⊓ ⨆ μ, f.unifEigenspace μ k = ⨆ μ, p ⊓ f.unifEigenspace μ k := by
  refine le_antisymm (fun m hm ↦ ?_)
    (le_inf_iff.mpr ⟨iSup_le fun μ ↦ inf_le_left, iSup_mono fun μ ↦ inf_le_right⟩)
  classical
  obtain ⟨hm₀ : m ∈ p, hm₁ : m ∈ ⨆ μ, f.unifEigenspace μ k⟩ := hm
  obtain ⟨m, hm₂, rfl⟩ := (mem_iSup_iff_exists_finsupp _ _).mp hm₁
  suffices ∀ μ, (m μ : V) ∈ p by
    exact (mem_iSup_iff_exists_finsupp _ _).mpr ⟨m, fun μ ↦ mem_inf.mp ⟨this μ, hm₂ μ⟩, rfl⟩
  intro μ
  by_cases hμ : μ ∈ m.support; swap
  · simp only [Finsupp.not_mem_support_iff.mp hμ, p.zero_mem]
  have hm₂_aux := hm₂
  simp_rw [Module.End.mem_unifEigenspace] at hm₂_aux
  choose l hlk hl using hm₂_aux
  let l₀ : ℕ := m.support.sup l
  have h_comm : ∀ (μ₁ μ₂ : K),
    Commute ((f - algebraMap K (End K V) μ₁) ^ l₀)
            ((f - algebraMap K (End K V) μ₂) ^ l₀) := fun μ₁ μ₂ ↦
    ((Commute.sub_right rfl <| Algebra.commute_algebraMap_right _ _).sub_left
      (Algebra.commute_algebraMap_left _ _)).pow_pow _ _
  let g : End K V := (m.support.erase μ).noncommProd _ fun μ₁ _ μ₂ _ _ ↦ h_comm μ₁ μ₂
  have hfg : Commute f g := Finset.noncommProd_commute _ _ _ _ fun μ' _ ↦
    (Commute.sub_right rfl <| Algebra.commute_algebraMap_right _ _).pow_right _
  have hg₀ : g (m.sum fun _μ mμ ↦ mμ) = g (m μ) := by
    suffices ∀ μ' ∈ m.support, g (m μ') = if μ' = μ then g (m μ) else 0 by
      rw [map_finsupp_sum, Finsupp.sum_congr (g2 := fun μ' _ ↦ if μ' = μ then g (m μ) else 0) this,
        Finsupp.sum_ite_eq', if_pos hμ]
    rintro μ' hμ'
    split_ifs with hμμ'
    · rw [hμμ']
    have hl₀ : ((f - algebraMap K (End K V) μ') ^ l₀) (m μ') = 0 := by
      rw [← LinearMap.mem_ker, Algebra.algebraMap_eq_smul_one, ← End.mem_unifEigenspace_nat]
      simp_rw [← End.mem_unifEigenspace_nat] at hl
      suffices (l μ' : ℕ∞) ≤ l₀ by exact (f.unifEigenspace μ').mono this (hl μ')
      simpa only [Nat.cast_le] using Finset.le_sup hμ'
    have : _ = g := (m.support.erase μ).noncommProd_erase_mul (Finset.mem_erase.mpr ⟨hμμ', hμ'⟩)
      (fun μ ↦ (f - algebraMap K (End K V) μ) ^ l₀) (fun μ₁ _ μ₂ _ _ ↦ h_comm μ₁ μ₂)
    rw [← this, LinearMap.mul_apply, hl₀, _root_.map_zero]
  have hg₁ : MapsTo g p p := Finset.noncommProd_induction _ _ _ (fun g' : End K V ↦ MapsTo g' p p)
      (fun f₁ f₂ ↦ MapsTo.comp) (mapsTo_id _) fun μ' _ ↦ by
    suffices MapsTo (f - algebraMap K (End K V) μ') p p by
      simp only [LinearMap.coe_pow]; exact this.iterate l₀
    intro x hx
    rw [LinearMap.sub_apply, algebraMap_end_apply]
    exact p.sub_mem (h _ hx) (smul_mem p μ' hx)
  have hg₂ : MapsTo g ↑(f.unifEigenspace μ k) ↑(f.unifEigenspace μ k) :=
    f.mapsTo_unifEigenspace_of_comm hfg μ k
  have hg₃ : InjOn g ↑(f.unifEigenspace μ k) := by
    apply LinearMap.injOn_of_disjoint_ker (subset_refl _)
    have this := f.independent_unifEigenspace k
    have aux (μ') (_hμ' : μ' ∈ m.support.erase μ) :
        (f.unifEigenspace μ') ↑l₀ ≤ (f.unifEigenspace μ') k := by
      apply (f.unifEigenspace μ').mono
      rintro k rfl
      simp only [ENat.some_eq_coe, Nat.cast_inj, exists_eq_left']
      apply Finset.sup_le
      intro i _hi
      simpa using hlk i
    -- simp_rw [f.maxGenEigenspace_eq_genEigenspace_finrank] at this ⊢
    rw [LinearMap.ker_noncommProd_eq_of_supIndep_ker, ← Finset.sup_eq_iSup]
    · have := Finset.supIndep_iff_disjoint_erase.mp (this.supIndep' m.support) μ hμ
      apply this.mono_right
      apply Finset.sup_mono_fun
      intro μ' hμ'
      rw [Algebra.algebraMap_eq_smul_one, ← End.unifEigenspace_nat]
      apply aux μ' hμ'
    · have := this.supIndep' (m.support.erase μ)
      apply Finset.supIndep_antimono_fun _ this
      intro μ' hμ'
      rw [Algebra.algebraMap_eq_smul_one, ← End.unifEigenspace_nat]
      apply aux μ' hμ'
  have hg₄ : SurjOn g
      ↑(p ⊓ f.unifEigenspace μ k) ↑(p ⊓ f.unifEigenspace μ k) := by
    have : MapsTo g
        ↑(p ⊓ f.unifEigenspace μ k) ↑(p ⊓ f.unifEigenspace μ k) :=
      hg₁.inter_inter hg₂
    rw [← LinearMap.injOn_iff_surjOn this]
    exact hg₃.mono inter_subset_right
  specialize hm₂ μ
  obtain ⟨y, ⟨hy₀ : y ∈ p, hy₁ : y ∈ f.unifEigenspace μ k⟩, hy₂ : g y = g (m μ)⟩ :=
    hg₄ ⟨(hg₀ ▸ hg₁ hm₀), hg₂ hm₂⟩
  rwa [← hg₃ hy₁ hm₂ hy₂]

theorem inf_iSup_genEigenspace [FiniteDimensional K V] (h : ∀ x ∈ p, f x ∈ p) :
    p ⊓ ⨆ μ, ⨆ k, f.genEigenspace μ k = ⨆ μ, ⨆ k, p ⊓ f.genEigenspace μ k := by
  simp_rw [← (f.genEigenspace _).mono.directed_le.inf_iSup_eq]
  refine le_antisymm (fun m hm ↦ ?_)
    (le_inf_iff.mpr ⟨iSup_le fun μ ↦ inf_le_left, iSup_mono fun μ ↦ inf_le_right⟩)
  classical
  obtain ⟨hm₀ : m ∈ p, hm₁ : m ∈ ⨆ μ, ⨆ k, f.genEigenspace μ k⟩ := hm
  obtain ⟨m, hm₂, rfl⟩ := (mem_iSup_iff_exists_finsupp _ _).mp hm₁
  suffices ∀ μ, (m μ : V) ∈ p by
    exact (mem_iSup_iff_exists_finsupp _ _).mpr ⟨m, fun μ ↦ mem_inf.mp ⟨this μ, hm₂ μ⟩, rfl⟩
  intro μ
  by_cases hμ : μ ∈ m.support; swap
  · simp only [Finsupp.not_mem_support_iff.mp hμ, p.zero_mem]
  have h_comm : ∀ (μ₁ μ₂ : K),
    Commute ((f - algebraMap K (End K V) μ₁) ^ finrank K V)
            ((f - algebraMap K (End K V) μ₂) ^ finrank K V) := fun μ₁ μ₂ ↦
    ((Commute.sub_right rfl <| Algebra.commute_algebraMap_right _ _).sub_left
      (Algebra.commute_algebraMap_left _ _)).pow_pow _ _
  let g : End K V := (m.support.erase μ).noncommProd _ fun μ₁ _ μ₂ _ _ ↦ h_comm μ₁ μ₂
  have hfg : Commute f g := Finset.noncommProd_commute _ _ _ _ fun μ' _ ↦
    (Commute.sub_right rfl <| Algebra.commute_algebraMap_right _ _).pow_right _
  have hg₀ : g (m.sum fun _μ mμ ↦ mμ) = g (m μ) := by
    suffices ∀ μ' ∈ m.support, g (m μ') = if μ' = μ then g (m μ) else 0 by
      rw [map_finsupp_sum, Finsupp.sum_congr (g2 := fun μ' _ ↦ if μ' = μ then g (m μ) else 0) this,
        Finsupp.sum_ite_eq', if_pos hμ]
    rintro μ' hμ'
    split_ifs with hμμ'
    · rw [hμμ']
    replace hm₂ : ((f - algebraMap K (End K V) μ') ^ finrank K V) (m μ') = 0 := by
      obtain ⟨k, hk⟩ := (mem_iSup_of_chain _ _).mp (hm₂ μ')
      simpa only [End.mem_genEigenspace] using
        Module.End.genEigenspace_le_genEigenspace_finrank _ _ k hk
    have : _ = g := (m.support.erase μ).noncommProd_erase_mul (Finset.mem_erase.mpr ⟨hμμ', hμ'⟩)
      (fun μ ↦ (f - algebraMap K (End K V) μ) ^ finrank K V) (fun μ₁ _ μ₂ _ _ ↦ h_comm μ₁ μ₂)
    rw [← this, LinearMap.mul_apply, hm₂, _root_.map_zero]
  have hg₁ : MapsTo g p p := Finset.noncommProd_induction _ _ _ (fun g' : End K V ↦ MapsTo g' p p)
      (fun f₁ f₂ ↦ MapsTo.comp) (mapsTo_id _) fun μ' _ ↦ by
    suffices MapsTo (f - algebraMap K (End K V) μ') p p by
      simp only [LinearMap.coe_pow]; exact this.iterate (finrank K V)
    intro x hx
    rw [LinearMap.sub_apply, algebraMap_end_apply]
    exact p.sub_mem (h _ hx) (smul_mem p μ' hx)
  have hg₂ : MapsTo g ↑(⨆ k, f.genEigenspace μ k) ↑(⨆ k, f.genEigenspace μ k) :=
    f.mapsTo_iSup_genEigenspace_of_comm hfg μ
  have hg₃ : InjOn g ↑(⨆ k, f.genEigenspace μ k) := by
    apply LinearMap.injOn_of_disjoint_ker (subset_refl _)
    have this := f.independent_genEigenspace
    simp_rw [f.iSup_genEigenspace_eq_genEigenspace_finrank] at this ⊢
    rw [LinearMap.ker_noncommProd_eq_of_supIndep_ker, ← Finset.sup_eq_iSup]
    · simpa only [End.genEigenspace_def] using
        Finset.supIndep_iff_disjoint_erase.mp (this.supIndep' m.support) μ hμ
    · simpa only [End.genEigenspace_def] using this.supIndep' (m.support.erase μ)
  have hg₄ : SurjOn g
      ↑(p ⊓ ⨆ k, f.genEigenspace μ k) ↑(p ⊓ ⨆ k, f.genEigenspace μ k) := by
    have : MapsTo g
        ↑(p ⊓ ⨆ k, f.genEigenspace μ k) ↑(p ⊓ ⨆ k, f.genEigenspace μ k) :=
      hg₁.inter_inter hg₂
    rw [← LinearMap.injOn_iff_surjOn this]
    exact hg₃.mono inter_subset_right
  specialize hm₂ μ
  obtain ⟨y, ⟨hy₀ : y ∈ p, hy₁ : y ∈ ⨆ k, f.genEigenspace μ k⟩, hy₂ : g y = g (m μ)⟩ :=
    hg₄ ⟨(hg₀ ▸ hg₁ hm₀), hg₂ hm₂⟩
  rwa [← hg₃ hy₁ hm₂ hy₂]

theorem eq_iSup_inf_unifEigenspace [FiniteDimensional K V] (k : ℕ∞)
    (h : ∀ x ∈ p, f x ∈ p) (h' : ⨆ μ, f.unifEigenspace μ k = ⊤) :
    p = ⨆ μ, p ⊓ f.unifEigenspace μ k := by
  rw [← inf_iSup_genEigenspace h, h', inf_top_eq]

theorem eq_iSup_inf_genEigenspace [FiniteDimensional K V]
    (h : ∀ x ∈ p, f x ∈ p) (h' : ⨆ μ, ⨆ k, f.genEigenspace μ k = ⊤) :
    p = ⨆ μ, ⨆ k, p ⊓ f.genEigenspace μ k := by
  rw [← inf_iSup_genEigenspace h, h', inf_top_eq]

end Submodule

/-- In finite dimensions, if the generalized eigenspaces of a linear endomorphism span the whole
space then the same is true of its restriction to any invariant submodule. -/
theorem Module.End.unifEigenspace_restrict_eq_top
    {p : Submodule K V} {f : Module.End K V} [FiniteDimensional K V] {k : ℕ∞}
    (h : ∀ x ∈ p, f x ∈ p) (h' : ⨆ μ, f.unifEigenspace μ k = ⊤) :
    ⨆ μ, Module.End.unifEigenspace (LinearMap.restrict f h) μ k = ⊤ := by
  have := congr_arg (Submodule.comap p.subtype) (Submodule.eq_iSup_inf_genEigenspace h h')
  have h_inj : Function.Injective p.subtype := Subtype.coe_injective
  simp_rw [Submodule.inf_genEigenspace f p h, Submodule.comap_subtype_self,
    ← Submodule.map_iSup, Submodule.comap_map_eq_of_injective h_inj] at this
  exact this.symm

/-- In finite dimensions, if the generalized eigenspaces of a linear endomorphism span the whole
space then the same is true of its restriction to any invariant submodule. -/
theorem Module.End.iSup_genEigenspace_restrict_eq_top
    {p : Submodule K V} {f : Module.End K V} [FiniteDimensional K V]
    (h : ∀ x ∈ p, f x ∈ p) (h' : ⨆ μ, ⨆ k, f.genEigenspace μ k = ⊤) :
    ⨆ μ, ⨆ k, Module.End.genEigenspace (LinearMap.restrict f h) μ k = ⊤ := by
  have := congr_arg (Submodule.comap p.subtype) (Submodule.eq_iSup_inf_genEigenspace h h')
  have h_inj : Function.Injective p.subtype := Subtype.coe_injective
  simp_rw [Submodule.inf_genEigenspace f p h, Submodule.comap_subtype_self,
    ← Submodule.map_iSup, Submodule.comap_map_eq_of_injective h_inj] at this
  exact this.symm
