/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Simultaneous eigenvectors and eigenvalues for families of endomorphisms

In finite dimensions, the theory of simultaneous eigenvalues for a family of linear endomorphisms
`i ↦ f i` enjoys similar properties to that of a single endomorphism, provided the family obeys a
compatibility condition. This condition is that the maximum generalised eigenspaces of each
endomorphism are invariant under the action of all members of the family. It is trivially satisfied
for commuting endomorphisms but there are important more general situations where it also holds
(e.g., representations of nilpotent Lie algebras).

## Main definitions / results
* `Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo`: the simultaneous generalised
  eigenspaces of a compatible family of endomorphisms are independent.
* `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo`: in finite dimensions, the
  simultaneous generalised eigenspaces of a compatible family of endomorphisms span if the same
  is true of each map individually.

-/

open Function Set

namespace Module.End

variable {ι R K M : Type*} [CommRing R] [Field K] [AddCommGroup M] [Module R M] [Module K M]
  (f : ι → End R M)

theorem mem_iInf_maxGenEigenspace_iff (χ : ι → R) (m : M) :
    m ∈ ⨅ i, (f i).maxGenEigenspace (χ i) ↔ ∀ j, ∃ k : ℕ, ((f j - χ j • ↑1) ^ k) m = 0 := by
  simp

/-- Given a family of endomorphisms `i ↦ f i`, a family of candidate eigenvalues `i ↦ μ i`, and a
submodule `p` which is invariant wrt every `f i`, the intersection of `p` with the simultaneous
maximal generalised eigenspace (taken over all `i`), is the same as the simultaneous maximal
generalised eigenspace of the `f i` restricted to `p`. -/
lemma _root_.Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo {μ : ι → R}
    (p : Submodule R M) (hfp : ∀ i, MapsTo (f i) p p) :
    p ⊓ ⨅ i, (f i).maxGenEigenspace (μ i) =
      (⨅ i, maxGenEigenspace ((f i).restrict (hfp i)) (μ i)).map p.subtype := by
  cases isEmpty_or_nonempty ι
  · simp [iInf_of_isEmpty]
  · simp_rw [inf_iInf, p.inf_genEigenspace _ (hfp _), Submodule.map_iInf _ p.injective_subtype]

/-- Given a family of endomorphisms `i ↦ f i`, a family of candidate eigenvalues `i ↦ μ i`, and a
distinguished index `i` whose maximal generalised `μ i`-eigenspace is invariant wrt every `f j`,
taking simultaneous maximal generalised eigenspaces is unaffected by first restricting to the
distinguished generalised `μ i`-eigenspace. -/
lemma iInf_maxGenEigenspace_restrict_map_subtype_eq
    {μ : ι → R} (i : ι)
    (h : ∀ j, MapsTo (f j) ((f i).maxGenEigenspace (μ i)) ((f i).maxGenEigenspace (μ i))) :
    letI p := (f i).maxGenEigenspace (μ i)
    letI q (j : ι) := maxGenEigenspace ((f j).restrict (h j)) (μ j)
    (⨅ j, q j).map p.subtype = ⨅ j, (f j).maxGenEigenspace (μ j) := by
  have : Nonempty ι := ⟨i⟩
  set p := (f i).maxGenEigenspace (μ i)
  have : ⨅ j, (f j).maxGenEigenspace (μ j) = p ⊓ ⨅ j, (f j).maxGenEigenspace (μ j) := by
    refine le_antisymm ?_ inf_le_right
    simpa only [le_inf_iff, le_refl, and_true] using iInf_le _ _
  rw [Submodule.map_iInf _ p.injective_subtype, this, Submodule.inf_iInf]
  conv_rhs =>
    enter [1]
    ext
    rw [p.inf_genEigenspace (f _) (h _)]

variable [NoZeroSMulDivisors R M]

lemma disjoint_iInf_maxGenEigenspace {χ₁ χ₂ : ι → R} (h : χ₁ ≠ χ₂) :
    Disjoint (⨅ i, (f i).maxGenEigenspace (χ₁ i)) (⨅ i, (f i).maxGenEigenspace (χ₂ i)) := by
  obtain ⟨j, hj⟩ : ∃ j, χ₁ j ≠ χ₂ j := Function.ne_iff.mp h
  exact (End.disjoint_genEigenspace (f j) hj ⊤ ⊤).mono (iInf_le _ j) (iInf_le _ j)

lemma injOn_iInf_maxGenEigenspace :
    InjOn (fun χ : ι → R ↦ ⨅ i, (f i).maxGenEigenspace (χ i))
      {χ | ⨅ i, (f i).maxGenEigenspace (χ i) ≠ ⊥} := by
  rintro χ₁ _ χ₂
    hχ₂ (hχ₁₂ : ⨅ i, (f i).maxGenEigenspace (χ₁ i) = ⨅ i, (f i).maxGenEigenspace (χ₂ i))
  contrapose! hχ₂
  simpa [hχ₁₂] using disjoint_iInf_maxGenEigenspace f hχ₂

lemma independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (h : ∀ i j φ, MapsTo (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigenspace φ)) :
    iSupIndep fun χ : ι → R ↦ ⨅ i, (f i).maxGenEigenspace (χ i) := by
  replace h (l : ι) (χ : ι → R) :
      MapsTo (f l) (⨅ i, (f i).maxGenEigenspace (χ i)) (⨅ i, (f i).maxGenEigenspace (χ i)) := by
    intro x hx
    simp only [iInf_eq_iInter, mem_iInter, SetLike.mem_coe] at hx ⊢
    exact fun i ↦ h l i (χ i) (hx i)
  classical
  suffices ∀ χ (s : Finset (ι → R)) (_ : χ ∉ s),
      Disjoint (⨅ i, (f i).maxGenEigenspace (χ i))
        (s.sup fun (χ : ι → R) ↦ ⨅ i, (f i).maxGenEigenspace (χ i)) by
    simpa only [iSupIndep_iff_supIndep_of_injOn (injOn_iInf_maxGenEigenspace f),
      Finset.supIndep_iff_disjoint_erase] using fun s χ _ ↦ this _ _ (s.notMem_erase χ)
  intro χ₁ s
  induction s using Finset.induction_on with
  | empty => simp
  | insert χ₂ s _n ih =>
  intro hχ₁₂
  obtain ⟨hχ₁₂ : χ₁ ≠ χ₂, hχ₁ : χ₁ ∉ s⟩ := by rwa [Finset.mem_insert, not_or] at hχ₁₂
  specialize ih hχ₁
  rw [Finset.sup_insert, disjoint_iff, Submodule.eq_bot_iff]
  rintro x ⟨hx, hx'⟩
  simp only [SetLike.mem_coe] at hx hx'
  suffices x ∈ ⨅ i, (f i).maxGenEigenspace (χ₂ i) by
    rw [← Submodule.mem_bot (R := R), ← (disjoint_iInf_maxGenEigenspace f hχ₁₂).eq_bot]
    exact ⟨hx, this⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'; clear hx'
  suffices ∀ l, ∃ (k : ℕ),
      ((f l - algebraMap R (Module.End R M) (χ₂ l)) ^ k) (y + z) ∈
      (⨅ i, (f i).maxGenEigenspace (χ₁ i)) ⊓
        Finset.sup s fun χ ↦ ⨅ i, (f i).maxGenEigenspace (χ i) by
    simpa [ih.eq_bot, Submodule.mem_bot] using this
  intro l
  let g : Module.End R M := f l - algebraMap R (Module.End R M) (χ₂ l)
  obtain ⟨k, hk : (g ^ k) y = 0⟩ := (mem_iInf_maxGenEigenspace_iff _ _ _).mp hy l
  have aux (f : End R M) (φ : R) (k : ℕ) (p : Submodule R M) (hp : MapsTo f p p) :
      MapsTo ((f - algebraMap R (Module.End R M) φ) ^ k) p p := by
    rw [Module.End.coe_pow]
    exact MapsTo.iterate (fun m hm ↦ p.sub_mem (hp hm) (p.smul_mem _ hm)) k
  refine ⟨k, Submodule.mem_inf.mp ⟨?_, ?_⟩⟩
  · refine aux (f l) (χ₂ l) k (⨅ i, (f i).maxGenEigenspace (χ₁ i)) ?_ hx
    simp only [Submodule.iInf_coe]
    exact h l χ₁
  · rw [map_add, hk, zero_add]
    suffices (s.sup fun χ ↦ (⨅ i, (f i).maxGenEigenspace (χ i))).map (g ^ k) ≤
        s.sup fun χ ↦ (⨅ i, (f i).maxGenEigenspace (χ i)) by
      refine this (Submodule.mem_map_of_mem ?_)
      simp_rw [Finset.sup_eq_iSup, ← Finset.sup_eq_iSup] at hz
      exact hz
    simp_rw [Finset.sup_eq_iSup, Submodule.map_iSup (ι := ι → R), Submodule.map_iSup (ι := _ ∈ s)]
    refine iSup₂_mono fun χ _ ↦ ?_
    rintro - ⟨u, hu, rfl⟩
    refine aux (f l) (χ₂ l) k (⨅ i, (f i).maxGenEigenspace (χ i)) ?_ hu
    simp only [Submodule.iInf_coe]
    exact h l χ

/-- Given a family of endomorphisms `i ↦ f i` which are compatible in the sense that every maximal
generalised eigenspace of `f i` is invariant wrt `f j`, if each `f i` is triangularizable, the
family is simultaneously triangularizable. -/
lemma iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo [FiniteDimensional K M]
    (f : ι → End K M)
    (h : ∀ i j φ, MapsTo (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigenspace φ))
    (h' : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) :
    ⨆ χ : ι → K, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by
  generalize h_dim : finrank K M = n
  induction n using Nat.strongRecOn generalizing M with | ind n ih => ?_
  obtain this | ⟨i : ι, hy : ¬ ∃ φ, (f i).maxGenEigenspace φ = ⊤⟩ :=
    forall_or_exists_not (fun j : ι ↦ ∃ φ : K, (f j).maxGenEigenspace φ = ⊤)
  · choose χ hχ using this
    replace hχ : ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by simpa
    simp_rw [eq_top_iff] at hχ ⊢
    exact le_trans hχ <| le_iSup (fun χ : ι → K ↦ ⨅ i, (f i).maxGenEigenspace (χ i)) χ
  · replace hy : ∀ φ, finrank K ((f i).maxGenEigenspace φ) < n := fun φ ↦ by
      simp_rw [not_exists, ← lt_top_iff_ne_top] at hy; exact h_dim ▸ Submodule.finrank_lt (hy φ).ne
    have hi (j : ι) (φ : K) :
        MapsTo (f j) ((f i).maxGenEigenspace φ) ((f i).maxGenEigenspace φ) := by
      exact h j i φ
    replace ih (φ : K) :
        ⨆ χ : ι → K, ⨅ j, maxGenEigenspace ((f j).restrict (hi j φ)) (χ j) = ⊤ := by
      apply ih _ (hy φ)
      · intro j k μ
        exact mapsTo_restrict_maxGenEigenspace_restrict_of_mapsTo (f j) (f k) _ _ (h j k μ)
      · exact fun j ↦ Module.End.genEigenspace_restrict_eq_top _ (h' j)
      · rfl
    replace ih (φ : K) :
        ⨆ (χ : ι → K) (_ : χ i = φ), ⨅ j, maxGenEigenspace ((f j).restrict (hi j φ)) (χ j) = ⊤ := by
      suffices ∀ χ : ι → K, χ i ≠ φ → ⨅ j, maxGenEigenspace ((f j).restrict (hi j φ)) (χ j) = ⊥ by
        specialize ih φ; rw [iSup_split, biSup_congr this] at ih; simpa using ih
      intro χ hχ
      rw [eq_bot_iff, ← ((f i).maxGenEigenspace φ).ker_subtype, LinearMap.ker,
        ← Submodule.map_le_iff_le_comap, ← Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo,
        ← disjoint_iff_inf_le]
      exact ((f i).disjoint_genEigenspace hχ.symm _ _).mono_right (iInf_le _ i)
    replace ih (φ : K) :
        ⨆ (χ : ι → K) (_ : χ i = φ), ⨅ j, maxGenEigenspace (f j) (χ j) =
        maxGenEigenspace (f i) φ := by
      have (χ : ι → K) (hχ : χ i = φ) : ⨅ j, maxGenEigenspace (f j) (χ j) =
          (⨅ j, maxGenEigenspace ((f j).restrict (hi j φ)) (χ j)).map
            ((f i).maxGenEigenspace φ).subtype := by
        rw [← hχ, iInf_maxGenEigenspace_restrict_map_subtype_eq]
      simp_rw [biSup_congr this, ← Submodule.map_iSup, ih, Submodule.map_top,
        Submodule.range_subtype]
    simpa only [← ih, iSup_comm (ι := K), iSup_iSup_eq_right] using h' i

/-- A commuting family of triangularizable endomorphisms is simultaneously triangularizable. -/
theorem iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    [FiniteDimensional K M] (f : ι → Module.End K M) (h : Pairwise fun i j ↦ Commute (f i) (f j))
    (h' : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) :
    ⨆ χ : ι → K, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by
  refine Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo _
    (fun i j ↦ Module.End.mapsTo_maxGenEigenspace_of_comm ?_) h'
  rcases eq_or_ne j i with rfl | hij <;> tauto

end Module.End
