/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Basis.Flag
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Projection

/-!
# Triangularizable linear endomorphisms

This file contains basic results relevant to the triangularizability of linear endomorphisms.

## Main definitions / results

* `Module.End.exists_eigenvalue`: in finite dimensions, over an algebraically closed field, every
  linear endomorphism has an eigenvalue.
* `Module.End.IsTriangularizedBy`: a flag-based predicate saying that a basis triangularizes an
  endomorphism.
* `Module.End.IsTriangularizedByFlag`: a predicate saying that every submodule in a flag is
  invariant.
* `Module.End.IsTriangularizable`: an endomorphism is triangularizable if it admits an invariant
  complete flag.
* `Module.End.isTriangularizedBy_iff_isUpperTriangular_toMatrix`: equivalently, the matrix of `f`
  in that basis is upper triangular.
* `Module.End.exists_isTriangularizedBy_of_iSup_maxGenEigenspace_eq_top`: in finite dimensions,
  if the maximal generalized eigenspaces span the whole space, then `f` admits a triangularizing
  basis.
* `Module.End.iSup_maxGenEigenspace_eq_top_of_charpoly_splits`: in finite dimensions, if the
  characteristic polynomial splits, then the maximal generalized eigenspaces span the whole space.
* `Module.End.exists_isTriangularizedBy_iff_iSup_maxGenEigenspace_eq_top`: in finite dimensions,
  a basis triangularizes an endomorphism if and only if its maximal generalized eigenspaces span.
* `Module.End.isTriangularizable`: in finite dimensions over an algebraically closed field, every
  endomorphism admits an invariant complete flag.
* `Module.End.exists_invariantFlag`: the unbundled form of `Module.End.isTriangularizable`.
* `Module.End.exists_isTriangularizedBy`: in finite dimensions over an algebraically closed field,
  every endomorphism admits a triangularizing basis.
* `Module.End.iSup_maxGenEigenspace_eq_top`: in finite dimensions, over an algebraically
  closed field, the generalized eigenspaces of any linear endomorphism span the whole space.
* `Module.End.iSup_genEigenspace_restrict_eq_top`: in finite dimensions, if the
  generalized eigenspaces of a linear endomorphism span the whole space then the same is true of
  its restriction to any invariant submodule.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2024]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## TODO

Prove the converse of `Module.End.isTriangularizable_of_iSup_maxGenEigenspace_eq_top`, completing
the finite-dimensional characterization of `Module.End.IsTriangularizable` by
`⨆ μ, f.maxGenEigenspace μ = ⊤`.

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/

public section

open Set Function Module Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Module.End

/-- A basis triangularizes an endomorphism if its associated complete flag is invariant. -/
def IsTriangularizedBy {n : ℕ} (f : End K V) (b : Basis (Fin n) K V) : Prop :=
  ∀ k : Fin (n + 1), b.flag k ∈ f.invtSubmodule

/-- A flag triangularizes an endomorphism if every submodule in the flag is invariant. -/
def IsTriangularizedByFlag (f : End K V) (c : Flag (Submodule K V)) : Prop :=
  ∀ ⦃p : Submodule K V⦄, p ∈ c → p ∈ f.invtSubmodule

/-- An endomorphism is triangularizable if it admits an invariant complete flag. -/
def IsTriangularizable (f : End K V) : Prop :=
  ∃ c : Flag (Submodule K V), f.IsTriangularizedByFlag c

variable {n : ℕ} {f : End K V} {b : Basis (Fin n) K V}

theorem isTriangularizedBy_iff_isTriangularizedByFlag_toFlag :
    f.IsTriangularizedBy b ↔ f.IsTriangularizedByFlag b.toFlag := by
  constructor
  · intro hf p hp
    rw [Basis.mem_toFlag] at hp
    obtain ⟨k, rfl⟩ := hp
    exact hf k
  · intro hf k
    exact hf (Basis.mem_toFlag b |>.2 ⟨k, rfl⟩)

theorem IsTriangularizedBy.isTriangularizable (hb : f.IsTriangularizedBy b) :
    f.IsTriangularizable :=
  ⟨b.toFlag, isTriangularizedBy_iff_isTriangularizedByFlag_toFlag.mp hb⟩

theorem isTriangularizedBy_of_flag_eq {b' : Basis (Fin n) K V}
    (hb : f.IsTriangularizedBy b) (hflag : ∀ k, b'.flag k = b.flag k) :
    f.IsTriangularizedBy b' := by
  intro k
  rw [hflag k]
  exact hb k

theorem IsTriangularizedBy.map {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    (hb : f.IsTriangularizedBy b) (e : V ≃ₗ[K] V₂) :
    (e.conj f).IsTriangularizedBy (b.map e) := by
  intro k
  rw [Module.Basis.flag_map]
  exact LinearEquiv.map_mem_invtSubmodule_conj_iff.mpr (hb k)

theorem isTriangularizedBy_iff_isUpperTriangular_toMatrix :
    f.IsTriangularizedBy b ↔ (LinearMap.toMatrix b b f).IsUpperTriangular := by
  constructor
  · intro hf i j hji
    rw [LinearMap.toMatrix_apply]
    have hmem : f (b j) ∈ LinearMap.ker (b.coord i) := by
      apply b.flag_le_ker_coord
      · exact Fin.castSucc_lt_iff_succ_le.mp (show j.castSucc < i.castSucc from hji)
      · exact (hf j.succ : b.flag j.succ ≤ (b.flag j.succ).comap f)
          (b.self_mem_flag (Fin.castSucc_lt_succ_iff.mpr le_rfl))
    simpa [Module.Basis.coord_apply] using LinearMap.mem_ker.mp hmem
  · intro hf k
    rw [Module.End.mem_invtSubmodule]
    exact b.flag_le_iff.2 fun i hik => by
      change f (b i) ∈ b.flag k
      rw [b.mem_flag_iff_repr_eq_zero]
      intro l hlk
      rw [← LinearMap.toMatrix_apply b b f l i]
      exact hf (Fin.castSucc_lt_castSucc_iff.mp (lt_of_lt_of_le hik hlk))

theorem IsTriangularizedBy.charpoly_splits [FiniteDimensional K V] (hb : f.IsTriangularizedBy b) :
    f.charpoly.Splits := by
  rw [← LinearMap.charpoly_toMatrix (f := f) b]
  rw [Matrix.charpoly_of_upperTriangular _
    (isTriangularizedBy_iff_isUpperTriangular_toMatrix.mp hb)]
  exact Polynomial.Splits.prod fun i _ => by
    simpa [sub_eq_add_neg] using Polynomial.Splits.X_add_C (-(LinearMap.toMatrix b b f i i))

/-- If the generalized eigenspaces of `f` span the whole space, then the same holds for the map
induced by `f` on a quotient by an invariant submodule. -/
theorem iSup_genEigenspace_mapQ_eq_top {p : Submodule K V} {f : End K V}
    (hfp : p ≤ p.comap f) {k : ℕ∞} (hf : ⨆ μ, f.genEigenspace μ k = ⊤) :
    ⨆ μ, Module.End.genEigenspace (p.mapQ p f hfp : End K (V ⧸ p)) μ k = ⊤ := by
  rw [← top_le_iff]
  calc
    ⊤ = (⊤ : Submodule K V).map p.mkQ := by
      rw [Submodule.map_top]
      exact (LinearMap.range_eq_top.mpr p.mkQ_surjective).symm
    _ = (⨆ μ, f.genEigenspace μ k).map p.mkQ := by rw [hf]
    _ = ⨆ μ, (f.genEigenspace μ k).map p.mkQ := by rw [Submodule.map_iSup]
    _ ≤ ⨆ μ, Module.End.genEigenspace (p.mapQ p f hfp : End K (V ⧸ p)) μ k :=
      iSup_mono fun μ =>
        Module.End.map_genEigenspace_le p.mkQ (Submodule.mapQ_mkQ p p f (h := hfp)) μ k

/-- The maximal-generalized-eigenspace version of
`Module.End.iSup_genEigenspace_mapQ_eq_top`. -/
theorem iSup_maxGenEigenspace_mapQ_eq_top {p : Submodule K V} {f : End K V}
    (hfp : p ≤ p.comap f) (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) :
    ⨆ μ, Module.End.maxGenEigenspace (p.mapQ p f hfp : End K (V ⧸ p)) μ = ⊤ :=
  iSup_genEigenspace_mapQ_eq_top hfp hf

theorem IsTriangularizedBy.mkFinCons_of_sub_mem_span_singleton {n : ℕ} {f : End K V}
    {v : V} {μ : K} {W : Submodule K V} {g : End K W} {bW : Basis (Fin n) K W}
    {hli hsp} (hg : g.IsTriangularizedBy bW) (hv : f v = μ • v)
    (hfg : ∀ w : W, f (w : V) - (g w : V) ∈ K ∙ v) :
    f.IsTriangularizedBy (Basis.mkFinCons v bW hli hsp) := by
  intro k
  refine Fin.cases (by simp) (fun k => ?_) k
  rw [Module.End.mem_invtSubmodule]
  exact (Basis.mkFinCons v bW hli hsp).flag_le_iff.2 fun i hi => by
    change f (Basis.mkFinCons v bW hli hsp i) ∈ (Basis.mkFinCons v bW hli hsp).flag k.succ
    revert hi
    refine Fin.cases (fun _ => ?_) ?_ i
    · rw [show Basis.mkFinCons v bW hli hsp 0 = v by simp, hv]
      exact Submodule.smul_mem _ _ <|
        Basis.span_singleton_le_mkFinCons_flag_succ k (Submodule.mem_span_singleton_self v)
    intro i hi
    rw [show Basis.mkFinCons v bW hli hsp i.succ = (bW i : V) by simp]
    have hgw := (hg k : bW.flag k ≤ (bW.flag k).comap g)
      (bW.self_mem_flag (Fin.succ_lt_succ_iff.mp hi))
    have hdecomp : f (bW i : V) = (f (bW i : V) - (g (bW i) : V)) + (g (bW i) : V) := by
      abel
    rw [hdecomp]
    exact Submodule.add_mem _ (Basis.span_singleton_le_mkFinCons_flag_succ k (hfg (bW i)))
      (Basis.map_flag_le_mkFinCons_flag_succ k ⟨_, hgw, rfl⟩)

theorem exists_hasEigenvalue_of_genEigenspace_eq_top [Nontrivial M] {f : End R M} (k : ℕ∞)
    (hf : ⨆ μ, f.genEigenspace μ k = ⊤) :
    ∃ μ, f.HasEigenvalue μ := by
  suffices ∃ μ, f.HasUnifEigenvalue μ k by
    peel this with μ hμ
    exact HasUnifEigenvalue.lt zero_lt_one hμ
  simp [HasUnifEigenvalue, ← not_forall, ← iSup_eq_bot, hf]

theorem exists_hasEigenvalue_of_iSup_maxGenEigenspace_eq_top [Nontrivial M] {f : End R M}
    (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) :
    ∃ μ, f.HasEigenvalue μ :=
  exists_hasEigenvalue_of_genEigenspace_eq_top ⊤ hf

-- This is Lemma 5.19 of [axler2024], although we are no longer following that proof.
/-- In finite dimensions, over an algebraically closed field, every linear endomorphism has an
eigenvalue. -/
theorem exists_eigenvalue [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) :
    ∃ c : K, f.HasEigenvalue c := by
  simp_rw [hasEigenvalue_iff_mem_spectrum]
  exact spectrum.nonempty_of_isAlgClosed_of_finiteDimensional K f

noncomputable instance [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) :
    Inhabited f.Eigenvalues :=
  ⟨⟨f.exists_eigenvalue.choose, f.exists_eigenvalue.choose_spec⟩⟩

theorem exists_isTriangularizedBy_of_subsingleton [Subsingleton V] (f : End K V) :
    ∃ n, ∃ b : Basis (Fin n) K V, f.IsTriangularizedBy b := by
  refine ⟨0, (Module.Basis.empty V : Basis (Fin 0) K V), ?_⟩
  intro k
  change (Module.Basis.empty V : Basis (Fin 0) K V).flag k ≤
    ((Module.Basis.empty V : Basis (Fin 0) K V).flag k).comap f
  intro x hx
  change f x ∈ (Module.Basis.empty V : Basis (Fin 0) K V).flag k
  convert hx using 1

private noncomputable def triangularizationAux_of_iSup_maxGenEigenspace_eq_top {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (f : End K V)
    (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) :
    ∃ n, ∃ b : Basis (Fin n) K V, f.IsTriangularizedBy b :=
  haveI : Decidable (Nontrivial V) := Classical.propDecidable _
  if hV : Nontrivial V then
    let ⟨μ, hμ⟩ := exists_hasEigenvalue_of_iSup_maxGenEigenspace_eq_top hf
    let ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ
    let L : Submodule K V := K ∙ v
    have hL : L ≤ L.comap f := by
      rw [Submodule.span_singleton_le_iff_mem]
      change f v ∈ L
      rw [hv.apply_eq_smul]
      exact Submodule.smul_mem L μ (Submodule.mem_span_singleton_self v)
    let qf : End K (V ⧸ L) := L.mapQ L f hL
    have hqf : ⨆ μ, qf.maxGenEigenspace μ = ⊤ :=
      iSup_maxGenEigenspace_mapQ_eq_top hL hf
    let ⟨n, bq, hbq⟩ := triangularizationAux_of_iSup_maxGenEigenspace_eq_top qf hqf
    let ⟨W, hW⟩ := L.exists_isCompl
    let e : (V ⧸ L) ≃ₗ[K] W := Submodule.quotientEquivOfIsCompl L W hW
    let g : End K W := e.conj qf
    ⟨n + 1, Basis.mkFinConsOfIsCompl v (bq.map e) hv.2 hW, by
      simpa [Basis.mkFinConsOfIsCompl] using (hbq.map e).mkFinCons_of_sub_mem_span_singleton
        hv.apply_eq_smul
        (by
          intro w
          have hq : L.mkQ (f (w : V)) = L.mkQ (g w : V) := by
            calc
              L.mkQ (f (w : V)) = qf (L.mkQ (w : V)) := by
                rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
              _ = qf (e.symm w) := by simp [e, Submodule.mkQ_apply]
              _ = e.symm (g w) := by simp [g]
              _ = L.mkQ (g w : V) := by simp [e, Submodule.mkQ_apply]
          change f (w : V) - (g w : V) ∈ L
          rw [← Submodule.ker_mkQ L]
          exact LinearMap.mem_ker.mpr (by
            simpa using congr_arg (fun x => x - L.mkQ (g w : V)) hq))⟩
  else
    haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    exists_isTriangularizedBy_of_subsingleton f
termination_by Module.finrank K V
decreasing_by
  have hdim := Submodule.finrank_quotient_add_finrank L
  rw [finrank_span_singleton hv.2] at hdim
  rw [← hdim]
  exact Nat.lt_add_of_pos_right Nat.zero_lt_one

/-- If the maximal generalized eigenspaces of a finite-dimensional endomorphism span the whole
space, then the endomorphism is triangularized by some basis. -/
theorem exists_isTriangularizedBy_of_iSup_maxGenEigenspace_eq_top [FiniteDimensional K V]
    {f : End K V} (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) :
    ∃ n, ∃ b : Basis (Fin n) K V, f.IsTriangularizedBy b :=
  triangularizationAux_of_iSup_maxGenEigenspace_eq_top f hf

/-- If the maximal generalized eigenspaces of a finite-dimensional endomorphism span the whole
space, then the endomorphism is triangularizable. -/
theorem isTriangularizable_of_iSup_maxGenEigenspace_eq_top [FiniteDimensional K V]
    {f : End K V} (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) :
    f.IsTriangularizable := by
  obtain ⟨n, b, hb⟩ := exists_isTriangularizedBy_of_iSup_maxGenEigenspace_eq_top hf
  exact hb.isTriangularizable

private theorem finrank_finset_sup_maxGenEigenspace [FiniteDimensional K V]
    (f : End K V) (s : Finset K) :
    finrank K (s.sup (fun μ => f.maxGenEigenspace μ) : Submodule K V) =
      ∑ μ ∈ s, finrank K (f.maxGenEigenspace μ) := by
  classical
  have hind := Module.End.independent_maxGenEigenspace f
  induction s using Finset.induction_on with
  | empty => simp
  | insert μ s hμ ih =>
      have hdisj : Disjoint (f.maxGenEigenspace μ)
          (s.sup (fun μ => f.maxGenEigenspace μ) : Submodule K V) := by
        have hs := hind.supIndep' (insert μ s)
        simpa [hμ] using
          (Finset.supIndep_iff_disjoint_erase.mp hs μ (Finset.mem_insert_self μ s))
      have hfin := Submodule.finrank_sup_add_finrank_inf_eq (f.maxGenEigenspace μ)
        (s.sup (fun μ => f.maxGenEigenspace μ) : Submodule K V)
      rw [hdisj.eq_bot, finrank_bot, add_zero] at hfin
      rw [Finset.sup_insert, Finset.sum_insert hμ, hfin, ih]

/-- If the characteristic polynomial of a finite-dimensional endomorphism splits, then its maximal
generalized eigenspaces span the whole space. -/
theorem iSup_maxGenEigenspace_eq_top_of_charpoly_splits [FiniteDimensional K V]
    {f : End K V} (hf : f.charpoly.Splits) :
    ⨆ μ, f.maxGenEigenspace μ = ⊤ := by
  classical
  let s := f.charpoly.roots.toFinset
  have hs : (s.sup (fun μ => f.maxGenEigenspace μ) : Submodule K V) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    calc
      finrank K (s.sup (fun μ => f.maxGenEigenspace μ) : Submodule K V)
          = ∑ μ ∈ s, finrank K (f.maxGenEigenspace μ) :=
            finrank_finset_sup_maxGenEigenspace f s
      _ = ∑ μ ∈ s, f.charpoly.rootMultiplicity μ := by
            refine Finset.sum_congr rfl fun μ _ => ?_
            exact LinearMap.finrank_maxGenEigenspace_eq f μ
      _ = ∑ μ ∈ s, f.charpoly.roots.count μ := by
            refine Finset.sum_congr rfl fun μ _ => ?_
            rw [Polynomial.count_roots]
      _ = f.charpoly.roots.card := by
            exact Multiset.sum_count_eq_card (by simp [s])
      _ = f.charpoly.natDegree := hf.natDegree_eq_card_roots.symm
      _ = finrank K V := LinearMap.charpoly_natDegree f
  rw [← top_le_iff, ← hs]
  exact Finset.sup_le fun μ _ => le_iSup f.maxGenEigenspace μ

theorem IsTriangularizedBy.iSup_maxGenEigenspace_eq_top [FiniteDimensional K V]
    (hb : f.IsTriangularizedBy b) :
    ⨆ μ, f.maxGenEigenspace μ = ⊤ :=
  iSup_maxGenEigenspace_eq_top_of_charpoly_splits hb.charpoly_splits

theorem exists_isTriangularizedBy_iff_iSup_maxGenEigenspace_eq_top [FiniteDimensional K V]
    (f : End K V) :
    (∃ n, ∃ b : Basis (Fin n) K V, f.IsTriangularizedBy b) ↔
      ⨆ μ, f.maxGenEigenspace μ = ⊤ := by
  constructor
  · rintro ⟨n, b, hb⟩
    exact hb.iSup_maxGenEigenspace_eq_top
  · exact exists_isTriangularizedBy_of_iSup_maxGenEigenspace_eq_top

/-- In finite dimensions, over an algebraically closed field, the generalized eigenspaces of any
linear endomorphism span the whole space. -/
theorem iSup_maxGenEigenspace_eq_top [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    ⨆ (μ : K), f.maxGenEigenspace μ = ⊤ :=
  iSup_maxGenEigenspace_eq_top_of_charpoly_splits (IsAlgClosed.splits f.charpoly)

/-- In finite dimensions over an algebraically closed field, every endomorphism is triangularized by
some basis. -/
theorem exists_isTriangularizedBy [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    ∃ n, ∃ b : Basis (Fin n) K V, f.IsTriangularizedBy b :=
  exists_isTriangularizedBy_of_iSup_maxGenEigenspace_eq_top (iSup_maxGenEigenspace_eq_top f)

/-- In finite dimensions over an algebraically closed field, every endomorphism is
triangularizable. -/
theorem isTriangularizable [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    f.IsTriangularizable :=
  isTriangularizable_of_iSup_maxGenEigenspace_eq_top (iSup_maxGenEigenspace_eq_top f)

/-- In finite dimensions over an algebraically closed field, every endomorphism admits an invariant
complete flag. -/
theorem exists_invariantFlag [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    ∃ c : Flag (Submodule K V), f.IsTriangularizedByFlag c :=
  f.isTriangularizable

end Module.End

namespace Submodule

variable {p : Submodule K V} {f : Module.End K V}

theorem inf_iSup_genEigenspace [FiniteDimensional K V] (h : ∀ x ∈ p, f x ∈ p) (k : ℕ∞) :
    p ⊓ ⨆ μ, f.genEigenspace μ k = ⨆ μ, p ⊓ f.genEigenspace μ k := by
  refine le_antisymm (fun m hm ↦ ?_)
    (le_inf_iff.mpr ⟨iSup_le fun μ ↦ inf_le_left, iSup_mono fun μ ↦ inf_le_right⟩)
  classical
  obtain ⟨hm₀ : m ∈ p, hm₁ : m ∈ ⨆ μ, f.genEigenspace μ k⟩ := hm
  obtain ⟨m, hm₂, rfl⟩ := (mem_iSup_iff_exists_finsupp _ _).mp hm₁
  suffices ∀ μ, (m μ : V) ∈ p by
    exact (mem_iSup_iff_exists_finsupp _ _).mpr ⟨m, fun μ ↦ mem_inf.mp ⟨this μ, hm₂ μ⟩, rfl⟩
  intro μ
  by_cases hμ : μ ∈ m.support; swap
  · simp only [Finsupp.notMem_support_iff.mp hμ, p.zero_mem]
  have hm₂_aux := hm₂
  simp_rw [Module.End.mem_genEigenspace] at hm₂_aux
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
      rw [map_finsuppSum, Finsupp.sum_congr (g2 := fun μ' _ ↦ if μ' = μ then g (m μ) else 0) this,
        Finsupp.sum_ite_eq', if_pos hμ]
    rintro μ' hμ'
    split_ifs with hμμ'
    · rw [hμμ']
    have hl₀ : ((f - algebraMap K (End K V) μ') ^ l₀) (m μ') = 0 := by
      rw [← LinearMap.mem_ker, Algebra.algebraMap_eq_smul_one, ← End.mem_genEigenspace_nat]
      simp_rw [← End.mem_genEigenspace_nat] at hl
      suffices (l μ' : ℕ∞) ≤ l₀ from (f.genEigenspace μ').mono this (hl μ')
      simpa only [Nat.cast_le] using Finset.le_sup hμ'
    have : _ = g := (m.support.erase μ).noncommProd_erase_mul (Finset.mem_erase.mpr ⟨hμμ', hμ'⟩)
      (fun μ ↦ (f - algebraMap K (End K V) μ) ^ l₀) (fun μ₁ _ μ₂ _ _ ↦ h_comm μ₁ μ₂)
    rw [← this, Module.End.mul_apply, hl₀, _root_.map_zero]
  have hg₁ : MapsTo g p p := Finset.noncommProd_induction _ _ _ (fun g' : End K V ↦ MapsTo g' p p)
      (fun f₁ f₂ ↦ MapsTo.comp) (mapsTo_id _) fun μ' _ ↦ by
    suffices MapsTo (f - algebraMap K (End K V) μ') p p by
      simp only [Module.End.coe_pow, this.iterate l₀]
    intro x hx
    rw [LinearMap.sub_apply, algebraMap_end_apply]
    exact p.sub_mem (h _ hx) (smul_mem p μ' hx)
  have hg₂ : MapsTo g ↑(f.genEigenspace μ k) ↑(f.genEigenspace μ k) :=
    f.mapsTo_genEigenspace_of_comm hfg μ k
  have hg₃ : InjOn g ↑(f.genEigenspace μ k) := by
    apply LinearMap.injOn_of_disjoint_ker subset_rfl
    have this := f.independent_genEigenspace k
    have aux (μ') (_hμ' : μ' ∈ m.support.erase μ) :
        (f.genEigenspace μ') ↑l₀ ≤ (f.genEigenspace μ') k := by
      apply (f.genEigenspace μ').mono
      obtain _ | k := k
      · exact le_top
      · exact Nat.cast_le.2 <| Finset.sup_le fun i _ ↦ Nat.cast_le.1 <| hlk i
    rw [LinearMap.ker_noncommProd_eq_of_supIndep_ker, ← Finset.sup_eq_iSup]
    · have := Finset.supIndep_iff_disjoint_erase.mp (this.supIndep' m.support) μ hμ
      apply this.mono_right
      apply Finset.sup_mono_fun
      intro μ' hμ'
      rw [Algebra.algebraMap_eq_smul_one, ← End.genEigenspace_nat]
      apply aux μ' hμ'
    · have := this.supIndep' (m.support.erase μ)
      apply this.antitone_fun
      intro μ' hμ'
      rw [Algebra.algebraMap_eq_smul_one, ← End.genEigenspace_nat]
      apply aux μ' hμ'
  have hg₄ : SurjOn g
      ↑(p ⊓ f.genEigenspace μ k) ↑(p ⊓ f.genEigenspace μ k) := by
    have : MapsTo g
        ↑(p ⊓ f.genEigenspace μ k) ↑(p ⊓ f.genEigenspace μ k) :=
      hg₁.inter_inter hg₂
    rw [← LinearMap.injOn_iff_surjOn this]
    exact hg₃.mono inter_subset_right
  specialize hm₂ μ
  obtain ⟨y, ⟨hy₀ : y ∈ p, hy₁ : y ∈ f.genEigenspace μ k⟩, hy₂ : g y = g (m μ)⟩ :=
    hg₄ ⟨(hg₀ ▸ hg₁ hm₀), hg₂ hm₂⟩
  rwa [← hg₃ hy₁ hm₂ hy₂]

theorem eq_iSup_inf_genEigenspace [FiniteDimensional K V] (k : ℕ∞)
    (h : ∀ x ∈ p, f x ∈ p) (h' : ⨆ μ, f.genEigenspace μ k = ⊤) :
    p = ⨆ μ, p ⊓ f.genEigenspace μ k := by
  rw [← inf_iSup_genEigenspace h, h', inf_top_eq]

end Submodule

/-- In finite dimensions, if the generalized eigenspaces of a linear endomorphism span the whole
space then the same is true of its restriction to any invariant submodule. -/
theorem Module.End.genEigenspace_restrict_eq_top
    {p : Submodule K V} {f : Module.End K V} [FiniteDimensional K V] {k : ℕ∞}
    (h : ∀ x ∈ p, f x ∈ p) (h' : ⨆ μ, f.genEigenspace μ k = ⊤) :
    ⨆ μ, Module.End.genEigenspace (LinearMap.restrict f h) μ k = ⊤ := by
  have := congr_arg (Submodule.comap p.subtype) (Submodule.eq_iSup_inf_genEigenspace k h h')
  have h_inj : Function.Injective p.subtype := Subtype.coe_injective
  simp_rw [Submodule.inf_genEigenspace f p h, Submodule.comap_subtype_self,
    ← Submodule.map_iSup, Submodule.comap_map_eq_of_injective h_inj] at this
  exact this.symm
