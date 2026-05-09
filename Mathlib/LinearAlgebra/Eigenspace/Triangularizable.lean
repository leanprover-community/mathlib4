/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Basis.Flag
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Quotient.Basic

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
* `Module.End.isTriangularizable`: in finite dimensions over an algebraically closed field, every
  endomorphism admits an invariant complete flag.
* `Module.End.exists_invariantFlag`: the unbundled form of `Module.End.isTriangularizable`.
* `Module.End.exists_isTriangularizedBy`: in finite dimensions over an algebraically closed field,
  every endomorphism admits a triangularizing basis.
* `Module.End.iSup_genEigenspace_eq_top`: in finite dimensions, over an algebraically
  closed field, the generalized eigenspaces of any linear endomorphism span the whole space.
* `Module.End.iSup_genEigenspace_restrict_eq_top`: in finite dimensions, if the
  generalized eigenspaces of a linear endomorphism span the whole space then the same is true of
  its restriction to any invariant submodule.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2024]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## TODO

Characterize `Module.End.IsTriangularizable` in finite dimensions over a field by the condition
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

theorem isTriangularizedBy_toFlag :
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
  ⟨b.toFlag, isTriangularizedBy_toFlag.mp hb⟩

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

/-- An intertwining linear map sends generalized eigenspaces into generalized eigenspaces with the
same eigenvalue and exponent. -/
theorem map_genEigenspace_le {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    {f : End K V} {g : End K V₂} (φ : V →ₗ[K] V₂) (hφ : g.comp φ = φ.comp f)
    (μ : K) (k : ℕ∞) :
    (f.genEigenspace μ k).map φ ≤ g.genEigenspace μ k := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨l, hl, hx⟩ :=
    (Module.End.mem_genEigenspace (f := f) (μ := μ) (k := k) (x := x)).mp hx
  apply (Module.End.mem_genEigenspace (f := g) (μ := μ) (k := k) (x := φ x)).mpr
  refine ⟨l, hl, ?_⟩
  rw [LinearMap.mem_ker] at hx ⊢
  have hsub (x : V) : (g - μ • 1) (φ x) = φ ((f - μ • 1) x) := by
    have hfg : g (φ x) = φ (f x) := by
      exact LinearMap.congr_fun hφ x
    simp [LinearMap.sub_apply, hfg]
  have hpow (l : ℕ) (x : V) :
      ((g - μ • 1) ^ l) (φ x) = φ (((f - μ • 1) ^ l) x) := by
    induction l with
    | zero => simp
    | succ l ih =>
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, hsub]
  rw [hpow, hx, map_zero]

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
        map_genEigenspace_le p.mkQ (Submodule.mapQ_mkQ p p f (h := hfp)) μ k

/-- The maximal-generalized-eigenspace version of
`Module.End.iSup_genEigenspace_mapQ_eq_top`. -/
theorem iSup_maxGenEigenspace_mapQ_eq_top {p : Submodule K V} {f : End K V}
    (hfp : p ≤ p.comap f) (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) :
    ⨆ μ, Module.End.maxGenEigenspace (p.mapQ p f hfp : End K (V ⧸ p)) μ = ⊤ :=
  iSup_genEigenspace_mapQ_eq_top hfp hf

theorem isCompl_span_singleton_mkFinCons_hli {v : V} {W : Submodule K V}
    (hv : v ≠ 0) (hW : IsCompl (K ∙ v) W) :
    ∀ c : K, ∀ x ∈ W, c • v + x = 0 → c = 0 := by
  intro c x hx hcx
  have hcvW : c • v ∈ W := by
    rw [add_eq_zero_iff_eq_neg] at hcx
    rw [hcx]
    exact W.neg_mem hx
  have hcvL : c • v ∈ K ∙ v :=
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  have hcv0 : c • v = 0 := by
    simpa using hW.disjoint.le_bot ⟨hcvL, hcvW⟩
  exact (smul_eq_zero.mp hcv0).resolve_right hv

theorem isCompl_span_singleton_mkFinCons_hsp {v : V} {W : Submodule K V}
    (hW : IsCompl (K ∙ v) W) : ∀ z : V, ∃ c : K, z + c • v ∈ W := by
  intro z
  have hz : z ∈ K ∙ v ⊔ W := by
    rw [hW.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, huz⟩ := Submodule.mem_sup.mp hz
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
  refine ⟨-a, ?_⟩
  rw [← huz]
  simpa [add_assoc, add_comm, add_left_comm] using hw

theorem span_singleton_le_mkFinCons_flag_succ {n : ℕ} {v : V} {W : Submodule K V}
    {bW : Basis (Fin n) K W} {hli hsp} (k : Fin (n + 1)) :
    K ∙ v ≤ (Basis.mkFinCons v bW hli hsp).flag k.succ := by
  rw [Submodule.span_singleton_le_iff_mem]
  convert (Basis.mkFinCons v bW hli hsp).self_mem_flag (i := 0) (k := k.succ) ?_
  · simp [Basis.coe_mkFinCons]
  · simp

theorem map_flag_le_mkFinCons_flag_succ {n : ℕ} {v : V} {W : Submodule K V}
    {bW : Basis (Fin n) K W} {hli hsp} (k : Fin (n + 1)) :
    (bW.flag k).map W.subtype ≤ (Basis.mkFinCons v bW hli hsp).flag k.succ := by
  rw [Submodule.map_le_iff_le_comap]
  exact bW.flag_le_iff.2 fun i hi => by
    change (bW i : V) ∈ (Basis.mkFinCons v bW hli hsp).flag k.succ
    convert (Basis.mkFinCons v bW hli hsp).self_mem_flag (i := i.succ)
      (k := k.succ) (Fin.succ_lt_succ_iff.mpr hi)
    simp [Basis.coe_mkFinCons]

theorem mkFinCons_apply_zero_mem_flag {n : ℕ} {f : End K V} {v : V} {μ : K}
    {W : Submodule K V} {bW : Basis (Fin n) K W} {hli hsp} (hv : f v = μ • v)
    (k : Fin (n + 1)) :
    f (Basis.mkFinCons v bW hli hsp 0) ∈ (Basis.mkFinCons v bW hli hsp).flag k.succ := by
  rw [show Basis.mkFinCons v bW hli hsp 0 = v by simp [Basis.coe_mkFinCons], hv]
  exact Submodule.smul_mem _ _ <|
    span_singleton_le_mkFinCons_flag_succ k (Submodule.mem_span_singleton_self v)

theorem mkFinCons_apply_succ_mem_flag {n : ℕ} {f : End K V} {v : V} {W : Submodule K V}
    {bW : Basis (Fin n) K W} {hli hsp} (hW : IsCompl (K ∙ v) W) {k : Fin (n + 1)}
    {i : Fin n} (hi : i.castSucc < k)
    (hg : Module.End.IsTriangularizedBy
      (W.projectionOnto (K ∙ v) hW.symm ∘ₗ f.domRestrict W : End K W) bW) :
    f (Basis.mkFinCons v bW hli hsp i.succ) ∈
      (Basis.mkFinCons v bW hli hsp).flag k.succ := by
  rw [show Basis.mkFinCons v bW hli hsp i.succ = (bW i : V) by simp [Basis.coe_mkFinCons]]
  have hgw := (hg k : bW.flag k ≤ (bW.flag k).comap
    (W.projectionOnto (K ∙ v) hW.symm ∘ₗ f.domRestrict W : End K W)) (bW.self_mem_flag hi)
  have hdecomp : f (bW i : V) = (K ∙ v).projection W hW (f (bW i : V)) +
      W.projection (K ∙ v) hW.symm (f (bW i : V)) := by
    simpa using (LinearMap.congr_fun (Submodule.projection_add_projection_eq_id hW)
      (f (bW i : V))).symm
  rw [hdecomp]
  exact Submodule.add_mem _ (span_singleton_le_mkFinCons_flag_succ k <|
    Submodule.projection_apply_mem hW _) (map_flag_le_mkFinCons_flag_succ k ⟨_, hgw, rfl⟩)

theorem isTriangularizedBy_mkFinCons {n : ℕ} {f : End K V} {v : V} {μ : K}
    {W : Submodule K V} {bW : Basis (Fin n) K W} {hli hsp} (hv : f v = μ • v)
    (hW : IsCompl (K ∙ v) W)
    (hg : Module.End.IsTriangularizedBy
      (W.projectionOnto (K ∙ v) hW.symm ∘ₗ f.domRestrict W : End K W) bW) :
    f.IsTriangularizedBy (Basis.mkFinCons v bW hli hsp) := by
  intro k
  refine Fin.cases (by simp) (fun k => ?_) k
  rw [Module.End.mem_invtSubmodule]
  exact (Basis.mkFinCons v bW hli hsp).flag_le_iff.2 fun i hi => by
    change f (Basis.mkFinCons v bW hli hsp i) ∈ (Basis.mkFinCons v bW hli hsp).flag k.succ
    revert hi
    refine Fin.cases (fun _ => mkFinCons_apply_zero_mem_flag hv k) ?_ i
    exact fun i hi => mkFinCons_apply_succ_mem_flag hW (Fin.succ_lt_succ_iff.mp hi) hg

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

private noncomputable def triangularizationAux {V : Type*} [AddCommGroup V] [Module K V]
    [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    ∃ n, ∃ b : Basis (Fin n) K V, f.IsTriangularizedBy b :=
  haveI : Decidable (Nontrivial V) := Classical.propDecidable _
  if hV : Nontrivial V then
    let μ : f.Eigenvalues := default
    let ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector
      (μ.property : f.HasEigenvalue μ)
    let L : Submodule K V := K ∙ v
    let ⟨W, hW⟩ := L.exists_isCompl
    let g : End K W := W.projectionOnto L hW.symm ∘ₗ f.domRestrict W
    let ⟨n, bW, hg⟩ := triangularizationAux g
    let hli := isCompl_span_singleton_mkFinCons_hli hv.2 hW
    let hsp := isCompl_span_singleton_mkFinCons_hsp hW
    ⟨n + 1, Basis.mkFinCons v bW hli hsp,
      isTriangularizedBy_mkFinCons hv.apply_eq_smul hW hg⟩
  else
    haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    exists_isTriangularizedBy_of_subsingleton f
termination_by Module.finrank K V
decreasing_by
  have hdim := Submodule.finrank_add_eq_of_isCompl hW
  rw [finrank_span_singleton hv.2] at hdim
  rw [← hdim]
  exact Nat.lt_add_of_pos_left Nat.zero_lt_one

/-- In finite dimensions over an algebraically closed field, every endomorphism is triangularized by
some basis. -/
theorem exists_isTriangularizedBy [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    ∃ n, ∃ b : Basis (Fin n) K V, f.IsTriangularizedBy b :=
  triangularizationAux f

/-- In finite dimensions over an algebraically closed field, every endomorphism is
triangularizable. -/
theorem isTriangularizable [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    f.IsTriangularizable := by
  obtain ⟨n, b, hb⟩ := f.exists_isTriangularizedBy
  exact hb.isTriangularizable

/-- In finite dimensions over an algebraically closed field, every endomorphism admits an invariant
complete flag. -/
theorem exists_invariantFlag [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    ∃ c : Flag (Submodule K V), f.IsTriangularizedByFlag c :=
  f.isTriangularizable

-- Lemma 8.22(c) of [axler2024]
/-- In finite dimensions, over an algebraically closed field, the generalized eigenspaces of any
linear endomorphism span the whole space. -/
theorem iSup_maxGenEigenspace_eq_top [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    ⨆ (μ : K), f.maxGenEigenspace μ = ⊤ := by
  -- We prove the claim by strong induction on the dimension of the vector space.
  suffices ∀ n, finrank K V = n → ⨆ (μ : K), f.maxGenEigenspace μ = ⊤ by exact this _ rfl
  intro n h_dim
  induction n using Nat.strong_induction_on generalizing V with | h n ih =>
  rcases n with - | n
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
      dsimp +instances only [ES]
      rw [h_dim]
      apply pos_finrank_genEigenspace_of_hasEigenvalue hμ₀ (Nat.zero_lt_succ n)
    -- and the dimensions of `ES` and `ER` add up to `finrank K V`.
    have h_dim_add : finrank K ER + finrank K ES = finrank K V := by
      dsimp +instances only [ER, ES]
      rw [Module.End.genEigenspace_nat, Module.End.genEigenrange_nat]
      apply LinearMap.finrank_range_add_finrank_ker
    -- Therefore the dimension `ER` mus be smaller than `finrank K V`.
    have h_dim_ER : finrank K ER < n.succ := by lia
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
      rw [maxGenEigenspace, genEigenspace_restrict]
      apply Submodule.map_comap_le
    -- It follows that `ER` is contained in the span of all generalized eigenvectors.
    have hER : ER ≤ ⨆ (μ : K), f.maxGenEigenspace μ := by
      rw [← ih_ER']
      exact iSup_mono hff'
    -- `ES` is contained in this span by definition.
    have hES : ES ≤ ⨆ (μ : K), f.maxGenEigenspace μ :=
      ((f.genEigenspace μ₀).mono le_top).trans (le_iSup f.maxGenEigenspace μ₀)
    -- Moreover, we know that `ER` and `ES` are disjoint.
    have h_disjoint : Disjoint ER ES := generalized_eigenvec_disjoint_range_ker f μ₀
    -- Since the dimensions of `ER` and `ES` add up to the dimension of `V`, it follows that the
    -- span of all generalized eigenvectors is all of `V`.
    change ⨆ (μ : K), f.maxGenEigenspace μ = ⊤
    rw [← top_le_iff, ← Submodule.eq_top_of_disjoint ER ES h_dim_add.ge h_disjoint]
    apply sup_le hER hES

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
