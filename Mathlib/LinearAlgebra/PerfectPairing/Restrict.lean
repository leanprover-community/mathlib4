/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.BaseChange

/-!
# Restriction to submodules and restriction of scalars for perfect pairings.

We provide API for restricting perfect pairings to submodules and for restricting their scalars.

## Main definitions
* `PerfectPairing.restrict`: restriction of a perfect pairing to submodules.
* `PerfectPairing.restrictScalars`: restriction of scalars for a perfect pairing taking values in a
  subring.
* `PerfectPairing.restrictScalarsField`: simultaneously restrict both the domains and scalars
  of a perfect pairing with coefficients in a field.

-/

open Function Module Set
open Submodule (span subset_span)

noncomputable section

namespace PerfectPairing

section CommRing

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (p : PerfectPairing R M N)

section Restrict

variable {M' N' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  (i : M' →ₗ[R] M) (j : N' →ₗ[R] N) (hi : Injective i) (hj : Injective j)
  (hij : p.IsPerfectCompl (LinearMap.range i) (LinearMap.range j))

include hi hj hij

private lemma restrict_aux : Bijective (p.toLinearMap.compl₁₂ i j) := by
  refine ⟨LinearMap.ker_eq_bot.mp <| eq_bot_iff.mpr fun m hm ↦ ?_, fun f ↦ ?_⟩
  · replace hm : i m ∈ (LinearMap.range j).dualAnnihilator.map p.toDualLeft.symm := by
      simp only [Submodule.mem_map, Submodule.mem_dualAnnihilator]
      refine ⟨p.toDualLeft (i m), ?_, LinearEquiv.symm_apply_apply _ _⟩
      rintro - ⟨n, rfl⟩
      simpa using LinearMap.congr_fun hm n
    suffices i m ∈ (⊥ : Submodule R M) by simpa [hi] using this
    simpa only [← hij.isCompl_left.inf_eq_bot, Submodule.mem_inf]
      using ⟨LinearMap.mem_range_self i m, hm⟩
  · set F : Module.Dual R N := f ∘ₗ j.linearProjOfIsCompl _ hj hij.isCompl_right with hF
    have hF (n : N') : F (j n) = f n := by simp [hF]
    set m : M := p.toDualLeft.symm F with hm
    obtain ⟨-, ⟨m₀, rfl⟩, y, hy, hm'⟩ :=
      Submodule.exists_add_eq_of_codisjoint hij.isCompl_left.codisjoint m
    refine ⟨m₀, LinearMap.ext fun n ↦ ?_⟩
    replace hy : (p y) (j n) = 0 := by
      simp only [Submodule.mem_map, Submodule.mem_dualAnnihilator] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      simpa only [apply_toDualLeft_symm_apply] using hg _ (LinearMap.mem_range_self j n)
    rw [hm, ← LinearEquiv.symm_apply_eq, map_add, LinearEquiv.symm_symm,
      toDualLeft_apply] at hm'
    simpa [← hF, ← LinearMap.congr_fun hm' (j n)]

/-- The restriction of a perfect pairing to submodules (expressed as injections to provide
definitional control). -/
@[simps!]
def restrict : PerfectPairing R M' N' where
  toLinearMap := p.toLinearMap.compl₁₂ i j
  bijective_left := p.restrict_aux i j hi hj hij
  bijective_right := p.flip.restrict_aux j i hj hi hij.flip

@[simp]
lemma restrict_apply_apply (x : M') (y : N') :
    p.restrict i j hi hj hij x y = p (i x) (j y) :=
  rfl

end Restrict

section RestrictScalars

variable {S M' N' : Type*}
  [CommRing S] [Algebra S R] [Module S M] [Module S N] [IsScalarTower S R M] [IsScalarTower S R N]
  [NoZeroSMulDivisors S R] [Nontrivial R]
  [AddCommGroup M'] [Module S M'] [AddCommGroup N'] [Module S N']
  (i : M' →ₗ[S] M) (j : N' →ₗ[S] N)

/-- An auxiliary definition used to construct `PerfectPairing.restrictScalars`. -/
private def restrictScalarsAux
    (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap S R).range) :
    M' →ₗ[S] N' →ₗ[S] S :=
  LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap S R)
    (FaithfulSMul.algebraMap_injective S R) p.toLinearMap hp

private lemma restrictScalarsAux_injective
    (hi : Injective i)
    (hN : span R (LinearMap.range j : Set N) = ⊤)
    (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap S R).range) :
    Injective (p.restrictScalarsAux i j hp) := by
  let f := LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap S R)
      (FaithfulSMul.algebraMap_injective S R) p.toLinearMap hp
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr fun x (hx : f x = 0) ↦ ?_
  replace hx (n : N) : p (i x) n = 0 := by
    have hn : n ∈ span R (LinearMap.range j : Set N) := hN ▸ Submodule.mem_top
    induction hn using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨n', rfl⟩ := hz
      simpa [f] using LinearMap.congr_fun hx n'
    | zero => simp
    | add => rw [← p.toLinearMap_apply, map_add]; aesop
    | smul => rw [← p.toLinearMap_apply, map_smul]; aesop
  rw [← i.map_eq_zero_iff hi, ← p.toLinearMap.map_eq_zero_iff p.bijective_left.injective]
  ext n
  simpa using hx n

private lemma restrictScalarsAux_surjective
    (h : ∀ g : Module.Dual S N', ∃ m,
      (p.toDualLeft (i m)).restrictScalars S ∘ₗ j = Algebra.linearMap S R ∘ₗ g)
    (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap S R).range) :
    Surjective (p.restrictScalarsAux i j hp) := by
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_iff'.mpr fun g : Module.Dual S N' ↦ ?_
  obtain ⟨m, hm⟩ := h g
  refine ⟨m, ?_⟩
  ext n
  apply FaithfulSMul.algebraMap_injective S R
  change Algebra.linearMap S R _ = _
  simpa [restrictScalarsAux] using LinearMap.congr_fun hm n

/-- Restriction of scalars for a perfect pairing taking values in a subring. -/
def restrictScalars
    (hi : Injective i) (hj : Injective j)
    (hM : span R (LinearMap.range i : Set M) = ⊤)
    (hN : span R (LinearMap.range j : Set N) = ⊤)
    (h₁ : ∀ g : Module.Dual S N', ∃ m,
      (p.toDualLeft (i m)).restrictScalars S ∘ₗ j = Algebra.linearMap S R ∘ₗ g)
    (h₂ : ∀ g : Module.Dual S M', ∃ n,
      (p.toDualRight (j n)).restrictScalars S ∘ₗ i = Algebra.linearMap S R ∘ₗ g)
    (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap S R).range) :
    PerfectPairing S M' N' :=
  { toLinearMap := p.restrictScalarsAux i j hp
    bijective_left := ⟨p.restrictScalarsAux_injective i j hi hN hp,
      p.restrictScalarsAux_surjective i j h₁ hp⟩
    bijective_right := ⟨p.flip.restrictScalarsAux_injective j i hj hM (fun m n ↦ hp n m),
      p.flip.restrictScalarsAux_surjective j i h₂ (fun m n ↦ hp n m)⟩}

end RestrictScalars

end CommRing

section Field

variable {K L M N : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  [Module K M] [Module K N] [IsScalarTower K L M]
  (p : PerfectPairing L M N)

/-- If a perfect pairing over a field `L` takes values in a subfield `K` along two `K`-subspaces
whose `L` span is full, then these subspaces induce a `K`-structure in the sense of
[*Algebra I*, Bourbaki : Chapter II, §8.1 Definition 1][bourbaki1989]. -/
lemma exists_basis_basis_of_span_eq_top_of_mem_algebraMap
    (M' : Submodule K M) (N' : Submodule K N)
    (hM : span L (M' : Set M) = ⊤)
    (hN : span L (N' : Set N) = ⊤)
    (hp : ∀ᵉ (x ∈ M') (y ∈ N'), p x y ∈ (algebraMap K L).range) :
    ∃ (n : ℕ) (b : Basis (Fin n) L M) (b' : Basis (Fin n) K M'), ∀ i, b i = b' i := by
  classical
  have : IsReflexive L M := p.reflexive_left
  have : IsReflexive L N := p.reflexive_right
  obtain ⟨v, hv₁, hv₂, hv₃⟩ := exists_linearIndependent L (M' : Set M)
  rw [hM] at hv₂
  let b : Basis _ L M := Basis.mk hv₃ <| by rw [← hv₂, Subtype.range_coe_subtype, Set.setOf_mem_eq]
  have : Fintype v := Set.Finite.fintype <| Module.Finite.finite_basis b
  set v' : v → M' := fun i ↦ ⟨i, hv₁ (Subtype.coe_prop i)⟩
  have hv' : LinearIndependent K v' := by
    replace hv₃ := hv₃.restrict_scalars (R := K) <| by
      simp_rw [← Algebra.algebraMap_eq_smul_one]
      exact FaithfulSMul.algebraMap_injective K L
    rw [show ((↑) : v → M) = M'.subtype ∘ v' by ext; simp [v']] at hv₃
    exact hv₃.of_comp
  suffices span K (Set.range v') = ⊤ by
    let e := (Module.Finite.finite_basis b).equivFin
    let b' : Basis _ K M' := Basis.mk hv' (by rw [this])
    exact ⟨_, b.reindex e, b'.reindex e, fun i ↦ by simp [b, b', v']⟩
  suffices span K v = M' by
    apply Submodule.map_injective_of_injective M'.injective_subtype
    rw [Submodule.map_span, ← Set.image_univ, Set.image_image]
    simpa [v']
  refine le_antisymm (Submodule.span_le.mpr hv₁) fun m hm ↦ ?_
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := exists_linearIndependent L (N' : Set N)
  rw [hN] at hw₂
  let bN : Basis _ L N := Basis.mk hw₃ <| by rw [← hw₂, Subtype.range_coe_subtype, Set.setOf_mem_eq]
  have : Fintype w := Set.Finite.fintype <| Module.Finite.finite_basis bN
  have e : v ≃ w := Fintype.equivOfCardEq <| by rw [← Module.finrank_eq_card_basis b,
    ← Module.finrank_eq_card_basis bN, p.finrank_eq]
  let bM := bN.dualBasis.map p.toDualLeft.symm
  have hbM (j : w) (x : M) (hx : x ∈ M') : bM.repr x j = p x (j : N) := by simp [bM, bN]
  have hj (j : w) : bM.repr m j ∈ (algebraMap K L).range := (hbM _ _ hm) ▸ hp m hm j (hw₁ j.2)
  replace hp (i : w) (j : v) :
      (bN.dualBasis.map p.toDualLeft.symm).toMatrix b i j ∈ (algebraMap K L).fieldRange := by
    simp only [Basis.toMatrix, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
      toDualLeft_apply, Basis.dualBasis_repr]
    exact hp (b j) (by simpa [b] using hv₁ j.2) (bN i) (by simpa [bN] using hw₁ i.2)
  have hA (i j) : b.toMatrix bM i j ∈ (algebraMap K L).range :=
    Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_left e _ (by simp [bM]) hp i j
  have h_span : span K v = span K (Set.range b) := by simp [b]
  rw [h_span, Basis.mem_span_iff_repr_mem, ← Basis.toMatrix_mulVec_repr bM b m]
  exact fun i ↦ Subring.sum_mem _ fun j _ ↦ Subring.mul_mem _ (hA i j) (hj j)

variable {M' N' : Type*}
  [AddCommGroup M'] [AddCommGroup N'] [Module K M'] [Module K N'] [IsScalarTower K L N]
  (i : M' →ₗ[K] M) (j : N' →ₗ[K] N) (hi : Injective i) (hj : Injective j)

/-- An auxiliary definition used only to simplify the construction of the more general definition
`PerfectPairing.restrictScalarsField`. -/
private def restrictScalarsFieldAux
    (hM : span L (LinearMap.range i : Set M) = ⊤)
    (hN : span L (LinearMap.range j : Set N) = ⊤)
    (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap K L).range) :
    PerfectPairing K M' N' := by
  suffices FiniteDimensional K M' from mkOfInjective _ (p.restrictScalarsAux_injective i j hi hN hp)
    (p.flip.restrictScalarsAux_injective j i hj hM (fun m n ↦ hp n m))
  obtain ⟨n, -, b', -⟩ := p.exists_basis_basis_of_span_eq_top_of_mem_algebraMap _ _ hM hN <| by
    rintro - ⟨m, rfl⟩ - ⟨n, rfl⟩
    exact hp m n
  have : FiniteDimensional K (LinearMap.range i) := FiniteDimensional.of_fintype_basis b'
  exact Finite.equiv (LinearEquiv.ofInjective i hi).symm

/-- Simultaneously restrict both the domains and scalars of a perfect pairing with coefficients in a
field. -/
def restrictScalarsField
    (hij : p.IsPerfectCompl (span L <| LinearMap.range i) (span L <| LinearMap.range j))
    (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap K L).range) :
    PerfectPairing K M' N' := by
  letI P : PerfectPairing L (span L <| LinearMap.range i) (span L <| LinearMap.range j) :=
    p.restrict (Submodule.subtype _) (Submodule.subtype _) (by simp) (by simp) (by simpa)
  exact P.restrictScalarsFieldAux
    ((LinearMap.range i).inclusionSpan L ∘ₗ i.rangeRestrict)
    ((LinearMap.range j).inclusionSpan L ∘ₗ j.rangeRestrict)
    (((LinearMap.range i).injective_inclusionSpan L).comp (by simpa))
    (((LinearMap.range j).injective_inclusionSpan L).comp (by simpa))
    (by rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_rangeRestrict _)]
        exact (LinearMap.range i).span_range_inclusionSpan L)
    (by rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_rangeRestrict _)]
        exact (LinearMap.range j).span_range_inclusionSpan L)
    (fun x y ↦ LinearMap.BilinMap.apply_apply_mem_of_mem_span
      (LinearMap.range <| Algebra.linearMap K L) (range i) (range j)
      ((LinearMap.restrictScalarsₗ K L _ _ _).comp (p.toLinearMap.restrictScalars K))
      (by simpa) (i x) (j y) (subset_span (mem_range_self x)) (subset_span (mem_range_self y)))

@[simp] lemma restrictScalarsField_apply_apply
    (hij : p.IsPerfectCompl (span L <| LinearMap.range i) (span L <| LinearMap.range j))
    (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap K L).range)
    (x : M') (y : N') :
    algebraMap K L (p.restrictScalarsField i j hi hj hij hp x y) = p (i x) (j y) :=
  LinearMap.restrictScalarsRange₂_apply i j (Algebra.linearMap K L)
    (FaithfulSMul.algebraMap_injective K L) p.toLinearMap hp x y

end Field

end PerfectPairing
