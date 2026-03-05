/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.Order.Extension.Well
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# Constructs a basis for exterior powers
-/

@[expose] public section

variable {R K M E : Type*} {n : ℕ}
  [CommRing R] [Field K] [AddCommGroup M] [Module R M] [AddCommGroup E] [Module K E]

open BigOperators

namespace exteriorPower

/-! Finiteness of the exterior power. -/

/-- The `n`th exterior power of a finite module is a finite module. -/
instance instFinite [Module.Finite R M] : Module.Finite R (⋀[R]^n M) := by
  rw [Module.Finite.iff_fg, ExteriorAlgebra.exteriorPower, LinearMap.range_eq_map]
  exact Submodule.FG.pow (Submodule.FG.map _ Module.Finite.fg_top) n

/-! We construct a basis of `⋀[R]^n M` from a basis of `M`. -/

open Module Set Set.powersetCard

variable (R n)

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `s` is a finset of
`I` of cardinality `n`, then we get a linear form on the `n`th exterior power of `M` by
applying the `exteriorPower.linearForm` construction to the family of linear forms
given by the coordinates of `b` indexed by elements of `s` (ordered using the given order on
`I`). -/
noncomputable def ιMultiDual {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : powersetCard I n) : Module.Dual R (⋀[R]^n M) :=
  pairingDual R M n (ιMulti_family R n b.coord s)

@[simp]
lemma ιMultiDual_apply_ιMulti {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : powersetCard I n) (v : Fin n → M) :
    ιMultiDual R n b s (ιMulti R n v) =
    (Matrix.of fun i j => b.coord (powersetCard.ofFinEmbEquiv.symm s j) (v i)).det := by
  simp [ιMultiDual, ιMulti_family, pairingDual_ιMulti_ιMulti]

/-- Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a finset of `I`
of cardinality `n`. If we apply the linear form on `⋀[R]^n M` defined by `b` and `s`
to the exterior product of the `b i` for `i ∈ s`, then we get `1`. -/
lemma ιMultiDual_apply_diag {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : powersetCard I n) :
    ιMultiDual R n b s (ιMulti_family R n b s) = 1 := by
  rw [ιMulti_family, ιMultiDual_apply_ιMulti]
  suffices Matrix.of (fun i j => b.coord (powersetCard.ofFinEmbEquiv.symm s j)
    (b (powersetCard.ofFinEmbEquiv.symm s i))) = 1 by
    simp_rw [Function.comp_apply, this, Matrix.det_one]
  ext
  simp [Matrix.one_apply, Finsupp.single_apply]

/-- Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a finset of `I`
of cardinality `n`. Let `t` be a finset of `I` of cardinality `n` such that `s ≠ t`. If we apply
the linear form on `⋀[R]^n M` defined by `b` and `s` to the exterior product of the
`b i` for `i ∈ t`, then we get `0`. -/
lemma ιMultiDual_apply_nondiag {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s t : powersetCard I n) (hst : s ≠ t) :
    ιMultiDual R n b s (ιMulti_family R n b t) = 0 := by
  rw [ιMulti_family, ιMultiDual_apply_ιMulti]
  obtain ⟨i, his, hit⟩ := (exists_mem_notMem_iff_ne s t).mp hst
  obtain ⟨k, rfl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr his
  apply Matrix.det_eq_zero_of_column_eq_zero k
  simp_rw [Matrix.of_apply, Basis.coord_apply, Function.comp_apply, Basis.repr_self]
  intro j
  apply Finsupp.single_eq_of_ne
  by_contra! h
  apply hit
  rw [h, powersetCard.ofFinEmbEquiv_symm_apply, ← powersetCard.mem_coe_iff]
  exact Finset.orderEmbOfFin_mem t.val t.prop j

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), then the family
`exteriorPower.ιMulti R n b` of the `n`-fold exterior products of its elements is linearly
independent in the `n`th exterior power of `M`. -/
lemma ιMulti_family_linearIndependent_ofBasis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    LinearIndependent R (ιMulti_family R n b) :=
  LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun s ↦ ιMultiDual R n b s)
    (fun _ _ h => ιMultiDual_apply_nondiag R n b _ _ h)
    (fun _ => ιMultiDual_apply_diag _ _ _ _)

variable {R} in
/-- If `b` is a basis of `M` (indexed by a linearly ordered type), the basis of the `n`th
exterior power of `M` formed by the `n`-fold exterior products of elements of `b`. -/
noncomputable def _root_.Module.Basis.exteriorPower {I : Type*} [LinearOrder I] (b : Basis I R M) :
    Basis (powersetCard I n) R (⋀[R]^n M) :=
  Basis.mk (ιMulti_family_linearIndependent_ofBasis _ _ _)
    (eq_top_iff.mp <| ιMulti_family_span_of_span R b.span_eq)

@[simp]
lemma coe_basis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    DFunLike.coe (b.exteriorPower n) = ιMulti_family R n b :=
  Basis.coe_mk _ _

lemma basis_apply {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n) :
    b.exteriorPower n s = ιMulti_family R n b s := by
  rw [coe_basis]

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `B` is the corresponding
basis of the `n`th exterior power of `M`, indexed by the set of finsets `s` of `I` of cardinality
`n`, then the coordinate function of `B` at `s` is the linear form on the `n`th exterior power
defined by `b` and `s` in `exteriorPower.ιMultiDual`. -/
lemma basis_coord {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n) :
    Basis.coord (b.exteriorPower n) s = ιMultiDual R n b s := by
  apply LinearMap.ext_on (ιMulti_family_span_of_span R (Basis.span_eq b))
  rintro x ⟨t, rfl⟩
  rw [Basis.coord_apply]
  by_cases! hst : s = t
  · rw [hst, ιMultiDual_apply_diag, ← basis_apply, Basis.repr_self, Finsupp.single_eq_same]
  · rw [ιMultiDual_apply_nondiag R n b s t hst, ← basis_apply, Basis.repr_self,
      Finsupp.single_eq_of_ne hst]

lemma basis_repr_apply {I : Type*} [LinearOrder I] (b : Basis I R M) (x : ⋀[R]^n M)
    (s : powersetCard I n) :
    Basis.repr (b.exteriorPower n) x s = ιMultiDual R n b s x := by
  simpa [← Basis.coord_apply] using LinearMap.congr_fun (basis_coord R n b s) x

@[simp]
lemma basis_repr_self {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n) :
    Basis.repr (b.exteriorPower n) (ιMulti_family R n b s) s = 1 := by
  simpa [basis_repr_apply] using ιMultiDual_apply_diag R n b s

@[simp]
lemma basis_repr_ne {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s t : powersetCard I n} (hst : s ≠ t) :
    Basis.repr (b.exteriorPower n) (ιMulti_family R n b s) t = 0 := by
  simpa [basis_repr_apply] using ιMultiDual_apply_nondiag R n b t s hst.symm

lemma basis_repr {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n) :
    Basis.repr (b.exteriorPower n) (ιMulti_family R n b s) = Finsupp.single s 1 := by
  ext t
  by_cases hst : s = t <;> simp [hst]

/-! ### Freeness and dimension of `⋀[R]^n M. -/

/-- If `M` is a free module, then so is its `n`th exterior power. -/
instance instFree [Module.Free R M] : Module.Free R (⋀[R]^n M) :=
  have ⟨I, b⟩ := Module.Free.exists_basis R M
  letI : LinearOrder I := IsWellFounded.wellOrderExtension emptyWf.rel
  Module.Free.of_basis (b.exteriorPower n)

variable [Nontrivial R]

/-- If `R` is non-trivial and `M` is finite free of rank `r`, then
the `n`th exterior power of `M` is of finrank `Nat.choose r n`. -/
lemma finrank_eq [Module.Free R M] [Module.Finite R M] :
    Module.finrank R (⋀[R]^n M) = Nat.choose (Module.finrank R M) n := by
  letI : LinearOrder (Module.Free.ChooseBasisIndex R M) :=
    IsWellFounded.wellOrderExtension emptyWf.rel
  let B := (Module.Free.chooseBasis R M).exteriorPower n
  rw [Module.finrank_eq_card_basis (Module.Free.chooseBasis R M), Module.finrank_eq_card_basis B,
    Fintype.card_eq_nat_card, powersetCard.card, Fintype.card_eq_nat_card]

/-! Results that only hold over a field. -/

/-- If `v` is a linearly independent family of vectors (indexed by a linearly ordered type),
then the family of its `n`-fold exterior products is also linearly independent. -/
lemma ιMulti_family_linearIndependent_field {I : Type*} [LinearOrder I] {v : I → E}
    (hv : LinearIndependent K v) : LinearIndependent K (ιMulti_family K n v) := by
  let W := Submodule.span K (Set.range v)
  suffices ∃ b : Basis I K W, v = W.subtype ∘ b by
    obtain ⟨b, hb⟩ := this
    rw [hb, ← map_comp_ιMulti_family]
    exact LinearIndependent.map' (coe_basis K n b ▸ (b.exteriorPower n).linearIndependent)
      _ (LinearMap.ker_eq_bot.mpr (map_injective_field (Submodule.subtype_injective _)))
  use Module.Basis.span hv
  ext i
  rw [Submodule.coe_subtype, Function.comp_apply, Basis.span_apply]

end exteriorPower

section

universe u v

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

namespace exteriorPower

lemma span_ιMulti_orderEmbedding_of_span_eq_top {ι : Type*} [LinearOrder ι] {g : ι → M}
    (hg : Submodule.span R (Set.range g) = ⊤) (n : ℕ) :
    Submodule.span R (Set.range (fun (x : Fin n ↪o ι) ↦ ιMulti R _ (g ∘ x))) = ⊤ := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Given a linearly ordered basis `b : Module.Basis ι R M`, the `n`th exterior power `⋀[R]^n M`
has a basis indexed by order embeddings `Fin n ↪o ι`. -/
noncomputable def basis {ι : Type*} [LinearOrder ι] (b : Module.Basis ι R M) (n : ℕ) :
    Module.Basis (Fin n ↪o ι) R (⋀[R]^n M) := by
  let e : (Fin n ↪o ι) → ⋀[R]^n M := fun a ↦ ιMulti R n (fun i ↦ b (a i))
  refine Module.Basis.mk (v := e) ?_ ?_
  · refine (linearIndependent_iff).2 fun l hl ↦ Finsupp.ext fun a0 ↦ ?_
    have h₁ (i : ι) : b.coord i (b i) = (1 : R) := by simp [Module.Basis.coord]
    have h₀ (i j : ι) (hij : i ≠ j) : b.coord i (b j) = (0 : R) := by simp [Module.Basis.coord, hij]
    let φ : ⋀[R]^n M →ₗ[R] R := pairingDual R M n (ιMulti R n (fun i ↦ b.coord (a0 i)))
    have hx : φ ((Finsupp.linearCombination R e) l) = 0 := by simpa using congr(φ $hl)
    have hx' : φ ((Finsupp.linearCombination R e) l) = l a0 := by
      simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul]
      refine (Finsupp.sum_eq_single a0 ?_ fun ha0 ↦ by simp).trans ?_
      · intro a ha hne
        have : φ (e a) = 0 := pairingDual_apply_apply_eq_one_zero b b.coord h₀ n a0 a hne.symm
        simp [this]
      · have : φ (e a0) = 1 := pairingDual_apply_apply_eq_one b b.coord h₁ h₀ n a0
        simp [this, smul_eq_mul]
    exact hx'.symm.trans hx
  · let S : Submodule R (⋀[R]^n M) := Submodule.span R (Set.range e)
    have mem_S_of_injective (v : Fin n → ι) (hv : Function.Injective v) :
        ιMulti R n (b ∘ v) ∈ S := by
      let σ : Equiv.Perm (Fin n) := Tuple.sort v
      have hmono : Monotone (v ∘ σ) := Tuple.monotone_sort v
      have hinj : Function.Injective (v ∘ σ) := hv.comp σ.injective
      let a : Fin n ↪o ι := OrderEmbedding.ofStrictMono (v ∘ σ) (hmono.strictMono_of_injective hinj)
      have hperm : ιMulti R n (b ∘ v) = Equiv.Perm.sign σ • ιMulti R n (b ∘ a) := by
        rw [← Equiv.Perm.sign_inv]
        convert AlternatingMap.map_perm (ιMulti R n) (b ∘ a) σ⁻¹
        simp [a, Function.comp_assoc]
      rw [hperm]
      exact S.smul_mem _ (Submodule.subset_span ⟨a, rfl⟩)
    let ψ : M [⋀^Fin n]→ₗ[R] (⋀[R]^n M ⧸ S) := S.mkQ.compAlternatingMap (ιMulti R n)
    have hψ : ψ = 0 := by
      refine Module.Basis.ext_alternating b fun v hv ↦ ?_
      simpa [ψ] using (Submodule.Quotient.mk_eq_zero S).2 (mem_S_of_injective v hv)
    have hrange : Set.range (ιMulti R n (M := M)) ⊆ S := by
      rintro _ ⟨m, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero S).1 (show ψ m = 0 from by simp [hψ])
    simpa [S, ιMulti_span R n M] using Submodule.span_le.mpr hrange

end exteriorPower

lemma subsingleton_of_card_generators_le {ι : Type*} [Finite ι] (g : ι → M)
    (hg : Submodule.span R (Set.range g) = ⊤) (i : ℕ) (hi : Nat.card ι < i) :
    Subsingleton (⋀[R]^i M) := by
  letI : Fintype ι := Fintype.ofFinite ι
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hcard : Fintype.card ι < i := by simpa [Nat.card_eq_fintype_card] using hi
  have hempty : IsEmpty (Fin i ↪o ι) := by
    refine ⟨fun f ↦ ?_⟩
    absurd f.injective
    contrapose hcard
    simpa using Fintype.card_le_of_injective f ‹_›
  have hbotTop : (⊥ : Submodule R (⋀[R]^i M)) = ⊤ := by
    rw [← exteriorPower.span_ιMulti_orderEmbedding_of_span_eq_top (R := R) (M := M) hg i]
    convert Submodule.span_empty.symm
    exact Set.range_eq_empty_iff.mpr hempty
  exact (Submodule.subsingleton_iff R).mp <| (subsingleton_iff_bot_eq_top).mp hbotTop

end
