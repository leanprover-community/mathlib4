/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Projection

/-!
# Bases in a vector space

This file provides results for bases of a vector space.

Some of these results should be merged with the results on free modules.
We state these results in a separate file to the results on modules to avoid an
import cycle.

## Main statements

* `Basis.ofVectorSpace` states that every vector space has a basis.
* `Module.Free.of_divisionRing` states that every vector space is a free module.

## Tags

basis, bases

-/

open Function Set Submodule

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']
variable {v : ι → V} {s t : Set V} {x y z : V}

open Submodule

namespace Basis

section ExistsBasis

/-- If `s` is a linear independent set of vectors, we can extend it to a basis. -/
noncomputable def extend (hs : LinearIndependent K ((↑) : s → V)) :
    Basis (hs.extend (subset_univ s)) K V :=
  Basis.mk
    (@LinearIndependent.restrict_of_comp_subtype _ _ _ id _ _ _ _ (hs.linearIndependent_extend _))
    (SetLike.coe_subset_coe.mp <| by simpa using hs.subset_span_extend (subset_univ s))

theorem extend_apply_self (hs : LinearIndependent K ((↑) : s → V)) (x : hs.extend _) :
    Basis.extend hs x = x :=
  Basis.mk_apply _ _ _

@[simp]
theorem coe_extend (hs : LinearIndependent K ((↑) : s → V)) : ⇑(Basis.extend hs) = ((↑) : _ → _) :=
  funext (extend_apply_self hs)

theorem range_extend (hs : LinearIndependent K ((↑) : s → V)) :
    range (Basis.extend hs) = hs.extend (subset_univ _) := by
  rw [coe_extend, Subtype.range_coe_subtype, setOf_mem_eq]

-- Porting note: adding this to make the statement of `subExtend` more readable
/-- Auxiliary definition: the index for the new basis vectors in `Basis.sumExtend`.

The specific value of this definition should be considered an implementation detail.
-/
def sumExtendIndex (hs : LinearIndependent K v) : Set V :=
  LinearIndependent.extend hs.to_subtype_range (subset_univ _) \ range v

/-- If `v` is a linear independent family of vectors, extend it to a basis indexed by a sum type. -/
noncomputable def sumExtend (hs : LinearIndependent K v) : Basis (ι ⊕ sumExtendIndex hs) K V :=
  let s := Set.range v
  let e : ι ≃ s := Equiv.ofInjective v hs.injective
  let b := hs.to_subtype_range.extend (subset_univ (Set.range v))
  (Basis.extend hs.to_subtype_range).reindex <|
    Equiv.symm <|
      calc
        ι ⊕ (b \ s : Set V) ≃ s ⊕ (b \ s : Set V) := Equiv.sumCongr e (Equiv.refl _)
        _ ≃ b :=
          haveI := Classical.decPred (· ∈ s)
          Equiv.Set.sumDiffSubset (hs.to_subtype_range.subset_extend _)

theorem subset_extend {s : Set V} (hs : LinearIndependent K ((↑) : s → V)) :
    s ⊆ hs.extend (Set.subset_univ _) :=
  hs.subset_extend _

/-- If `s` is a family of linearly independent vectors contained in a set `t` spanning `V`,
then one can get a basis of `V` containing `s` and contained in `t`. -/
noncomputable def extendLe (hs : LinearIndependent K ((↑) : s → V))
    (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
    Basis (hs.extend hst) K V :=
  Basis.mk
    (@LinearIndependent.restrict_of_comp_subtype _ _ _ id _ _ _ _ (hs.linearIndependent_extend _))
    (le_trans ht <| Submodule.span_le.2 <| by simpa using hs.subset_span_extend hst)

theorem extendLe_apply_self (hs : LinearIndependent K ((↑) : s → V))
    (hst : s ⊆ t) (ht : ⊤ ≤ span K t) (x : hs.extend hst) :
    Basis.extendLe hs hst ht x = x :=
  Basis.mk_apply _ _ _

@[simp]
theorem coe_extendLe (hs : LinearIndependent K ((↑) : s → V))
    (hst : s ⊆ t) (ht : ⊤ ≤ span K t) : ⇑(Basis.extendLe hs hst ht) = ((↑) : _ → _) :=
  funext (extendLe_apply_self hs hst ht)

theorem range_extendLe (hs : LinearIndependent K ((↑) : s → V))
    (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
    range (Basis.extendLe hs hst ht) = hs.extend hst := by
  rw [coe_extendLe, Subtype.range_coe_subtype, setOf_mem_eq]

theorem subset_extendLe (hs : LinearIndependent K ((↑) : s → V))
    (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
    s ⊆ range (Basis.extendLe hs hst ht) :=
  (range_extendLe hs hst ht).symm ▸ hs.subset_extend hst

theorem extendLe_subset (hs : LinearIndependent K ((↑) : s → V))
    (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
    range (Basis.extendLe hs hst ht) ⊆ t :=
  (range_extendLe hs hst ht).symm ▸ hs.extend_subset hst

/-- If a set `s` spans the space, this is a basis contained in `s`. -/
noncomputable def ofSpan (hs : ⊤ ≤ span K s) :
    Basis ((linearIndependent_empty K V).extend (empty_subset s)) K V :=
  extendLe (linearIndependent_empty K V) (empty_subset s) hs

theorem ofSpan_apply_self (hs : ⊤ ≤ span K s)
    (x : (linearIndependent_empty K V).extend (empty_subset s)) :
    Basis.ofSpan hs x = x :=
  extendLe_apply_self (linearIndependent_empty K V) (empty_subset s) hs x

@[simp]
theorem coe_ofSpan (hs : ⊤ ≤ span K s) : ⇑(ofSpan hs) = ((↑) : _ → _) :=
  funext (ofSpan_apply_self hs)

theorem range_ofSpan (hs : ⊤ ≤ span K s) :
    range (ofSpan hs) = (linearIndependent_empty K V).extend (empty_subset s) := by
  rw [coe_ofSpan, Subtype.range_coe_subtype, setOf_mem_eq]

theorem ofSpan_subset (hs : ⊤ ≤ span K s) : range (ofSpan hs) ⊆ s :=
  extendLe_subset (linearIndependent_empty K V) (empty_subset s) hs

section

variable (K V)

/-- A set used to index `Basis.ofVectorSpace`. -/
noncomputable def ofVectorSpaceIndex : Set V :=
  (linearIndependent_empty K V).extend (subset_univ _)

/-- Each vector space has a basis. -/
noncomputable def ofVectorSpace : Basis (ofVectorSpaceIndex K V) K V :=
  Basis.extend (linearIndependent_empty K V)

@[stacks 09FN "Generalized from fields to division rings."]
instance (priority := 100) _root_.Module.Free.of_divisionRing : Module.Free K V :=
  Module.Free.of_basis (ofVectorSpace K V)

theorem ofVectorSpace_apply_self (x : ofVectorSpaceIndex K V) : ofVectorSpace K V x = x := by
  unfold ofVectorSpace
  exact Basis.mk_apply _ _ _

@[simp]
theorem coe_ofVectorSpace : ⇑(ofVectorSpace K V) = ((↑) : _ → _ ) :=
  funext fun x => ofVectorSpace_apply_self K V x

theorem ofVectorSpaceIndex.linearIndependent :
    LinearIndependent K ((↑) : ofVectorSpaceIndex K V → V) := by
  convert (ofVectorSpace K V).linearIndependent
  ext x
  rw [ofVectorSpace_apply_self]

theorem range_ofVectorSpace : range (ofVectorSpace K V) = ofVectorSpaceIndex K V :=
  range_extend _

theorem exists_basis : ∃ s : Set V, Nonempty (Basis s K V) :=
  ⟨ofVectorSpaceIndex K V, ⟨ofVectorSpace K V⟩⟩

end

end ExistsBasis

end Basis

open Fintype

variable (K V)

theorem VectorSpace.card_fintype [Fintype K] [Fintype V] : ∃ n : ℕ, card V = card K ^ n := by
  classical
  exact ⟨card (Basis.ofVectorSpaceIndex K V), Module.card_fintype (Basis.ofVectorSpace K V)⟩

section AtomsOfSubmoduleLattice

variable {K V}

/-- For a module over a division ring, the span of a nonzero element is an atom of the
lattice of submodules. -/
theorem nonzero_span_atom (v : V) (hv : v ≠ 0) : IsAtom (span K {v} : Submodule K V) := by
  constructor
  · rw [Submodule.ne_bot_iff]
    exact ⟨v, ⟨mem_span_singleton_self v, hv⟩⟩
  · intro T hT
    by_contra h
    apply hT.2
    change span K {v} ≤ T
    simp_rw [span_singleton_le_iff_mem, ← Ne.eq_def, Submodule.ne_bot_iff] at *
    rcases h with ⟨s, ⟨hs, hz⟩⟩
    rcases mem_span_singleton.1 (hT.1 hs) with ⟨a, rfl⟩
    rcases eq_or_ne a 0 with rfl | h
    · simp only [zero_smul, ne_eq, not_true] at hz
    · rwa [T.smul_mem_iff h] at hs

/-- The atoms of the lattice of submodules of a module over a division ring are the
submodules equal to the span of a nonzero element of the module. -/
theorem atom_iff_nonzero_span (W : Submodule K V) :
    IsAtom W ↔ ∃ v ≠ 0, W = span K {v} := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases' h with hbot h
    rcases (Submodule.ne_bot_iff W).1 hbot with ⟨v, ⟨hW, hv⟩⟩
    refine ⟨v, ⟨hv, ?_⟩⟩
    by_contra heq
    specialize h (span K {v})
    rw [span_singleton_eq_bot, lt_iff_le_and_ne] at h
    exact hv (h ⟨(span_singleton_le_iff_mem v W).2 hW, Ne.symm heq⟩)
  · rcases h with ⟨v, ⟨hv, rfl⟩⟩
    exact nonzero_span_atom v hv

/-- The lattice of submodules of a module over a division ring is atomistic. -/
instance : IsAtomistic (Submodule K V) where
  eq_sSup_atoms W := by
    refine ⟨_, submodule_eq_sSup_le_nonzero_spans W, ?_⟩
    rintro _ ⟨w, ⟨_, ⟨hw, rfl⟩⟩⟩
    exact nonzero_span_atom w hw

end AtomsOfSubmoduleLattice

variable {K V}

theorem LinearMap.exists_leftInverse_of_injective (f : V →ₗ[K] V') (hf_inj : LinearMap.ker f = ⊥) :
    ∃ g : V' →ₗ[K] V, g.comp f = LinearMap.id := by
  let B := Basis.ofVectorSpaceIndex K V
  let hB := Basis.ofVectorSpace K V
  have hB₀ : _ := hB.linearIndependent.to_subtype_range
  have : LinearIndependent K (fun x => x : f '' B → V') := by
    have h₁ : LinearIndependent K ((↑) : ↥(f '' Set.range (Basis.ofVectorSpace K V)) → V') :=
      LinearIndependent.image_subtype (f := f) hB₀ (show Disjoint _ _ by simp [hf_inj])
    rwa [Basis.range_ofVectorSpace K V] at h₁
  let C := this.extend (subset_univ _)
  have BC := this.subset_extend (subset_univ _)
  let hC := Basis.extend this
  haveI Vinh : Inhabited V := ⟨0⟩
  refine ⟨(hC.constr ℕ : _ → _) (C.restrict (invFun f)), hB.ext fun b => ?_⟩
  rw [image_subset_iff] at BC
  have fb_eq : f b = hC ⟨f b, BC b.2⟩ := by
    change f b = Basis.extend this _
    simp_rw [Basis.extend_apply_self]
  dsimp []
  rw [Basis.ofVectorSpace_apply_self, fb_eq, hC.constr_basis]
  exact leftInverse_invFun (LinearMap.ker_eq_bot.1 hf_inj) _

theorem Submodule.exists_isCompl (p : Submodule K V) : ∃ q : Submodule K V, IsCompl p q :=
  let ⟨f, hf⟩ := p.subtype.exists_leftInverse_of_injective p.ker_subtype
  ⟨LinearMap.ker f, LinearMap.isCompl_of_proj <| LinearMap.ext_iff.1 hf⟩

instance Submodule.complementedLattice : ComplementedLattice (Submodule K V) :=
  ⟨Submodule.exists_isCompl⟩

/-- Any linear map `f : p →ₗ[K] V'` defined on a subspace `p` can be extended to the whole
space. -/
theorem LinearMap.exists_extend {p : Submodule K V} (f : p →ₗ[K] V') :
    ∃ g : V →ₗ[K] V', g.comp p.subtype = f :=
  let ⟨g, hg⟩ := p.subtype.exists_leftInverse_of_injective p.ker_subtype
  ⟨f.comp g, by rw [LinearMap.comp_assoc, hg, f.comp_id]⟩

open Submodule LinearMap

/-- If `p < ⊤` is a subspace of a vector space `V`, then there exists a nonzero linear map
`f : V →ₗ[K] K` such that `p ≤ ker f`. -/
theorem Submodule.exists_le_ker_of_lt_top (p : Submodule K V) (hp : p < ⊤) :
    ∃ (f : V →ₗ[K] K), f ≠ 0 ∧ p ≤ ker f := by
  rcases SetLike.exists_of_lt hp with ⟨v, -, hpv⟩; clear hp
  rcases (LinearPMap.supSpanSingleton ⟨p, 0⟩ v (1 : K) hpv).toFun.exists_extend with ⟨f, hf⟩
  refine ⟨f, ?_, ?_⟩
  · rintro rfl
    rw [LinearMap.zero_comp] at hf
    have := LinearPMap.supSpanSingleton_apply_mk ⟨p, 0⟩ v (1 : K) hpv 0 p.zero_mem 1
    simpa using (LinearMap.congr_fun hf _).trans this
  · refine fun x hx => mem_ker.2 ?_
    have := LinearPMap.supSpanSingleton_apply_mk ⟨p, 0⟩ v (1 : K) hpv x hx 0
    simpa using (LinearMap.congr_fun hf _).trans this

theorem quotient_prod_linearEquiv (p : Submodule K V) : Nonempty (((V ⧸ p) × p) ≃ₗ[K] V) :=
  let ⟨q, hq⟩ := p.exists_isCompl
  Nonempty.intro <|
    ((quotientEquivOfIsCompl p q hq).prod (LinearEquiv.refl _ _)).trans
      (prodEquivOfIsCompl q p hq.symm)

end DivisionRing
