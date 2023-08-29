/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
import Mathlib.LinearAlgebra.Basis
import Mathlib.LinearAlgebra.FreeModule.Basic

#align_import linear_algebra.basis from "leanprover-community/mathlib"@"13bce9a6b6c44f6b4c91ac1c1d2a816e2533d395"

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

open BigOperators

set_option autoImplicit false
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
                                     -- 🎉 no goals
#align basis.extend Basis.extend

theorem extend_apply_self (hs : LinearIndependent K ((↑) : s → V)) (x : hs.extend _) :
    Basis.extend hs x = x :=
  Basis.mk_apply _ _ _
#align basis.extend_apply_self Basis.extend_apply_self

@[simp]
theorem coe_extend (hs : LinearIndependent K ((↑) : s → V)) : ⇑(Basis.extend hs) = ((↑) : _ → _) :=
  funext (extend_apply_self hs)
#align basis.coe_extend Basis.coe_extend

theorem range_extend (hs : LinearIndependent K ((↑) : s → V)) :
    range (Basis.extend hs) = hs.extend (subset_univ _) := by
  rw [coe_extend, Subtype.range_coe_subtype, setOf_mem_eq]
  -- 🎉 no goals
#align basis.range_extend Basis.range_extend

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
        Sum ι (b \ s : Set V) ≃ Sum s (b \ s : Set V) := Equiv.sumCongr e (Equiv.refl _)
        _ ≃ b :=
          haveI := Classical.decPred (· ∈ s)
          Equiv.Set.sumDiffSubset (hs.to_subtype_range.subset_extend _)
#align basis.sum_extend Basis.sumExtend

theorem subset_extend {s : Set V} (hs : LinearIndependent K ((↑) : s → V)) :
    s ⊆ hs.extend (Set.subset_univ _) :=
  hs.subset_extend _
#align basis.subset_extend Basis.subset_extend

section

variable (K V)

/-- A set used to index `Basis.ofVectorSpace`. -/
noncomputable def ofVectorSpaceIndex : Set V :=
  (linearIndependent_empty K V).extend (subset_univ _)
#align basis.of_vector_space_index Basis.ofVectorSpaceIndex

/-- Each vector space has a basis. -/
noncomputable def ofVectorSpace : Basis (ofVectorSpaceIndex K V) K V :=
  Basis.extend (linearIndependent_empty K V)
#align basis.of_vector_space Basis.ofVectorSpace

instance (priority := 100) _root_.Module.Free.of_divisionRing : Module.Free K V :=
  Module.Free.of_basis (ofVectorSpace K V)
#align module.free.of_division_ring Module.Free.of_divisionRing

theorem ofVectorSpace_apply_self (x : ofVectorSpaceIndex K V) : ofVectorSpace K V x = x := by
  unfold ofVectorSpace
  -- ⊢ ↑(extend (_ : LinearIndependent K fun x => ↑x)) x = ↑x
  exact Basis.mk_apply _ _ _
  -- 🎉 no goals
#align basis.of_vector_space_apply_self Basis.ofVectorSpace_apply_self

@[simp]
theorem coe_ofVectorSpace : ⇑(ofVectorSpace K V) = ((↑) : _ → _ ) :=
  funext fun x => ofVectorSpace_apply_self K V x
#align basis.coe_of_vector_space Basis.coe_ofVectorSpace

theorem ofVectorSpaceIndex.linearIndependent :
    LinearIndependent K ((↑) : ofVectorSpaceIndex K V → V) := by
  convert (ofVectorSpace K V).linearIndependent
  -- ⊢ Subtype.val = ↑(ofVectorSpace K V)
  ext x
  -- ⊢ ↑x = ↑(ofVectorSpace K V) x
  rw [ofVectorSpace_apply_self]
  -- 🎉 no goals
#align basis.of_vector_space_index.linear_independent Basis.ofVectorSpaceIndex.linearIndependent

theorem range_ofVectorSpace : range (ofVectorSpace K V) = ofVectorSpaceIndex K V :=
  range_extend _
#align basis.range_of_vector_space Basis.range_ofVectorSpace

theorem exists_basis : ∃ s : Set V, Nonempty (Basis s K V) :=
  ⟨ofVectorSpaceIndex K V, ⟨ofVectorSpace K V⟩⟩
#align basis.exists_basis Basis.exists_basis

end

end ExistsBasis

end Basis

open Fintype

variable (K V)

theorem VectorSpace.card_fintype [Fintype K] [Fintype V] : ∃ n : ℕ, card V = card K ^ n := by
  classical
  exact ⟨card (Basis.ofVectorSpaceIndex K V), Module.card_fintype (Basis.ofVectorSpace K V)⟩
#align vector_space.card_fintype VectorSpace.card_fintype

section AtomsOfSubmoduleLattice

variable {K V}

/-- For a module over a division ring, the span of a nonzero element is an atom of the
lattice of submodules. -/
theorem nonzero_span_atom (v : V) (hv : v ≠ 0) : IsAtom (span K {v} : Submodule K V) := by
  constructor
  -- ⊢ span K {v} ≠ ⊥
  · rw [Submodule.ne_bot_iff]
    -- ⊢ ∃ x, x ∈ span K {v} ∧ x ≠ 0
    exact ⟨v, ⟨mem_span_singleton_self v, hv⟩⟩
    -- 🎉 no goals
  · intro T hT
    -- ⊢ T = ⊥
    by_contra h
    -- ⊢ False
    apply hT.2
    -- ⊢ ↑(span K {v}) ⊆ ↑T
    change span K {v} ≤ T
    -- ⊢ span K {v} ≤ T
    simp_rw [span_singleton_le_iff_mem, ← Ne.def, Submodule.ne_bot_iff] at *
    -- ⊢ v ∈ T
    rcases h with ⟨s, ⟨hs, hz⟩⟩
    -- ⊢ v ∈ T
    rcases mem_span_singleton.1 (hT.1 hs) with ⟨a, rfl⟩
    -- ⊢ v ∈ T
    rcases eq_or_ne a 0 with rfl | h
    -- ⊢ v ∈ T
    · simp only [zero_smul, ne_eq, not_true] at hz
      -- 🎉 no goals
    · rwa [T.smul_mem_iff h] at hs
      -- 🎉 no goals
#align nonzero_span_atom nonzero_span_atom

/-- The atoms of the lattice of submodules of a module over a division ring are the
submodules equal to the span of a nonzero element of the module. -/
theorem atom_iff_nonzero_span (W : Submodule K V) :
    IsAtom W ↔ ∃ (v : V) (_ : v ≠ 0), W = span K {v} := by
  refine' ⟨fun h => _, fun h => _⟩
  -- ⊢ ∃ v x, W = span K {v}
  · cases' h with hbot h
    -- ⊢ ∃ v x, W = span K {v}
    rcases(Submodule.ne_bot_iff W).1 hbot with ⟨v, ⟨hW, hv⟩⟩
    -- ⊢ ∃ v x, W = span K {v}
    refine' ⟨v, ⟨hv, _⟩⟩
    -- ⊢ W = span K {v}
    by_contra heq
    -- ⊢ False
    specialize h (span K {v})
    -- ⊢ False
    rw [span_singleton_eq_bot, lt_iff_le_and_ne] at h
    -- ⊢ False
    exact hv (h ⟨(span_singleton_le_iff_mem v W).2 hW, Ne.symm heq⟩)
    -- 🎉 no goals
  · rcases h with ⟨v, ⟨hv, rfl⟩⟩
    -- ⊢ IsAtom (span K {v})
    exact nonzero_span_atom v hv
    -- 🎉 no goals
#align atom_iff_nonzero_span atom_iff_nonzero_span

/-- The lattice of submodules of a module over a division ring is atomistic. -/
instance : IsAtomistic (Submodule K V) where
  eq_sSup_atoms W := by
    refine ⟨_, submodule_eq_sSup_le_nonzero_spans W, ?_⟩
    -- ⊢ ∀ (a : Submodule K V), a ∈ {T | ∃ m x x, T = span K {m}} → IsAtom a
    rintro _ ⟨w, ⟨_, ⟨hw, rfl⟩⟩⟩
    -- ⊢ IsAtom (span K {w})
    exact nonzero_span_atom w hw
    -- 🎉 no goals

end AtomsOfSubmoduleLattice

variable {K V}

theorem LinearMap.exists_leftInverse_of_injective (f : V →ₗ[K] V') (hf_inj : LinearMap.ker f = ⊥) :
    ∃ g : V' →ₗ[K] V, g.comp f = LinearMap.id := by
  let B := Basis.ofVectorSpaceIndex K V
  -- ⊢ ∃ g, comp g f = id
  let hB := Basis.ofVectorSpace K V
  -- ⊢ ∃ g, comp g f = id
  have hB₀ : _ := hB.linearIndependent.to_subtype_range
  -- ⊢ ∃ g, comp g f = id
  have : LinearIndependent K (fun x => x : f '' B → V') := by
    have h₁ : LinearIndependent K ((↑) : ↥(f '' Set.range (Basis.ofVectorSpace K V)) → V') :=
      @LinearIndependent.image_subtype _ _ _ _ _ _ _ _ _ f hB₀ (show Disjoint _ _ by simp [hf_inj])
    rwa [Basis.range_ofVectorSpace K V] at h₁
  let C := this.extend (subset_univ _)
  -- ⊢ ∃ g, comp g f = id
  have BC := this.subset_extend (subset_univ _)
  -- ⊢ ∃ g, comp g f = id
  let hC := Basis.extend this
  -- ⊢ ∃ g, comp g f = id
  haveI Vinh : Inhabited V := ⟨0⟩
  -- ⊢ ∃ g, comp g f = id
  refine' ⟨(hC.constr ℕ : _ → _) (C.restrict (invFun f)), hB.ext fun b => _⟩
  -- ⊢ ↑(comp (↑(Basis.constr hC ℕ) (Set.restrict C (invFun ↑f))) f) (↑hB b) = ↑id  …
  rw [image_subset_iff] at BC
  -- ⊢ ↑(comp (↑(Basis.constr hC ℕ) (Set.restrict C (invFun ↑f))) f) (↑hB b) = ↑id  …
  have fb_eq : f b = hC ⟨f b, BC b.2⟩ := by
    change f b = Basis.extend this _
    simp_rw [Basis.extend_apply_self]
  dsimp []
  -- ⊢ ↑(↑(Basis.constr (Basis.extend this) ℕ) (Set.restrict (LinearIndependent.ext …
  rw [Basis.ofVectorSpace_apply_self, fb_eq, hC.constr_basis]
  -- ⊢ Set.restrict (LinearIndependent.extend this (_ : ↑f '' Basis.ofVectorSpaceIn …
  exact leftInverse_invFun (LinearMap.ker_eq_bot.1 hf_inj) _
  -- 🎉 no goals
#align linear_map.exists_left_inverse_of_injective LinearMap.exists_leftInverse_of_injective

theorem Submodule.exists_isCompl (p : Submodule K V) : ∃ q : Submodule K V, IsCompl p q :=
  let ⟨f, hf⟩ := p.subtype.exists_leftInverse_of_injective p.ker_subtype
  ⟨LinearMap.ker f, LinearMap.isCompl_of_proj <| LinearMap.ext_iff.1 hf⟩
#align submodule.exists_is_compl Submodule.exists_isCompl

instance Module.Submodule.complementedLattice : ComplementedLattice (Submodule K V) :=
  ⟨Submodule.exists_isCompl⟩
#align module.submodule.complemented_lattice Module.Submodule.complementedLattice

theorem LinearMap.exists_rightInverse_of_surjective (f : V →ₗ[K] V') (hf_surj : range f = ⊤) :
    ∃ g : V' →ₗ[K] V, f.comp g = LinearMap.id := by
  let C := Basis.ofVectorSpaceIndex K V'
  -- ⊢ ∃ g, comp f g = id
  let hC := Basis.ofVectorSpace K V'
  -- ⊢ ∃ g, comp f g = id
  haveI : Inhabited V := ⟨0⟩
  -- ⊢ ∃ g, comp f g = id
  refine' ⟨(hC.constr ℕ : _ → _) (C.restrict (invFun f)), hC.ext fun c => _⟩
  -- ⊢ ↑(comp f (↑(Basis.constr hC ℕ) (Set.restrict C (invFun ↑f)))) (↑hC c) = ↑id  …
  rw [LinearMap.comp_apply, hC.constr_basis]
  -- ⊢ ↑f (Set.restrict C (invFun ↑f) c) = ↑id (↑hC c)
  simp [rightInverse_invFun (LinearMap.range_eq_top.1 hf_surj) c]
  -- 🎉 no goals
#align linear_map.exists_right_inverse_of_surjective LinearMap.exists_rightInverse_of_surjective

/-- Any linear map `f : p →ₗ[K] V'` defined on a subspace `p` can be extended to the whole
space. -/
theorem LinearMap.exists_extend {p : Submodule K V} (f : p →ₗ[K] V') :
    ∃ g : V →ₗ[K] V', g.comp p.subtype = f :=
  let ⟨g, hg⟩ := p.subtype.exists_leftInverse_of_injective p.ker_subtype
  ⟨f.comp g, by rw [LinearMap.comp_assoc, hg, f.comp_id]⟩
                -- 🎉 no goals
#align linear_map.exists_extend LinearMap.exists_extend

open Submodule LinearMap

/-- If `p < ⊤` is a subspace of a vector space `V`, then there exists a nonzero linear map
`f : V →ₗ[K] K` such that `p ≤ ker f`. -/
theorem Submodule.exists_le_ker_of_lt_top (p : Submodule K V) (hp : p < ⊤) :
    ∃ (f : V →ₗ[K] K), f ≠ 0 ∧ p ≤ ker f := by
  rcases SetLike.exists_of_lt hp with ⟨v, -, hpv⟩; clear hp
  -- ⊢ ∃ f, f ≠ 0 ∧ p ≤ ker f
                                                   -- ⊢ ∃ f, f ≠ 0 ∧ p ≤ ker f
  rcases(LinearPMap.supSpanSingleton ⟨p, 0⟩ v (1 : K) hpv).toFun.exists_extend with ⟨f, hf⟩
  -- ⊢ ∃ f, f ≠ 0 ∧ p ≤ ker f
  refine' ⟨f, _, _⟩
  -- ⊢ f ≠ 0
  · rintro rfl
    -- ⊢ False
    rw [LinearMap.zero_comp] at hf
    -- ⊢ False
    have := LinearPMap.supSpanSingleton_apply_mk ⟨p, 0⟩ v (1 : K) hpv 0 p.zero_mem 1
    -- ⊢ False
    simpa using (LinearMap.congr_fun hf _).trans this
    -- 🎉 no goals
  · refine' fun x hx => mem_ker.2 _
    -- ⊢ ↑f x = 0
    have := LinearPMap.supSpanSingleton_apply_mk ⟨p, 0⟩ v (1 : K) hpv x hx 0
    -- ⊢ ↑f x = 0
    simpa using (LinearMap.congr_fun hf _).trans this
    -- 🎉 no goals
#align submodule.exists_le_ker_of_lt_top Submodule.exists_le_ker_of_lt_top

theorem quotient_prod_linearEquiv (p : Submodule K V) : Nonempty (((V ⧸ p) × p) ≃ₗ[K] V) :=
  let ⟨q, hq⟩ := p.exists_isCompl
  Nonempty.intro <|
    ((quotientEquivOfIsCompl p q hq).prod (LinearEquiv.refl _ _)).trans
      (prodEquivOfIsCompl q p hq.symm)
#align quotient_prod_linear_equiv quotient_prod_linearEquiv

end DivisionRing
