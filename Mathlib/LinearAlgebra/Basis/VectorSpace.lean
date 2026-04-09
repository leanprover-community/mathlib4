/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Tactic.Field

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

@[expose] public section

open Function Module Set Submodule

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']
variable {v : ι → V} {s t : Set V} {x y z : V}

open Submodule

namespace Module.Basis

section ExistsBasis

/-- If `s` is a linear independent set of vectors, we can extend it to a basis. -/
noncomputable def extend (hs : LinearIndepOn K id s) :
    Basis (hs.extend (subset_univ s)) K V :=
  Basis.mk
    (hs.linearIndepOn_extend _).linearIndependent_restrict
    (SetLike.coe_subset_coe.mp <| by simpa using hs.subset_span_extend (subset_univ s))

theorem extend_apply_self (hs : LinearIndepOn K id s) (x : hs.extend _) : Basis.extend hs x = x :=
  Basis.mk_apply _ _ _

@[simp]
theorem coe_extend (hs : LinearIndepOn K id s) : ⇑(Basis.extend hs) = ((↑) : _ → _) :=
  funext (extend_apply_self hs)

theorem range_extend (hs : LinearIndepOn K id s) :
    range (Basis.extend hs) = hs.extend (subset_univ _) := by
  rw [coe_extend, Subtype.range_coe_subtype, setOf_mem_eq]

/-- Auxiliary definition: the index for the new basis vectors in `Basis.sumExtend`.

The specific value of this definition should be considered an implementation detail. -/
def sumExtendIndex (hs : LinearIndependent K v) : Set V :=
  LinearIndepOn.extend hs.linearIndepOn_id (subset_univ _) \ range v

/-- If `v` is a linear independent family of vectors, extend it to a basis indexed by a sum type. -/
noncomputable def sumExtend (hs : LinearIndependent K v) : Basis (ι ⊕ sumExtendIndex hs) K V :=
  let s := Set.range v
  let e : ι ≃ s := Equiv.ofInjective v hs.injective
  let b := hs.linearIndepOn_id.extend (subset_univ (Set.range v))
  (Basis.extend hs.linearIndepOn_id).reindex <|
    Equiv.symm <|
      calc
        ι ⊕ (b \ s : Set V) ≃ s ⊕ (b \ s : Set V) := Equiv.sumCongr e (Equiv.refl _)
        _ ≃ b :=
          haveI := Classical.decPred (· ∈ s)
          Equiv.Set.sumDiffSubset (hs.linearIndepOn_id.subset_extend _)

theorem subset_extend {s : Set V} (hs : LinearIndepOn K id s) : s ⊆ hs.extend (Set.subset_univ _) :=
  hs.subset_extend _

/-- If `s` is a family of linearly independent vectors contained in a set `t` spanning `V`,
then one can get a basis of `V` containing `s` and contained in `t`. -/
noncomputable def extendLe (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
    Basis (hs.extend hst) K V :=
  Basis.mk
    ((hs.linearIndepOn_extend _).linearIndependent ..)
    (le_trans ht <| Submodule.span_le.2 <| by simpa using hs.subset_span_extend hst)

theorem extendLe_apply_self (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t)
    (x : hs.extend hst) : Basis.extendLe hs hst ht x = x :=
  Basis.mk_apply _ _ _

@[simp]
theorem coe_extendLe (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
    ⇑(Basis.extendLe hs hst ht) = ((↑) : _ → _) :=
  funext (extendLe_apply_self hs hst ht)

theorem range_extendLe (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
    range (Basis.extendLe hs hst ht) = hs.extend hst := by
  rw [coe_extendLe, Subtype.range_coe_subtype, setOf_mem_eq]

theorem subset_extendLe (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
    s ⊆ range (Basis.extendLe hs hst ht) :=
  (range_extendLe hs hst ht).symm ▸ hs.subset_extend hst

theorem extendLe_subset (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
    range (Basis.extendLe hs hst ht) ⊆ t :=
  (range_extendLe hs hst ht).symm ▸ hs.extend_subset hst

/-- If a set `s` spans the space, this is a basis contained in `s`. -/
noncomputable def ofSpan (hs : ⊤ ≤ span K s) :
    Basis ((linearIndepOn_empty K id).extend (empty_subset s)) K V :=
  extendLe (linearIndependent_empty K V) (empty_subset s) hs

theorem ofSpan_apply_self (hs : ⊤ ≤ span K s)
    (x : (linearIndepOn_empty K id).extend (empty_subset s)) :
    Basis.ofSpan hs x = x :=
  extendLe_apply_self (linearIndependent_empty K V) (empty_subset s) hs x

@[simp]
theorem coe_ofSpan (hs : ⊤ ≤ span K s) : ⇑(ofSpan hs) = ((↑) : _ → _) :=
  funext (ofSpan_apply_self hs)

theorem range_ofSpan (hs : ⊤ ≤ span K s) :
    range (ofSpan hs) = (linearIndepOn_empty K id).extend (empty_subset s) := by
  rw [coe_ofSpan, Subtype.range_coe_subtype, setOf_mem_eq]

theorem ofSpan_subset (hs : ⊤ ≤ span K s) : range (ofSpan hs) ⊆ s :=
  extendLe_subset (linearIndependent_empty K V) (empty_subset s) hs

section

variable (K V)

/-- A set used to index `Basis.ofVectorSpace`. -/
noncomputable def ofVectorSpaceIndex : Set V :=
  (linearIndepOn_empty K id).extend (subset_univ _)

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
theorem coe_ofVectorSpace : ⇑(ofVectorSpace K V) = ((↑) : _ → _) :=
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

end Module.Basis

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
  · obtain ⟨hbot, h⟩ := h
    rcases (Submodule.ne_bot_iff W).1 hbot with ⟨v, ⟨hW, hv⟩⟩
    refine ⟨v, ⟨hv, ?_⟩⟩
    by_contra heq
    specialize h (span K {v})
    rw [span_singleton_eq_bot, lt_iff_le_and_ne] at h
    exact hv (h ⟨(span_singleton_le_iff_mem v W).2 hW, Ne.symm heq⟩)
  · rcases h with ⟨v, ⟨hv, rfl⟩⟩
    exact nonzero_span_atom v hv

/-- The lattice of submodules of a module over a division ring is atomistic. -/
instance : IsAtomistic (Submodule K V) :=
  CompleteLattice.isAtomistic_iff.2 fun W => by
    refine ⟨_, submodule_eq_sSup_le_nonzero_spans W, ?_⟩
    rintro _ ⟨w, ⟨_, ⟨hw, rfl⟩⟩⟩
    exact nonzero_span_atom w hw

end AtomsOfSubmoduleLattice

variable {K V}

theorem LinearMap.exists_leftInverse_of_injective (f : V →ₗ[K] V') (hf_inj : LinearMap.ker f = ⊥) :
    ∃ g : V' →ₗ[K] V, g.comp f = LinearMap.id := by
  let B := Basis.ofVectorSpaceIndex K V
  let hB := Basis.ofVectorSpace K V
  have hB₀ : _ := hB.linearIndependent.linearIndepOn_id
  have : LinearIndepOn K _root_.id (f '' B) := by
    have h₁ : LinearIndepOn K _root_.id (f '' Set.range (Basis.ofVectorSpace K V)) :=
      LinearIndepOn.image (f := f) hB₀ (show Disjoint _ _ by simp [hf_inj])
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
  dsimp
  rw [Basis.ofVectorSpace_apply_self, fb_eq, hC.constr_basis]
  exact leftInverse_invFun (LinearMap.ker_eq_bot.1 hf_inj) _

open scoped Classical in
/-- The left inverse of `f : E →ₗ[𝕜] F`.

If `f` is not injective, then we use the junk value `0`. -/
noncomputable
def LinearMap.leftInverse (f : V →ₗ[K] V') : V' →ₗ[K] V :=
  if h_inj : LinearMap.ker f = ⊥ then
  (f.exists_leftInverse_of_injective h_inj).choose
  else 0

theorem LinearMap.leftInverse_comp_of_inj {f : V →ₗ[K] V'} (h_inj : LinearMap.ker f = ⊥) :
    f.leftInverse ∘ₗ f = LinearMap.id := by
  simpa [leftInverse, h_inj] using (f.exists_leftInverse_of_injective h_inj).choose_spec

/-- If `f` is injective, then the left inverse composed with `f` is the identity. -/
theorem LinearMap.leftInverse_apply_of_inj {f : V →ₗ[K] V'} (h_inj : LinearMap.ker f = ⊥) (x : V) :
    f.leftInverse (f x) = x :=
  LinearMap.ext_iff.mp (f.leftInverse_comp_of_inj h_inj) x

theorem Submodule.exists_isCompl (p : Submodule K V) : ∃ q : Submodule K V, IsCompl p q :=
  ⟨LinearMap.ker p.subtype.leftInverse,
    LinearMap.isCompl_of_proj <| LinearMap.leftInverse_apply_of_inj p.ker_subtype⟩

instance Submodule.complementedLattice : ComplementedLattice (Submodule K V) :=
  ⟨Submodule.exists_isCompl⟩

/-- Any linear map `f : p →ₗ[K] V'` defined on a subspace `p` can be extended to the whole
space. -/
theorem LinearMap.exists_extend {p : Submodule K V} (f : p →ₗ[K] V') :
    ∃ g : V →ₗ[K] V', g.comp p.subtype = f :=
  let ⟨g, hg⟩ := p.subtype.exists_leftInverse_of_injective p.ker_subtype
  ⟨f.comp g, by rw [LinearMap.comp_assoc, hg, f.comp_id]⟩

theorem LinearMap.exists_extend_of_notMem {p : Submodule K V} {v : V} (f : p →ₗ[K] V')
    (hv : v ∉ p) (y : V') : ∃ g : V →ₗ[K] V', g.comp p.subtype = f ∧ g v = y := by
  rcases (LinearPMap.supSpanSingleton ⟨p, f⟩ v y hv).toFun.exists_extend with ⟨g, hg⟩
  refine ⟨g, ?_, ?_⟩
  · ext x
    have := LinearPMap.supSpanSingleton_apply_mk_of_mem ⟨p, f⟩ y hv x.2
    simpa using congr($hg _).trans this
  · have := LinearPMap.supSpanSingleton_apply_self ⟨p, f⟩ y hv
    simpa using congr($hg _).trans this

open Submodule LinearMap

theorem Submodule.exists_le_ker_of_notMem {p : Submodule K V} {v : V} (hv : v ∉ p) :
    ∃ f : V →ₗ[K] K, f v ≠ 0 ∧ p ≤ ker f := by
  rcases LinearMap.exists_extend_of_notMem (0 : p →ₗ[K] K) hv 1 with ⟨f, hpf, hfv⟩
  refine ⟨f, by simp [hfv], fun x hx ↦ ?_⟩
  simpa using congr($hpf ⟨x, hx⟩)

/-- If `V` and `V'` are nontrivial vector spaces over a field `K`, the space of `K`-linear maps
between them is nontrivial. -/
instance [Nontrivial V] [Nontrivial V'] : Nontrivial (V →ₗ[K] V') := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := exists_ne (0 : V')
  have : v ∉ (⊥ : Submodule K V) := by simp only [mem_bot, hv, not_false_eq_true]
  obtain ⟨g, _, hg⟩ := LinearMap.exists_extend_of_notMem (K := K) 0 this w
  exact ⟨g, 0, DFunLike.ne_iff.mpr ⟨v, by simp_all⟩⟩

/-- If `p < ⊤` is a subspace of a vector space `V`, then there exists a nonzero linear map
`f : V →ₗ[K] K` such that `p ≤ ker f`. -/
theorem Submodule.exists_le_ker_of_lt_top (p : Submodule K V) (hp : p < ⊤) :
    ∃ (f : V →ₗ[K] K), f ≠ 0 ∧ p ≤ ker f := by
  rcases SetLike.exists_of_lt hp with ⟨v, -, hpv⟩
  rcases exists_le_ker_of_notMem hpv with ⟨f, hfv, hpf⟩
  exact ⟨f, ne_of_apply_ne (· v) hfv, hpf⟩

theorem quotient_prod_linearEquiv (p : Submodule K V) : Nonempty (((V ⧸ p) × p) ≃ₗ[K] V) :=
  let ⟨q, hq⟩ := p.exists_isCompl
  Nonempty.intro <|
    ((quotientEquivOfIsCompl p q hq).prodCongr (LinearEquiv.refl _ _)).trans
      (prodEquivOfIsCompl q p hq.symm)

end DivisionRing

section Field

open Submodule LinearMap Module

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable {f : V →ₗ[K] K} {v : V}

/-- In a vector space, given a nonzero linear form `f`,
a nonzero vector `v` such that `f v ≠ 0`,
there exists a basis `b` with an index `i`
such that `v = b i` and `f = (f v) • b.coord i`. -/
theorem exists_basis_of_pairing_ne_zero
    (hfv : f v ≠ 0) :
    ∃ (n : Set V) (b : Module.Basis n K V) (i : n),
      v = b i ∧ f = (f v) • b.coord i := by
  set b₁ := Basis.ofVectorSpace K (ker f)
  set s : Set V := (ker f).subtype '' Set.range b₁
  have hs : span K s = ker f := by
    simp only [s, span_image]
    simp
  set n := insert v s
  have H₁ : LinearIndepOn K _root_.id n := by
    apply LinearIndepOn.id_insert
    · apply LinearIndepOn.image
      · exact b₁.linearIndependent.linearIndepOn_id
      · simp
    · simp [hs, hfv]
  have H₂ : ⊤ ≤ span K n := by
    rintro x -
    simp only [n, mem_span_insert']
    use -f x / f v
    simp only [hs, mem_ker, map_add, map_smul, smul_eq_mul]
    field
  set b := Basis.mk H₁ (by simpa using H₂)
  set i : n := ⟨v, s.mem_insert v⟩
  have hi : b i = v := by simp [b, i]
  refine ⟨n, b, i, by simp [b, i], ?_⟩
  rw [← hi]
  apply b.ext
  intro j
  by_cases h : i = j
  · simp [h]
  · suffices f (b j) = 0 by
      simp [Finsupp.single_eq_of_ne h, this]
    rw [← mem_ker, ← hs, Basis.coe_mk]
    apply subset_span
    apply Or.resolve_left (Set.mem_insert_iff.mpr j.prop)
    simp [← hi, b, Subtype.coe_inj, Ne.symm h]

/-- In a vector space, given a nonzero linear form `f`,
a nonzero vector `v` such that `f v = 0`,
there exists a basis `b` with two distinct indices `i`, `j`
such that `v = b i` and `f = b.coord j`. -/
theorem exists_basis_of_pairing_eq_zero
    (hfv : f v = 0) (hf : f ≠ 0) (hv : v ≠ 0) :
    ∃ (n : Set V) (b : Basis n K V) (i j : n),
      i ≠ j ∧ v = b i ∧ f = b.coord j := by
  lift v to ker f using hfv
  have : LinearIndepOn K _root_.id {v} := by simpa using hv
  set b₁ : Basis _ K (ker f) := .extend this
  obtain ⟨w, hw⟩ : ∃ w, f w = 1 := by
    simp only [ne_eq, DFunLike.ext_iff, not_forall] at hf
    rcases hf with ⟨w, hw⟩
    use (f w)⁻¹ • w
    simp_all
  set s : Set V := (ker f).subtype '' Set.range b₁
  have hs : span K s = ker f := by
    simp only [s, span_image]
    simp
  have hvs : ↑v ∈ s := by
    refine ⟨v, ?_, by simp⟩
    simp [b₁, this.subset_extend _ _]
  set n := insert w s
  have H₁ : LinearIndepOn K _root_.id n := by
    apply LinearIndepOn.id_insert
    · apply LinearIndepOn.image
      · exact b₁.linearIndependent.linearIndepOn_id
      · simp
    · simp [hs, hw]
  have H₂ : ⊤ ≤ span K n := by
    rintro x -
    simp only [n, mem_span_insert']
    use -f x
    simp [hs, hw]
  set b := Basis.mk H₁ (by simpa using H₂)
  refine ⟨n, b, ⟨v, by simp [n, hvs]⟩, ⟨w, by simp [n]⟩, ?_, by simp [b], ?_⟩
  · apply_fun (f ∘ (↑))
    simp [hw]
  · apply b.ext
    intro i
    rw [Basis.coord_apply, Basis.repr_self]
    simp only [b, Basis.mk_apply]
    rcases i with ⟨x, rfl | ⟨x, hx, rfl⟩⟩
    · simp [hw]
    · suffices x ≠ w by simp [this]
      apply_fun f
      simp [hw]

end Field
