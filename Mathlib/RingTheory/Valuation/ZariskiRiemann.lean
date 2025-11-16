/-
Copyright (c) 2025 Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer, Junyan Xu
-/
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Zariski–Riemann space

We show that the Zariski–Riemann space of a finitely generated extension K of
transcendence degree 1 over k (a function field of 1 variable) is proper scheme over k.
This can be considered "resolution of singularities for curves".
-/

variable (R k K : Type*) [CommRing R] [Field k] [Field K] [Algebra R K] [Algebra k K]

open IntermediateField AlgebraicGeometry TopologicalSpace

namespace Algebra

/-! ## Zariski–Riemann space -/

/-- If `K` is an `R`-algebra, `Place R K` is the collection of valuation subrings in `K`
that are `R`-subalgebras. It can be given a locally ringed space structure,
in which setting it is known as the Zariski--Riemann space. -/
@[ext] structure Place extends Subalgebra R K, ValuationSubring K

def genericPoint : Place R K where
  __ : Subalgebra R K := ⊤
  __ : ValuationSubring K := ⊤

instance : SetLike (Place R K) K where
  coe v := v.carrier
  coe_injective' _ _ := Place.ext

instance : SMulMemClass (Place R K) R K where
  smul_mem {v} r _ h := v.toSubalgebra.smul_mem h r

instance : SubringClass (Place R K) K := sorry

instance (v : Place R K) : HasMemOrInvMem v where
  mem_or_inv_mem := v.mem_or_inv_mem'

variable {k K} in
theorem Place.integralClosure_le (v : Place k K) : integralClosure k K ≤ v.toSubalgebra := by
  intro z hz
  by_contra hzv
  have : z⁻¹ ∈ v.toSubalgebra := (v.toValuationSubring.mem_or_inv_mem z).resolve_left hzv
  exact hzv (IsIntegral.mem_of_inv_mem hz this)

instance : TopologicalSpace (Place R K) :=
  -- subbasis consists of sets of all places containing a particular element
  .generateFrom {{v | f ∈ v} | f : K}
/- Later refactoring: consider define topology on `ValuationSubring K`
and take induced topology from there. -/

variable {K} in
/- This is analogous to `D(f)` in Zariski topology because `f ∈ v ↔ f⁻¹ ∉ 𝔪ᵥ`.
But we no longer have `D(f * g) = D(f) ∩ D(g)`, so these form a subbasis, not a basis. -/
def basicOpen (s : Finset K) : Opens (Place R K) where
  carrier := {v | (s : Set K) ⊆ v}
  is_open' := by
    convert isOpen_biInter_finset (s := s) (f := fun k => {v : Place R K | k ∈ v}) <|
      fun f _ => isOpen_generateFrom_of_mem ⟨f, rfl⟩
    ext x
    refine ⟨?_, fun hx f hf => Set.mem_iInter.mp (Set.mem_iInter.mp hx f) hf⟩
    rintro hx U ⟨i, rfl⟩ j ⟨z, rfl⟩
    exact hx z

theorem basicOpen_eq_top_iff {s : Finset K} :
    basicOpen R s = ⊤ ↔ (s : Set K) ⊆ integralClosure R K := by
  sorry

theorem basicOpen_union [DecidableEq K] {s t : Finset K} :
    basicOpen R (s ∪ t) = basicOpen R s ⊓ basicOpen R t := by
  sorry

theorem isTopologicalBasis :
    IsTopologicalBasis (α := Place R K) {basicOpen R s | s : Finset K} := by
  sorry

section Compact

/-! We shall prove that the Zariski–Riemann space `Place R K` is a (quasi-)compact space,
following the proof of GTM 29, Commutative Algebra II by Zariski and Samuel, Theorem 40 on p. 113.

I find that it is better to use Bool instead of SignType {-,0,+} for this proof, as
`ofPlace` is not injective with {-,0,+} (though we only need surjectivity to deduce compactness). -/

/-- The subset in 2^K corresponding to valuation rings in K containing R. -/
def placeSet : Set (K → Bool) :=
  (⋂ xy : K × K, (· xy.1) ⁻¹' {false} ∪ (· xy.2) ⁻¹' {false} ∪
    (· (xy.1 + xy.2)) ⁻¹' {true} ∩ (· (xy.1 * xy.2)) ⁻¹' {true}) ∩
  (⋂ x : K, (· x) ⁻¹' {false} ∪ (· (- x)) ⁻¹' {true}) ∩
  (⋂ x : R, (· (algebraMap R K x)) ⁻¹' {true}) ∩
  (⋂ x ≠ (0 : K), (· x) ⁻¹' {true} ∪ (· x⁻¹) ⁻¹' {true})

variable (s : Set K)

variable {K} in
/-- The subset in `placeSet R K` corresponding to valuation rings in K containing R and s. -/
def placeSet' : Set (placeSet R K) := Subtype.val ⁻¹' (⋂ x ∈ s, (· x) ⁻¹' {true})

theorem isClosed_placeSet : IsClosed (placeSet R K) := by
  refine (((isClosed_iInter fun xy ↦ .union (.union ?_ ?_) (.inter ?_ ?_)).inter
    (isClosed_iInter fun x ↦ .union ?_ ?_)).inter <| isClosed_iInter fun x ↦ ?_).inter
    (isClosed_biInter fun x hx ↦ .union ?_ ?_)
  all_goals exact (isClosed_discrete _).preimage (continuous_apply _)

theorem isClosed_placeSet' : IsClosed (placeSet' R s) := by
  sorry

variable {R K}

theorem mem_placeSet_iff {v} : v ∈ placeSet R K ↔
    (∀ ⦃x y⦄, v x = true → v y = true → v (x + y) = true ∧ v (x * y) = true) ∧
    (∀ ⦃x⦄, v x = true → v (- x) = true) ∧
    (∀ x, v (algebraMap R K x) = true) ∧
    (∀ ⦃x⦄, x ≠ 0 → v x = true ∨ v x⁻¹ = true) := by
  simp_rw [placeSet, Set.mem_inter_iff, Set.mem_iInter, and_assoc]; congr! <;>
    simp [or_iff_not_imp_left]

variable (R K)

namespace Place

def ofPlaceSet (v : placeSet R K) : Place R K where
  carrier := {f | v.1 f = true}
  mul_mem' hf hg := ((mem_placeSet_iff.mp v.2).1 hf hg).2
  add_mem' hf hg := ((mem_placeSet_iff.mp v.2).1 hf hg).1
  algebraMap_mem' := (mem_placeSet_iff.mp v.2).2.2.1
  neg_mem' h := (mem_placeSet_iff.mp v.2).2.1 h
  mem_or_inv_mem' x := by
    obtain rfl | ne := eq_or_ne x 0
    · rw [← map_zero (algebraMap R K)]; exact .inl ((mem_placeSet_iff.mp v.2).2.2.1 _)
    · exact (mem_placeSet_iff.mp v.2).2.2.2 ne

@[simp] theorem mem_ofPlaceSet_iff {v : placeSet R K} {f : K} :
    f ∈ ofPlaceSet R K v ↔ v.1 f = true := .rfl

theorem continuous_ofPlaceSet : Continuous (ofPlaceSet R K) :=
  continuous_generateFrom_iff.mpr <| by
    rintro _ ⟨f, rfl⟩
    exact isOpen_induced ((isOpen_discrete {true}).preimage (continuous_apply (A := fun _ ↦ _) f))

variable {R K} in
noncomputable def toPlaceSet (v : Place R K) : placeSet R K where
  val f := by classical exact Decidable.decide (f ∈ v)
  property := mem_placeSet_iff.mpr <| by simp+contextual [add_mem, mul_mem, mem_or_inv_mem]

theorem ofPlaceSet_bijective : (ofPlaceSet R K).Bijective :=
  ⟨fun v₁ v₂ eq ↦ Subtype.ext (funext <| by simpa using SetLike.ext_iff.mp eq),
    fun v ↦ ⟨v.toPlaceSet, SetLike.ext <| by simp [toPlaceSet]⟩⟩

theorem preimage_ofPlaceSet_basicOpen (s : Finset K) :
    ofPlaceSet R K ⁻¹' basicOpen R s = placeSet' R s := by
  sorry

theorem image_placeSet' (s : Finset K) : ofPlaceSet R K '' placeSet' R s = basicOpen R s := by
  rw [← preimage_ofPlaceSet_basicOpen,
    Set.image_preimage_eq _ (ofPlaceSet_bijective R K).surjective]

end Place

end Compact

instance : CompactSpace (Place R K) := by
  rw [← isCompact_univ_iff, ← (Place.ofPlaceSet_bijective ..).2.range_eq]
  have := isCompact_iff_compactSpace.mp (isClosed_placeSet R K).isCompact
  exact isCompact_range (Place.continuous_ofPlaceSet R K)

instance : QuasiSeparatedSpace (Place R K) := by
  refine .of_isTopologicalBasis (isTopologicalBasis R K) fun s t ↦ ?_
  sorry -- use `basicOpen_union`, reduce to showing `basicOpen R (s ∪ t)` is compact

/- Not part of this project, see p.2 of
https://scispace.com/pdf/some-closure-operations-in-zariski-riemann-spaces-of-7bx8on35dg.pdf
  See https://arxiv.org/pdf/1309.5190 Corollary 3.3 for a proof based on ultrafilters.
  See also https://math.stanford.edu/~conrad/Perfseminar/refs/wedhornadic.pdf §3.4,
https://perso.ens-lyon.fr/sophie.morel/adic_notes.pdf §I.2.5. -/
instance : SpectralSpace (Place R K) := by
  sorry

-- Every nonempty open set contains the generic point.
theorem closure_genericPoint : closure {genericPoint k K} = .univ := by
  sorry

instance : IrreducibleSpace (Place R K) := by
  sorry

def Place.locallyRingedSpace : LocallyRingedSpace where
  carrier := .of (Place R K)
  presheaf :=
  { -- sections over an open set is the intersection of all places in the set
    obj U := .of ↥(⨅ v : U.1, v.1.toSubalgebra)
    map := sorry
    map_id := sorry, map_comp := sorry /- may be automatic -/ }
  IsSheaf := sorry
  isLocalRing := sorry
  /- Show the stalk at a place is isomorphic to the valuation subring.
    In general, a direct limit of inclusions is the union.
    If an element `f` is in a valuation subring, it is also in each valuation subring
    in the neighborhood `basicOpen R f`. -/

-- show all sections are domains with k-algebra structure (easy)
-- mathlib doesn't have definition of integral scheme?
-- compute global sections = integral (algebraic) closure of k in K

end Algebra

/-! ## Basics of function fields -/

namespace Algebra

class Is1DFunctionField : Prop where
  trdeg_eq_one : Algebra.trdeg k K = 1
  fg : (⊤ : IntermediateField k K).FG

theorem Is1DFunctionField.iff_exists_transcendental_finiteDimensional :
    Is1DFunctionField k K ↔ ∃ x : K, Transcendental k x ∧ FiniteDimensional k⟮x⟯ K := by
  sorry

namespace Place

open AlgebraicGeometry CategoryTheory

noncomputable def _root_.IsHomeomorph.toRingedSpaceIso
    {X Y : RingedSpace} (f : X ⟶ Y) (homeo : IsHomeomorph f.base)
    (bij : ∀ x : X, Function.Bijective (f.stalkMap x)) :
    X ≅ Y :=
  have : Epi f.base := (TopCat.epi_iff_surjective _).mpr homeo.bijective.2
  have (x : X) : IsIso (f.stalkMap x) := (ConcreteCategory.isIso_iff_bijective _).mpr (bij x)
  have := (SheafedSpace.IsOpenImmersion.of_stalk_iso f homeo.isOpenEmbedding).to_iso
  asIso f

noncomputable def _root_.IsHomeomorph.toLocallyRingedSpaceIso
    {X Y : LocallyRingedSpace} (f : X ⟶ Y) (homeo : IsHomeomorph f.base)
    (bij : ∀ x : X, Function.Bijective (f.stalkMap x)) :
    X ≅ Y :=
  sorry
  -- nontrivial; need to show the inverse also induces local ring homs on stalks
  -- use `isLocalHom_equiv` and `AlgebraicGeometry.PresheafedSpace.stalkMap.isIso` (instance)

def locallyRingedSpace.restrictToSpec (f : K) :
    (locallyRingedSpace R K).restrict (basicOpen R {f}).isOpenEmbedding ⟶
    Spec.toLocallyRingedSpace.obj (.op <| .of <| integralClosure (adjoin R {f}) K) :=
  ΓSpec.locallyRingedSpaceAdjunction.homEquiv _ _ <| .op <| by
    -- develop API to work with LRS morphisms from Γ-Spec adjunction?
    sorry -- construct ring hom from `integralClosure R[f] K` to sections over `basicOpen R {f}`

open Polynomial in
attribute [local instance] FractionRing.liftAlgebra in
theorem _root_.Polynomial.IsN2 {k K : Type*} [Field k] [Field K] [Algebra k[X] K]
    [FaithfulSMul k[X] K] [FiniteDimensional (FractionRing k[X]) K] :
    Module.Finite k[X] (integralClosure k[X] K) := by
  sorry -- see https://stacks.math.columbia.edu/tag/032O for a proof
  /- [Hartshorne, Theorem I.3.9A] (finiteness of integral closure) refers to
    GTM 28 by Zariski and Samuel, Ch. V, Theorem 9 on p.267-268. -/
  /- Corollary: `integralClosure k[X] K` is Noetherian, therefore Dedekind (still true if k[X]
    replaced by any Dedekind domain by Krull–Akizuki, which we're not going to prove here).
      Localizations at primes are therefore (discrete) valuation rings.
      Transporting this to `adjoin k {f}` (isomorphic to `k[X]` if `f` transcendental),
    we see that `restrictToSpec` is surjective.
      When K/k is 1D function field, this shows every place other than the generic point is
    a discrete valuation ring, recovering [Stichtenoth, Theorem 1.1.6].
      TODO: connect Dedekind to regularity/smoothness so we can really claim
    resolution of singularities. -/

variable [Is1DFunctionField k K]

def locallyRingedSpace.restrictIsoSpec (f : K) (hf : Transcendental k f) :
    (locallyRingedSpace k K).restrict (basicOpen k {f}).isOpenEmbedding ≅
    Spec.toLocallyRingedSpace.obj (.op <| .of <| integralClosure (adjoin k {f}) K) := by
  refine IsHomeomorph.toLocallyRingedSpaceIso (restrictToSpec k K f) ?_ ?_
  · sorry -- show homeomorphism, c.f. [Hartshorne, Lemma I.6.5]
  · sorry -- show iso on stalks

def scheme : Scheme where
  __ := locallyRingedSpace k K
  local_affine x := sorry
    /- pick any k-transcendental element in K; for each place v either f ∈ v or f⁻¹ ∈ v,
      so v ∈ basicOpen k {f} or v ∈ basicOpen k {f⁻¹}. Now use `restrictIsoSpec`. -/

instance : CompactSpace (scheme k K) := inferInstanceAs <| CompactSpace <| Place k K

instance : QuasiSeparatedSpace (scheme k K) := inferInstanceAs <| QuasiSeparatedSpace <| Place k K

-- In fact the complement of every basic open is finite, see [Hartshorne, Lemma I.6.5].

section SameUniverse

universe u

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [Is1DFunctionField k K]

def structureMorphism : scheme k K ⟶ Spec (.of k) := sorry -- use Γ-Spec adjunction

instance : QuasiCompact (structureMorphism k K) :=
  (quasiCompact_iff_compactSpace _).mpr inferInstance

instance : QuasiSeparated (structureMorphism k K) :=
  (quasiSeparated_iff_quasiSeparatedSpace _).mpr inferInstance

instance : LocallyOfFiniteType (structureMorphism k K) := by
  sorry  -- follows from `Polynomial.IsN2`

instance : IsProper (structureMorphism k K) := .of_valuativeCriterion _ <| by
  sorry

/- We don't have a valuative criterion for LocallyRingedSpace; if we had it should be satisfied
even when K/k isn't a 1D function field.

  Following [Hartshorne, Theorem I.6.9] it is possible to show `Place.scheme k K`
is in fact projective over `k`. -/

end SameUniverse

end Place

end Algebra
