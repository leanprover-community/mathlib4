/-
Copyright (c) 2025 Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer, Junyan Xu
-/
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
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

variable (v : Place R K)

instance : HasMemOrInvMem v where
  mem_or_inv_mem := v.mem_or_inv_mem'

instance : Algebra v K := inferInstanceAs (Algebra v.toSubalgebra K)
instance : IsScalarTower R v K := inferInstanceAs (IsScalarTower R v.toSubalgebra K)
instance : IsFractionRing v K :=
  inferInstanceAs (IsFractionRing v.toValuationSubring K)
instance : ValuationRing v := inferInstanceAs (ValuationRing v.toValuationSubring)

variable {R K} in
theorem Place.integralClosure_le (v : Place R K) : integralClosure R K ≤ v.toSubalgebra :=
  fun x hx ↦ by
    obtain ⟨x, rfl⟩ := (IsIntegrallyClosed.integralClosure_eq_bot v K).le hx.tower_top
    exact x.2
  /- before golfing: by
  have hv := IsIntegrallyClosed.integralClosure_eq_bot v K
  intro x hx
  have hx := hx.tower_top (A := v)
  obtain ⟨x', rfl⟩ := hv.le hx
  exact x'.2 -/

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
      fun f _ ↦ isOpen_generateFrom_of_mem ⟨f, rfl⟩
    ext x
    refine ⟨?_, fun hx f hf ↦ Set.mem_iInter.mp (Set.mem_iInter.mp hx f) hf⟩
    rintro hx U ⟨i, rfl⟩ j ⟨z, rfl⟩
    exact hx z

@[stacks 090P]

theorem basicOpen_eq_top_iff {s : Finset K} :
    basicOpen R s = ⊤ ↔ (s : Set K) ⊆ integralClosure R K := by
    constructor
    -- First case: hard direction
    · intro h x xs
      obtain rfl | xnezero := eq_or_ne x 0
      · simp only [SetLike.mem_coe, zero_mem]

      contrapose! h
    -- construct an intermediate algebra R ⊆ B ⊆ K which contains x⁻¹ and not x
      let B := adjoin R {x⁻¹}
      have xinvB : x⁻¹ ∈ B  := Algebra.mem_adjoin_of_mem rfl
      -- Now we prove that x∉ B. This is surprisingly difficult.
      have xnB : x ∉ B := by
        contrapose! h
        have ⟨p, hp⟩ := Algebra.adjoin_mem_exists_aeval _ _ h

        -- We construct a polynomial q which witnesses the fact that x∈ IntClosure of R.
        let d := p.natDegree

        apply (mem_integralClosure_iff _ _ ).mpr
        let q := .X ^ (d + 1) - p.reverse

        -- We prove that q is monic
        have qmon : q.Monic := Polynomial.monic_X_pow_sub <|
          calc p.reverse.degree ≤ p.reverse.natDegree := Polynomial.degree_le_natDegree
          _ ≤ p.natDegree := mod_cast Polynomial.reverse_natDegree_le p
          _ = d := rfl
          _ < d + 1 := mod_cast Nat.lt_add_one d

        -- Here we prove that q(x) indeed equals zero.
        have xinvxeq1 : x⁻¹ * x = 1 := inv_mul_cancel₀ xnezero
        have xxinveq1 : x * x⁻¹ = 1 := mul_inv_cancel₀ xnezero

        let : Invertible x⁻¹ := ⟨x, xxinveq1 , xinvxeq1⟩
        let : Invertible x := ⟨x⁻¹, xinvxeq1 , xxinveq1⟩
        have : ⅟(x⁻¹) = x := by rfl
        open Polynomial in
        have hq : q.aeval x = 0 := by
          calc q.aeval x = x ^ (d + 1) - p.reverse.aeval x := by
                rw [aeval_sub]; simp
              _ = x ^ (d + 1) - p.reverse.aeval x * x⁻¹ ^ d * x ^ d := by simp [mul_assoc]
              _ = x ^ (d + 1) - p.aeval x⁻¹ * x ^ d := by
                    simp only [sub_right_inj, mul_eq_mul_right_iff]
                    left
                    rw [aeval_def, aeval_def]
                    nth_rewrite 1 [← this]
                    rw [eval₂_reverse_mul_pow (algebraMap R K) x⁻¹ p]
              _ = 0 := by rw [hp]; ring

        -- This is completing the Lemma
        exact ⟨q, qmon, hq⟩

      -- Now we have proven that B is an algebra with x⁻¹ ∈ B and x∉ B
      -- We now construct a valuation ring V⊆ K which does not contain x.

      -- Here, we show that x⁻¹ is a non-unit of B ...
      let xinv : B := ⟨x⁻¹, xinvB⟩
      · have xinvnu : xinv ∈ nonunits B := mem_nonunits_iff.mpr <| by
          contrapose! xnB
          rcases xnB with ⟨u,eq ⟩
          convert u.inv.2
          have hu : IsUnit (u : K) := u.isUnit.map B.subtype
          apply hu.mul_left_cancel
          conv_lhs => rw [eq]
          rw [Units.inv_eq_val_inv]
          calc xinv * x = 1 := inv_mul_cancel₀ xnezero
          _ = u * u⁻¹ := congr_arg (·.1) u.val_inv.symm

        rcases exists_max_ideal_of_mem_nonunits xinvnu with ⟨I, Imax, xinvI⟩

        --  ... And thus, we obtain a maximal ideal I of B containing x⁻¹...
        let BI := LocalSubring.ofPrime B.toSubring I
        --  ⋯ And pass to the localisation of B at I to apply the following lemma
        -- that guarantees that there is a Valuation ring, V, that contains B,
        -- with the property that x⁻¹ ∈ maxIdeal(V)

        obtain ⟨V, hv⟩ := LocalSubring.exists_le_valuationSubring BI
        have xnV : x ∉ V := by
          contrapose! xnB
          have := hv.2
          have : algebraMap B.toSubring BI.toSubring xinv ∈
              IsLocalRing.maximalIdeal BI.toSubring := by
            change Ideal B.toSubring at I
            rw [← IsLocalization.AtPrime.map_eq_maximalIdeal I]
            exact Ideal.mem_map_of_mem _ xinvI

          refine (map_nonunit (Subring.inclusion hv.1) _ this ?_).elim
          lift x to V using xnB
          apply IsUnit.of_mul_eq_one_right x
          ext
          exact mul_inv_cancel₀ xnezero

        -- We finally are prepared to conclude the proof, by showing that V ∈ Place (R K) is not in
        -- basicOpen R s, witnessing that basicOpen≠ Top.
        let V' : Place R K :=
          { __ := V , algebraMap_mem' r := hv.1 (LocalSubring.le_ofPrime _ _ (B.algebraMap_mem r))}

        -- Show that basicopen ≠ ⊤ because V is not in the basic open.
        have vnbasic : V' ∉ basicOpen R s := by
          contrapose! xnV
          exact xnV xs

        contrapose! vnbasic
        rw [vnbasic]
        trivial

    -- Second case: Easy direction.
    rintro h
    ext V
    exact ⟨fun hV ↦ ⟨⟩, fun Vtop x xs ↦ V.integralClosure_le (h xs)⟩


-- the global sections of the sheaf on `Place R K`
-- follows from `basicOpen_eq_top_iff`
theorem iInf_eq_integralClosure :
    (⨅ v : Place R K, v.toSubalgebra) = integralClosure R K := by
  sorry

theorem iInf_eq_integralClosure_adjoin (s : Finset K) :
    (⨅ v : basicOpen k s, v.1.toSubalgebra) =
    (integralClosure (Algebra.adjoin k (s : Set K)) K).restrictScalars k := by
  sorry -- use induction?

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
  See https://arxiv.org/pdf/1309.5
  190 Corollary 3.3 for a proof based on ultrafilters.
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

end Algebra

/-! ## Basics of function fields -/

namespace Algebra

class Is1DFunctionField : Prop where
  trdeg_eq_one : Algebra.trdeg k K = 1
  fg : (⊤ : IntermediateField k K).FG

theorem Is1DFunctionField.finiteDimensional_of_transcendental (ff : Is1DFunctionField k K)
    (x : K) (hx : Transcendental k x) : FiniteDimensional k⟮x⟯ K := by
  sorry

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
