import Mathlib

set_option linter.style.longLine false
set_option linter.style.cdot false

open Subgroup
open scoped Finset
open scoped Pointwise


variable {G : Type*} [hG: Group G] [DecidableEq G]

-- TODO - I don't really understand why `S` needs to be an `outParam`?
-- If I remove that, then the `PseudoMetricSpace G` starts erroring
-- See also:
-- * `set_option synthInstance.checkSynthOrder false`
class Generates {S: outParam (Finset G)}: Prop where
  generates : ((closure (S : Set G) : Set G) = ⊤)
  has_inv: ∀ g ∈ S, g⁻¹ ∈ S

variable {S : Finset G} [hGS: Generates (G := G) (S := S)] [hS: Nonempty S]

lemma s_union_sinv : (S: Set G) ∪ (S: Set G)⁻¹ = S := by
  ext a
  have foo := hGS.has_inv (a⁻¹)
  simp only [inv_inv] at foo
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_inv, or_iff_left_iff_imp]
  exact foo

lemma S_eq_Sinv: S = S⁻¹ := by
  ext a
  refine ⟨?_, ?_⟩
  . intro ha
    have a_inv := hGS.has_inv a ha
    exact Finset.mem_inv'.mpr a_inv
  . intro ha
    simp at ha
    have a_inv := hGS.has_inv a⁻¹ ha
    simp only [inv_inv] at a_inv
    exact a_inv



lemma mem_closure (x: G): x ∈ closure (S : Set G) := by
  have hg := hGS.generates
  simp only [Set.top_eq_univ, coe_eq_univ] at hg
  simp [hg]

-- Predicate stating that an element of G equals a product of elements of S
def ProdS (x: G) (l: List S): Prop := l.unattach.prod = x

-- Each element of G can be written as a product of elements of S in at least one way
lemma mem_S_prod_list (x: G): ∃ l: List S, ProdS x l := by
  -- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Group.20.28.2FMonoid.2Fetc.29.20closures.20are.20a.20finite.20product.2Fsum/near/477951441
  have foo := Submonoid.exists_list_of_mem_closure (s := S ∪ S⁻¹) (x := x)
  rw [← Subgroup.closure_toSubmonoid _] at foo
  simp only [mem_toSubmonoid, Finset.mem_coe] at foo
  specialize foo (mem_closure x)
  rw [s_union_sinv (S := S)] at foo
  obtain ⟨l, ⟨mem_s, prod_eq⟩⟩ := foo
  use (l.attach).map (fun x => ⟨x.val, mem_s (x.val) x.property⟩)
  unfold ProdS
  unfold List.unattach
  simp [prod_eq]

lemma list_tail_unattach (T: Type*)  {p : T → Prop} (l: List { x : T // p x}): l.tail.unattach = l.unattach.tail := by
  unfold List.unattach
  simp

noncomputable def WordNorm (g: G) := sInf {n: ℕ | ∃ l: List S, l.length = n ∧ ProdS g l}

lemma word_norm_prod (g: G) (n: ℕ) (hgn: WordNorm (S := S) g = n): ∃ l: List S, ProdS g l ∧ l.length = n := by
  have foo := Nat.sInf_mem (s := {n: ℕ | ∃ l: List S, l.length = n ∧ ProdS g l})
  obtain ⟨l, hl⟩ := mem_S_prod_list (S := S) g
  unfold ProdS at hl
  rw [Set.nonempty_def] at foo
  specialize foo ⟨l.length, ⟨l, ⟨by simp, hl⟩⟩⟩
  simp only [Set.mem_setOf_eq] at foo
  obtain ⟨l, ⟨hl, hl_prod⟩⟩ := foo
  rw [← hgn]
  exact ⟨l, ⟨hl_prod, hl⟩⟩

lemma word_norm_prod_self (g: G): ∃ l: List S, ProdS g l ∧ l.length = WordNorm (S := S) g := by
  exact word_norm_prod (S := S) g (WordNorm (S := S) g) rfl

lemma word_norm_le (g: G) (l: List S) (hgl: ProdS g l): WordNorm (S := S) g ≤ l.length := by
  unfold WordNorm
  apply Nat.sInf_le
  use l

noncomputable def WordDist (x y: G) := WordNorm (S := S) (x⁻¹ * y)

lemma WordDist_self (x: G): WordDist (S := S) x x = 0 := by
  unfold WordDist
  rw [inv_mul_cancel]
  unfold WordNorm
  simp only [Nat.sInf_eq_zero, Set.mem_setOf_eq, List.length_eq_zero_iff, exists_eq_left]
  left
  rfl

lemma WordDist_swap_le (x y: G): WordDist (S := S) y x ≤ WordDist (S := S) x y := by
  unfold WordDist
  obtain ⟨l, l_prod, l_len⟩ := word_norm_prod (x⁻¹ * y) (WordNorm (x⁻¹ * y)) (rfl)
  unfold ProdS at l_prod
  apply_fun (fun x => x⁻¹) at l_prod
  rw [mul_inv_rev, inv_inv] at l_prod
  rw [List.prod_inv_reverse] at l_prod

  have commute_unattach: List.map (Inv.inv) l.unattach = (l.map (fun x => ⟨x.val⁻¹, hGS.has_inv x.val x.property⟩)).unattach := by
    apply List.ext_getElem?
    intro i
    simp


  rw [commute_unattach, ← List.unattach_reverse] at l_prod
  have prod_le := word_norm_le (S := S) (y⁻¹ * x) _ l_prod
  conv at prod_le =>
    rhs
    equals l.length =>
      simp
  rw [l_len] at prod_le
  exact prod_le

lemma WordDist_comm (x y: G): WordDist (S := S) x y = WordDist (S := S) y x := by
  have le_left := WordDist_swap_le (S := S) x y
  have le_right := WordDist_swap_le (S := S) y x
  exact Nat.le_antisymm le_right le_left

lemma WordDist_triangle (x y z: G): WordDist (S := S) x z ≤ WordDist (S := S) x y + WordDist (S := S) y z := by
  have eq_through_y: x⁻¹ * z = x⁻¹ * y * y⁻¹ * z := by
    simp

  unfold WordDist
  obtain ⟨l_x_y, x_y_prod, x_y_len⟩ := word_norm_prod_self (S := S) (x⁻¹ * y)
  obtain ⟨l_y_z, y_z_prod, y_z_len⟩ := word_norm_prod_self (S := S) (y⁻¹ * z)
  unfold ProdS at x_y_prod
  unfold ProdS at y_z_prod

  have prod_append: ProdS (S := S) (x⁻¹ * z) (l_x_y ++ l_y_z) := by
    unfold ProdS
    simp
    rw [x_y_prod, y_z_prod]
    rw [← mul_assoc]
    simp

  have le_append := word_norm_le (S := S) (x⁻¹ * z) _ prod_append
  rw [List.length_append] at le_append
  rw [x_y_len, y_z_len] at le_append
  exact le_append

-- TODO - I'm not certain that these are actually the correct instances for the proof

noncomputable instance WordDist.instPseudoMetricSpace: PseudoMetricSpace G where
  dist x y := WordDist (G := G) (S := S) x y
  dist_self x := by
    norm_cast
    exact WordDist_self (S := S) x
  dist_comm x y := by
    norm_cast
    exact WordDist_comm (S := S) x y
  dist_triangle x y z := by
    norm_cast
    exact WordDist_triangle (S := S) x y z

noncomputable instance WordDist.instMetricSpace: MetricSpace G where
  eq_of_dist_eq_zero := by
    intro x y hdist
    simp [dist, WordDist, WordNorm] at hdist
    match hdist with
    | .inl empty_prod =>
      unfold ProdS at empty_prod
      simp only [List.unattach_nil, List.prod_nil] at empty_prod
      apply_fun (fun y => x * y) at empty_prod
      simp only [mul_one, mul_inv_cancel_left] at empty_prod
      exact empty_prod
    | .inr empty_set =>
      obtain ⟨l, hl⟩ := mem_S_prod_list (S := S) (x⁻¹ * y)
      unfold ProdS at hl
      have len_in_set: l.unattach.length ∈ (∅ : Set ℕ) := by
        rw [← empty_set]
        simp only [List.length_unattach, Set.mem_setOf_eq]
        use l
        refine ⟨rfl, hl⟩
      simp only [Set.mem_empty_iff_false] at len_in_set

-- TODO - is there an easier way to transfer all of the theorems/instances from `G` to `Additive (MulOpposite G)`?

noncomputable instance WordDist.instPseudoMetricSpaceAddOpp: PseudoMetricSpace (Additive (MulOpposite G)) where
  dist x y := dist x.toMul.unop y.toMul.unop
  dist_self x := by
    apply PseudoMetricSpace.dist_self
  dist_comm x y := by
    apply PseudoMetricSpace.dist_comm
  dist_triangle x y z := by
    apply PseudoMetricSpace.dist_triangle

noncomputable instance WordDist.instMetricSpaceAddOpp: MetricSpace (Additive (MulOpposite G)) where
  eq_of_dist_eq_zero := by
    intro x y hxy
    have := MetricSpace.eq_of_dist_eq_zero (x := x.toMul.unop) (y := y.toMul.unop) hxy
    simp only [MulOpposite.unop_inj, EmbeddingLike.apply_eq_iff_eq] at this
    exact this

--def WordMetricSpace := MetricSpace.ofDistTopology ()
noncomputable instance WordDist.instMeasurableSpace: MeasurableSpace G := borel G

noncomputable instance WordDist.instMeasureableSpaceOpp: MeasurableSpace (Additive (MulOpposite G)) := borel (Additive (MulOpposite G))

noncomputable instance WordDist.instBorelSpace: BorelSpace G where
  measurable_eq := rfl

noncomputable instance WordDist.instBorelSpaceAddOpp: BorelSpace (Additive (MulOpposite G)) where
  measurable_eq := rfl

-- TODO - are we really supposed to be using a metric topology if it turns out to be the discrete topology?
lemma singleton_open (x: G): IsOpen {x} := by
  rw [Metric.isOpen_singleton_iff]
  use 1
  simp only [gt_iff_lt, zero_lt_one, true_and]
  intro y hy
  simp [dist] at hy
  have dist_zero := dist_eq_zero (x := y) (y := x)
  simp [dist] at dist_zero
  rw [dist_zero] at hy
  exact hy

instance discreteTopology: DiscreteTopology G := by
  rw [← singletons_open_iff_discrete]
  exact singleton_open

instance : ContinuousMul G where
  continuous_mul := continuous_of_discreteTopology

instance : ContinuousInv G where
  continuous_inv := continuous_of_discreteTopology

instance: IsTopologicalGroup G where
  continuous_mul := continuous_of_discreteTopology
  continuous_inv := continuous_of_discreteTopology


instance IsTopologicalGroupAddOpp: IsTopologicalAddGroup (Additive (MulOpposite G)) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

-- Define Haar measure so that singleton sets have measure 1 -
-- I think this is what we want in order to be able to nicely convert integrals to sums
noncomputable def myHaar := MeasureTheory.Measure.haarMeasure (G := G) {
  carrier := {1}
  isCompact' := by
    simp
  interior_nonempty' := by
    have one_mem: (1 : G) ∈ interior {1} := by
      rw [mem_interior]
      use {1}
      simp
    apply Set.nonempty_def.mpr
    exact ⟨1, one_mem⟩
}

noncomputable def addHaarSingleton: TopologicalSpace.PositiveCompacts (Additive (MulOpposite G)) := {
  carrier := {0}
  isCompact' := by
    simp
  interior_nonempty' := by
    have zero_mem: (0 : Additive (MulOpposite G)) ∈ interior {0} := by
      rw [mem_interior]
      use {0}
      simp
    apply Set.nonempty_def.mpr
    exact ⟨0, zero_mem⟩
}

lemma singleton_carrier: (addHaarSingleton.carrier) = ({0} : (Set (Additive (MulOpposite G)))) := by
  unfold addHaarSingleton
  rfl

noncomputable abbrev myHaarAddOpp := MeasureTheory.Measure.addHaarMeasure (G := Additive (MulOpposite G)) addHaarSingleton

-- Definition 3.5 in Vikman - a harmonic function on G
def Harmonic (f: G → ℂ): Prop := ∀ x: G, f x = ((1 : ℂ) / #(S)) * ∑ s ∈ S, f (x * s)

-- A Lipschitz harmonic function from section 3.2 of Vikman
structure LipschitzH [Generates (G := G) (S := S)] where
  -- The underlying function
  toFun: G → ℂ
  -- The function is Lipschitz for some constant C
  lipschitz: ∃ C, LipschitzWith C toFun
  -- The function is harmonic
  harmonic: Harmonic (S := S) toFun


instance: FunLike (LipschitzH (G := G)) G ℂ where
  coe := LipschitzH.toFun
  -- TODO - why does this work? I blindly copied it from `OneHom.funLike`
  coe_injective' f g h := by cases f; cases g; congr

@[ext]
theorem LipschitzH.ext [Generates (G := G) (S := S)] {f g: LipschitzH (G := G)} (h: ∀ x, f.toFun x = g.toFun x): f = g := DFunLike.ext _ _ h

instance LipschitzH.add [Generates (S := S)] : Add (LipschitzH (G := G)) := {
  add := fun f g => {
    toFun := fun x => f.toFun x + g.toFun x
    lipschitz := by
      obtain ⟨C1, hC1⟩ := f.lipschitz
      obtain ⟨C2, hC2⟩ := g.lipschitz
      use C1 + C2
      exact LipschitzWith.add hC1 hC2
    harmonic := by
      unfold Harmonic
      intro x
      have ha := f.harmonic
      have hb := g.harmonic
      unfold Harmonic at ha hb
      simp_rw [ha x, hb x]
      field_simp
      rw [← Finset.sum_add_distrib]
  }
}
instance LipschitzH.zero [Generates (S := S)] : Zero (LipschitzH (G := G)) := {
  zero := {
    toFun := fun x => 0
    lipschitz := by
      use 0
      exact LipschitzWith.const 0
    harmonic := by simp [Harmonic]
  }
}
instance LipschitzH.addMonoid [Generates (S := S)] : AddMonoid (LipschitzH (G := G)) := {
  LipschitzH.zero,
  LipschitzH.add with
  add_assoc := fun _ _ _ => ext fun _ => add_assoc _ _ _
  zero_add := fun _ => ext fun _ => zero_add _
  add_zero := fun _ => ext fun _ => add_zero _
  nsmul := nsmulRec
}

instance LipschitzH.instAddCommMonoid: AddCommMonoid (LipschitzH (G := G)) := {
  LipschitzH.addMonoid with add_comm := fun _ _ => ext fun _ => add_comm _ _
}

-- V is the vector space
def V := Module ℂ (LipschitzH (G := G))

@[simp]
theorem LipschitzH.add_apply (f g: LipschitzH (G := G)) (x: G): (f + g).toFun x = f x + g x := by
  unfold LipschitzH.add
  rfl

instance lipschitzHVectorSpace : V (G := G) := {
  smul := fun c f => {
    toFun := fun x => c * f.toFun x
    lipschitz := by
      conv =>
        rhs
        intro C
        rhs
        equals (fun (x: ℂ) => c * x) ∘ f.toFun =>
          unfold Function.comp
          simp
      obtain ⟨C, hC⟩ := f.lipschitz
      use ‖c‖₊ * C
      apply LipschitzWith.comp (lipschitzWith_smul _) hC
    harmonic := by
      unfold Harmonic
      intro x
      field_simp
      rw [← Finset.mul_sum]
      rw [← mul_div]
      rw [mul_eq_mul_left_iff]
      left
      have hf := f.harmonic x
      unfold Harmonic at hf
      simp at hf
      field_simp at hf
      exact hf
  }
  one_smul := by simp [HSMul.hSMul]
  mul_smul := by
    intro x y f
    simp [HSMul.hSMul]
    ext g
    rw [mul_assoc]
  smul_zero := by
    intro a
    dsimp [HSMul.hSMul]
    dsimp [OfNat.ofNat]
    dsimp [Zero.zero]
    simp
  smul_add := by
    intro a f g
    dsimp [HSMul.hSMul]
    simp [mul_add]
    ext p
    simp [DFunLike.coe]
  add_smul := by
    intro a f g
    dsimp [HSMul.hSMul]
    simp [add_mul]
    ext p
    simp [DFunLike.coe]
  zero_smul := by
    intro a
    dsimp [HSMul.hSMul]
    dsimp [OfNat.ofNat]
    dsimp [Zero.zero]
    simp
}

-- TODO - use the fact that G is finitely generated
instance countableG: Countable (Additive (MulOpposite G)) := by
  apply Function.Surjective.countable (f := fun (x: List S) => (Additive.ofMul (MulOpposite.op (x.unattach.prod))))
  intro g
  obtain ⟨l, hl⟩ := mem_S_prod_list (S := S) g.toMul.unop
  use l
  simp only
  unfold ProdS at hl
  rw [hl]
  simp

lemma singleton_pairwise_disjoint (s: Set (Additive (MulOpposite G))) : s.PairwiseDisjoint Set.singleton := by
  refine Set.pairwiseDisjoint_iff.mpr ?_
  intro a ha b hb hab
  unfold Set.singleton at hab
  simp at hab
  exact hab.symm


-- Use the fact that we have the discrete topology
lemma my_add_haar_eq_count: (myHaarAddOpp (G := G)) = MeasureTheory.Measure.count := by
  ext s hs
  by_cases s_finite: Set.Finite s
  .
    have eq_singletons := Set.biUnion_of_singleton (s := s)
    nth_rw 1 [← eq_singletons]
    rw [MeasureTheory.Measure.count_apply_finite s s_finite]
    rw [MeasureTheory.measure_biUnion]
    .
      -- TODO - extract 'measure {a} = 1' to a lemma
      simp_rw [MeasureTheory.Measure.addHaar_singleton]
      unfold myHaarAddOpp
      simp_rw [← singleton_carrier]
      simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
      rw [MeasureTheory.Measure.addHaarMeasure_self]
      rw [ENNReal.tsum_set_const]
      simp
      norm_cast
      rw [Set.Finite.encard_eq_coe_toFinset_card s_finite]
    . exact Set.Finite.countable s_finite
    .
      apply singleton_pairwise_disjoint
    .
      intro a ha
      apply IsOpen.measurableSet
      simp
  .
    have s_infinite: s.Infinite := by
      exact s_finite
    rw [MeasureTheory.Measure.count_apply_infinite s_infinite]
    have eq_singletons := Set.biUnion_of_singleton (s := s)
    nth_rw 1 [← eq_singletons]
    rw [MeasureTheory.measure_biUnion]
    .
      simp_rw [MeasureTheory.Measure.addHaar_singleton]
      unfold myHaarAddOpp
      simp_rw [← singleton_carrier]
      simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
      rw [MeasureTheory.Measure.addHaarMeasure_self]
      simp only [ENNReal.tsum_one, ENat.toENNReal_eq_top, ENat.card_eq_top]
      exact Set.infinite_coe_iff.mpr s_finite
    . exact Set.to_countable s
    . apply singleton_pairwise_disjoint
    .
      intro a ha
      apply IsOpen.measurableSet
      simp


-- With the counting measure, A.E is the same as everywgere
lemma count_ae_everywhere (p: G → Prop): (∀ᵐ g ∂(MeasureTheory.Measure.count), p g) = ∀ a: G, p a := by
  rw [MeasureTheory.ae_iff]
  simp [MeasureTheory.Measure.count_eq_zero_iff]
  -- TODO - there has to be a much simpler way of proving this
  refine ⟨?_, ?_⟩
  . intro h
    intro a
    by_contra this
    have a_in: a ∈ {a | ¬ p a} := by
      simp [this]
    have foo := Set.nonempty_of_mem a_in
    rw [← Set.not_nonempty_iff_eq_empty] at h
    contradiction
  . intro h
    by_contra this
    simp at this
    rw [← ne_eq] at this
    rw [← Set.nonempty_iff_ne_empty'] at this
    obtain ⟨a, ha⟩ := this
    specialize h a
    simp at ha
    contradiction

-- Use the fact that our measure is the counting measure (since we have the discrete topology),
-- and negating a finite set of points in an additive group leaves the cardinality unchanged
instance myNegInvariant: MeasureTheory.Measure.IsNegInvariant (myHaarAddOpp (G := G)) := {
  neg_eq_self := by
    rw [my_add_haar_eq_count]
    simp only [MeasureTheory.Measure.neg_eq_self]
}

-- TODO - I don't think we can use this, as `MeasureTheory.convolution' would require our group to be commutative
-- (via `NormedAddCommGroup`)
open scoped Convolution
noncomputable def Conv (f g: G → ℝ) (x: G) : ℝ :=
  (MeasureTheory.convolution (G := Additive (MulOpposite G)) (fun x => f x.toMul.unop) (fun x => g x.toMul.unop) (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp (Additive.ofMul (MulOpposite.op x)))

def ConvExists (f g: G → ℝ) := MeasureTheory.ConvolutionExists (G := Additive (MulOpposite G)) (fun x => f x.toMul.unop) (fun x => g x.toMul.unop) (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp


abbrev opAdd (g : G) := Additive.ofMul (MulOpposite.op g)


-- A versi on of `conv_exists` where at least one of the functions has finite support
-- This lets us avoid dealing with 'MemLp' in most cases
lemma conv_exists_fin_supp (f g: G → ℝ) (hfg: f.support.Finite ∨ g.support.Finite): ConvExists f g := by
  unfold ConvExists MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt
  intro x
  apply Continuous.integrable_of_hasCompactSupport
  . exact continuous_of_discreteTopology
  .
    unfold HasCompactSupport
    rw [isCompact_iff_finite]
    dsimp [tsupport]
    rw [closure_discrete]
    simp only [Function.support_mul]
    match hfg with
    | .inl hf =>
      apply Set.Finite.inter_of_left
      apply Set.Finite.subset (s := opAdd '' f.support)
      . unfold opAdd
        exact Set.Finite.image (fun g ↦ Additive.ofMul (MulOpposite.op g)) hf
      . intro a ha
        simp at ha
        simp [opAdd]
        use a.toMul.unop
        simp only [MulOpposite.op_unop, ofMul_toMul, and_true]
        exact ha
    | .inr hg =>
      apply Set.Finite.inter_of_right
      let myFun := fun a => -(opAdd a) + x
      have finite_image := Set.finite_image_iff (f := myFun) (s := g.support) ?_
      .
        conv =>
          arg 1
          equals (myFun '' Function.support g) =>
            ext a
            simp
            refine ⟨?_, ?_⟩
            . intro ha
              use (MulOpposite.unop (Additive.toMul a))⁻¹ * MulOpposite.unop (Additive.toMul x)
              refine ⟨ha, ?_⟩
              simp [myFun, opAdd]
            . intro ha
              simp [myFun, opAdd] at ha
              obtain ⟨b, b_zero, a_eq⟩ := ha
              rw [← a_eq]
              simp [b_zero]
        rw [finite_image]
        exact hg
      .
        simp [myFun, opAdd]
        apply Set.injOn_of_injective
        intro a b hab
        simp only [add_left_inj, neg_inj, EmbeddingLike.apply_eq_iff_eq, MulOpposite.op_inj,
          myFun] at hab
        exact hab


lemma conv_exists (p q : ℝ) (hp: 0 < p) (hq: 0 < q) (hpq: p.HolderConjugate q) (f g: G → ℝ)
  (hf: MeasureTheory.MemLp ((fun x => f x.toMul.unop)) (ENNReal.ofReal p) myHaarAddOpp)
  (hg: ∀ y: G, MeasureTheory.MemLp ((fun x => g (x.toMul.unop⁻¹ * y))) (ENNReal.ofReal q) myHaarAddOpp)
  : ConvExists f g := by
  unfold ConvExists MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt MeasureTheory.Integrable
  intro x
  simp only [toMul_sub, MulOpposite.unop_div, ContinuousLinearMap.mul_apply']
  refine ⟨MeasureTheory.AEStronglyMeasurable.of_discrete, ?_⟩
  unfold MeasureTheory.HasFiniteIntegral
  simp
  have holder_bound := ENNReal.lintegral_mul_le_Lp_mul_Lq (MeasureTheory.Measure.count) (hpq)
    (AEMeasurable.of_discrete) (AEMeasurable.of_discrete)
    (f := fun a => ‖f (MulOpposite.unop (Additive.toMul a))‖ₑ)
    (g := fun a => ‖g ((MulOpposite.unop (Additive.toMul a))⁻¹ * MulOpposite.unop (Additive.toMul x))‖ₑ)
  simp at holder_bound
  rw [my_add_haar_eq_count]

  have p_ne_zero: ENNReal.ofReal p ≠ 0 := by
    simp [hp]

  have p_ne_top: ENNReal.ofReal p ≠ ⊤ := by
    simp

  have q_ne_zero: ENNReal.ofReal q ≠ 0 := by
    simp [hq]

  have p_ge_zero: 0 ≤ p := by
    linarith

  have q_ge_zero: 0 ≤ q := by
    linarith

  have integral_lt_top := ne_top_of_le_ne_top (?_) holder_bound
  . exact Ne.lt_top' (id (Ne.symm integral_lt_top))
  . apply WithTop.mul_ne_top
    .
      have foo := MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top p_ne_zero (by simp) (MeasureTheory.MemLp.eLpNorm_lt_top hf)
      rw [my_add_haar_eq_count] at foo
      rw [ENNReal.toReal_ofReal p_ge_zero] at foo
      apply ENNReal.rpow_ne_top_of_nonneg (?_) ?_
      . simp only [inv_nonneg]
        linarith
      . exact LT.lt.ne_top foo
    .
      have foo := MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top q_ne_zero (by simp) (MeasureTheory.MemLp.eLpNorm_lt_top (hg x.toMul.unop))
      rw [my_add_haar_eq_count] at foo
      rw [ENNReal.toReal_ofReal q_ge_zero] at foo
      apply ENNReal.rpow_ne_top_of_nonneg (?_) ?_
      . simp only [inv_nonneg]
        linarith
      .
        exact LT.lt.ne_top foo

-- -- For now, we should add additional hypothesis that 'f' and 'g' are non-negative
-- -- This is enoguh for the Vikman proof
-- lemma conv_exists_bad (c: ℝ) (hc: 0 ≤ c) (p q : ENNReal) (hpq: p.HolderConjugate q) (f g: G → ℝ)
--   (hf: MeasureTheory.MemLp ((fun x => f x.toMul.unop)) p myHaarAddOpp)
--   (hg: MeasureTheory.MemLp ((fun x => g x.toMul.unop)) q myHaarAddOpp)
--   : MeasureTheory.ConvolutionExists (G := Additive (MulOpposite G)) (fun x => f x.toMul.unop) (fun x => g x.toMul.unop) (ContinuousLinearMap.mul ℝ ℝ) myHaarAddOpp := by
--   unfold MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt
--   intro x
--   -- We can use young's hypothesis to bound the norm of the convolution function, giving us something like `∫ ∫ q < ⊤ ` (or stronger)
--   -- However, we also need the convolution to exist at all (e.g. the inner integral converges: `∫ q < ⊤ )
--   have h_young := ENNReal.eLpNorm_top_convolution_le' (p := p) (q := q) (L := (ContinuousLinearMap.mul ℝ ℝ)) (𝕜 := ℝ) (F := ℝ) (E := ℝ) (E' := ℝ) (G := Additive (MulOpposite G)) (f := (fun x => f x.toMul.unop)) (g := (fun x => g x.toMul.unop)) (μ := myHaarAddOpp)
--     hpq MeasureTheory.AEStronglyMeasurable.of_discrete MeasureTheory.AEStronglyMeasurable.of_discrete (c := c) ?_

--   .
--     unfold MeasureTheory.Integrable
--     refine ⟨MeasureTheory.AEStronglyMeasurable.of_discrete, ?_⟩
--     unfold MeasureTheory.HasFiniteIntegral
--     simp only [MeasureTheory.eLpNorm_exponent_top] at h_young

--     have f_finite := hf.2
--     have g_finite := hg.2
--     rw [lt_top_iff_ne_top] at f_finite g_finite
--     rw [← ENNReal.ofReal_toReal f_finite] at h_young
--     rw [← ENNReal.ofReal_toReal g_finite] at h_young
--     rw [← ENNReal.ofReal_mul hc] at h_young
--     rw [← ENNReal.ofReal_mul ?_] at h_young
--     . have other_lt_top := ENNReal.ofReal_lt_top (r := (c * (MeasureTheory.eLpNorm (fun x ↦ f (MulOpposite.unop (Additive.toMul x))) p myHaarAddOpp).toReal *
--         (MeasureTheory.eLpNorm (fun x ↦ g (MulOpposite.unop (Additive.toMul x))) q myHaarAddOpp).toReal))

--       have ess_sup_lt_top := lt_of_le_of_lt h_young other_lt_top
--       unfold MeasureTheory.convolution at ess_sup_lt_top
--       rw [my_add_haar_eq_count] at ess_sup_lt_top
--       rw [MeasureTheory.eLpNormEssSup_eq_essSup_enorm] at ess_sup_lt_top
--       simp at ess_sup_lt_top
--       rw [lt_top_iff_ne_top] at ess_sup_lt_top
--       rw [ne_eq] at ess_sup_lt_top
--       rw [not_iff_not.mpr (iSup_eq_top _)] at ess_sup_lt_top
--       simp at ess_sup_lt_top
--       obtain ⟨C, hC, bound_integral⟩ := ess_sup_lt_top
--       specialize bound_integral x.toMul.unop
--       simp only [toMul_sub, MulOpposite.unop_div, ContinuousLinearMap.mul_apply',
--         gt_iff_lt]
--       norm_cast at bound_integral
--       rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae] at bound_integral
--       conv at bound_integral =>
--         lhs
--         arg 1
--         arg 1
--         arg 2
--         intro a
--         rw [← Real.enorm_of_nonneg]
--         tactic =>
--           sorry
--         tactic =>

--           sorry
--       simp_rw [← Real.enorm_of_nonneg ?_] at bound_integral
--       have ae_lt := ae_lt_of_essSup_lt other_lt_top

--       sorry
--   . sorry

-- Defintion 3.11 in Vikman: The function 'μ',  not to be confused with a measure on a measure space
noncomputable def mu: G → ℝ := ((1 : ℝ) / (#(S) : ℝ)) • ∑ s ∈ S, Pi.single s (1 : ℝ)

-- Definition 3.11 in Vikman - the m-fold convolution of μ with itself
noncomputable def muConv (n: ℕ): G → ℝ := (Nat.iterate (Conv (S := S) (mu (S := S))) n) (mu (S := S))



abbrev delta (s: G): G → ℝ := Pi.single s 1

lemma conv_eq_sum {f h: G → ℝ} (hconv: ConvExists f h) (g: G): Conv f h g = ∑' (a : Additive Gᵐᵒᵖ), f (MulOpposite.unop (Additive.toMul a)) * h ((MulOpposite.unop (Additive.toMul a))⁻¹ * g) := by
  unfold Conv
  unfold MeasureTheory.convolution
  rw [MeasureTheory.integral_countable']
  .
    simp_rw [MeasureTheory.measureReal_def]
    unfold myHaarAddOpp
    simp_rw [MeasureTheory.Measure.addHaar_singleton]
    simp [MeasureTheory.Measure.addHaarMeasure_self]
    simp_rw [← singleton_carrier]
    simp_rw [TopologicalSpace.PositiveCompacts.carrier_eq_coe]
    simp [MeasureTheory.Measure.addHaarMeasure_self]
  . exact (hconv (opAdd g))

-- Old stuff for two LP_2 function - might be useful later
    -- unfold ConvExists MeasureTheory.ConvolutionExists MeasureTheory.ConvolutionExistsAt
    -- have my_exists := conv_exists (S := S) (p := 2) (q := 2) (by simp) (by simp) (by exact Real.HolderConjugate.two_two) f (delta s) hf ?_
    -- .
    --   intro x
    --   exact MeasureTheory.ConvolutionExistsAt.integrable (my_exists x)
    -- .
    --   intro x
    --   unfold delta
    --   apply Continuous.memLp_of_hasCompactSupport
    --   . exact continuous_of_discreteTopology
    --   .
    --     unfold HasCompactSupport
    --     rw [isCompact_iff_finite]
    --     dsimp [tsupport]
    --     rw [closure_discrete]

    --     apply Set.Finite.subset (s := {opAdd (x * s⁻¹)}) (by simp)
    --     intro a ha
    --     dsimp [Pi.single, Function.update] at ha
    --     simp at ha
    --     simp [opAdd]
    --     rw [← ha]
    --     simp

-- Proposition 3.12, item 1, in Vikman
lemma f_conv_delta (f: G → ℝ) (g s: G): (Conv (S := S) f (Pi.single s 1)) g = f (g * s⁻¹) := by

  rw [conv_eq_sum]
  .
    rw [tsum_eq_sum (s := {opAdd ((g * s⁻¹))}) ?_]
    .
      simp
      -- TODO - why does this need 'conv'?
      conv =>
        lhs
        arg 2
        arg 3
        simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right]
      simp
    .
      intro b hb
      simp only [Finset.mem_singleton] at hb
      simp only [mul_eq_zero]
      right
      apply Pi.single_eq_of_ne
      apply_fun (fun x => x * s⁻¹)
      simp only [mul_inv_cancel, ne_eq]
      apply_fun (fun x => (MulOpposite.unop (Additive.toMul b)) * x)
      conv =>
        lhs
        simp
        rw [← mul_assoc, ← mul_assoc]
        simp only [mul_inv_cancel, one_mul]
      simp only [mul_one, ne_eq]
      rw [eq_comm]
      unfold opAdd at hb
      apply_fun MulOpposite.op
      simp only [MulOpposite.op_unop, MulOpposite.op_mul, MulOpposite.op_inv, ne_eq]
      apply_fun Additive.ofMul
      simp only [ofMul_toMul]
      exact hb
  .
    apply conv_exists_fin_supp
    right
    simp

-- TODO - figure out why we need this
instance Real.t2Space: T2Space ℝ := TopologicalSpace.t2Space_of_metrizableSpace

lemma f_mul_mu_summable (f: G → ℝ) (g: G) (s: G):
  Summable fun a ↦
    (f (MulOpposite.unop (Additive.toMul a))) * (Pi.single (f := (fun s ↦ ℝ) ) s (1 : ℝ) (((MulOpposite.unop (Additive.toMul a))⁻¹ * g))) := by
  apply summable_of_finite_support
  simp only [one_div, Function.support_mul, Function.support_inv]
  apply Set.Finite.inter_of_right
  simp [Pi.single, Function.update]
  apply Set.Finite.subset (s := {(opAdd (g * s⁻¹))})
  . simp
  . intro a ha
    simp at ha
    simp [opAdd]
    simp [← ha]

-- Proposition 3.12, item 2, in Vikman
lemma f_conv_mu (f: G → ℝ) (hf: ConvExists f (mu (S := S))) (g: G): (Conv (S := S) f (mu (S := S))) g = ((1 : ℝ) / (#(S) : ℝ)) * ∑ s ∈ S, f (g * s) := by
  rw [conv_eq_sum]
  .

    dsimp [mu]
    simp_rw [← mul_assoc]
    conv =>
      lhs
      arg 1
      intro a
      rhs
      equals (∑ s ∈ S, (Pi.single s (1 : ℝ) ((MulOpposite.unop (Additive.toMul a))⁻¹ * g))) =>
        simp


        -- rw [tsum_eq_sum (s := Finset.image opAdd S) (by
        --   intro b hb
        --   simp
        --   right
        --   simp at hb
        --   simp [Pi.single, Function.update]
        --   simp [opAdd] at hb
        --   by_contra!
        --   simp_rw [← this] at hb
        --   sorry
        -- )]

    simp_rw [Finset.mul_sum]
    rw [Summable.tsum_finsetSum]
    .
      --rw [Finset.sum_comm]
      have delta_conv := f_conv_delta (S := S) f g
      conv at delta_conv =>
        intro x
        rw [conv_eq_sum (by
          apply conv_exists_fin_supp
          right
          simp
        )]

      simp_rw [mul_comm, mul_assoc]
      --simp_rw [← mul_tsum]
      conv =>
        lhs
        rhs
        intro x
        rw [Summable.tsum_mul_left (hf := by (
          apply f_mul_mu_summable
        ))]
        rw [delta_conv x]

      simp
      rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      rw [mul_comm]
      simp
      left
      conv =>
        lhs
        arg 1
        equals S⁻¹ =>
          exact S_eq_Sinv
      simp
    .
      intro s hs
      simp_rw [mul_comm, mul_assoc]
      simp only [one_div]
      by_cases card_zero: #(S) = 0
      .
        simp [card_zero]
        unfold Summable
        use 0
        exact hasSum_zero
      .
        rw [summable_mul_left_iff]
        . apply f_mul_mu_summable
        . field_simp
  . exact hf

-- The expression 'Σ s_1, ..., s_n ∈ S, f(s_1 * ... * s_n)'
-- This is a sum over all n-tuples of elements in S, where each term in is f (s_1 * ... * s_n)
-- TODO - is there aless horrible way to write in in mathlib?
def NTupleSum (n: ℕ) (f: G → ℝ): ℝ := ∑ s : (Fin n → S), f ((List.ofFn s).unattach.prod)
--∑ s ∈ (Finset.pi (Finset.range (n + 1))) (fun _ => S), f (List.ofFn (n := n + 1) (fun m => s m.val (by simp))).prod

-- The 'm + 1' terms are due to the fact that 'muConv 0' still applies mu once (without any convolution)
theorem mu_conv_eq_sum (m: ℕ) (g: G): muConv m g = (((1 : ℝ) / (#(S) : ℝ)) ^ (m + 1)) * (NTupleSum (S := S) (m + 1) (delta g))  := by
  induction m with
  | zero =>
    simp [muConv, NTupleSum, mu, delta, Pi.single, Function.update]
    by_cases g_in_s: g ∈ S
    .
      simp [g_in_s]
      conv =>
        rhs
        rhs
        rhs
        rhs
        equals {fun (a : Fin 1) => ⟨g, g_in_s⟩} =>
          ext a
          simp
          refine ⟨?_, ?_⟩
          . intro a_zero_eq
            ext x
            simp
            have x_eq_zero: x = 0 := by
              exact Fin.fin_one_eq_zero x
            rw [x_eq_zero]
            exact a_zero_eq
          . intro a_eq
            simp [a_eq]
      simp
    .
      simp [g_in_s]
      right
      by_contra this
      .
        simp at this
        apply Finset.nonempty_of_ne_empty at this
        obtain ⟨x, hx⟩ := Finset.Nonempty.exists_mem this
        simp at hx
        rw [← hx] at g_in_s
        simp at g_in_s
  | succ n ih =>
    sorry

-- structure ListPrefix {T: Type*} (n: ℕ) (head: T) (suffix target: List T): Prop where
--   suffix_neq: suffix ≠ []
--   suffix_head: suffix.head suffix_neq ≠ head
--   target_eq: (List.replicate n head) ++ suffix = target



-- lemma replicate_head (T: Type*) (l: List T) (a: T) (ha: a ∈ l): (l = List.replicate l.length a) ∨ (∃ n: ℕ, ∃ suffix: List T, ListPrefix n a suffix l)  := by
--   by_cases all_eq: ∀ x ∈ l, x = a
--   .
--     left
--     exact List.eq_replicate_of_mem all_eq
--   .
--     right



-- Based on https://github.com/YaelDillies/LeanCamCombi/blob/b6312bee17293272af6bdcdb47b3ffe98fca46a4/LeanCamCombi/GrowthInGroups/Lecture1.lean#L41
def HasPolynomialGrowthD (d: ℕ): Prop := ∀ n ≥ 2, #(S ^ n) ≤ n ^ d
def HasPolynomialGrowth: Prop := ∃ d, HasPolynomialGrowthD (S := S) d

lemma smaller_closure (T: Type*) (A B: Set T) (G: Group T) (hc: B ⊆ closure A) (hb: closure B = ⊤): closure A = ⊤ := by
  --apply?
  sorry

lemma S_nonempty: S.Nonempty := by
  exact Finset.nonempty_coe_sort.mp hS

variable [Inhabited G]

structure PreservesProd (T: Type*) (l h: List G) (γ: G) where
  prod_eq: l.prod = h.prod
  same_sum: (l.map (fun s => if s = γ then 1 else 0)).sum = (h.map (fun s => if s = γ then 1 else 0)).sum

set_option maxHeartbeats 500000

abbrev countElemOrInv {T: Type*} [ht: Group T] [heq: DecidableEq T] {E: Set T} (l: List E) (γ: T): ℤ := (l.map (fun (s: E) => if s = γ then 1 else if s = γ⁻¹ then -1 else 0)).sum
abbrev isElemOrInv {T: Type*} [ht: Group T] [heq: DecidableEq T] (g: T): T → Bool := fun a => decide (a = g ∨ a = g⁻¹)
lemma take_count_sum_eq_exp {T: Type*} [ht: Group T] [heq: DecidableEq T] {E: Set T} (l: List E) (g: T) (hg: g ≠ g⁻¹) (hl: ∀ val ∈ l, val = g ∨ val = g⁻¹): l.unattach.prod = g^(countElemOrInv l g) := by
  induction l with
  | nil =>
    simp [countElemOrInv]
  | cons h t ih =>
    simp [countElemOrInv]
    by_cases h_eq_g: h = g
    .
      simp [h_eq_g]
      rw [ih]
      . rw [← zpow_one_add]
      . simp at hl
        intro val hval
        have hl_right := hl.2 val (by simp) (by simp [hval])
        exact hl_right
    .
      have h_eq_inv: h = g⁻¹ := by
        specialize hl h
        simp at hl
        simp  [h_eq_g] at hl
        exact hl
      simp [h_eq_g, h_eq_inv]
      rw [ih]
      rw [← zpow_neg_one]
      rw [← zpow_add]
      simp [hg.symm]
      simp at hl
      intro val hval
      have hl_right := hl.2 val (by simp) (by simp [hval])
      exact hl_right

open Additive

def e_i_regular_helper (φ: (Additive G) →+ ℤ) (γ: G) (s: S): G := (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))

def E_helper (φ: (Additive G) →+ ℤ) (γ: G) := {γ, γ⁻¹} ∪ Set.range (ι := S) (e_i_regular_helper φ γ)

lemma take_drop_len {T: Type*} {l: List T} {p: T → Bool}: (l.takeWhile p).length + (l.dropWhile p).length = l.length := by
  suffices h: l.takeWhile p ++ l.dropWhile p = l by
    nth_rw 3 [← h]
    rw [List.length_append]
  exact List.takeWhile_append_dropWhile

lemma three_two (d: ℕ) (hd: d >= 1) (hG: HasPolynomialGrowthD d (S := S)) (g: G) (φ: (Additive G) →+ ℤ) (hφ: Function.Surjective φ): φ.ker.FG := by
  have gamma_one: ∃ γ: G, φ γ = 1 := by
    exact hφ 1

  obtain ⟨γ, hγ⟩ := gamma_one
  have phi_ofmul: φ (ofMul γ) = 1 := by
    exact hγ
  --
  let e_i: S → (Additive G) := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))
  let e_i_regular: S → G := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))



  let max_phi := max 1 ((Finset.image Int.natAbs (Finset.image φ (Finset.image ofMul S))).max' (by simp [S_nonempty]))
  --have nonempty_image := Finset(Finset.Nonempty.image S_nonempty ofMul)
  --have second_e

  have e_i_zero: ∀ s: S, φ (e_i s) = 0 := by
    intro s
    unfold e_i
    simp
    simp [phi_ofmul]

  have e_i_regular_zero: ∀ s: S, φ (ofMul (e_i_regular s)) = 0 := by
    dsimp [ofMul]
    intro s
    unfold e_i_regular
    simp
    simp [phi_ofmul]

  have e_i_ker: ∀ s: S, e_i s ∈ φ.ker := by
    intro s
    exact e_i_zero s

-- Subgroup.closure_eq_of_l

  let gamma_i := fun (i: ℕ) => γ^(i : ℤ)
  have closure_enlarge: Subgroup.closure ({1, γ, γ⁻¹} ∪ (e_i '' Set.univ)) = Subgroup.closure (({1, γ, γ⁻¹} ∪ (e_i_regular '' Set.univ))^(max_phi + 1)) := by
    rw [Subgroup.closure_pow]
    . simp
    . unfold max_phi
      simp
      -- have max_le := Finset.le_max' (Finset.image Int.natAbs (Finset.image φ (Finset.image ofMul S))) 1 ?_
      -- . exact Nat.ne_zero_of_lt max_le
      -- .
      --   simp
      --   use γ

    -- Subgroup.closure_pow
    -- Set.pow_mem_pow


  have new_closure_e_i: Subgroup.closure ({1, γ, γ⁻¹} ∪ (e_i '' Set.univ)) = (Subgroup.closure S) := by
    rw [closure_enlarge]
    apply Subgroup.closure_eq_of_le
    .
      rw [hGS.generates]
      exact fun ⦃a⦄ a ↦ trivial
    .
      simp
      intro s hs
      simp
      rw [← mem_toSubmonoid]
      rw [Subgroup.closure_toSubmonoid]
      dsimp [Membership.mem]
      rw [Submonoid.closure_eq_image_prod]
      -- TODO - why do we need any of this?
      dsimp [Set.Mem]
      rw [← Set.mem_def (a := s) (s := List.prod '' _)]
      rw [Set.mem_image]


      have foo := Submonoid.exists_list_of_mem_closure (s := ((S ∪ S⁻¹) : Set G)) (x := s)
      rw [← Subgroup.closure_toSubmonoid _] at foo
      simp only [mem_toSubmonoid, Finset.mem_coe] at foo
      have generates := hGS.generates
      have x_in_top: s ∈ (⊤: Set G) := by
        simp

      rw [← generates] at x_in_top
      specialize foo x_in_top
      obtain ⟨l, ⟨l_mem_s, l_prod⟩⟩ := foo
      simp [s_union_sinv] at l_mem_s

      let l_attach := l.attach
      let list_with_mem: List S := (l_attach).map (fun a => ⟨a.val, l_mem_s a.val a.prop⟩)
      let new_list := list_with_mem.map (fun s => (e_i s) + ofMul (γ^(((φ (ofMul s.val))))))

      have cancel_add_minus: max_phi - 1 + 1 = max_phi := by
        omega

      use new_list
      refine ⟨?_, ?_⟩
      .
        simp
        intro x hx
        unfold new_list list_with_mem l_attach at hx
        simp at hx
        obtain ⟨a, ha, x_eq_sum⟩ := hx
        left

        have gamma_phi_in: γ^(max_phi) ∈ ({1, γ, γ⁻¹} ∪ Set.range e_i_regular) ^ max_phi := by
          apply Set.pow_mem_pow
          simp

        have gamma_phi_in_minus_plus: γ^(φ a) ∈ ({1, γ, γ⁻¹} ∪ Set.range e_i_regular) ^ (max_phi - 1  +1) := by
          by_cases val_pos: 0 < φ a
          .
            have eq_self: Int.natAbs (φ a) = φ a := by
              simp [val_pos]
              linarith
            conv =>
              arg 2
              equals γ ^ (Int.natAbs (φ a)) =>
                nth_rw 1 [← eq_self]
                norm_cast
            apply Set.pow_subset_pow_right (m := Int.natAbs (φ a)) (n := max_phi - 1 + 1)
            . simp
            .
              rw [cancel_add_minus]
              unfold max_phi
              simp
              right
              apply Finset.le_max'
              simp
              use a
              refine ⟨l_mem_s a ha, ?_⟩
              conv =>
                pattern ofMul a
                equals a => rfl
            .
              apply Set.pow_mem_pow
              simp
          .
            have eq_neg_abs: (φ a) = -(φ a).natAbs := by
              rw [← Int.abs_eq_natAbs]
              simp at val_pos
              rw [← abs_eq_neg_self] at val_pos
              omega
            rw [eq_neg_abs]
            conv =>
              arg 2
              equals (γ⁻¹) ^ (↑(φ a).natAbs) =>
                simp
                rw [Int.abs_eq_natAbs]
                norm_cast
            -- TOOD - deduplicate this with the positive case
            apply Set.pow_subset_pow_right (m := Int.natAbs (φ a)) (n := max_phi - 1 + 1)
            . simp
            .
              rw [cancel_add_minus]
              unfold max_phi
              simp
              right
              apply Finset.le_max'
              simp
              use a
              refine ⟨l_mem_s a ha, ?_⟩
              conv =>
                pattern ofMul a
                equals a => rfl
            .
              apply Set.pow_mem_pow
              simp
        have a_mem_s: a ∈ S := by exact l_mem_s a ha

        have e_pi_s_mem: e_i_regular ⟨s, hs⟩ ∈ ({1, γ ,γ⁻¹} ∪ Set.range e_i_regular) := by
          simp

        have e_pi_a_mem: e_i_regular ⟨a, a_mem_s⟩ ∈ ({1, γ, γ⁻¹} ∪ Set.range e_i_regular) := by
          simp


        have max_phi_gt: 0 < max_phi := by
          simp [max_phi]

        let zero_fin: Fin max_phi := ⟨0, max_phi_gt⟩

        let one_instance: Fin max_phi → One ↑({1, γ, γ⁻¹} ∪ Set.range e_i_regular) := by
          intro i
          use 1
          simp

        have e_pi_s_mem_pow: e_i_regular ⟨a, l_mem_s a ha⟩ ∈ (({1, γ, γ⁻¹} ∪ Set.range e_i_regular)^(max_phi - 1 + 1)) := by
          rw [Set.mem_pow]
          --simp_rw [List.ofFn_eq_map]



          --rw [List.finRange_eq_pmap_range]

          let no_coe: Fin (max_phi - 1 + 1) → G := (Fin.cons (e_i_regular ⟨a, a_mem_s⟩) (fun (n: Fin (max_phi - 1)) => (1 : G)))

          use Fin.cons (⟨e_i_regular ⟨a, l_mem_s a ha⟩, e_pi_a_mem⟩) (fun n => ⟨1, by simp⟩)
          conv =>
            arg 1
            arg 1
            arg 1
            intro i
            equals no_coe i =>
              simp [no_coe]

              by_cases i_eq_zero: i = 0
              . simp [i_eq_zero]
              .
                have i_ne_zero : i ≠ 0 := by
                  exact i_eq_zero
                rw [← Fin.exists_succ_eq] at i_ne_zero
                obtain ⟨z, hz⟩ := i_ne_zero
                rw [← hz]
                simp

          unfold no_coe
          rw [List.ofFn_cons]
          simp


        have prod_mem_power: e_i_regular ⟨a, a_mem_s⟩ * γ ^ φ (ofMul a) ∈ ({1, γ, γ⁻¹} ∪ Set.range e_i_regular) ^ (max_phi - 1 + 1 + 1) := by
          rw [pow_succ']
          rw [Set.mem_mul]
          use e_i_regular ⟨a, a_mem_s⟩
          refine ⟨by simp, ?_⟩
          use γ ^ φ (ofMul a)
          refine ⟨gamma_phi_in_minus_plus, ?_⟩
          simp

        have prod_eq_sum: e_i ⟨a, l_mem_s a ha⟩ + φ (ofMul a) • ofMul γ = (e_i_regular ⟨a, a_mem_s⟩) * (γ ^ φ (ofMul a)) := by
          simp [e_i, e_i_regular, cancel_add_minus]


          conv =>
            rhs
            arg 1
            equals ofMul (a* γ^(-(φ (ofMul a)))) =>
              simp

          apply_fun (fun x => x * (γ ^ (- φ (ofMul a))))
          .
            simp only
            simp
            conv =>
              lhs
              equals a * (γ ^ φ (ofMul a))⁻¹ =>
                simp
                rfl
            conv =>
              rhs
              rhs
              equals ofMul (γ ^ (- φ (ofMul a))) =>
                simp

            rw [← ofMul_mul]
            conv =>
              rhs
              equals (a * γ ^ (-φ (ofMul a))) =>
                rfl
            simp
          .
            exact mul_left_injective (γ ^ (-φ (ofMul a)))






        rw [← x_eq_sum]
        rw [prod_eq_sum]
        rw [cancel_add_minus] at prod_mem_power
        apply prod_mem_power








      unfold new_list list_with_mem l_attach
      simp
      conv =>
        arg 1
        arg 1
        arg 1
        arg 1
        intro z
        unfold e_i
        simp
      simp
      conv =>
        arg 1
        arg 1
        arg 1
        equals id =>
          rfl
      simp
      exact l_prod
  let gamma_m := fun (m: ℤ) (s: S) => γ^m * (e_i s).toMul * γ^(-m)
  let a := Set.range (Function.uncurry gamma_m)
  have gamma_m_ker_phi: (Subgroup.closure (Set.range (Function.uncurry gamma_m))) = φ.ker.toSubgroup := by
    ext z
    refine ⟨?_, ?_⟩
    . intro hz
      have foo := Submonoid.exists_list_of_mem_closure (s := Set.range (Function.uncurry gamma_m) ∪ (Set.range (Function.uncurry gamma_m))⁻¹) (x := z)
      rw [← Subgroup.closure_toSubmonoid _] at foo
      specialize foo hz
      obtain ⟨l, ⟨l_mem_s, l_prod⟩⟩ := foo
      rw [← l_prod]
      rw [← MonoidHom.coe_toMultiplicative_ker]
      rw [MonoidHom.mem_ker]
      rw [MonoidHom.map_list_prod]
      apply List.prod_eq_one
      intro x hx
      simp at hx
      obtain ⟨a, a_mem_l, phi_a⟩ := hx
      specialize l_mem_s a a_mem_l
      unfold gamma_m at l_mem_s
      simp at l_mem_s
      rw [← phi_a]
      match l_mem_s with
      | .inl a_eq_prod =>
        obtain ⟨n, val, val_in_s, prod_eq_a⟩ := a_eq_prod
        rw [← prod_eq_a]
        simp
        have apply_mult := AddMonoidHom.toMultiplicative_apply_apply φ (toMul (e_i ⟨val, val_in_s⟩))
        conv at apply_mult =>
          rhs
          rhs
          arg 2
          equals e_i ⟨val, val_in_s⟩ => rfl
        rw [e_i_zero] at apply_mult
        exact apply_mult
      | .inr a_eq_prod =>
        obtain ⟨n, val, val_in_s, prod_eq_a⟩ := a_eq_prod
        apply_fun Inv.inv at prod_eq_a
        simp at prod_eq_a
        -- TODO - deduplicate this with the branch above
        rw [← prod_eq_a]
        simp
        have apply_mult := AddMonoidHom.toMultiplicative_apply_apply φ (toMul (e_i ⟨val, val_in_s⟩))
        conv at apply_mult =>
          rhs
          rhs
          arg 2
          equals e_i ⟨val, val_in_s⟩ => rfl
        rw [e_i_zero] at apply_mult
        exact apply_mult
    .
      intro hz

      -- We need to write 'γ^a (f⁻¹ )' as an element of e_i

      -- γ^(φ(f_1)) (f_1⁻¹ ) = f_2 γ^(-φ(f_2))

      -- have first_set_inv_self: ({(1 : G), γ, γ⁻¹} : (Set G)) = ( {(1 : G), γ, γ⁻¹} : (Set G))⁻¹ := by
      --   simp
      --   -- Why can't simp do this for us? Soemthing to do with the wrong '⁻¹' instances?
      --   rw [Set.pair_comm]

      -- This is *false* - we would need to be able t swap the order of 'f_i' and 'γ'
      -- have e_i_eq_inv: (e_i '' Set.univ) = -(e_i '' Set.univ) := by
      --   ext p
      --   refine ⟨?_, ?_⟩
      --   . intro hp
      --     simp [e_i] at hp
      --     simp [e_i]
      --     obtain ⟨a, a_mem, e_i_ap⟩ := hp
      --     use a⁻¹
      --     rw [S_eq_Sinv (S := S)]
      --     simp
      --     refine ⟨a_mem, ?_⟩

      --     simp_rw [← e_i_ap]
      --     use a⁻¹
      --     have eq_inv := S_eq_Sinv (S := S)
      --     rw [eq_inv]
      --     simp
      --     refine ⟨a_mem, ?_⟩
      --     apply_fun (fun x => (ofMul a) + x)
      --     .
      --       simp





      -- have new_set_inv_self: {(1 : G), γ, γ⁻¹} ∪ (e_i '' Set.univ) = -({(1 : G), γ, γ⁻¹} ∪ (e_i '' Set.univ)) := by
      --   ext p
        -- TODO - find a cleaner way of proving this
        -- refine ⟨?_, ?_⟩
        -- . intro hp
        --   simp at hp
        --   match hp with
        --   | .inl p_in_set =>
        --     match p_in_set with
        --     | .inl p_eq_one =>
        --       simp [p_eq_one]
        --       left
        --       left
        --       simp [neg]
        --       unfold toMul
        --       simp [Multiplicative.ofAdd]
        --       rfl
        --     | .inr p_eq_other =>
        --       match p_eq_other with
        --       | .inl p_eq_gamma =>
        --         simp [p_eq_gamma]
        --         left
        --         right
        --         right
        --         rfl
        --       | .inr p_eq_gamma_inv =>
        --         simp [p_eq_gamma_inv]
        --         left
        --         right
        --         left
        --         simp [neg]
        --         unfold toMul
        --         simp [Multiplicative.ofAdd]
        --         conv =>
        --           lhs
        --           arg 1
        --           equals γ⁻¹ => rfl
        --         simp
        --   | .inr p_in_set =>





      --have foo := Submonoid.exists_list_of_mem_closure (s := ({1, γ, γ⁻¹} ∪ (e_i '' Set.univ))) (x := z)
      have foo := Submonoid.exists_list_of_mem_closure (s := S ∪ S⁻¹) (x := z)
      --rw [s_union_sinv] at foo
      rw [← Subgroup.closure_toSubmonoid _] at foo
      --rw [← Subgroup.closure_toSubmonoid _] at foo
      rw [← new_closure_e_i] at foo
      rw [Subgroup.closure_toSubmonoid] at foo
      have generates := hGS.generates
      have z_in_top: z ∈ (⊤: Set G) := by
        simp
      rw [← generates] at z_in_top
      simp at z_in_top
      rw [s_union_sinv] at foo
      simp at foo
      --specialize foo (z_in_top)



      -- --rw [← Subgroup.closure_toSubmonoid] at foo
      -- rw [← new_closure_e_i] at foo
      -- rw [Subgroup.closure_toSubmonoid] at foo
      -- --rw [← Subgroup.closure_toSubmonoid _] at foo
      -- simp only [mem_toSubmonoid, Finset.mem_coe] at foo


      -- have foo := AddSubmonoid.exists_list_of_mem_closure (s := (φ.ker : Set (Additive G)) ∪ -(φ.ker)) (x := ofMul z)
      -- rw [← AddSubgroup.closure_toAddSubmonoid _] at foo
      -- rw [AddSubgroup.mem_toAddSubmonoid] at foo
      -- simp at foo
      -- --rw [Submonoid.toAddSubmonoid_closure] at foo
      -- specialize foo hz
      -- obtain ⟨l, ⟨l_mem_s, l_prod⟩⟩ := foo


      let E: Set G := {γ, γ⁻¹} ∪ Set.range e_i_regular ∪ (Set.range e_i_regular)⁻¹
      let gamma_sum: List E -> ℤ := fun (l) => l.count ⟨γ, by simp [E]⟩ - l.count ⟨γ⁻¹, by simp [E]⟩


      -- TODO: where do we add this? (hsum: gamma_sum list = 0)
      let rec rewrite_list (list: List (E)) (hlist: φ (ofMul list.unattach.prod) = 0): { t: List (((Set.range (Function.uncurry gamma_m) : (Set G)) ∪ (Set.range (Function.uncurry gamma_m))⁻¹ : (Set G))) // list.unattach.prod = t.unattach.prod } := by
        let is_gamma: E → Bool := fun (k: E) => k = γ ∨ k = γ⁻¹
        let is_gamma_prop: E → Prop := fun (k: E) => k = γ ∨ k = γ⁻¹
        have eq_split: list = list.takeWhile is_gamma ++ list.dropWhile is_gamma := by
          exact Eq.symm List.takeWhile_append_dropWhile
        by_cases header_eq_full: list.takeWhile is_gamma = list
        .
          have list_eq_gamma_m: ∃ m: ℤ, list.unattach.prod = γ ^ m := by
            unfold is_gamma at header_eq_full
            clear eq_split is_gamma is_gamma_prop hlist

            induction list with
            | nil =>
              use 0
              simp
            | cons h t ih =>
              have h_gamma: h = γ ∨ h = γ⁻¹ := by
                simp at header_eq_full
                exact header_eq_full.1
              rw [List.takeWhile_cons_of_pos] at header_eq_full
              .
                rw [List.cons_eq_cons] at header_eq_full
                specialize ih header_eq_full.2
                obtain ⟨m, hm⟩ := ih
                by_cases h_eq_gamma: h = γ
                .
                  use (m + 1)
                  simp [h_eq_gamma, hm]
                  exact mul_self_zpow γ m
                . use (-1 + m)
                  simp [h_eq_gamma] at h_gamma
                  simp [h_gamma, hm]
                  rw [← zpow_neg_one]
                  rw [zpow_add]
              . simp [h_gamma]


          have empty_prod_eq: list.unattach.prod = ([] : List E).unattach.prod := by
            obtain ⟨m, hm⟩ := list_eq_gamma_m
            rw [hm]
            simp
            rw [hm] at hlist
            simp at hlist
            simp [phi_ofmul] at hlist
            simp [hlist]

          exact ⟨[], empty_prod_eq⟩
        .

          have tail_nonempty: list.dropWhile is_gamma ≠ [] := by
            rw [not_iff_not.mpr List.takeWhile_eq_self_iff] at header_eq_full
            rw [← not_iff_not.mpr List.dropWhile_eq_nil_iff] at header_eq_full
            exact header_eq_full
          have list_nonempty: 0 < list.length := by
            rw [List.length_pos_iff]
            apply List.IsSuffix.ne_nil (xs := list.dropWhile is_gamma) (List.dropWhile_suffix _) tail_nonempty

          have dropwhile_len_gt: 0 < (list.dropWhile is_gamma).length := by
            exact List.length_pos_iff.mpr tail_nonempty

          have not_is_gamma := List.dropWhile_get_zero_not is_gamma list dropwhile_len_gt
          simp at not_is_gamma

          have not_is_gamma_prop: ¬ is_gamma_prop (List.dropWhile is_gamma list)[0] := by
            dsimp [is_gamma_prop]
            dsimp [is_gamma] at not_is_gamma
            exact of_decide_eq_false not_is_gamma

          simp [is_gamma_prop] at not_is_gamma_prop
          have drop_head_in_e_i: (List.dropWhile is_gamma list)[0].val ∈ (Set.range e_i_regular) ∪ (Set.range e_i_regular)⁻¹ := by
            have drop_in_E: (List.dropWhile is_gamma list)[0].val ∈ E := by
              simp [E]
            simp only [E] at drop_in_E
            simp_rw [Set.union_assoc] at drop_in_E
            rw [Set.mem_union] at drop_in_E
            have not_in_left: (List.dropWhile is_gamma list)[0].val ∉ ({γ, γ⁻¹} : Set G) := by
              simp [not_is_gamma_prop]

            -- TODO - why can't simp handle this?
            have in_right := Or.resolve_left drop_in_E not_in_left
            exact in_right


          let m := ((list.takeWhile is_gamma).map (fun (k : E) => if k = γ then 1 else if k = γ⁻¹ then -1 else 0)).sum

          have in_range: γ ^ m * ↑(List.dropWhile is_gamma list)[0] * γ ^ (-m) ∈ (Set.range (Function.uncurry gamma_m)) ∪ ((Set.range (Function.uncurry gamma_m)))⁻¹ := by
            simp [gamma_m]
            simp at drop_head_in_e_i
            match drop_head_in_e_i with
            | .inl drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              left
              use m
              use s
              use s_in_S
              simp
              rw [← eq_e_i]
              rfl
            | .inr drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              right
              use m
              use s
              use s_in_S
              conv =>
                rhs
                rw [← mul_assoc]
              simp
              rw [← eq_e_i]
              rfl

          have phi_ofmul_gamma: φ (ofMul γ) = 1 := by
            exact hγ

          have gamma_ne_inv: γ ≠ γ⁻¹ := by
            by_contra this
            apply_fun ofMul at this
            apply_fun φ at this
            rw [phi_ofmul_gamma] at this
            rw [ofMul_inv] at this
            rw [AddMonoidHom.map_neg] at this
            rw [phi_ofmul_gamma] at this
            omega

          let gamma_copy: List E := if (m >= 0) then List.replicate m.natAbs ⟨γ, by simp [E]⟩ else List.replicate (m.natAbs) ⟨γ⁻¹, by simp [E]⟩
          let gamma_copy_inv: List E := if (m >= 0) then List.replicate m.natAbs ⟨γ⁻¹, by simp [E]⟩ else List.replicate (m.natAbs) ⟨γ, by simp [E]⟩

          have count_gamma_copy: gamma_sum gamma_copy = m := by
            simp [gamma_sum, gamma_copy]
            by_cases m_ge: 0 ≤ m
            .
              simp [m_ge]
              rw [List.count_replicate]
              simp [gamma_ne_inv]
              exact m_ge
            .
              simp [m_ge]
              rw [List.count_replicate]
              simp [gamma_ne_inv.symm]
              simp at m_ge
              apply_fun (fun x => -x)
              .
                simp
                omega
              . exact neg_injective

          have count_gamma_inv_eq_zero: ∀ m, List.count ⟨γ⁻¹, by simp [E]⟩ ((List.replicate (α := E) m (⟨γ, by simp [E]⟩ : E))) = 0 := by
            intro m
            rw [List.count_replicate]
            simp [gamma_ne_inv]

          have count_gamma_eq_zero: ∀ m, ((List.replicate (α := E) m (Subtype.mk γ⁻¹ (by simp [E]) : E)).count ⟨γ, by simp [E]⟩ = 0) := by
            intro m
            rw [List.count_replicate]
            simp [gamma_ne_inv.symm]

          have count_gamma_copy_inv: gamma_sum gamma_copy_inv = -m := by
            simp [gamma_sum, gamma_copy_inv]
            by_cases m_ge: 0 ≤ m
            .
              simp [m_ge]
              rw [List.count_replicate]
              simp [gamma_ne_inv.symm]
              exact m_ge
            .
              simp [m_ge]
              rw [List.count_replicate]
              simp [gamma_ne_inv]
              omega


          -- have count_gamm_in_copy:  List.count ⟨γ⁻¹, by simp [E]⟩ gamma_copy = 0 := by
          --   simp [gamma_copy]
          --   by_cases m_ge: 0 ≤ m
          --   .
          --     simp [m_ge]
          --     rw [List.count_replicate]
          --     simp [gamma_ne_inv]
          --   .
          --     simp only [m_ge, ↓reduceIte]
          --     rw [List.count_replicate]
          --     simp [gamma_ne_inv.symm]
          --     omega

          have gamma_sum_head: gamma_sum (gamma_copy ++ [(List.dropWhile is_gamma list)[0]] ++ gamma_copy_inv) = 0 := by
            simp [gamma_sum]
            rw [add_comm, sub_eq_add_neg]
            simp [List.count_cons]
            dsimp [gamma_sum] at count_gamma_copy
            rw [add_assoc]
            conv =>
              lhs
              rhs
              rhs
              rw [add_comm]
            rw [add_assoc]
            conv =>
              lhs
              rhs
              rhs
              rw [← add_assoc]
              lhs
              rw [← sub_eq_add_neg]
              rw [count_gamma_copy]


            simp [gamma_sum] at count_gamma_copy_inv
            conv =>
              lhs
              rw [← add_assoc]
              rhs
              rw [add_comm]
              lhs
              rw [add_comm]
            rw [add_assoc]
            conv =>
              lhs
              rhs
              rw [add_comm]
            rw [← add_assoc]
            rw [← add_assoc]
            rw [← add_assoc]
            rw [← sub_eq_add_neg, ← sub_eq_add_neg]
            rw [count_gamma_copy_inv]
            abel
            simp [not_is_gamma_prop.left]
            simp [not_is_gamma_prop.right]

          have gamma_sum_split (p q: List E): gamma_sum (p ++ q) = gamma_sum p + gamma_sum q := by
            simp [gamma_sum]
            abel

          have gamma_copy_prod: gamma_copy.unattach.prod = γ^m := by
            simp [gamma_copy]
            by_cases m_ge: 0 ≤ m
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              rw [← abs_eq_self] at m_ge
              rw [m_ge]
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              simp at m_ge
              have m_le: m ≤ 0 := by omega
              rw [← abs_eq_neg_self] at m_le
              simp [m_le]

          have gamma_copy_inv_prod: gamma_copy_inv.unattach.prod = γ^(-m) := by
            simp [gamma_copy_inv]
            by_cases m_ge: 0 ≤ m
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              rw [← abs_eq_self] at m_ge
              rw [m_ge]
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              simp at m_ge
              have m_le: m ≤ 0 := by omega
              rw [← abs_eq_neg_self] at m_le
              simp [m_le]

          have E_inhabited: Inhabited E := by
            use γ
            simp [E]

          have header_prod: (List.takeWhile is_gamma list).unattach.prod = γ^m := by
            have my_lemma := take_count_sum_eq_exp (List.takeWhile is_gamma list) γ gamma_ne_inv ?_
            .
              rw [my_lemma]
            .
              have foo (x: E) := List.mem_takeWhile_imp (p := fun (val: E) => (val = γ ∨ val = γ⁻¹)) (l := list) (x := x)
              conv at foo =>
                intro x hx
                equals ↑x = γ ∨ ↑x = γ⁻¹ =>
                  simp
              exact foo

          -- 'γ^n * a * γ^(_n) * γn * tail', as a list of elements in E
          let mega_list := (gamma_copy ++ [(List.dropWhile is_gamma list)[0]] ++ gamma_copy_inv) ++ (gamma_copy ++ (list.dropWhile is_gamma).tail)
          have mega_list_prod: mega_list.unattach.prod = list.unattach.prod := by
            simp [mega_list]
            simp [gamma_copy_prod, gamma_copy_inv_prod]
            conv =>
              rhs
              rw [eq_split]
              rw [List.unattach_append]
              simp
            have dropwhile_not_nul : (List.dropWhile is_gamma list) ≠ [] := by
              exact tail_nonempty
            --have dropwhile_len-
            apply_fun (fun x => x * (List.dropWhile is_gamma list).unattach.prod⁻¹)
            .
              simp
              conv =>
                pattern _[0]
                equals (List.dropWhile is_gamma list).headI =>
                  rw [← List.head_eq_getElem_zero dropwhile_not_nul]
                  rw [← List.getI_zero_eq_headI]
                  rw [List.head_eq_getElem_zero]
                  exact
                    Eq.symm
                      (List.getI_eq_getElem (List.dropWhile is_gamma list)
                        (List.length_pos_iff.mpr dropwhile_not_nul))

              have unattach_len_pos: 0 < (List.dropWhile is_gamma list).unattach.length := by
                rw [List.length_unattach]
                exact List.length_pos_iff.mpr dropwhile_not_nul

              conv =>
                lhs
                lhs
                rhs
                equals (List.dropWhile is_gamma list).unattach.headI * (List.dropWhile is_gamma list).unattach.tail.prod =>
                  rw [← List.getI_zero_eq_headI]
                  rw [← List.getI_zero_eq_headI]
                  rw [List.getI_eq_getElem _ (List.length_pos_iff.mpr dropwhile_not_nul)]
                  rw [List.getI_eq_getElem _ unattach_len_pos]
                  simp [List.getElem_unattach _ unattach_len_pos]
                  rw [list_tail_unattach]

              rw [List.headI_mul_tail_prod_of_ne_nil]
              .
                simp
                simp [header_prod]
              .
                by_contra this
                rw [List.eq_nil_iff_length_eq_zero] at this
                rw [List.length_unattach] at this
                rw [← List.eq_nil_iff_length_eq_zero] at this
                contradiction


            . exact mul_left_injective (List.dropWhile is_gamma list).unattach.prod⁻¹

          have sublist_phi_zero: φ (gamma_copy ++ (List.dropWhile is_gamma list).tail).unattach.prod = 0 := by
            rw [← mega_list_prod] at hlist
            unfold mega_list at hlist
            simp at hlist
            simp at drop_head_in_e_i
            match drop_head_in_e_i with
            | .inl drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              rw [← eq_e_i] at hlist
              simp [e_i_regular_zero] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              rw [gamma_copy_prod, gamma_copy_inv_prod] at hlist
              simp at hlist
              rw [← ofMul_list_prod] at hlist
              rw [← ofMul_list_prod] at hlist
              simp
              conv =>
                lhs
                arg 2
                equals (ofMul gamma_copy.unattach.prod) + (ofMul (List.dropWhile is_gamma list).tail.unattach.prod) =>
                  rfl

              simp
              rw [← ofMul_list_prod]
              rw [← ofMul_list_prod]
              exact hlist
            | .inr drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              rw [inv_eq_iff_eq_inv.symm] at eq_e_i
              rw [← eq_e_i] at hlist
              simp [e_i_regular_zero] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              rw [gamma_copy_prod, gamma_copy_inv_prod] at hlist
              simp at hlist
              rw [← ofMul_list_prod] at hlist
              rw [← ofMul_list_prod] at hlist
              simp
              conv =>
                lhs
                arg 2
                equals (ofMul gamma_copy.unattach.prod) + (ofMul (List.dropWhile is_gamma list).tail.unattach.prod) =>
                  rfl

              simp
              rw [← ofMul_list_prod]
              rw [← ofMul_list_prod]
              exact hlist

          have gamma_copy_len: gamma_copy.length = m.natAbs := by
            simp [gamma_copy]
            split_ifs <;> simp

          have gamma_copy_inv_len: gamma_copy_inv.length = m.natAbs := by
            simp [gamma_copy_inv]
            split_ifs <;> simp

          have count_head_lt: (List.map (fun (k: E) ↦ if ↑k = γ then (1 : ℤ) else if ↑k = γ⁻¹ then -1 else 0)
          (List.takeWhile (fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹)) list)).sum.natAbs ≤ (List.takeWhile (fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹)) list).length := by
            induction (List.takeWhile (fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹)) list) with
            | nil =>
              simp
            | cons h t ih =>
              simp
              split_ifs
              . omega
              . omega
              . omega

          have take_drop_le: ((List.takeWhile (fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹)) list)).length + ((List.dropWhile (fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹)) list)).length = list.length := by
            apply take_drop_len


          let rewritten_sub_list := (rewrite_list (gamma_copy ++ (list.dropWhile is_gamma).tail) sublist_phi_zero)
          let return_list := (⟨γ^m * (List.dropWhile is_gamma list)[0] * γ^(-m), in_range⟩) :: rewritten_sub_list.val

          -- Show that the list (rewritten in terms of `γ^m * e_i * γ^(-m)` terms) is in the kernel of φ
          -- have return_list_kernel: φ (ofMul return_list.unattach.prod) = 0 := by
          --   simp
          --   rw [AddMonoidHom.map_list_sum]
          --   apply List.sum_eq_zero
          --   intro x hx
          --   simp at hx
          --   obtain ⟨a, ⟨⟨q, r, r_mem_s, gamma_r⟩, a_mem_list⟩, phi_a⟩ := hx
          --   rw [← phi_a, ← gamma_r]
          --   simp [gamma_m]
          --   apply e_i_zero



          have sublist_prod_preserve: rewritten_sub_list.val.unattach.prod = (gamma_copy ++ (list.dropWhile is_gamma).tail).unattach.prod := by
            rw [← rewritten_sub_list.property]



          have mega_list_prod_preserve: mega_list.unattach.prod = return_list.unattach.prod := by
            unfold mega_list return_list
            simp
            rw [gamma_copy_prod]
            rw [gamma_copy_inv_prod]
            simp
            rw [← rewritten_sub_list.property]
            simp
            rw [gamma_copy_prod]
            conv =>
              rhs
              rw [mul_assoc]
              rhs
              rw [← mul_assoc]
              simp
            rw [mul_assoc]

          have return_list_prod: list.unattach.prod = return_list.unattach.prod := by
            rw [← mega_list_prod_preserve]
            exact mega_list_prod.symm


          exact ⟨return_list, return_list_prod⟩
      --termination_by list.countP (fun (k : E_helper φ γ) => decide (k.val ∈ Set.range (e_i_regular_helper (G := G) φ γ)))
      termination_by list.length
      decreasing_by {
        simp
        simp [gamma_copy] at gamma_copy_len
        simp [gamma_copy_inv] at gamma_copy_inv_len
        dsimp [gamma_sum] at count_gamma_copy
        dsimp [gamma_sum] at count_gamma_copy_inv
        split_ifs
        .
          simp [count_gamma_copy]
          conv =>
            rhs
            rw [← take_drop_len (p := fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹))]
          apply add_lt_add_of_le_of_lt
          . apply count_head_lt
          . simp [is_gamma] at dropwhile_len_gt
            apply Nat.sub_one_lt
            apply Nat.pos_iff_ne_zero.mp dropwhile_len_gt
        .
          simp [count_gamma_copy]
          conv =>
            rhs
            rw [← take_drop_len (p := fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹))]
          apply add_lt_add_of_le_of_lt
          . apply count_head_lt
          . simp [is_gamma] at dropwhile_len_gt
            apply Nat.sub_one_lt
            apply Nat.pos_iff_ne_zero.mp dropwhile_len_gt
      }

      let my_res := rewrite_list (l.map ( fun g => ⟨g.toMul, by simp [E]⟩)) sorry

      --let a := rewrite_list [] (by sorry)
      sorry
  sorry
-- Decompose list of {e_k, γ}:

-- The starting list must have the powers of γ sum to zero (since it's in the kernel of φ)


-- Map the list in a way that maintains the invariant that the powers of γ sum to zero:
-- If the head is e_i, then map it to γ_0,i = e_i
-- Otherwise, collect gamma terms:
-- If we get γ^a e_i * γ^b, then
-- * If the head is γ^n e_i for some n (collecting up adjacent γ), then choose γ_n,i = γ^n * e_i * γ^(-n)
-- * If the remaining list is just γ^n, then n must be 0 (since we maintained the invariant)
