import Mathlib

set_option linter.style.longLine false
set_option linter.style.cdot false
--set_option linter.unusedVariables true
--set_option linter.unusedVariables.analyzeTactics true

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
  -- This should be fine, since the growth rate doesn't depend on the generating set
  one_mem: (1 : G) ∈ S
  has_inv: ∀ g ∈ S, g⁻¹ ∈ S




variable {S S' : Finset G} [hGS: Generates (G := G) (S := S)] [hS: Nonempty S]
-- [hGS': Generates (G := G) (S := S')] [hS': Nonempty S]


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

instance G_FG: Group.FG G := {
  out := by
    unfold Subgroup.FG
    use S
    have foo := hGS.generates
    simp at foo
    exact foo
}



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

def IsLipschitz (f: G → ℂ) := ∃ C, LipschitzWith C f

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



lemma S_nonempty: S.Nonempty := by exact Finset.nonempty_coe_sort.mp hS

def ConstLipschitzH (z: ℂ) : LipschitzH (G := G) := {
  toFun := fun x => z
  lipschitz := by
    use 0
    apply LipschitzWith.const
  harmonic := by
    unfold Harmonic
    intro x
    simp
    field_simp
    have card_ne_zero: (#(S) : ℂ) ≠ 0 := by
      sorry
    field_simp
}

lemma ConstLipschitzH_apply (z : ℂ) (g: G): (ConstLipschitzH (G := G) z) g = z := by
  unfold ConstLipschitzH
  rfl

instance LipschitzH.zero [Generates (S := S)] : Zero (LipschitzH (G := G)) := {
  zero := {
    toFun := fun x => 0
    lipschitz := by
      use 0
      exact LipschitzWith.const 0
    harmonic := by simp [Harmonic]
  }
}


@[simp]
theorem LipschitzH.add_apply (f g: LipschitzH (G := G)) (x: G): (f + g).toFun x = f x + g x := by
  unfold LipschitzH.add
  rfl

instance lipschitzSMul: SMul ℂ (LipschitzH (G := G)) := {
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
}

instance LipschitzH.addMonoid [Generates (S := S)] : AddMonoid (LipschitzH (G := G)) := {
  LipschitzH.zero,
  LipschitzH.add with
  add_assoc := fun _ _ _ => ext fun _ => add_assoc _ _ _
  zero_add := fun _ => ext fun _ => zero_add _
  add_zero := fun _ => ext fun _ => add_zero _
  nsmul := fun n f => (n : ℂ) • f
  nsmul_zero := by
    intro f
    dsimp [HSMul.hSMul, SMul.smul]
    dsimp [OfNat.ofNat]
    dsimp [Zero.zero]
    simp
  nsmul_succ := by
    sorry
}


-- -- See https://github.com/leanprover-community/mathlib4/blob/6c6e0180f0d3dc9f47f85532f48d268d8656789a/Mathlib/Topology/ContinuousMap/Bounded/Normed.lean#L194-L196
-- instance lipschitzHAddCommGroup: AddCommGroup (LipschitzH (G := G)) := by
--   apply DFunLike.coe_injective.addCommGroup
--   .
--     ext g
--     simp [DFunLike.coe]
--     unfold Zero.toOfNat0
--     simp [Zero.zero]
--   .
--     intro x y
--     simp [DFunLike.coe]
--     ext g
--     simp [DFunLike.coe]
--   . intro f
--     ext g
--     simp [DFunLike.coe]
--     simp [negLipschitzH]
--   .
--     intro f h
--     ext g
--     simp [DFunLike.coe]
--     conv =>
--       lhs
--       dsimp [HSub.hSub]
--     simp [subLipschithZ]
--     simp [DFunLike.coe]
--     simp [negLipschitzH]
--     rw [sub_eq_add_neg]
--   . intro f
--     intro n
--     simp [DFunLike.coe]
--     dsimp [HSMul.hSMul]
--     dsimp [SMul.smul]



instance negLipschitzH: Neg (LipschitzH (G := G)) := {
  neg := fun f => {
    toFun := fun x => -f.toFun x
    lipschitz := by
      obtain ⟨C, hC⟩ := f.lipschitz
      use C
      exact LipschitzWith.neg hC
    harmonic := by
      have f_harmonic := f.harmonic
      simp [Harmonic] at f_harmonic
      unfold Harmonic
      intro g
      simp
      specialize f_harmonic g
      exact f_harmonic
  }
}

-- TODO - is there an existing instance we should be using here?
instance subLipschithZ: Sub (LipschitzH (G := G)) := {
  sub := fun f g => f + -g
}

instance lipschitzSmulZ: SMul ℤ (LipschitzH (G := G)) := {
  smul := fun n f => (n : ℂ) • f
}

instance LipschitzH.instAddCommMonoid: AddCommMonoid (LipschitzH (G := G)) := {
  LipschitzH.addMonoid with add_comm := fun _ _ => ext fun _ => add_comm _ _
}

instance LipschitzH.instAddCommGroup: AddCommGroup (LipschitzH (G := G)) := {
  LipschitzH.instAddCommMonoid with
  sub_eq_add_neg := by
    intro f h
    sorry
  zsmul := fun n f => (n : ℂ) • f
  zsmul_zero' := by
    intro f
    dsimp [HSMul.hSMul, SMul.smul]
    ext g
    simp [DFunLike.coe]
    unfold Zero.toOfNat0
    unfold OfNat.ofNat
    simp [Zero.zero]
  neg_add_cancel := by
    intro f
    ext g
    simp
    simp [negLipschitzH]
    simp [DFunLike.coe]
    unfold Zero.toOfNat0
    unfold OfNat.ofNat
    simp [Zero.zero]
  zsmul_succ' := by sorry
  zsmul_neg' := by
    intro n hn
    simp
    sorry
}


-- V is the vector space
abbrev V := Module ℂ (LipschitzH (G := G))




lemma zero_apply (x: G): (0: LipschitzH (G := G) (S := S)).toFun x = 0 := by
  unfold LipschitzH.zero
  rfl

--set_option pp.all true

instance lipschitzHVectorSpace : V (G := G) := {
  smul := lipschitzSMul.smul
  one_smul := by simp [HSMul.hSMul, SMul.smul]
  mul_smul := by
    intro x y f
    simp [HSMul.hSMul, SMul.smul]
    ext g
    rw [mul_assoc]
  smul_zero := by
    intro c
    dsimp [HSMul.hSMul, SMul.smul]
    ext g
    simp
    have foo := zero_apply g
    rw [foo]
    simp
  smul_add := by
    intro a f g
    dsimp [HSMul.hSMul, SMul.smul]
    simp [mul_add]
    ext p
    simp [DFunLike.coe]
  add_smul := by
    intro a f g
    dsimp [HSMul.hSMul, SMul.smul]
    simp [add_mul]
    ext p
    simp [DFunLike.coe]
  zero_smul := by
    intro a
    dsimp [HSMul.hSMul, SMul.smul]
    dsimp [OfNat.ofNat]
    dsimp [Zero.zero]
    simp
}

instance V_FiniteDimentional: FiniteDimensional ℂ (LipschitzH (G := G)) := by
  -- This is a very long part of the proof in Vikman
  sorry

def ConstF: Submodule ℂ (LipschitzH (G := G)) := {
  carrier := Set.range ConstLipschitzH
  add_mem' := by
    intro a b ha hb
    simp at ha
    simp at hb
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    simp
    use (x + y)
    ext g
    simp [ConstLipschitzH]
    rw [← hx, ← hy]
    dsimp [ConstLipschitzH]
    simp [DFunLike.coe]
  zero_mem' := by
    use (0 : ℂ)
    simp [ConstLipschitzH]
    ext g
    simp [DFunLike.coe]
    dsimp [OfNat.ofNat]
    simp [Zero.zero]
  smul_mem' := by
    intro c f hf
    simp at hf
    simp
    obtain ⟨x, hx⟩ := hf
    use (c * x)
    ext g
    simp [ConstLipschitzH]
    simp [HSMul.hSMul, SMul.smul]
    left
    rw [← hx]
    simp [ConstLipschitzH]
}

instance isometricGMul: IsIsometricSMul G G where
  isometry_smul := by
    intro g
    simp [Isometry]
    intro a b
    simp [edist]
    simp [PseudoMetricSpace.edist]
    simp [WordDist]
    group



def gAct (g: G) (v: LipschitzH (S := S)): LipschitzH (S := S) := {
  toFun := fun x => v (g⁻¹ * x)
  lipschitz := by
    obtain ⟨C, hC⟩ := v.lipschitz
    use C
    simp [LipschitzWith]
    intro x y
    simp [LipschitzWith] at hC
    specialize hC (g⁻¹ * x) (g⁻¹ * y)
    simp [DFunLike.coe]
    simp at hC
    exact hC
  harmonic := by
    unfold Harmonic
    intro x
    have v_harmonic := v.harmonic
    simp [Harmonic] at v_harmonic
    specialize v_harmonic (g⁻¹ * x)
    simp [DFunLike.coe]
    simp_rw [← mul_assoc]
    exact v_harmonic
}


def gAct_const (g: G) (z: ℂ): gAct g (ConstLipschitzH z) = ConstLipschitzH z := by
  unfold gAct
  unfold ConstLipschitzH
  ext x
  simp [DFunLike.coe]

#synth Module ℂ (LipschitzH (G := G))
#synth AddCommGroup (LipschitzH (G := G))

abbrev W := (LipschitzH (G := G)) ⧸ ConstF

@[simp]
lemma lipschitz_neg_tofun (f: LipschitzH (G := G)): (-f).toFun = -(f.toFun) := by
  rfl


lemma lipschitz_add_tofun (f g: LipschitzH (G := G)): (f + g).toFun = f.toFun + g.toFun := by
  rfl


lemma lipschitz_sub_tofun (f g: LipschitzH (G := G)): (f - g).toFun = f.toFun - g.toFun := by
  rfl


def gActW (g: G): W (G := G) → W (G := G) := Quotient.lift (fun f => Submodule.Quotient.mk (gAct g f)) (by
  intro f h hfh
  simp
  rw [Submodule.Quotient.eq']
  dsimp [HasEquiv.Equiv] at hfh
  rw [ConstF.quotientRel_def] at hfh
  dsimp [gAct]
  simp [HAdd.hAdd]
  dsimp [Add.add]
  simp [ConstF] at hfh
  obtain ⟨z, hz⟩ := hfh
  simp [ConstLipschitzH] at hz
  simp [ConstF]
  simp [ConstLipschitzH]
  use -z
  ext a
  apply_fun LipschitzH.toFun at hz
  have app_eq := congrFun hz (g⁻¹ * a)
  simp at app_eq
  rw [lipschitz_sub_tofun] at app_eq
  simp at app_eq
  rw [app_eq]
  simp
  rw [sub_eq_add_neg]
  rw [add_comm]
  rfl
)



noncomputable def LipschitzSemiNorm (f: G → ℂ): NNReal := sInf { k: NNReal | LipschitzWith k f }

-- The lift of LipschitzSemiNorm to W, using a proof that LipschitzSemiNorm doesn't depend on the choice representative
-- (adding a constant to a Lipschitz function doesn't change its Lipschitz constant)
noncomputable def LipschitzSemiNorm_w (w: W (G := G)) := Quotient.lift ((fun f => LipschitzSemiNorm (G := G) f.toFun)) (by
  intro f g hfg
  dsimp [HasEquiv.Equiv] at hfg
  rw [ConstF.quotientRel_def] at hfg
  simp [ConstF] at hfg
  obtain ⟨k, hk⟩ := hfg
  have f_eq_g_k: f = g + (ConstLipschitzH k) := by
    exact Eq.symm (add_eq_of_eq_sub' hk)
  rw [f_eq_g_k]
  simp [LipschitzSemiNorm]
  simp [LipschitzWith]
  simp_rw [edist_eq_enorm_sub]
  simp_rw [ConstLipschitzH_apply]
  simp [DFunLike.coe]
) w



lemma lipschiz_norm_zero: LipschitzSemiNorm (S := S) (0) = 0 := by
  unfold LipschitzSemiNorm
  have zero_mem: 0 ∈ { k: NNReal | LipschitzWith k (0 : LipschitzH (G := G)) } := by
    simp
    apply LipschitzWith.const
  have sinf_le: sInf { k: NNReal | LipschitzWith k (0 : LipschitzH (G := G)) } ≤ 0 := by
    exact csInf_le' zero_mem
  exact nonpos_iff_eq_zero.mp sinf_le



#synth IsStrictOrderedRing NNReal

-- TODO - upstream to mathlib
lemma lipschitz_attains_norm (f: G → ℂ) (hf: IsLipschitz f): LipschitzWith (LipschitzSemiNorm (G := G) f) f := by
  by_contra!
  have orig_this := this
  simp [LipschitzWith] at this
  obtain ⟨x, y, hdist⟩ := this
  have edist_ne_zero: edist x y ≠ 0 := by
    by_contra!
    rw [this] at hdist
    simp at this
    rw [this] at hdist
    simp at hdist

  have edist_not_top: edist x y ≠ ⊤ := by
    rw [edist_nndist]
    exact ENNReal.coe_ne_top

  rw [← ENNReal.lt_div_iff_mul_lt (by simp) (Or.inl edist_not_top)] at hdist
  simp [LipschitzSemiNorm] at hdist
  have isglb_sinf := isGLB_csInf (s := { k: NNReal | LipschitzWith k f }) (by
    obtain ⟨K, hK⟩ := hf
    use K
    simp
    exact hK
  ) (by simp)



  have between := IsGLB.exists_between (b := (edist (f x) (f y) / edist x y).toNNReal) isglb_sinf (by
    rw [edist_nndist]
    rw [edist_nndist]
    conv =>
      rhs
      equals (nndist (f x) (f y)) / (nndist x y) =>
        rw [← ENNReal.coe_div]
        simp
        exact ENNReal.coe_ne_zero.mp edist_ne_zero

    rw [edist_nndist] at hdist
    rw [edist_nndist] at hdist
    have edist_gt_zero: edist x y > 0 := by
      exact pos_of_ne_zero edist_ne_zero

    have x_ne_y := edist_pos.mp edist_gt_zero

    conv at hdist =>
      rhs
      equals ENNReal.ofNNReal ((nndist (f x) (f y)) / (nndist x y)) =>
        rw [ENNReal.coe_div]
        simp [x_ne_y]


    norm_cast at hdist
  )
  obtain ⟨D, lipschitz_d, sinf_le_d, d_lt_slope⟩ := between
  simp [LipschitzWith] at lipschitz_d
  specialize lipschitz_d x y
  rw [mul_comm] at lipschitz_d
  apply ENNReal.div_le_of_le_mul' at lipschitz_d
  repeat rw [edist_nndist] at lipschitz_d
  repeat rw [edist_nndist] at d_lt_slope
  rw [← ENNReal.coe_div] at lipschitz_d
  .
    norm_cast at lipschitz_d
    rw [← ENNReal.coe_div] at d_lt_slope
    .
      norm_cast at d_lt_slope
      apply not_lt_of_le at lipschitz_d
      contradiction
    . rw [edist_nndist] at edist_ne_zero
      exact fun a ↦ edist_ne_zero (congrArg ENNReal.ofNNReal a)
  . rw [edist_nndist] at edist_ne_zero
    exact fun a ↦ edist_ne_zero (congrArg ENNReal.ofNNReal a)

lemma lipschitz_norm_triangle (x y z: G → ℂ) (hx: IsLipschitz x) (hy: IsLipschitz y) (hz: IsLipschitz z): LipschitzSemiNorm (G := G) (x - z) ≤ LipschitzSemiNorm (G := G) (x - y) + LipschitzSemiNorm (G := G) (y - z) := by
  simp [LipschitzSemiNorm]
  conv =>
    pattern x - z
    equals (x - y) + (y - z) =>
      field_simp


  have sum_norm_mem: (LipschitzSemiNorm (x - y)) + (LipschitzSemiNorm (y - z)) ∈ { k: NNReal | LipschitzWith k ((x - y) + (y - z)) } := by
    simp only [LipschitzSemiNorm]
    apply LipschitzWith.add
    .
      apply lipschitz_attains_norm
      simp [IsLipschitz]
      simp [IsLipschitz] at hx
      simp [IsLipschitz] at hy
      obtain ⟨X, hX⟩ := hx
      obtain ⟨Y, hY⟩ := hy
      use X + Y
      apply LipschitzWith.sub hX hY
    .
      apply lipschitz_attains_norm
      simp [IsLipschitz]
      simp [IsLipschitz] at hy
      simp [IsLipschitz] at hz
      obtain ⟨Y, hY⟩ := hy
      obtain ⟨Z, hZ⟩ := hz
      use Y + Z
      apply LipschitzWith.sub hY hZ

  have sinf_le_sum := csInf_le (by simp) sum_norm_mem
  simp [LipschitzSemiNorm] at sinf_le_sum
  conv at sinf_le_sum =>
    pattern x - z
    equals (x - y) + (y - z) =>
      field_simp
  exact sinf_le_sum


lemma lipschitzH_norm_triangle (x y z: LipschitzH (G := G)): LipschitzSemiNorm (G := G) (x - z) ≤ LipschitzSemiNorm (G := G) (x - y) + LipschitzSemiNorm (G := G) (y - z) := by
  apply lipschitz_norm_triangle x y z x.lipschitz y.lipschitz z.lipschitz



--def lift_triangle (x y z: LipschitzH) := Quotient.lift lipschitzH_norm_triangle sorry

noncomputable instance LipschitzH_seminorm: SeminormedAddCommGroup (LipschitzH (G := G)) where
  norm := fun v => LipschitzSemiNorm (G := G) v
  dist_self := by
    intro v
    simp [LipschitzSemiNorm]
    exact lipschiz_norm_zero
  dist_comm := by
    intro x y
    simp [LipschitzSemiNorm]
    simp [DFunLike.coe]
    conv =>
      lhs
      pattern x - y
      equals -(y - x) =>
        field_simp
    simp_rw [lipschitz_neg_tofun]
    simp_rw [lipschitzWith_neg_iff]
  dist_triangle := by
    intro x y z
    simp
    apply lipschitzH_norm_triangle

-- Note that we only implement SeminormedAddCommGroup for LipschitzH, so this is only
-- really a seminormed space. The quotient space W := LipschitzH ⧸ ConstF
-- is an actual normed space.
noncomputable instance LipschitzH_normed: NormedSpace ℂ (LipschitzH (G := G)) where
  norm_smul_le := by
    intro c f
    simp [HSMul.hSMul, SMul.smul]
    simp [norm]
    conv =>
      lhs
      simp [LipschitzSemiNorm]
    norm_cast
    apply csInf_le (by
      simp [BddBelow]
      apply Set.nonempty_of_mem (x := 0)
      rw [mem_lowerBounds]
      simp
    )
    simp
    let K := LipschitzSemiNorm (G := G) f
    have hK := lipschitz_attains_norm f (f.lipschitz)
    use ‖ (c * K) ‖₊
    simp
    have comp_mul_const := LipschitzWith.comp (Kf := ‖c‖₊) (Kg := K) (f := fun x => c • x) (g := f.toFun) (by apply lipschitzWith_smul) hK
    simp at comp_mul_const
    conv =>
      lhs
      arg 2
      simp [DFunLike.coe]
      equals (fun x ↦ c • x) ∘ f.toFun => rfl


    refine ⟨comp_mul_const, ?_⟩
    simp [norm]
    left
    simp [K]

--def myInst := Submodule.Quotient.normedAddCommGroup (S := ConstF)

lemma lipschitz_norm_const (z: ℂ): LipschitzSemiNorm (G := G) (ConstLipschitzH z) = 0 := by
  unfold LipschitzSemiNorm
  have zero_mem: 0 ∈ { k: NNReal | LipschitzWith k (ConstLipschitzH (G := G) z).toFun } := by
    simp
    simp [ConstLipschitzH]
    simp [LipschitzWith]
  have my_le := csInf_le (by simp) zero_mem
  exact nonpos_iff_eq_zero.mp my_le


lemma constf_eq_null: (ConstF (G := G) : Set (LipschitzH (G := G))) = nullAddSubgroup (LipschitzH (G := G)) := by
  unfold ConstF
  unfold nullAddSubgroup
  ext f
  simp
  refine ⟨?_, ?_⟩
  .
    intro hf
    obtain ⟨z, hz⟩ := hf
    rw [← hz]
    simp [norm]
    apply lipschitz_norm_const
  .
    intro hf
    simp [norm, LipschitzSemiNorm] at hf
    have lipschitz_zero := lipschitz_attains_norm f (f.lipschitz)
    simp [LipschitzSemiNorm] at lipschitz_zero
    rw [hf] at lipschitz_zero
    simp [LipschitzWith] at lipschitz_zero
    use (f.toFun 1)
    simp [ConstLipschitzH]
    ext a
    simp
    apply lipschitz_zero

instance const_isClosed: IsClosed (ConstF (G := G) : Set (LipschitzH (G := G))) := by
  rw [constf_eq_null]
  exact isClosed_nullAddSubgroup


#synth NormedSpace ℂ (W (S := S))
#synth NormedAddCommGroup (W (S := S))

#synth TopologicalSpace (W (G := G))
-- noncomputable instance W_seminorm: SeminormedAddCommGroup (W (G := G)) where
--   norm := fun f => (LipschitzSemiNorm_w f).val
--   dist_self := by
--     intro w
--     simp [LipschitzSemiNorm_w]
--     rw [← Submodule.Quotient.mk_zero]
--     unfold Submodule.Quotient.mk
--     rw [Quotient.lift_mk]
--     exact lipschiz_norm_zero
--   dist_comm := by
--     intro x w
--     simp
--     dsimp [LipschitzSemiNorm_w]
--     conv =>
--       pattern w - x
--       equals -(x - w) =>
--         field_simp

--     have forward_elem: Submodule.Quotient.mk (x - w).out = x - w := by
--       simp [Submodule.Quotient.mk]
--     rw [← forward_elem]
--     rw [← Submodule.Quotient.mk_neg]


--     unfold Submodule.Quotient.mk
--     repeat rw [Quotient.lift_mk]
--     simp [LipschitzSemiNorm]
--     conv =>
--       rhs
--       arg 1
--       arg 1
--       intro k
--       rw [lipschitz_neg_tofun]
--       rw [lipschitzWith_neg_iff]
--   dist_triangle := by
--     intro x y z
--     simp [LipschitzSemiNorm_w]

--     have forward_elem (w: W (G := G)): Submodule.Quotient.mk (w).out = w := by
--       simp [Submodule.Quotient.mk]
--     rw [← forward_elem (w := (x - z))]
--     rw [← forward_elem (w := (x - y))]
--     rw [← forward_elem (w := (y - z))]
--     unfold Submodule.Quotient.mk
--     rw [Quotient.lift_mk]
--     rw [Quotient.lift_mk]
--     rw [Quotient.lift_mk]

--     have triangle := lipschitz_norm_triangle (Quotient.out (x)).toFun (Quotient.out (y)).toFun (Quotient.out (z)).toFun sorry sorry sorry

--     simp [LipschitzSemiNorm]
--     conv =>
--       pattern x - z
--       equals (x - y) + (y - z) =>
--         field_simp




-- The space 'GL(W)' of invertible continuous linear functions from W to W
abbrev GL_W := (W (G := G) →L[ℂ] W (G := G))ˣ


--#synth NormedSpace ℂ (GL_W (G := G))
--#synth MetricSpace (GL_W (G := G))


#synth FiniteDimensional ℂ (LipschitzH (G := G))
#synth TopologicalSpace (LipschitzH (G := G))

def GRep: Representation ℂ G (LipschitzH (G := G))  := {
  toFun := fun g => {
    toFun := gAct g
    map_add' := by
      intro f h
      ext a
      simp [gAct]
      simp [DFunLike.coe]
    map_smul' := by
      intro c f
      ext a
      simp [gAct]
      simp [DFunLike.coe]
      simp [HSMul.hSMul, SMul.smul]
  }
  map_one' := by
    ext f a
    simp [gAct]
    rfl
  map_mul' := by
    intro g h
    ext f a
    simp [gAct]
    simp [DFunLike.coe]
    simp [mul_assoc]
}

-- We start with a map from G into the space of (not necessarily invertible) linear maps from W to W
def GRepW_non_invertible: Representation ℂ G (W (G := G)) := Representation.quotient (GRep (G := G)) ConstF (by
  intro g
  intro f hf
  simp
  simp [ConstF]
  simp [ConstF] at hf
  obtain ⟨K, hK⟩ := hf
  use K
  ext a
  simp [GRep]
  rw [← hK]
  rw [gAct_const]
)

-- We then build a map from G into the group of invertible linear maps from W to W
noncomputable def GRepW_base := Representation.asGroupHom (G := G) GRepW_non_invertible


-- GRep just translates functions by g⁻¹, so it preserves the Lipschitz operator norm
lemma GRep_preserves_norm (g: G) (f: LipschitzH): ‖(GRep g) f‖ = ‖f‖ := by
  simp [GRep]
  simp [norm]
  nth_rw 1 [LipschitzSemiNorm]
  rw [gAct]
  simp [DFunLike.coe]
  conv =>
    lhs
    arg 1
    arg 1
    intro k
    equals (LipschitzWith k (f.toFun ∘ (fun y => (g⁻¹ * y)))) =>
      rfl

  have comp := LipschitzWith.comp (f := f.toFun) (g := fun y => (g⁻¹ • y)) (Kf := (LipschitzSemiNorm ⇑f)) (Kg := 1) ?_ ?_
  rotate_left 1
  . apply lipschitz_attains_norm
    exact f.lipschitz
  . simp [LipschitzWith]

  have norm_mem: (LipschitzSemiNorm (G := G) f) ∈ { k: NNReal | LipschitzWith k (f.toFun ∘ (fun y => (g⁻¹ * y))) } := by
    simp
    simp at comp
    exact comp


  apply le_antisymm
  .
    apply csInf_le (by
      simp [BddBelow]
      apply Set.nonempty_of_mem (x := 0)
      rw [mem_lowerBounds]
      simp
    ) norm_mem
  .
    apply le_csInf
    .
      apply Set.nonempty_of_mem (x := (LipschitzSemiNorm ⇑f)) norm_mem
    . intro b hb
      simp at hb
      simp [LipschitzSemiNorm]
      apply csInf_le
      .
        simp [BddBelow]
        apply Set.nonempty_of_mem (x := 0)
        rw [mem_lowerBounds]
        simp
      . simp
        simp [LipschitzWith] at hb
        simp [LipschitzWith]
        intro x y
        specialize hb (g * x) (g * y)
        simp at hb
        exact hb




-- Takes in an invertible linear map from W to W, and produces a *continuous* linear map from W to W
noncomputable def GRepW: (W (G := G) →ₗ[ℂ] W (G := G))ˣ →* GL_W (G := G) := {
  toFun := fun f => {
    val := LinearMap.toContinuousLinearMap f.val
    inv := LinearMap.toContinuousLinearMap f.inv
    val_inv := by
      have old_inv := f.val_inv
      ext a
      apply_fun (fun f => f a) at old_inv
      simp
      simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
      apply old_inv
    inv_val := by
      have old_inv := f.inv_val
      ext a
      apply_fun (fun f => f a) at old_inv
      simp
      simp only [Units.inv_eq_val_inv, Module.End.one_apply] at old_inv
      apply old_inv
  }
  map_one' := by
    ext a
    simp
  map_mul' := by
    intro f g
    ext a
    simp
}

-- noncomputable def GRepW_Multiplicative: (W (G := G) →ₗ[ℂ] W (G := G)) →* (Multiplicative (GL_W (G := G))) := {
--   toFun := fun f => Multiplicative.ofAdd (GRepW f)
--   map_one' := by
--     simp
--   map_mul' := by
--     intro f g
--     ext
--     simp [DFunLike.coe]
--     simp [ContinuousLinearMap.toFun_eq_coe]
--     simp [ContinuousLinearMap.mul_apply]
-- }

#synth Group (GL_W (G := G))

lemma quotient_norm_eq_norm (f: LipschitzH (G := G)): ‖(Submodule.Quotient.mk f : W)‖ = ‖f‖ := by
  --dsimp [norm]
  -- conv =>
  --   lhs
  --   arg 2
  --   equals ‖↑ f‖ =>
  --     sorry
  have foo := QuotientAddGroup.norm_mk (S := ConstF.toAddSubgroup) f
  conv =>
    lhs
    equals ‖(QuotientAddGroup.mk f : (LipschitzH ⧸ ConstF.toAddSubgroup))‖ =>
      rfl
  rw [QuotientAddGroup.norm_mk]
  simp [Metric.infDist]
  dsimp [EMetric.infEdist]

  conv =>
    lhs
    arg 1
    arg 1
    intro y
    arg 1
    intro hy
    equals (‖f‖₊ : ENNReal) =>
      simp [ConstF] at hy
      obtain ⟨a, ha⟩ := hy
      simp [edist, PseudoMetricSpace.edist]
      simp [LipschitzSemiNorm]
      simp [LipschitzWith]
      simp_rw [← ha]
      simp [ConstLipschitzH, DFunLike.coe]
      simp_rw [lipschitz_sub_tofun]
      simp
      rfl

  conv =>
    arg 1
    arg 1
    arg 1
    intro y
    arg 1
    intro hy

  rw [biInf_const ?_]
  . simp
  . exact Submodule.nonempty ConstF

-- Define the norm on invertible maps (Units) using the norm on the underlying linear maps
noncomputable instance GL_W_opNorm : Norm (GL_W (G := G)) where
  norm := fun f => ‖f.val‖

-- Unfortunately, we cannot use 'NormedGroup', since we have a multiplicate group,
-- but we want our distance function to be ‖f - g‖, not ‖f * g⁻¹‖
noncomputable instance GL_W_psuedoMetric: PseudoMetricSpace (GL_W (G := G)) where
  dist := fun f g => ‖f.val - g.val‖
  dist_self := by
    simp
  dist_comm := by
    intro x y
    conv =>
      rhs
      arg 1
      equals -(x.val - y.val) =>
        simp
    rw [ContinuousLinearMap.opNorm_neg]
  dist_triangle := by
    intro x y z
    conv =>
      lhs
      arg 1
      equals (x.val - y.val + y.val - z.val) =>
        simp

    have triangle := ContinuousLinearMap.opNorm_add_le (f := x.val - y.val) (g := y.val - z.val)
    field_simp at triangle
    field_simp
    exact triangle

-- noncomputable instance GL_W_NormedGroup : SeminormedGroup (GL_W (G := G)) := {
--   norm := GL_W_opNorm.norm,
--   dist_self := by
--     simp
--     simp [norm]
--     unfold ContinuousLinearMap.opNorm
--     simp

--   dist_comm := by sorry
--   dist_eq := by sorry
-- }

--#synth MetricSpace (LinearMap.GeneralLinearGroup ℝ ℝ)

#synth NormedRing (W (G := G) →L[ℂ] W (G := G))

lemma GLW_preseves_norm (g: G) (w: W (G := G)): ‖(GRepW (G := G) (GRepW_base g)).val w‖ = ‖w‖ := by
  unfold GL_W
  have exists_v: ∃ v, Submodule.Quotient.mk v = w := by
    apply Quotient.exists_rep
  obtain ⟨v, hv⟩ := exists_v
  simp [GRepW, GRepW_base, GRepW_non_invertible]
  nth_rw 1 [← hv]
  rw [Representation.asGroupHom_apply]
  simp
  --rw [Submodule.mapQ_apply]
  rw [quotient_norm_eq_norm]
  rw [GRep_preserves_norm]
  rw [← hv]
  rw [quotient_norm_eq_norm]

-- We want the topology to come from our metric space 'GL_W_psuedoMetric', not from the units
attribute [-instance] Units.instTopologicalSpaceUnits
-- The image of G under our representation: ρ(G) in the Vikman paper
noncomputable def rho_g := ((GRepW (G := G)).restrict ((GRepW_base (G := G)).range)).range

def rho_g_closure := _root_.closure (rho_g (G := G)).carrier

instance GL_W_proper: ProperSpace (GL_W (G := G)) := by
  unfold GL_W
  apply FiniteDimensional.RCLike.properSpace_submodule


--   apply FiniteDimensional.proper_rclike (K := ℂ)

-- In the Vikman paper, rho_g is precompact, and the closure of rho_g is a compact subgroup
theorem compact_rho_g: IsCompact (rho_g_closure (G := G)) := by
  unfold rho_g_closure rho_g
  apply Bornology.IsBounded.isCompact_closure
  rw [Metric.isBounded_iff]
  use 2
  intro p hp q hq
  simp at hp
  simp at hq
  obtain ⟨a, p_eq_a_rep⟩ := hp
  obtain ⟨b, q_eq_b_rep⟩ := hq
  simp [dist]
  rw [ContinuousLinearMap.norm_def]
  apply csInf_le (by
    simp [BddBelow]
    apply Set.nonempty_of_mem (x := 0)
    rw [mem_lowerBounds]
    simp
    intro x hx _
    exact hx
  )
  simp
  intro x
  rw [sub_eq_add_neg]
  have norm_triangle := norm_add_le (p.val x) (- q.val x)
  simp only [norm_neg] at norm_triangle
  rw [← p_eq_a_rep, ← q_eq_b_rep] at norm_triangle
  rw [GLW_preseves_norm] at norm_triangle
  rw [GLW_preseves_norm] at norm_triangle
  rw [two_mul]
  rw [p_eq_a_rep] at norm_triangle
  rw [q_eq_b_rep] at norm_triangle
  exact norm_triangle


-- Section 3.3 in Vikmanm, "Construction of a representation"
-- This is a combination of Cartan's Theorem and Theorem 3.6, giving us the conclusion that
-- ρ(G) contains an abelian subgroup of finite index
lemma rho_g_contains_abelian: ∃ M: Subgroup ((rho_g (G := G))), IsMulCommutative M ∧ M.FiniteIndex := by
  sorry

-- We need this to work with Finset
noncomputable instance GL_W_DecidableEq: DecidableEq (GL_W (G := G)) := by
  apply Classical.typeDecidableEq

noncomputable instance w_map_DecidableEq: DecidableEq (W (G := G) →ₗ[ℂ] W (G := G)) := by
  apply Classical.typeDecidableEq

instance rho_g_FG: Group.FG (rho_g (G := G)) := by
  have fg_grep: Group.FG ↥(GRepW_base (G := G)).range := by
    apply Group.fg_range
  unfold rho_g
  apply Group.fg_range


-- The input data and proofs for Theorem 3.1 in Vikman
structure Theorem3_1_Data where
  -- An abelian subgruop of G, with finite index
  G': Subgroup G
  isMulCommutative: IsMulCommutative G'
  finite_index: G'.FiniteIndex
  -- G' can be mapped homomorphically onto ℤ
  φ: (Additive G) →+ ℤ
  (hφ: Function.Surjective φ)

-- Case 1 in Section 3.3 of Vikman, where the representation ρ(G) is infinite
lemma rho_g_case_infinite (hr: Infinite (↥(rho_g (G := G)))): Nonempty (Theorem3_1_Data (G := G)) := by
  obtain ⟨H, H_abelian, H_finite_index⟩ := rho_g_contains_abelian (G := G)
  -- TODO - generalize this to a lemma: finite-index subgroup of an infinite group is infinite
  -- and upstream to mathlib


  --have h_commgroup: CommGroup H := by
  --  apply CommGroup.ofIsMulCommutative

  have h_fg: Group.FG ↥H := by infer_instance
  --have h_fg_comm: @Group.FG ↥H CommGroup.toGroup := by
  --  dsimp [CommGroup.toGroup]
  --  exact h_fg

  have card_mul := Subgroup.card_mul_index H
  rw [Nat.card_eq_zero_of_infinite (α := rho_g (G := G))] at card_mul
  rw [Nat.mul_eq_zero] at card_mul
  simp [H_finite_index.index_ne_zero] at card_mul
  rw [Nat.card_eq_zero] at card_mul
  simp at card_mul
  obtain h_infinite := card_mul


  -- TODO - figure out how to make instance inference work here
  obtain ⟨i, j, i_fin, j_fin, p, p_prime, e, exists_iso⟩ := @CommGroup.equiv_free_prod_directSum_zmod H (by apply CommGroup.ofIsMulCommutative) (h_fg)
  have iso := Classical.choice exists_iso

  have j_nonempty: Nonempty j := by
    by_contra!
    simp at this
    simp [this] at iso
    have H_finite : Finite H := by
      rw [Equiv.finite_iff iso.toEquiv]
      have finite_i: Finite i := by
        infer_instance
      have finite_mul: ∀ f: i, Finite (Multiplicative (ZMod (p f ^ e f))) := by
        intro f
        simp [Multiplicative]
        have pow_ne_zero: NeZero (p f ^ e f) := by
          exact {
            out := by
              simp
              have first_ne_zero := Nat.Prime.ne_zero (p_prime f)
              simp [first_ne_zero]
          }
        apply Finite.of_fintype
      apply Finite.instProd
    have no_finite := card_mul.not_finite
    contradiction

  -- TODO - can we get the comp '∘' syntax to give us a monoid hom, instead of a plain function?
  let h_to_z := (Pi.evalMonoidHom _ (Classical.choice (by
    exact j_nonempty
  ))).comp ((MonoidHom.fst _ _).comp iso.toMonoidHom)

  have h_to_z_surjective: Function.Surjective h_to_z := by
    unfold h_to_z
    simp
    apply Function.Surjective.comp
    .
      intro x
      simp
      use fun _ => x
    . apply Function.Surjective.comp
      . exact Prod.fst_surjective
      . exact iso.surjective

  let rho_hom := ((GRepW (G := G)).comp ((GRepW_base (G := G))))

  -- Interpret H as a subgroup of GL_W
  let H_as_GL_W := Subgroup.map (Subgroup.subtype (rho_g (S := S))) H
  -- Take the preimage ρ⁻¹(H) := G'
  let G' := Subgroup.comap rho_hom H_as_GL_W


  have G'_index := Subgroup.index_comap H_as_GL_W rho_hom
  simp [relindex] at G'_index

  have subgroupof_equiv := Subgroup.subgroupOfEquivOfLe (H := H_as_GL_W) (K := rho_hom.range) (by
    simp [H_as_GL_W, rho_hom, rho_g]
    intro x hx
    simp
    simp at hx
    obtain ⟨⟨g, x_eq_rep_g⟩, x_mem_H⟩ := hx
    use g
  )

  conv at G'_index =>
    rhs
    equals H_as_GL_W.index =>
      unfold Subgroup.subgroupOf
      sorry



  have H_index_ne_zero := H_finite_index.index_ne_zero

  have G'_finite_index: G'.FiniteIndex := by
    unfold G'
    exact {
      index_ne_zero := by
        rw [G'_index]
        dsimp [H_as_GL_W]
        rw [Subgroup.index_map_subtype]
        simp [H_index_ne_zero]

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
-- and the Vikman paper
def HasPolynomialGrowthD (d: ℕ): Prop := ∃ a: ℕ+, ∀ n ≥ 2, #(S ^ n) ≤ a * n ^ d
def HasPolynomialGrowth: Prop := ∃ d, HasPolynomialGrowthD (S := S) d

-- TODO - upstream to mathlib
lemma s_pow_inv (n: ℕ): (S^n)⁻¹ = (S⁻¹)^n := by
  induction n with
  | zero =>
    simp only [pow_zero, inv_one]
  | succ n ih =>
    simp only [inv_pow]

-- TODO - upstream to mathlib
lemma mem_closure_iff_mem_pow (g: G): g ∈ Subgroup.closure S ↔ ∃ n, g ∈ S^n := by
  refine ⟨?_, ?_⟩
  .
    intro hg
    induction hg using Subgroup.closure_induction with
    | one =>
      use 1
      simp
      exact hGS.one_mem
    | inv a ha a_mem =>
      obtain ⟨n, hn⟩ := a_mem
      use n
      rw [← Finset.mem_inv']
      rw [s_pow_inv]
      rw [← S_eq_Sinv]
      exact hn
    | mem s hs =>
      use 1
      simp
      exact hs
    | mul a b ha hb iha ihb =>
      obtain ⟨p, hp⟩ := iha
      obtain ⟨q, hq⟩ := ihb
      use (p + q)
      rw [pow_add]
      rw [Finset.mem_mul]
      refine ⟨a, hp, b, hq, rfl⟩
  .
    intro _
    apply mem_closure g

lemma poly_growth_implies (d: ℕ) (hd: HasPolynomialGrowthD (S := S) d): HasPolynomialGrowthD (S := S') d := by

  simp [HasPolynomialGrowthD] at hd
  obtain ⟨a, s_poly⟩ := hd
  simp [HasPolynomialGrowthD]
  have b: ℕ+ := 1
  have C: ℕ := 0
  use ⟨#(S ^ C) * ↑a, (by
    simp only [PNat.pos, mul_pos_iff_of_pos_right, Finset.card_pos]
    refine Finset.Nonempty.pow ?_
    exact Finset.nonempty_coe_sort.mp hS
  )⟩
  intro n hn
  --have inject_s_card := Finset.card_le_card_of_injOn (s := S') (t := S ^ C) sorry sorry sorry
  specialize s_poly n hn
  have le_pow := Finset.card_pow_le (s := S') (n := n)

  calc
    #(S' ^ n) ≤ #((S ^ C) * S^n) := sorry
    _ ≤ #((S ^ C)) * #(S ^ n) := by
      exact Finset.card_mul_le
    _ ≤ #((S ^ C)) * (↑a * n ^ d) := by
      exact Nat.mul_le_mul_left (#(S ^ C)) s_poly

    -- _ = #((S ^ n) ^ C) := by
    --   rw [← pow_mul]
    --   rw [mul_comm]
    --   rw [pow_mul]
    -- _ ≤ #(S ^ n)^C := by exact Finset.card_pow_le
    -- _ ≤ (↑a * n ^ d)^C := by
    --   exact Nat.pow_le_pow_left s_poly C

  rw [← mul_assoc]
  simp
  -- calc
  --   #(S' ^ n) ≤ #(S') ^ n := by apply Finset.card_pow_le
  --   _ ≤ #(S ^ C) ^ n := by exact Nat.pow_le_pow_left inject_s_card n
  --   _ ≤ (↑a * C ^ d)^n := by exact Nat.pow_le_pow_left s_poly n


#print axioms poly_growth_implies







lemma S_nonempty: S.Nonempty := by
  exact Finset.nonempty_coe_sort.mp hS

-- TODO - get rid of this, since all groups must be inhabited
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
      .
        rw [← zpow_neg_one]
        rw [← zpow_add]
        simp [hg.symm]
      .
        simp at hl
        intro val hval
        have hl_right := hl.2 val (by simp) (by simp [hval])
        exact hl_right

open Additive


lemma list_filter_one {T: Type*} [DecidableEq T] [Group T] (l: List T): (l.filter (fun s => !decide (s = 1))).prod = l.prod := by
  induction l with
  | nil =>
    simp
  | cons h t ih =>
    simp
    by_cases h_eq_one: h = 1
    .
      simp [h_eq_one]
      exact ih
    .
      rw [List.filter_cons]
      simp [h_eq_one]
      exact ih

def e_i_regular_helper (φ: (Additive G) →+ ℤ) (γ: G) (s: S): G := (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))

def E_helper (φ: (Additive G) →+ ℤ) (γ: G) := {γ, γ⁻¹} ∪ Set.range (ι := S) (e_i_regular_helper φ γ)

lemma take_drop_len {T: Type*} {l: List T} {p: T → Bool}: (l.takeWhile p).length + (l.dropWhile p).length = l.length := by
  suffices h: l.takeWhile p ++ l.dropWhile p = l by
    nth_rw 3 [← h]
    rw [List.length_append]
  exact List.takeWhile_append_dropWhile

def gamma_m_helper (φ: (Additive G) →+ ℤ) (γ: G) (m: ℤ) (s: S): G := γ^m * (e_i_regular_helper φ γ s) * γ^(-m)

lemma gamma_m_eq_mulAt (φ: (Additive G) →+ ℤ) (γ: G) (m: ℤ) (s: S): gamma_m_helper φ γ m s = (MulAut.conj ((γ^m))) (e_i_regular_helper φ γ s) := by
  dsimp [gamma_m_helper]
  simp


-- The set {γ_m_i}_{m ≤ n}
def three_two_S_n (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ): Finset G := Finset.image (Function.uncurry (gamma_m_helper (S := S) φ γ)) ((Finset.Icc (-n : ℤ) n).product S.attach)
--def three_two_S_n (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ): Finset G := (Function.uncurry (gamma_m_helper (S := S) φ γ)) '' ({ m: ℤ | |m| ≤ n} ×ˢ Set.univ)
-- The set of words of at length at most n generated by {γ_m_i}_{m ≤ n}
-- Note - This is based on https://terrytao.wordpress.com/2010/02/18/a-proof-of-gromovs-theorem/, which uses
-- "length at most n"
-- The Vikman paper says "words of length n", which seems incorrect

lemma gamma_helper_subset_S_n (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ): Set.range (gamma_m_helper (S := S) φ γ n) ⊆ three_two_S_n (S := S) φ γ n := by
  intro val hval
  simp [three_two_S_n]
  use n
  refine ⟨by omega, ?_⟩
  simp at hval
  exact hval

instance simple_finite_list (P: Finset G) (n: ℕ): Finite { l: List P | l.length ≤ n } := by
  apply List.finite_length_le

-- List.finite_length_le
-- instance finite_list (P: Finset G) (n: ℕ): Finite { l: List G | l.length ≤ n ∧ ∀ x ∈ l, x ∈ P } := by
--   apply Finite.of_injective (β := { l: List P | l.length ≤ n }) (f := fun l => by (
--     have l_prop := l.property
--     simp only [Set.mem_setOf_eq] at l_prop
--     have mem_prop := l_prop.2
--     exact ⟨l.val.attach.map (fun g => ⟨g.val, mem_prop g.val g.property⟩), by (
--       simp
--       exact l_prop.1
--     )⟩
--   ))
--   simp
--   intro a b
--   induction a.val
--   .
--     simp
--     simp
--   . sorry
--   hint
--   intro hab
--   simp_rw [List.map_eq_iff] at hab
--   ext n g
--   specialize hab n
--   simp at hab
--   simp [Option.map] at hab
--   split at hab
--   .
--     split at hab
--     .
--       rename _ => some_eq
--       simp at some_eq
--       simp at hab
--       sorry
--     . sorry
--   . sorry

--   -- convert (Finset.range n).finite_toSet.biUnion (fun i _ => by (

--   --   sorry
--   -- ))
--   -- . sorry
--   -- . sorry
--   -- . sorry
--   -- . sorry
--   apply @Finite.of_injective _ (β := { l: List P | l.length ≤ n }) (List.finite_length_le _ _) (f := fun l => by (
--     simp at l
--     simp
--     let other: { l: List P // l.length ≤ n} := ⟨l.val.attach.map (fun q => ⟨q.val, ?_⟩), ?_⟩
--     . exact other
--     .
--       have prop := q.property
--       have l_prop := l.property.2
--       exact l_prop q prop
--     . simp
--       exact l.property.1
--   ))
--   simp
--   intro a b hab

--   simp at hab

--   rw [Subtype.eq_iff]
--   rw [List.map_eq_iff] at hab
--   ext n g
--   specialize hab n
--   simp only [List.getElem?_map] at hab

--   rw [List.eq_iff]
--   induction ha: a.val with
--   | nil =>


--       simp [ha]
--   | cons c =>
--     simp_rw [ha] at hab





--   --apply
--   sorry

noncomputable def list_len_n (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ): Finset (List ((three_two_S_n φ γ n (S := S)))) := @Set.toFinset _ { l: List ((three_two_S_n φ γ n (S := S))) | l.length ≤ n } (@Fintype.ofFinite _ _)

noncomputable def three_two_B_n (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ): Finset G := Finset.image (fun l => l.unattach.prod) (list_len_n φ γ n (S := S))

noncomputable def three_two_B_n_single_s (φ: (Additive G) →+ ℤ) (γ: G) (n: ℕ) (s: G): Finset G := Finset.image (fun l => l.unattach.prod) (list_len_n φ γ n (S := {s}))



set_option maxHeartbeats 600000

-- If G has polynomial growth, than we can find an N such that S_n ⊆ B_n * B_n⁻¹
lemma new_three_two_poly_growth (d: ℕ) (hd: d >= 1) (hG: HasPolynomialGrowthD d (S := S)) (γ: G) (φ: (Additive G) →+ ℤ) (hφ: Function.Surjective φ) (hγ: φ γ = 1) (s: G) (s_mem: s ∈ S): ∃ n, three_two_S_n (S := {s}) φ γ (n + 1) ⊆ ((three_two_B_n (S := {s}) φ γ n) * (three_two_B_n (S := {s}) φ γ n)⁻¹)  := by
  by_contra!
  simp [HasPolynomialGrowthD] at hG
  have little_o_poly := isLittleO_pow_exp_pos_mul_atTop d (b := Real.log 2) (Real.log_pos (by simp))
  simp at little_o_poly
  simp_rw [Real.exp_mul] at little_o_poly
  rw [Real.exp_log (by simp)] at little_o_poly
  apply Asymptotics.IsLittleO.eventuallyLE at little_o_poly
  apply Filter.Eventually.natCast_atTop at little_o_poly
  simp at little_o_poly

  -- Find an N' such that N^D < 2^N
  obtain ⟨N', hN⟩ := little_o_poly

  -- Write γ as a product of elements in S
  obtain ⟨gamma_list, gamma_list_prod⟩ := mem_S_prod_list γ
  simp [ProdS] at gamma_list_prod

  have gamma_list_inv: ((gamma_list.unattach).map (fun x => x⁻¹)).reverse.prod = γ⁻¹ := by
    rw [← List.prod_inv_reverse]
    rw [gamma_list_prod]

  have gamma_list_comm_inv: ((gamma_list.unattach).map (fun x => x⁻¹)) = (gamma_list.map (fun s => ⟨s.val⁻¹, hGS.has_inv s.val s.property⟩)).unattach := by
    clear gamma_list_prod gamma_list_inv
    induction gamma_list with
    | nil =>
      simp
    | cons a b ih =>
      simp
      exact ih

  rw [gamma_list_comm_inv] at gamma_list_inv



  -- Choose our N large enough that we can apply all of the above conditions
  let N := max N' (max gamma_list.length (max (φ (ofMul s)).natAbs 2))
  -- specialize hN N (by simp [N])
  -- specialize this N
  -- rw [Finset.not_subset] at this
  -- obtain ⟨p, ⟨p_mem, p_not_prod⟩⟩ := this
  -- rw [Finset.mem_mul.not] at p_not_prod
  -- push_neg at p_not_prod


  have disjoint_smul (M: ℕ) (hM: N ≤ M) (p: G) (p_mem: p ∈ three_two_S_n (S := {s}) φ γ (M + 1)) (p_not_prod: p ∉ three_two_B_n (S := {s}) φ γ M * (three_two_B_n (S := {s}) φ γ M)⁻¹): (p • three_two_B_n (S := {s}) φ γ M) ∩ (three_two_B_n (S := {s}) φ γ M) = ∅ := by
    rw [Finset.mem_mul.not] at p_not_prod
    push_neg at p_not_prod

    ext a
    simp only [Finset.mem_inter, Finset.not_mem_empty, iff_false, not_and]
    intro ha
    simp only [Finset.smul_finset_def, smul_eq_mul, Finset.mem_image] at ha
    obtain ⟨b, b_mem, s_b_eq⟩ := ha
    apply_fun (fun g => g * b⁻¹ ) at s_b_eq
    simp at s_b_eq
    apply Finset.inv_mem_inv at b_mem
    by_contra!
    specialize p_not_prod a this b⁻¹ b_mem
    rw [ne_comm] at p_not_prod
    contradiction


  have s_n_subset: ∀ M, N ≤ M → three_two_S_n (S := {s}) φ γ M ⊆ three_two_S_n (S := {s}) φ γ (M + 1) := by
    intro m hM a ha
    simp [three_two_S_n] at ha
    simp [three_two_S_n]
    obtain ⟨n, hn, s_n_eq⟩ := ha
    use n
    refine ⟨by omega, s_n_eq⟩

  have s_n_subset_all (x y: ℕ) (hxy: x ≤ y): three_two_S_n (S := {s}) φ γ x ⊆ three_two_S_n (S := {s}) φ γ (y) := by
    intro a ha
    simp [three_two_S_n] at ha
    simp [three_two_S_n]
    obtain ⟨n, hn, s_n_eq⟩ := ha
    use n
    refine ⟨by omega, s_n_eq⟩


  have b_n_subset_b_n_succ: ∀ M, N ≤ M → three_two_B_n (S := {s}) φ γ M ⊆ three_two_B_n (S := {s}) φ γ (M + 1) := by
    intro M hM a ha
    simp [three_two_B_n] at ha
    simp [three_two_B_n]
    obtain ⟨l, l_len, l_prod⟩ := ha
    simp [list_len_n]
    use l.map (fun s => ⟨s.val, by (
      exact s_n_subset M hM s.property
    )⟩)
    simp
    simp [list_len_n] at l_len
    refine ⟨by omega, ?_⟩
    conv =>
      lhs
      arg 1
      equals l.unattach =>
        simp [List.unattach, -List.map_subtype]
    exact l_prod

  have smul_subset (M: ℕ) (hM: N ≤ M) (p: G) (p_mem: p ∈ three_two_S_n (S := {s}) φ γ (M + 1)): p • three_two_B_n (S := {s}) φ γ M ⊆ three_two_B_n (S := {s}) φ γ (M + 1) := by
    intro a ha
    simp [three_two_B_n] at ha
    simp [three_two_B_n]
    simp only [Finset.smul_finset_def, smul_eq_mul, Finset.mem_image] at ha
    obtain ⟨list_prod, ⟨list, list_mem, list_prod_eq⟩, p_mul_eq⟩ := ha
    --have new_p_mem := (s_n_subset_all (N + 1) (M + 1) (by omega)) p_mem
    --have p_mem_M := s_n_subset M hM p_mem
    use (⟨p, p_mem⟩ :: (list.map (fun s => ⟨s.val, by (
      exact s_n_subset M hM s.property
    )⟩)))
    refine ⟨?_, ?_⟩
    .
      simp [list_len_n, list_mem]
      simp [list_len_n] at list_mem
      exact list_mem

    .
      simp
      conv =>
        lhs
        arg 2
        arg 1
        equals list.unattach =>
          simp [List.unattach, -List.map_subtype]
      rw [list_prod_eq, p_mul_eq]


  have s_n_bound: ∀ M: ℕ, N ≤ M → ∀ a ∈ three_two_S_n (S := {s}) φ γ M, ∃ l: List S, l.unattach.prod = a ∧ l.length ≤ 4*M^2 := by
    intro M hM a ha
    simp [three_two_S_n, gamma_m_helper, e_i_regular_helper] at ha
    obtain ⟨m, m_bound, s_m_eq⟩ := ha
    let gamma_inv_list: List S := (gamma_list.map (fun s => ⟨s.val⁻¹, hGS.has_inv s.val s.property⟩)).reverse

    -- Depending on whether these values are positive or negative, we either need to repeat γ or γ⁻¹ in the first list
    let m_list_choice := if 0 < m then gamma_list else gamma_inv_list
    let phi_list_choice := if 0 < (-φ (ofMul s)) then gamma_list else gamma_inv_list

    let m_list_choice_inv := if 0 < m then gamma_inv_list else gamma_list

      --
    --have phi_natabs: (φ (ofMul s)).natAbs = -φ (ofMul s) := by omega
    use (List.replicate m.natAbs m_list_choice).flatten ++ [⟨s, s_mem⟩] ++ (List.replicate (-(φ (ofMul s))).natAbs phi_list_choice).flatten ++ (List.replicate m.natAbs m_list_choice_inv).flatten
    refine ⟨?_, ?_⟩
    .
      simp [phi_list_choice]
      --rw [gamma_list_prod]
      norm_cast
      rw [← s_m_eq]
      rw [← zpow_natCast]
      conv =>
        rhs
        arg 1
        arg 2
        -- TODO - is there a tactic that can normalize the 'ofMul' stuff for us?
        equals s * γ^(-(φ (ofMul s))) =>
          rw [← ofMul_zpow]
          rw [← sub_eq_add_neg]
          rw [← ofMul_div]
          rw [div_eq_mul_inv]
          rw [← inv_zpow]
          rw [inv_zpow']
          rfl


      --rw [← zpow_natCast, phi_natabs]
      simp
      simp_rw [m_list_choice, m_list_choice_inv]
      by_cases m_pos: 0 < m
      .
        simp_rw [m_pos]
        simp
        have m_eq_abs : |m| = m := by
          rw [Int.abs_eq_natAbs]
          omega
        rw [← zpow_natCast]
        simp [gamma_inv_list]
        rw [gamma_list_inv]
        rw [gamma_list_prod]
        rw [m_eq_abs]
        group
        by_cases phi_neg: (φ (ofMul s)) < 0
        .
          have phi_abs: |(φ (ofMul s))| = -φ (ofMul s) := by
            rw [Int.abs_eq_natAbs]
            omega
          rw [phi_abs]
          simp_rw [phi_neg]
          simp
          rw [gamma_list_prod]
          rw [m_eq_abs]
          group
        .
          have phi_abs: |(φ (ofMul s))| = φ (ofMul s) := by
            rw [Int.abs_eq_natAbs]
            omega
          rw [phi_abs]
          simp_rw [phi_neg]
          simp
          rw [gamma_list_inv]
          rw [m_eq_abs]
          group
      .
        simp_rw [m_pos]
        simp
        have neg_abs_m : |m| = - m := by
          rw [Int.abs_eq_natAbs]
          omega
        rw [← zpow_natCast]
        simp [gamma_inv_list]
        rw [gamma_list_inv]
        rw [gamma_list_prod]
        group
        rw [neg_abs_m]
        group
        -- TODO - this can be deduplicated
        by_cases phi_neg: (φ (ofMul s)) < 0
        .
          have phi_abs: |(φ (ofMul s))| = -φ (ofMul s) := by
            rw [Int.abs_eq_natAbs]
            omega
          rw [phi_abs]
          simp_rw [phi_neg]
          simp
          rw [gamma_list_prod]
          rw [neg_abs_m]
          group
        .
          have phi_abs: |(φ (ofMul s))| = φ (ofMul s) := by
            rw [Int.abs_eq_natAbs]
            omega
          rw [phi_abs]
          simp_rw [phi_neg]
          simp
          rw [gamma_list_inv]
          rw [neg_abs_m]
          group
    .

      simp [m_list_choice, m_list_choice_inv]
      simp_rw [apply_ite]
      have m_natabs_le: m.natAbs ≤ M := by omega
      have gamma_list_len_le: gamma_list.length ≤ N := by omega
      have inv_list_len_eq: gamma_inv_list.length = gamma_list.length := by
        simp [gamma_inv_list]
      simp [inv_list_len_eq]
      have n_squared_pos: 1 ≤ N * N := by
        simp [N]
      have m_squared_pos: 1 ≤ M * M := by
        nlinarith
      have phi_choice_len: phi_list_choice.length = gamma_list.length := by
        simp [phi_list_choice]
        simp_rw [apply_ite]
        simp [inv_list_len_eq]
      rw [phi_choice_len]
      have phi_s_le_: (φ (ofMul s)).natAbs ≤ M := by omega
      calc
        _ ≤ M * M + ((φ (ofMul s)).natAbs * gamma_list.length + M * M + 1) := by
          nlinarith
        _ ≤ 2 * M * M + ((φ (ofMul s)).natAbs * gamma_list.length) + 1 := by
          nlinarith
        -- Extremely crude upper bound, but we only need to show a polynomial bound,
        -- so it's fine to use '1 <= N * N'
        _ ≤ 2 * M * M + ((φ (ofMul s)).natAbs * gamma_list.length) + M*M := by
          nlinarith
        _ ≤ 3 * M * M + ((φ (ofMul s)).natAbs * gamma_list.length) := by
          nlinarith
        _ ≤ 3 * M * M + (M * gamma_list.length) := by
          nlinarith
        _ ≤ 3 * M * M + (M * M) := by
          nlinarith
        _ = 4 * M * M := by
          nlinarith
        _ = 4 * M^2 := by nlinarith


  have b_n_subset_s_n_squared: ∀ M, N ≤ M → three_two_B_n (S := {s}) φ γ M ⊆ S ^ (M * (4 * M^2)) := by
    intro M hM a ha
    have orig_ha := ha
    rw [Finset.mem_pow]
    simp [three_two_B_n] at ha
    obtain ⟨l, l_len, l_prod⟩ := ha
    let nested_list := l.map (fun s => ((s_n_bound M hM s.val s.property).choose))
    have flat_list_prod: nested_list.flatten.unattach.prod = a := by
      simp [nested_list]
      rw [← l_prod]
      conv =>
        lhs
        arg 1
        equals l.unattach =>
          clear l_len l_prod nested_list
          induction l with
          | nil =>
            simp
          | cons h t ih =>
            simp
            rw [ih]
            simp [List.unattach, -List.map_subtype]
            simp at ih
            have my_spec := Exists.choose_spec ((s_n_bound M hM h h.property))
            have first_prop := my_spec.1
            -- wtf
            nth_rw 8 [← first_prop]
            simp



    have flat_list_len: nested_list.flatten.length ≤ nested_list.length • (4 * M^2) := by
      simp
      have foo := List.sum_le_card_nsmul (l := (List.map List.length nested_list)) (4 * M^2) ?_
      --simp only [List.length_map, smul_eq_mul, nested_list] at foo
      .
        conv at foo =>
          rhs
          simp
        exact foo
      .
        intro q hq
        simp at hq
        obtain ⟨s_list, h_s_prod, s_len⟩ := hq
        simp [nested_list] at h_s_prod
        obtain ⟨gamma_n, gamma_n_mem, gamma_n_mem_l, s_prod_eq⟩ := h_s_prod
        have s_prod_prop: s_list.unattach.prod = gamma_n ∧ s_list.length ≤ 4*M^2 := by
          have my_spec := Exists.choose_spec ((s_n_bound M hM gamma_n gamma_n_mem))
          rw [s_prod_eq] at my_spec
          exact my_spec
        rw [← s_len]
        exact s_prod_prop.2

    have nested_len_eq: nested_list.length = l.length := by
      simp [nested_list]

    rw [nested_len_eq] at flat_list_len
    simp [list_len_n] at l_len
    simp only [smul_eq_mul] at flat_list_len
    have nested_list_le_n_squared: nested_list.flatten.length ≤ M * (4 * M^2) := by
      apply le_mul_of_le_mul_right (b := l.length)
      . omega
      . omega


    let filled_list := nested_list.flatten ++ (List.replicate ((M * (4 * M^2)) - nested_list.flatten.length) ⟨1, hGS.one_mem⟩)

    have filled_list_prod: filled_list.unattach.prod = nested_list.flatten.unattach.prod := by
      simp [filled_list]


    have len_eq: filled_list.length = M * (4 * M^2) := by
      simp [filled_list]
      apply Nat.add_sub_of_le
      simp at nested_list_le_n_squared
      exact nested_list_le_n_squared

    rw [← len_eq]
    use filled_list.get
    conv =>
      lhs
      equals (List.ofFn (filled_list.get)).unattach.prod =>
        simp

    simp
    rw [filled_list_prod]
    exact flat_list_prod

  conv at b_n_subset_s_n_squared =>
    intro M hM
    rhs
    rhs
    equals 4 * M^3 => ring


  -- #(B_n) grows exponentially, at least from N onword
  have b_n_card_exp: ∀ M: ℕ, N ≤ M → 2^(M - N) ≤ #(three_two_B_n (S := {s}) φ γ M) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
      simp [three_two_B_n, list_len_n]
      use [⟨(gamma_m_helper φ γ 0 ⟨s, s_mem⟩), ?_⟩]
      . simp [N]
      .
        simp [three_two_S_n]
        use 0
        refine ⟨by omega, ?_⟩
        simp [gamma_m_helper, e_i_regular_helper]

    | succ k hk ih =>
      rw [← tsub_add_eq_add_tsub hk]
      rw [pow_succ]

      --specialize hN N (by simp [N])
      specialize this k
      rw [Finset.not_subset] at this
      obtain ⟨p, ⟨p_mem, p_not_prod⟩⟩ := this
      --rw [Finset.mem_mul.not] at p_not_prod
      --push_neg at p_not_prod

      have union_subset_n_succ: three_two_B_n (S := {s}) φ γ k ∪ (p • three_two_B_n (S := {s}) φ γ k) ⊆ three_two_B_n (S := {s}) φ γ (k + 1) := by
        apply Finset.union_subset
        . exact b_n_subset_b_n_succ k hk
        . exact smul_subset k hk p p_mem


      have card_le := Finset.card_le_card (union_subset_n_succ)
      rw [Finset.card_union_of_disjoint ?_] at card_le
      .
        simp at card_le
        ring_nf at card_le
        rw [add_comm] at card_le
        omega
        --have b_n_subset_n := Finset.card_le_card (b_n_subset_s_n_squared N (by simp))
        --have b_n_succ_subset := Finset.card_le_card (b_n_subset_s_n_squared (N + 1) (by simp))
        --simp at b_n_succ_subset
      .
        specialize disjoint_smul  k hk p p_mem p_not_prod
        rw [Finset.inter_comm] at disjoint_smul
        rw [Finset.disjoint_iff_inter_eq_empty]
        exact disjoint_smul


  have little_o_poly := isLittleO_pow_exp_pos_mul_atTop (3 * d) (b := (Real.log 2)) (by
    --simp
    apply Real.log_pos
    simp
  )
  simp at little_o_poly
  simp_rw [Real.exp_mul] at little_o_poly
  rw [Real.exp_log (by simp)] at little_o_poly


  obtain ⟨a, hG⟩ := hG

  have mul_four := Asymptotics.IsLittleO.const_mul_left little_o_poly (a * 4^d)
  rw [← Asymptotics.isLittleO_const_mul_right_iff (c := 2^(-N : ℤ)) (hc := (by simp))] at mul_four
  --have mul_four := little_o_poly


  --rw [Asymptotics.IsLittleO.tendsto_zero_of_tendsto] at little_o_poly
  apply Asymptotics.IsLittleO.def (c := (1 : ℝ)  / 2) (hc := by simp) at mul_four
  apply Filter.Eventually.natCast_atTop at mul_four
  simp at mul_four
  obtain ⟨M', hM⟩ := mul_four
  let M: ℕ := max N M'





  have m_le_n: N ≤ M := by omega


  specialize b_n_card_exp M m_le_n
  specialize b_n_subset_s_n_squared
  have b_n_subset_n := Finset.card_le_card (b_n_subset_s_n_squared M (m_le_n))

  have m_ge_one: 1 ≤ M := by
    omega

  have m_cubed: 1 ≤ M^3 := by
    apply Nat.one_le_pow
    omega


  have other_poly := hG (4 * M ^ 3) (by
    omega
  )

  have m_pow_lt := hM (M) (by omega)
  rw [pow_mul] at m_pow_lt

  -- apply_fun (fun (g: ℝ) => 2 * g) at m_pow_lt
  -- .
  --   simp at m_pow_lt

  -- .
  --   apply Monotone.const_mul
  --   exact fun ⦃a b⦄ a ↦ a
  --   simp


  have helper_lemma (a b c : ℝ) (ha: 0 < a) (hb: 0 < b) (hc: 0 < c) (habc: a ≤ b * c) (hb: b < 1): a < c := by
    nlinarith

  have strict_lt: a * 4 ^ d * (↑M ^ 3) ^ d < (((2 : ℝ) ^ N)⁻¹ * 2 ^ M) := by
    apply helper_lemma (b := 2⁻¹)
    .
      field_simp
    . simp
    . simp
    . exact m_pow_lt
    . field_simp


    -- apply lt_or_eq_of_le at m_pow_lt
    -- match m_pow_lt with
    -- | .inl strict =>
    --   omega
    -- | .inr eq =>
    --   rw [eq]
    --   rw [mul_comm]l
    --   apply mul_lt_of_lt_one_right'
    --   apply lt_mul_of_one_lt_right'
    --   apply mul_lt_of_lt_of_le_one


  conv at strict_lt =>
    rhs
    equals 2^(M - N) =>
      have m_minu_n_pos: N ≤ M := by omega
      field_simp
      rw [← pow_add]
      simp
      omega


  norm_cast at strict_lt
  rw [mul_assoc, ← mul_pow] at strict_lt

  have eventually_lt_double: a * (4 * M ^ 3) ^ d < 2 ^ (M - N) := by
    exact strict_lt

  omega



lemma closure_iterate_mulact {T: Type*} [Group T] [DecidableEq T] (a b: T) (n: ℤ)
  (conj_in: (a^n * b * a^(-n)) ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs))))
  (conj_inv_in: (a^(-n) * b * a^(n)) ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs)))) :
 (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )) = (Subgroup.closure (G := T) (Set.range (fun (m : ℤ) => a^m * b * a^(-m)))) := by
  ext x
  refine ⟨?_, ?_⟩
  .
    intro hx
    apply Subgroup.closure_mono (h := (fun (m: ℤ) ↦ a ^ m * b * a ^ (-m)) '' Set.Ioo (-n.natAbs) n.natAbs)
    .
      intro y hy
      simp at hy
      simp
      obtain ⟨m, hm, y_eq⟩ := hy
      use m
    . exact hx
  .
    intro hx
    have closed_under_conj: ∀ y ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )), a * y * a⁻¹ ∈  (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        simp at hz
        obtain ⟨m, hm, z_eq⟩ := hz
        rw [← z_eq]
        by_cases m_lt_n_sub: m < (n.natAbs : ℤ) - 1
        . apply Subgroup.subset_closure
          simp
          use (m + 1)
          refine ⟨?_, ?_⟩
          .
            refine ⟨?_, ?_⟩
            . omega
            .
              apply_fun (fun (z: ℤ) => z + 1) at m_lt_n_sub
              .
                simp at m_lt_n_sub
                exact m_lt_n_sub
              . exact add_right_strictMono
          .
            rw [← mul_self_zpow]
            simp
            repeat rw [← mul_assoc]
        .
          have n_minus_eq: n - 1 + 1 = n := by
            omega
          simp at m_lt_n_sub
          have m_eq_n_minus: m = (|n|) - 1 := by
            omega
          -- TODO - there must be an easier way to do this
          rw [m_eq_n_minus]
          repeat rw [← mul_assoc]
          rw [mul_self_zpow]
          simp
          rw [← zpow_neg]
          rw [← inv_zpow']
          rw [mul_assoc]
          rw [← zpow_add_one]
          simp
          simp at conj_in
          by_cases n_pos: 0 < n
          .
            have n_eq_abs: n = |n| := by
              exact Eq.symm (abs_of_pos n_pos)
            nth_rw 3 [← n_eq_abs]
            nth_rw 3 [← n_eq_abs]
            exact conj_in
          .
            have n_eq_neg_abs: |n| = -n := by
              apply abs_of_nonpos
              omega
            simp at n_pos
            nth_rw 3 [n_eq_neg_abs]
            nth_rw 3 [n_eq_neg_abs]
            simp
            simp at conj_inv_in
            exact conj_inv_in
      | one =>
        simp
        apply Subgroup.one_mem
      | mul y z hy hz y_mem z_mem =>
        have mul_mem := Subgroup.mul_mem _ y_mem z_mem
        simp at mul_mem
        simp
        exact mul_mem
      | inv y hy y_mem =>
        rw [← Subgroup.inv_mem_iff]
        simp
        rw [← mul_assoc]
        simp at y_mem
        exact y_mem

    -- TODO - deduplicate this
    have closed_under_conj_inv: ∀ y ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )), a⁻¹ * y * a ∈  (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        simp at hz
        obtain ⟨m, hm, z_eq⟩ := hz
        rw [← z_eq]
        by_cases m_lt_n_sub: (-n.natAbs : ℤ) < m - 1
        . apply Subgroup.subset_closure
          simp
          use (m - 1)
          refine ⟨?_, ?_⟩
          .
            refine ⟨?_, ?_⟩
            .
              simp at m_lt_n_sub
              have ⟨m_gt, other⟩ := hm
              omega

            .
              apply_fun (fun (z: ℤ) => z - 1) at m_lt_n_sub
              .
                simp at m_lt_n_sub
                omega
              . exact add_right_strictMono
          .
            repeat rw [← mul_assoc]
            nth_rw 2 [← zpow_neg_one]
            rw [← zpow_add]
            rw [add_comm, ← sub_eq_add_neg]
            conv =>
              rhs
              rw [mul_assoc]
              rhs
              rw [← inv_zpow]
              rw [inv_zpow']
              rw [mul_zpow_self]
              rw [add_comm]
            simp
            rw [← inv_zpow]
            simp
            rw [sub_eq_add_neg]

        .
          have n_minus_eq: n - 1 + 1 = n := by
            omega
          simp at m_lt_n_sub
          have m_eq_n_minus: m = (-|n|) + 1 := by
            omega
          -- TODO - there must be an easier way to do this
          rw [m_eq_n_minus]
          repeat rw [← mul_assoc]
          rw [← mul_self_zpow]
          simp
          rw [← zpow_neg]
          rw [← zpow_neg_one]
          rw [mul_assoc]
          rw [mul_assoc]
          rw [mul_assoc]
          simp
          repeat rw [← mul_assoc]
          simp at conj_inv_in
          by_cases n_pos: 0 < n
          .
            have n_eq_abs: n = |n| := by
              exact Eq.symm (abs_of_pos n_pos)
            nth_rw 3 [← n_eq_abs]
            nth_rw 3 [← n_eq_abs]
            exact conj_inv_in
          .
            have n_eq_neg_abs: |n| = -n := by
              apply abs_of_nonpos
              omega
            simp at n_pos
            nth_rw 3 [n_eq_neg_abs]
            nth_rw 3 [n_eq_neg_abs]
            simp
            simp at conj_in
            exact conj_in
      | one =>
        simp
        apply Subgroup.one_mem
      | mul y z hy hz y_mem z_mem =>
        have mul_mem := Subgroup.mul_mem _ y_mem z_mem
        repeat rw [← mul_assoc] at mul_mem
        simp at mul_mem
        simp
        repeat rw [← mul_assoc]
        exact mul_mem
      | inv y hy y_mem =>
        rw [← Subgroup.inv_mem_iff]
        simp
        rw [← mul_assoc]
        simp at y_mem
        exact y_mem



    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp at hy
      obtain ⟨m, hm, y_eq⟩ := hy
      by_cases m_in_range: m ∈ Set.Ioo (-n.natAbs : ℤ) n.natAbs
      .
        apply Subgroup.subset_closure
        simp
        use m
        simp at m_in_range
        refine ⟨by omega, by simp⟩
      .
        simp only [Set.mem_Ioo] at m_in_range
        rw [not_and_or] at m_in_range
        simp at m_in_range
        by_cases m_pos: 0 < m
        .
          -- TODO - why is this needed?
          have exists_nat_abs: ∃ m_abs: ℕ, m = m_abs := by
            use m.natAbs
            omega
          obtain ⟨m_abs, m_eq_abs⟩ := exists_nat_abs
          have abs_n_le: |n| ≤ m_abs := by
            by_contra!
            rw [← m_eq_abs] at this
            omega
          have nat_abs_n_le: n.natAbs ≤ m_abs := by
            rw [Int.abs_eq_natAbs] at abs_n_le
            omega
          rw [m_eq_abs]
          clear m_eq_abs
          clear abs_n_le
          induction m_abs, nat_abs_n_le using Nat.le_induction with
          | base =>
            simp at conj_in
            simp
            by_cases n_pos: 0 < n
            .
              have n_eq_abs: n = |n| := by
                exact Eq.symm (abs_of_pos n_pos)
              nth_rw 3 [← n_eq_abs]
              nth_rw 3 [← n_eq_abs]
              exact conj_in
            .
              have n_eq_neg_abs: |n| = -n := by
                apply abs_of_nonpos
                omega
              simp at conj_inv_in
              rw [n_eq_neg_abs] at conj_inv_in
              simp at conj_inv_in
              rw [n_eq_neg_abs]
              simp
              exact conj_inv_in
          | succ p hsucc ih =>
            specialize closed_under_conj _ ih
            norm_cast
            rw [pow_succ']
            repeat rw [← mul_assoc] at closed_under_conj
            simp at closed_under_conj
            simp
            repeat rw [← mul_assoc]
            exact closed_under_conj

        .
          -- TODO - why is this needed?
          have exists_nat_abs: ∃ m_abs: ℕ, m = -m_abs := by
            use m.natAbs
            omega
          obtain ⟨m_abs, m_eq_abs⟩ := exists_nat_abs
          have abs_n_le: |n| ≤ m_abs := by
            by_contra!
            omega
          have nat_abs_n_le: n.natAbs ≤ m_abs := by
            rw [Int.abs_eq_natAbs] at abs_n_le
            omega
          rw [m_eq_abs]
          clear m_eq_abs
          clear abs_n_le
          induction m_abs, nat_abs_n_le using Nat.le_induction with
          | base =>
            simp at conj_in
            simp
            by_cases n_pos: 0 < n
            .
              have n_eq_abs: n = |n| := by
                exact Eq.symm (abs_of_pos n_pos)
              nth_rw 3 [← n_eq_abs]
              nth_rw 3 [← n_eq_abs]
              simp at conj_inv_in
              exact conj_inv_in
            .
              have n_eq_neg_abs: |n| = -n := by
                apply abs_of_nonpos
                omega
              rw [n_eq_neg_abs] at conj_in
              simp at conj_in
              rw [n_eq_neg_abs]
              simp
              exact conj_in
          | succ p hsucc ih =>
            --rw [← Subgroup.inv_mem_iff]
            --simp
            specialize closed_under_conj_inv _ ih
            simp at ih
            norm_cast
            rw [zpow_negSucc]
            rw [pow_succ]
            --rw [zpow_add]
            repeat rw [← mul_assoc] at closed_under_conj_inv
            simp at closed_under_conj_inv
            simp
            repeat rw [← mul_assoc]
            exact closed_under_conj_inv


    | one => apply Subgroup.one_mem
    | mul y z hy hz y_mem z_mem =>
      apply Subgroup.mul_mem
      . exact y_mem
      . exact z_mem
    | inv y hy y_mem =>
      apply Subgroup.inv_mem _ y_mem

#print axioms closure_iterate_mulact

--- Consequence of `three_two_poly_growth` - the set of all 'γ^n *e_i γ^(-n)' is contained the closure of S_n
lemma three_poly_poly_growth_all_s_n (d: ℕ) (hd: d >= 1) (hG: HasPolynomialGrowthD d (S := S)) (γ: G) (φ: (Additive G) →+ ℤ) (hφ: Function.Surjective φ) (hγ: φ γ = 1)
  : ∃ n, ∀ m, (Finset.image (gamma_m_helper (S := S) (G := G) φ γ m) Finset.univ).toSet ⊆ Subgroup.closure (three_two_S_n (G := G) (S := S) φ γ (n)).toSet := by
  let r: ℕ := Finset.max' (Finset.image (fun s => (by
    exact sInf { n: ℕ | three_two_S_n (S := {s}) φ γ (n + 1) ⊆ ((three_two_B_n (S := {s}) φ γ n) * (three_two_B_n (S := {s}) φ γ n)⁻¹) }
    --exact {Classical.choose (new_three_two_poly_growth (G := G) (S := S) d hd hG γ φ hφ hγ s)}
  )) S) (by
    simp
    exact S_nonempty
  )
  use r
  intro m
  intro x hx
  simp [gamma_m_helper] at hx
  simp [three_two_S_n, gamma_m_helper]
  obtain ⟨s, hs, x_eq_conj⟩ := hx

  let all_n_vals := { n : ℕ | three_two_S_n (S := {s}) φ γ (n + 1) ⊆ ((three_two_B_n (S := {s}) φ γ n) * (three_two_B_n (S := {s}) φ γ n)⁻¹)}
  let n := sInf all_n_vals
  have set_nonempty: all_n_vals.Nonempty := by
    exact new_three_two_poly_growth (G := G) (S := S) d hd hG γ φ hφ hγ s hs
  have temp_s_n_subset := Nat.sInf_mem set_nonempty
  have s_n_subset: n ∈ all_n_vals := by
    exact temp_s_n_subset
  simp [all_n_vals] at s_n_subset
  --obtain ⟨n, s_n_subset⟩ := new_three_two_poly_growth (G := G) (S := S) d hd hG γ φ hφ hγ s
  have n_le_r: n ≤ r := by
    simp [r]
    apply Finset.le_max'
    simp
    use s


  have my_iter := closure_iterate_mulact γ (e_i_regular_helper φ γ ⟨s, hs⟩) (n + 1)
  simp [three_two_S_n, gamma_m_helper] at s_n_subset
  have closure_eq := my_iter ?_ ?_
  .
    have x_mem_closure_range: x ∈ Subgroup.closure (Set.range fun (m : ℤ) ↦ γ ^ m * e_i_regular_helper φ γ ⟨s, hs⟩ * γ ^ (-m : ℤ)) := by
      by_cases m_pos: 0 < m
      .
        have m_eq_natabs: m = m.natAbs := by
          omega
        apply Subgroup.subset_closure
        simp
        use m.natAbs
        rw [m_eq_natabs] at x_eq_conj
        rw [← x_eq_conj]
      .
        --rw [← Subgroup.closure_inv]
        --rw [← Subgroup.inv_mem_iff]
        have m_eq_neg_natabs: m = -m.natAbs := by
          omega
        apply Subgroup.subset_closure
        simp
        --simp only [zpow_neg, zpow_natCast, Set.mem_range]
        use m

    rw [← closure_eq] at x_mem_closure_range
    apply Subgroup.closure_mono (h := ((fun (m : ℤ) ↦ γ ^ m * e_i_regular_helper φ γ ⟨s, hs⟩ * γ ^ (-m : ℤ)) '' (Set.Ioo (-(r + 1) : ℤ) (r + 1 : ℤ))))
    .
      intro p hp
      simp at hp
      simp
      obtain ⟨q, hp, p_eq⟩ := hp
      use q
      refine ⟨by omega, ?_⟩
      use s
      use hs
    .
      apply (Subgroup.closure_mono _) x_mem_closure_range
      intro z hz
      simp at hz
      simp
      obtain ⟨a, ⟨a_gt, a_lt⟩, z_eq⟩ := hz
      use a
      refine ⟨⟨?_, ?_⟩, z_eq⟩
      .
        --have neg_n_gt_r: (-r : ℤ) ≤ (-n : ℤ) := by omega
        norm_cast at a_gt
        omega
      .
        norm_cast at a_lt
        omega
  .
    specialize s_n_subset (n + 1) (by omega) (by omega) s rfl
    simp [three_two_B_n] at s_n_subset
    rw [Finset.mem_mul] at s_n_subset
    obtain ⟨val, val_in_image, other_val, ⟨other_val_in_image, prod_vals_eq⟩⟩ := s_n_subset
    rw [← zpow_neg] at prod_vals_eq
    -- todo - avoid needing to do these simps
    simp [e_i_regular_helper] at prod_vals_eq
    simp [e_i_regular_helper]
    rw [← prod_vals_eq]
    apply Subgroup.mul_mem
    .
      simp at val_in_image
      obtain ⟨list, hlist, list_prod_eq⟩ := val_in_image
      rw [← list_prod_eq]
      apply Subgroup.list_prod_mem
      intro z hz
      simp [list_len_n] at hlist
      simp at hz
      obtain ⟨z_in_s_n, z_in_list⟩ := hz
      simp [three_two_S_n] at z_in_s_n
      apply Subgroup.subset_closure
      simp
      obtain ⟨p, p_in_range, e_i_eq⟩ := z_in_s_n
      use p
      norm_cast
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp [gamma_m_helper] at e_i_eq
      obtain ⟨q, q_mem, e_i_eq'⟩ := e_i_eq
      simp [e_i_regular_helper]
    .
      simp at other_val_in_image
      obtain ⟨list, hlist, list_prod_eq⟩ := other_val_in_image
      apply_fun Inv.inv at list_prod_eq
      simp at list_prod_eq
      rw [← list_prod_eq]
      apply Subgroup.inv_mem
      apply Subgroup.list_prod_mem
      intro z hz
      simp [list_len_n] at hlist
      simp at hz
      obtain ⟨z_in_s_n, z_in_list⟩ := hz
      simp [three_two_S_n] at z_in_s_n
      apply Subgroup.subset_closure
      simp
      obtain ⟨p, p_in_range, e_i_eq⟩ := z_in_s_n
      use p
      norm_cast
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp [gamma_m_helper] at e_i_eq
      obtain ⟨q, q_mem, e_i_eq'⟩ := e_i_eq
      simp [e_i_regular_helper]
  .
    -- TODO - 99% of this can be deduplicated
    specialize s_n_subset (-(n + 1)) (by omega) (by omega) s rfl
    -- Deduplicate verything after here
    simp [three_two_B_n] at s_n_subset

    rw [Finset.mem_mul] at s_n_subset
    obtain ⟨val, val_in_image, other_val, ⟨other_val_in_image, prod_vals_eq⟩⟩ := s_n_subset
    rw [← zpow_neg] at prod_vals_eq
    -- todo - avoid needing to do these simps
    simp [e_i_regular_helper] at prod_vals_eq
    simp [e_i_regular_helper]
    rw [← prod_vals_eq]
    apply Subgroup.mul_mem
    .
      simp at val_in_image
      obtain ⟨list, hlist, list_prod_eq⟩ := val_in_image
      rw [← list_prod_eq]
      apply Subgroup.list_prod_mem
      intro z hz
      simp [list_len_n] at hlist
      simp at hz
      obtain ⟨z_in_s_n, z_in_list⟩ := hz
      simp [three_two_S_n] at z_in_s_n
      apply Subgroup.subset_closure
      simp
      obtain ⟨p, p_in_range, e_i_eq⟩ := z_in_s_n
      use p
      norm_cast
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp [gamma_m_helper] at e_i_eq
      obtain ⟨q, q_mem, e_i_eq'⟩ := e_i_eq
      simp [e_i_regular_helper]
    .
      simp at other_val_in_image
      obtain ⟨list, hlist, list_prod_eq⟩ := other_val_in_image
      apply_fun Inv.inv at list_prod_eq
      simp at list_prod_eq
      rw [← list_prod_eq]
      apply Subgroup.inv_mem
      apply Subgroup.list_prod_mem
      intro z hz
      simp [list_len_n] at hlist
      simp at hz
      obtain ⟨z_in_s_n, z_in_list⟩ := hz
      simp [three_two_S_n] at z_in_s_n
      apply Subgroup.subset_closure
      simp
      obtain ⟨p, p_in_range, e_i_eq⟩ := z_in_s_n
      use p
      norm_cast
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp [gamma_m_helper] at e_i_eq
      obtain ⟨q, q_mem, e_i_eq'⟩ := e_i_eq
      simp [e_i_regular_helper]


-- The kernel of `φ` is generated by {γ_m_i}
lemma three_two_gamma_m_generates(φ: (Additive G) →+ ℤ) (hφ: Function.Surjective φ) (γ: G) (hγ: φ γ = 1) : Subgroup.closure (Set.range (Function.uncurry (gamma_m_helper (G := G) (S := S) φ γ))) = AddSubgroup.toSubgroup φ.ker := by
  have phi_ofmul: φ (ofMul γ) = 1 := by
    exact hγ
  --
  let e_i: S → (Additive G) := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))
  let e_i_regular: S → G := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))



  let max_phi := max 1 ((Finset.image Int.natAbs (Finset.image φ (Finset.image ofMul S))).max' (by simp [S_nonempty]))
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

  have closure_enlarge: Subgroup.closure ({1, γ, γ⁻¹} ∪ (e_i '' Set.univ)) = Subgroup.closure (({1, γ, γ⁻¹} ∪ (e_i_regular '' Set.univ))^(max_phi + 1)) := by
    rw [Subgroup.closure_pow]
    . simp
    . unfold max_phi
      simp


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

      have foo := Submonoid.exists_list_of_mem_closure (s := ({1, γ, γ⁻¹} ∪ e_i '' Set.univ) ∪ ({1, γ, γ⁻¹} ∪ e_i '' Set.univ)⁻¹) (x := z)
      apply_fun Subgroup.toSubmonoid at new_closure_e_i
      rw [Subgroup.closure_toSubmonoid _] at new_closure_e_i
      rw [Subgroup.closure_toSubmonoid _] at new_closure_e_i
      rw [new_closure_e_i] at foo
      rw [← Subgroup.closure_toSubmonoid _] at foo
      simp only [mem_toSubmonoid, Finset.mem_coe] at foo

      conv at foo =>
        intro hz
        arg 1
        intro l
        lhs
        intro y
        intro hy
        rw [Set.union_comm {1, γ, γ⁻¹} (e_i '' Set.univ)]
        rw [Set.union_assoc]
        arg 1
        rhs
        rw [Set.union_comm]
        rw [Set.union_inv]
        rw [Set.union_assoc]
        rhs
        simp

      have generates := hGS.generates
      have z_in_top: z ∈ (⊤: Set G) := by
        simp

      rw [← generates] at z_in_top
      have z_eq_prod := foo z_in_top
      clear foo

      let E: Set G := {γ, γ⁻¹} ∪ Set.range e_i_regular ∪ (Set.range e_i_regular)⁻¹

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

          let rewritten_sub_list := (rewrite_list (gamma_copy ++ (list.dropWhile is_gamma).tail) sublist_phi_zero)
          let return_list := (⟨γ^m * (List.dropWhile is_gamma list)[0] * γ^(-m), in_range⟩) :: rewritten_sub_list.val

          -- Show that the list (rewritten in terms of `γ^m * e_i * γ^(-m)` terms) is in the kernel of φ


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
      termination_by list.length
      decreasing_by {
        simp
        split_ifs
        .
          simp
          conv =>
            rhs
            rw [← take_drop_len (p := fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹))]
          apply add_lt_add_of_le_of_lt
          . apply count_head_lt
          . simp [is_gamma] at dropwhile_len_gt
            apply Nat.sub_one_lt
            apply Nat.pos_iff_ne_zero.mp dropwhile_len_gt
        .
          simp-- [count_gamma_copy]
          conv =>
            rhs
            rw [← take_drop_len (p := fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹))]
          apply add_lt_add_of_le_of_lt
          . apply count_head_lt
          . simp [is_gamma] at dropwhile_len_gt
            apply Nat.sub_one_lt
            apply Nat.pos_iff_ne_zero.mp dropwhile_len_gt
      }

      obtain ⟨z_list, h_z_list⟩ := z_eq_prod
      rw [← list_filter_one] at h_z_list
      have z_filter_mem_e: ∀ p ∈ (List.filter (fun s ↦ !decide (s = 1)) z_list), p ∈ E := by
        intro p hp
        dsimp [E]
        simp at hp
        obtain ⟨h_z_list_in, _⟩ := h_z_list
        specialize h_z_list_in p hp.1
        rw [Set.mem_union] at h_z_list_in
        rw [Set.mem_union] at h_z_list_in
        match h_z_list_in with
        | .inl h_z_list_in =>
          simp at h_z_list_in
          obtain ⟨a, a_mem_s, e_i_ap⟩ := h_z_list_in
          apply Set.mem_union_left
          apply Set.mem_union_right
          simp
          use a
          use a_mem_s
        | .inr h_z_list_in =>
          simp at h_z_list_in
          match h_z_list_in with
          | .inl h_z_list_in =>
            obtain ⟨a, a_mem_s, e_i_ap⟩ := h_z_list_in
            apply Set.mem_union_right
            simp
            use a
            use a_mem_s
          | .inr h_z_list_in =>
            simp [hp.2] at h_z_list_in
            apply Set.mem_union_left
            apply Set.mem_union_left
            simp
            exact h_z_list_in.symm

      let my_res := rewrite_list ((z_list.filter (fun s ↦ !decide (s = 1))).attach.map (fun (g) => ⟨g.val, z_filter_mem_e g.val g.property⟩)) (by
        simp
        -- TODO - there has to be a less awful way of doing this
        conv =>
          arg 1
          arg 2
          arg 1
          arg 2
          equals (List.filter (fun s ↦ !decide (s = 1)) z_list) =>
            clear h_z_list

            ext i q
            simp
            by_cases list_get: (List.filter (fun s ↦ !decide (s = 1)) z_list)[i]? = none
            . simp [list_get]
            . simp at list_get
              simp [list_get]
        rw [← ofMul_list_prod]
        rw [h_z_list.2]
        exact hz
      )
      have my_res_prop := my_res.property
      rw [← Subgroup.mem_toSubmonoid]
      rw [Subgroup.closure_toSubmonoid _]
      conv =>
        equals z ∈ (Submonoid.closure (Set.range (Function.uncurry gamma_m) ∪ (Set.range (Function.uncurry gamma_m))⁻¹) : Set _) =>
          rfl
      rw [Submonoid.closure_eq_image_prod]
      rw [Set.mem_image]
      use my_res.val.unattach
      refine ⟨?_, ?_⟩
      . simp only [Set.mem_setOf_eq]
        intro x hx
        rw [List.mem_unattach] at hx
        obtain ⟨x_prop, _⟩ := hx
        exact x_prop
      .
        rw [← my_res_prop]
        conv =>
          pattern List.unattach _
          equals (List.filter (fun s ↦ !decide (s = 1)) z_list) =>
            ext i q
            simp
            by_cases list_get: (List.filter (fun s ↦ !decide (s = 1)) z_list)[i]? = none
            . simp [list_get]
            . simp at list_get
              simp [list_get]
        exact h_z_list.2
  exact gamma_m_ker_phi

lemma three_two_ker_fg (d: ℕ) (hd: d >= 1) (hG: HasPolynomialGrowthD d (S := S)) (g: G) (φ: (Additive G) →+ ℤ) (hφ: Function.Surjective φ): φ.ker.FG := by
  simp only [AddSubgroup.FG]
  obtain ⟨γ, phi_gamma⟩ := hφ 1
  --obtain ⟨n, hn⟩ := three_two_poly_growth d hd hG γ φ hφ phi_gamma
  obtain ⟨n, hn⟩ := three_poly_poly_growth_all_s_n d hd hG γ φ hφ phi_gamma
  use (Finset.preimage (three_two_S_n (S := S) φ γ (n)) Multiplicative.ofAdd (by
    apply Set.injOn_of_injective
    exact fun ⦃a₁ a₂⦄ a ↦ a
  ))
  simp
  ext z
  refine ⟨?_, ?_⟩
  . intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      simp [three_two_S_n, gamma_m_helper, e_i_regular_helper] at hx
      obtain ⟨m, m_in_range, s, s_mem_s, prod_eq_x⟩ := hx
      apply_fun ofMul at prod_eq_x
      simp only [ofMul_mul, ofMul_zpow, ofMul_inv, ofMul_toMul] at prod_eq_x
      simp
      conv at prod_eq_x =>
        rhs
        equals x => rfl
      rw [← prod_eq_x]
      simp [phi_gamma]
      conv =>
        lhs
        arg 2
        equals (ofMul s + -(φ (ofMul s) • γ)) => rfl
      simp [phi_gamma]
    | one =>
      simp
    | mul y z y_mem z_mem hy hz =>
      exact (AddSubgroup.add_mem_cancel_right φ.ker hz).mpr hy
    | inv x x_mem hx =>
      exact AddSubgroup.neg_mem φ.ker hx
  . intro hz
    have generates_ker := three_two_gamma_m_generates φ hφ γ phi_gamma
    --obtain ⟨γ, hγ, generates_ker⟩ := three_two_gamma_m_generates φ hφ

    have mem_ker_iff: ∀ z, z ∈ (AddSubgroup.toSubgroup φ.ker) ↔ z ∈ φ.ker := by
      exact fun z ↦ Eq.to_iff rfl
    rw [← mem_ker_iff] at hz
    rw [← generates_ker] at hz

    --have exists_prod_list := Submonoid.exists_list_of_mem_closure (s := S ∪ S⁻¹) (x := x)
    rw [← mem_toSubmonoid] at hz
    rw [Subgroup.closure_toSubmonoid _] at hz
    have exists_prod := Submonoid.exists_list_of_mem_closure hz
    obtain ⟨l, l_mem, z_eq_prod⟩ := exists_prod
    rw [← z_eq_prod]
    conv =>
      arg 2
      equals ofMul l.prod => rfl
    apply AddSubgroup.list_sum_mem
    simp only [Additive.forall]
    intro a ha
    specialize l_mem (ofMul a) ha
    --simp [three_two_S_n]
    simp at l_mem
    match l_mem with
    | .inl l_mem =>
      obtain ⟨p, s, s_mem, helper_eq_a⟩ := l_mem
      specialize hn p
      simp at hn
      rw [Set.range_subset_iff] at hn
      specialize hn ⟨s, s_mem⟩
      simp at hn
      rw [← helper_eq_a]
      rw [← Subgroup.toAddSubgroup'_closure]
      exact hn
    | .inr l_mem =>
      rw [← AddSubgroup.neg_mem_iff]
      obtain ⟨p, s, s_mem, helper_eq_a⟩ := l_mem
      conv at helper_eq_a =>
        rhs
        equals -ofMul a => rfl
      specialize hn p
      simp at hn
      rw [Set.range_subset_iff] at hn
      specialize hn ⟨s, s_mem⟩
      simp at hn
      rw [← helper_eq_a]
      rw [← Subgroup.toAddSubgroup'_closure]
      exact hn

-- Decompose list of {e_k, γ}:

-- The starting list must have the powers of γ sum to zero (since it's in the kernel of φ)


-- Map the list in a way that maintains the invariant that the powers of γ sum to zero:
-- If the head is e_i, then map it to γ_0,i = e_i
-- Otherwise, collect gamma terms:
-- If we get γ^a e_i * γ^b, then
-- * If the head is γ^n e_i for some n (collecting up adjacent γ), then choose γ_n,i = γ^n * e_i * γ^(-n)
-- * If the remaining list is just γ^n, then n must be 0 (since we maintained the invariant)

#print axioms three_two_gamma_m_generates
#print axioms three_two_ker_fg
