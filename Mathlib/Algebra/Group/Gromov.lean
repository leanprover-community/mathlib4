import Mathlib

open Subgroup
open scoped Finset
open scoped Pointwise


variable {G : Type*} [Group G]

-- TODO - I don't really understand why `S` needs to be an `outParam`?
-- If I remove that, then the `PseudoMetricSpace G` starts erroring
-- See also:
-- * `set_option synthInstance.checkSynthOrder false`
class Generates {S: outParam (Finset G)}: Prop where
  generates : ((closure (S : Set G) : Set G) = ⊤)
  has_inv: ∀ g ∈ S, g⁻¹ ∈ S

variable {S : Finset G} [hGS: Generates (G := G) (S := S)]

lemma s_union_sinv : (S: Set G) ∪ (S: Set G)⁻¹ = S := by
  ext a
  have foo := hGS.has_inv (a⁻¹)
  simp only [inv_inv] at foo
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_inv, or_iff_left_iff_imp]
  exact foo

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

--def WordMetricSpace := MetricSpace.ofDistTopology ()
noncomputable instance WordDist.instMeasurableSpace: MeasurableSpace G := borel G

noncomputable instance WordDist.instBorelSpace: BorelSpace G where
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

noncomputable instance fakeSub: Sub G where
  sub x y := y⁻¹ * x

structure Lipschitz [Generates (G := G) (S := S)] where
  toFun: G → ℂ
  lipschitz: ∃ C, LipschitzWith C toFun

instance: FunLike (Lipschitz (G := G)) G ℂ where
  coe := Lipschitz.toFun
  -- TODO - why does this work? I blindly copied it from `OneHom.funLike`
  coe_injective' f g h := by cases f; cases g; congr

@[ext]
theorem Lipschitz.ext [Generates (G := G) (S := S)] {f g: Lipschitz (G := G)} (h: ∀ x, f.toFun x = g.toFun x): f = g := DFunLike.ext _ _ h

instance Lipschitz.add [Generates (S := S)] : Add (Lipschitz (G := G)) := {
  add := fun f g => {
    toFun := fun x => f.toFun x + g.toFun x
    lipschitz := by
      obtain ⟨C1, hC1⟩ := f.lipschitz
      obtain ⟨C2, hC2⟩ := g.lipschitz
      use C1 + C2
      exact LipschitzWith.add hC1 hC2
  }
}
instance Lipschitz.zero [Generates (S := S)] : Zero (Lipschitz (G := G)) := {
  zero := {
    toFun := fun x => 0
    lipschitz := by
      use 0
      exact LipschitzWith.const 0
  }
}
instance Lipschitz.addMonoid [Generates (S := S)] : AddMonoid (Lipschitz (G := G)) := {
  Lipschitz.zero,
  Lipschitz.add with
  add_assoc := fun _ _ _ => ext fun _ => add_assoc _ _ _
  zero_add := fun _ => ext fun _ => zero_add _
  add_zero := fun _ => ext fun _ => add_zero _
  nsmul := nsmulRec
}

instance Lipschitz.instAddCommMonoid: AddCommMonoid (Lipschitz (G := G)) := {
  Lipschitz.addMonoid with add_comm := fun _ _ => ext fun _ => add_comm _ _
}

-- V is the vector space
def V := Module ℂ (Lipschitz (G := G))

-- TODO - I don't think we can use this, as `MeasureTheory.convolution' would require our group to be commutative
-- (via `NormedAddCommGroup`)
--open scoped Convolution
--def Conv (f g: G → ℝ) := f ⋆[ContinuousLinearMap.mul (𝕜 := ℝ) G, μ] g
