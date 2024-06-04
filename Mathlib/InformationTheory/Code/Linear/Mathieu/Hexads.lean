import Mathlib.InformationTheory.Code.Linear.Mathieu.GolayWeight
import Mathlib.Data.Fintype.Powerset
import Mathlib.Combinatorics.Pigeonhole

open Set
open scoped Pointwise
open BigOperators

open Submodule.Quotient

abbrev Hexad_space := golay_code_space' ⧸ GolayCode
instance : Fintype (GolayCode.toAddSubgroup) := inferInstanceAs (Fintype GolayCode)

lemma mem_coset_iff {x : golay_code_space'} {y : golay_code_space'} :
    (mk x : Hexad_space) = (mk y : Hexad_space) ↔ x + y ∈ GolayCode := by
  rw [Submodule.Quotient.eq]
  simp only [CharTwo.sub_eq_add]

noncomputable def minrep (x : Hexad_space) : golay_code_space' :=
  Function.argminOn (golay_code_space'.weight) wellFounded_lt (mk ⁻¹' {x})
    (mk_surjective GolayCode x)

lemma minrep_in (x : Hexad_space) : (mk (minrep x) : Hexad_space) = x := by
  have : minrep x ∈ (mk ⁻¹' {x}) := by
    dsimp [minrep]
    exact
      Function.argminOn_mem golay_code_space'.weight wellFounded_lt (mk ⁻¹' {x}) (minrep.proof_1 x)
  simp only [mem_preimage, mem_singleton_iff] at this
  exact this


noncomputable def minrep_weight (x : Hexad_space) : ℕ :=
  (minrep x).weight

lemma minrep_weight_le_weight (x : golay_code_space') : minrep_weight (mk x : Hexad_space) ≤ x.weight:= by
  dsimp [minrep_weight,minrep]
  apply Function.argminOn_le
  simp only [mem_preimage, mem_singleton_iff]

lemma weight_triangle (x y : golay_code_space') : (x + y).weight ≤ x.weight + y.weight := by
  rw [weight_sum]
  simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]



lemma weight_le_four_unique_of_weight_le_three {x y: golay_code_space'} (hx : x.weight ≤ 3)
    (hy : y.weight ≤ 4) (heq : (mk x : Hexad_space) = (mk y : Hexad_space)): x = y := by
  have hsum : (x + y) ∈ GolayCode := by exact mem_coset_iff.mp heq
  have : (x + y).weight ≤ x.weight + y.weight := by
    exact weight_triangle x y
  have : (x + y).weight ≤ 7 := by
    omega
  have : (x + y).weight = 0 ∨ 8 ≤ (x + y).weight := by exact gc_weight_eq_zero_or_ge_8 hsum
  have hzero : (x + y).weight = 0 := by omega
  simp only [Finset.card_eq_zero] at hzero
  ext c
  dsimp [golay_code_space'.to_finset] at hzero
  rw [Finset.eq_empty_iff_forall_not_mem] at hzero
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hzero
  specialize hzero c
  revert hzero
  generalize x c = a
  generalize y c = b
  revert a b
  decide

lemma weight_inter_eq_zero_or_four_of_weight_four {x y : golay_code_space'} (hx : x.weight = 4)
    (hy : y.weight = 4) (heq : (mk x : Hexad_space) = (mk y : Hexad_space)): (x * y).weight = 0 ∨ (x * y).weight = 4 := by
  have hsum : (x + y) ∈ GolayCode := by exact mem_coset_iff.mp heq
  have h1: (x + y).weight = x.weight + y.weight - 2 * (x * y).weight := by
    exact weight_sum x y
  have h2 : (x + y).weight = 0 ∨ 8 ≤ (x + y).weight := by exact gc_weight_eq_zero_or_ge_8 hsum
  rw [hx,hy] at h1
  have : (x * y).weight ≤ x.weight := weight_mul_le_weight_left x y
  omega

lemma golay_code_space'.to_finset_inj : Function.Injective golay_code_space'.to_finset := by
  intro a b h
  rw [Finset.ext_iff] at h
  simp only [mem_to_finset, Prod.forall] at h
  ext v
  specialize h v.1 v.2
  simp only [Prod.mk.eta] at h
  revert h
  generalize a v = x
  generalize b v = y
  revert x y
  decide

lemma eq_inter_of_weight_eq_weight_inter {x y : golay_code_space'}
    (hinter : x.weight = (x * y).weight): x = (x * y) := by
  dsimp [golay_code_space'.weight] at hinter
  apply golay_code_space'.to_finset_inj
  have : (x * y).to_finset = x.to_finset ∩ y.to_finset := by exact to_finset_mul x y
  rw [this] at hinter ⊢
  symm
  apply Finset.eq_of_subset_of_card_le
  . exact Finset.inter_subset_left x.to_finset y.to_finset
  . exact Nat.le_of_eq hinter


lemma eq_of_weight_four_of_inter_four {x y : golay_code_space'} (hx : x.weight = 4) (hy : y.weight = 4)
    (heq : (x * y).weight = 4) : x = y := by
  rw [← hx] at heq
  rw [eq_inter_of_weight_eq_weight_inter heq.symm]
  rw [hx, ← hy] at heq
  rw [mul_comm] at heq ⊢
  rw [← eq_inter_of_weight_eq_weight_inter heq.symm]


lemma golay_code_space_card_eq : Fintype.card golay_code_space' = 2 ^ 24 := by
  rw [Fintype.card_pi]
  rw [Finset.prod_const,ZMod.card]
  decide


lemma golay_code_card_eq : Fintype.card GolayCode = 2 ^ 12 := by
  suffices Fintype.card ((Fin 12) → ZMod 2) = 2 ^ 12 by
    rw [← this]
    rw [Fintype.card_eq]
    exact ⟨gc_basis.equivFun.toEquiv⟩
  simp only [Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Nat.reducePow]


lemma hexad_space_card_eq : Fintype.card Hexad_space = 2 ^12 := by
  suffices Fintype.card golay_code_space' = Fintype.card GolayCode * Fintype.card Hexad_space by
    rw [golay_code_card_eq] at this
    rw [golay_code_space_card_eq] at this
    omega
  rw [GolayCode.card_eq_card_quotient_mul_card]

noncomputable def of_finset (s : Finset golay_code_index): golay_code_space' :=
  fun c => if c ∈ s then 1 else 0

lemma of_finset_to_finset (x : golay_code_space') : of_finset (x.to_finset) = x := by
  ext c
  dsimp [of_finset,golay_code_space'.to_finset]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  generalize x c = a
  revert a
  decide

lemma to_finset_of_finset (s : Finset golay_code_index) : (of_finset s).to_finset = s := by
  ext c
  dsimp [of_finset,golay_code_space'.to_finset]
  simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not, Finset.filter_univ_mem]

lemma card_weight_eq (n:ℕ) : Fintype.card {x : golay_code_space' // x.weight = n } = (24 : ℕ).choose n:= by
  simp_rw [golay_code_space'.weight]
  calc
    Fintype.card { x : golay_code_space' // x.to_finset.card = n }
      = Fintype.card {x : Finset golay_code_index // x.card = n} := by
      rw [Fintype.card_eq]
      exact ⟨{
        toFun := fun ⟨x,hx⟩ => ⟨x.to_finset,hx⟩
        invFun := fun ⟨x,hx⟩ => ⟨of_finset x, by rw [to_finset_of_finset x]; exact hx⟩
        left_inv := fun ⟨x,hx⟩ => by
          simp only [Subtype.mk.injEq]
          rw [of_finset_to_finset x]
        right_inv := fun ⟨x,hx⟩ => by
          simp only [Subtype.mk.injEq]
          rw [to_finset_of_finset x]
      }⟩
    _ = (24 : ℕ).choose n := by
      simp only [Fintype.card_finset_len, Fintype.card_prod, Fintype.card_fin]
      have : Fintype.card F4 = 4 := by decide
      rw [this]

lemma finset_filter_card_weight_eq (n:ℕ) :
    (Finset.filter (fun x : golay_code_space' => x.weight = n) Finset.univ).card = (24 :ℕ).choose n := by
  rw [← card_weight_eq n]
  exact Eq.symm (Fintype.card_subtype (fun x : golay_code_space' ↦ x.weight = n))

lemma finset_filter_weight_le (n : ℕ) :
  (Finset.filter (fun x :golay_code_space' => x.weight ≤ n) Finset.univ).card =
    ∑ i ≤ n, (Finset.filter (fun x : golay_code_space' => x.weight = i) Finset.univ).card := by
  induction n
  . simp_rw [Finset.Iic,LocallyFiniteOrderBot.finsetIic]
    simp only [nonpos_iff_eq_zero, Finset.card_eq_zero, bot_eq_zero', Finset.Icc_self,
      Finset.sum_singleton]
  . rename_i n hi
    rw [← Finset.filter_card_add_filter_neg_card_eq_card (fun x : golay_code_space' => x.weight = n + 1)]
    simp_rw [Finset.filter_filter]
    have : ∀ m, (m ≤ n + 1 ∧ m = n + 1) ↔ m = n + 1 := by simp only [and_iff_right_iff_imp,
      forall_eq, le_refl]
    simp_rw [this]
    have : ∀ m, (m ≤ n + 1 ∧ ¬ m = n + 1) ↔ m ≤ n := by omega
    simp_rw [this]
    rw [hi]
    have : Finset.Iic (n + 1) = insert (n + 1) (Finset.Iic n) := by
      ext m
      simp only [Finset.mem_Iic, Finset.mem_insert]
      omega
    rw [this]
    simp only [Finset.mem_Iic, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero,
      not_false_eq_true, Finset.sum_insert]

lemma card_weight_le_three :
    Fintype.card {x:golay_code_space' // x.weight ≤ 3} = 2325 := by
  rw [Fintype.card_subtype]
  rw [finset_filter_weight_le 3]
  dsimp [Finset.Iic, LocallyFiniteOrderBot.finsetIic]
  simp only [bot_eq_zero']
  dsimp [Finset.Icc, LocallyFiniteOrder.finsetIcc]
  simp only [Multiset.sum_coe]
  dsimp [List.range']
  simp_rw [finset_filter_card_weight_eq]
  decide

-- example : Fintype.card {x : golay_code_space' // x.weight = 2 } = 23 * 12 := by
--   rw [card_weight_eq 2]
--   simp only [Nat.reduceMul]
--   decide

-- example : Fintype.card {x : golay_code_space' // x.weight = 3 } = 23 * 4 * 22 := by
--   rw [card_weight_eq 3]
--   simp only [Nat.reduceMul]
--   decide

-- example : Fintype.card {x : golay_code_space' // x.weight = 4} = 23 * 22 * 21 := by
--   rw [card_weight_eq 4]
--   simp only [Nat.reduceMul]
--   decide

noncomputable def map_le_three_to_space : {x : golay_code_space' // x.weight ≤ 3} ≃ { y : Hexad_space // minrep_weight y ≤ 3 } where
  toFun := fun ⟨x,hx⟩ => ⟨(mk x : Hexad_space),by
    dsimp [minrep_weight]
    apply le_trans (minrep_weight_le_weight x) hx⟩
  invFun := fun ⟨y,hy⟩ => ⟨minrep y,by
    exact hy⟩
  left_inv := fun ⟨x,hx⟩ => by
    simp only [Subtype.mk.injEq]
    apply weight_le_four_unique_of_weight_le_three
    . exact le_trans (minrep_weight_le_weight x) hx
    . omega
    . exact minrep_in (mk x)
  right_inv := fun ⟨x,hx⟩ => by
    simp only [Subtype.mk.injEq]
    exact minrep_in x


noncomputable def dichotomy_equiv : {y : Hexad_space // minrep_weight y ≤ 3} ⊕ {y: Hexad_space // ¬ minrep_weight y ≤ 3} ≃ Hexad_space where
  toFun := fun
    | Sum.inl ⟨x,_⟩ => x
    | Sum.inr ⟨x,_⟩ => x
  invFun := fun x => if h : minrep_weight x ≤ 3 then Sum.inl ⟨x,h⟩ else Sum.inr ⟨x,h⟩
  left_inv := fun x => by
    obtain ⟨x,hx⟩|⟨x,hx⟩ := x
    all_goals simp only
    . rw [dif_pos hx]
    . rw [dif_neg hx]
  right_inv := fun x => by
    simp only
    if hx : minrep_weight x ≤ 3 then
      rw [dif_pos hx]
    else
      rw [dif_neg hx]

lemma card_dichotomy: Fintype.card {y : Hexad_space // minrep_weight y ≤ 3} + Fintype.card {y: Hexad_space // ¬ minrep_weight y ≤ 3} = 2 ^12 := by
  rw [← hexad_space_card_eq]
  rw [← Fintype.card_sum]
  rw [Fintype.card_eq]
  exact ⟨dichotomy_equiv⟩

lemma card_minweight_nle_three : Fintype.card {y : Hexad_space // ¬ minrep_weight y ≤ 3} = 1771 := by
  have := card_dichotomy
  have : Fintype.card {y : Hexad_space // minrep_weight y ≤ 3} = 2325 := by
    rw [← card_weight_le_three]
    rw [Fintype.card_eq]
    exact ⟨map_le_three_to_space.symm⟩
  omega


noncomputable def foo :
    {x :golay_code_space' // x.weight = 4} → {y :Hexad_space // minrep_weight y = 4} :=
  fun ⟨x,hx⟩ => ⟨ (mk x : Hexad_space), by
    have : minrep_weight (mk x : Hexad_space) ≤ 4 := by
      exact hx ▸ (minrep_weight_le_weight x)
    suffices ¬ minrep_weight (mk x : Hexad_space) ≤ 3 by
      omega
    intro hrep
    have : minrep (mk x : Hexad_space) = x := by
      apply weight_le_four_unique_of_weight_le_three
      . exact hrep
      . exact hx.le
      . exact minrep_in (mk x)
    dsimp [minrep_weight] at hrep
    rw [this] at hrep
    omega⟩


noncomputable def bar (x : golay_code_space'): Hexad_space := (mk x : Hexad_space)

def weight_four_finset := Finset.filter (fun x : golay_code_space' => x.weight = 4) Finset.univ

noncomputable def minrep_four_finset := Finset.filter (fun y : Hexad_space => minrep_weight y = 4) Finset.univ

lemma bar_map_weight (x : golay_code_space')
    (hx : x ∈ weight_four_finset):
    bar x ∈ minrep_four_finset := by
  dsimp [weight_four_finset] at hx
  dsimp only [minrep_four_finset]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  have le_four : minrep_weight (mk x : Hexad_space) ≤ 4 := by
    exact hx ▸ (minrep_weight_le_weight x)
  suffices ¬ minrep_weight (mk x : Hexad_space) ≤ 3 by
    push_neg at this
    exact Nat.le_antisymm le_four this
  intro hrep
  have : minrep (mk x : Hexad_space) = x := by
    apply weight_le_four_unique_of_weight_le_three
    . exact hrep
    . exact hx.le
    . exact minrep_in (mk x)
  dsimp [minrep_weight] at hrep
  rw [this] at hrep
  omega



-- lemma reverse_image_max_six (y : Hexad_space) (hy : minrep_weight y = 4):
--   Finset.filter (fun x : golay_code_space' => x.weight = 4) Finset.univ
#eval 6 * 23 * 11 * 7


-- set_option diagnostics true
lemma card_minrep_four_le : minrep_four_finset.card ≤ 1771 := by
  rw [← card_minweight_nle_three]
  rw [Fintype.card_subtype]
  apply Finset.card_mono
  rw [minrep_four_finset]
  intro h
  simp_rw [Finset.mem_filter]
  simp_rw [Finset.mem_univ, true_and]
  generalize minrep_weight h = z
  omega

lemma card_fiber_eq_sum (y:Hexad_space) :
    letI := fun a b : Hexad_space => Classical.propDecidable (a = b)
    (∑ x ∈ Finset.filter (fun x : golay_code_space' => bar x = y) weight_four_finset,
      x).weight = ∑ x ∈ Finset.filter (fun x: golay_code_space' => bar x = y) weight_four_finset, x.weight := by
  letI := fun a b : Hexad_space => Classical.propDecidable (a = b)
  refine Finset.induction_on' (Finset.filter (fun x : golay_code_space' => bar x = y) weight_four_finset) ?_ ?_
  . simp only [Finset.sum_empty, Finset.card_eq_zero]
    decide
  . intro x s hs hs' hnmem hw
    simp_rw [Finset.sum_insert hnmem]
    dsimp [weight_four_finset] at hs hs'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    rw [weight_sum_disjoint, hw]
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro y' hy'
    obtain hs' := hs' hy'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs'
    rw [← hs'.right] at hs
    dsimp [bar] at hs'
    rw [Eq.comm] at hs'
    suffices (x * y').weight = 0 by
      simp only [Finset.card_eq_zero] at this
      dsimp only [golay_code_space'.to_finset] at this
      rw [Finset.eq_empty_iff_forall_not_mem] at this
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at this
      ext c
      specialize this c
      revert this
      simp only [Pi.zero_apply]
      generalize (x * y') c = b
      fin_cases b <;> simp
    obtain l|r := weight_inter_eq_zero_or_four_of_weight_four hs.left hs'.left.symm hs.right
    . exact l
    have : x = y' := by exact eq_of_weight_four_of_inter_four hs.left hs'.left.symm r
    rw [this] at hnmem
    contradiction

lemma card_fiber_le_6 (y : Hexad_space) :
    letI := fun a b : Hexad_space => Classical.propDecidable (a = b)
    (Finset.filter (fun x => bar x = y) weight_four_finset).card ≤ 6 := by
  letI := fun a b : Hexad_space => Classical.propDecidable (a = b)
  suffices (Finset.filter (fun x => bar x = y) weight_four_finset).card * 4 ≤ 24 by
    omega
  rw [Finset.card_filter]
  rw [Finset.sum_mul]
  simp_rw [mul_comm,mul_ite,mul_one,mul_zero]
  dsimp [weight_four_finset]
  calc (∑ x ∈ Finset.filter (fun x ↦ x.weight = 4) Finset.univ, if bar x = y then 4 else 0)
    = (∑ x ∈ Finset.filter (fun x ↦ x.weight = 4) Finset.univ, if bar x = y then x.weight else 0) := by
        apply Finset.sum_congr rfl
        . simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro x hx
          rw [← hx]
  _ = ∑ x ∈ weight_four_finset, if bar x = y then x.weight else 0 := rfl
  _ = ∑ x ∈ Finset.filter (fun x => bar x = y) weight_four_finset, x.weight := by
      rw [← Finset.sum_filter]
  _ = (∑ x ∈ Finset.filter (fun x => bar x = y) weight_four_finset, x).weight := by
      rw [card_fiber_eq_sum]
  _ ≤ 24 := by apply weight_max_eq

lemma minrep_weight_four_of_weight_four {x : golay_code_space'} (hx : x.weight = 4) :
    minrep_weight (mk x : Hexad_space) = 4 := by
  have : minrep_weight (mk x : Hexad_space) ≤ 4 := by exact hx ▸ minrep_weight_le_weight x
  have : ¬ minrep_weight (mk x : Hexad_space) ≤ 3 := by
    intro h
    have : (mk (minrep (mk x : Hexad_space)) : Hexad_space) = (mk x : Hexad_space) := by
      exact minrep_in (mk x)
    have : minrep (mk x) = x := by
      apply weight_le_four_unique_of_weight_le_three h hx.le this
    dsimp [minrep_weight] at h
    rw [this,hx] at h
    contradiction
  omega


lemma weight_four_finset_card_eq_sum :
    letI := fun a b : Hexad_space => Classical.propDecidable (a = b)
    weight_four_finset.card = ∑ y ∈ minrep_four_finset, (Finset.filter (fun x => bar x = y) weight_four_finset).card := by
  letI := fun a b : Hexad_space => Classical.propDecidable (a = b)
  rw [Finset.card_eq_sum_card_fiberwise bar_map_weight]

lemma card_fiber_eq_six :
    letI := fun a b : Hexad_space => Classical.propDecidable (a = b)
    ∀ y ∈ minrep_four_finset, (Finset.filter (fun x => bar x = y) weight_four_finset).card = 6 := by
  rw [← Finset.sum_eq_sum_iff_of_le]
  . rw [← weight_four_finset_card_eq_sum]
    rw [Finset.sum_const]
    have := card_minrep_four_le
    -- simp only [smul_eq_mul] -- dit wegcommenten fixt de error
    sorry
  . intro i _
    exact card_fiber_le_6 i




/-
i have : minrep_four_finset.card ≤ 1771

i have : weight_four_finset.card = 10626 = 6 * 1771.
i have : fibers of `bar` have weight at most six.

i can prove : the cardinality of weight_four_finset.card is equal to the sum of cardinalities of fibers of `bar`

therefore, i must have that fibers have weight exact: by using `Finset.sum_eq_sum_iff_of_le`



i would like: 1771 ≤ Minrep_four_finset.card
to do this: show that  weight_four_finset.card ≤ 6 * minrep_four_finset.card
for this, it suffices to show that for every fiber of `bar` has at least 6 elements?

use something? weight_four_finset.card

-/
-- #check sum_le_sum_fiberwise_of_sum_fiber_nonpos
