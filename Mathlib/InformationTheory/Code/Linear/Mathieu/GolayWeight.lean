import Mathlib.InformationTheory.Code.Linear.Mathieu.BGolay
import Mathlib.InformationTheory.Code.Linear.Mathieu.GolayActions
import Mathlib.GroupTheory.Coset
import Mathlib.Data.Fintype.Basic

open Set
open scoped Pointwise
open BigOperators

example : True := trivial

-- #synth SMul (SemilinearCodeAut (ZMod 2) trivdist hdist GolayCode) (golay_code_index)
-- #synth Fintype golay_code_index

#synth AddCommGroup golay_code_space'

abbrev golay_code_space'.weight (x : golay_code_space') : ℕ :=
  x.to_finset.card

lemma weight_eq_norm (x : golay_code_space') : addGNorm hdist x = x.weight := by
  dsimp [golay_code_space'.weight,addGNorm,golay_code_space'.to_finset]
  rw [Nat.cast_inj]
  dsimp only [hammingNorm]
  suffices Finset.filter (fun i => x i ≠ 0) Finset.univ = Finset.filter (fun i => x i = 1) Finset.univ by
    rw [this]
  ext i
  simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  obtain z := x i
  revert z
  decide


lemma weight_max_eq (x : golay_code_space') : x.weight ≤ 24 := by
  dsimp [golay_code_space'.weight]
  suffices Finset.univ.card = 24 by
    rw [←this]
    exact Finset.card_le_univ _
  decide

section
variable {a n:ℕ∞}
instance : Decidable (a ∣ n) := by
  if n = 0 then
    rename_i h1
    apply Decidable.isTrue
    rw [h1]
    simp only [dvd_zero]
  else
  if a = 0 then
    rename_i h1 h2
    apply Decidable.isFalse
    rw [dvd_iff_exists_eq_mul_left]
    push_neg
    rw [h2]
    simp only [mul_zero, ne_eq, forall_const]
    exact h1
  else
  if n = ⊤ then
    apply Decidable.isTrue
    rename_i h1 h2 h
    rw [h]
    use ⊤
    rw [ENat.mul_top]
    exact h2
  else
  if a = ⊤ then
    apply Decidable.isFalse
    rw [dvd_iff_exists_eq_mul_left]
    push_neg
    intro c
    if c = 0 then
      rename_i h1 h2 h3 h4 h5
      rw [h5]
      rw [zero_mul]
      exact h1
    else
      rename_i h1 h2 h3 h4 h5
      rw [h4]
      rw [ENat.mul_top h5]
      exact h3
  else
    if ENat.toNat a ∣ ENat.toNat n then
      rename_i h1 h2 h3 h4 h5
      apply Decidable.isTrue
      rw [← ENat.coe_toNat h3,← ENat.coe_toNat h4]
      rw [dvd_iff_exists_eq_mul_left] at h5 ⊢
      obtain ⟨c,hc⟩ := h5
      use c
      rw [← ENat.coe_mul, hc]
    else
      apply Decidable.isFalse
      rename_i h1 h2 h3 h4 h5
      rw [dvd_iff_exists_eq_mul_left] at h5 ⊢
      push_neg at h5 ⊢
      intro c
      contrapose! h5
      use (ENat.toNat c)
      rw [h5]
      simp only [map_mul]
end
-- example : 2 ∣ (gc_b₁ * gc_b₄).weight := by decide


noncomputable def golay_code_space'.of_set (s : Set golay_code_index): golay_code_space' := fun c =>
  letI := fun x => Classical.propDecidable (x ∈ s)
  if c ∈ s then 1 else 0

instance instDecidablePred {m : golay_code_space'} : DecidablePred (. ∈ (m : Set golay_code_index)) := by
  intro x
  if h: m x = 1 then
    apply Decidable.isTrue
    simp only
    dsimp [Membership.mem,SetLike.coe, golay_code_space'.to_finset]
    simp only [toFinset_setOf, Finset.coe_filter, Finset.mem_univ, true_and]
    exact h
  else
    exact Decidable.isFalse (by
      dsimp [Membership.mem]
      dsimp [SetLike.coe,golay_code_space'.to_finset]
      simp only [toFinset_setOf, Finset.coe_filter, Finset.mem_univ, true_and]
      exact h)

@[simp]
lemma coe_of_set_eq_self (s : Set golay_code_index) :
    (golay_code_space'.of_set s : Set golay_code_index) = s := by
      ext y
      simp only [SetLike.mem_coe]
      dsimp [Membership.mem, SetLike.coe,golay_code_space'.to_finset]
      simp only [toFinset_setOf, Finset.coe_filter, Finset.mem_univ, true_and]
      dsimp [golay_code_space'.of_set]
      simp only [ite_eq_left_iff, zero_ne_one, imp_false, not_not, setOf_mem_eq]

@[simp]
lemma of_set_coe_eq_self (m : golay_code_space') :
    golay_code_space'.of_set (m : Set golay_code_index) = m := by
  ext c
  dsimp [golay_code_space'.of_set,SetLike.coe,golay_code_space'.to_finset]
  simp only [toFinset_setOf, Finset.coe_filter, Finset.mem_univ, true_and, mem_setOf_eq]
  obtain x := m c
  revert x
  decide


lemma inter_eq_inter (x y : golay_code_space') : (x ∩ y : Set golay_code_index) = x.to_finset ∩ y.to_finset := by
  dsimp [SetLike.coe]
  simp only [Finset.coe_inter]

lemma to_finset_mul (x y : golay_code_space') : (x * y).to_finset = x.to_finset ∩ y.to_finset := by
  dsimp [golay_code_space'.to_finset]
  simp only [mul_eq_one, toFinset_setOf]
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]

-- lemma to_finset_sub (x y : golay_code_space)

lemma weight_inter (x y: golay_code_space') :
  x.weight = (x * y).weight + (x * (1 + x * y)).weight := by
    dsimp [golay_code_space'.weight]
    suffices x.to_finset = (x * y).to_finset ∪ ((x * (1 + x * y))).to_finset by
      rw [this]
      rw [Finset.card_union_eq_card_add_card]
      simp_rw [to_finset_mul]
      refine Finset.disjoint_right.mpr ?_
      intro a ha
      simp only [Finset.mem_inter, not_and] at ha ⊢
      intro hx
      obtain ha := ha.right
      dsimp [golay_code_space'.to_finset] at ha hx ⊢
      simp only [CharTwo.sub_eq_add, add_right_eq_self, mul_eq_zero, toFinset_setOf,
        Finset.mem_filter, Finset.mem_univ, true_and] at ha hx ⊢
      rw [hx] at ha
      simp only [one_ne_zero, false_or] at ha
      rw [ha]
      simp only [zero_ne_one, not_false_eq_true]
    ext a
    dsimp [golay_code_space'.to_finset]
    simp only [toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, mul_eq_one,
      CharTwo.sub_eq_add, add_right_eq_self, mul_eq_zero, Finset.mem_union]
    generalize x a = z₁
    generalize y a = z₂
    revert z₁ z₂
    decide


lemma to_finset_add (x y : golay_code_space') :
    (x + y).to_finset
      = symmDiff x.to_finset y.to_finset := by
  ext i
  dsimp [golay_code_space'.to_finset]
  simp only [toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.mem_symmDiff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  generalize x i = z₁
  generalize y i = z₂
  revert z₁ z₂
  decide

lemma mul_self (x : golay_code_space') : x * x = x := by
  ext c
  simp only [Pi.mul_apply]
  generalize x c= z
  revert z
  decide

instance : CharP golay_code_space' 2 := by
  rw [CharP.charP_iff_prime_eq_zero]
  decide
  exact Nat.prime_two

lemma add_eq_symm_diff (x y : golay_code_space') :
    x + y = (x + x * y) + (y + x * y) := by
  ring_nf
  rw [CharP.ofNat_eq_zero golay_code_space' 2]
  rw [mul_zero,add_zero]

lemma add_self (x : golay_code_space') : x + x = 0 := by
  ext i
  rw [Pi.add_apply]
  simp only [CharTwo.add_self_eq_zero, Pi.zero_apply]

lemma weight_sum (x y : golay_code_space') :
    (x + y).weight = x.weight + y.weight - 2 * (x * y).weight:= by
  symm
  rw [weight_inter x (x * y).compl]
  dsimp [golay_code_space'.compl]
  rw [left_distrib,mul_one,← mul_assoc,mul_self]
  rw [left_distrib,mul_one,left_distrib,mul_self,← add_assoc, add_self,zero_add]
  rw [← mul_assoc, mul_self]
  rw [weight_inter y (x * y)]
  rw [left_distrib,mul_one]
  rw [mul_comm y,mul_assoc,mul_self]
  rw [mul_comm y, mul_assoc,mul_self]
  ring_nf
  rw [add_assoc,add_comm ((x * y).weight * 2)]
  rw [← add_assoc, Nat.add_sub_cancel]
  rw [weight_inter (x + y) x]
  rw [add_eq_symm_diff x y]
  simp_rw [right_distrib,mul_self]
  rw [mul_comm (x * y) x, ← mul_assoc,mul_self x, mul_comm y x,add_self,add_zero]
  simp_rw [left_distrib]
  simp only [mul_one, add_right_inj]
  rw [← mul_assoc,mul_self,← add_assoc x x (x * y),add_self,zero_add,← add_assoc (x * y)]
  rw [add_self,zero_add,mul_comm (x * y) x,← mul_assoc,mul_self,mul_self,add_self]
  rw [zero_add,add_zero, mul_comm y (x * y),mul_assoc x y y, mul_self,mul_comm y x]
  rw [add_self,add_zero,add_comm]

lemma mul_basis_even : ∀ x ∈ range gc_basis_fam, ∀ y ∈ range gc_basis_fam, 2 ∣ (x * y).weight := by
  rw [gc_basis_fam]
  dsimp [gc_b₁,gc_b₂,gc_b₃,gc_b₄,gc_b₅,gc_b₆,gc_b₇,gc_b₈,gc_b₉,gc_b₁₀,gc_b₁₁,gc_b₁₂]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons, Matrix.range_empty,
    union_empty, union_singleton, union_insert, mem_insert_iff, mem_singleton_iff]
  simp only [forall_eq_or_imp, forall_eq]
  constructor
  . decide
  constructor
  . decide
  constructor
  . decide
  constructor
  . decide
  constructor
  . decide
  constructor
  . decide
  constructor
  . decide
  constructor
  . decide
  decide -- for some reason putting this further up makes it fail

lemma enat_mul_sub_left_distrib (a b c : ℕ) : (a * (b - c) : ℕ∞) = (a * b - a * c) := by
  simp_rw [← ENat.coe_sub,←ENat.coe_mul, ← ENat.coe_sub]
  rw [Nat.mul_sub_left_distrib]


private lemma shortcut {a b n: ℕ∞} (hn : n ≠ 0) (hab : a = n * b) (hcd : a ≠ ⊤) : (b ≠ ⊤) := by
  rw [hab] at hcd
  contrapose! hcd
  rw [hcd]
  rw [ENat.mul_top hn]


lemma mul_gc_even {x y : golay_code_space'} (hx : x ∈ GolayCode) (hy : y ∈ GolayCode) :
    2 ∣ (x * y).weight := by
  rw [← gc_span_is_gc] at hx hy
  apply Submodule.span_induction₂ hx hy
  . exact mul_basis_even
  . simp only [zero_mul, forall_const]
    use 0
    decide
  . simp only [mul_zero, forall_const]
    use 0
    decide
  have_goal left_mul := by
    intro x₁ x₂ y ⟨c₁,hc₁⟩ ⟨c₂,hc₂⟩
    rw [right_distrib,weight_sum]
    rw [hc₁,hc₂,← left_distrib]
    generalize ((x₁ * y) * (x₂ * y)).weight = z
    use c₁ + c₂ - z
    rw [Nat.mul_sub_left_distrib,left_distrib]
  . intro x y₁ y₂ h₁ h₂
    rw [mul_comm] at h₁ h₂ ⊢
    exact left_mul y₁ y₂ x h₁ h₂
  have_goal left_smul := by
    intro r
    fin_cases r
    . simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, zero_smul, zero_mul]
      exact fun _ _ _ => ⟨0, by rw [mul_zero];decide⟩
    . simp only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, one_smul, imp_self, implies_true]
  . intro r x y h
    rw [mul_comm] at h ⊢
    exact left_smul r y x h

example : True := trivial

lemma four_dvd_weight_sum_of_terms :
    ∀ x ∈ GolayCode, ∀ y∈ GolayCode, 4 ∣ x.weight → 4 ∣ y.weight → 4 ∣ (x + y).weight := by
  intro x hx y hy
  intro ⟨c₁,hc₁⟩ ⟨c₂,hc₂⟩
  rw [weight_sum x y]
  generalize hz : (x * y).weight = z
  have hz_even : 2 ∣ z := by
    rw [← hz]
    exact mul_gc_even hx hy
  obtain ⟨z₂,hz₂⟩ := hz_even
  subst hz₂
  rw [hc₁,hc₂]
  ring_nf
  rw [← Nat.right_distrib,← Nat.mul_sub_right_distrib]
  simp only [dvd_mul_left]

lemma four_dvd_weight : ∀ x ∈ GolayCode, 4 ∣ x.weight := by
  rw [← gc_span_is_gc]
  intro x hx
  refine Submodule.span_induction' ?basis ?zero ?add ?smul hx
  . simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons, Matrix.range_empty,
      union_empty, union_singleton, union_insert, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      forall_eq]
    dsimp [gc_b₁,gc_b₂,gc_b₃,gc_b₄,gc_b₅,gc_b₆,gc_b₇, gc_b₈,gc_b₉,gc_b₁₀,gc_b₁₁,gc_b₁₂]
    repeat' apply And.intro
    any_goals (use 2;decide) -- all basis elements have weights either 2*4 or 2*3
    any_goals (use 3;decide)
  . use 0
    decide
  . rw [gc_span_is_gc]
    exact four_dvd_weight_sum_of_terms
  . intro a
    fin_cases a
    . simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, zero_smul]
      intro _ _ _
      use 0 ; decide
    . simp only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, one_smul, imp_self, implies_true]

lemma mem_coe_iff (x : golay_code_space') (i : golay_code_index) : i ∈ (x : Set golay_code_index) ↔ x i = 1 := by
  dsimp [SetLike.coe,golay_code_space'.to_finset]
  simp only [toFinset_setOf, Finset.coe_filter, Finset.mem_univ, true_and]
  rfl

lemma golay_code_space'.mem_iff (x : golay_code_space') (i : golay_code_index):
  i ∈ x ↔ x i = 1 := by
  rw [← mem_coe_iff x i]
  rfl


lemma coe_onesub (x : golay_code_space') : (↑(1 - x) : Set golay_code_index) = (x:Set golay_code_index)ᶜ := by
  ext v
  rw [mem_coe_iff (1 - x) v]
  simp only [Pi.sub_apply, Pi.one_apply, CharTwo.sub_eq_add, add_right_eq_self, mem_compl_iff,
    SetLike.mem_coe]
  rw [x.mem_iff]
  generalize x v = z
  revert z
  decide

def col (i : Fin 6) : golay_code_space' := fun c => if c.1 = i then 1 else 0

def row (x : F4) : golay_code_space' := fun c => if c.2 = x then 1 else 0

lemma row_prod_eq_zero (x y:F4) : x ≠ y ↔ row x * row y = 0 := by
  rw [Function.funext_iff]
  dsimp [row]
  simp only [mul_ite, mul_one, mul_zero, ite_eq_right_iff, one_ne_zero, imp_false, Prod.forall,
    forall_eq, forall_const]
  exact Iff.intro (fun x h => x h.symm) (fun x h => x h.symm)

lemma row_prod_eq (x y : F4) : row x  * row y = if x = y then row x else 0 := by
  if h:x = y then
    rw [if_pos h, h,mul_self]
  else
    rw [if_neg h,← row_prod_eq_zero]
    exact h

lemma col_prod_eq_zero (i j: Fin 6) : i ≠ j ↔ col i * col j = 0:= by
  symm
  rw [Function.funext_iff]
  dsimp [col]
  simp only [mul_ite, mul_one, mul_zero, ite_eq_right_iff, one_ne_zero, imp_false, Prod.forall,
    forall_const, forall_eq]
  exact Iff.intro (fun x h => x h.symm) (fun x h => x h.symm)

lemma col_prod_eq (i j: Fin 6) : col i * col j = if i = j then col i else 0 := by
  if h: i = j then
    rw [if_pos h, h, mul_self]
  else
    rw [if_neg h, ← col_prod_eq_zero]
    exact h

lemma one_eq_cols : 1 = col 0 + col 1 + col 2 + col 3 + col 4 + col 5 := by
  ext i
  fin_cases i <;> decide

lemma weight_sum_disjoint (a b : golay_code_space') (hdis: a * b = 0) :
    (a + b).weight = a.weight + b.weight := by
  rw [weight_sum,hdis]
  suffices (golay_code_space'.weight 0) = 0 by
    rw [this]
    simp only [mul_zero, tsub_zero]
  decide

lemma weight_split_by_column (x : golay_code_space') : x.weight = ∑ i, (x * col i).weight := by
  dsimp [Finset.univ,Fintype.elems,List.finRange]
  have : ∀ i j, x * col i * (x * col j) = x * (col i * col j) := by
    intros
    rw [mul_comm,mul_assoc,mul_comm (col _), ← mul_assoc,← mul_assoc,mul_self, mul_assoc]
  simp only [Fin.isValue, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
  nth_rw 1 [← mul_one x,one_eq_cols]
  simp_rw [left_distrib]
  repeat rw [weight_sum_disjoint]
  simp_rw [add_assoc]
  any_goals simp_rw [right_distrib]
  all_goals simp [this,col_prod_eq]

lemma col_weight_parity_eq_parity (x : golay_code_space') (i:Fin 6) :
    ↑((x * col i).weight) = to_binary_vert' x i := by
  dsimp [golay_code_space'.weight, to_binary_vert']
  calc
    ↑(x * col i).to_finset.card
      = ↑(Finset.filter (fun x_1 ↦ x x_1 * col i x_1 = 1) Finset.univ).card := by
        dsimp [golay_code_space'.to_finset]
    _ = ↑(Finset.filter (fun x_1 ↦ x x_1 = 1 ∧ x_1.1 = i) Finset.univ).card := by
        simp_rw [mul_eq_one]
        dsimp [col]
        simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
    _ = ↑(Finset.filter (fun y ↦ x (i,y) = 1) Finset.univ).card := by
        rw [Finset.card_eq_of_equiv ?equiv]
        case equiv => exact {
          toFun := fun ⟨y,hy⟩ => ⟨y.2,by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
            rw [← hy.right]
            exact hy.left⟩
          invFun := fun ⟨y',hy'⟩ => ⟨(i,y'),by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hy' ⊢
            exact hy'⟩
          left_inv := fun ⟨a,ha⟩ => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subtype.mk.injEq] at ha ⊢
            rw [← ha.right]
          right_inv := fun ⟨⟨z,b⟩,hb⟩ => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        }
    _ = ↑((∑ _ ∈ Finset.filter (fun y ↦ x (i,y) = 1) Finset.univ, 1) : ℕ) := by
      rw [Finset.card_eq_sum_ones]
    _ = ↑((∑ a : F4, if x (i, a) = 1 then 1 else 0) : ℕ) := by
      rw [Finset.sum_filter]
    _ = ∑ a : F4, ((if x (i,a) = 1 then 1 else 0 : ℕ) : ZMod 2) := by
      simp only [Finset.sum_boole, Nat.cast_id, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    _ = ∑ a : F4, if x (i,a) = 1 then (1:ZMod 2) else (0:ZMod 2) := by
      simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_boole]
    _ = ∑ a : F4, if x (i,a) = 1 then x (i,a) else x (i,a) := by
      congr
      simp only [ite_self]
      ext z
      generalize x (i,z) = y
      revert y
      decide
    _ = ∑ x_1 : F4, x (i, x_1) := by
      simp only [ite_self]

lemma col_weight_eq_four (i : Fin 6) : (col i).weight = 4 := by
  fin_cases i <;> decide

lemma mul_col_weight_le_four {x : golay_code_space'} {i : Fin 6} :
    (x * col i).weight ≤ 4 := by
  have col_card_eq_four : (col i).weight = 4 := by
    fin_cases i <;> decide
  rw [← col_card_eq_four]
  dsimp [golay_code_space'.weight]
  suffices (x * col i).to_finset ≤ (col i).to_finset by
    exact Finset.card_le_card this
  dsimp [golay_code_space'.to_finset]
  simp only [mul_eq_one]
  intro v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_imp, imp_self, implies_true]

lemma to_hexacode_eq_at_col {x : golay_code_space'} {i : Fin 6} :
    to_hexacode' x i = to_hexacode' (x * col i) i := by
  simp_rw [to_hexacode'_apply]
  simp only [Pi.mul_apply]
  dsimp [col]
  simp only [↓reduceIte, mul_one]



lemma col_weight_ne_four_of_nzero {x : golay_code_space'} {i : Fin 6}
    (hnzero : to_hexacode' x i ≠ 0) : (x * col i).weight ≠ 4 := by
  contrapose! hnzero
  dsimp [golay_code_space'.weight] at hnzero
  rw [to_hexacode_eq_at_col]
  suffices (x * col i) = (col i) by
    rw [this]
    fin_cases i <;> decide
  apply to_finset_inj
  apply Finset.eq_of_subset_of_card_le
  . intro h
    dsimp [golay_code_space'.to_finset]
    simp only [mul_eq_one, Finset.mem_filter, Finset.mem_univ, true_and, and_imp, imp_self,
      implies_true]
  . rw [hnzero]
    have := col_weight_eq_four i
    dsimp [golay_code_space'.weight] at this
    rw [this]

lemma col_weight_ne_zero_of_nzero {x : golay_code_space'} {i:Fin 6}
    (hnzero : to_hexacode' x i ≠ 0) : (x * col i).weight ≠ 0 := by
  contrapose! hnzero
  rw [to_hexacode_eq_at_col]
  simp only [Finset.card_eq_zero] at hnzero
  have : x * col i = 0 := by
    ext ⟨j,y⟩
    simp only [Pi.mul_apply, Pi.zero_apply, mul_eq_zero]
    dsimp [golay_code_space'.to_finset,col] at hnzero ⊢
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
    if hj : j = i then
      left
      rw [hj]
      simp only [mul_ite, mul_one, mul_zero] at hnzero
      rw [Finset.eq_empty_iff_forall_not_mem] at hnzero
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.forall] at hnzero
      specialize hnzero i y
      simp only [↓reduceIte] at hnzero
      revert hnzero
      generalize x (i,y) = a
      revert a
      decide
    else
      right
      exact hj
  rw [this]
  rw [to_hexacode'_apply]
  simp only [Pi.zero_apply, CharTwo.add_self_eq_zero, zero_smul]

lemma mul_col_weight_eq_four_of_even_of_w_nzero_of_hc_zero {x : golay_code_space'} {i : Fin 6}
    (heven : to_binary_vert' x i = 0) (hw : x (i,0) ≠ 0) (hczero : to_hexacode' x i = 0) :
    (x * col i).weight = 4 := by
  suffices x * col i = col i by
    rw [this]
    exact col_weight_eq_four i
  rw [Function.funext_iff]
  have hw : x (i,0) = 1 := by
    revert hw
    generalize x (i,0) = z
    revert z
    decide
  dsimp [col]
  simp only [mul_ite, mul_one, mul_zero, Prod.forall]
  intro j y
  if hj : j = i then
    rw [if_pos hj,if_pos hj]
    rw [hj]
    fin_cases y
    . exact hw
    . rw [(to_hexacode_binary_inv x i heven ).left]
      rw [hczero,hw]
      decide
    . rw [(to_hexacode_binary_inv x i heven).right.left]
      rw [hczero,hw]
      decide
    . rw [(to_hexacode_binary_inv x i heven).right.right]
      rw [hczero,hw]
      decide
  else
    rw [if_neg hj,if_neg hj]

lemma mul_col_weight_eq_zero_of_even_of_w_zero_of_hc_zero {x : golay_code_space'} {i : Fin 6}
    (heven : to_binary_vert' x i = 0) (hw : x (i,0) = 0) (hczero : to_hexacode' x i = 0) :
    (x * col i).weight = 0 := by
  dsimp [golay_code_space'.weight]
  simp only [Finset.card_eq_zero]
  rw [Finset.eq_empty_iff_forall_not_mem]
  dsimp [golay_code_space'.to_finset,col]
  simp only [mul_ite, mul_one, mul_zero, Finset.mem_filter, Finset.mem_univ, true_and, Prod.forall]
  intro j b
  if hj : j = i then
    rw [if_pos hj]
    rw [hj]
    clear hj j
    fin_cases b
    . rw [hw]
      decide
    . rw [(to_hexacode_binary_inv x i heven).left,hw,hczero]
      decide
    . rw [(to_hexacode_binary_inv x i heven).right.left,hw,hczero]
      decide
    . rw [(to_hexacode_binary_inv x i heven).right.right,hw,hczero]
      decide
  else
    rw [if_neg hj]
    decide


lemma top_row_parity_eq_coe_filter_card (x : golay_code_space') :
    ↑(Finset.filter (fun i ↦ ¬ x (i,0) = 0) Finset.univ).card = to_binary_hori' x := by
  rw [to_binary_hori'_apply]
  suffices (Finset.filter (fun i ↦ ¬ x (i,0) = 0) Finset.univ) = (Finset.filter (fun y => x (y,0) = 1) Finset.univ) by
    rw [this]
    calc
      ↑(Finset.filter (fun y ↦ x (y, 0) = 1) Finset.univ).card
        = ∑ x_1 : Fin 6, if x (x_1 ,0) = 1 then (1 : ZMod 2) else 0 := by
        simp only [Finset.sum_boole]
      _ = ∑ i, x (i,0) := by
        congr
        ext i
        generalize x (i,0) = z
        revert z
        decide
      _ = x (0, 0) + x (1, 0) + x (2, 0) + x (3, 0) + x (4, 0) + x (5, 0) := by
        dsimp [Finset.univ,Fintype.elems,List.finRange]
        simp only [Fin.isValue, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
        simp_rw [add_assoc]
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  generalize x (i,0) = z
  revert z
  decide


lemma mul_col_weight_eq_two_of_even_of_hc_nzero {x : golay_code_space'} {i:Fin 6}
    (heven : to_binary_vert' x i = 0) (hnzero : to_hexacode' x i ≠ 0) : (x * col i).weight = 2 := by
  have : (x * col i).weight ≤ 4 := by exact mul_col_weight_le_four
  have : (x * col i).weight ≠ 4 := by exact col_weight_ne_four_of_nzero hnzero
  have : (x * col i).weight ≠ 0 := by exact col_weight_ne_zero_of_nzero hnzero
  obtain hz := col_weight_parity_eq_parity x i
  rw [heven] at hz
  have : (x * col i).weight ≠ 1 := by
    by_contra hcontra
    rw [hcontra] at hz
    simp only [Nat.cast_one] at hz
    contradiction
  have : (x * col i).weight ≠ 3 := by
    by_contra hcontra
    rw [hcontra] at hz
    simp only [Nat.cast_ofNat] at hz
    contradiction
  omega

lemma one_le_col_weight_of_odd {x : golay_code_space'} {i : Fin 6} (hodd : to_binary_vert' x i = 1):
    1 ≤ (x * col i).weight := by
  obtain hz := col_weight_parity_eq_parity x i
  rw [hodd] at hz
  have : (x * col i).weight ≠ 0 := by
    intro hcontra
    rw [hcontra] at hz
    contradiction
  omega

lemma six_le_weight_gc_of_odd {x : golay_code_space'} (hx : x ∈ GolayCode) (hodd : to_binary_hori' x = 1) :
    6 ≤ x.weight := by
  rw [weight_split_by_column]
  calc
    6 = ∑ i : Fin 6, 1 := by simp only [mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    _ ≤ ∑ i : Fin 6, (x * col i).weight := by
      apply Finset.sum_le_sum
      intro i
      simp only [Finset.mem_univ, true_implies]
      apply one_le_col_weight_of_odd
      rw [hx.2 i]
      exact hodd


lemma eight_le_weight_gc_of_even_of_hc_nzero {x : golay_code_space'} (hx : x ∈ GolayCode)
    (heven : to_binary_hori' x = 0) (hnzero : to_hexacode' x ≠ 0): 8 ≤ x.weight := by
  rw [weight_split_by_column]
  calc
    8 = 4 * 2 := by decide
    _ ≤ (Finset.filter (fun j => ¬ to_hexacode' x j = 0) Finset.univ).card • 2 := by
      simp only [smul_eq_mul]
      obtain hz := @HexaCode.four_le_norm_of_nzero (to_hexacode' x) hx.1 hnzero
      dsimp [addGNorm] at hz
      simp only [Nat.ofNat_le_cast] at hz
      dsimp [hammingNorm] at hz
      exact Nat.mul_le_mul_right 2 hz
    _ ≤ ∑ _ ∈ (Finset.filter (fun j => ¬ to_hexacode' x j = 0) Finset.univ), 2 := by
      apply Finset.card_nsmul_le_sum
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, le_refl, implies_true]
    _ ≤ ∑ i ∈ (Finset.filter (fun j => ¬ to_hexacode' x j = 0) Finset.univ), (x * col i).weight := by
      apply Finset.sum_le_sum
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hnzero
      apply Eq.le
      symm
      apply mul_col_weight_eq_two_of_even_of_hc_nzero
      . rw [hx.2 i]
        exact heven
      . exact hnzero
    _ ≤ _ := by
      apply Finset.sum_le_univ_sum_of_nonneg
      simp only [zero_le, implies_true]

lemma eight_le_weight_gc_of_even_of_hc_zero {x : golay_code_space'} (hx : x ∈ GolayCode)
    (heven : to_binary_hori' x = 0) (hczero : to_hexacode' x = 0) (hnzero : x ≠ 0) : 8 ≤ x.weight := by
  suffices hsuf : 2 ≤ (Finset.filter (fun i => ¬ x (i,0) = 0) Finset.univ).card by
    calc
      8 = 2 * 4 := by decide
      _ ≤ (Finset.filter (fun i => ¬ x (i,0) = 0) Finset.univ).card • 4 := by
        simp only [smul_eq_mul]
        exact Nat.mul_le_mul_right 4 hsuf
      _ ≤ ∑ _ ∈ (Finset.filter (fun i => ¬ x (i,0) = 0) Finset.univ), 4 := by
        apply Finset.card_nsmul_le_sum
        simp only [le_refl, implies_true]
      _ = ∑ i ∈ (Finset.filter (fun i => ¬ x (i,0) = 0) Finset.univ), (x * col i).weight := by
        rw [Finset.sum_eq_sum_iff_of_le]
        have_goal weight_four := by
          intro i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro hnzero
          refine (mul_col_weight_eq_four_of_even_of_w_nzero_of_hc_zero ?_ hnzero ?_).symm
          . rw [hx.2 i]
            exact heven
          . rw [hczero]
            simp only [Pi.zero_apply]
        intro i hi
        specialize weight_four i hi
        exact weight_four.le
      _ ≤ ∑ i, (x * col i).weight := by
        apply Finset.sum_le_univ_sum_of_nonneg
        simp only [zero_le, implies_true]
      _ = x.weight := by exact Eq.symm (weight_split_by_column x)
  obtain hz := top_row_parity_eq_coe_filter_card x
  rw [heven] at hz
  have : (Finset.filter (fun i ↦ ¬ x (i,0) = 0) Finset.univ).card ≠ 1 := by
    intro h
    rw [h] at hz
    contradiction
  have : (Finset.filter (fun i ↦ ¬ x (i,0) = 0) Finset.univ).card ≠ 0 := by
    contrapose! hnzero
    simp only [Finset.card_eq_zero] at hnzero
    rw [Finset.eq_empty_iff_forall_not_mem] at hnzero
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Decidable.not_not] at hnzero
    ext ⟨i,c⟩
    simp only [Pi.zero_apply]
    obtain hz' := mul_col_weight_eq_zero_of_even_of_w_zero_of_hc_zero ?_ (hnzero i) ?_
    simp only [Finset.card_eq_zero] at hz'
    rw [Finset.eq_empty_iff_forall_not_mem] at hz'
    dsimp [golay_code_space'.to_finset, col] at hz'
    simp only [mul_ite, mul_one, mul_zero, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.forall] at hz'
    specialize hz' i c
    simp only [↓reduceIte] at hz'
    revert hz'
    generalize x (i,c) = z
    revert z
    decide
  . rw [hczero]
    simp only [Pi.zero_apply]
  skip_goal
  . rw [hx.2 i]
    exact heven
  omega


#check to_hexacode_binary_inv

lemma eight_le_weight_of_ne_zero {x:golay_code_space'} (hx : x ∈ GolayCode) (hnzero : x ≠ 0): 8 ≤ x.weight  := by
  have : 4 ∣ x.weight := by exact four_dvd_weight x hx
  if heven : to_binary_hori' x = 0 then
    if hc_zero : to_hexacode' x = 0 then
      have : 8 ≤ x.weight := by exact eight_le_weight_gc_of_even_of_hc_zero hx heven hc_zero hnzero
      omega
    else
      have : 8 ≤ x.weight := by exact eight_le_weight_gc_of_even_of_hc_nzero hx heven hc_zero
      omega
  else
    have hodd : to_binary_hori' x = 1 := by
      revert heven
      generalize to_binary_hori' x = z
      revert z
      decide
    have : 6 ≤ x.weight := by exact six_le_weight_gc_of_odd hx hodd
    omega

lemma gc_weight_eq_zero_or_ge_8 {x : golay_code_space'} (hx : x ∈ GolayCode) : x.weight = 0 ∨ 8 ≤ x.weight := by
  if h: x = 0 then
    left
    rw [h]
    decide
  else
    right
    exact eight_le_weight_of_ne_zero hx h

lemma coe_weight_eq_norm (x : golay_code_space') : ↑x.weight = addGNorm hdist x := by
  dsimp [addGNorm]
  simp only [Nat.cast_inj]
  dsimp [hammingNorm]
  dsimp [golay_code_space'.weight]
  dsimp [golay_code_space'.to_finset]
  congr
  ext i
  generalize x i = z
  fin_cases z
  . simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, zero_ne_one, not_true_eq_false]
  . simp only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, one_ne_zero, not_false_eq_true]

@[simp]
lemma mem_to_finset (x :golay_code_space') (y : golay_code_index) : y ∈ x.to_finset ↔ x y = 1 := by
  dsimp [golay_code_space'.to_finset]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma mul_subset_left (x y : golay_code_space') : (x * y).to_finset ≤ x.to_finset := by
  intro z
  simp only [mem_to_finset, Pi.mul_apply, mul_eq_one, and_imp]
  exact fun x _ => x

lemma weight_mul_le_weight_left (x y: golay_code_space') : (x * y).weight ≤ x.weight:= by
  dsimp [golay_code_space'.weight]
  apply Finset.card_mono
  exact mul_subset_left x y


lemma weight_mul_le_weight_right (x y : golay_code_space') : (x * y).weight ≤ y.weight := by
  rw [mul_comm]
  exact weight_mul_le_weight_left y x
