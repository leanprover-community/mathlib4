import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TwoSidedIdeal.BigOperators

universe u v

variable (K : Type u) [Field K]

open scoped TensorProduct

variable {K} in
/--
a non-zero element in an ideal that can be represented as a sum of tensor products of `n`-terms.
-/
structure is_obtainable_by_sum_tmul
    {ιA A B : Type*} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (x : A ⊗[K] B) (𝒜 : Basis ιA K A) (I : TwoSidedIdeal (A ⊗[K] B)) (n : ℕ) : Prop where
  mem : x ∈ I
  ne_zero : x ≠ 0
  rep : ∃ (s : Finset ιA) (_ : s.card = n) (f : ιA → B),
    x = ∑ i ∈ s, 𝒜 i ⊗ₜ[K] f i

variable {K} in
lemma is_obtainable_by_sum_tmul.exists_minimal_element
    {A B : Type v} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (ιA : Type*) (𝒜 : Basis ιA K A)
    (I : TwoSidedIdeal (A ⊗[K] B)) (hI : I ≠ ⊥) :
    ∃ (n : ℕ) (x : A ⊗[K] B), is_obtainable_by_sum_tmul x 𝒜 I n ∧
      ∀ (m : ℕ) (y : A ⊗[K] B) , is_obtainable_by_sum_tmul y 𝒜 I m → n ≤ m := by
  classical
  have := SetLike.ext_iff.not.mp hI
  push_neg at this

  obtain ⟨x, ⟨hx0, hx1⟩|⟨hx0, hx1⟩⟩ := this
  pick_goal 2
  · change x = 0 at hx1
    subst hx1
    exact hx0 I.zero_mem |>.elim
  obtain ⟨s, rfl⟩ := TensorProduct.eq_repr_basis_left 𝒜 x
  let n := @Nat.find (fun n => ∃ x : A ⊗[K] B, is_obtainable_by_sum_tmul x 𝒜 I n) _
    ⟨s.support.card, ∑ i ∈ s.support, 𝒜 i ⊗ₜ[K] s i, ⟨hx0, hx1, s.support, rfl, s, rfl⟩⟩
  obtain ⟨x, hx⟩ : ∃ x, is_obtainable_by_sum_tmul x 𝒜 I n :=
    @Nat.find_spec (fun n => ∃ x : A ⊗[K] B, is_obtainable_by_sum_tmul x 𝒜 I n) _
      ⟨s.support.card, ∑ i ∈ s.support, 𝒜 i ⊗ₜ[K] s i, ⟨hx0, hx1, s.support, rfl, s, rfl⟩⟩
  refine ⟨n, x, hx, fun m y hy => ?_⟩
  by_contra r
  simp only [not_le] at r
  have := @Nat.find_min (fun n => ∃ x : A ⊗[K] B, is_obtainable_by_sum_tmul x 𝒜 I n) _
      ⟨s.support.card, ∑ i ∈ s.support, 𝒜 i ⊗ₜ[K] s i, ⟨hx0, hx1, s.support, rfl, s, rfl⟩⟩ m r
  simp only [not_exists] at this
  exact this y hy

namespace TwoSidedIdeal

variable {R : Type*} [Ring R]

def span' (s : Set R) : TwoSidedIdeal R := .mk'
  {x | ∃ (ι : Type) (fin : Fintype ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, xL i * y i * xR i}
  ⟨Empty, Fintype.instEmpty, Empty.elim, Empty.elim, Empty.elim, by simp⟩
  (by
    rintro _ _ ⟨na, fina, xLa, xRa, ya, rfl⟩ ⟨nb, finb, xLb, xRb, yb, rfl⟩
    refine ⟨na ⊕ nb, inferInstance, Sum.elim xLa xLb, Sum.elim xRa xRb, Sum.elim ya yb, by
      simp⟩)
  (by
    rintro _ ⟨n, finn, xL, xR, y, rfl⟩
    exact ⟨n, finn, -xL, xR, y, by simp⟩)
  (by
    rintro a _ ⟨n, finn, xL, xR, y, rfl⟩
    exact ⟨n, finn, a • xL, xR, y, by
      rw [Finset.mul_sum]; simp only [mul_assoc, Pi.smul_apply, smul_eq_mul]⟩)
  (by
    rintro _ b ⟨n, finn, xL, xR, y, rfl⟩
    exact ⟨n, finn, xL, fun x ↦ xR x * b, y, by simp [Finset.sum_mul, mul_assoc]⟩)

lemma mem_span'_iff_exists_fin (s : Set R) (x : R) :
    x ∈ span' s ↔
    ∃ (ι : Type) (_ : Fintype ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, xL i * (y i : R) * xR i := by
  simp only [span', mem_mk', Set.mem_setOf_eq]

lemma mem_span_iff_exists_fin (s : Set R) (x : R) :
    x ∈ span s ↔
    ∃ (ι : Type) (_ : Fintype ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, xL i * (y i : R) * xR i := by
  suffices eq1 : span s = span' s by
    rw [eq1]
    simp only [span', Set.mem_setOf_eq]
    generalize_proofs h1 h2 h3 h4 h5
    simp_all only [mem_mk', Set.mem_setOf_eq]

  rw [span, RingCon.ringConGen_eq]
  apply ringCon_injective
  refine sInf_eq_of_forall_ge_of_forall_gt_exists_lt ?_ ?_
  · rintro I (hI : ∀ a b, _ → _)
    suffices span' s ≤ .mk I by
      rw [ringCon_le_iff] at this
      exact this
    intro x h
    rw [mem_span'_iff_exists_fin] at h
    obtain ⟨n, finn, xL, xR, y, rfl⟩ := h
    rw [mem_iff]
    refine TwoSidedIdeal.finsetSum_mem _ _ _ fun i _ ↦ TwoSidedIdeal.mul_mem_right _ _ _
      (TwoSidedIdeal.mul_mem_left _ _ _ <| hI (y i) 0 (by simp))
  · rintro I hI
    exact ⟨(span' s).ringCon, fun a b H ↦ ⟨PUnit, inferInstance, fun _ ↦ 1, fun _ ↦ 1,
      fun _ ↦ ⟨a - b, by simp [H]⟩, by simp⟩, hI⟩

lemma coe_top_set : ((⊤ : TwoSidedIdeal R) : Set R) = Set.univ := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_univ]
  rfl

lemma span_le {s : Set R} {I : TwoSidedIdeal R} : s ⊆ I ↔ span s ≤ I := by
  rw [le_iff]
  constructor
  · intro h x hx
    rw [SetLike.mem_coe, mem_span_iff_exists_fin] at hx
    obtain ⟨n, finn, xL, xR, y, rfl⟩ := hx
    exact I.finsetSum_mem _ _ fun i _ => I.mul_mem_right _ _ (I.mul_mem_left _ _ <| h (y i).2)
  · intro h x hx
    exact h <| subset_span hx

lemma coe_bot_set : ((⊥ : TwoSidedIdeal R) : Set R) = {0} := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_singleton_iff]
  rfl

end TwoSidedIdeal

open scoped Classical in
lemma TensorProduct.sum_tmul_basis_right_eq_zero'
    (B : Type*) [Ring B] [Algebra K B]
    (C : Type*) [Ring C] [Algebra K C]
    {ιC : Type*} (𝒞 : Basis ιC K C)
    (s : Finset ιC) (b : ιC → B)
    (h : ∑ i ∈ s, b i ⊗ₜ[K] 𝒞 i = 0) :
    ∀ i ∈ s, b i = 0 := by
  intro i
  have := TensorProduct.sum_tmul_basis_right_eq_zero (κ := ιC) 𝒞 (M := B)
    { support := s.filter fun i => b i ≠ 0
      toFun := fun x => if x ∈ s then b x else 0
      mem_support_toFun := by simp }
    (by
      simp only [Finsupp.sum, ne_eq, Finsupp.coe_mk, Finset.sum_filter, ite_not]
      convert h using 1
      congr!
      aesop)
  simpa using Finsupp.ext_iff.mp this i

lemma TensorProduct.sum_tmul_basis_left_eq_zero'
    (B : Type*) [Ring B] [Algebra K B]
    (C : Type*) [Ring C] [Algebra K C]
    {ιB : Type*} (ℬ : Basis ιB K B)
    (s : Finset ιB) (c : ιB → C)
    (h : ∑ i ∈ s, ℬ i ⊗ₜ[K] c i = 0) :
    ∀ i ∈ s, c i = 0 := by
  apply TensorProduct.sum_tmul_basis_right_eq_zero' K C B ℬ s c
  apply_fun TensorProduct.comm K B C at h
  simpa using h

lemma TensorProduct.map_comap_eq_of_isSimple_isCentralSimple
    {A B : Type v} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [isSimple_A : IsSimpleRing A]
    [isCentral_B : Algebra.IsCentral K B]
    [isSimple_B : IsSimpleRing B]
    (I : TwoSidedIdeal (A ⊗[K] B)) :
    I = TwoSidedIdeal.span
      (Set.image (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B) (
        I.comap (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B))) := by
  classical
  refine le_antisymm ?_ ?_
  · if I_ne_bot : I = ⊥
    then subst I_ne_bot; exact bot_le
    else

    let f : A →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeLeft
    change I ≤ TwoSidedIdeal.span (Set.image f <| I.comap f)
    let 𝒜 := Basis.ofVectorSpace K A
    obtain ⟨n, x, ⟨x_mem, x_ne_zero, ⟨s, card_s, b, rfl⟩⟩, H⟩ :=
      is_obtainable_by_sum_tmul.exists_minimal_element _ 𝒜 I I_ne_bot

    have b_ne_zero : ∀ i ∈ s, b i ≠ 0 := by
      by_contra! h
      rcases h with ⟨i, h1, h2⟩

      specialize H (n - 1) (∑ i ∈ s, 𝒜 i ⊗ₜ[K] b i) ⟨x_mem, x_ne_zero, ⟨s.erase i,
        by rw [Finset.card_erase_of_mem, card_s]; exact h1, b, by
        symm
        fapply Finset.sum_subset
        · exact Finset.erase_subset i s
        · intro x hx1 hx2
          simp only [Finset.mem_erase, ne_eq, not_and] at hx2
          rw [show x = i by tauto, h2, TensorProduct.tmul_zero]⟩⟩
      have ineq1 : 0 < n := by
        rw [← card_s, Finset.card_pos]
        exact ⟨i, h1⟩
      omega

    if s_ne_empty : s = ∅
    then
      subst s_ne_empty
      simp only [Finset.card_empty, Finset.sum_empty, ne_eq, not_true_eq_false] at *
    else
      obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr s_ne_empty

      have ineq1 : 0 < n := by
        rw [← card_s, Finset.card_pos]
        exact ⟨i₀, hi₀⟩

      have x_eq' :
          ∑ i ∈ s, 𝒜 i ⊗ₜ[K] b i =
          𝒜 i₀ ⊗ₜ[K] b i₀ +
          ∑ i ∈ s.erase i₀, 𝒜 i ⊗ₜ[K] b i := by
        rw [show 𝒜 i₀ ⊗ₜ[K] b i₀ = ∑ i ∈ {i₀}, 𝒜 i ⊗ₜ[K] b i by rw [Finset.sum_singleton],
          ← Finset.sum_disjUnion]
        pick_goal 2
        · rw [← Finset.disjoint_erase_comm]
          simp only [Finset.erase_singleton, Finset.image_empty, Finset.disjoint_empty_left]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext x
        simp only [Finset.disjUnion_eq_union, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_erase, ne_eq]
        constructor
        · intro hx
          if hx' : x = i₀ then left; exact hx'
          else right; exact ⟨hx', hx⟩
        · rintro (rfl|⟨_, hx2⟩) <;> assumption


      have span_bi₀ : TwoSidedIdeal.span {b i₀} = ⊤ := isSimple_B.1.2 _ |>.resolve_left fun r => by
        have mem : b i₀ ∈ (⊥ : TwoSidedIdeal B) := by
          rw [← r]
          apply TwoSidedIdeal.subset_span
          simp only [Set.mem_singleton_iff]
        exact b_ne_zero i₀ hi₀ mem

      have one_mem : (1 : B) ∈ TwoSidedIdeal.span {b i₀} := by rw [span_bi₀]; trivial
      rw [TwoSidedIdeal.mem_span_iff_exists_fin] at one_mem
      obtain ⟨ℐ, inst1, xL, xR, y, one_eq⟩ := one_mem

      replace one_eq : 1 = ∑ i : ℐ, xL i * b i₀ * xR i := by
        rw [one_eq]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr
        simpa only [Set.mem_singleton_iff] using (y i).2

      let ω := ∑ i ∈ s, 𝒜 i ⊗ₜ[K] b i
      let Ω := ∑ i : ℐ, (1 ⊗ₜ[K] xL i) * ω * (1 ⊗ₜ[K] xR i)
      have Ω_in_I : Ω ∈ I := TwoSidedIdeal.finsetSum_mem _ _ _ fun i _ => I.mul_mem_right _ _ <|
        I.mul_mem_left _ _ x_mem

      have Ω_eq :
          Ω =
          𝒜 i₀ ⊗ₜ[K] (∑ i : ℐ, xL i * b i₀ * xR i) +
          ∑ i ∈ s.erase i₀, 𝒜 i ⊗ₜ[K] (∑ j : ℐ, xL j * b i * xR j) := by
        dsimp only [Ω, ω]
        simp only [x_eq', mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Finset.mul_sum,
          add_mul, mul_one, Finset.sum_mul, Finset.sum_add_distrib, TensorProduct.tmul_sum,
          add_right_inj]
        rw [Finset.sum_comm]
      rw [← one_eq] at Ω_eq

      have Ω_prop_1 (b : B) : (1 ⊗ₜ b) * Ω - Ω * (1 ⊗ₜ b) ∈ I :=
        I.sub_mem (I.mul_mem_left _ _ Ω_in_I) (I.mul_mem_right _ _ Ω_in_I)

      have Ω_prop_2 (x : B) : ((1 : A) ⊗ₜ[K] x) * Ω - Ω * ((1 : A) ⊗ₜ[K] x) =
          ∑ i ∈ s.erase i₀, 𝒜 i ⊗ₜ[K]
            (∑ j : ℐ, (x * (xL j * b i * xR j) - (xL j * b i * xR j) * x)) := by
        rw [Ω_eq]
        simp only [TensorProduct.tmul_sum, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one, Finset.mul_sum, add_mul, Finset.sum_mul, add_sub_add_left_eq_sub,
          Finset.sum_sub_distrib, TensorProduct.tmul_sub]

      have Ω_prop_3 (x : B) : ((1 : A) ⊗ₜ[K] x) * Ω - Ω * ((1 : A) ⊗ₜ[K] x) = 0 := by
        by_contra rid
        specialize H (n - 1) (((1 : A) ⊗ₜ[K] x) * Ω - Ω * ((1 : A) ⊗ₜ[K] x))
          ⟨Ω_prop_1 x, rid, ⟨s.erase i₀, by rw [Finset.card_erase_of_mem, card_s]; exact hi₀, _,
            Ω_prop_2 x⟩⟩
        omega

      simp_rw [Ω_prop_2] at Ω_prop_3
      have Ω_prop_4 : ∀ i ∈ s.erase i₀,
          ∑ j : ℐ, (xL j * b i * xR j) ∈ Subalgebra.center K B := by
        intro i hi
        rw [Subalgebra.mem_center_iff]
        intro x
        specialize Ω_prop_3 x
        simp only [Finset.mul_sum, Finset.sum_mul, ← sub_eq_zero, sub_zero]
        rw [← Finset.sum_sub_distrib, sub_zero]
        simpa using TensorProduct.sum_tmul_basis_left_eq_zero' _ _ _ 𝒜 (s.erase i₀) _ Ω_prop_3 i hi

      simp_rw [Algebra.IsCentral.center_eq_bot, Algebra.mem_bot, Set.mem_range] at Ω_prop_4
      choose k hk using Ω_prop_4
      have Ω_eq2 := calc Ω
        _ = 𝒜 i₀ ⊗ₜ[K] 1 + ∑ i ∈ s.erase i₀, 𝒜 i ⊗ₜ[K] ∑ j : ℐ, xL j * b i * xR j := Ω_eq
        _ = 𝒜 i₀ ⊗ₜ[K] 1 + ∑ i ∈ (s.erase i₀).attach, 𝒜 i ⊗ₜ[K] ∑ j : ℐ, xL j * b i * xR j := by
            congr 1
            exact Finset.sum_attach _ _ |>.symm
        _ = 𝒜 i₀ ⊗ₜ[K] 1 + ∑ i ∈ (s.erase i₀).attach, 𝒜 i ⊗ₜ[K] algebraMap _ _ (k i.1 i.2) := by
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hk i.1 i.2]
        _ = 𝒜 i₀ ⊗ₜ[K] 1 +  ∑ i ∈ (s.erase i₀).attach, 𝒜 i ⊗ₜ[K] (k i.1 i.2 • (1 : B) : B) := by
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Algebra.algebraMap_eq_smul_one]
        _ = 𝒜 i₀ ⊗ₜ[K] 1 + ∑ i ∈ (s.erase i₀).attach, (k i.1 i.2 • 𝒜 i) ⊗ₜ[K] (1 : B) := by
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [TensorProduct.smul_tmul]
        _ = 𝒜 i₀ ⊗ₜ[K] 1 + (∑ i ∈ (s.erase i₀).attach, (k i.1 i.2 • 𝒜 i)) ⊗ₜ[K] (1 : B) := by
            rw [TensorProduct.sum_tmul]
        _ = (𝒜 i₀ + (∑ i ∈ (s.erase i₀).attach, (k i.1 i.2 • 𝒜 i))) ⊗ₜ[K] 1 := by
            rw [TensorProduct.add_tmul]

      rw [Ω_eq2] at Ω_in_I
      have hI : I.comap f = ⊤ := isSimple_A.1.2 _ |>.resolve_left fun r => by
        have mem : 𝒜 i₀ + (∑ i ∈ (s.erase i₀).attach, (k i.1 i.2 • 𝒜 i)) ∈ I.comap f := by
          rw [TwoSidedIdeal.mem_comap]
          exact Ω_in_I
        rw [r] at mem
        change _ = 0 at mem
        rw [mem, TensorProduct.zero_tmul] at Ω_eq2
        have LI := 𝒜.linearIndependent
        rw [linearIndependent_iff'] at LI
        specialize LI s (fun i =>
          if i = i₀ then 1
          else if h : i ∈ s.erase i₀ then k i h else 0) (by
          dsimp only
          simp_rw [ite_smul, one_smul, dite_smul, zero_smul]
          rw [Finset.sum_ite,
            show ∑ x ∈ Finset.filter (fun x ↦ x = i₀) s, 𝒜 x = ∑ x ∈ {i₀}, 𝒜 x by
            refine Finset.sum_congr ?_ fun _ _ => rfl
            ext
            simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_right_iff_imp]
            rintro rfl
            exact hi₀, Finset.sum_singleton,
            show Finset.filter (fun x ↦ ¬x = i₀) s = s.erase i₀ by
            ext
            simp only [Finset.mem_filter, Finset.mem_erase, ne_eq]
            rw [and_comm], ← Finset.sum_attach]
          conv_rhs => rw [← mem]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [dif_pos i.2]) i₀ hi₀
        rw [if_pos rfl] at LI
        exact zero_ne_one LI.symm
      rw [hI, TwoSidedIdeal.coe_top_set, TwoSidedIdeal.le_iff]
      rintro x -
      rw [SetLike.mem_coe]
      induction x using TensorProduct.induction_on with
      | zero => simp [TwoSidedIdeal.zero_mem]
      | tmul a b =>
        rw [show a ⊗ₜ[K] b = (a ⊗ₜ 1) * (1 ⊗ₜ b) by simp]
        exact TwoSidedIdeal.mul_mem_right _ _ _ <| TwoSidedIdeal.subset_span ⟨a, ⟨⟩, rfl⟩
      | add x y hx hy => exact TwoSidedIdeal.add_mem _ hx hy

  · rw [← TwoSidedIdeal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap] at hx
    exact hx

instance TensorProduct.simple
    (A B : Type v) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [isSimple_A : IsSimpleRing A]
    [isCentral_B : Algebra.IsCentral K B]
    [isSimple_B : IsSimpleRing B] :
    IsSimpleRing (A ⊗[K] B) := by
  let f : A →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeLeft
  suffices eq1 : ∀ (I : TwoSidedIdeal (A ⊗[K] B)),
      I = TwoSidedIdeal.span (Set.image f <| I.comap f) by
    refine ⟨⟨fun I => ?_⟩⟩
    specialize eq1 I
    rcases isSimple_A.1.2 (I.comap f) with h|h
    · left
      rw [h, TwoSidedIdeal.coe_bot_set, Set.image_singleton, map_zero] at eq1
      rw [eq1, eq_bot_iff, TwoSidedIdeal.le_iff]
      rintro x hx
      rw [SetLike.mem_coe, TwoSidedIdeal.mem_span_iff_exists_fin] at hx
      obtain ⟨ι, inst, xL, xR, y, rfl⟩ := hx
      rw [SetLike.mem_coe]
      refine TwoSidedIdeal.finsetSum_mem _ _ _ fun i _ => ?_
      have := (y i).2
      simp only [Set.mem_singleton_iff] at this
      rw [this, mul_zero, zero_mul]
      rfl
    · right
      rw [h, TwoSidedIdeal.coe_top_set] at eq1
      rw [eq1, eq_top_iff, TwoSidedIdeal.le_iff]
      rintro x -
      rw [SetLike.mem_coe]
      induction x using TensorProduct.induction_on with
      | zero => simp [TwoSidedIdeal.zero_mem]
      | tmul a b =>
        rw [show a ⊗ₜ[K] b = (a ⊗ₜ 1) * (1 ⊗ₜ b) by simp]
        exact TwoSidedIdeal.mul_mem_right _ _ _ <| TwoSidedIdeal.subset_span ⟨a, ⟨⟩, rfl⟩
      | add x y hx hy => exact TwoSidedIdeal.add_mem _ hx hy

  apply TensorProduct.map_comap_eq_of_isSimple_isCentralSimple
