/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Anne Baanen
-/
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.LinearAlgebra.Finsupp.SumProd
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# Linear independence

This file collects consequences of linear (in)dependence and includes specialized tests for
specific families of vectors, requiring more theory to state.

## Main statements

We prove several specialized tests for linear independence of families of vectors and of sets of
vectors.

* `linearIndependent_option`, `linearIndependent_fin_cons`,
  `linearIndependent_fin_succ`: type-specific tests for linear independence of families of vector
  fields;
* `linearIndependent_insert`, `linearIndependent_pair`: linear independence tests for set operations

In many cases we additionally provide dot-style operations (e.g., `LinearIndependent.union`) to
make the linear independence tests usable as `hv.insert ha` etc.

We also prove that, when working over a division ring,
any family of vectors includes a linear independent subfamily spanning the same subspace.

## TODO

Rework proofs to hold in semirings, by avoiding the path through
`ker (Finsupp.linearCombination R v) = ⊥`.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/


assert_not_exists Cardinal

noncomputable section

open Function Set Submodule

universe u' u

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*} {s : Set ι}
variable {M : Type*} {M' : Type*} {V : Type u}

section Semiring


variable {v : ι → M}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R M']
variable (R) (v)

variable {R v}

/-- A finite family of vectors `v i` is linear independent iff the linear map that sends
`c : ι → R` to `∑ i, c i • v i` is injective. -/
theorem Fintype.linearIndependent_iff'ₛ [Fintype ι] [DecidableEq ι] :
    LinearIndependent R v ↔
      Injective (LinearMap.lsum R (fun _ ↦ R) ℕ fun i ↦ LinearMap.id.smulRight (v i)) := by
  simp [Fintype.linearIndependent_iffₛ, Injective, funext_iff]

lemma LinearIndependent.pair_iffₛ {x y : M} :
    LinearIndependent R ![x, y] ↔
      ∀ (s t s' t' : R), s • x + t • y = s' • x + t' • y → s = s' ∧ t = t' := by
  simp [Fintype.linearIndependent_iffₛ, Fin.forall_fin_two, ← FinVec.forall_iff]; rfl

lemma LinearIndependent.eq_of_pair {x y : M} (h : LinearIndependent R ![x, y])
    {s t s' t' : R} (h' : s • x + t • y = s' • x + t' • y) : s = s' ∧ t = t' :=
  pair_iffₛ.mp h _ _ _ _ h'

lemma LinearIndependent.eq_zero_of_pair' {x y : M} (h : LinearIndependent R ![x, y])
    {s t : R} (h' : s • x = t • y) : s = 0 ∧ t = 0 := by
  suffices H : s = 0 ∧ 0 = t from ⟨H.1, H.2.symm⟩
  exact h.eq_of_pair (by simpa using h')

lemma LinearIndependent.eq_zero_of_pair {x y : M} (h : LinearIndependent R ![x, y])
    {s t : R} (h' : s • x + t • y = 0) : s = 0 ∧ t = 0 := by
  replace h := @h (.single 0 s + .single 1 t) 0 ?_
  · exact ⟨by simpa using congr($h 0), by simpa using congr($h 1)⟩
  simpa

section Indexed

theorem linearIndepOn_iUnion_of_directed {η : Type*} {s : η → Set ι} (hs : Directed (· ⊆ ·) s)
    (h : ∀ i, LinearIndepOn R v (s i)) : LinearIndepOn R v (⋃ i, s i) := by
  by_cases hη : Nonempty η
  · refine linearIndepOn_of_finite (⋃ i, s i) fun t ht ft => ?_
    rcases finite_subset_iUnion ft ht with ⟨I, fi, hI⟩
    rcases hs.finset_le fi.toFinset with ⟨i, hi⟩
    exact (h i).mono (Subset.trans hI <| iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))
  · refine (linearIndepOn_empty R v).mono (t := iUnion (s ·)) ?_
    rintro _ ⟨_, ⟨i, _⟩, _⟩
    exact hη ⟨i⟩

theorem linearIndepOn_sUnion_of_directed {s : Set (Set ι)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ a ∈ s, LinearIndepOn R v a) : LinearIndepOn R v (⋃₀ s) := by
  rw [sUnion_eq_iUnion]
  exact linearIndepOn_iUnion_of_directed hs.directed_val (by simpa using h)

theorem linearIndepOn_biUnion_of_directed {η} {s : Set η} {t : η → Set ι}
    (hs : DirectedOn (t ⁻¹'o (· ⊆ ·)) s) (h : ∀ a ∈ s, LinearIndepOn R v (t a)) :
    LinearIndepOn R v (⋃ a ∈ s, t a) := by
  rw [biUnion_eq_iUnion]
  exact linearIndepOn_iUnion_of_directed (directed_comp.2 <| hs.directed_val) (by simpa using h)

end Indexed

section repr

variable (hv : LinearIndependent R v)

/-- See also `iSupIndep_iff_linearIndependent_of_ne_zero`. -/
theorem LinearIndependent.iSupIndep_span_singleton (hv : LinearIndependent R v) :
    iSupIndep fun i => R ∙ v i := by
  refine iSupIndep_def.mp fun i => ?_
  rw [disjoint_iff_inf_le]
  intro m hm
  simp only [mem_inf, mem_span_singleton, iSup_subtype'] at hm
  rw [← span_range_eq_iSup] at hm
  obtain ⟨⟨r, rfl⟩, hm⟩ := hm
  suffices r = 0 by simp [this]
  apply hv.eq_zero_of_smul_mem_span i
  convert hm
  ext
  simp

end repr

section union

open LinearMap Finsupp

theorem linearIndependent_inl_union_inr' {v : ι → M} {v' : ι' → M'}
    (hv : LinearIndependent R v) (hv' : LinearIndependent R v') :
    LinearIndependent R (Sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) := by
  have : linearCombination R (Sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) =
      .prodMap (linearCombination R v) (linearCombination R v') ∘ₗ
      (sumFinsuppLEquivProdFinsupp R).toLinearMap := by
    ext (_ | _) <;> simp [linearCombination_comapDomain]
  rw [LinearIndependent, this]
  simpa [LinearMap.coe_prodMap] using ⟨hv, hv'⟩

theorem LinearIndependent.inl_union_inr {s : Set M} {t : Set M'}
    (hs : LinearIndependent R (fun x => x : s → M))
    (ht : LinearIndependent R (fun x => x : t → M')) :
    LinearIndependent R (fun x => x : ↥(inl R M M' '' s ∪ inr R M M' '' t) → M × M') := by
  nontriviality R
  let e : s ⊕ t ≃ ↥(inl R M M' '' s ∪ inr R M M' '' t) :=
    .ofBijective (Sum.elim (fun i ↦ ⟨_, .inl ⟨_, i.2, rfl⟩⟩) fun i ↦ ⟨_, .inr ⟨_, i.2, rfl⟩⟩)
      ⟨by rintro (_ | _) (_ | _) eq <;> simp [hs.ne_zero, ht.ne_zero] at eq <;> aesop,
        by rintro ⟨_, ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩⟩ <;> aesop⟩
  refine (linearIndependent_equiv' e ?_).mp (linearIndependent_inl_union_inr' hs ht)
  ext (_ | _) <;> rfl

end union

section Maximal

universe v w

variable (R)

/-- TODO : refactor to use `Maximal`. -/
theorem exists_maximal_linearIndepOn' (v : ι → M) :
    ∃ s : Set ι, (LinearIndepOn R v s) ∧ ∀ t : Set ι, s ⊆ t → (LinearIndepOn R v t) → s = t := by
  let indep : Set ι → Prop := fun s => LinearIndepOn R v s
  let X := { I : Set ι // indep I }
  let r : X → X → Prop := fun I J => I.1 ⊆ J.1
  have key : ∀ c : Set X, IsChain r c → indep (⋃ (I : X) (_ : I ∈ c), I) := by
    intro c hc
    dsimp [indep]
    rw [linearIndepOn_iffₛ]
    intro f hfsupp g hgsupp hsum
    rcases eq_empty_or_nonempty c with (rfl | hn)
    · rw [show f = 0 by simpa using hfsupp, show g = 0 by simpa using hgsupp]
    haveI : IsRefl X r := ⟨fun _ => Set.Subset.refl _⟩
    classical
    obtain ⟨I, _I_mem, hI⟩ : ∃ I ∈ c, (f.support ∪ g.support : Set ι) ⊆ I :=
      f.support.coe_union _ ▸ hc.directedOn.exists_mem_subset_of_finset_subset_biUnion hn <| by
        simpa using And.intro hfsupp hgsupp
    exact linearIndepOn_iffₛ.mp I.2 f (subset_union_left.trans hI)
      g (subset_union_right.trans hI) hsum
  have trans : Transitive r := fun I J K => Set.Subset.trans
  obtain ⟨⟨I, hli : indep I⟩, hmax : ∀ a, r ⟨I, hli⟩ a → r a ⟨I, hli⟩⟩ :=
    exists_maximal_of_chains_bounded
      (fun c hc => ⟨⟨⋃ I ∈ c, (I : Set ι), key c hc⟩, fun I => Set.subset_biUnion_of_mem⟩) @trans
  exact ⟨I, hli, fun J hsub hli => Set.Subset.antisymm hsub (hmax ⟨J, hli⟩ hsub)⟩

end Maximal

end Semiring

section Module

variable {v : ι → M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

/-- A finite family of vectors `v i` is linear independent iff the linear map that sends
`c : ι → R` to `∑ i, c i • v i` has the trivial kernel. -/
theorem Fintype.linearIndependent_iff' [Fintype ι] [DecidableEq ι] :
    LinearIndependent R v ↔
      LinearMap.ker (LinearMap.lsum R (fun _ ↦ R) ℕ fun i ↦ LinearMap.id.smulRight (v i)) = ⊥ := by
  simp [Fintype.linearIndependent_iff, LinearMap.ker_eq_bot', funext_iff]

/-- `linearIndepOn_pair_iff` is a simpler version over fields. -/
lemma LinearIndepOn.pair_iff {i j : ι} (f : ι → M) (hij : i ≠ j) :
    LinearIndepOn R f {i,j} ↔ ∀ c d : R, c • f i + d • f j = 0 → c = 0 ∧ d = 0 := by
  classical
  rw [linearIndepOn_iff'']
  refine ⟨fun h c d hcd ↦ ?_, fun h t g ht hg0 h0 ↦ ?_⟩
  · specialize h {i, j} (Pi.single i c + Pi.single j d)
    simpa +contextual [Finset.sum_pair, Pi.single_apply, hij, hij.symm, hcd] using h
  have ht' : t ⊆ {i, j} := by simpa [← Finset.coe_subset]
  rw [Finset.sum_subset ht', Finset.sum_pair hij] at h0
  · obtain ⟨hi0, hj0⟩ := h _ _ h0
    exact fun k hkt ↦ Or.elim (ht hkt) (fun h ↦ h ▸ hi0) (fun h ↦ h ▸ hj0)
  simp +contextual [hg0]

section Pair

variable {x y : M}

/-- Also see `LinearIndependent.pair_iff'` for a simpler version over fields. -/
lemma LinearIndependent.pair_iff :
    LinearIndependent R ![x, y] ↔ ∀ (s t : R), s • x + t • y = 0 → s = 0 ∧ t = 0 := by
  rw [← linearIndepOn_univ, ← Finset.coe_univ, show @Finset.univ (Fin 2) _ = {0,1} from rfl,
    Finset.coe_insert, Finset.coe_singleton, LinearIndepOn.pair_iff _ (by trivial)]
  simp

lemma LinearIndependent.pair_symm_iff :
    LinearIndependent R ![x, y] ↔ LinearIndependent R ![y, x] := by
  suffices ∀ x y : M, LinearIndependent R ![x, y] → LinearIndependent R ![y, x] by tauto
  simp only [LinearIndependent.pair_iff]
  intro x y h s t
  specialize h t s
  rwa [add_comm, and_comm]

@[simp] lemma LinearIndependent.pair_neg_left_iff :
    LinearIndependent R ![-x, y] ↔ LinearIndependent R ![x, y] := by
  rw [pair_iff, pair_iff]
  refine ⟨fun h s t hst ↦ ?_, fun h s t hst ↦ ?_⟩ <;> simpa using h (-s) t (by simpa using hst)

@[simp] lemma LinearIndependent.pair_neg_right_iff :
    LinearIndependent R ![x, -y] ↔ LinearIndependent R ![x, y] := by
  rw [pair_symm_iff, pair_neg_left_iff, pair_symm_iff]

variable {S : Type*} [CommRing S] [Module S R] [Module S M]
  [SMulCommClass S R M] [IsScalarTower S R M] [NoZeroSMulDivisors S R]
  (a b c d : S)

lemma LinearIndependent.pair_smul_iff {u : S} (hu : u ≠ 0) :
    LinearIndependent R ![u • x, u • y] ↔ LinearIndependent R ![x, y] := by
  simp only [LinearIndependent.pair_iff]
  refine ⟨fun h s t hst ↦ ?_, fun h s t hst ↦ ?_⟩
  · exact h s t (by rw [← smul_comm u s, ← smul_comm u t, ← smul_add, hst, smul_zero])
  · specialize h (u • s) (u • t) (by rw [smul_assoc, smul_assoc, smul_comm u s, smul_comm u t, hst])
    exact ⟨(smul_eq_zero_iff_right hu).mp h.1, (smul_eq_zero_iff_right hu).mp h.2⟩

private lemma LinearIndependent.pair_add_smul_add_smul_iff_aux (h : a * d ≠ b * c)
    (h' : LinearIndependent R ![x, y]) :
    LinearIndependent R ![a • x + b • y, c • x + d • y] := by
  simp only [LinearIndependent.pair_iff] at h' ⊢
  intro s t hst
  specialize h' (a • s + c • t) (b • s + d • t) (by simp only [← hst, smul_add, add_smul,
    smul_assoc, smul_comm a s, smul_comm c t, smul_comm b s, smul_comm d t]; abel)
  obtain ⟨h₁, h₂⟩ := h'
  constructor
  · suffices (a * d) • s = (b * c) • s by
      by_contra hs; exact h (_root_.smul_left_injective S hs ‹_›)
    calc (a * d) • s
        = d • a • s := by rw [mul_comm, mul_smul]
      _ = - (d • c • t) := by rw [eq_neg_iff_add_eq_zero, ← smul_add, h₁, smul_zero]
      _ = (b * c) • s := ?_
    · rw [mul_comm, mul_smul, neg_eq_iff_add_eq_zero, add_comm, smul_comm d c, ← smul_add, h₂,
        smul_zero]
  · suffices (a * d) • t = (b * c) • t by
      by_contra ht; exact h (_root_.smul_left_injective S ht ‹_›)
    calc (a * d) • t
        = a • d • t := by rw [mul_smul]
      _ = - (a • b • s) := by rw [eq_neg_iff_add_eq_zero, ← smul_add, add_comm, h₂, smul_zero]
      _ = (b * c) • t := ?_
    · rw [mul_smul, neg_eq_iff_add_eq_zero, smul_comm a b, ← smul_add, h₁, smul_zero]

@[simp] lemma LinearIndependent.pair_add_smul_add_smul_iff [Nontrivial R] :
    LinearIndependent R ![a • x + b • y, c • x + d • y] ↔
      LinearIndependent R ![x, y] ∧ a * d ≠ b * c := by
  rcases eq_or_ne (a * d) (b * c) with h | h
  · suffices ¬ LinearIndependent R ![a • x + b • y, c • x + d • y] by simpa [h]
    rw [pair_iff]
    push_neg
    by_cases hbd : b = 0 ∧ d = 0
    · simp only [hbd.1, hbd.2, zero_smul, add_zero]
      by_cases hac : a = 0 ∧ c = 0; · exact ⟨1, 0, by simp [hac.1, hac.2], by simp⟩
      refine ⟨c • 1, -a • 1, ?_, by aesop⟩
      simp only [smul_assoc, one_smul, neg_smul]
      module
    refine ⟨d • 1, -b • 1, ?_, by contrapose! hbd; simp_all⟩
    simp only [smul_add, smul_assoc, one_smul, smul_smul, mul_comm d, h]
    module
  refine ⟨fun h' ↦ ⟨?_, h⟩, fun ⟨h₁, h₂⟩ ↦ pair_add_smul_add_smul_iff_aux _ _ _ _ h₂ h₁⟩
  suffices LinearIndependent R ![(a * d - b * c) • x, (a * d - b * c) • y] by
    rwa [pair_smul_iff (sub_ne_zero_of_ne h)] at this
  convert pair_add_smul_add_smul_iff_aux d (-b) (-c) a (by simpa [mul_comm d a]) h' using 1
  ext i; fin_cases i <;> simp <;> module

@[deprecated (since := "2025-04-15")]
alias LinearIndependent.linear_combination_pair_of_det_ne_zero :=
  LinearIndependent.pair_add_smul_add_smul_iff

@[simp] lemma LinearIndependent.pair_add_smul_right_iff :
    LinearIndependent R ![x, c • x + y] ↔ LinearIndependent R ![x, y] := by
  rcases subsingleton_or_nontrivial S with hS | hS; · simp [hS.elim c 0]
  nontriviality R
  simpa using pair_add_smul_add_smul_iff (x := x) (y := y) 1 0 c 1

@[simp] lemma LinearIndependent.pair_add_smul_left_iff :
    LinearIndependent R ![x + b • y, y] ↔ LinearIndependent R ![x, y] := by
  rcases subsingleton_or_nontrivial S with hS | hS; · simp [hS.elim b 0]
  nontriviality R
  simpa using pair_add_smul_add_smul_iff (x := x) (y := y) 1 b 0 1

@[simp] lemma LinearIndependent.pair_add_right_iff :
    LinearIndependent R ![x, x + y] ↔ LinearIndependent R ![x, y] := by
  suffices ∀ x y : M, LinearIndependent R ![x, x + y] → LinearIndependent R ![x, y] from
    ⟨this x y, fun h ↦ by simpa using this (-x) (x + y) (by simpa)⟩
  simp only [LinearIndependent.pair_iff]
  intro x y h s t h'
  obtain ⟨h₁, h₂⟩ := h (s - t) t (by rw [sub_smul, smul_add, ← h']; abel)
  rw [h₂, sub_zero] at h₁
  tauto

@[simp] lemma LinearIndependent.pair_add_left_iff :
    LinearIndependent R ![x + y, y] ↔ LinearIndependent R ![x, y] := by
  rw [← pair_symm_iff, add_comm, pair_add_right_iff, pair_symm_iff]

end Pair

end Module

/-! ### Properties which require `Ring R` -/


section Module

variable {v : ι → M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

theorem linearIndepOn_id_iUnion_finite {f : ι → Set M} (hl : ∀ i, LinearIndepOn R id (f i))
    (hd : ∀ i, ∀ t : Set ι, t.Finite → i ∉ t → Disjoint (span R (f i)) (⨆ i ∈ t, span R (f i))) :
    LinearIndepOn R id (⋃ i, f i) := by
  classical
  rw [iUnion_eq_iUnion_finset f]
  apply linearIndepOn_iUnion_of_directed
  · apply directed_of_isDirected_le
    exact fun t₁ t₂ ht => iUnion_mono fun i => iUnion_subset_iUnion_const fun h => ht h
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    rw [Finset.set_biUnion_insert]
    refine (hl _).id_union ih ?_
    rw [span_iUnion₂]
    exact hd i s s.finite_toSet his

theorem linearIndependent_iUnion_finite {η : Type*} {ιs : η → Type*} {f : ∀ j : η, ιs j → M}
    (hindep : ∀ j, LinearIndependent R (f j))
    (hd : ∀ i, ∀ t : Set η,
      t.Finite → i ∉ t → Disjoint (span R (range (f i))) (⨆ i ∈ t, span R (range (f i)))) :
    LinearIndependent R fun ji : Σ j, ιs j => f ji.1 ji.2 := by
  nontriviality R
  apply LinearIndependent.of_linearIndepOn_id_range
  · rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hxy
    by_cases h_cases : x₁ = y₁
    · subst h_cases
      refine Sigma.eq rfl ?_
      rw [LinearIndependent.injective (hindep _) hxy]
    · have h0 : f x₁ x₂ = 0 := by
        apply
          disjoint_def.1 (hd x₁ {y₁} (finite_singleton y₁) fun h => h_cases (eq_of_mem_singleton h))
            (f x₁ x₂) (subset_span (mem_range_self _))
        rw [iSup_singleton]
        simp only at hxy
        rw [hxy]
        exact subset_span (mem_range_self y₂)
      exact False.elim ((hindep x₁).ne_zero _ h0)
  rw [range_sigma_eq_iUnion_range]
  apply linearIndepOn_id_iUnion_finite (fun j => (hindep j).linearIndepOn_id) hd

open LinearMap

variable (R) in
theorem exists_maximal_linearIndepOn (v : ι → M) :
    ∃ s : Set ι, (LinearIndepOn R v s) ∧ ∀ i ∉ s, ∃ a : R, a ≠ 0 ∧ a • v i ∈ span R (v '' s) := by
  classical
    rcases exists_maximal_linearIndepOn' R v with ⟨I, hIlinind, hImaximal⟩
    use I, hIlinind
    intro i hi
    specialize hImaximal (I ∪ {i}) (by simp)
    set J := I ∪ {i} with hJ
    have memJ : ∀ {x}, x ∈ J ↔ x = i ∨ x ∈ I := by simp [hJ]
    have hiJ : i ∈ J := by simp [J]
    have h := by
      refine mt hImaximal ?_
      · intro h2
        rw [h2] at hi
        exact absurd hiJ hi
    obtain ⟨f, supp_f, sum_f, f_ne⟩ := linearDepOn_iff.mp h
    have hfi : f i ≠ 0 := by
      contrapose hIlinind
      refine linearDepOn_iff.mpr ⟨f, ?_, sum_f, f_ne⟩
      simp only [Finsupp.mem_supported, hJ] at supp_f ⊢
      rintro x hx
      refine (memJ.mp (supp_f hx)).resolve_left ?_
      rintro rfl
      exact hIlinind (Finsupp.mem_support_iff.mp hx)
    use f i, hfi
    have hfi' : i ∈ f.support := Finsupp.mem_support_iff.mpr hfi
    rw [← Finset.insert_erase hfi', Finset.sum_insert (Finset.notMem_erase _ _),
      add_eq_zero_iff_eq_neg] at sum_f
    rw [sum_f]
    refine neg_mem (sum_mem fun c hc => smul_mem _ _ (subset_span ⟨c, ?_, rfl⟩))
    exact (memJ.mp (supp_f (Finset.erase_subset _ _ hc))).resolve_left (Finset.ne_of_mem_erase hc)

@[stacks 0CKM]
lemma linearIndependent_algHom_toLinearMap
    (K M L) [CommSemiring K] [Semiring M] [Algebra K M] [CommRing L] [IsDomain L] [Algebra K L] :
    LinearIndependent L (AlgHom.toLinearMap : (M →ₐ[K] L) → M →ₗ[K] L) := by
  apply LinearIndependent.of_comp (LinearMap.ltoFun K M L)
  exact (linearIndependent_monoidHom M L).comp
    (RingHom.toMonoidHom ∘ AlgHom.toRingHom)
    (fun _ _ e ↦ AlgHom.ext (DFunLike.congr_fun e :))

lemma linearIndependent_algHom_toLinearMap' (K M L) [CommRing K]
    [Semiring M] [Algebra K M] [CommRing L] [IsDomain L] [Algebra K L] [NoZeroSMulDivisors K L] :
    LinearIndependent K (AlgHom.toLinearMap : (M →ₐ[K] L) → M →ₗ[K] L) :=
  (linearIndependent_algHom_toLinearMap K M L).restrict_scalars' K

lemma LinearMap.injective_of_linearIndependent {N : Type*} [AddCommGroup N] [Module R N]
    {f : M →ₗ[R] N} {ι : Type*} {v : ι → M}
    (hv : Submodule.span R (.range v) = ⊤) (hli : LinearIndependent R (f ∘ v)) :
    Function.Injective f := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  have : x ∈ Submodule.span R (.range v) := by rw [hv]; exact mem_top
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp this
  simp only [map_finsuppSum, map_smul] at hx
  obtain rfl := linearIndependent_iff.mp hli c hx
  simp

lemma LinearMap.bijective_of_linearIndependent_of_span_eq_top {N : Type*} [AddCommGroup N]
    [Module R N] {f : M →ₗ[R] N} {ι : Type*} {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤)
    (hli : LinearIndependent R (f ∘ v)) (hsp : Submodule.span R (Set.range <| f ∘ v) = ⊤) :
    Function.Bijective f := by
  refine ⟨LinearMap.injective_of_linearIndependent hv hli, ?_⟩
  rw [Set.range_comp, ← Submodule.map_span, hv, Submodule.map_top] at hsp
  rwa [← range_eq_top]

end Module

/-!
### Properties which require `DivisionRing K`

These can be considered generalizations of properties of linear independence in vector spaces.
-/


section Module

variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable {v : ι → V} {s t : Set V} {x y : V}

open Submodule

/- TODO: some of the following proofs can generalized with a zero_ne_one predicate type class
(instead of a data containing type class) -/
theorem mem_span_insert_exchange :
    x ∈ span K (insert y s) → x ∉ span K s → y ∈ span K (insert x s) := by
  simp only [mem_span_insert, forall_exists_index, and_imp]
  rintro a z hz rfl h
  refine ⟨a⁻¹, -a⁻¹ • z, smul_mem _ _ hz, ?_⟩
  have a0 : a ≠ 0 := by
    rintro rfl
    simp_all
  match_scalars <;> simp [a0]

protected theorem LinearIndepOn.insert {s : Set ι} {x : ι} (hs : LinearIndepOn K v s)
    (hx : v x ∉ span K (v '' s)) : LinearIndepOn K v (insert x s) := by
  rw [← union_singleton]
  have x0 : v x ≠ 0 := fun h => hx (h ▸ zero_mem _)
  apply hs.union (LinearIndepOn.singleton _ x0)
  rwa [image_singleton, disjoint_span_singleton' x0]

protected theorem LinearIndepOn.id_insert (hs : LinearIndepOn K id s) (hx : x ∉ span K s) :
    LinearIndepOn K id (insert x s) :=
  hs.insert ((image_id s).symm ▸ hx)

theorem linearIndependent_option' :
    LinearIndependent K (fun o => Option.casesOn' o x v : Option ι → V) ↔
      LinearIndependent K v ∧ x ∉ Submodule.span K (range v) := by
  -- Porting note: Explicit universe level is required in `Equiv.optionEquivSumPUnit`.
  rw [← linearIndependent_equiv (Equiv.optionEquivSumPUnit.{u'} ι).symm, linearIndependent_sum,
    @range_unique _ PUnit, @linearIndependent_unique_iff PUnit, disjoint_span_singleton]
  dsimp [(· ∘ ·)]
  refine ⟨fun h => ⟨h.1, fun hx => h.2.1 <| h.2.2 hx⟩, fun h => ⟨h.1, ?_, fun hx => (h.2 hx).elim⟩⟩
  rintro rfl
  exact h.2 (zero_mem _)

theorem LinearIndependent.option (hv : LinearIndependent K v)
    (hx : x ∉ Submodule.span K (range v)) :
    LinearIndependent K (fun o => Option.casesOn' o x v : Option ι → V) :=
  linearIndependent_option'.2 ⟨hv, hx⟩

theorem linearIndependent_option {v : Option ι → V} : LinearIndependent K v ↔
    LinearIndependent K (v ∘ (↑) : ι → V) ∧
      v none ∉ Submodule.span K (range (v ∘ (↑) : ι → V)) := by
  simp only [← linearIndependent_option', Option.casesOn'_none_coe]

theorem linearIndepOn_insert {s : Set ι} {a : ι} {f : ι → V} (has : a ∉ s) :
    LinearIndepOn K f (insert a s) ↔ LinearIndepOn K f s ∧ f a ∉ Submodule.span K (f '' s) := by
  classical
  rw [LinearIndepOn, LinearIndepOn, ← linearIndependent_equiv
    ((Equiv.optionEquivSumPUnit _).trans (Equiv.Set.insert has).symm), linearIndependent_option]
  simp only [comp_def]
  rw [range_comp']
  simp

theorem linearIndepOn_id_insert (hxs : x ∉ s) :
    LinearIndepOn K id (insert x s) ↔ LinearIndepOn K id s ∧ x ∉ Submodule.span K s :=
  (linearIndepOn_insert (f := id) hxs).trans <| by simp

theorem linearIndepOn_insert_iff {s : Set ι} {a : ι} {f : ι → V} :
    LinearIndepOn K f (insert a s) ↔ LinearIndepOn K f s ∧ (f a ∈ span K (f '' s) → a ∈ s) := by
  by_cases has : a ∈ s
  · simp [insert_eq_of_mem has, has]
  simp [linearIndepOn_insert has, has]

theorem linearIndepOn_id_insert_iff {a : V} {s : Set V} :
    LinearIndepOn K id (insert a s) ↔ LinearIndepOn K id s ∧ (a ∈ span K s → a ∈ s) := by
  simpa using linearIndepOn_insert_iff (a := a) (f := id)

theorem LinearIndepOn.mem_span_iff {s : Set ι} {a : ι} {f : ι → V} (h : LinearIndepOn K f s) :
    f a ∈ Submodule.span K (f '' s) ↔ (LinearIndepOn K f (insert a s) → a ∈ s) := by
  by_cases has : a ∈ s
  · exact iff_of_true (subset_span <| mem_image_of_mem f has) fun _ ↦ has
  simp [linearIndepOn_insert_iff, h, has]

/-- A shortcut to a convenient form for the negation in `LinearIndepOn.mem_span_iff`. -/
theorem LinearIndepOn.notMem_span_iff {s : Set ι} {a : ι} {f : ι → V} (h : LinearIndepOn K f s) :
    f a ∉ Submodule.span K (f '' s) ↔ LinearIndepOn K f (insert a s) ∧ a ∉ s := by
  rw [h.mem_span_iff, _root_.not_imp]

@[deprecated (since := "2025-05-23")]
alias LinearIndepOn.not_mem_span_iff := LinearIndepOn.notMem_span_iff

theorem LinearIndepOn.mem_span_iff_id {s : Set V} {a : V} (h : LinearIndepOn K id s) :
    a ∈ Submodule.span K s ↔ (LinearIndepOn K id (insert a s) → a ∈ s) := by
  simpa using h.mem_span_iff (a := a)

theorem LinearIndepOn.notMem_span_iff_id {s : Set V} {a : V} (h : LinearIndepOn K id s) :
    a ∉ Submodule.span K s ↔ LinearIndepOn K id (insert a s) ∧ a ∉ s := by
  rw [h.mem_span_iff_id, _root_.not_imp]

@[deprecated (since := "2025-05-23")]
alias LinearIndepOn.not_mem_span_iff_id := LinearIndepOn.notMem_span_iff_id

theorem linearIndepOn_id_pair {x y : V} (hx : x ≠ 0) (hy : ∀ a : K, a • x ≠ y) :
    LinearIndepOn K id {x, y} :=
  pair_comm y x ▸ (LinearIndepOn.id_singleton K hx).id_insert (x := y) <|
    mt mem_span_singleton.1 <| not_exists.2 hy

/-- `LinearIndepOn.pair_iff` is a version that works over arbitrary rings. -/
theorem linearIndepOn_pair_iff {i j : ι} (v : ι → V) (hij : i ≠ j) (hi : v i ≠ 0) :
    LinearIndepOn K v {i, j} ↔ ∀ (c : K), c • v i ≠ v j := by
  rw [pair_comm]
  convert linearIndepOn_insert (s := {i}) (a := j) hij.symm
  simp [hi, mem_span_singleton]

/-- Also see `LinearIndependent.pair_iff` for the version over arbitrary rings. -/
theorem LinearIndependent.pair_iff' {x y : V} (hx : x ≠ 0) :
    LinearIndependent K ![x, y] ↔ ∀ a : K, a • x ≠ y := by
  rw [← linearIndepOn_univ, ← Finset.coe_univ, show @Finset.univ (Fin 2) _ = {0,1} from rfl,
    Finset.coe_insert, Finset.coe_singleton, linearIndepOn_pair_iff _ (by simp) (by simpa)]
  simp

theorem linearIndependent_fin_cons {n} {v : Fin n → V} :
    LinearIndependent K (Fin.cons x v : Fin (n + 1) → V) ↔
      LinearIndependent K v ∧ x ∉ Submodule.span K (range v) := by
  rw [← linearIndependent_equiv (finSuccEquiv n).symm, linearIndependent_option]
  exact Iff.rfl

theorem linearIndependent_fin_snoc {n} {v : Fin n → V} :
    LinearIndependent K (Fin.snoc v x : Fin (n + 1) → V) ↔
      LinearIndependent K v ∧ x ∉ Submodule.span K (range v) := by
  rw [Fin.snoc_eq_cons_rotate, ← Function.comp_def, linearIndependent_equiv,
    linearIndependent_fin_cons]

/-- See `LinearIndependent.fin_cons'` for an uglier version that works if you
only have a module over a semiring. -/
theorem LinearIndependent.fin_cons {n} {v : Fin n → V} (hv : LinearIndependent K v)
    (hx : x ∉ Submodule.span K (range v)) : LinearIndependent K (Fin.cons x v : Fin (n + 1) → V) :=
  linearIndependent_fin_cons.2 ⟨hv, hx⟩

theorem linearIndependent_fin_succ {n} {v : Fin (n + 1) → V} :
    LinearIndependent K v ↔
      LinearIndependent K (Fin.tail v) ∧ v 0 ∉ Submodule.span K (range <| Fin.tail v) := by
  rw [← linearIndependent_fin_cons, Fin.cons_self_tail]

theorem linearIndependent_fin_succ' {n} {v : Fin (n + 1) → V} : LinearIndependent K v ↔
    LinearIndependent K (Fin.init v) ∧ v (Fin.last _) ∉ Submodule.span K (range <| Fin.init v) := by
  rw [← linearIndependent_fin_snoc, Fin.snoc_init_self]

/-- Equivalence between `k + 1` vectors of length `n` and `k` vectors of length `n` along with a
vector in the complement of their span.
-/
def equiv_linearIndependent (n : ℕ) :
    { s : Fin (n + 1) → V // LinearIndependent K s } ≃
      Σ s : { s : Fin n → V // LinearIndependent K s },
        ((Submodule.span K (Set.range (s : Fin n → V)))ᶜ : Set V) where
  toFun s := ⟨⟨Fin.tail s.val, (linearIndependent_fin_succ.mp s.property).left⟩,
    ⟨s.val 0, (linearIndependent_fin_succ.mp s.property).right⟩⟩
  invFun s := ⟨Fin.cons s.2.val s.1.val,
    linearIndependent_fin_cons.mpr ⟨s.1.property, s.2.property⟩⟩
  left_inv _ := by simp only [Fin.cons_self_tail, Subtype.coe_eta]
  right_inv := fun ⟨_, _⟩ => by simp only [Fin.cons_zero, Subtype.coe_eta, Sigma.mk.inj_iff,
    Fin.tail_cons, heq_eq_eq, and_self]

theorem linearIndependent_fin2 {f : Fin 2 → V} :
    LinearIndependent K f ↔ f 1 ≠ 0 ∧ ∀ a : K, a • f 1 ≠ f 0 := by
  rw [linearIndependent_fin_succ, linearIndependent_unique_iff, range_unique, mem_span_singleton,
    not_exists, show Fin.tail f default = f 1 by rw [← Fin.succ_zero_eq_one]; rfl]

theorem exists_linearIndepOn_extension {s t : Set ι} (hs : LinearIndepOn K v s) (hst : s ⊆ t) :
    ∃ b ⊆ t, s ⊆ b ∧ v '' t ⊆ span K (v '' b) ∧ LinearIndepOn K v b := by
  obtain ⟨b, sb, h⟩ := by
    refine zorn_subset_nonempty { b | b ⊆ t ∧ LinearIndepOn K v b} ?_ _ ⟨hst, hs⟩
    · refine fun c hc cc _c0 => ⟨⋃₀ c, ⟨?_, ?_⟩, fun x => ?_⟩
      · exact sUnion_subset fun x xc => (hc xc).1
      · exact linearIndepOn_sUnion_of_directed cc.directedOn fun x xc => (hc xc).2
      · exact subset_sUnion_of_mem
  refine ⟨b, h.prop.1, sb, fun _ ⟨x, hx, hvx⟩ => by_contra fun hn ↦ hn ?_, h.prop.2⟩
  subst hvx
  exact subset_span <| mem_image_of_mem v <| h.mem_of_prop_insert
    ⟨insert_subset hx h.prop.1, h.prop.2.insert hn⟩

theorem exists_linearIndepOn_id_extension (hs : LinearIndepOn K id s) (hst : s ⊆ t) :
    ∃ b ⊆ t, s ⊆ b ∧ t ⊆ span K b ∧ LinearIndepOn K id b := by
  convert exists_linearIndepOn_extension hs hst <;> simp

variable (K t)

theorem exists_linearIndependent :
    ∃ b ⊆ t, span K b = span K t ∧ LinearIndependent K ((↑) : b → V) := by
  obtain ⟨b, hb₁, -, hb₂, hb₃⟩ :=
    exists_linearIndepOn_id_extension (linearIndependent_empty K V) (Set.empty_subset t)
  exact ⟨b, hb₁, (span_eq_of_le _ hb₂ (Submodule.span_mono hb₁)).symm, hb₃⟩

/-- Indexed version of `exists_linearIndependent`. -/
lemma exists_linearIndependent' (v : ι → V) :
    ∃ (κ : Type u') (a : κ → ι), Injective a ∧
      Submodule.span K (Set.range (v ∘ a)) = Submodule.span K (Set.range v) ∧
      LinearIndependent K (v ∘ a) := by
  obtain ⟨t, ht, hsp, hli⟩ := exists_linearIndependent K (Set.range v)
  choose f hf using ht
  let s : Set ι := Set.range (fun a : t ↦ f a.property)
  have hs {i : ι} (hi : i ∈ s) : v i ∈ t := by obtain ⟨a, rfl⟩ := hi; simp [hf]
  let f' (a : s) : t := ⟨v a.val, hs a.property⟩
  refine ⟨s, Subtype.val, Subtype.val_injective, hsp.symm ▸ by congr; aesop, ?_⟩
  · rw [← show Subtype.val ∘ f' = v ∘ Subtype.val by ext; simp [f']]
    apply hli.comp
    rintro ⟨i, x, rfl⟩ ⟨j, y, rfl⟩ hij
    simp only [Subtype.ext_iff, hf, f'] at hij
    simp [hij]

variable {K} {s t : Set ι}

/-- `LinearIndepOn.extend` adds vectors to a linear independent set `s ⊆ t` until it spans
all elements of `t`. -/
noncomputable def LinearIndepOn.extend (hs : LinearIndepOn K v s) (hst : s ⊆ t) : Set ι :=
  Classical.choose (exists_linearIndepOn_extension hs hst)

theorem LinearIndepOn.extend_subset (hs : LinearIndepOn K v s) (hst : s ⊆ t) : hs.extend hst ⊆ t :=
  let ⟨hbt, _hsb, _htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  hbt

theorem LinearIndepOn.subset_extend (hs : LinearIndepOn K v s) (hst : s ⊆ t) : s ⊆ hs.extend hst :=
  let ⟨_hbt, hsb, _htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  hsb

theorem LinearIndepOn.image_subset_span_image_extend (hs : LinearIndepOn K v s) (hst : s ⊆ t) :
    v '' t ⊆ span K (v '' hs.extend hst) :=
  let ⟨_hbt, _hsb, htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  htb

theorem LinearIndepOn.subset_span_extend {s t : Set V} (hs : LinearIndepOn K id s) (hst : s ⊆ t) :
    t ⊆ span K (hs.extend hst) := by
  convert hs.image_subset_span_image_extend hst <;> simp

theorem LinearIndepOn.span_image_extend_eq_span_image (hs : LinearIndepOn K v s) (hst : s ⊆ t) :
    span K (v '' hs.extend hst) = span K (v '' t) :=
  le_antisymm (span_mono (image_mono (hs.extend_subset hst)))
    (span_le.2 (hs.image_subset_span_image_extend hst))

theorem LinearIndepOn.span_extend_eq_span {s t : Set V} (hs : LinearIndepOn K id s) (hst : s ⊆ t) :
    span K (hs.extend hst) = span K t :=
  le_antisymm (span_mono (hs.extend_subset hst)) (span_le.2 (hs.subset_span_extend hst))

theorem LinearIndepOn.linearIndepOn_extend (hs : LinearIndepOn K v s) (hst : s ⊆ t) :
    LinearIndepOn K v (hs.extend hst) :=
  let ⟨_hbt, _hsb, _htb, hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  hli

-- TODO(Mario): rewrite?
theorem exists_of_linearIndepOn_of_finite_span {s : Set V} {t : Finset V}
    (hs : LinearIndepOn K id s) (hst : s ⊆ (span K ↑t : Submodule K V)) :
    ∃ t' : Finset V, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = t.card := by
  classical
  have :
    ∀ t : Finset V,
      ∀ s' : Finset V,
        ↑s' ⊆ s →
          s ∩ ↑t = ∅ →
            s ⊆ (span K ↑(s' ∪ t) : Submodule K V) →
              ∃ t' : Finset V, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = (s' ∪ t).card :=
    fun t =>
    Finset.induction_on t
      (fun s' hs' _ hss' =>
        have : s = ↑s' := eq_of_linearIndepOn_id_of_span_subtype hs hs' <| by simpa using hss'
        ⟨s', by simp [this]⟩)
      fun b₁ t hb₁t ih s' hs' hst hss' =>
      have hb₁s : b₁ ∉ s := fun h => by
        have : b₁ ∈ s ∩ ↑(insert b₁ t) := ⟨h, Finset.mem_insert_self _ _⟩
        rwa [hst] at this
      have hb₁s' : b₁ ∉ s' := fun h => hb₁s <| hs' h
      have hst : s ∩ ↑t = ∅ :=
        eq_empty_of_subset_empty <|
          -- Porting note: `-subset_inter_iff` required.
          Subset.trans
            (by simp [inter_subset_inter, -subset_inter_iff])
            (le_of_eq hst)
      Classical.by_cases (p := s ⊆ (span K ↑(s' ∪ t) : Submodule K V))
        (fun this =>
          let ⟨u, hust, hsu, Eq⟩ := ih _ hs' hst this
          have hb₁u : b₁ ∉ u := fun h => (hust h).elim hb₁s hb₁t
          ⟨insert b₁ u, by simp [insert_subset_insert hust], Subset.trans hsu (by simp), by
            simp [Eq, hb₁t, hb₁s', hb₁u]⟩)
        fun this =>
        let ⟨b₂, hb₂s, hb₂t⟩ := not_subset.mp this
        have hb₂t' : b₂ ∉ s' ∪ t := fun h => hb₂t <| subset_span h
        have : s ⊆ (span K ↑(insert b₂ s' ∪ t) : Submodule K V) := fun b₃ hb₃ => by
          have : ↑(s' ∪ insert b₁ t) ⊆ insert b₁ (insert b₂ ↑(s' ∪ t) : Set V) := by
            simp only [insert_eq, union_subset_union, Subset.refl,
              subset_union_right, Finset.union_insert, Finset.coe_insert]
          have hb₃ : b₃ ∈ span K (insert b₁ (insert b₂ ↑(s' ∪ t) : Set V)) :=
            span_mono this (hss' hb₃)
          have : s ⊆ (span K (insert b₁ ↑(s' ∪ t)) : Submodule K V) := by
            simpa [insert_eq, -singleton_union, -union_singleton] using hss'
          have hb₁ : b₁ ∈ span K (insert b₂ ↑(s' ∪ t)) :=
            mem_span_insert_exchange (this hb₂s) hb₂t
          rw [span_insert_eq_span hb₁] at hb₃; simpa using hb₃
        let ⟨u, hust, hsu, eq⟩ := ih _ (by simp [insert_subset_iff, hb₂s, hs']) hst this
        ⟨u, Subset.trans hust <| union_subset_union (Subset.refl _) (by simp [subset_insert]), hsu,
          by simp [eq, hb₂t', hb₁t, hb₁s']⟩
  have eq : ((t.filter fun x => x ∈ s) ∪ t.filter fun x => x ∉ s) = t := by
    ext1 x
    by_cases x ∈ s <;> simp [*]
  apply
    Exists.elim
      (this (t.filter fun x => x ∉ s) (t.filter fun x => x ∈ s) (by simp [Set.subset_def])
        (by simp +contextual [Set.ext_iff]) (by rwa [eq]))
  intro u h
  exact
    ⟨u, Subset.trans h.1 (by simp +contextual [subset_def, or_imp]),
      h.2.1, by simp only [h.2.2, eq]⟩

theorem exists_finite_card_le_of_finite_of_linearIndependent_of_span {s t : Set V} (ht : t.Finite)
    (hs : LinearIndepOn K id s) (hst : s ⊆ span K t) :
    ∃ h : s.Finite, h.toFinset.card ≤ ht.toFinset.card :=
  have : s ⊆ (span K ↑ht.toFinset : Submodule K V) := by simpa
  let ⟨u, _hust, hsu, Eq⟩ := exists_of_linearIndepOn_of_finite_span hs this
  have : s.Finite := u.finite_toSet.subset hsu
  ⟨this, by rw [← Eq]; exact Finset.card_le_card <| Finset.coe_subset.mp <| by simp [hsu]⟩

end Module
