import Mathlib.Topology.ContinuousFunction.StoneWeierstrass
import Mathlib.Algebra.Star.NonUnitalSubalgebra

open Set RingHom Topology Filter

variable {K X A F S : Type*} [TopologicalSpace X]
variable [CompactSpace X] (x₀ : X)

attribute [fun_prop] continuous_algebraMap ContinuousMap.continuous_eval_const

-- the statement should be in terms of non unital subalgebras, but we lack API
-- TODO : this is a bad name
theorem AlgHom.closure_ker_inter [CommRing K] [Ring A] [Algebra K A]
    [TopologicalSpace K] [T1Space K] [TopologicalSpace A] [ContinuousSub A] [ContinuousSMul K A]
    [FunLike F A K] [AlgHomClass F K A K] [SetLike S A] [OneMemClass S A] [AddSubgroupClass S A]
    [SMulMemClass S K A] (φ : F) (hφ : Continuous φ) (s : S) :
    closure (s ∩ ker φ) = closure s ∩ (ker φ : Set A) := by
  refine subset_antisymm ?_ ?_
  · simpa only [ker_eq, (isClosed_singleton.preimage hφ).closure_eq]
      using closure_inter_subset_inter_closure s (ker φ : Set A)
  · intro x ⟨hxs, (hxφ : φ x = 0)⟩
    rw [mem_closure_iff_clusterPt, ClusterPt] at hxs
    have : Tendsto (fun y ↦ y - φ y • 1) (𝓝 x ⊓ 𝓟 s) (𝓝 x) := by
      conv => congr; rfl; rfl; rw [← sub_zero x, ← zero_smul K 1, ← hxφ]
      exact Filter.tendsto_inf_left (Continuous.tendsto (by fun_prop) x)
    refine mem_closure_of_tendsto this <| eventually_inf_principal.mpr ?_
    filter_upwards [] with g hg using
      ⟨sub_mem hg (SMulMemClass.smul_mem _ <| one_mem _), by simp [RingHom.mem_ker]⟩

-- the statement should be in terms of non unital subalgebras, but let's stick with sets
theorem foo [IsROrC K] (A : StarSubalgebra K C(X, K)) (φ : C(X, K) →⋆ₐ[K] K) (hφ : Continuous φ)
    (hA : A.SeparatesPoints) :
    closure (A ∩ ker φ) = (ker φ : Set (C(X, K))) := by
  -- this rewrite is a bit slow, but oh well...
  rw [AlgHom.closure_ker_inter φ hφ A]
  -- easy, I'm just lazy
  sorry

-- TODO add elab as eliminator to `NonUnitalAlgebra.adjoin_induction`
open MvPolynomial in
theorem bar_key [CommRing K] [CommRing A] [Algebra K A] {s : Set A} {a b : A}
    (ha : a ∈ Algebra.adjoin K s) (hb : b ∈ NonUnitalAlgebra.adjoin K s) :
    a * b ∈ NonUnitalAlgebra.adjoin K s := by
  obtain ⟨P, rfl⟩ : ∃ P : MvPolynomial s K, aeval ((↑) : s → A) P = a := by
    rwa [Algebra.adjoin_eq_range, AlgHom.mem_range] at ha
  refine P.induction_on (M := fun Q ↦ aeval ((↑) : s → A) Q * b ∈ _)
    (fun x ↦ ?_) (fun Q R hQ hR ↦ ?_) (fun Q x hQ ↦ ?_)
  · simpa only [aeval_C, algebraMap_smul, ← smul_eq_mul] using SMulMemClass.smul_mem x hb
  · simpa only [add_mul, map_add] using add_mem hQ hR
  · simpa only [map_mul, aeval_X, mul_comm _ (x : A), mul_assoc]
      using mul_mem (NonUnitalAlgebra.subset_adjoin K x.2) hQ

open MvPolynomial in
theorem bar [CommRing K] [CommRing A] [Algebra K A] {s : Set A}
    (H : Algebra.adjoin K s = ⊤) :
    (Ideal.span s : Set A) = NonUnitalAlgebra.adjoin K s := by
  refine subset_antisymm (fun a ha ↦ ?_) (fun a ha ↦ ?_)
  · exact Submodule.span_induction ha (NonUnitalAlgebra.subset_adjoin K) (zero_mem _)
      (fun _ _ ↦ add_mem) (fun b c hc ↦ bar_key (H.symm ▸ trivial) hc)
  · exact NonUnitalAlgebra.adjoin_induction (p := (· ∈ Ideal.span s)) ha
      Ideal.subset_span (fun _ _ ↦ add_mem) (zero_mem _)
      (fun _ _ hx _ ↦ Ideal.mul_mem_right _ _ hx) (fun r Q hQ ↦ Submodule.smul_of_tower_mem _ r hQ)

open MvPolynomial in
theorem NonUnitalAlgebra.adjoin_eq_map [CommRing K] [CommRing A] [Algebra K A] {s : Set A} :
    NonUnitalAlgebra.adjoin K s = NonUnitalSubalgebra.map (aeval ((↑) : s → A))
      (NonUnitalAlgebra.adjoin K (range MvPolynomial.X)) := by
  refine le_antisymm ?_ ?_
  · rw [adjoin_le_iff]
    exact fun a ha ↦ ⟨MvPolynomial.X ⟨a, ha⟩, subset_adjoin K (mem_range_self _), aeval_X _ _⟩
  · sorry -- neds too much API for now

-- job for algebraists. Maybe even the version for any `c : σ → R` ???
open Set RingHom in
theorem MvPolynomial.ker_aeval_zero {R σ : Type*} [CommRing R] :
    ker (eval (0 : σ → R)) = Ideal.span (Set.range .X) := sorry

-- do we want this ?
protected abbrev ContinuousMap.X {Y : Type*} [TopologicalSpace Y] (S : Set Y) : C(S, Y) :=
  ⟨((↑) : S → Y), continuous_subtype_val⟩

lemma truc {Y : Type*} [TopologicalSpace Y] [CommSemiring Y] [TopologicalSemiring Y] (S : Set Y) :
    ContinuousMap.X S = (Polynomial.toContinuousMapOnAlgHom S) Polynomial.X :=
  by ext; exact Polynomial.eval_X.symm

open Polynomial in
@[simp]
lemma ContinuousMap.polynomial_aeval_apply {X R A : Type*} [CommSemiring R] [TopologicalSpace X]
    [TopologicalSpace A] [CommSemiring A] [Algebra R A] [TopologicalSemiring A]
    (f : C(X, A)) (q : Polynomial R) (x : X) :
    aeval f q x = aeval (f x) q := by
  rw [← coeFnAlgHom_apply R, ← aeval_algHom_apply]
  -- note : aeval_fn_apply should be generalized to algebras
  exact .symm <| aeval_algHom_apply (Pi.evalAlgHom R (fun _ ↦ A) x) _ _

open MvPolynomial in
@[simp]
lemma ContinuousMap.mvPolynomial_aeval_apply {σ X R A : Type*} [CommSemiring R] [TopologicalSpace X]
    [TopologicalSpace A] [CommSemiring A] [Algebra R A] [TopologicalSemiring A]
    (f : σ → C(X, A)) (q : MvPolynomial σ R) (x : X) :
    aeval f q x = aeval (f · x) q := by
  change (Pi.evalAlgHom R (fun _ ↦ A) x).comp (((coeFnAlgHom R).comp (aeval f))) q = _
  rw [MvPolynomial.comp_aeval, MvPolynomial.comp_aeval]
  rfl

-- name mismatch : StarSubalgebra.adjoin VS Algebra.adjoin

-- we don't have `NonUnitalStarAlgebra.adjoin` so the statement is definitely not ideal
open MvPolynomial in
lemma goal [IsROrC K] {S : Set K} [S_compact : CompactSpace S] (S_zero : 0 ∈ S) :
    closure (NonUnitalStarAlgebra.adjoin K {ContinuousMap.X S}) =
    {f : C(S, K) | f ⟨0, S_zero⟩ = 0} := by
  let _ : CommRing C(S, K) := inferInstance
  let _ : Algebra K C(S, K) := inferInstance
  -- should exist in some form
  let φ : C(S, K) →⋆ₐ[K] K :=
  { toFun := fun f ↦ f ⟨0, S_zero⟩,
    map_one' := rfl,
    map_mul' := fun f g ↦ rfl,
    map_zero' := rfl
    map_add' := fun f g ↦ rfl
    commutes' := fun a ↦ rfl
    map_star' := fun f ↦ rfl }
  have φ_cont : Continuous φ := ContinuousMap.continuous_eval_const _
  set σ : Set C(S, K) := {ContinuousMap.X S, star (ContinuousMap.X S)} with σ_eq
  change _ = (ker φ : Set C(S, K))
  rw [← foo (polynomialFunctions S).starClosure φ φ_cont
    (Subalgebra.separatesPoints_monotone le_sup_left (polynomialFunctions_separatesPoints S))]
  rw [← NonUnitalStarSubalgebra.coe_toNonUnitalSubalgebra,
    NonUnitalStarAlgebra.adjoin_toNonUnitalSubalgebra K {ContinuousMap.X S},
    star_singleton, singleton_union]
  rw [polynomialFunctions.starClosure_eq_adjoin_X, ← StarSubalgebra.coe_toSubalgebra,
    ← truc, StarSubalgebra.adjoin_toSubalgebra K {ContinuousMap.X S},
    star_singleton, singleton_union]
  rw [Algebra.adjoin_eq_range, NonUnitalAlgebra.adjoin_eq_map, AlgHom.coe_range, RingHom.ker_eq,
    NonUnitalSubalgebra.coe_map, ← image_preimage_eq_range_inter, ← preimage_comp]
  refine congrArg _ (congrArg _ ?_)
  have : φ ∘ aeval ((↑) : σ → C(S, K)) = eval 0 := by
    ext P
    change aeval ((↑) : σ → C(S, K)) P ⟨0, S_zero⟩ = eval 0 P
    rw [ContinuousMap.mvPolynomial_aeval_apply, aeval_def, eval, coe_eval₂Hom]
    --- AAAAAAAAAAARGH THIS IS SO OBVIOUS
    sorry
  rw [← bar MvPolynomial.adjoin_range_X, this, ← MvPolynomial.ker_aeval_zero, RingHom.ker_eq]

-- -- We lack some `topologicalClosure`s
-- open MvPolynomial in
-- theorem bar_topo [CommRing K] [CommRing A] [Algebra K A] {s : Set A}
--     [TopologicalSpace A] [TopologicalSemiring A]
--     (H : (Algebra.adjoin K s).topologicalClosure = ⊤) :
--     ((Ideal.span s).topologicalClosure : Set A) =
--       (NonUnitalAlgebra.adjoin K s).topologicalClosure := by
--   refine subset_antisymm
--     (closure_minimal (fun a ha ↦ ?_) isClosed_closure)
--     (closure_mono <| fun a ha ↦ ?_)
--   · exact Submodule.span_induction ha
--       (NonUnitalAlgebra.subset_adjoin K |>.trans subset_closure) (zero_mem _)
--       (fun _ _ ↦ add_mem) (fun b c hc ↦ bar_key (H.symm ▸ trivial) hc)
--   · exact NonUnitalAlgebra.adjoin_induction (p := (· ∈ Ideal.span s)) ha
--       Ideal.subset_span (fun _ _ ↦ add_mem) (zero_mem _)
--       (fun _ _ hx _ ↦ Ideal.mul_mem_right _ _ hx) (fun r Q hQ ↦ Submodule.smul_of_tower_mem _ r hQ)
