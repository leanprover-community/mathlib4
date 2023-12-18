/-
Copyright (c) 2023 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Extension.Well

/-!
# Proof that continuous mutlilinear maps are infinitely differentiable.

When `f` is a continuous multilinear map on `(i : ι) → E i` with `ι finite`, we define its
derivative `f.deriv` at `x` as the continuous linear map sending `y` to the sum over
`i` in `ι` of the value of `f` at the vector sending `j` in `ι` to `x j` for
`j ≠ i` and to `y j` for `j=i`. This is the continuous version of `f.linearDeriv`.

We show that this is indeed the strong derivative of `f`.

We then show that `f.deriv`, as a map of `x`, is the sum over `i` in `ι` of
of continuous multilinear map with variables indexed by `{j : ι | j ≠ i}`
composed with the continuous linear projection on `(j : ι) → E j` that kills
the factor `E i`. This allows us to deduce by an induction on `Fintype.card ι`
that `f` is indeed infinitely differentiable.


## Main results

Let `f` be a continuous multilinear map in finitely many variables.
*

## Implementation notes

We run into some universe trouble when doing the last induction, so we need to first
prove a version of the main theorem where all the spaces are in the same universe.
For technical reasons (i.e. the fact that `ContinuousMultilinearMap.domDomCongr` is
only defined when all `E i` are the same type), we first restrict to the case where all
`E i` are equal to the same type when generalizing to different universes, and in a
last step we deduce the result that we want.
-/



namespace ContinuousLinearMap


variable {R : Type*} [Semiring R] [TopologicalSpace R] {ι : Type*} [Fintype ι]
{M : ι → Type*} {N : Type*}
[(i : ι) → AddCommMonoid (M i)] [AddCommMonoid N] [(i : ι) → TopologicalSpace (M i)]
[TopologicalSpace N] [(i : ι) → Module R (M i)] [Module R N] [DecidableEq ι]

variable (R M)

/-- Auxiliary construction: given normed modules `R i` indexed by a type `ι`, and
given a fixed element `i` of `ι`, this constructs the  embed_eraseding of the product
of the `R j` for `i ≠ j` into` the product of all `R j`.-/
def embed_erase (i : ι) :
    ((j : (Finset.univ (α := ι).erase i)) → M j) →L[R] ((i : ι) → M i) := by
  apply ContinuousLinearMap.pi
  intro j
  by_cases h : j = i
  . exact 0
  . have hj : j ∈ (Finset.univ (α := ι).erase i) := by
      simp only [Finset.mem_univ, not_true_eq_false, Finset.mem_erase, ne_eq, h,
      not_false_eq_true, and_self]
    exact ContinuousLinearMap.proj (⟨j, hj⟩ : (Finset.univ (α := ι).erase i))

@[simp]
lemma embed_erase_apply_same (i : ι)
    (x : ((j : (Finset.univ (α := ι).erase i)) → M j)) :
    embed_erase R M i x i = 0 := by
  unfold embed_erase
  simp only [coe_pi', dite_true, zero_apply]

@[simp]
lemma embed_erase_apply_noteq (i : ι)
    (x : ((j : (Finset.univ (α := ι).erase i)) → M j)) {j : ι} (hj : j ≠ i) :
    embed_erase R M i x j = x ⟨j, by simp only [Finset.mem_univ,
    not_true_eq_false, Finset.mem_erase, ne_eq, hj, not_false_eq_true, and_self]⟩ := by
  unfold embed_erase
  simp only [coe_pi', hj, dite_false, proj_apply, ne_eq]

end ContinuousLinearMap

namespace ContinuousMultilinearMap

open Filter Asymptotics ContinuousLinearMap Set Metric
open Topology NNReal Asymptotics ENNReal
open NormedField MultilinearMap BigOperators


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
{E : ι → Type*} {F : Type*} [(i : ι) → NormedAddCommGroup (E i)] [NormedAddCommGroup F]
[(i : ι) → NormedSpace 𝕜 (E i)] [NormedSpace 𝕜 F] [DecidableEq ι]

lemma map_piecewise_sub_map_piecewise [LinearOrder ι] (a b v : (i : ι) → E i) (s : Finset ι)
(f : MultilinearMap 𝕜 E F) :
    f (s.piecewise a v) - f (s.piecewise b v) = ∑ i in s, f
      fun j ↦ if j ∈ s then if j < i then a j else if j = i then a j - b j else b j else v j := by
      sorry

def toMultilinearMap_erase (i : ι) (f : ContinuousMultilinearMap 𝕜 E F) :
MultilinearMap 𝕜 (fun (j : (Finset.univ (α := ι).erase i)) => E j) (((i : ι) → E i) →L[𝕜] F) :=
{
  toFun := fun x => ContinuousLinearMap.comp (σ₁₂ := RingHom.id 𝕜) (f.toContinuousLinearMap
    (ContinuousLinearMap.embed_erase 𝕜 E i x) i) (ContinuousLinearMap.proj i)
  map_add' := by
    intro _ x ⟨j, hj⟩ a b
    simp only
    ext y
    simp only at a b
    simp only [coe_comp', Function.comp_apply, proj_apply, ContinuousLinearMap.add_apply]
    have heq : ∀ (c : E j), (toContinuousLinearMap f ((embed_erase 𝕜 E i) (Function.update x ⟨j, hj⟩ c)) i) (y i) =
     f (Function.update (fun k => if k ≠ i then embed_erase 𝕜 E i x k else y k) j c) := by
       intro c
       unfold toContinuousLinearMap
       simp only [coe_mk', LinearMap.coe_mk, LinearMap.coe_toAddHom,
         MultilinearMap.toLinearMap_apply, coe_coe, ne_eq, ite_not]
       congr
       ext k
       simp only [Finset.mem_univ, not_true_eq_false, Finset.mem_erase, ne_eq, and_true] at hj
       by_cases h : k = i
       . rw [h, Function.update_same, Function.update_noteq (Ne.symm hj)]
         simp only [embed_erase_apply_same, ite_true]
       . by_cases h' : k = j
         . rw [h', Function.update_same, Function.update_noteq hj, embed_erase_apply_noteq 𝕜 E _ _ hj, Function.update_same]
         . rw [Function.update_noteq h, Function.update_noteq h', embed_erase_apply_noteq _ _ _ _ h]
           have h1 : j ∈ (Finset.univ (α := ι).erase i) := by simp only [Finset.mem_univ,
             not_true_eq_false, Finset.mem_erase, ne_eq, hj, not_false_eq_true, and_self]
           have h2 : k ∈ (Finset.univ (α := ι).erase i) := by simp only [Finset.mem_univ,
             not_true_eq_false, Finset.mem_erase, ne_eq, h, not_false_eq_true, and_self]
           have hne : (⟨k, h2⟩ : (Finset.univ (α := ι).erase i)) ≠ ⟨j, h1⟩ := by
             by_contra habs
             apply_fun (fun x => x.1) at habs
             exact h' habs
           rw [Function.update_noteq hne]
           simp only [h, ne_eq, not_false_eq_true,  embed_erase_apply_noteq, ite_false]
    rw [heq a, heq b, heq (a + b)]
    simp only [ne_eq, ite_not, map_add]
  map_smul' := by
    intro _ x ⟨j, hj⟩ c a
    simp only
    ext y
    simp only at a
    simp only [coe_comp', Function.comp_apply, proj_apply, coe_smul', Pi.smul_apply]
    have heq : ∀ (c : E j), (toContinuousLinearMap f ((embed_erase 𝕜 E i) (Function.update x ⟨j, hj⟩ c)) i) (y i) =
     f (Function.update (fun k => if k ≠ i then  embed_erase 𝕜 E i x k else y k) j c) := by
       intro c
       unfold toContinuousLinearMap
       simp only [coe_mk', LinearMap.coe_mk, LinearMap.coe_toAddHom,
         MultilinearMap.toLinearMap_apply, coe_coe, ne_eq, ite_not]
       congr
       ext k
       simp only [Finset.mem_univ, not_true_eq_false, Finset.mem_erase, ne_eq, and_true] at hj
       by_cases h : k = i
       . rw [h, Function.update_same, Function.update_noteq (Ne.symm hj)]
         simp only [embed_erase_apply_same, ite_true]
       . by_cases h' : k = j
         . rw [h', Function.update_same, Function.update_noteq hj,  embed_erase_apply_noteq 𝕜 E _ _ hj, Function.update_same]
         . rw [Function.update_noteq h, Function.update_noteq h',  embed_erase_apply_noteq _ _ _ _ h]
           have h1 : j ∈ (Finset.univ (α := ι).erase i) := by simp only [Finset.mem_univ,
             not_true_eq_false, Finset.mem_erase, ne_eq, hj, not_false_eq_true, and_self]
           have h2 : k ∈ (Finset.univ (α := ι).erase i) := by simp only [Finset.mem_univ,
             not_true_eq_false, Finset.mem_erase, ne_eq, h, not_false_eq_true, and_self]
           have hne : (⟨k, h2⟩ : (Finset.univ (α := ι).erase i)) ≠ ⟨j, h1⟩ := by
             by_contra habs
             apply_fun (fun x => x.1) at habs
             exact h' habs
           rw [Function.update_noteq hne]
           simp only [h, ne_eq, not_false_eq_true,  embed_erase_apply_noteq, ite_false]
    rw [heq a, heq (c • a)]
    simp only [ne_eq, ite_not, map_smul]
}

lemma toMultilinearMap_erase_apply (i : ι) (f : ContinuousMultilinearMap 𝕜 E F) (x : (j : (Finset.univ (α := ι).erase i)) → E j)
(y : (i : ι) → E i) :
f.toMultilinearMap_erase i x y = f (fun j => if h : j = i then y j else x ⟨j, by simp only [Finset.mem_univ,
  not_true_eq_false, Finset.mem_erase, ne_eq, h, not_false_eq_true, and_self]⟩) := by
  unfold toMultilinearMap_erase toContinuousLinearMap
  simp only [MultilinearMap.coe_mk, coe_comp', coe_mk', LinearMap.coe_mk, LinearMap.coe_toAddHom,
    Function.comp_apply, proj_apply, MultilinearMap.toLinearMap_apply, coe_coe, ne_eq]
  congr
  ext j
  by_cases h : j = i
  . rw [h, Function.update_same]
    simp only [dite_true]
  . rw [Function.update_noteq h]
    simp only [ne_eq, h, not_false_eq_true,  embed_erase_apply_noteq, dite_false]


lemma toMultilinearMap_erase_norm_le (i : ι) (f : ContinuousMultilinearMap 𝕜 E F) (x : (j : (Finset.univ (α := ι).erase i)) → E j) :
‖f.toMultilinearMap_erase i x‖ ≤ ‖f‖ * Finset.prod Finset.univ (fun j => ‖x j‖) := by
  rw [ContinuousLinearMap.op_norm_le_iff]
  . intro y
    rw [toMultilinearMap_erase_apply]
    refine le_trans (ContinuousMultilinearMap.le_op_norm f _) ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [←(Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i))]
    simp only [Finset.mem_univ, not_true_eq_false, ne_eq, dite_true]
    refine mul_le_mul ?_ (norm_le_pi_norm y i) (norm_nonneg _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    set I : (j : ι) → (j ∈ (Finset.univ (α := ι).erase i)) → (Finset.univ (α := ι).erase i) := fun j hj => ⟨j, hj⟩
    have hI : ∀ (j : ι) (hj : j ∈ (Finset.univ (α := ι).erase i)), I j hj ∈ Finset.univ := fun _ _ => Finset.mem_univ _
    have heq : ∀ (j : ι) (hj : j ∈ (Finset.univ (α := ι).erase i)),
      (fun k ↦ ‖if hk : k = i then y k else x ⟨k, by simp only [Finset.mem_univ,
        not_true_eq_false, Finset.mem_erase, ne_eq, hk, not_false_eq_true, and_self]⟩‖) j =
        ‖x (I j hj)‖ := by
      intro j hj
      simp only [Finset.mem_univ, not_true_eq_false, Finset.mem_erase, ne_eq, and_true] at hj
      simp only [hj, ne_eq, dite_false]
    set J : (k : (Finset.univ (α := ι).erase i)) → (k ∈ Finset.univ) → ι := fun k _ => k.1
    have hJ : ∀ (k : (Finset.univ (α := ι).erase i)) (hk : k ∈ Finset.univ), J k hk ∈ (Finset.univ (α := ι).erase i) :=
      fun k _ =>  k.2
    have hJI : ∀ (j : ι) (hj : j ∈ (Finset.univ (α := ι).erase i)), J (I j hj) (hI j hj) = j :=
      fun _ _ => by simp only [Finset.univ_eq_attach]
    have hIJ : ∀ (k : (Finset.univ (α := ι).erase i)) (hk : k ∈ Finset.univ),
      I (J k hk) (hJ k hk) = k := fun _ _ => by simp only [Finset.univ_eq_attach, Subtype.coe_eta]
    rw [Finset.prod_bij' I hI heq J hJ hJI hIJ (g := fun k => ‖x k‖)]
  . exact mul_nonneg (norm_nonneg f) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))


noncomputable def toContinuousMultilinearMap_erase (i : ι) (f : ContinuousMultilinearMap 𝕜 E F) :
ContinuousMultilinearMap 𝕜 (fun (j : (Finset.univ (α := ι).erase i)) => E j) (((i : ι) → E i) →L[𝕜] F) :=
MultilinearMap.mkContinuous (f.toMultilinearMap_erase i) ‖f‖ (f.toMultilinearMap_erase_norm_le i)

lemma toContinuousMultilinearMap_coe (i : ι) (f : ContinuousMultilinearMap 𝕜 E F) :
(f.toContinuousMultilinearMap_erase i).toFun =
(fun x => ContinuousLinearMap.comp (toContinuousLinearMap f x i) (ContinuousLinearMap.proj i))
∘ (fun x => embed_erase 𝕜 E i x) := by
  ext x
  unfold toContinuousMultilinearMap_erase toMultilinearMap_erase toContinuousLinearMap
  simp only [MultilinearMap.toFun_eq_coe, coe_coe, MultilinearMap.coe_mkContinuous,
    MultilinearMap.coe_mk, coe_comp', coe_mk', LinearMap.coe_mk, LinearMap.coe_toAddHom,
    Function.comp_apply, proj_apply, MultilinearMap.toLinearMap_apply]

lemma toContinuousMultilinearMap_coe' (i : ι) (f : ContinuousMultilinearMap 𝕜 E F) :
(fun x => ContinuousLinearMap.comp (toContinuousLinearMap f x i) (ContinuousLinearMap.proj i)) =
(f.toContinuousMultilinearMap_erase i).toFun ∘
(ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (R := 𝕜) j.1)) := by
  ext x y
  unfold toContinuousMultilinearMap_erase toMultilinearMap_erase toContinuousLinearMap
  simp only [coe_comp', coe_mk', LinearMap.coe_mk, LinearMap.coe_toAddHom, Function.comp_apply,
    proj_apply, MultilinearMap.toLinearMap_apply, coe_coe, MultilinearMap.toFun_eq_coe,
    MultilinearMap.coe_mkContinuous, MultilinearMap.coe_mk, coe_pi']
  congr
  ext j
  by_cases h : j = i
  . rw [h, Function.update_same, Function.update_same]
  . rw [Function.update_noteq h, Function.update_noteq h,  embed_erase_apply_noteq _ _ _ _ h]



noncomputable def deriv (f : ContinuousMultilinearMap 𝕜 E F)
(x : (i : ι) → E i) : ((i : ι) → E i) →L[𝕜] F :=
Finset.sum Finset.univ (fun (i : ι) => (f.toContinuousLinearMap x i).comp (ContinuousLinearMap.proj i))

@[simp]
lemma deriv_def (f : ContinuousMultilinearMap 𝕜 E F)
(x : (i : ι) → E i) :
f.deriv x = Finset.sum Finset.univ (fun (i : ι) => (f.toContinuousLinearMap x i).comp (ContinuousLinearMap.proj i)) := rfl

@[simp]
lemma deriv_apply (f : ContinuousMultilinearMap 𝕜 E F)
(x y : (i : ι) → E i) :
  f.deriv x y = Finset.sum Finset.univ (fun (i : ι) => f (Function.update x i (y i))) := by
  unfold deriv toContinuousLinearMap
  simp only [ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_comp',
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, LinearMap.coe_toAddHom, Finset.sum_apply,
    Function.comp_apply, ContinuousLinearMap.proj_apply, MultilinearMap.toLinearMap_apply, coe_coe]

@[simp]
lemma deriv_coe_apply (f : ContinuousMultilinearMap 𝕜 E F) (x y: (i : ι) → (E i)):
f.deriv x y = f.toMultilinearMap.linearDeriv x y := by
  simp only [deriv_apply, MultilinearMap.linearDeriv_apply, coe_coe]


@[simp]
lemma deriv_coe (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → (E i)):
(f.deriv x).toLinearMap = f.toMultilinearMap.linearDeriv x := by
  apply LinearMap.ext
  intro y
  apply deriv_coe_apply


lemma sub_vs_deriv (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
((fun p => f p.1 - f p.2 - (deriv f x) (p.1 - p.2)) ∘ fun x_1 => (x, x) + x_1) =
    fun h => Finset.sum (Set.Finite.toFinset ((Set.finite_coe_iff (s := {s : Finset ι | 2 ≤ s.card})).mp
    inferInstance)) (fun (s : Finset ι) => f (s.piecewise h.1 x) - f (s.piecewise h.2 x)) := by
  have heq : ((fun p => f p.1 - f p.2 - (deriv f x) (p.1 - p.2)) ∘ fun x_1 => (x, x) + x_1) =
    (fun h => f (x + h.1) - f (x + h.2) - (deriv f x) (h.1 - h.2)) := by
    ext h
    rw [Function.comp_apply, Prod.fst_add, Prod.snd_add]
    simp only
    rw [sub_add_eq_sub_sub, add_comm, add_sub_assoc, sub_self, add_zero]
  rw [heq]
  ext h
  rw [deriv_coe_apply]; erw [map_sub_total_vs_linearDeriv]; rfl


lemma sub_piecewise_bound (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i)
(h : (((i : ι) → (E i)) × ((i : ι) → E i)))
{s : Finset ι} (hs : 2 ≤ s.card) :
‖f (s.piecewise h.1 x) - f (s.piecewise h.2 x)‖ ≤ s.card • (‖f‖ *
‖x‖ ^ sᶜ.card * ‖h‖ ^ (s.card - 1) * ‖h.1 - h.2‖) := by
  letI : LinearOrder ι := WellFounded.wellOrderExtension emptyWf.wf
  set n := s.card
  convert (congr_arg norm (f.toMultilinearMap.map_piecewise_sub_map_piecewise
    h.1 h.2 x s)).trans_le _
  refine le_trans (norm_sum_le _ _) ?_
  have heq : n = Finset.card s := rfl
  rw [heq, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro i hi
  refine le_trans (ContinuousMultilinearMap.le_op_norm f _) ?_
  rw [mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [ ←(Finset.prod_compl_mul_prod s)]
  rw [←(Finset.mul_prod_erase s _ hi)]
  simp only [hi, dite_true]
  conv => lhs
          congr
          rfl
          congr
          simp only [lt_irrefl i, ite_false, ite_true]
          rfl
  have hle1aux : ∀ (j : ι), j ∈ sᶜ →
    (fun k => ‖if k ∈ s then
          if k < i then h.1 k
          else
            if k = i then h.1 k - h.2 k
            else h.2 k
        else x k‖) j ≤ ‖x‖ := by
    intro j hj
    rw [Finset.mem_compl] at hj
    simp only [hj, ite_false]
    apply norm_le_pi_norm
  have hle1 := Finset.prod_le_prod (s := sᶜ) (fun j _ => norm_nonneg _) hle1aux
  rw [Finset.prod_const] at hle1
  refine mul_le_mul ?_ ?_ (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg
    (fun _ _ => norm_nonneg _))) (pow_nonneg (norm_nonneg _) _)
  . rw [← Finset.prod_const]
    apply Finset.prod_le_prod (fun j _ => norm_nonneg _)
    intro j hj
    rw [Finset.mem_compl] at hj
    simp only [hj, ite_false]
    exact norm_le_pi_norm _ _
  . rw [mul_comm, ← Pi.sub_apply]
    refine mul_le_mul ?_ (norm_le_pi_norm _ _) (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    rw [← (Finset.card_erase_of_mem hi), ← Finset.prod_const]
    apply Finset.prod_le_prod (fun j _ => norm_nonneg _)
    intro j hj
    rw [Finset.mem_erase] at hj
    simp only [hj.2, ite_true]
    by_cases hj' : j < i
    . simp only [hj', ite_true]
      exact le_trans (norm_le_pi_norm _ _) (norm_fst_le h)
    . simp only [hj', hj.1, ite_false]
      exact le_trans (norm_le_pi_norm _ _) (norm_snd_le h)



lemma sub_piecewise_littleO (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i)
{s : Finset ι} (hs : 2 ≤ s.card) :
(fun (h : (((i : ι) → (E i)) × ((i : ι) → E i))) =>
f (s.piecewise h.1 x) - f (s.piecewise h.2 x)) =o[nhds 0] (fun p => p.1 - p.2) := by
  rw [Asymptotics.isLittleO_iff]
  intro C hC
  have hspos : 0 < s.card - 1  := by
    rw [←Nat.pred_eq_sub_one, Nat.lt_pred_iff, ←Nat.succ_le_iff]
    exact hs
  have h0 : 0 ≤ s.card * ‖f‖ * ‖x‖ ^ sᶜ.card :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (pow_nonneg (norm_nonneg _) _)
  have h0' : 0 < s.card * ‖f‖ * ‖x‖ ^ sᶜ.card + 1 :=
    lt_of_lt_of_le (zero_lt_one) (le_add_of_nonneg_left h0)
  have h1 : 0 < C / (s.card * ‖f‖ * ‖x‖ ^ sᶜ.card + 1) := div_pos hC h0'
  apply Filter.Eventually.mp
    (eventually_nhds_norm_smul_sub_lt (1 : 𝕜) (0 : (((i : ι) → (E i)) × ((i : ι) → E i)))
      (ε := Real.rpow (C / (s.card * ‖f‖ * ‖x‖ ^ (sᶜ.card) + 1)) ((Nat.cast (R := ℝ) (s.card - 1))⁻¹))
      (Real.rpow_pos_of_pos h1 _))
  apply Filter.eventually_of_forall
  intro h
  rw [one_smul, sub_zero]
  intro hbound
  refine le_trans (sub_piecewise_bound f x h hs) ?_
  simp only [ge_iff_le, nsmul_eq_mul]
  rw [←mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg (h.1 - h.2))
  have h2 := pow_le_pow_of_le_left (norm_nonneg h) (le_of_lt hbound) (s.card - 1)
  erw [Real.rpow_nat_inv_pow_nat (le_of_lt h1) (Ne.symm (ne_of_lt hspos))] at h2
  rw [←mul_assoc, ←mul_assoc]
  refine le_trans (mul_le_mul_of_nonneg_left h2 h0) ?_
  rw [mul_div, _root_.div_le_iff h0']
  linarith


-- Derivability results.

variable {u : Set ((i : ι) → E i)}

theorem hasStrictFDerivAt (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    HasStrictFDerivAt f (f.deriv x) x := by
  letI : LinearOrder ι := WellFounded.wellOrderExtension emptyWf.wf
  simp only [HasStrictFDerivAt]
  simp only [←map_add_left_nhds_zero (x, x), isLittleO_map]
  have heq : ((fun p => p.1 - p.2) ∘ fun p => (x, x) + p) = fun p => p.1 - p.2 := by
    apply funext
    intro p
    simp only [Function.comp_apply, Prod.fst_add, Prod.snd_add, add_sub_add_left_eq_sub]
  rw [sub_vs_deriv, heq]
  apply Asymptotics.IsLittleO.sum
  intro s hs
  simp only [Finite.toFinset_setOf, Finset.mem_univ, forall_true_left, not_le, Finset.mem_filter,
    true_and] at hs
  apply sub_piecewise_littleO f x hs

theorem hasFDerivAt (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    HasFDerivAt f (f.deriv x) x :=
  (f.hasStrictFDerivAt x).hasFDerivAt

theorem hasFDerivWithinAt (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    HasFDerivWithinAt f (f.deriv x) u x :=
  (f.hasFDerivAt x).hasFDerivWithinAt

theorem differentiableAt (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    DifferentiableAt 𝕜 f x :=
  (f.hasFDerivAt x).differentiableAt

theorem differentiableWithinAt (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    DifferentiableWithinAt 𝕜 f u x :=
  (f.differentiableAt x).differentiableWithinAt

protected theorem fderiv (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    fderiv 𝕜 f x = f.deriv x :=
  HasFDerivAt.fderiv (f.hasFDerivAt x)

protected theorem fderivWithin (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i)
    (hxs : UniqueDiffWithinAt 𝕜 u x) : fderivWithin 𝕜 f u x = f.deriv x := by
  rw [DifferentiableAt.fderivWithin (f.differentiableAt x) hxs]
  exact f.fderiv x

theorem differentiable (f : ContinuousMultilinearMap 𝕜 E F) : Differentiable 𝕜 f :=
  fun x => f.differentiableAt x

theorem differentiableOn (f : ContinuousMultilinearMap 𝕜 E F) :
    DifferentiableOn 𝕜 f u :=
  f.differentiable.differentiableOn


universe u

theorem contDiff_aux {r : ℕ} : ∀ (ι' : Type u) (hι : Fintype ι')
(E' : ι' → Type u) (F' : Type u)
(hE1 : (i : ι') → NormedAddCommGroup (E' i)) (hF1 : NormedAddCommGroup F') (hE2 : (i : ι') → NormedSpace 𝕜 (E' i))
(hF2 : NormedSpace 𝕜 F')
(n : ℕ∞) (f : ContinuousMultilinearMap 𝕜 E' F'),
(Fintype.card ι' = r) → (DecidableEq ι') → ContDiff 𝕜 n f := by
  induction' r with r IH
  . intro ι' hι E' F' hE1 hF1 hE2 hF2 n f hr hdec
    letI := hι
    letI := hE1
    letI := hE2
    letI := hF1
    letI := hF2
    letI := hdec
    rw [Fintype.card_eq_zero_iff] at hr
    letI := hr
    have he : ∀ (x : (i : ι') → E' i), x = 0 :=
      fun _ => funext (fun i => hr.elim i)
    have heq : f = ContinuousMultilinearMap.constOfIsEmpty 𝕜 E' (f 0) := by
      ext x
      rw [he x, constOfIsEmpty_apply]
    rw [heq]
    apply contDiff_const
  . intro ι' hι E' F' hE1 hF1 hE2 hF2 n f hr hdec
    letI := hι
    letI := hE1
    letI := hE2
    letI := hF1
    letI := hF2
    letI := hdec
    suffices h : ContDiff 𝕜 ⊤ f from h.of_le le_top
    rw [contDiff_top_iff_fderiv, and_iff_right f.differentiable]
    rw [funext (fun x => f.fderiv x), funext (fun x => f.deriv_def x)]
    apply ContDiff.sum
    intro i _
    rw [toContinuousMultilinearMap_coe']
    refine ContDiff.comp ?_ (ContinuousLinearMap.contDiff _)
    have hcard : Fintype.card (Finset.univ (α := ι').erase i) = r := by
      simp only [Finset.mem_univ, not_true_eq_false, Finset.mem_erase, ne_eq, and_true,
        Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, ge_iff_le]
      rw [hr, ←Nat.pred_eq_sub_one, Nat.pred_succ]
    exact IH (Finset.univ (α := ι').erase i) inferInstance
      (fun (i : (Finset.univ (α := ι').erase i)) => E' i) (((i : ι') → (E' i)) →L[𝕜] F')
      (fun (i : (Finset.univ (α := ι').erase i)) => hE1 i) inferInstance
      (fun (i : (Finset.univ (α := ι').erase i)) => hE2 i) inferInstance
      ⊤ (f.toContinuousMultilinearMap_erase i) hcard inferInstance

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem contDiff_aux' {n : ℕ∞} (f : ContinuousMultilinearMap 𝕜 (fun (_ : ι) => G) F) :
ContDiff 𝕜 n f := by
  let r := Fintype.card ι
  let ιu : Type max u_2 u_4 u_5  := ULift.{max u_2 u_4 u_5} ι
  let Gu : Type max u_2 u_4 u_5 := ULift.{max u_2 u_4 u_5} G
  let Fu : Type max u_2 u_4 u_5 := ULift.{max u_2 u_4 u_5} F
  have isoι : ιu ≃ ι := Equiv.ulift
  have isoG : Gu ≃L[𝕜] G := ContinuousLinearEquiv.ulift
  have isoF : Fu ≃L[𝕜] F := ContinuousLinearEquiv.ulift
  set g := isoF.symm.toContinuousLinearMap.compContinuousMultilinearMap
    ((f.domDomCongr isoι.symm).compContinuousLinearMap (fun _ => isoG.toContinuousLinearMap))
  have hfg : f = isoF.toContinuousLinearMap ∘ g ∘ (ContinuousLinearMap.pi
    (fun i => ContinuousLinearMap.comp isoG.symm.toContinuousLinearMap (ContinuousLinearMap.proj (isoι i))) :
    ((i : ι) → G) →L[𝕜] (i : ιu) → Gu) := by
    ext v
    simp only [ContinuousLinearEquiv.coe_coe, compContinuousMultilinearMap_coe, coe_pi', coe_comp',
      Function.comp_apply, proj_apply, compContinuousLinearMap_apply,
      ContinuousLinearEquiv.apply_symm_apply, domDomCongr_apply]
    congr
    ext j
    rw [Equiv.apply_symm_apply]
  rw [hfg]
  refine ContDiff.comp (ContinuousLinearMap.contDiff _) (ContDiff.comp ?_ (ContinuousLinearMap.contDiff _))
  exact contDiff_aux (𝕜 := 𝕜) (r := r) ιu inferInstance (fun _ => Gu) Fu (fun _ => inferInstance)
    inferInstance (fun _ => inferInstance) inferInstance n g (by simp only [Fintype.card_ulift]) inferInstance

theorem contDiff {n : ℕ∞} (f : ContinuousMultilinearMap 𝕜 E F) :
ContDiff 𝕜 n f := by
  set G := (i : ι) → E i
  set g : ContinuousMultilinearMap 𝕜 (fun (_ : ι) => G) F := f.compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj i)
  set truc : ((i : ι) → (E i)) →L[𝕜] (i : ι) → G := by
    apply ContinuousLinearMap.pi
    intro i
    refine ContinuousLinearMap.comp ?_ (ContinuousLinearMap.proj i)
    apply ContinuousLinearMap.pi
    intro j
    by_cases h : j = i
    . rw [h]; apply ContinuousLinearMap.id
    . exact 0
  have hfg : f = g ∘ truc := by
    ext v
    simp only [eq_mpr_eq_cast, coe_pi', coe_comp', Function.comp_apply, proj_apply,
      compContinuousLinearMap_apply, cast_eq, dite_eq_ite, ite_true, coe_id', id_eq]
  rw [hfg]
  exact ContDiff.comp g.contDiff_aux' (ContinuousLinearMap.contDiff _)

end ContinuousMultilinearMap
