/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Lattice
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.LinearAlgebra.Basis
import Mathlib.LinearAlgebra.Quotient

#align_import ring_theory.ideal.operations from "leanprover-community/mathlib"@"e7f0ddbf65bd7181a85edb74b64bdc35ba4bdc74"

/-!
# More operations on modules and ideals
-/

universe u v w x

open BigOperators Pointwise

namespace Submodule

variable {R : Type u} {M : Type v} {F : Type*} {G : Type*}

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

open Pointwise

instance hasSMul' : SMul (Ideal R) (Submodule R M) :=
  ⟨Submodule.map₂ (LinearMap.lsmul R M)⟩
#align submodule.has_smul' Submodule.hasSMul'

/-- This duplicates the global `smul_eq_mul`, but doesn't have to unfold anywhere near as much to
apply. -/
protected theorem _root_.Ideal.smul_eq_mul (I J : Ideal R) : I • J = I * J :=
  rfl
#align ideal.smul_eq_mul Ideal.smul_eq_mul

/-- `N.annihilator` is the ideal of all elements `r : R` such that `r • N = 0`. -/
def annihilator (N : Submodule R M) : Ideal R :=
  LinearMap.ker (LinearMap.lsmul R N)
#align submodule.annihilator Submodule.annihilator

variable {I J : Ideal R} {N P : Submodule R M}

theorem mem_annihilator {r} : r ∈ N.annihilator ↔ ∀ n ∈ N, r • n = (0 : M) :=
  ⟨fun hr n hn => congr_arg Subtype.val (LinearMap.ext_iff.1 (LinearMap.mem_ker.1 hr) ⟨n, hn⟩),
    fun h => LinearMap.mem_ker.2 <| LinearMap.ext fun n => Subtype.eq <| h n.1 n.2⟩
#align submodule.mem_annihilator Submodule.mem_annihilator

theorem mem_annihilator' {r} : r ∈ N.annihilator ↔ N ≤ comap (r • (LinearMap.id : M →ₗ[R] M)) ⊥ :=
  mem_annihilator.trans ⟨fun H n hn => (mem_bot R).2 <| H n hn, fun H _ hn => (mem_bot R).1 <| H hn⟩
#align submodule.mem_annihilator' Submodule.mem_annihilator'

theorem mem_annihilator_span (s : Set M) (r : R) :
    r ∈ (Submodule.span R s).annihilator ↔ ∀ n : s, r • (n : M) = 0 := by
  rw [Submodule.mem_annihilator]
  constructor
  · intro h n
    exact h _ (Submodule.subset_span n.prop)
  · intro h n hn
    refine Submodule.span_induction hn ?_ ?_ ?_ ?_
    · intro x hx
      exact h ⟨x, hx⟩
    · exact smul_zero _
    · intro x y hx hy
      rw [smul_add, hx, hy, zero_add]
    · intro a x hx
      rw [smul_comm, hx, smul_zero]
#align submodule.mem_annihilator_span Submodule.mem_annihilator_span

theorem mem_annihilator_span_singleton (g : M) (r : R) :
    r ∈ (Submodule.span R ({g} : Set M)).annihilator ↔ r • g = 0 := by simp [mem_annihilator_span]
#align submodule.mem_annihilator_span_singleton Submodule.mem_annihilator_span_singleton

theorem annihilator_bot : (⊥ : Submodule R M).annihilator = ⊤ :=
  (Ideal.eq_top_iff_one _).2 <| mem_annihilator'.2 bot_le
#align submodule.annihilator_bot Submodule.annihilator_bot

theorem annihilator_eq_top_iff : N.annihilator = ⊤ ↔ N = ⊥ :=
  ⟨fun H =>
    eq_bot_iff.2 fun (n : M) hn =>
      (mem_bot R).2 <| one_smul R n ▸ mem_annihilator.1 ((Ideal.eq_top_iff_one _).1 H) n hn,
    fun H => H.symm ▸ annihilator_bot⟩
#align submodule.annihilator_eq_top_iff Submodule.annihilator_eq_top_iff

theorem annihilator_mono (h : N ≤ P) : P.annihilator ≤ N.annihilator := fun _ hrp =>
  mem_annihilator.2 fun n hn => mem_annihilator.1 hrp n <| h hn
#align submodule.annihilator_mono Submodule.annihilator_mono

theorem annihilator_iSup (ι : Sort w) (f : ι → Submodule R M) :
    annihilator (⨆ i, f i) = ⨅ i, annihilator (f i) :=
  le_antisymm (le_iInf fun _ => annihilator_mono <| le_iSup _ _) fun _ H =>
    mem_annihilator'.2 <|
      iSup_le fun i =>
        have := (mem_iInf _).1 H i
        mem_annihilator'.1 this
#align submodule.annihilator_supr Submodule.annihilator_iSup

theorem smul_mem_smul {r} {n} (hr : r ∈ I) (hn : n ∈ N) : r • n ∈ I • N :=
  apply_mem_map₂ _ hr hn
#align submodule.smul_mem_smul Submodule.smul_mem_smul

theorem smul_le {P : Submodule R M} : I • N ≤ P ↔ ∀ r ∈ I, ∀ n ∈ N, r • n ∈ P :=
  map₂_le
#align submodule.smul_le Submodule.smul_le

@[simp, norm_cast]
lemma coe_set_smul : (I : Set R) • N = I • N :=
  Submodule.set_smul_eq_of_le _ _ _
    (fun _ _ hr hx => smul_mem_smul hr hx)
    (smul_le.mpr fun _ hr _ hx => mem_set_smul_of_mem_mem hr hx)

@[elab_as_elim]
theorem smul_induction_on {p : M → Prop} {x} (H : x ∈ I • N) (Hb : ∀ r ∈ I, ∀ n ∈ N, p (r • n))
    (H1 : ∀ x y, p x → p y → p (x + y)) : p x := by
  have H0 : p 0 := by simpa only [zero_smul] using Hb 0 I.zero_mem 0 N.zero_mem
  refine Submodule.iSup_induction (x := x) _ H ?_ H0 H1
  rintro ⟨i, hi⟩ m ⟨j, hj, hj'⟩
  rw [← hj']
  exact Hb _ hi _ hj
#align submodule.smul_induction_on Submodule.smul_induction_on

/-- Dependent version of `Submodule.smul_induction_on`. -/
@[elab_as_elim]
theorem smul_induction_on' {x : M} (hx : x ∈ I • N) {p : ∀ x, x ∈ I • N → Prop}
    (Hb : ∀ (r : R) (hr : r ∈ I) (n : M) (hn : n ∈ N), p (r • n) (smul_mem_smul hr hn))
    (H1 : ∀ x hx y hy, p x hx → p y hy → p (x + y) (Submodule.add_mem _ ‹_› ‹_›)) : p x hx := by
  refine' Exists.elim _ fun (h : x ∈ I • N) (H : p x h) => H
  exact
    smul_induction_on hx (fun a ha x hx => ⟨_, Hb _ ha _ hx⟩) fun x y ⟨_, hx⟩ ⟨_, hy⟩ =>
      ⟨_, H1 _ _ _ _ hx hy⟩
#align submodule.smul_induction_on' Submodule.smul_induction_on'

theorem mem_smul_span_singleton {I : Ideal R} {m : M} {x : M} :
    x ∈ I • span R ({m} : Set M) ↔ ∃ y ∈ I, y • m = x :=
  ⟨fun hx =>
    smul_induction_on hx
      (fun r hri n hnm =>
        let ⟨s, hs⟩ := mem_span_singleton.1 hnm
        ⟨r * s, I.mul_mem_right _ hri, hs ▸ mul_smul r s m⟩)
      fun m1 m2 ⟨y1, hyi1, hy1⟩ ⟨y2, hyi2, hy2⟩ =>
      ⟨y1 + y2, I.add_mem hyi1 hyi2, by rw [add_smul, hy1, hy2]⟩,
    fun ⟨y, hyi, hy⟩ => hy ▸ smul_mem_smul hyi (subset_span <| Set.mem_singleton m)⟩
#align submodule.mem_smul_span_singleton Submodule.mem_smul_span_singleton

theorem smul_le_right : I • N ≤ N :=
  smul_le.2 fun r _ _ => N.smul_mem r
#align submodule.smul_le_right Submodule.smul_le_right

theorem smul_mono (hij : I ≤ J) (hnp : N ≤ P) : I • N ≤ J • P :=
  map₂_le_map₂ hij hnp
#align submodule.smul_mono Submodule.smul_mono

theorem smul_mono_left (h : I ≤ J) : I • N ≤ J • N :=
  map₂_le_map₂_left h
#align submodule.smul_mono_left Submodule.smul_mono_left

theorem smul_mono_right (h : N ≤ P) : I • N ≤ I • P :=
  map₂_le_map₂_right h
#align submodule.smul_mono_right Submodule.smul_mono_right

theorem map_le_smul_top (I : Ideal R) (f : R →ₗ[R] M) :
    Submodule.map f I ≤ I • (⊤ : Submodule R M) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [← mul_one y, ← smul_eq_mul, f.map_smul]
  exact smul_mem_smul hy mem_top
#align submodule.map_le_smul_top Submodule.map_le_smul_top

@[simp]
theorem annihilator_smul (N : Submodule R M) : annihilator N • N = ⊥ :=
  eq_bot_iff.2 (smul_le.2 fun _ => mem_annihilator.1)
#align submodule.annihilator_smul Submodule.annihilator_smul

@[simp]
theorem annihilator_mul (I : Ideal R) : annihilator I * I = ⊥ :=
  annihilator_smul I
#align submodule.annihilator_mul Submodule.annihilator_mul

@[simp]
theorem mul_annihilator (I : Ideal R) : I * annihilator I = ⊥ := by rw [mul_comm, annihilator_mul]
#align submodule.mul_annihilator Submodule.mul_annihilator

variable (I J N P)

@[simp]
theorem smul_bot : I • (⊥ : Submodule R M) = ⊥ :=
  map₂_bot_right _ _
#align submodule.smul_bot Submodule.smul_bot

@[simp]
theorem bot_smul : (⊥ : Ideal R) • N = ⊥ :=
  map₂_bot_left _ _
#align submodule.bot_smul Submodule.bot_smul

@[simp]
theorem top_smul : (⊤ : Ideal R) • N = N :=
  le_antisymm smul_le_right fun r hri => one_smul R r ▸ smul_mem_smul mem_top hri
#align submodule.top_smul Submodule.top_smul

theorem smul_sup : I • (N ⊔ P) = I • N ⊔ I • P :=
  map₂_sup_right _ _ _ _
#align submodule.smul_sup Submodule.smul_sup

theorem sup_smul : (I ⊔ J) • N = I • N ⊔ J • N :=
  map₂_sup_left _ _ _ _
#align submodule.sup_smul Submodule.sup_smul

protected theorem smul_assoc : (I • J) • N = I • J • N :=
  le_antisymm
    (smul_le.2 fun _ hrsij t htn =>
      smul_induction_on hrsij
        (fun r hr s hs =>
          (@smul_eq_mul R _ r s).symm ▸ smul_smul r s t ▸ smul_mem_smul hr (smul_mem_smul hs htn))
        fun x y => (add_smul x y t).symm ▸ Submodule.add_mem _)
    (smul_le.2 fun r hr _ hsn =>
      suffices J • N ≤ Submodule.comap (r • (LinearMap.id : M →ₗ[R] M)) ((I • J) • N) from this hsn
      smul_le.2 fun s hs n hn =>
        show r • s • n ∈ (I • J) • N from mul_smul r s n ▸ smul_mem_smul (smul_mem_smul hr hs) hn)
#align submodule.smul_assoc Submodule.smul_assoc

theorem smul_inf_le (M₁ M₂ : Submodule R M) : I • (M₁ ⊓ M₂) ≤ I • M₁ ⊓ I • M₂ :=
  le_inf (Submodule.smul_mono_right inf_le_left) (Submodule.smul_mono_right inf_le_right)
#align submodule.smul_inf_le Submodule.smul_inf_le

theorem smul_iSup {ι : Sort*} {I : Ideal R} {t : ι → Submodule R M} : I • iSup t = ⨆ i, I • t i :=
  map₂_iSup_right _ _ _
#align submodule.smul_supr Submodule.smul_iSup

theorem smul_iInf_le {ι : Sort*} {I : Ideal R} {t : ι → Submodule R M} :
    I • iInf t ≤ ⨅ i, I • t i :=
  le_iInf fun _ => smul_mono_right (iInf_le _ _)
#align submodule.smul_infi_le Submodule.smul_iInf_le

variable (S : Set R) (T : Set M)

theorem span_smul_span : Ideal.span S • span R T = span R (⋃ (s ∈ S) (t ∈ T), {s • t}) :=
  (map₂_span_span _ _ _ _).trans <| congr_arg _ <| Set.image2_eq_iUnion _ _ _
#align submodule.span_smul_span Submodule.span_smul_span

theorem ideal_span_singleton_smul (r : R) (N : Submodule R M) :
    (Ideal.span {r} : Ideal R) • N = r • N := by
  have : span R (⋃ (t : M) (_ : t ∈ N), {r • t}) = r • N := by
    convert span_eq (r • N)
    exact (Set.image_eq_iUnion _ (N : Set M)).symm
  conv_lhs => rw [← span_eq N, span_smul_span]
  simpa
#align submodule.ideal_span_singleton_smul Submodule.ideal_span_singleton_smul

theorem mem_of_span_top_of_smul_mem (M' : Submodule R M) (s : Set R) (hs : Ideal.span s = ⊤) (x : M)
    (H : ∀ r : s, (r : R) • x ∈ M') : x ∈ M' := by
  suffices (⊤ : Ideal R) • span R ({x} : Set M) ≤ M' by
    rw [top_smul] at this
    exact this (subset_span (Set.mem_singleton x))
  rw [← hs, span_smul_span, span_le]
  simpa using H
#align submodule.mem_of_span_top_of_smul_mem Submodule.mem_of_span_top_of_smul_mem

/-- Given `s`, a generating set of `R`, to check that an `x : M` falls in a
submodule `M'` of `x`, we only need to show that `r ^ n • x ∈ M'` for some `n` for each `r : s`. -/
theorem mem_of_span_eq_top_of_smul_pow_mem (M' : Submodule R M) (s : Set R) (hs : Ideal.span s = ⊤)
    (x : M) (H : ∀ r : s, ∃ n : ℕ, ((r : R) ^ n : R) • x ∈ M') : x ∈ M' := by
  obtain ⟨s', hs₁, hs₂⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
  replace H : ∀ r : s', ∃ n : ℕ, ((r : R) ^ n : R) • x ∈ M' := fun r => H ⟨_, hs₁ r.2⟩
  choose n₁ n₂ using H
  let N := s'.attach.sup n₁
  have hs' := Ideal.span_pow_eq_top (s' : Set R) hs₂ N
  apply M'.mem_of_span_top_of_smul_mem _ hs'
  rintro ⟨_, r, hr, rfl⟩
  convert M'.smul_mem (r ^ (N - n₁ ⟨r, hr⟩)) (n₂ ⟨r, hr⟩) using 1
  simp only [Subtype.coe_mk, smul_smul, ← pow_add]
  rw [tsub_add_cancel_of_le (Finset.le_sup (s'.mem_attach _) : n₁ ⟨r, hr⟩ ≤ N)]
#align submodule.mem_of_span_eq_top_of_smul_pow_mem Submodule.mem_of_span_eq_top_of_smul_pow_mem

variable {M' : Type w} [AddCommMonoid M'] [Module R M']

theorem map_smul'' (f : M →ₗ[R] M') : (I • N).map f = I • N.map f :=
  le_antisymm
      (map_le_iff_le_comap.2 <|
        smul_le.2 fun r hr n hn =>
          show f (r • n) ∈ I • N.map f from
            (f.map_smul r n).symm ▸ smul_mem_smul hr (mem_map_of_mem hn)) <|
    smul_le.2 fun r hr _ hn =>
      let ⟨p, hp, hfp⟩ := mem_map.1 hn
      hfp ▸ f.map_smul r p ▸ mem_map_of_mem (smul_mem_smul hr hp)
#align submodule.map_smul'' Submodule.map_smul''

variable {I}

theorem mem_smul_span {s : Set M} {x : M} :
    x ∈ I • Submodule.span R s ↔ x ∈ Submodule.span R (⋃ (a ∈ I) (b ∈ s), ({a • b} : Set M)) := by
  rw [← I.span_eq, Submodule.span_smul_span, I.span_eq]
  rfl
#align submodule.mem_smul_span Submodule.mem_smul_span

variable (I)

/-- If `x` is an `I`-multiple of the submodule spanned by `f '' s`,
then we can write `x` as an `I`-linear combination of the elements of `f '' s`. -/
theorem mem_ideal_smul_span_iff_exists_sum {ι : Type*} (f : ι → M) (x : M) :
    x ∈ I • span R (Set.range f) ↔
      ∃ (a : ι →₀ R) (_ : ∀ i, a i ∈ I), (a.sum fun i c => c • f i) = x := by
  constructor; swap
  · rintro ⟨a, ha, rfl⟩
    exact Submodule.sum_mem _ fun c _ => smul_mem_smul (ha c) <| subset_span <| Set.mem_range_self _
  refine' fun hx => span_induction (mem_smul_span.mp hx) _ _ _ _
  · simp only [Set.mem_iUnion, Set.mem_range, Set.mem_singleton_iff]
    rintro x ⟨y, hy, x, ⟨i, rfl⟩, rfl⟩
    refine' ⟨Finsupp.single i y, fun j => _, _⟩
    · letI := Classical.decEq ι
      rw [Finsupp.single_apply]
      split_ifs
      · assumption
      · exact I.zero_mem
    refine' @Finsupp.sum_single_index ι R M _ _ i _ (fun i y => y • f i) _
    simp
  · exact ⟨0, fun _ => I.zero_mem, Finsupp.sum_zero_index⟩
  · rintro x y ⟨ax, hax, rfl⟩ ⟨ay, hay, rfl⟩
    refine' ⟨ax + ay, fun i => I.add_mem (hax i) (hay i), Finsupp.sum_add_index' _ _⟩ <;> intros <;>
      simp only [zero_smul, add_smul]
  · rintro c x ⟨a, ha, rfl⟩
    refine' ⟨c • a, fun i => I.mul_mem_left c (ha i), _⟩
    rw [Finsupp.sum_smul_index, Finsupp.smul_sum] <;> intros <;> simp only [zero_smul, mul_smul]
#align submodule.mem_ideal_smul_span_iff_exists_sum Submodule.mem_ideal_smul_span_iff_exists_sum

theorem mem_ideal_smul_span_iff_exists_sum' {ι : Type*} (s : Set ι) (f : ι → M) (x : M) :
    x ∈ I • span R (f '' s) ↔ ∃ (a : s →₀ R) (_ : ∀ i, a i ∈ I), (a.sum fun i c => c • f i) = x :=
  by rw [← Submodule.mem_ideal_smul_span_iff_exists_sum, ← Set.image_eq_range]
#align submodule.mem_ideal_smul_span_iff_exists_sum' Submodule.mem_ideal_smul_span_iff_exists_sum'

theorem mem_smul_top_iff (N : Submodule R M) (x : N) :
    x ∈ I • (⊤ : Submodule R N) ↔ (x : M) ∈ I • N := by
  change _ ↔ N.subtype x ∈ I • N
  have : Submodule.map N.subtype (I • ⊤) = I • N := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  rw [← this]
  exact (Function.Injective.mem_set_image N.injective_subtype).symm
#align submodule.mem_smul_top_iff Submodule.mem_smul_top_iff

@[simp]
theorem smul_comap_le_comap_smul (f : M →ₗ[R] M') (S : Submodule R M') (I : Ideal R) :
    I • S.comap f ≤ (I • S).comap f := by
  refine' Submodule.smul_le.mpr fun r hr x hx => _
  rw [Submodule.mem_comap] at hx ⊢
  rw [f.map_smul]
  exact Submodule.smul_mem_smul hr hx
#align submodule.smul_comap_le_comap_smul Submodule.smul_comap_le_comap_smul

end CommSemiring

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M]

variable {N N₁ N₂ P P₁ P₂ : Submodule R M}

/-- `N.colon P` is the ideal of all elements `r : R` such that `r • P ⊆ N`. -/
def colon (N P : Submodule R M) : Ideal R :=
  annihilator (P.map N.mkQ)
#align submodule.colon Submodule.colon

theorem mem_colon {r} : r ∈ N.colon P ↔ ∀ p ∈ P, r • p ∈ N :=
  mem_annihilator.trans
     ⟨fun H p hp => (Quotient.mk_eq_zero N).1 (H (Quotient.mk p) (mem_map_of_mem hp)),
       fun H _ ⟨p, hp, hpm⟩ => hpm ▸ (N.mkQ.map_smul r p ▸ (Quotient.mk_eq_zero N).2 <| H p hp)⟩
#align submodule.mem_colon Submodule.mem_colon

theorem mem_colon' {r} : r ∈ N.colon P ↔ P ≤ comap (r • (LinearMap.id : M →ₗ[R] M)) N :=
  mem_colon
#align submodule.mem_colon' Submodule.mem_colon'

theorem colon_mono (hn : N₁ ≤ N₂) (hp : P₁ ≤ P₂) : N₁.colon P₂ ≤ N₂.colon P₁ := fun _ hrnp =>
  mem_colon.2 fun p₁ hp₁ => hn <| mem_colon.1 hrnp p₁ <| hp hp₁
#align submodule.colon_mono Submodule.colon_mono

theorem iInf_colon_iSup (ι₁ : Sort w) (f : ι₁ → Submodule R M) (ι₂ : Sort x)
    (g : ι₂ → Submodule R M) : (⨅ i, f i).colon (⨆ j, g j) = ⨅ (i) (j), (f i).colon (g j) :=
  le_antisymm (le_iInf fun _ => le_iInf fun _ => colon_mono (iInf_le _ _) (le_iSup _ _)) fun _ H =>
    mem_colon'.2 <|
      iSup_le fun j =>
        map_le_iff_le_comap.1 <|
          le_iInf fun i =>
            map_le_iff_le_comap.2 <|
              mem_colon'.1 <|
                have := (mem_iInf _).1 H i
                have := (mem_iInf _).1 this j
                this
#align submodule.infi_colon_supr Submodule.iInf_colon_iSup

@[simp]
theorem mem_colon_singleton {N : Submodule R M} {x : M} {r : R} :
    r ∈ N.colon (Submodule.span R {x}) ↔ r • x ∈ N :=
  calc
    r ∈ N.colon (Submodule.span R {x}) ↔ ∀ a : R, r • a • x ∈ N := by
      simp [Submodule.mem_colon, Submodule.mem_span_singleton]
    _ ↔ r • x ∈ N := by simp_rw [fun (a : R) ↦ smul_comm r a x]; exact SetLike.forall_smul_mem_iff
#align submodule.mem_colon_singleton Submodule.mem_colon_singleton

@[simp]
theorem _root_.Ideal.mem_colon_singleton {I : Ideal R} {x r : R} :
    r ∈ I.colon (Ideal.span {x}) ↔ r * x ∈ I := by
  simp only [← Ideal.submodule_span_eq, Submodule.mem_colon_singleton, smul_eq_mul]
#align ideal.mem_colon_singleton Ideal.mem_colon_singleton

end CommRing

end Submodule

namespace Ideal

section Add

variable {R : Type u} [Semiring R]

@[simp]
theorem add_eq_sup {I J : Ideal R} : I + J = I ⊔ J :=
  rfl
#align ideal.add_eq_sup Ideal.add_eq_sup

@[simp]
theorem zero_eq_bot : (0 : Ideal R) = ⊥ :=
  rfl
#align ideal.zero_eq_bot Ideal.zero_eq_bot

@[simp]
theorem sum_eq_sup {ι : Type*} (s : Finset ι) (f : ι → Ideal R) : s.sum f = s.sup f :=
  rfl
#align ideal.sum_eq_sup Ideal.sum_eq_sup

end Add

section MulAndRadical

variable {R : Type u} {ι : Type*} [CommSemiring R]

variable {I J K L : Ideal R}

instance : Mul (Ideal R) :=
  ⟨(· • ·)⟩

@[simp]
theorem one_eq_top : (1 : Ideal R) = ⊤ := by erw [Submodule.one_eq_range, LinearMap.range_id]
#align ideal.one_eq_top Ideal.one_eq_top

theorem add_eq_one_iff : I + J = 1 ↔ ∃ i ∈ I, ∃ j ∈ J, i + j = 1 := by
  rw [one_eq_top, eq_top_iff_one, add_eq_sup, Submodule.mem_sup]

theorem mul_mem_mul {r s} (hr : r ∈ I) (hs : s ∈ J) : r * s ∈ I * J :=
  Submodule.smul_mem_smul hr hs
#align ideal.mul_mem_mul Ideal.mul_mem_mul

theorem mul_mem_mul_rev {r s} (hr : r ∈ I) (hs : s ∈ J) : s * r ∈ I * J :=
  mul_comm r s ▸ mul_mem_mul hr hs
#align ideal.mul_mem_mul_rev Ideal.mul_mem_mul_rev

theorem pow_mem_pow {x : R} (hx : x ∈ I) (n : ℕ) : x ^ n ∈ I ^ n :=
  Submodule.pow_mem_pow _ hx _
#align ideal.pow_mem_pow Ideal.pow_mem_pow

theorem prod_mem_prod {ι : Type*} {s : Finset ι} {I : ι → Ideal R} {x : ι → R} :
    (∀ i ∈ s, x i ∈ I i) → (∏ i in s, x i) ∈ ∏ i in s, I i := by
  classical
    refine Finset.induction_on s ?_ ?_
    · intro
      rw [Finset.prod_empty, Finset.prod_empty, one_eq_top]
      exact Submodule.mem_top
    · intro a s ha IH h
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact
        mul_mem_mul (h a <| Finset.mem_insert_self a s)
          (IH fun i hi => h i <| Finset.mem_insert_of_mem hi)
#align ideal.prod_mem_prod Ideal.prod_mem_prod

theorem mul_le : I * J ≤ K ↔ ∀ r ∈ I, ∀ s ∈ J, r * s ∈ K :=
  Submodule.smul_le
#align ideal.mul_le Ideal.mul_le

theorem mul_le_left : I * J ≤ J :=
  Ideal.mul_le.2 fun _ _ _ => J.mul_mem_left _
#align ideal.mul_le_left Ideal.mul_le_left

theorem mul_le_right : I * J ≤ I :=
  Ideal.mul_le.2 fun _ hr _ _ => I.mul_mem_right _ hr
#align ideal.mul_le_right Ideal.mul_le_right

@[simp]
theorem sup_mul_right_self : I ⊔ I * J = I :=
  sup_eq_left.2 Ideal.mul_le_right
#align ideal.sup_mul_right_self Ideal.sup_mul_right_self

@[simp]
theorem sup_mul_left_self : I ⊔ J * I = I :=
  sup_eq_left.2 Ideal.mul_le_left
#align ideal.sup_mul_left_self Ideal.sup_mul_left_self

@[simp]
theorem mul_right_self_sup : I * J ⊔ I = I :=
  sup_eq_right.2 Ideal.mul_le_right
#align ideal.mul_right_self_sup Ideal.mul_right_self_sup

@[simp]
theorem mul_left_self_sup : J * I ⊔ I = I :=
  sup_eq_right.2 Ideal.mul_le_left
#align ideal.mul_left_self_sup Ideal.mul_left_self_sup

variable (I J K)

protected theorem mul_comm : I * J = J * I :=
  le_antisymm (mul_le.2 fun _ hrI _ hsJ => mul_mem_mul_rev hsJ hrI)
    (mul_le.2 fun _ hrJ _ hsI => mul_mem_mul_rev hsI hrJ)
#align ideal.mul_comm Ideal.mul_comm

protected theorem mul_assoc : I * J * K = I * (J * K) :=
  Submodule.smul_assoc I J K
#align ideal.mul_assoc Ideal.mul_assoc

theorem span_mul_span (S T : Set R) : span S * span T = span (⋃ (s ∈ S) (t ∈ T), {s * t}) :=
  Submodule.span_smul_span S T
#align ideal.span_mul_span Ideal.span_mul_span

variable {I J K}

theorem span_mul_span' (S T : Set R) : span S * span T = span (S * T) := by
  unfold span
  rw [Submodule.span_mul_span]
#align ideal.span_mul_span' Ideal.span_mul_span'

theorem span_singleton_mul_span_singleton (r s : R) :
    span {r} * span {s} = (span {r * s} : Ideal R) := by
  unfold span
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]
#align ideal.span_singleton_mul_span_singleton Ideal.span_singleton_mul_span_singleton

theorem span_singleton_pow (s : R) (n : ℕ) : span {s} ^ n = (span {s ^ n} : Ideal R) := by
  induction' n with n ih; · simp [Set.singleton_one]
  simp only [pow_succ, ih, span_singleton_mul_span_singleton]
#align ideal.span_singleton_pow Ideal.span_singleton_pow

theorem mem_mul_span_singleton {x y : R} {I : Ideal R} : x ∈ I * span {y} ↔ ∃ z ∈ I, z * y = x :=
  Submodule.mem_smul_span_singleton
#align ideal.mem_mul_span_singleton Ideal.mem_mul_span_singleton

theorem mem_span_singleton_mul {x y : R} {I : Ideal R} : x ∈ span {y} * I ↔ ∃ z ∈ I, y * z = x := by
  simp only [mul_comm, mem_mul_span_singleton]
#align ideal.mem_span_singleton_mul Ideal.mem_span_singleton_mul

theorem le_span_singleton_mul_iff {x : R} {I J : Ideal R} :
    I ≤ span {x} * J ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI :=
  show (∀ {zI} (_ : zI ∈ I), zI ∈ span {x} * J) ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI by
    simp only [mem_span_singleton_mul]
#align ideal.le_span_singleton_mul_iff Ideal.le_span_singleton_mul_iff

theorem span_singleton_mul_le_iff {x : R} {I J : Ideal R} :
    span {x} * I ≤ J ↔ ∀ z ∈ I, x * z ∈ J := by
  simp only [mul_le, mem_span_singleton_mul, mem_span_singleton]
  constructor
  · intro h zI hzI
    exact h x (dvd_refl x) zI hzI
  · rintro h _ ⟨z, rfl⟩ zI hzI
    rw [mul_comm x z, mul_assoc]
    exact J.mul_mem_left _ (h zI hzI)
#align ideal.span_singleton_mul_le_iff Ideal.span_singleton_mul_le_iff

theorem span_singleton_mul_le_span_singleton_mul {x y : R} {I J : Ideal R} :
    span {x} * I ≤ span {y} * J ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zI = y * zJ := by
  simp only [span_singleton_mul_le_iff, mem_span_singleton_mul, eq_comm]
#align ideal.span_singleton_mul_le_span_singleton_mul Ideal.span_singleton_mul_le_span_singleton_mul

theorem span_singleton_mul_right_mono [IsDomain R] {x : R} (hx : x ≠ 0) :
    span {x} * I ≤ span {x} * J ↔ I ≤ J := by
  simp_rw [span_singleton_mul_le_span_singleton_mul, mul_right_inj' hx,
    exists_eq_right', SetLike.le_def]
#align ideal.span_singleton_mul_right_mono Ideal.span_singleton_mul_right_mono

theorem span_singleton_mul_left_mono [IsDomain R] {x : R} (hx : x ≠ 0) :
    I * span {x} ≤ J * span {x} ↔ I ≤ J := by
  simpa only [mul_comm I, mul_comm J] using span_singleton_mul_right_mono hx
#align ideal.span_singleton_mul_left_mono Ideal.span_singleton_mul_left_mono

theorem span_singleton_mul_right_inj [IsDomain R] {x : R} (hx : x ≠ 0) :
    span {x} * I = span {x} * J ↔ I = J := by
  simp only [le_antisymm_iff, span_singleton_mul_right_mono hx]
#align ideal.span_singleton_mul_right_inj Ideal.span_singleton_mul_right_inj

theorem span_singleton_mul_left_inj [IsDomain R] {x : R} (hx : x ≠ 0) :
    I * span {x} = J * span {x} ↔ I = J := by
  simp only [le_antisymm_iff, span_singleton_mul_left_mono hx]
#align ideal.span_singleton_mul_left_inj Ideal.span_singleton_mul_left_inj

theorem span_singleton_mul_right_injective [IsDomain R] {x : R} (hx : x ≠ 0) :
    Function.Injective ((span {x} : Ideal R) * ·) := fun _ _ =>
  (span_singleton_mul_right_inj hx).mp
#align ideal.span_singleton_mul_right_injective Ideal.span_singleton_mul_right_injective

theorem span_singleton_mul_left_injective [IsDomain R] {x : R} (hx : x ≠ 0) :
    Function.Injective fun I : Ideal R => I * span {x} := fun _ _ =>
  (span_singleton_mul_left_inj hx).mp
#align ideal.span_singleton_mul_left_injective Ideal.span_singleton_mul_left_injective

theorem eq_span_singleton_mul {x : R} (I J : Ideal R) :
    I = span {x} * J ↔ (∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI) ∧ ∀ z ∈ J, x * z ∈ I := by
  simp only [le_antisymm_iff, le_span_singleton_mul_iff, span_singleton_mul_le_iff]
#align ideal.eq_span_singleton_mul Ideal.eq_span_singleton_mul

theorem span_singleton_mul_eq_span_singleton_mul {x y : R} (I J : Ideal R) :
    span {x} * I = span {y} * J ↔
      (∀ zI ∈ I, ∃ zJ ∈ J, x * zI = y * zJ) ∧ ∀ zJ ∈ J, ∃ zI ∈ I, x * zI = y * zJ :=
  by simp only [le_antisymm_iff, span_singleton_mul_le_span_singleton_mul, eq_comm]
#align ideal.span_singleton_mul_eq_span_singleton_mul Ideal.span_singleton_mul_eq_span_singleton_mul

theorem prod_span {ι : Type*} (s : Finset ι) (I : ι → Set R) :
    (∏ i in s, Ideal.span (I i)) = Ideal.span (∏ i in s, I i) :=
  Submodule.prod_span s I
#align ideal.prod_span Ideal.prod_span

theorem prod_span_singleton {ι : Type*} (s : Finset ι) (I : ι → R) :
    (∏ i in s, Ideal.span ({I i} : Set R)) = Ideal.span {∏ i in s, I i} :=
  Submodule.prod_span_singleton s I
#align ideal.prod_span_singleton Ideal.prod_span_singleton

@[simp]
theorem multiset_prod_span_singleton (m : Multiset R) :
    (m.map fun x => Ideal.span {x}).prod = Ideal.span ({Multiset.prod m} : Set R) :=
  Multiset.induction_on m (by simp) fun a m ih => by
    simp only [Multiset.map_cons, Multiset.prod_cons, ih, ← Ideal.span_singleton_mul_span_singleton]
#align ideal.multiset_prod_span_singleton Ideal.multiset_prod_span_singleton

theorem finset_inf_span_singleton {ι : Type*} (s : Finset ι) (I : ι → R)
    (hI : Set.Pairwise (↑s) (IsCoprime on I)) :
    (s.inf fun i => Ideal.span ({I i} : Set R)) = Ideal.span {∏ i in s, I i} := by
  ext x
  simp only [Submodule.mem_finset_inf, Ideal.mem_span_singleton]
  exact ⟨Finset.prod_dvd_of_coprime hI, fun h i hi => (Finset.dvd_prod_of_mem _ hi).trans h⟩
#align ideal.finset_inf_span_singleton Ideal.finset_inf_span_singleton

theorem iInf_span_singleton {ι : Type*} [Fintype ι] {I : ι → R}
    (hI : ∀ (i j) (_ : i ≠ j), IsCoprime (I i) (I j)) :
    ⨅ i, span ({I i} : Set R) = span {∏ i, I i} := by
  rw [← Finset.inf_univ_eq_iInf, finset_inf_span_singleton]
  rwa [Finset.coe_univ, Set.pairwise_univ]
#align ideal.infi_span_singleton Ideal.iInf_span_singleton

theorem iInf_span_singleton_natCast {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    {I : ι → ℕ} (hI : Pairwise fun i j => (I i).Coprime (I j)) :
    ⨅ (i : ι), span {(I i : R)} = span {((∏ i : ι, I i : ℕ) : R)} := by
  rw [iInf_span_singleton, Nat.cast_prod]
  exact fun i j h ↦ (hI h).cast

theorem sup_eq_top_iff_isCoprime {R : Type*} [CommSemiring R] (x y : R) :
    span ({x} : Set R) ⊔ span {y} = ⊤ ↔ IsCoprime x y := by
  rw [eq_top_iff_one, Submodule.mem_sup]
  constructor
  · rintro ⟨u, hu, v, hv, h1⟩
    rw [mem_span_singleton'] at hu hv
    rw [← hu.choose_spec, ← hv.choose_spec] at h1
    exact ⟨_, _, h1⟩
  · exact fun ⟨u, v, h1⟩ =>
      ⟨_, mem_span_singleton'.mpr ⟨_, rfl⟩, _, mem_span_singleton'.mpr ⟨_, rfl⟩, h1⟩
#align ideal.sup_eq_top_iff_is_coprime Ideal.sup_eq_top_iff_isCoprime

theorem mul_le_inf : I * J ≤ I ⊓ J :=
  mul_le.2 fun r hri s hsj => ⟨I.mul_mem_right s hri, J.mul_mem_left r hsj⟩
#align ideal.mul_le_inf Ideal.mul_le_inf

theorem multiset_prod_le_inf {s : Multiset (Ideal R)} : s.prod ≤ s.inf := by
  classical
    refine' s.induction_on _ _
    · rw [Multiset.inf_zero]
      exact le_top
    intro a s ih
    rw [Multiset.prod_cons, Multiset.inf_cons]
    exact le_trans mul_le_inf (inf_le_inf le_rfl ih)
#align ideal.multiset_prod_le_inf Ideal.multiset_prod_le_inf

theorem prod_le_inf {s : Finset ι} {f : ι → Ideal R} : s.prod f ≤ s.inf f :=
  multiset_prod_le_inf
#align ideal.prod_le_inf Ideal.prod_le_inf

theorem mul_eq_inf_of_coprime (h : I ⊔ J = ⊤) : I * J = I ⊓ J :=
  le_antisymm mul_le_inf fun r ⟨hri, hrj⟩ =>
    let ⟨s, hsi, t, htj, hst⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 h)
    mul_one r ▸
      hst ▸
        (mul_add r s t).symm ▸ Ideal.add_mem (I * J) (mul_mem_mul_rev hsi hrj) (mul_mem_mul hri htj)
#align ideal.mul_eq_inf_of_coprime Ideal.mul_eq_inf_of_coprime

theorem sup_mul_eq_of_coprime_left (h : I ⊔ J = ⊤) : I ⊔ J * K = I ⊔ K :=
  le_antisymm (sup_le_sup_left mul_le_left _) fun i hi => by
    rw [eq_top_iff_one] at h; rw [Submodule.mem_sup] at h hi ⊢
    obtain ⟨i1, hi1, j, hj, h⟩ := h; obtain ⟨i', hi', k, hk, hi⟩ := hi
    refine' ⟨_, add_mem hi' (mul_mem_right k _ hi1), _, mul_mem_mul hj hk, _⟩
    rw [add_assoc, ← add_mul, h, one_mul, hi]
#align ideal.sup_mul_eq_of_coprime_left Ideal.sup_mul_eq_of_coprime_left

theorem sup_mul_eq_of_coprime_right (h : I ⊔ K = ⊤) : I ⊔ J * K = I ⊔ J := by
  rw [mul_comm]
  exact sup_mul_eq_of_coprime_left h
#align ideal.sup_mul_eq_of_coprime_right Ideal.sup_mul_eq_of_coprime_right

theorem mul_sup_eq_of_coprime_left (h : I ⊔ J = ⊤) : I * K ⊔ J = K ⊔ J := by
  rw [sup_comm] at h
  rw [sup_comm, sup_mul_eq_of_coprime_left h, sup_comm]
#align ideal.mul_sup_eq_of_coprime_left Ideal.mul_sup_eq_of_coprime_left

theorem mul_sup_eq_of_coprime_right (h : K ⊔ J = ⊤) : I * K ⊔ J = I ⊔ J := by
  rw [sup_comm] at h
  rw [sup_comm, sup_mul_eq_of_coprime_right h, sup_comm]
#align ideal.mul_sup_eq_of_coprime_right Ideal.mul_sup_eq_of_coprime_right

theorem sup_prod_eq_top {s : Finset ι} {J : ι → Ideal R} (h : ∀ i, i ∈ s → I ⊔ J i = ⊤) :
    (I ⊔ ∏ i in s, J i) = ⊤ :=
  Finset.prod_induction _ (fun J => I ⊔ J = ⊤)
    (fun J K hJ hK => (sup_mul_eq_of_coprime_left hJ).trans hK)
    (by simp_rw [one_eq_top, sup_top_eq]) h
#align ideal.sup_prod_eq_top Ideal.sup_prod_eq_top

theorem sup_iInf_eq_top {s : Finset ι} {J : ι → Ideal R} (h : ∀ i, i ∈ s → I ⊔ J i = ⊤) :
    (I ⊔ ⨅ i ∈ s, J i) = ⊤ :=
  eq_top_iff.mpr <|
    le_of_eq_of_le (sup_prod_eq_top h).symm <|
      sup_le_sup_left (le_of_le_of_eq prod_le_inf <| Finset.inf_eq_iInf _ _) _
#align ideal.sup_infi_eq_top Ideal.sup_iInf_eq_top

theorem prod_sup_eq_top {s : Finset ι} {J : ι → Ideal R} (h : ∀ i, i ∈ s → J i ⊔ I = ⊤) :
    (∏ i in s, J i) ⊔ I = ⊤ :=
  sup_comm.trans (sup_prod_eq_top fun i hi => sup_comm.trans <| h i hi)
#align ideal.prod_sup_eq_top Ideal.prod_sup_eq_top

theorem iInf_sup_eq_top {s : Finset ι} {J : ι → Ideal R} (h : ∀ i, i ∈ s → J i ⊔ I = ⊤) :
    (⨅ i ∈ s, J i) ⊔ I = ⊤ :=
  sup_comm.trans (sup_iInf_eq_top fun i hi => sup_comm.trans <| h i hi)
#align ideal.infi_sup_eq_top Ideal.iInf_sup_eq_top

theorem sup_pow_eq_top {n : ℕ} (h : I ⊔ J = ⊤) : I ⊔ J ^ n = ⊤ := by
  rw [← Finset.card_range n, ← Finset.prod_const]
  exact sup_prod_eq_top fun _ _ => h
#align ideal.sup_pow_eq_top Ideal.sup_pow_eq_top

theorem pow_sup_eq_top {n : ℕ} (h : I ⊔ J = ⊤) : I ^ n ⊔ J = ⊤ := by
  rw [← Finset.card_range n, ← Finset.prod_const]
  exact prod_sup_eq_top fun _ _ => h
#align ideal.pow_sup_eq_top Ideal.pow_sup_eq_top

theorem pow_sup_pow_eq_top {m n : ℕ} (h : I ⊔ J = ⊤) : I ^ m ⊔ J ^ n = ⊤ :=
  sup_pow_eq_top (pow_sup_eq_top h)
#align ideal.pow_sup_pow_eq_top Ideal.pow_sup_pow_eq_top

variable (I)

-- @[simp] -- Porting note: simp can prove this
theorem mul_bot : I * ⊥ = ⊥ := by simp
#align ideal.mul_bot Ideal.mul_bot

-- @[simp] -- Porting note: simp can prove this
theorem bot_mul : ⊥ * I = ⊥ := by simp
#align ideal.bot_mul Ideal.bot_mul

@[simp]
theorem mul_top : I * ⊤ = I :=
  Ideal.mul_comm ⊤ I ▸ Submodule.top_smul I
#align ideal.mul_top Ideal.mul_top

@[simp]
theorem top_mul : ⊤ * I = I :=
  Submodule.top_smul I
#align ideal.top_mul Ideal.top_mul

variable {I}

theorem mul_mono (hik : I ≤ K) (hjl : J ≤ L) : I * J ≤ K * L :=
  Submodule.smul_mono hik hjl
#align ideal.mul_mono Ideal.mul_mono

theorem mul_mono_left (h : I ≤ J) : I * K ≤ J * K :=
  Submodule.smul_mono_left h
#align ideal.mul_mono_left Ideal.mul_mono_left

theorem mul_mono_right (h : J ≤ K) : I * J ≤ I * K :=
  Submodule.smul_mono_right h
#align ideal.mul_mono_right Ideal.mul_mono_right

variable (I J K)

theorem mul_sup : I * (J ⊔ K) = I * J ⊔ I * K :=
  Submodule.smul_sup I J K
#align ideal.mul_sup Ideal.mul_sup

theorem sup_mul : (I ⊔ J) * K = I * K ⊔ J * K :=
  Submodule.sup_smul I J K
#align ideal.sup_mul Ideal.sup_mul

variable {I J K}

theorem pow_le_pow_right {m n : ℕ} (h : m ≤ n) : I ^ n ≤ I ^ m := by
  cases' Nat.exists_eq_add_of_le h with k hk
  rw [hk, pow_add]
  exact le_trans mul_le_inf inf_le_left
#align ideal.pow_le_pow_right Ideal.pow_le_pow_right

theorem pow_le_self {n : ℕ} (hn : n ≠ 0) : I ^ n ≤ I :=
  calc
    I ^ n ≤ I ^ 1 := pow_le_pow_right (Nat.pos_of_ne_zero hn)
    _ = I := pow_one _
#align ideal.pow_le_self Ideal.pow_le_self

theorem pow_right_mono {I J : Ideal R} (e : I ≤ J) (n : ℕ) : I ^ n ≤ J ^ n := by
  induction' n with _ hn
  · rw [pow_zero, pow_zero]
  · rw [pow_succ, pow_succ]
    exact Ideal.mul_mono e hn
#align ideal.pow_right_mono Ideal.pow_right_mono

@[simp]
theorem mul_eq_bot {R : Type*} [CommSemiring R] [NoZeroDivisors R] {I J : Ideal R} :
    I * J = ⊥ ↔ I = ⊥ ∨ J = ⊥ :=
  ⟨fun hij =>
    or_iff_not_imp_left.mpr fun I_ne_bot =>
      J.eq_bot_iff.mpr fun j hj =>
        let ⟨i, hi, ne0⟩ := I.ne_bot_iff.mp I_ne_bot
        Or.resolve_left (mul_eq_zero.mp ((I * J).eq_bot_iff.mp hij _ (mul_mem_mul hi hj))) ne0,
    fun h => by cases' h with h h <;> rw [← Ideal.mul_bot, h, Ideal.mul_comm]⟩
#align ideal.mul_eq_bot Ideal.mul_eq_bot

instance {R : Type*} [CommSemiring R] [NoZeroDivisors R] : NoZeroDivisors (Ideal R) where
  eq_zero_or_eq_zero_of_mul_eq_zero := mul_eq_bot.1

instance {R : Type*} [CommSemiring R] {S : Type*} [CommRing S] [Algebra R S]
    [NoZeroSMulDivisors R S] {I : Ideal S} : NoZeroSMulDivisors R I :=
  Submodule.noZeroSMulDivisors (Submodule.restrictScalars R I)

/-- A product of ideals in an integral domain is zero if and only if one of the terms is zero. -/
@[simp]
lemma multiset_prod_eq_bot {R : Type*} [CommRing R] [IsDomain R] {s : Multiset (Ideal R)} :
    s.prod = ⊥ ↔ ⊥ ∈ s :=
  Multiset.prod_eq_zero_iff

/-- A product of ideals in an integral domain is zero if and only if one of the terms is zero. -/
@[deprecated multiset_prod_eq_bot] -- since 26 Dec 2023
theorem prod_eq_bot {R : Type*} [CommRing R] [IsDomain R] {s : Multiset (Ideal R)} :
    s.prod = ⊥ ↔ ∃ I ∈ s, I = ⊥ := by
  simp
#align ideal.prod_eq_bot Ideal.prod_eq_bot

theorem span_pair_mul_span_pair (w x y z : R) :
    (span {w, x} : Ideal R) * span {y, z} = span {w * y, w * z, x * y, x * z} := by
  simp_rw [span_insert, sup_mul, mul_sup, span_singleton_mul_span_singleton, sup_assoc]
#align ideal.span_pair_mul_span_pair Ideal.span_pair_mul_span_pair

theorem isCoprime_iff_codisjoint : IsCoprime I J ↔ Codisjoint I J := by
  rw [IsCoprime, codisjoint_iff]
  constructor
  · rintro ⟨x, y, hxy⟩
    rw [eq_top_iff_one]
    apply (show x * I + y * J ≤ I ⊔ J from
      sup_le (mul_le_left.trans le_sup_left) (mul_le_left.trans le_sup_right))
    rw [hxy]
    simp only [one_eq_top, Submodule.mem_top]
  · intro h
    refine' ⟨1, 1, _⟩
    simpa only [one_eq_top, top_mul, Submodule.add_eq_sup]

theorem isCoprime_iff_add : IsCoprime I J ↔ I + J = 1 := by
  rw [isCoprime_iff_codisjoint, codisjoint_iff, add_eq_sup, one_eq_top]

theorem isCoprime_iff_exists : IsCoprime I J ↔ ∃ i ∈ I, ∃ j ∈ J, i + j = 1 := by
  rw [← add_eq_one_iff, isCoprime_iff_add]

theorem isCoprime_iff_sup_eq : IsCoprime I J ↔ I ⊔ J = ⊤ := by
  rw [isCoprime_iff_codisjoint, codisjoint_iff]

open List in
theorem isCoprime_tfae : TFAE [IsCoprime I J, Codisjoint I J, I + J = 1,
    ∃ i ∈ I, ∃ j ∈ J, i + j = 1, I ⊔ J = ⊤] := by
  rw [← isCoprime_iff_codisjoint, ← isCoprime_iff_add, ← isCoprime_iff_exists,
      ← isCoprime_iff_sup_eq]
  simp

theorem _root_.IsCoprime.codisjoint (h : IsCoprime I J) : Codisjoint I J :=
  isCoprime_iff_codisjoint.mp h

theorem _root_.IsCoprime.add_eq (h : IsCoprime I J) : I + J = 1 := isCoprime_iff_add.mp h

theorem _root_.IsCoprime.exists (h : IsCoprime I J) : ∃ i ∈ I, ∃ j ∈ J, i + j = 1 :=
  isCoprime_iff_exists.mp h

theorem _root_.IsCoprime.sup_eq (h : IsCoprime I J) : I ⊔ J = ⊤ := isCoprime_iff_sup_eq.mp h

theorem isCoprime_span_singleton_iff (x y : R) :
    IsCoprime (span <| singleton x) (span <| singleton y) ↔ IsCoprime x y := by
  simp_rw [isCoprime_iff_codisjoint, codisjoint_iff, eq_top_iff_one, mem_span_singleton_sup,
    mem_span_singleton]
  constructor
  · rintro ⟨a, _, ⟨b, rfl⟩, e⟩; exact ⟨a, b, mul_comm b y ▸ e⟩
  · rintro ⟨a, b, e⟩; exact ⟨a, _, ⟨b, rfl⟩, mul_comm y b ▸ e⟩

theorem isCoprime_biInf {J : ι → Ideal R} {s : Finset ι}
    (hf : ∀ j ∈ s, IsCoprime I (J j)) : IsCoprime I (⨅ j ∈ s, J j) := by
  classical
  simp_rw [isCoprime_iff_add] at *
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert i s _ hs =>
      rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
      set K := ⨅ j ∈ s, J j
      calc
        1 = I + K            := (hs fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)).symm
        _ = I + K*(I + J i)  := by rw [hf i (Finset.mem_insert_self i s), mul_one]
        _ = (1+K)*I + K*J i  := by ring
        _ ≤ I + K ⊓ J i      := add_le_add mul_le_left mul_le_inf

/-- The radical of an ideal `I` consists of the elements `r` such that `r ^ n ∈ I` for some `n`. -/
def radical (I : Ideal R) : Ideal R where
  carrier := { r | ∃ n : ℕ, r ^ n ∈ I }
  zero_mem' := ⟨1, (pow_one (0 : R)).symm ▸ I.zero_mem⟩
  add_mem' :=
  fun {x y} ⟨m, hxmi⟩ ⟨n, hyni⟩ =>
    ⟨m + n,
      (add_pow x y (m + n)).symm ▸ I.sum_mem <|
        show
          ∀ c ∈ Finset.range (Nat.succ (m + n)), x ^ c * y ^ (m + n - c) * Nat.choose (m + n) c ∈ I
          from fun c _ =>
          Or.casesOn (le_total c m) (fun hcm =>
              I.mul_mem_right _ <|
                I.mul_mem_left _ <|
                  Nat.add_comm n m ▸
                    (add_tsub_assoc_of_le hcm n).symm ▸
                      (pow_add y n (m - c)).symm ▸ I.mul_mem_right _ hyni) (fun hmc =>
               I.mul_mem_right _ <|
                I.mul_mem_right _ <|
                  add_tsub_cancel_of_le hmc ▸ (pow_add x m (c - m)).symm ▸ I.mul_mem_right _ hxmi)⟩
-- Porting note: Below gives weird errors without `by exact`
  smul_mem' {r s} := by exact fun ⟨n, h⟩ ↦ ⟨n, (mul_pow r s n).symm ▸ I.mul_mem_left (r ^ n) h⟩
#align ideal.radical Ideal.radical

/-- An ideal is radical if it contains its radical. -/
def IsRadical (I : Ideal R) : Prop :=
  I.radical ≤ I
#align ideal.is_radical Ideal.IsRadical

theorem le_radical : I ≤ radical I := fun r hri => ⟨1, (pow_one r).symm ▸ hri⟩
#align ideal.le_radical Ideal.le_radical

/-- An ideal is radical iff it is equal to its radical. -/
theorem radical_eq_iff : I.radical = I ↔ I.IsRadical := by
  rw [le_antisymm_iff, and_iff_left le_radical, IsRadical]
#align ideal.radical_eq_iff Ideal.radical_eq_iff

alias ⟨_, IsRadical.radical⟩ := radical_eq_iff
#align ideal.is_radical.radical Ideal.IsRadical.radical

variable (R)

theorem radical_top : (radical ⊤ : Ideal R) = ⊤ :=
  (eq_top_iff_one _).2 ⟨0, Submodule.mem_top⟩
#align ideal.radical_top Ideal.radical_top

variable {R}

theorem radical_mono (H : I ≤ J) : radical I ≤ radical J := fun _ ⟨n, hrni⟩ => ⟨n, H hrni⟩
#align ideal.radical_mono Ideal.radical_mono

variable (I)

theorem radical_isRadical : (radical I).IsRadical := fun r ⟨n, k, hrnki⟩ =>
  ⟨n * k, (pow_mul r n k).symm ▸ hrnki⟩
#align ideal.radical_is_radical Ideal.radical_isRadical

@[simp]
theorem radical_idem : radical (radical I) = radical I :=
  (radical_isRadical I).radical
#align ideal.radical_idem Ideal.radical_idem

variable {I}

theorem IsRadical.radical_le_iff (hJ : J.IsRadical) : I.radical ≤ J ↔ I ≤ J :=
  ⟨le_trans le_radical, fun h => hJ.radical ▸ radical_mono h⟩
#align ideal.is_radical.radical_le_iff Ideal.IsRadical.radical_le_iff

theorem radical_le_radical_iff : radical I ≤ radical J ↔ I ≤ radical J :=
  (radical_isRadical J).radical_le_iff
#align ideal.radical_le_radical_iff Ideal.radical_le_radical_iff

theorem radical_eq_top : radical I = ⊤ ↔ I = ⊤ :=
  ⟨fun h =>
    (eq_top_iff_one _).2 <|
      let ⟨n, hn⟩ := (eq_top_iff_one _).1 h
      @one_pow R _ n ▸ hn,
    fun h => h.symm ▸ radical_top R⟩
#align ideal.radical_eq_top Ideal.radical_eq_top

theorem IsPrime.isRadical (H : IsPrime I) : I.IsRadical := fun _ ⟨n, hrni⟩ =>
  H.mem_of_pow_mem n hrni
#align ideal.is_prime.is_radical Ideal.IsPrime.isRadical

theorem IsPrime.radical (H : IsPrime I) : radical I = I :=
  IsRadical.radical H.isRadical
#align ideal.is_prime.radical Ideal.IsPrime.radical

variable (I J)

theorem radical_sup : radical (I ⊔ J) = radical (radical I ⊔ radical J) :=
  le_antisymm (radical_mono <| sup_le_sup le_radical le_radical) <|
    radical_le_radical_iff.2 <| sup_le (radical_mono le_sup_left) (radical_mono le_sup_right)
#align ideal.radical_sup Ideal.radical_sup

theorem radical_inf : radical (I ⊓ J) = radical I ⊓ radical J :=
  le_antisymm (le_inf (radical_mono inf_le_left) (radical_mono inf_le_right))
    fun r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩ =>
    ⟨m + n, (pow_add r m n).symm ▸ I.mul_mem_right _ hrm,
      (pow_add r m n).symm ▸ J.mul_mem_left _ hrn⟩
#align ideal.radical_inf Ideal.radical_inf

theorem radical_mul : radical (I * J) = radical I ⊓ radical J := by
  refine le_antisymm ?_ fun r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩ =>
    ⟨m + n, (pow_add r m n).symm ▸ mul_mem_mul hrm hrn⟩
  have := radical_mono <| @mul_le_inf _ _ I J
  simp_rw [radical_inf I J] at this
  assumption
#align ideal.radical_mul Ideal.radical_mul

variable {I J}

theorem IsPrime.radical_le_iff (hJ : IsPrime J) : I.radical ≤ J ↔ I ≤ J :=
  IsRadical.radical_le_iff hJ.isRadical
#align ideal.is_prime.radical_le_iff Ideal.IsPrime.radical_le_iff

theorem radical_eq_sInf (I : Ideal R) : radical I = sInf { J : Ideal R | I ≤ J ∧ IsPrime J } :=
  le_antisymm (le_sInf fun J hJ ↦ hJ.2.radical_le_iff.2 hJ.1) fun r hr ↦
    by_contradiction fun hri ↦
      let ⟨m, (hrm : r ∉ radical m), him, hm⟩ :=
        zorn_nonempty_partialOrder₀ { K : Ideal R | r ∉ radical K }
          (fun c hc hcc y hyc =>
            ⟨sSup c, fun ⟨n, hrnc⟩ =>
              let ⟨y, hyc, hrny⟩ := (Submodule.mem_sSup_of_directed ⟨y, hyc⟩ hcc.directedOn).1 hrnc
              hc hyc ⟨n, hrny⟩,
              fun z => le_sSup⟩)
          I hri
      have : ∀ x ∉ m, r ∈ radical (m ⊔ span {x}) := fun x hxm =>
        by_contradiction fun hrmx =>
          hxm <|
            hm (m ⊔ span {x}) hrmx le_sup_left ▸
              (le_sup_right : _ ≤ m ⊔ span {x}) (subset_span <| Set.mem_singleton _)
      have : IsPrime m :=
        ⟨by rintro rfl; rw [radical_top] at hrm; exact hrm trivial, fun {x y} hxym =>
          or_iff_not_imp_left.2 fun hxm =>
            by_contradiction fun hym =>
              let ⟨n, hrn⟩ := this _ hxm
              let ⟨p, hpm, q, hq, hpqrn⟩ := Submodule.mem_sup.1 hrn
              let ⟨c, hcxq⟩ := mem_span_singleton'.1 hq
              let ⟨k, hrk⟩ := this _ hym
              let ⟨f, hfm, g, hg, hfgrk⟩ := Submodule.mem_sup.1 hrk
              let ⟨d, hdyg⟩ := mem_span_singleton'.1 hg
              hrm
                ⟨n + k, by
                  rw [pow_add, ← hpqrn, ← hcxq, ← hfgrk, ← hdyg, add_mul, mul_add (c * x),
                      mul_assoc c x (d * y), mul_left_comm x, ← mul_assoc];
                    refine'
                      m.add_mem (m.mul_mem_right _ hpm)
                        (m.add_mem (m.mul_mem_left _ hfm) (m.mul_mem_left _ hxym))⟩⟩
    hrm <|
      this.radical.symm ▸ (sInf_le ⟨him, this⟩ : sInf { J : Ideal R | I ≤ J ∧ IsPrime J } ≤ m) hr
#align ideal.radical_eq_Inf Ideal.radical_eq_sInf

theorem isRadical_bot_of_noZeroDivisors {R} [CommSemiring R] [NoZeroDivisors R] :
    (⊥ : Ideal R).IsRadical := fun _ hx => hx.recOn fun _ hn => pow_eq_zero hn
#align ideal.is_radical_bot_of_no_zero_divisors Ideal.isRadical_bot_of_noZeroDivisors

@[simp]
theorem radical_bot_of_noZeroDivisors {R : Type u} [CommSemiring R] [NoZeroDivisors R] :
    radical (⊥ : Ideal R) = ⊥ :=
  eq_bot_iff.2 isRadical_bot_of_noZeroDivisors
#align ideal.radical_bot_of_no_zero_divisors Ideal.radical_bot_of_noZeroDivisors

instance : IdemCommSemiring (Ideal R) :=
  inferInstance

variable (R)

theorem top_pow (n : ℕ) : (⊤ ^ n : Ideal R) = ⊤ :=
  Nat.recOn n one_eq_top fun n ih => by rw [pow_succ, ih, top_mul]
#align ideal.top_pow Ideal.top_pow

variable {R}

variable (I)

theorem radical_pow (n : ℕ) (H : n > 0) : radical (I ^ n) = radical I :=
  Nat.recOn n (Not.elim (by decide))
    (fun n ih H =>
      Or.casesOn (lt_or_eq_of_le <| Nat.le_of_lt_succ H)
        (fun H =>
          calc
            radical (I ^ (n + 1)) = radical I ⊓ radical (I ^ n) := by
              rw [pow_succ]
              exact radical_mul _ _
            _ = radical I ⊓ radical I := by rw [ih H]
            _ = radical I := inf_idem
            )
        fun H => H ▸ (pow_one I).symm ▸ rfl)
    H
#align ideal.radical_pow Ideal.radical_pow

theorem IsPrime.mul_le {I J P : Ideal R} (hp : IsPrime P) : I * J ≤ P ↔ I ≤ P ∨ J ≤ P := by
  rw [or_comm, Ideal.mul_le]
  simp_rw [hp.mul_mem_iff_mem_or_mem, SetLike.le_def, ← forall_or_left, or_comm, forall_or_left]
#align ideal.is_prime.mul_le Ideal.IsPrime.mul_le

theorem IsPrime.inf_le {I J P : Ideal R} (hp : IsPrime P) : I ⊓ J ≤ P ↔ I ≤ P ∨ J ≤ P :=
  ⟨fun h ↦ hp.mul_le.1 <| mul_le_inf.trans h, fun h ↦ h.elim inf_le_left.trans inf_le_right.trans⟩
#align ideal.is_prime.inf_le Ideal.IsPrime.inf_le

theorem IsPrime.multiset_prod_le {s : Multiset (Ideal R)} {P : Ideal R} (hp : IsPrime P) :
    s.prod ≤ P ↔ ∃ I ∈ s, I ≤ P :=
  s.induction_on (by simp [hp.ne_top]) fun I s ih ↦ by simp [hp.mul_le, ih]
#align ideal.is_prime.multiset_prod_le Ideal.IsPrime.multiset_prod_le

theorem IsPrime.multiset_prod_map_le {s : Multiset ι} (f : ι → Ideal R) {P : Ideal R}
    (hp : IsPrime P) : (s.map f).prod ≤ P ↔ ∃ i ∈ s, f i ≤ P := by
  simp_rw [hp.multiset_prod_le, Multiset.mem_map, exists_exists_and_eq_and]
#align ideal.is_prime.multiset_prod_map_le Ideal.IsPrime.multiset_prod_map_le

theorem IsPrime.prod_le {s : Finset ι} {f : ι → Ideal R} {P : Ideal R} (hp : IsPrime P) :
    s.prod f ≤ P ↔ ∃ i ∈ s, f i ≤ P :=
  hp.multiset_prod_map_le f
#align ideal.is_prime.prod_le Ideal.IsPrime.prod_le

theorem IsPrime.inf_le' {s : Finset ι} {f : ι → Ideal R} {P : Ideal R} (hp : IsPrime P) :
    s.inf f ≤ P ↔ ∃ i ∈ s, f i ≤ P :=
  ⟨fun h ↦ hp.prod_le.1 <| prod_le_inf.trans h, fun ⟨_, his, hip⟩ ↦ (Finset.inf_le his).trans hip⟩
#align ideal.is_prime.inf_le' Ideal.IsPrime.inf_le'

-- Porting note: needed to add explicit coercions (· : Set R).
theorem subset_union {R : Type u} [Ring R] {I J K : Ideal R} :
    (I : Set R) ⊆ J ∪ K ↔ I ≤ J ∨ I ≤ K :=
  AddSubgroupClass.subset_union
#align ideal.subset_union Ideal.subset_union

theorem subset_union_prime' {R : Type u} [CommRing R] {s : Finset ι} {f : ι → Ideal R} {a b : ι}
    (hp : ∀ i ∈ s, IsPrime (f i)) {I : Ideal R} :
    ((I : Set R) ⊆ f a ∪ f b ∪ ⋃ i ∈ (↑s : Set ι), f i) ↔ I ≤ f a ∨ I ≤ f b ∨ ∃ i ∈ s, I ≤ f i := by
  suffices
    ((I : Set R) ⊆ f a ∪ f b ∪ ⋃ i ∈ (↑s : Set ι), f i) → I ≤ f a ∨ I ≤ f b ∨ ∃ i ∈ s, I ≤ f i from
    ⟨this, fun h =>
      Or.casesOn h
        (fun h =>
          Set.Subset.trans h <|
            Set.Subset.trans (Set.subset_union_left _ _) (Set.subset_union_left _ _))
        fun h =>
        Or.casesOn h
          (fun h =>
            Set.Subset.trans h <|
              Set.Subset.trans (Set.subset_union_right _ _) (Set.subset_union_left _ _))
          fun ⟨i, his, hi⟩ => by
          refine' Set.Subset.trans hi <| Set.Subset.trans _ <| Set.subset_union_right _ _;
            exact Set.subset_biUnion_of_mem (u := fun x ↦ (f x : Set R)) (Finset.mem_coe.2 his)⟩
  generalize hn : s.card = n; intro h
  induction' n with n ih generalizing a b s
  · clear hp
    rw [Finset.card_eq_zero] at hn
    subst hn
    rw [Finset.coe_empty, Set.biUnion_empty, Set.union_empty, subset_union] at h
    simpa only [exists_prop, Finset.not_mem_empty, false_and_iff, exists_false, or_false_iff]
  classical
    replace hn : ∃ (i : ι) (t : Finset ι), i ∉ t ∧ insert i t = s ∧ t.card = n :=
      Finset.card_eq_succ.1 hn
    rcases hn with ⟨i, t, hit, rfl, hn⟩
    replace hp : IsPrime (f i) ∧ ∀ x ∈ t, IsPrime (f x) := (t.forall_mem_insert _ _).1 hp
    by_cases Ht : ∃ j ∈ t, f j ≤ f i
    · obtain ⟨j, hjt, hfji⟩ : ∃ j ∈ t, f j ≤ f i := Ht
      obtain ⟨u, hju, rfl⟩ : ∃ u, j ∉ u ∧ insert j u = t :=
        ⟨t.erase j, t.not_mem_erase j, Finset.insert_erase hjt⟩
      have hp' : ∀ k ∈ insert i u, IsPrime (f k) := by
        rw [Finset.forall_mem_insert] at hp ⊢
        exact ⟨hp.1, hp.2.2⟩
      have hiu : i ∉ u := mt Finset.mem_insert_of_mem hit
      have hn' : (insert i u).card = n := by
        rwa [Finset.card_insert_of_not_mem] at hn ⊢
        exacts [hiu, hju]
      have h' : (I : Set R) ⊆ f a ∪ f b ∪ ⋃ k ∈ (↑(insert i u) : Set ι), f k := by
        rw [Finset.coe_insert] at h ⊢
        rw [Finset.coe_insert] at h
        simp only [Set.biUnion_insert] at h ⊢
        rw [← Set.union_assoc (f i : Set R)] at h
        erw [Set.union_eq_self_of_subset_right hfji] at h
        exact h
      specialize ih hp' hn' h'
      refine' ih.imp id (Or.imp id (Exists.imp fun k => _))
      exact And.imp (fun hk => Finset.insert_subset_insert i (Finset.subset_insert j u) hk) id
    by_cases Ha : f a ≤ f i
    · have h' : (I : Set R) ⊆ f i ∪ f b ∪ ⋃ j ∈ (↑t : Set ι), f j := by
        rw [Finset.coe_insert, Set.biUnion_insert, ← Set.union_assoc,
          Set.union_right_comm (f a : Set R)] at h
        erw [Set.union_eq_self_of_subset_left Ha] at h
        exact h
      specialize ih hp.2 hn h'
      right
      rcases ih with (ih | ih | ⟨k, hkt, ih⟩)
      · exact Or.inr ⟨i, Finset.mem_insert_self i t, ih⟩
      · exact Or.inl ih
      · exact Or.inr ⟨k, Finset.mem_insert_of_mem hkt, ih⟩
    by_cases Hb : f b ≤ f i
    · have h' : (I : Set R) ⊆ f a ∪ f i ∪ ⋃ j ∈ (↑t : Set ι), f j := by
        rw [Finset.coe_insert, Set.biUnion_insert, ← Set.union_assoc,
          Set.union_assoc (f a : Set R)] at h
        erw [Set.union_eq_self_of_subset_left Hb] at h
        exact h
      specialize ih hp.2 hn h'
      rcases ih with (ih | ih | ⟨k, hkt, ih⟩)
      · exact Or.inl ih
      · exact Or.inr (Or.inr ⟨i, Finset.mem_insert_self i t, ih⟩)
      · exact Or.inr (Or.inr ⟨k, Finset.mem_insert_of_mem hkt, ih⟩)
    by_cases Hi : I ≤ f i
    · exact Or.inr (Or.inr ⟨i, Finset.mem_insert_self i t, Hi⟩)
    have : ¬I ⊓ f a ⊓ f b ⊓ t.inf f ≤ f i := by
      simp only [hp.1.inf_le, hp.1.inf_le', not_or]
      exact ⟨⟨⟨Hi, Ha⟩, Hb⟩, Ht⟩
    rcases Set.not_subset.1 this with ⟨r, ⟨⟨⟨hrI, hra⟩, hrb⟩, hr⟩, hri⟩
    by_cases HI : (I : Set R) ⊆ f a ∪ f b ∪ ⋃ j ∈ (↑t : Set ι), f j
    · specialize ih hp.2 hn HI
      rcases ih with (ih | ih | ⟨k, hkt, ih⟩)
      · left
        exact ih
      · right
        left
        exact ih
      · right
        right
        exact ⟨k, Finset.mem_insert_of_mem hkt, ih⟩
    exfalso
    rcases Set.not_subset.1 HI with ⟨s, hsI, hs⟩
    rw [Finset.coe_insert, Set.biUnion_insert] at h
    have hsi : s ∈ f i := ((h hsI).resolve_left (mt Or.inl hs)).resolve_right (mt Or.inr hs)
    rcases h (I.add_mem hrI hsI) with (⟨ha | hb⟩ | hi | ht)
    · exact hs (Or.inl <| Or.inl <| add_sub_cancel' r s ▸ (f a).sub_mem ha hra)
    · exact hs (Or.inl <| Or.inr <| add_sub_cancel' r s ▸ (f b).sub_mem hb hrb)
    · exact hri (add_sub_cancel r s ▸ (f i).sub_mem hi hsi)
    · rw [Set.mem_iUnion₂] at ht
      rcases ht with ⟨j, hjt, hj⟩
      simp only [Finset.inf_eq_iInf, SetLike.mem_coe, Submodule.mem_iInf] at hr
      exact hs (Or.inr <| Set.mem_biUnion hjt <| add_sub_cancel' r s ▸ (f j).sub_mem hj <| hr j hjt)
#align ideal.subset_union_prime' Ideal.subset_union_prime'

/-- Prime avoidance. Atiyah-Macdonald 1.11, Eisenbud 3.3, Stacks 00DS, Matsumura Ex.1.6. -/
theorem subset_union_prime {R : Type u} [CommRing R] {s : Finset ι} {f : ι → Ideal R} (a b : ι)
    (hp : ∀ i ∈ s, i ≠ a → i ≠ b → IsPrime (f i)) {I : Ideal R} :
    ((I : Set R) ⊆ ⋃ i ∈ (↑s : Set ι), f i) ↔ ∃ i ∈ s, I ≤ f i :=
  suffices ((I : Set R) ⊆ ⋃ i ∈ (↑s : Set ι), f i) → ∃ i, i ∈ s ∧ I ≤ f i by
    have aux := fun h => (bex_def.2 <| this h)
    simp_rw [exists_prop] at aux
    refine ⟨aux, fun ⟨i, his, hi⟩ ↦ Set.Subset.trans hi ?_⟩
    apply Set.subset_biUnion_of_mem (show i ∈ (↑s : Set ι) from his)
  fun h : (I : Set R) ⊆ ⋃ i ∈ (↑s : Set ι), f i => by
  classical
    by_cases has : a ∈ s
    · obtain ⟨t, hat, rfl⟩ : ∃ t, a ∉ t ∧ insert a t = s :=
        ⟨s.erase a, Finset.not_mem_erase a s, Finset.insert_erase has⟩
      by_cases hbt : b ∈ t
      · obtain ⟨u, hbu, rfl⟩ : ∃ u, b ∉ u ∧ insert b u = t :=
          ⟨t.erase b, Finset.not_mem_erase b t, Finset.insert_erase hbt⟩
        have hp' : ∀ i ∈ u, IsPrime (f i) := by
          intro i hiu
          refine' hp i (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hiu)) _ _ <;>
              rintro rfl <;>
            solve_by_elim only [Finset.mem_insert_of_mem, *]
        rw [Finset.coe_insert, Finset.coe_insert, Set.biUnion_insert, Set.biUnion_insert, ←
          Set.union_assoc, subset_union_prime' hp'] at h
        rwa [Finset.exists_mem_insert, Finset.exists_mem_insert]
      · have hp' : ∀ j ∈ t, IsPrime (f j) := by
          intro j hj
          refine' hp j (Finset.mem_insert_of_mem hj) _ _ <;> rintro rfl <;>
            solve_by_elim only [Finset.mem_insert_of_mem, *]
        rw [Finset.coe_insert, Set.biUnion_insert, ← Set.union_self (f a : Set R),
          subset_union_prime' hp', ← or_assoc, or_self_iff] at h
        rwa [Finset.exists_mem_insert]
    · by_cases hbs : b ∈ s
      · obtain ⟨t, hbt, rfl⟩ : ∃ t, b ∉ t ∧ insert b t = s :=
          ⟨s.erase b, Finset.not_mem_erase b s, Finset.insert_erase hbs⟩
        have hp' : ∀ j ∈ t, IsPrime (f j) := by
          intro j hj
          refine' hp j (Finset.mem_insert_of_mem hj) _ _ <;> rintro rfl <;>
            solve_by_elim only [Finset.mem_insert_of_mem, *]
        rw [Finset.coe_insert, Set.biUnion_insert, ← Set.union_self (f b : Set R),
          subset_union_prime' hp', ← or_assoc, or_self_iff] at h
        rwa [Finset.exists_mem_insert]
      rcases s.eq_empty_or_nonempty with hse | hsne
      · subst hse
        rw [Finset.coe_empty, Set.biUnion_empty, Set.subset_empty_iff] at h
        have : (I : Set R) ≠ ∅ := Set.Nonempty.ne_empty (Set.nonempty_of_mem I.zero_mem)
        exact absurd h this
      · cases' hsne.bex with i his
        obtain ⟨t, _, rfl⟩ : ∃ t, i ∉ t ∧ insert i t = s :=
          ⟨s.erase i, Finset.not_mem_erase i s, Finset.insert_erase his⟩
        have hp' : ∀ j ∈ t, IsPrime (f j) := by
          intro j hj
          refine' hp j (Finset.mem_insert_of_mem hj) _ _ <;> rintro rfl <;>
            solve_by_elim only [Finset.mem_insert_of_mem, *]
        rw [Finset.coe_insert, Set.biUnion_insert, ← Set.union_self (f i : Set R),
          subset_union_prime' hp', ← or_assoc, or_self_iff] at h
        rwa [Finset.exists_mem_insert]
#align ideal.subset_union_prime Ideal.subset_union_prime

section Dvd

/-- If `I` divides `J`, then `I` contains `J`.

In a Dedekind domain, to divide and contain are equivalent, see `Ideal.dvd_iff_le`.
-/
theorem le_of_dvd {I J : Ideal R} : I ∣ J → J ≤ I
  | ⟨_, h⟩ => h.symm ▸ le_trans mul_le_inf inf_le_left
#align ideal.le_of_dvd Ideal.le_of_dvd

@[simp]
theorem isUnit_iff {I : Ideal R} : IsUnit I ↔ I = ⊤ :=
  isUnit_iff_dvd_one.trans
    ((@one_eq_top R _).symm ▸
      ⟨fun h => eq_top_iff.mpr (Ideal.le_of_dvd h), fun h => ⟨⊤, by rw [mul_top, h]⟩⟩)
#align ideal.is_unit_iff Ideal.isUnit_iff

instance uniqueUnits : Unique (Ideal R)ˣ where
  default := 1
  uniq u := Units.ext (show (u : Ideal R) = 1 by rw [isUnit_iff.mp u.isUnit, one_eq_top])
#align ideal.unique_units Ideal.uniqueUnits

end Dvd

end MulAndRadical

section MapAndComap

variable {R : Type u} {S : Type v}

section Semiring

variable {F : Type*} [Semiring R] [Semiring S]

variable [FunLike F R S] [rc : RingHomClass F R S]

variable (f : F)

variable {I J : Ideal R} {K L : Ideal S}

/-- `I.map f` is the span of the image of the ideal `I` under `f`, which may be bigger than
  the image itself. -/
def map (I : Ideal R) : Ideal S :=
  span (f '' I)
#align ideal.map Ideal.map

/-- `I.comap f` is the preimage of `I` under `f`. -/
def comap (I : Ideal S) : Ideal R where
  carrier := f ⁻¹' I
  add_mem' {x y} hx hy := by
    simp only [Set.mem_preimage, SetLike.mem_coe, map_add f] at hx hy ⊢
    exact add_mem hx hy
  zero_mem' := by simp only [Set.mem_preimage, map_zero, SetLike.mem_coe, Submodule.zero_mem]
  smul_mem' c x hx := by
    simp only [smul_eq_mul, Set.mem_preimage, map_mul, SetLike.mem_coe] at *
    exact mul_mem_left I _ hx
#align ideal.comap Ideal.comap

-- Porting note: new theorem
-- @[simp] -- Porting note: TODO enable simp after the port
theorem coe_comap (I : Ideal S) : (comap f I : Set R) = f ⁻¹' I := rfl

variable {f}

theorem map_mono (h : I ≤ J) : map f I ≤ map f J :=
  span_mono <| Set.image_subset _ h
#align ideal.map_mono Ideal.map_mono

theorem mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : x ∈ I) : f x ∈ map f I :=
  subset_span ⟨x, h, rfl⟩
#align ideal.mem_map_of_mem Ideal.mem_map_of_mem

theorem apply_coe_mem_map (f : F) (I : Ideal R) (x : I) : f x ∈ I.map f :=
  mem_map_of_mem f x.2
#align ideal.apply_coe_mem_map Ideal.apply_coe_mem_map

theorem map_le_iff_le_comap : map f I ≤ K ↔ I ≤ comap f K :=
  span_le.trans Set.image_subset_iff
#align ideal.map_le_iff_le_comap Ideal.map_le_iff_le_comap

@[simp]
theorem mem_comap {x} : x ∈ comap f K ↔ f x ∈ K :=
  Iff.rfl
#align ideal.mem_comap Ideal.mem_comap

theorem comap_mono (h : K ≤ L) : comap f K ≤ comap f L :=
  Set.preimage_mono fun _ hx => h hx
#align ideal.comap_mono Ideal.comap_mono

variable (f)

theorem comap_ne_top (hK : K ≠ ⊤) : comap f K ≠ ⊤ :=
  (ne_top_iff_one _).2 <| by rw [mem_comap, map_one]; exact (ne_top_iff_one _).1 hK
#align ideal.comap_ne_top Ideal.comap_ne_top

variable {G : Type*} [FunLike G S R] [rcg : RingHomClass G S R]

theorem map_le_comap_of_inv_on (g : G) (I : Ideal R) (hf : Set.LeftInvOn g f I) :
    I.map f ≤ I.comap g := by
  refine' Ideal.span_le.2 _
  rintro x ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_comap, hf hx]
  exact hx
#align ideal.map_le_comap_of_inv_on Ideal.map_le_comap_of_inv_on

theorem comap_le_map_of_inv_on (g : G) (I : Ideal S) (hf : Set.LeftInvOn g f (f ⁻¹' I)) :
    I.comap f ≤ I.map g := fun x (hx : f x ∈ I) => hf hx ▸ Ideal.mem_map_of_mem g hx
#align ideal.comap_le_map_of_inv_on Ideal.comap_le_map_of_inv_on

/-- The `Ideal` version of `Set.image_subset_preimage_of_inverse`. -/
theorem map_le_comap_of_inverse (g : G) (I : Ideal R) (h : Function.LeftInverse g f) :
    I.map f ≤ I.comap g :=
  map_le_comap_of_inv_on _ _ _ <| h.leftInvOn _
#align ideal.map_le_comap_of_inverse Ideal.map_le_comap_of_inverse

/-- The `Ideal` version of `Set.preimage_subset_image_of_inverse`. -/
theorem comap_le_map_of_inverse (g : G) (I : Ideal S) (h : Function.LeftInverse g f) :
    I.comap f ≤ I.map g :=
  comap_le_map_of_inv_on _ _ _ <| h.leftInvOn _
#align ideal.comap_le_map_of_inverse Ideal.comap_le_map_of_inverse

instance IsPrime.comap [hK : K.IsPrime] : (comap f K).IsPrime :=
  ⟨comap_ne_top _ hK.1, fun {x y} => by simp only [mem_comap, map_mul]; apply hK.2⟩
#align ideal.is_prime.comap Ideal.IsPrime.comap

variable (I J K L)

theorem map_top : map f ⊤ = ⊤ :=
  (eq_top_iff_one _).2 <| subset_span ⟨1, trivial, map_one f⟩
#align ideal.map_top Ideal.map_top

theorem gc_map_comap : GaloisConnection (Ideal.map f) (Ideal.comap f) := fun _ _ =>
  Ideal.map_le_iff_le_comap
#align ideal.gc_map_comap Ideal.gc_map_comap

@[simp]
theorem comap_id : I.comap (RingHom.id R) = I :=
  Ideal.ext fun _ => Iff.rfl
#align ideal.comap_id Ideal.comap_id

@[simp]
theorem map_id : I.map (RingHom.id R) = I :=
  (gc_map_comap (RingHom.id R)).l_unique GaloisConnection.id comap_id
#align ideal.map_id Ideal.map_id

theorem comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f : R →+* S) (g : S →+* T) :
    (I.comap g).comap f = I.comap (g.comp f) :=
  rfl
#align ideal.comap_comap Ideal.comap_comap

theorem map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R →+* S) (g : S →+* T) :
    (I.map f).map g = I.map (g.comp f) :=
  ((gc_map_comap f).compose (gc_map_comap g)).l_unique (gc_map_comap (g.comp f)) fun _ =>
    comap_comap _ _
#align ideal.map_map Ideal.map_map

theorem map_span (f : F) (s : Set R) : map f (span s) = span (f '' s) := by
  refine (Submodule.span_eq_of_le _ ?_ ?_).symm
  · rintro _ ⟨x, hx, rfl⟩; exact mem_map_of_mem f (subset_span hx)
  · rw [map_le_iff_le_comap, span_le, coe_comap, ← Set.image_subset_iff]
    exact subset_span
#align ideal.map_span Ideal.map_span

variable {f I J K L}

theorem map_le_of_le_comap : I ≤ K.comap f → I.map f ≤ K :=
  (gc_map_comap f).l_le
#align ideal.map_le_of_le_comap Ideal.map_le_of_le_comap

theorem le_comap_of_map_le : I.map f ≤ K → I ≤ K.comap f :=
  (gc_map_comap f).le_u
#align ideal.le_comap_of_map_le Ideal.le_comap_of_map_le

theorem le_comap_map : I ≤ (I.map f).comap f :=
  (gc_map_comap f).le_u_l _
#align ideal.le_comap_map Ideal.le_comap_map

theorem map_comap_le : (K.comap f).map f ≤ K :=
  (gc_map_comap f).l_u_le _
#align ideal.map_comap_le Ideal.map_comap_le

@[simp]
theorem comap_top : (⊤ : Ideal S).comap f = ⊤ :=
  (gc_map_comap f).u_top
#align ideal.comap_top Ideal.comap_top

@[simp]
theorem comap_eq_top_iff {I : Ideal S} : I.comap f = ⊤ ↔ I = ⊤ :=
  ⟨fun h => I.eq_top_iff_one.mpr (map_one f ▸ mem_comap.mp ((I.comap f).eq_top_iff_one.mp h)),
    fun h => by rw [h, comap_top]⟩
#align ideal.comap_eq_top_iff Ideal.comap_eq_top_iff

@[simp]
theorem map_bot : (⊥ : Ideal R).map f = ⊥ :=
  (gc_map_comap f).l_bot
#align ideal.map_bot Ideal.map_bot

variable (f I J K L)

@[simp]
theorem map_comap_map : ((I.map f).comap f).map f = I.map f :=
  (gc_map_comap f).l_u_l_eq_l I
#align ideal.map_comap_map Ideal.map_comap_map

@[simp]
theorem comap_map_comap : ((K.comap f).map f).comap f = K.comap f :=
  (gc_map_comap f).u_l_u_eq_u K
#align ideal.comap_map_comap Ideal.comap_map_comap

theorem map_sup : (I ⊔ J).map f = I.map f ⊔ J.map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup
#align ideal.map_sup Ideal.map_sup

theorem comap_inf : comap f (K ⊓ L) = comap f K ⊓ comap f L :=
  rfl
#align ideal.comap_inf Ideal.comap_inf

variable {ι : Sort*}

theorem map_iSup (K : ι → Ideal R) : (iSup K).map f = ⨆ i, (K i).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup
#align ideal.map_supr Ideal.map_iSup

theorem comap_iInf (K : ι → Ideal S) : (iInf K).comap f = ⨅ i, (K i).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_iInf
#align ideal.comap_infi Ideal.comap_iInf

theorem map_sSup (s : Set (Ideal R)) : (sSup s).map f = ⨆ I ∈ s, (I : Ideal R).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sSup
#align ideal.map_Sup Ideal.map_sSup

theorem comap_sInf (s : Set (Ideal S)) : (sInf s).comap f = ⨅ I ∈ s, (I : Ideal S).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_sInf
#align ideal.comap_Inf Ideal.comap_sInf

theorem comap_sInf' (s : Set (Ideal S)) : (sInf s).comap f = ⨅ I ∈ comap f '' s, I :=
  _root_.trans (comap_sInf f s) (by rw [iInf_image])
#align ideal.comap_Inf' Ideal.comap_sInf'

theorem comap_isPrime [H : IsPrime K] : IsPrime (comap f K) :=
  ⟨comap_ne_top f H.ne_top, fun {x y} h => H.mem_or_mem <| by rwa [mem_comap, map_mul] at h⟩
#align ideal.comap_is_prime Ideal.comap_isPrime

variable {I J K L}

theorem map_inf_le : map f (I ⊓ J) ≤ map f I ⊓ map f J :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).monotone_l.map_inf_le _ _
#align ideal.map_inf_le Ideal.map_inf_le

theorem le_comap_sup : comap f K ⊔ comap f L ≤ comap f (K ⊔ L) :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).monotone_u.le_map_sup _ _
#align ideal.le_comap_sup Ideal.le_comap_sup

@[simp]
theorem smul_top_eq_map {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (algebraMap R S)).restrictScalars R := by
  refine'
    le_antisymm (Submodule.smul_le.mpr fun r hr y _ => _) fun x hx =>
      Submodule.span_induction hx _ _ _ _
  · rw [Algebra.smul_def]
    exact mul_mem_right _ _ (mem_map_of_mem _ hr)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← mul_one (algebraMap R S x), ← Algebra.smul_def]
    exact Submodule.smul_mem_smul hx Submodule.mem_top
  · exact Submodule.zero_mem _
  · intro x y
    exact Submodule.add_mem _
  intro a x hx
  refine' Submodule.smul_induction_on hx _ _
  · intro r hr s _
    rw [smul_comm]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro x y hx hy
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
#align ideal.smul_top_eq_map Ideal.smul_top_eq_map

@[simp]
theorem coe_restrictScalars {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    (I : Ideal S) : (I.restrictScalars R : Set S) = ↑I :=
  rfl
#align ideal.coe_restrict_scalars Ideal.coe_restrictScalars

/-- The smallest `S`-submodule that contains all `x ∈ I * y ∈ J`
is also the smallest `R`-submodule that does so. -/
@[simp]
theorem restrictScalars_mul {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (I J : Ideal S) : (I * J).restrictScalars R = I.restrictScalars R * J.restrictScalars R :=
  le_antisymm
    (fun _ hx =>
      Submodule.mul_induction_on hx (fun _ hx _ hy => Submodule.mul_mem_mul hx hy) fun _ _ =>
        Submodule.add_mem _)
    (Submodule.mul_le.mpr fun _ hx _ hy => Ideal.mul_mem_mul hx hy)
#align ideal.restrict_scalars_mul Ideal.restrictScalars_mul

section Surjective

variable (hf : Function.Surjective f)

open Function

theorem map_comap_of_surjective (I : Ideal S) : map f (comap f I) = I :=
  le_antisymm (map_le_iff_le_comap.2 le_rfl) fun s hsi =>
    let ⟨r, hfrs⟩ := hf s
    hfrs ▸ (mem_map_of_mem f <| show f r ∈ I from hfrs.symm ▸ hsi)
#align ideal.map_comap_of_surjective Ideal.map_comap_of_surjective

/-- `map` and `comap` are adjoint, and the composition `map f ∘ comap f` is the
  identity -/
def giMapComap : GaloisInsertion (map f) (comap f) :=
  GaloisInsertion.monotoneIntro (gc_map_comap f).monotone_u (gc_map_comap f).monotone_l
    (fun _ => le_comap_map) (map_comap_of_surjective _ hf)
#align ideal.gi_map_comap Ideal.giMapComap

theorem map_surjective_of_surjective : Surjective (map f) :=
  (giMapComap f hf).l_surjective
#align ideal.map_surjective_of_surjective Ideal.map_surjective_of_surjective

theorem comap_injective_of_surjective : Injective (comap f) :=
  (giMapComap f hf).u_injective
#align ideal.comap_injective_of_surjective Ideal.comap_injective_of_surjective

theorem map_sup_comap_of_surjective (I J : Ideal S) : (I.comap f ⊔ J.comap f).map f = I ⊔ J :=
  (giMapComap f hf).l_sup_u _ _
#align ideal.map_sup_comap_of_surjective Ideal.map_sup_comap_of_surjective

theorem map_iSup_comap_of_surjective (K : ι → Ideal S) : (⨆ i, (K i).comap f).map f = iSup K :=
  (giMapComap f hf).l_iSup_u _
#align ideal.map_supr_comap_of_surjective Ideal.map_iSup_comap_of_surjective

theorem map_inf_comap_of_surjective (I J : Ideal S) : (I.comap f ⊓ J.comap f).map f = I ⊓ J :=
  (giMapComap f hf).l_inf_u _ _
#align ideal.map_inf_comap_of_surjective Ideal.map_inf_comap_of_surjective

theorem map_iInf_comap_of_surjective (K : ι → Ideal S) : (⨅ i, (K i).comap f).map f = iInf K :=
  (giMapComap f hf).l_iInf_u _
#align ideal.map_infi_comap_of_surjective Ideal.map_iInf_comap_of_surjective

theorem mem_image_of_mem_map_of_surjective {I : Ideal R} {y} (H : y ∈ map f I) : y ∈ f '' I :=
  Submodule.span_induction H (fun _ => id) ⟨0, I.zero_mem, map_zero f⟩
    (fun _ _ ⟨x1, hx1i, hxy1⟩ ⟨x2, hx2i, hxy2⟩ =>
      ⟨x1 + x2, I.add_mem hx1i hx2i, hxy1 ▸ hxy2 ▸ map_add f _ _⟩)
    fun c _ ⟨x, hxi, hxy⟩ =>
    let ⟨d, hdc⟩ := hf c
    ⟨d * x, I.mul_mem_left _ hxi, hdc ▸ hxy ▸ map_mul f _ _⟩
#align ideal.mem_image_of_mem_map_of_surjective Ideal.mem_image_of_mem_map_of_surjective

theorem mem_map_iff_of_surjective {I : Ideal R} {y} : y ∈ map f I ↔ ∃ x, x ∈ I ∧ f x = y :=
  ⟨fun h => (Set.mem_image _ _ _).2 (mem_image_of_mem_map_of_surjective f hf h), fun ⟨_, hx⟩ =>
    hx.right ▸ mem_map_of_mem f hx.left⟩
#align ideal.mem_map_iff_of_surjective Ideal.mem_map_iff_of_surjective

theorem le_map_of_comap_le_of_surjective : comap f K ≤ I → K ≤ map f I := fun h =>
  map_comap_of_surjective f hf K ▸ map_mono h
#align ideal.le_map_of_comap_le_of_surjective Ideal.le_map_of_comap_le_of_surjective

theorem map_eq_submodule_map (f : R →+* S) [h : RingHomSurjective f] (I : Ideal R) :
    I.map f = Submodule.map f.toSemilinearMap I :=
  Submodule.ext fun _ => mem_map_iff_of_surjective f h.1
#align ideal.map_eq_submodule_map Ideal.map_eq_submodule_map

end Surjective

section Injective

variable (hf : Function.Injective f)

theorem comap_bot_le_of_injective : comap f ⊥ ≤ I := by
  refine' le_trans (fun x hx => _) bot_le
  rw [mem_comap, Submodule.mem_bot, ← map_zero f] at hx
  exact Eq.symm (hf hx) ▸ Submodule.zero_mem ⊥
#align ideal.comap_bot_le_of_injective Ideal.comap_bot_le_of_injective

theorem comap_bot_of_injective : Ideal.comap f ⊥ = ⊥ :=
  le_bot_iff.mp (Ideal.comap_bot_le_of_injective f hf)
#align ideal.comap_bot_of_injective Ideal.comap_bot_of_injective

end Injective

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `map f.symm (map f I) = I`. -/
@[simp]
theorem map_of_equiv (I : Ideal R) (f : R ≃+* S) :
    (I.map (f : R →+* S)).map (f.symm : S →+* R) = I := by
  rw [← RingEquiv.toRingHom_eq_coe, ← RingEquiv.toRingHom_eq_coe, map_map,
    RingEquiv.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, map_id]
#align ideal.map_of_equiv Ideal.map_of_equiv

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`,
  then `comap f (comap f.symm I) = I`. -/
@[simp]
theorem comap_of_equiv (I : Ideal R) (f : R ≃+* S) :
    (I.comap (f.symm : S →+* R)).comap (f : R →+* S) = I := by
  rw [← RingEquiv.toRingHom_eq_coe, ← RingEquiv.toRingHom_eq_coe, comap_comap,
    RingEquiv.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, comap_id]
#align ideal.comap_of_equiv Ideal.comap_of_equiv

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `map f I = comap f.symm I`. -/
theorem map_comap_of_equiv (I : Ideal R) (f : R ≃+* S) : I.map (f : R →+* S) = I.comap f.symm :=
  le_antisymm (Ideal.map_le_comap_of_inverse _ _ _ (Equiv.left_inv' _))
      (Ideal.comap_le_map_of_inverse _ _ _ (Equiv.right_inv' _))
#align ideal.map_comap_of_equiv Ideal.map_comap_of_equiv

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `comap f.symm I = map f I`. -/
@[simp]
theorem comap_symm (I : Ideal R) (f : R ≃+* S) : I.comap f.symm = I.map f :=
  (map_comap_of_equiv I f).symm

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `map f.symm I = comap f I`. -/
@[simp]
theorem map_symm (I : Ideal S) (f : R ≃+* S) : I.map f.symm = I.comap f :=
  map_comap_of_equiv I (RingEquiv.symm f)



end Semiring

section Ring

variable {F : Type*} [Ring R] [Ring S]

variable [FunLike F R S] [RingHomClass F R S] (f : F) {I : Ideal R}

section Surjective

variable (hf : Function.Surjective f)

theorem comap_map_of_surjective (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥ :=
  le_antisymm
    (fun r h =>
      let ⟨s, hsi, hfsr⟩ := mem_image_of_mem_map_of_surjective f hf h
      Submodule.mem_sup.2
        ⟨s, hsi, r - s, (Submodule.mem_bot S).2 <| by rw [map_sub, hfsr, sub_self],
          add_sub_cancel'_right s r⟩)
    (sup_le (map_le_iff_le_comap.1 le_rfl) (comap_mono bot_le))
#align ideal.comap_map_of_surjective Ideal.comap_map_of_surjective

/-- Correspondence theorem -/
def relIsoOfSurjective : Ideal S ≃o { p : Ideal R // comap f ⊥ ≤ p } where
  toFun J := ⟨comap f J, comap_mono bot_le⟩
  invFun I := map f I.1
  left_inv J := map_comap_of_surjective f hf J
  right_inv I :=
    Subtype.eq <|
      show comap f (map f I.1) = I.1 from
        (comap_map_of_surjective f hf I).symm ▸ le_antisymm (sup_le le_rfl I.2) le_sup_left
  map_rel_iff' {I1 I2} :=
    ⟨fun H => map_comap_of_surjective f hf I1 ▸ map_comap_of_surjective f hf I2 ▸ map_mono H,
      comap_mono⟩
#align ideal.rel_iso_of_surjective Ideal.relIsoOfSurjective

/-- The map on ideals induced by a surjective map preserves inclusion. -/
def orderEmbeddingOfSurjective : Ideal S ↪o Ideal R :=
  (relIsoOfSurjective f hf).toRelEmbedding.trans (Subtype.relEmbedding (fun x y => x ≤ y) _)
#align ideal.order_embedding_of_surjective Ideal.orderEmbeddingOfSurjective

theorem map_eq_top_or_isMaximal_of_surjective {I : Ideal R} (H : IsMaximal I) :
    map f I = ⊤ ∨ IsMaximal (map f I) := by
  refine' or_iff_not_imp_left.2 fun ne_top => ⟨⟨fun h => ne_top h, fun J hJ => _⟩⟩
  · refine'
      (relIsoOfSurjective f hf).injective
        (Subtype.ext_iff.2 (Eq.trans (H.1.2 (comap f J) (lt_of_le_of_ne _ _)) comap_top.symm))
    · exact map_le_iff_le_comap.1 (le_of_lt hJ)
    · exact fun h => hJ.right (le_map_of_comap_le_of_surjective f hf (le_of_eq h.symm))
#align ideal.map_eq_top_or_is_maximal_of_surjective Ideal.map_eq_top_or_isMaximal_of_surjective

theorem comap_isMaximal_of_surjective {K : Ideal S} [H : IsMaximal K] : IsMaximal (comap f K) := by
  refine' ⟨⟨comap_ne_top _ H.1.1, fun J hJ => _⟩⟩
  suffices map f J = ⊤ by
    have := congr_arg (comap f) this
    rw [comap_top, comap_map_of_surjective _ hf, eq_top_iff] at this
    rw [eq_top_iff]
    exact le_trans this (sup_le (le_of_eq rfl) (le_trans (comap_mono bot_le) (le_of_lt hJ)))
  refine'
    H.1.2 (map f J)
      (lt_of_le_of_ne (le_map_of_comap_le_of_surjective _ hf (le_of_lt hJ)) fun h =>
        ne_of_lt hJ (_root_.trans (congr_arg (comap f) h) _))
  rw [comap_map_of_surjective _ hf, sup_eq_left]
  exact le_trans (comap_mono bot_le) (le_of_lt hJ)
#align ideal.comap_is_maximal_of_surjective Ideal.comap_isMaximal_of_surjective

theorem comap_le_comap_iff_of_surjective (I J : Ideal S) : comap f I ≤ comap f J ↔ I ≤ J :=
  ⟨fun h => (map_comap_of_surjective f hf I).symm.le.trans (map_le_of_le_comap h), fun h =>
    le_comap_of_map_le ((map_comap_of_surjective f hf I).le.trans h)⟩
#align ideal.comap_le_comap_iff_of_surjective Ideal.comap_le_comap_iff_of_surjective

end Surjective


section Bijective

variable (hf : Function.Bijective f)

/-- Special case of the correspondence theorem for isomorphic rings -/
def relIsoOfBijective : Ideal S ≃o Ideal R where
  toFun := comap f
  invFun := map f
  left_inv := (relIsoOfSurjective f hf.right).left_inv
  right_inv J :=
    Subtype.ext_iff.1
      ((relIsoOfSurjective f hf.right).right_inv ⟨J, comap_bot_le_of_injective f hf.left⟩)
  map_rel_iff' {_ _} := (relIsoOfSurjective f hf.right).map_rel_iff'
#align ideal.rel_iso_of_bijective Ideal.relIsoOfBijective

theorem comap_le_iff_le_map {I : Ideal R} {K : Ideal S} : comap f K ≤ I ↔ K ≤ map f I :=
  ⟨fun h => le_map_of_comap_le_of_surjective f hf.right h, fun h =>
    (relIsoOfBijective f hf).right_inv I ▸ comap_mono h⟩
#align ideal.comap_le_iff_le_map Ideal.comap_le_iff_le_map

theorem map.isMaximal {I : Ideal R} (H : IsMaximal I) : IsMaximal (map f I) := by
  refine'
    or_iff_not_imp_left.1 (map_eq_top_or_isMaximal_of_surjective f hf.right H) fun h => H.1.1 _
  calc
    I = comap f (map f I) := ((relIsoOfBijective f hf).right_inv I).symm
    _ = comap f ⊤ := by rw [h]
    _ = ⊤ := by rw [comap_top]
#align ideal.map.is_maximal Ideal.map.isMaximal

end Bijective

theorem RingEquiv.bot_maximal_iff (e : R ≃+* S) :
    (⊥ : Ideal R).IsMaximal ↔ (⊥ : Ideal S).IsMaximal :=
  ⟨fun h => map_bot (f := e.toRingHom) ▸ map.isMaximal e.toRingHom e.bijective h, fun h =>
    map_bot (f := e.symm.toRingHom) ▸ map.isMaximal e.symm.toRingHom e.symm.bijective h⟩
#align ideal.ring_equiv.bot_maximal_iff Ideal.RingEquiv.bot_maximal_iff

end Ring

section CommRing

variable {F : Type*} [CommRing R] [CommRing S]

variable [FunLike F R S] [rc : RingHomClass F R S]

variable (f : F)

variable {I J : Ideal R} {K L : Ideal S}

variable (I J K L)

theorem map_mul : map f (I * J) = map f I * map f J :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      mul_le.2 fun r hri s hsj =>
        show (f (r * s)) ∈ map f I * map f J by
          rw [_root_.map_mul]; exact mul_mem_mul (mem_map_of_mem f hri) (mem_map_of_mem f hsj))
    (span_mul_span (↑f '' ↑I) (↑f '' ↑J) ▸ (span_le.2 <|
      Set.iUnion₂_subset fun i ⟨r, hri, hfri⟩ =>
        Set.iUnion₂_subset fun j ⟨s, hsj, hfsj⟩ =>
          Set.singleton_subset_iff.2 <|
            hfri ▸ hfsj ▸ by rw [← _root_.map_mul]; exact mem_map_of_mem f (mul_mem_mul hri hsj)))
#align ideal.map_mul Ideal.map_mul

/-- The pushforward `Ideal.map` as a monoid-with-zero homomorphism. -/
@[simps]
def mapHom : Ideal R →*₀ Ideal S where
  toFun := map f
  map_mul' I J := Ideal.map_mul f I J
  map_one' := by simp only [one_eq_top]; exact Ideal.map_top f
  map_zero' := Ideal.map_bot
#align ideal.map_hom Ideal.mapHom

protected theorem map_pow (n : ℕ) : map f (I ^ n) = map f I ^ n :=
  map_pow (mapHom f) I n
#align ideal.map_pow Ideal.map_pow

theorem comap_radical : comap f (radical K) = radical (comap f K) := by
  ext
  simp [radical]
#align ideal.comap_radical Ideal.comap_radical

variable {K}

theorem IsRadical.comap (hK : K.IsRadical) : (comap f K).IsRadical := by
  rw [← hK.radical, comap_radical]
  apply radical_isRadical
#align ideal.is_radical.comap Ideal.IsRadical.comap

variable {I J L}

theorem map_radical_le : map f (radical I) ≤ radical (map f I) :=
  map_le_iff_le_comap.2 fun r ⟨n, hrni⟩ => ⟨n, map_pow f r n ▸ mem_map_of_mem f hrni⟩
#align ideal.map_radical_le Ideal.map_radical_le

theorem le_comap_mul : comap f K * comap f L ≤ comap f (K * L) :=
  map_le_iff_le_comap.1 <|
    (map_mul f (comap f K) (comap f L)).symm ▸
      mul_mono (map_le_iff_le_comap.2 <| le_rfl) (map_le_iff_le_comap.2 <| le_rfl)
#align ideal.le_comap_mul Ideal.le_comap_mul

theorem le_comap_pow (n : ℕ) : K.comap f ^ n ≤ (K ^ n).comap f := by
  induction' n with n n_ih
  · rw [pow_zero, pow_zero, Ideal.one_eq_top, Ideal.one_eq_top]
    exact rfl.le
  · rw [pow_succ, pow_succ]
    exact (Ideal.mul_mono_right n_ih).trans (Ideal.le_comap_mul f)
#align ideal.le_comap_pow Ideal.le_comap_pow

end CommRing

end MapAndComap

section IsPrimary

variable {R : Type u} [CommSemiring R]

/-- A proper ideal `I` is primary iff `xy ∈ I` implies `x ∈ I` or `y ∈ radical I`. -/
def IsPrimary (I : Ideal R) : Prop :=
  I ≠ ⊤ ∧ ∀ {x y : R}, x * y ∈ I → x ∈ I ∨ y ∈ radical I
#align ideal.is_primary Ideal.IsPrimary

theorem IsPrime.isPrimary {I : Ideal R} (hi : IsPrime I) : IsPrimary I :=
  ⟨hi.1, fun {_ _} hxy => (hi.mem_or_mem hxy).imp id fun hyi => le_radical hyi⟩
#align ideal.is_prime.is_primary Ideal.IsPrime.isPrimary

theorem mem_radical_of_pow_mem {I : Ideal R} {x : R} {m : ℕ} (hx : x ^ m ∈ radical I) :
    x ∈ radical I :=
  radical_idem I ▸ ⟨m, hx⟩
#align ideal.mem_radical_of_pow_mem Ideal.mem_radical_of_pow_mem

theorem isPrime_radical {I : Ideal R} (hi : IsPrimary I) : IsPrime (radical I) :=
  ⟨mt radical_eq_top.1 hi.1,
   fun {x y} ⟨m, hxy⟩ => by
    rw [mul_pow] at hxy; cases' hi.2 hxy with h h
    · exact Or.inl ⟨m, h⟩
    · exact Or.inr (mem_radical_of_pow_mem h)⟩
#align ideal.is_prime_radical Ideal.isPrime_radical

theorem isPrimary_inf {I J : Ideal R} (hi : IsPrimary I) (hj : IsPrimary J)
    (hij : radical I = radical J) : IsPrimary (I ⊓ J) :=
  ⟨ne_of_lt <| lt_of_le_of_lt inf_le_left (lt_top_iff_ne_top.2 hi.1),
   fun {x y} ⟨hxyi, hxyj⟩ => by
    rw [radical_inf, hij, inf_idem]
    cases' hi.2 hxyi with hxi hyi; cases' hj.2 hxyj with hxj hyj
    · exact Or.inl ⟨hxi, hxj⟩
    · exact Or.inr hyj
    · rw [hij] at hyi
      exact Or.inr hyi⟩
#align ideal.is_primary_inf Ideal.isPrimary_inf

end IsPrimary

section Total

variable (ι : Type*)

variable (M : Type*) [AddCommGroup M] {R : Type*} [CommRing R] [Module R M] (I : Ideal R)

variable (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤)

open BigOperators

/-- A variant of `Finsupp.total` that takes in vectors valued in `I`. -/
noncomputable def finsuppTotal : (ι →₀ I) →ₗ[R] M :=
  (Finsupp.total ι M R v).comp (Finsupp.mapRange.linearMap I.subtype)
#align ideal.finsupp_total Ideal.finsuppTotal

variable {ι M v}

theorem finsuppTotal_apply (f : ι →₀ I) :
    finsuppTotal ι M I v f = f.sum fun i x => (x : R) • v i := by
  dsimp [finsuppTotal]
  rw [Finsupp.total_apply, Finsupp.sum_mapRange_index]
  exact fun _ => zero_smul _ _
#align ideal.finsupp_total_apply Ideal.finsuppTotal_apply

theorem finsuppTotal_apply_eq_of_fintype [Fintype ι] (f : ι →₀ I) :
    finsuppTotal ι M I v f = ∑ i, (f i : R) • v i := by
  rw [finsuppTotal_apply, Finsupp.sum_fintype]
  exact fun _ => zero_smul _ _
#align ideal.finsupp_total_apply_eq_of_fintype Ideal.finsuppTotal_apply_eq_of_fintype

theorem range_finsuppTotal :
    LinearMap.range (finsuppTotal ι M I v) = I • Submodule.span R (Set.range v) := by
  ext
  rw [Submodule.mem_ideal_smul_span_iff_exists_sum]
  refine' ⟨fun ⟨f, h⟩ => ⟨Finsupp.mapRange.linearMap I.subtype f, fun i => (f i).2, h⟩, _⟩
  rintro ⟨a, ha, rfl⟩
  classical
    refine' ⟨a.mapRange (fun r => if h : r ∈ I then ⟨r, h⟩ else 0) (by simp), _⟩
    rw [finsuppTotal_apply, Finsupp.sum_mapRange_index]
    · apply Finsupp.sum_congr
      intro i _
      rw [dif_pos (ha i)]
    · exact fun _ => zero_smul _ _
#align ideal.range_finsupp_total Ideal.range_finsuppTotal

end Total

section Basis

variable {ι R S : Type*} [CommSemiring R] [CommRing S] [IsDomain S] [Algebra R S]

/-- A basis on `S` gives a basis on `Ideal.span {x}`, by multiplying everything by `x`. -/
noncomputable def basisSpanSingleton (b : Basis ι R S) {x : S} (hx : x ≠ 0) :
    Basis ι R (span ({x} : Set S)) :=
  b.map <|
    LinearEquiv.ofInjective (Algebra.lmul R S x) (LinearMap.mul_injective hx) ≪≫ₗ
        LinearEquiv.ofEq _ _
          (by
            ext
            simp [mem_span_singleton', mul_comm]) ≪≫ₗ
      (Submodule.restrictScalarsEquiv R S S (Ideal.span ({x} : Set S))).restrictScalars R
#align ideal.basis_span_singleton Ideal.basisSpanSingleton

@[simp]
theorem basisSpanSingleton_apply (b : Basis ι R S) {x : S} (hx : x ≠ 0) (i : ι) :
    (basisSpanSingleton b hx i : S) = x * b i := by
  simp only [basisSpanSingleton, Basis.map_apply, LinearEquiv.trans_apply,
    Submodule.restrictScalarsEquiv_apply, LinearEquiv.ofInjective_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.restrictScalars_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
  -- This used to be the end of the proof before leanprover/lean4#2644
  erw [LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply']
#align ideal.basis_span_singleton_apply Ideal.basisSpanSingleton_apply

@[simp]
theorem constr_basisSpanSingleton {N : Type*} [Semiring N] [Module N S] [SMulCommClass R N S]
    (b : Basis ι R S) {x : S} (hx : x ≠ 0) :
    (b.constr N).toFun (((↑) : _ → S) ∘ (basisSpanSingleton b hx)) = Algebra.lmul R S x :=
  b.ext fun i => by
    erw [Basis.constr_basis, Function.comp_apply, basisSpanSingleton_apply, LinearMap.mul_apply']
#align ideal.constr_basis_span_singleton Ideal.constr_basisSpanSingleton

end Basis

end Ideal

section span_range
variable {α R : Type*} [Semiring R]

theorem Finsupp.mem_ideal_span_range_iff_exists_finsupp {x : R} {v : α → R} :
    x ∈ Ideal.span (Set.range v) ↔ ∃ c : α →₀ R, (c.sum fun i a => a * v i) = x :=
  Finsupp.mem_span_range_iff_exists_finsupp

/-- An element `x` lies in the span of `v` iff it can be written as sum `∑ cᵢ • vᵢ = x`.
-/
theorem mem_ideal_span_range_iff_exists_fun [Fintype α] {x : R} {v : α → R} :
    x ∈ Ideal.span (Set.range v) ↔ ∃ c : α → R, ∑ i, c i * v i = x :=
  mem_span_range_iff_exists_fun _

end span_range

theorem Associates.mk_ne_zero' {R : Type*} [CommSemiring R] {r : R} :
    Associates.mk (Ideal.span {r} : Ideal R) ≠ 0 ↔ r ≠ 0 := by
  rw [Associates.mk_ne_zero, Ideal.zero_eq_bot, Ne.def, Ideal.span_singleton_eq_bot]
#align associates.mk_ne_zero' Associates.mk_ne_zero'

-- Porting note: added explicit coercion `(b i : S)`
/-- If `I : Ideal S` has a basis over `R`,
`x ∈ I` iff it is a linear combination of basis vectors. -/
theorem Basis.mem_ideal_iff {ι R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {I : Ideal S}
    (b : Basis ι R I) {x : S} : x ∈ I ↔ ∃ c : ι →₀ R, x = Finsupp.sum c fun i x => x • (b i : S) :=
  (b.map ((I.restrictScalarsEquiv R _ _).restrictScalars R).symm).mem_submodule_iff
#align basis.mem_ideal_iff Basis.mem_ideal_iff

/-- If `I : Ideal S` has a finite basis over `R`,
`x ∈ I` iff it is a linear combination of basis vectors. -/
theorem Basis.mem_ideal_iff' {ι R S : Type*} [Fintype ι] [CommRing R] [CommRing S] [Algebra R S]
    {I : Ideal S} (b : Basis ι R I) {x : S} : x ∈ I ↔ ∃ c : ι → R, x = ∑ i, c i • (b i : S) :=
  (b.map ((I.restrictScalarsEquiv R _ _).restrictScalars R).symm).mem_submodule_iff'
#align basis.mem_ideal_iff' Basis.mem_ideal_iff'

namespace RingHom

variable {R : Type u} {S : Type v} {T : Type w}

section Semiring

variable {F : Type*} {G : Type*} [Semiring R] [Semiring S] [Semiring T]

variable [FunLike F R S] [rcf : RingHomClass F R S] [FunLike G T S] [rcg : RingHomClass G T S]
variable (f : F) (g : G)

/-- Kernel of a ring homomorphism as an ideal of the domain. -/
def ker : Ideal R :=
  Ideal.comap f ⊥
#align ring_hom.ker RingHom.ker

/-- An element is in the kernel if and only if it maps to zero.-/
theorem mem_ker {r} : r ∈ ker f ↔ f r = 0 := by rw [ker, Ideal.mem_comap, Submodule.mem_bot]
#align ring_hom.mem_ker RingHom.mem_ker

theorem ker_eq : (ker f : Set R) = Set.preimage f {0} :=
  rfl
#align ring_hom.ker_eq RingHom.ker_eq

theorem ker_eq_comap_bot (f : F) : ker f = Ideal.comap f ⊥ :=
  rfl
#align ring_hom.ker_eq_comap_bot RingHom.ker_eq_comap_bot

theorem comap_ker (f : S →+* R) (g : T →+* S) : f.ker.comap g = ker (f.comp g) := by
  rw [RingHom.ker_eq_comap_bot, Ideal.comap_comap, RingHom.ker_eq_comap_bot]
#align ring_hom.comap_ker RingHom.comap_ker

/-- If the target is not the zero ring, then one is not in the kernel.-/
theorem not_one_mem_ker [Nontrivial S] (f : F) : (1 : R) ∉ ker f := by
  rw [mem_ker, map_one]
  exact one_ne_zero
#align ring_hom.not_one_mem_ker RingHom.not_one_mem_ker

theorem ker_ne_top [Nontrivial S] (f : F) : ker f ≠ ⊤ :=
  (Ideal.ne_top_iff_one _).mpr <| not_one_mem_ker f
#align ring_hom.ker_ne_top RingHom.ker_ne_top

lemma _root_.Pi.ker_ringHom {ι : Type*} {R : ι → Type*} [∀ i, Semiring (R i)]
    (φ : ∀ i, S →+* R i) : ker (Pi.ringHom φ) = ⨅ i, ker (φ i) := by
  ext x
  simp [mem_ker, Ideal.mem_iInf, Function.funext_iff]

@[simp]
theorem ker_rangeSRestrict (f : R →+* S) : ker f.rangeSRestrict = ker f :=
  Ideal.ext fun _ ↦ Subtype.ext_iff

end Semiring

section Ring

variable {F : Type*} [Ring R] [Semiring S] [FunLike F R S] [rc : RingHomClass F R S] (f : F)

theorem injective_iff_ker_eq_bot : Function.Injective f ↔ ker f = ⊥ := by
  rw [SetLike.ext'_iff, ker_eq, Set.ext_iff]
  exact injective_iff_map_eq_zero' f
#align ring_hom.injective_iff_ker_eq_bot RingHom.injective_iff_ker_eq_bot

theorem ker_eq_bot_iff_eq_zero : ker f = ⊥ ↔ ∀ x, f x = 0 → x = 0 := by
  rw [← injective_iff_map_eq_zero f, injective_iff_ker_eq_bot]
#align ring_hom.ker_eq_bot_iff_eq_zero RingHom.ker_eq_bot_iff_eq_zero

@[simp]
theorem ker_coe_equiv (f : R ≃+* S) : ker (f : R →+* S) = ⊥ := by
  simpa only [← injective_iff_ker_eq_bot] using EquivLike.injective f
#align ring_hom.ker_coe_equiv RingHom.ker_coe_equiv

@[simp]
theorem ker_equiv {F' : Type*} [EquivLike F' R S] [RingEquivClass F' R S] (f : F') : ker f = ⊥ := by
  simpa only [← injective_iff_ker_eq_bot] using EquivLike.injective f
#align ring_hom.ker_equiv RingHom.ker_equiv

end Ring

section RingRing

variable {F : Type*} [Ring R] [Ring S] [FunLike F R S] [rc : RingHomClass F R S] (f : F)

theorem sub_mem_ker_iff {x y} : x - y ∈ ker f ↔ f x = f y := by rw [mem_ker, map_sub, sub_eq_zero]
#align ring_hom.sub_mem_ker_iff RingHom.sub_mem_ker_iff

@[simp]
theorem ker_rangeRestrict (f : R →+* S) : ker f.rangeRestrict = ker f :=
  Ideal.ext fun _ ↦ Subtype.ext_iff

end RingRing

/-- The kernel of a homomorphism to a domain is a prime ideal. -/
theorem ker_isPrime {F : Type*} [Ring R] [Ring S] [IsDomain S]
    [FunLike F R S] [RingHomClass F R S] (f : F) :
    (ker f).IsPrime :=
  ⟨by
    rw [Ne.def, Ideal.eq_top_iff_one]
    exact not_one_mem_ker f,
   fun {x y} => by
    simpa only [mem_ker, map_mul] using @eq_zero_or_eq_zero_of_mul_eq_zero S _ _ _ _ _⟩
#align ring_hom.ker_is_prime RingHom.ker_isPrime

/-- The kernel of a homomorphism to a field is a maximal ideal. -/
theorem ker_isMaximal_of_surjective {R K F : Type*} [Ring R] [Field K]
    [FunLike F R K] [RingHomClass F R K] (f : F)
    (hf : Function.Surjective f) : (ker f).IsMaximal := by
  refine'
    Ideal.isMaximal_iff.mpr
      ⟨fun h1 => one_ne_zero' K <| map_one f ▸ (mem_ker f).mp h1, fun J x hJ hxf hxJ => _⟩
  obtain ⟨y, hy⟩ := hf (f x)⁻¹
  have H : 1 = y * x - (y * x - 1) := (sub_sub_cancel _ _).symm
  rw [H]
  refine' J.sub_mem (J.mul_mem_left _ hxJ) (hJ _)
  rw [mem_ker]
  simp only [hy, map_sub, map_one, map_mul, inv_mul_cancel (mt (mem_ker f).mpr hxf), sub_self]
#align ring_hom.ker_is_maximal_of_surjective RingHom.ker_isMaximal_of_surjective

end RingHom

namespace Ideal

variable {R : Type*} {S : Type*} {F : Type*}

section Semiring

variable [Semiring R] [Semiring S] [FunLike F R S] [rc : RingHomClass F R S]

theorem map_eq_bot_iff_le_ker {I : Ideal R} (f : F) : I.map f = ⊥ ↔ I ≤ RingHom.ker f := by
  rw [RingHom.ker, eq_bot_iff, map_le_iff_le_comap]
#align ideal.map_eq_bot_iff_le_ker Ideal.map_eq_bot_iff_le_ker

theorem ker_le_comap {K : Ideal S} (f : F) : RingHom.ker f ≤ comap f K := fun _ hx =>
  mem_comap.2 (((RingHom.mem_ker f).1 hx).symm ▸ K.zero_mem)
#align ideal.ker_le_comap Ideal.ker_le_comap

theorem map_isPrime_of_equiv {F' : Type*} [EquivLike F' R S] [RingEquivClass F' R S]
    (f : F') {I : Ideal R} [IsPrime I] : IsPrime (map f I) := by
  have h : I.map f = I.map ((f : R ≃+* S) : R →+* S) := rfl
  rw [h, map_comap_of_equiv I (f : R ≃+* S)]
  exact Ideal.IsPrime.comap (RingEquiv.symm (f : R ≃+* S))
#align ideal.map_is_prime_of_equiv Ideal.map_isPrime_of_equiv


end Semiring

section Ring

variable [Ring R] [Ring S] [FunLike F R S] [rc : RingHomClass F R S]

theorem map_sInf {A : Set (Ideal R)} {f : F} (hf : Function.Surjective f) :
    (∀ J ∈ A, RingHom.ker f ≤ J) → map f (sInf A) = sInf (map f '' A) := by
  refine' fun h => le_antisymm (le_sInf _) _
  · intro j hj y hy
    cases' (mem_map_iff_of_surjective f hf).1 hy with x hx
    cases' (Set.mem_image _ _ _).mp hj with J hJ
    rw [← hJ.right, ← hx.right]
    exact mem_map_of_mem f (sInf_le_of_le hJ.left (le_of_eq rfl) hx.left)
  · intro y hy
    cases' hf y with x hx
    refine' hx ▸ mem_map_of_mem f _
    have : ∀ I ∈ A, y ∈ map f I := by simpa using hy
    rw [Submodule.mem_sInf]
    intro J hJ
    rcases (mem_map_iff_of_surjective f hf).1 (this J hJ) with ⟨x', hx', rfl⟩
    have : x - x' ∈ J := by
      apply h J hJ
      rw [RingHom.mem_ker, map_sub, hx, sub_self]
    simpa only [sub_add_cancel] using J.add_mem this hx'
#align ideal.map_Inf Ideal.map_sInf

theorem map_isPrime_of_surjective {f : F} (hf : Function.Surjective f) {I : Ideal R} [H : IsPrime I]
    (hk : RingHom.ker f ≤ I) : IsPrime (map f I) := by
  refine' ⟨fun h => H.ne_top (eq_top_iff.2 _), fun {x y} => _⟩
  · replace h := congr_arg (comap f) h
    rw [comap_map_of_surjective _ hf, comap_top] at h
    exact h ▸ sup_le (le_of_eq rfl) hk
  · refine' fun hxy => (hf x).recOn fun a ha => (hf y).recOn fun b hb => _
    rw [← ha, ← hb, ← _root_.map_mul f, mem_map_iff_of_surjective _ hf] at hxy
    rcases hxy with ⟨c, hc, hc'⟩
    rw [← sub_eq_zero, ← map_sub] at hc'
    have : a * b ∈ I := by
      convert I.sub_mem hc (hk (hc' : c - a * b ∈ RingHom.ker f)) using 1
      abel
    exact
      (H.mem_or_mem this).imp (fun h => ha ▸ mem_map_of_mem f h) fun h => hb ▸ mem_map_of_mem f h
#align ideal.map_is_prime_of_surjective Ideal.map_isPrime_of_surjective

theorem map_eq_bot_iff_of_injective {I : Ideal R} {f : F} (hf : Function.Injective f) :
    I.map f = ⊥ ↔ I = ⊥ := by
  rw [map_eq_bot_iff_le_ker, (RingHom.injective_iff_ker_eq_bot f).mp hf, le_bot_iff]
#align ideal.map_eq_bot_iff_of_injective Ideal.map_eq_bot_iff_of_injective

end Ring

section CommRing

variable [CommRing R] [CommRing S]

theorem map_eq_iff_sup_ker_eq_of_surjective {I J : Ideal R} (f : R →+* S)
    (hf : Function.Surjective f) : map f I = map f J ↔ I ⊔ RingHom.ker f = J ⊔ RingHom.ker f := by
  rw [← (comap_injective_of_surjective f hf).eq_iff, comap_map_of_surjective f hf,
    comap_map_of_surjective f hf, RingHom.ker_eq_comap_bot]
#align ideal.map_eq_iff_sup_ker_eq_of_surjective Ideal.map_eq_iff_sup_ker_eq_of_surjective

theorem map_radical_of_surjective {f : R →+* S} (hf : Function.Surjective f) {I : Ideal R}
    (h : RingHom.ker f ≤ I) : map f I.radical = (map f I).radical := by
  rw [radical_eq_sInf, radical_eq_sInf]
  have : ∀ J ∈ {J : Ideal R | I ≤ J ∧ J.IsPrime}, RingHom.ker f ≤ J := fun J hJ => h.trans hJ.left
  convert map_sInf hf this
  refine' funext fun j => propext ⟨_, _⟩
  · rintro ⟨hj, hj'⟩
    haveI : j.IsPrime := hj'
    exact
      ⟨comap f j, ⟨⟨map_le_iff_le_comap.1 hj, comap_isPrime f j⟩, map_comap_of_surjective f hf j⟩⟩
  · rintro ⟨J, ⟨hJ, hJ'⟩⟩
    haveI : J.IsPrime := hJ.right
    refine' ⟨hJ' ▸ map_mono hJ.left, hJ' ▸ map_isPrime_of_surjective hf (le_trans h hJ.left)⟩
#align ideal.map_radical_of_surjective Ideal.map_radical_of_surjective

end CommRing

end Ideal

namespace Submodule

variable {R : Type u} {M : Type v}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

-- TODO: show `[Algebra R A] : Algebra (Ideal R) A` too
instance moduleSubmodule : Module (Ideal R) (Submodule R M) where
  smul_add := smul_sup
  add_smul := sup_smul
  mul_smul := Submodule.smul_assoc
  one_smul := by simp
  zero_smul := bot_smul
  smul_zero := smul_bot
#align submodule.module_submodule Submodule.moduleSubmodule

lemma span_smul_eq
    (s : Set R) (N : Submodule R M) :
    Ideal.span s • N = s • N := by
  rw [← coe_set_smul, coe_span_smul]

end Submodule

namespace RingHom

variable {A B C : Type*} [Ring A] [Ring B] [Ring C]

variable (f : A →+* B) (f_inv : B → A)

/-- Auxiliary definition used to define `liftOfRightInverse` -/
def liftOfRightInverseAux (hf : Function.RightInverse f_inv f) (g : A →+* C)
    (hg : RingHom.ker f ≤ RingHom.ker g) :
    B →+* C :=
  { AddMonoidHom.liftOfRightInverse f.toAddMonoidHom f_inv hf ⟨g.toAddMonoidHom, hg⟩ with
    toFun := fun b => g (f_inv b)
    map_one' := by
      rw [← map_one g, ← sub_eq_zero, ← map_sub g, ← mem_ker g]
      apply hg
      rw [mem_ker f, map_sub f, sub_eq_zero, map_one f]
      exact hf 1
    map_mul' := by
      intro x y
      rw [← map_mul g, ← sub_eq_zero, ← map_sub g, ← mem_ker g]
      apply hg
      rw [mem_ker f, map_sub f, sub_eq_zero, map_mul f]
      simp only [hf _] }
#align ring_hom.lift_of_right_inverse_aux RingHom.liftOfRightInverseAux

@[simp]
theorem liftOfRightInverseAux_comp_apply (hf : Function.RightInverse f_inv f) (g : A →+* C)
    (hg : RingHom.ker f ≤ RingHom.ker g) (a : A) :
    (f.liftOfRightInverseAux f_inv hf g hg) (f a) = g a :=
  f.toAddMonoidHom.liftOfRightInverse_comp_apply f_inv hf ⟨g.toAddMonoidHom, hg⟩ a
#align ring_hom.lift_of_right_inverse_aux_comp_apply RingHom.liftOfRightInverseAux_comp_apply

/-- `liftOfRightInverse f hf g hg` is the unique ring homomorphism `φ`

* such that `φ.comp f = g` (`RingHom.liftOfRightInverse_comp`),
* where `f : A →+* B` has a right_inverse `f_inv` (`hf`),
* and `g : B →+* C` satisfies `hg : f.ker ≤ g.ker`.

See `RingHom.eq_liftOfRightInverse` for the uniqueness lemma.

```
   A .
   |  \
 f |   \ g
   |    \
   v     \⌟
   B ----> C
      ∃!φ
```
-/
def liftOfRightInverse (hf : Function.RightInverse f_inv f) :
    { g : A →+* C // RingHom.ker f ≤ RingHom.ker g } ≃ (B →+* C) where
  toFun g := f.liftOfRightInverseAux f_inv hf g.1 g.2
  invFun φ := ⟨φ.comp f, fun x hx => (mem_ker _).mpr <| by simp [(mem_ker _).mp hx]⟩
  left_inv g := by
    ext
    simp only [comp_apply, liftOfRightInverseAux_comp_apply, Subtype.coe_mk]
  right_inv φ := by
    ext b
    simp [liftOfRightInverseAux, hf b]
#align ring_hom.lift_of_right_inverse RingHom.liftOfRightInverse

/-- A non-computable version of `RingHom.liftOfRightInverse` for when no computable right
inverse is available, that uses `Function.surjInv`. -/
@[simp]
noncomputable abbrev liftOfSurjective (hf : Function.Surjective f) :
    { g : A →+* C // RingHom.ker f ≤ RingHom.ker g } ≃ (B →+* C) :=
  f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)
#align ring_hom.lift_of_surjective RingHom.liftOfSurjective

theorem liftOfRightInverse_comp_apply (hf : Function.RightInverse f_inv f)
    (g : { g : A →+* C // RingHom.ker f ≤ RingHom.ker g }) (x : A) :
    (f.liftOfRightInverse f_inv hf g) (f x) = g.1 x :=
  f.liftOfRightInverseAux_comp_apply f_inv hf g.1 g.2 x
#align ring_hom.lift_of_right_inverse_comp_apply RingHom.liftOfRightInverse_comp_apply

theorem liftOfRightInverse_comp (hf : Function.RightInverse f_inv f)
    (g : { g : A →+* C // RingHom.ker f ≤ RingHom.ker g }) :
    (f.liftOfRightInverse f_inv hf g).comp f = g :=
  RingHom.ext <| f.liftOfRightInverse_comp_apply f_inv hf g
#align ring_hom.lift_of_right_inverse_comp RingHom.liftOfRightInverse_comp

theorem eq_liftOfRightInverse (hf : Function.RightInverse f_inv f) (g : A →+* C)
    (hg : RingHom.ker f ≤ RingHom.ker g) (h : B →+* C) (hh : h.comp f = g) :
    h = f.liftOfRightInverse f_inv hf ⟨g, hg⟩ := by
  simp_rw [← hh]
  exact ((f.liftOfRightInverse f_inv hf).apply_symm_apply _).symm
#align ring_hom.eq_lift_of_right_inverse RingHom.eq_liftOfRightInverse

end RingHom

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)

lemma coe_ker : RingHom.ker f = RingHom.ker (f : A →+* B) := rfl

lemma coe_ideal_map (I : Ideal A) :
    Ideal.map f I = Ideal.map (f : A →+* B) I := rfl

end AlgHom
