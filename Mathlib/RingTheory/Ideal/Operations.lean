/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Data.Fintype.Lattice
import Mathlib.RingTheory.Coprime.Lemmas

#align_import ring_theory.ideal.operations from "leanprover-community/mathlib"@"e7f0ddbf65bd7181a85edb74b64bdc35ba4bdc74"

/-!
# More operations on modules and ideals
-/

assert_not_exists Basis -- See `RingTheory.Ideal.Basis`
assert_not_exists Submodule.hasQuotient -- See `RingTheory.Ideal.QuotientOperations`

universe u v w x

open Pointwise

namespace Submodule

variable {R : Type u} {M : Type v} {M' F G : Type*}

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

open Pointwise

instance hasSMul' : SMul (Ideal R) (Submodule R M) :=
  ⟨Submodule.map₂ (LinearMap.lsmul R M)⟩
#align submodule.has_smul' Submodule.hasSMul'

/-- This duplicates the global `smul_eq_mul`, but doesn't have to unfold anywhere near as much to
apply. -/
protected theorem _root_.Ideal.smul_eq_mul (I J : Ideal R) : I • J = I * J :=
  rfl
#align ideal.smul_eq_mul Ideal.smul_eq_mul

variable (R M) in
/-- `Module.annihilator R M` is the ideal of all elements `r : R` such that `r • M = 0`. -/
def _root_.Module.annihilator : Ideal R := LinearMap.ker (LinearMap.lsmul R M)

theorem _root_.Module.mem_annihilator {r} : r ∈ Module.annihilator R M ↔ ∀ m : M, r • m = 0 :=
  ⟨fun h ↦ (congr($h ·)), (LinearMap.ext ·)⟩

theorem _root_.LinearMap.annihilator_le_of_injective (f : M →ₗ[R] M') (hf : Function.Injective f) :
    Module.annihilator R M' ≤ Module.annihilator R M := fun x h ↦ by
  rw [Module.mem_annihilator] at h ⊢; exact fun m ↦ hf (by rw [map_smul, h, f.map_zero])

theorem _root_.LinearMap.annihilator_le_of_surjective (f : M →ₗ[R] M')
    (hf : Function.Surjective f) : Module.annihilator R M ≤ Module.annihilator R M' := fun x h ↦ by
  rw [Module.mem_annihilator] at h ⊢
  intro m; obtain ⟨m, rfl⟩ := hf m
  rw [← map_smul, h, f.map_zero]

theorem _root_.LinearEquiv.annihilator_eq (e : M ≃ₗ[R] M') :
    Module.annihilator R M = Module.annihilator R M' :=
  (e.annihilator_le_of_surjective e.surjective).antisymm (e.annihilator_le_of_injective e.injective)

/-- `N.annihilator` is the ideal of all elements `r : R` such that `r • N = 0`. -/
abbrev annihilator (N : Submodule R M) : Ideal R :=
  Module.annihilator R N
#align submodule.annihilator Submodule.annihilator

theorem annihilator_top : (⊤ : Submodule R M).annihilator = Module.annihilator R M :=
  topEquiv.annihilator_eq

variable {I J : Ideal R} {N P : Submodule R M}

theorem mem_annihilator {r} : r ∈ N.annihilator ↔ ∀ n ∈ N, r • n = (0 : M) := by
  simp_rw [annihilator, Module.mem_annihilator, Subtype.forall, Subtype.ext_iff]; rfl
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
theorem smul_induction_on {p : M → Prop} {x} (H : x ∈ I • N) (smul : ∀ r ∈ I, ∀ n ∈ N, p (r • n))
    (add : ∀ x y, p x → p y → p (x + y)) : p x := by
  have H0 : p 0 := by simpa only [zero_smul] using smul 0 I.zero_mem 0 N.zero_mem
  refine Submodule.iSup_induction (x := x) _ H ?_ H0 add
  rintro ⟨i, hi⟩ m ⟨j, hj, hj'⟩
  rw [← hj']
  exact smul _ hi _ hj
#align submodule.smul_induction_on Submodule.smul_induction_on

/-- Dependent version of `Submodule.smul_induction_on`. -/
@[elab_as_elim]
theorem smul_induction_on' {x : M} (hx : x ∈ I • N) {p : ∀ x, x ∈ I • N → Prop}
    (smul : ∀ (r : R) (hr : r ∈ I) (n : M) (hn : n ∈ N), p (r • n) (smul_mem_smul hr hn))
    (add : ∀ x hx y hy, p x hx → p y hy → p (x + y) (Submodule.add_mem _ ‹_› ‹_›)) : p x hx := by
  refine Exists.elim ?_ fun (h : x ∈ I • N) (H : p x h) => H
  exact
    smul_induction_on hx (fun a ha x hx => ⟨_, smul _ ha _ hx⟩) fun x y ⟨_, hx⟩ ⟨_, hy⟩ =>
      ⟨_, add _ _ _ _ hx hy⟩
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

instance : CovariantClass (Ideal R) (Submodule R M) HSMul.hSMul LE.le :=
  ⟨fun _ _ => map₂_le_map₂_right⟩

@[deprecated smul_mono_right] -- 2024-03-31
protected theorem smul_mono_right (h : N ≤ P) : I • N ≤ I • P :=
  _root_.smul_mono_right I h
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

@[deprecated smul_inf_le] -- 2024-03-31
protected theorem smul_inf_le (M₁ M₂ : Submodule R M) :
    I • (M₁ ⊓ M₂) ≤ I • M₁ ⊓ I • M₂ := smul_inf_le _ _ _
#align submodule.smul_inf_le Submodule.smul_inf_le

theorem smul_iSup {ι : Sort*} {I : Ideal R} {t : ι → Submodule R M} : I • iSup t = ⨆ i, I • t i :=
  map₂_iSup_right _ _ _
#align submodule.smul_supr Submodule.smul_iSup

@[deprecated smul_iInf_le] -- 2024-03-31
protected theorem smul_iInf_le {ι : Sort*} {I : Ideal R} {t : ι → Submodule R M} :
    I • iInf t ≤ ⨅ i, I • t i :=
  smul_iInf_le
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

@[simp]
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

open Pointwise in
@[simp]
theorem map_pointwise_smul (r : R) (N : Submodule R M) (f : M →ₗ[R] M') :
    (r • N).map f = r • N.map f := by
  simp_rw [← ideal_span_singleton_smul, map_smul'']

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
  refine fun hx => span_induction (mem_smul_span.mp hx) ?_ ?_ ?_ ?_
  · simp only [Set.mem_iUnion, Set.mem_range, Set.mem_singleton_iff]
    rintro x ⟨y, hy, x, ⟨i, rfl⟩, rfl⟩
    refine ⟨Finsupp.single i y, fun j => ?_, ?_⟩
    · letI := Classical.decEq ι
      rw [Finsupp.single_apply]
      split_ifs
      · assumption
      · exact I.zero_mem
    refine @Finsupp.sum_single_index ι R M _ _ i _ (fun i y => y • f i) ?_
    simp
  · exact ⟨0, fun _ => I.zero_mem, Finsupp.sum_zero_index⟩
  · rintro x y ⟨ax, hax, rfl⟩ ⟨ay, hay, rfl⟩
    refine ⟨ax + ay, fun i => I.add_mem (hax i) (hay i), Finsupp.sum_add_index' ?_ ?_⟩ <;>
      intros <;> simp only [zero_smul, add_smul]
  · rintro c x ⟨a, ha, rfl⟩
    refine ⟨c • a, fun i => I.mul_mem_left c (ha i), ?_⟩
    rw [Finsupp.sum_smul_index, Finsupp.smul_sum] <;> intros <;> simp only [zero_smul, mul_smul]
#align submodule.mem_ideal_smul_span_iff_exists_sum Submodule.mem_ideal_smul_span_iff_exists_sum

theorem mem_ideal_smul_span_iff_exists_sum' {ι : Type*} (s : Set ι) (f : ι → M) (x : M) :
    x ∈ I • span R (f '' s) ↔
    ∃ (a : s →₀ R) (_ : ∀ i, a i ∈ I), (a.sum fun i c => c • f i) = x := by
  rw [← Submodule.mem_ideal_smul_span_iff_exists_sum, ← Set.image_eq_range]
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
  refine Submodule.smul_le.mpr fun r hr x hx => ?_
  rw [Submodule.mem_comap] at hx ⊢
  rw [f.map_smul]
  exact Submodule.smul_mem_smul hr hx
#align submodule.smul_comap_le_comap_smul Submodule.smul_comap_le_comap_smul

end CommSemiring

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
    (∀ i ∈ s, x i ∈ I i) → (∏ i ∈ s, x i) ∈ ∏ i ∈ s, I i := by
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
      (∀ zI ∈ I, ∃ zJ ∈ J, x * zI = y * zJ) ∧ ∀ zJ ∈ J, ∃ zI ∈ I, x * zI = y * zJ := by
  simp only [le_antisymm_iff, span_singleton_mul_le_span_singleton_mul, eq_comm]
#align ideal.span_singleton_mul_eq_span_singleton_mul Ideal.span_singleton_mul_eq_span_singleton_mul

theorem prod_span {ι : Type*} (s : Finset ι) (I : ι → Set R) :
    (∏ i ∈ s, Ideal.span (I i)) = Ideal.span (∏ i ∈ s, I i) :=
  Submodule.prod_span s I
#align ideal.prod_span Ideal.prod_span

theorem prod_span_singleton {ι : Type*} (s : Finset ι) (I : ι → R) :
    (∏ i ∈ s, Ideal.span ({I i} : Set R)) = Ideal.span {∏ i ∈ s, I i} :=
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
    (s.inf fun i => Ideal.span ({I i} : Set R)) = Ideal.span {∏ i ∈ s, I i} := by
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
    refine s.induction_on ?_ ?_
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
    refine ⟨_, add_mem hi' (mul_mem_right k _ hi1), _, mul_mem_mul hj hk, ?_⟩
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
    (I ⊔ ∏ i ∈ s, J i) = ⊤ :=
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
    (∏ i ∈ s, J i) ⊔ I = ⊤ := by rw [sup_comm, sup_prod_eq_top]; intro i hi; rw [sup_comm, h i hi]
#align ideal.prod_sup_eq_top Ideal.prod_sup_eq_top

theorem iInf_sup_eq_top {s : Finset ι} {J : ι → Ideal R} (h : ∀ i, i ∈ s → J i ⊔ I = ⊤) :
    (⨅ i ∈ s, J i) ⊔ I = ⊤ := by rw [sup_comm, sup_iInf_eq_top]; intro i hi; rw [sup_comm, h i hi]
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

-- @[simp] -- Porting note (#10618): simp can prove this
theorem mul_bot : I * ⊥ = ⊥ := by simp
#align ideal.mul_bot Ideal.mul_bot

-- @[simp] -- Porting note (#10618): simp can prove thisrove this
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
  smul_mono_right _ h
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
    exact Ideal.mul_mono hn e
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
    refine ⟨1, 1, ?_⟩
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
  add_mem' := fun {_ _} ⟨m, hxmi⟩ ⟨n, hyni⟩ =>
    ⟨m + n - 1, add_pow_add_pred_mem_of_pow_mem I hxmi hyni⟩
  smul_mem' {r s} := fun ⟨n, h⟩ ↦ ⟨n, (mul_pow r s n).symm ▸ I.mul_mem_left (r ^ n) h⟩
#align ideal.radical Ideal.radical

theorem mem_radical_iff {r : R} : r ∈ I.radical ↔ ∃ n : ℕ, r ^ n ∈ I := Iff.rfl

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

theorem isRadical_iff_pow_one_lt (k : ℕ) (hk : 1 < k) : I.IsRadical ↔ ∀ r, r ^ k ∈ I → r ∈ I :=
  ⟨fun h _r hr ↦ h ⟨k, hr⟩, fun h x ⟨n, hx⟩ ↦
    k.pow_imp_self_of_one_lt hk _ (fun _ _ ↦ .inr ∘ I.smul_mem _) h n x hx⟩

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

theorem mem_radical_of_pow_mem {I : Ideal R} {x : R} {m : ℕ} (hx : x ^ m ∈ radical I) :
    x ∈ radical I :=
  radical_idem I ▸ ⟨m, hx⟩
#align ideal.mem_radical_of_pow_mem Ideal.mem_radical_of_pow_mem

theorem disjoint_powers_iff_not_mem (y : R) (hI : I.IsRadical) :
    Disjoint (Submonoid.powers y : Set R) ↑I ↔ y ∉ I.1 := by
  refine ⟨fun h => Set.disjoint_left.1 h (Submonoid.mem_powers _),
      fun h => disjoint_iff.mpr (eq_bot_iff.mpr ?_)⟩
  rintro x ⟨⟨n, rfl⟩, hx'⟩
  exact h (hI <| mem_radical_of_pow_mem <| le_radical hx')
#align ideal.disjoint_powers_iff_not_mem Ideal.disjoint_powers_iff_not_mem

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

variable {I J} in
theorem IsRadical.inf (hI : IsRadical I) (hJ : IsRadical J) : IsRadical (I ⊓ J) := by
  rw [IsRadical, radical_inf]; exact inf_le_inf hI hJ

/-- The reverse inclusion does not hold for e.g. `I := fun n : ℕ ↦ Ideal.span {(2 ^ n : ℤ)}`. -/
theorem radical_iInf_le {ι} (I : ι → Ideal R) : radical (⨅ i, I i) ≤ ⨅ i, radical (I i) :=
  le_iInf fun _ ↦ radical_mono (iInf_le _ _)

theorem isRadical_iInf {ι} (I : ι → Ideal R) (hI : ∀ i, IsRadical (I i)) : IsRadical (⨅ i, I i) :=
  (radical_iInf_le I).trans (iInf_mono hI)

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
                    refine
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

lemma radical_pow : ∀ {n}, n ≠ 0 → radical (I ^ n) = radical I
  | 1, _ => by simp
  | n + 2, _ => by rw [pow_succ, radical_mul, radical_pow n.succ_ne_zero, inf_idem]
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

theorem IsPrime.multiset_prod_mem_iff_exists_mem {I : Ideal R} (hI : I.IsPrime) (s : Multiset R) :
    s.prod ∈ I ↔ ∃ p ∈ s, p ∈ I := by
  simpa [span_singleton_le_iff_mem] using (hI.multiset_prod_map_le (span {·}))

theorem IsPrime.prod_le {s : Finset ι} {f : ι → Ideal R} {P : Ideal R} (hp : IsPrime P) :
    s.prod f ≤ P ↔ ∃ i ∈ s, f i ≤ P :=
  hp.multiset_prod_map_le f
#align ideal.is_prime.prod_le Ideal.IsPrime.prod_le

theorem IsPrime.prod_mem_iff_exists_mem {I : Ideal R} (hI : I.IsPrime) (s : Finset R) :
    s.prod (fun x ↦ x) ∈ I ↔ ∃ p ∈ s, p ∈ I := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  exact hI.multiset_prod_mem_iff_exists_mem s.val

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
            Set.Subset.trans Set.subset_union_left Set.subset_union_left)
        fun h =>
        Or.casesOn h
          (fun h =>
            Set.Subset.trans h <|
              Set.Subset.trans Set.subset_union_right Set.subset_union_left)
          fun ⟨i, his, hi⟩ => by
          refine Set.Subset.trans hi <| Set.Subset.trans ?_ Set.subset_union_right;
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
      refine ih.imp id (Or.imp id (Exists.imp fun k => ?_))
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
    · exact hs (Or.inl <| Or.inl <| add_sub_cancel_left r s ▸ (f a).sub_mem ha hra)
    · exact hs (Or.inl <| Or.inr <| add_sub_cancel_left r s ▸ (f b).sub_mem hb hrb)
    · exact hri (add_sub_cancel_right r s ▸ (f i).sub_mem hi hsi)
    · rw [Set.mem_iUnion₂] at ht
      rcases ht with ⟨j, hjt, hj⟩
      simp only [Finset.inf_eq_iInf, SetLike.mem_coe, Submodule.mem_iInf] at hr
      exact hs $ Or.inr $ Set.mem_biUnion hjt <|
        add_sub_cancel_left r s ▸ (f j).sub_mem hj <| hr j hjt
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
          refine hp i (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hiu)) ?_ ?_ <;>
              rintro rfl <;>
            solve_by_elim only [Finset.mem_insert_of_mem, *]
        rw [Finset.coe_insert, Finset.coe_insert, Set.biUnion_insert, Set.biUnion_insert, ←
          Set.union_assoc, subset_union_prime' hp'] at h
        rwa [Finset.exists_mem_insert, Finset.exists_mem_insert]
      · have hp' : ∀ j ∈ t, IsPrime (f j) := by
          intro j hj
          refine hp j (Finset.mem_insert_of_mem hj) ?_ ?_ <;> rintro rfl <;>
            solve_by_elim only [Finset.mem_insert_of_mem, *]
        rw [Finset.coe_insert, Set.biUnion_insert, ← Set.union_self (f a : Set R),
          subset_union_prime' hp', ← or_assoc, or_self_iff] at h
        rwa [Finset.exists_mem_insert]
    · by_cases hbs : b ∈ s
      · obtain ⟨t, hbt, rfl⟩ : ∃ t, b ∉ t ∧ insert b t = s :=
          ⟨s.erase b, Finset.not_mem_erase b s, Finset.insert_erase hbs⟩
        have hp' : ∀ j ∈ t, IsPrime (f j) := by
          intro j hj
          refine hp j (Finset.mem_insert_of_mem hj) ?_ ?_ <;> rintro rfl <;>
            solve_by_elim only [Finset.mem_insert_of_mem, *]
        rw [Finset.coe_insert, Set.biUnion_insert, ← Set.union_self (f b : Set R),
          subset_union_prime' hp', ← or_assoc, or_self_iff] at h
        rwa [Finset.exists_mem_insert]
      rcases s.eq_empty_or_nonempty with hse | hsne
      · subst hse
        rw [Finset.coe_empty, Set.biUnion_empty, Set.subset_empty_iff] at h
        have : (I : Set R) ≠ ∅ := Set.Nonempty.ne_empty (Set.nonempty_of_mem I.zero_mem)
        exact absurd h this
      · cases' hsne with i his
        obtain ⟨t, _, rfl⟩ : ∃ t, i ∉ t ∧ insert i t = s :=
          ⟨s.erase i, Finset.not_mem_erase i s, Finset.insert_erase his⟩
        have hp' : ∀ j ∈ t, IsPrime (f j) := by
          intro j hj
          refine hp j (Finset.mem_insert_of_mem hj) ?_ ?_ <;> rintro rfl <;>
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



section Total

variable (ι : Type*)
variable (M : Type*) [AddCommGroup M] {R : Type*} [CommRing R] [Module R M] (I : Ideal R)
variable (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤)

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
  refine ⟨fun ⟨f, h⟩ => ⟨Finsupp.mapRange.linearMap I.subtype f, fun i => (f i).2, h⟩, ?_⟩
  rintro ⟨a, ha, rfl⟩
  classical
    refine ⟨a.mapRange (fun r => if h : r ∈ I then ⟨r, h⟩ else 0) (by simp), ?_⟩
    rw [finsuppTotal_apply, Finsupp.sum_mapRange_index]
    · apply Finsupp.sum_congr
      intro i _
      rw [dif_pos (ha i)]
    · exact fun _ => zero_smul _ _
#align ideal.range_finsupp_total Ideal.range_finsuppTotal

end Total

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
  rw [Associates.mk_ne_zero, Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
#align associates.mk_ne_zero' Associates.mk_ne_zero'

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

@[simp]
theorem set_smul_top_eq_span (s : Set R) :
    s • ⊤ = Ideal.span s :=
  Eq.trans (span_smul_eq s ⊤).symm <|
    Eq.trans (smul_eq_mul (Ideal R)) (Ideal.mul_top (.span s))

end Submodule
