/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.Submodule.EqLocus
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.Ring.Idempotents
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Order.OmegaCompletePartialOrder

/-!
# The span of a set of vectors, as a submodule

* `Submodule.span s` is defined to be the smallest submodule containing the set `s`.

## Notations

* We introduce the notation `R ∙ v` for the span of a singleton, `Submodule.span R {v}`.  This is
  `\span`, not the same as the scalar multiplication `•`/`\bub`.

-/

variable {R R₂ K M M₂ V S : Type*}

namespace Submodule

open Function Set

open Pointwise

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable {x : M} (p p' : Submodule R M)
variable [Semiring R₂] {σ₁₂ : R →+* R₂}
variable [AddCommMonoid M₂] [Module R₂ M₂]
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂]

variable {s t : Set M}

/-- A version of `Submodule.span_eq` for when the span is by a smaller ring. -/
@[simp]
theorem span_coe_eq_restrictScalars [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :
    span S (p : Set M) = p.restrictScalars S :=
  span_eq (p.restrictScalars S)

include σ₁₂ in
/-- A version of `Submodule.map_span_le` that does not require the `RingHomSurjective`
assumption. -/
theorem image_span_subset (f : F) (s : Set M) (N : Submodule R₂ M₂) :
    f '' span R s ⊆ N ↔ ∀ m ∈ s, f m ∈ N := image_subset_iff.trans <| span_le (p := N.comap f)

include σ₁₂ in
theorem image_span_subset_span (f : F) (s : Set M) : f '' span R s ⊆ span R₂ (f '' s) :=
  (image_span_subset f s _).2 fun x hx ↦ subset_span ⟨x, hx, rfl⟩

theorem map_span [RingHomSurjective σ₁₂] (f : F) (s : Set M) :
    (span R s).map f = span R₂ (f '' s) :=
  Eq.symm <| span_eq_of_le _ (Set.image_subset f subset_span) (image_span_subset_span f s)

alias _root_.LinearMap.map_span := Submodule.map_span

theorem map_span_le [RingHomSurjective σ₁₂] (f : F) (s : Set M) (N : Submodule R₂ M₂) :
    map f (span R s) ≤ N ↔ ∀ m ∈ s, f m ∈ N := image_span_subset f s N

alias _root_.LinearMap.map_span_le := Submodule.map_span_le

-- See also `span_preimage_eq` below.
theorem span_preimage_le (f : F) (s : Set M₂) :
    span R (f ⁻¹' s) ≤ (span R₂ s).comap f := by
  rw [span_le, comap_coe]
  exact preimage_mono subset_span

alias _root_.LinearMap.span_preimage_le := Submodule.span_preimage_le

section

variable {N : Type*} [AddCommMonoid N] [Module R N]

lemma linearMap_eq_iff_of_eq_span {V : Submodule R M} (f g : V →ₗ[R] N)
    {S : Set M} (hV : V = span R S) :
    f = g ↔ ∀ (s : S), f ⟨s, by simpa only [hV] using subset_span (by simp)⟩ =
      g ⟨s, by simpa only [hV] using subset_span (by simp)⟩ := by
  constructor
  · rintro rfl _
    rfl
  · intro h
    subst hV
    suffices ∀ (x : M) (hx : x ∈ span R S), f ⟨x, hx⟩ = g ⟨x, hx⟩ by
      ext ⟨x, hx⟩
      exact this x hx
    intro x hx
    induction hx using span_induction with
    | mem x hx => exact h ⟨x, hx⟩
    | zero => erw [map_zero, map_zero]
    | add x y hx hy hx' hy' =>
        erw [f.map_add ⟨x, hx⟩ ⟨y, hy⟩, g.map_add ⟨x, hx⟩ ⟨y, hy⟩]
        rw [hx', hy']
    | smul a x hx hx' =>
        erw [f.map_smul a ⟨x, hx⟩, g.map_smul a ⟨x, hx⟩]
        rw [hx']

lemma linearMap_eq_iff_of_span_eq_top (f g : M →ₗ[R] N)
    {S : Set M} (hM : span R S = ⊤) :
    f = g ↔ ∀ (s : S), f s = g s := by
  convert linearMap_eq_iff_of_eq_span (f.comp (Submodule.subtype _))
    (g.comp (Submodule.subtype _)) hM.symm
  constructor
  · rintro rfl
    rfl
  · intro h
    ext x
    exact DFunLike.congr_fun h ⟨x, by simp⟩

lemma linearMap_eq_zero_iff_of_span_eq_top (f : M →ₗ[R] N)
    {S : Set M} (hM : span R S = ⊤) :
    f = 0 ↔ ∀ (s : S), f s = 0 :=
  linearMap_eq_iff_of_span_eq_top f 0 hM

lemma linearMap_eq_zero_iff_of_eq_span {V : Submodule R M} (f : V →ₗ[R] N)
    {S : Set M} (hV : V = span R S) :
    f = 0 ↔ ∀ (s : S), f ⟨s, by simpa only [hV] using subset_span (by simp)⟩ = 0 :=
  linearMap_eq_iff_of_eq_span f 0 hV

end

/-- See `Submodule.span_smul_eq` (in `RingTheory.Ideal.Operations`) for
`span R (r • s) = r • span R s` that holds for arbitrary `r` in a `CommSemiring`. -/
theorem span_smul_eq_of_isUnit (s : Set M) (r : R) (hr : IsUnit r) : span R (r • s) = span R s := by
  apply le_antisymm
  · apply span_smul_le
  · convert span_smul_le (r • s) ((hr.unit⁻¹ : _) : R)
    rw [smul_smul]
    erw [hr.unit.inv_val]
    rw [one_smul]

/-- We can regard `coe_iSup_of_chain` as the statement that `(↑) : (Submodule R M) → Set M` is
Scott continuous for the ω-complete partial order induced by the complete lattice structures. -/
theorem coe_scott_continuous :
    OmegaCompletePartialOrder.ωScottContinuous ((↑) : Submodule R M → Set M) :=
  OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup
    ⟨SetLike.coe_mono, coe_iSup_of_chain⟩

theorem disjoint_span_singleton {K E : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    {s : Submodule K E} {x : E} : Disjoint s (K ∙ x) ↔ x ∈ s → x = 0 := by
  refine disjoint_def.trans ⟨fun H hx => H x hx <| subset_span <| mem_singleton x, ?_⟩
  intro H y hy hyx
  obtain ⟨c, rfl⟩ := mem_span_singleton.1 hyx
  by_cases hc : c = 0
  · rw [hc, zero_smul]
  · rw [s.smul_mem_iff hc] at hy
    rw [H hy, smul_zero]

theorem disjoint_span_singleton' {K E : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    {p : Submodule K E} {x : E} (x0 : x ≠ 0) : Disjoint p (K ∙ x) ↔ x ∉ p :=
  disjoint_span_singleton.trans ⟨fun h₁ h₂ => x0 (h₁ h₂), fun h₁ h₂ => (h₁ h₂).elim⟩

variable (R S s)

/-- If `R` is "smaller" ring than `S` then the span by `R` is smaller than the span by `S`. -/
theorem span_le_restrictScalars [Semiring S] [SMul R S] [Module S M] [IsScalarTower R S M] :
    span R s ≤ (span S s).restrictScalars R :=
  Submodule.span_le.2 Submodule.subset_span

/-- A version of `Submodule.span_le_restrictScalars` with coercions. -/
@[simp]
theorem span_subset_span [Semiring S] [SMul R S] [Module S M] [IsScalarTower R S M] :
    ↑(span R s) ⊆ (span S s : Set M) :=
  span_le_restrictScalars R S s

/-- Taking the span by a large ring of the span by the small ring is the same as taking the span
by just the large ring. -/
theorem span_span_of_tower [Semiring S] [SMul R S] [Module S M] [IsScalarTower R S M] :
    span S (span R s : Set M) = span S s :=
  le_antisymm (span_le.2 <| span_subset_span R S s) (span_mono subset_span)

variable {R S s}

theorem span_singleton_eq_span_singleton {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [NoZeroSMulDivisors R M] {x y : M} : ((R ∙ x) = R ∙ y) ↔ ∃ z : Rˣ, z • x = y := by
  constructor
  · simp only [le_antisymm_iff, span_singleton_le_iff_mem, mem_span_singleton]
    rintro ⟨⟨a, rfl⟩, b, hb⟩
    rcases eq_or_ne y 0 with rfl | hy; · simp
    refine ⟨⟨b, a, ?_, ?_⟩, hb⟩
    · apply smul_left_injective R hy
      simpa only [mul_smul, one_smul]
    · rw [← hb] at hy
      apply smul_left_injective R (smul_ne_zero_iff.1 hy).2
      simp only [mul_smul, one_smul, hb]
  · rintro ⟨u, rfl⟩
    exact (span_singleton_group_smul_eq _ _ _).symm

-- Should be `@[simp]` but doesn't fire due to https://github.com/leanprover/lean4/pull/3701.
theorem span_image [RingHomSurjective σ₁₂] (f : F) :
    span R₂ (f '' s) = map f (span R s) :=
  (map_span f s).symm

@[simp] -- Should be replaced with `Submodule.span_image` when https://github.com/leanprover/lean4/pull/3701 is fixed.
theorem span_image' [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) :
    span R₂ (f '' s) = map f (span R s) :=
  span_image _

theorem apply_mem_span_image_of_mem_span [RingHomSurjective σ₁₂] (f : F) {x : M}
    {s : Set M} (h : x ∈ Submodule.span R s) : f x ∈ Submodule.span R₂ (f '' s) := by
  rw [Submodule.span_image]
  exact Submodule.mem_map_of_mem h

theorem apply_mem_span_image_iff_mem_span [RingHomSurjective σ₁₂] {f : F} {x : M}
    {s : Set M} (hf : Function.Injective f) :
    f x ∈ Submodule.span R₂ (f '' s) ↔ x ∈ Submodule.span R s := by
  rw [← Submodule.mem_comap, ← Submodule.map_span, Submodule.comap_map_eq_of_injective hf]

@[simp]
theorem map_subtype_span_singleton {p : Submodule R M} (x : p) :
    map p.subtype (R ∙ x) = R ∙ (x : M) := by simp [← span_image]

/-- `f` is an explicit argument so we can `apply` this theorem and obtain `h` as a new goal. -/
theorem not_mem_span_of_apply_not_mem_span_image [RingHomSurjective σ₁₂] (f : F) {x : M}
    {s : Set M} (h : f x ∉ Submodule.span R₂ (f '' s)) : x ∉ Submodule.span R s :=
  h.imp (apply_mem_span_image_of_mem_span f)

theorem iSup_toAddSubmonoid {ι : Sort*} (p : ι → Submodule R M) :
    (⨆ i, p i).toAddSubmonoid = ⨆ i, (p i).toAddSubmonoid := by
  refine le_antisymm (fun x => ?_) (iSup_le fun i => toAddSubmonoid_mono <| le_iSup _ i)
  simp_rw [iSup_eq_span, AddSubmonoid.iSup_eq_closure, mem_toAddSubmonoid, coe_toAddSubmonoid]
  intro hx
  refine Submodule.span_induction (fun x hx => ?_) ?_ (fun x y _ _ hx hy => ?_)
    (fun r x _ hx => ?_) hx
  · exact AddSubmonoid.subset_closure hx
  · exact AddSubmonoid.zero_mem _
  · exact AddSubmonoid.add_mem _ hx hy
  · refine AddSubmonoid.closure_induction ?_ ?_ ?_ hx
    · rintro x ⟨_, ⟨i, rfl⟩, hix : x ∈ p i⟩
      apply AddSubmonoid.subset_closure (Set.mem_iUnion.mpr ⟨i, _⟩)
      exact smul_mem _ r hix
    · rw [smul_zero]
      exact AddSubmonoid.zero_mem _
    · intro x y _ _ hx hy
      rw [smul_add]
      exact AddSubmonoid.add_mem _ hx hy

/-- An induction principle for elements of `⨆ i, p i`.
If `C` holds for `0` and all elements of `p i` for all `i`, and is preserved under addition,
then it holds for all elements of the supremum of `p`. -/
@[elab_as_elim]
theorem iSup_induction {ι : Sort*} (p : ι → Submodule R M) {C : M → Prop} {x : M}
    (hx : x ∈ ⨆ i, p i) (hp : ∀ (i), ∀ x ∈ p i, C x) (h0 : C 0)
    (hadd : ∀ x y, C x → C y → C (x + y)) : C x := by
  rw [← mem_toAddSubmonoid, iSup_toAddSubmonoid] at hx
  exact AddSubmonoid.iSup_induction (x := x) _ hx hp h0 hadd

/-- A dependent version of `submodule.iSup_induction`. -/
@[elab_as_elim]
theorem iSup_induction' {ι : Sort*} (p : ι → Submodule R M) {C : ∀ x, (x ∈ ⨆ i, p i) → Prop}
    (mem : ∀ (i) (x) (hx : x ∈ p i), C x (mem_iSup_of_mem i hx)) (zero : C 0 (zero_mem _))
    (add : ∀ x y hx hy, C x hx → C y hy → C (x + y) (add_mem ‹_› ‹_›)) {x : M}
    (hx : x ∈ ⨆ i, p i) : C x hx := by
  refine Exists.elim ?_ fun (hx : x ∈ ⨆ i, p i) (hc : C x hx) => hc
  refine iSup_induction p (C := fun x : M ↦ ∃ (hx : x ∈ ⨆ i, p i), C x hx) hx
    (fun i x hx => ?_) ?_ fun x y => ?_
  · exact ⟨_, mem _ _ hx⟩
  · exact ⟨_, zero⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, add _ _ _ _ Cx Cy⟩

theorem singleton_span_isCompactElement (x : M) :
    CompleteLattice.IsCompactElement (span R {x} : Submodule R M) := by
  rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le]
  intro d hemp hdir hsup
  have : x ∈ (sSup d) := (SetLike.le_def.mp hsup) (mem_span_singleton_self x)
  obtain ⟨y, ⟨hyd, hxy⟩⟩ := (mem_sSup_of_directed hemp hdir).mp this
  exact ⟨y, ⟨hyd, by simpa only [span_le, singleton_subset_iff] ⟩⟩

/-- The span of a finite subset is compact in the lattice of submodules. -/
theorem finset_span_isCompactElement (S : Finset M) :
    CompleteLattice.IsCompactElement (span R S : Submodule R M) := by
  rw [span_eq_iSup_of_singleton_spans]
  simp only [Finset.mem_coe]
  rw [← Finset.sup_eq_iSup]
  exact
    CompleteLattice.isCompactElement_finsetSup S fun x _ => singleton_span_isCompactElement x

/-- The span of a finite subset is compact in the lattice of submodules. -/
theorem finite_span_isCompactElement (S : Set M) (h : S.Finite) :
    CompleteLattice.IsCompactElement (span R S : Submodule R M) :=
  Finite.coe_toFinset h ▸ finset_span_isCompactElement h.toFinset

instance : IsCompactlyGenerated (Submodule R M) :=
  ⟨fun s =>
    ⟨(fun x => span R {x}) '' s,
      ⟨fun t ht => by
        rcases (Set.mem_image _ _ _).1 ht with ⟨x, _, rfl⟩
        apply singleton_span_isCompactElement, by
        rw [sSup_eq_iSup, iSup_image, ← span_eq_iSup_of_singleton_spans, span_eq]⟩⟩⟩

variable {M' : Type*} [AddCommMonoid M'] [Module R M'] (q₁ q₁' : Submodule R M')

/-- The product of two submodules is a submodule. -/
def prod : Submodule R (M × M') :=
  { p.toAddSubmonoid.prod q₁.toAddSubmonoid with
    carrier := p ×ˢ q₁
    smul_mem' := by rintro a ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨smul_mem _ a hx, smul_mem _ a hy⟩ }

@[simp]
theorem prod_coe : (prod p q₁ : Set (M × M')) = (p : Set M) ×ˢ (q₁ : Set M') :=
  rfl

@[simp]
theorem mem_prod {p : Submodule R M} {q : Submodule R M'} {x : M × M'} :
    x ∈ prod p q ↔ x.1 ∈ p ∧ x.2 ∈ q :=
  Set.mem_prod

theorem span_prod_le (s : Set M) (t : Set M') : span R (s ×ˢ t) ≤ prod (span R s) (span R t) :=
  span_le.2 <| Set.prod_mono subset_span subset_span

@[simp]
theorem prod_top : (prod ⊤ ⊤ : Submodule R (M × M')) = ⊤ := by ext; simp

@[simp]
theorem prod_bot : (prod ⊥ ⊥ : Submodule R (M × M')) = ⊥ := by ext ⟨x, y⟩; simp

theorem prod_mono {p p' : Submodule R M} {q q' : Submodule R M'} :
    p ≤ p' → q ≤ q' → prod p q ≤ prod p' q' :=
  Set.prod_mono

@[simp]
theorem prod_inf_prod : prod p q₁ ⊓ prod p' q₁' = prod (p ⊓ p') (q₁ ⊓ q₁') :=
  SetLike.coe_injective Set.prod_inter_prod

@[simp]
theorem prod_sup_prod : prod p q₁ ⊔ prod p' q₁' = prod (p ⊔ p') (q₁ ⊔ q₁') := by
  refine le_antisymm
    (sup_le (prod_mono le_sup_left le_sup_left) (prod_mono le_sup_right le_sup_right)) ?_
  simp only [SetLike.le_def, mem_prod, and_imp, Prod.forall]; intro xx yy hxx hyy
  rcases mem_sup.1 hxx with ⟨x, hx, x', hx', rfl⟩
  rcases mem_sup.1 hyy with ⟨y, hy, y', hy', rfl⟩
  exact mem_sup.2 ⟨(x, y), ⟨hx, hy⟩, (x', y'), ⟨hx', hy'⟩, rfl⟩

end AddCommMonoid

section AddCommGroup

variable [Ring R] [AddCommGroup M] [Module R M]

@[simp]
theorem span_neg (s : Set M) : span R (-s) = span R s :=
  calc
    span R (-s) = span R ((-LinearMap.id : M →ₗ[R] M) '' s) := by simp
    _ = map (-LinearMap.id) (span R s) := (map_span (-LinearMap.id) _).symm
    _ = span R s := by simp

instance : IsModularLattice (Submodule R M) :=
  ⟨fun y z xz a ha => by
    rw [mem_inf, mem_sup] at ha
    rcases ha with ⟨⟨b, hb, c, hc, rfl⟩, haz⟩
    rw [mem_sup]
    refine ⟨b, hb, c, mem_inf.2 ⟨hc, ?_⟩, rfl⟩
    rw [← add_sub_cancel_right c b, add_comm]
    apply z.sub_mem haz (xz hb)⟩

lemma isCompl_comap_subtype_of_isCompl_of_le {p q r : Submodule R M}
    (h₁ : IsCompl q r) (h₂ : q ≤ p) :
    IsCompl (q.comap p.subtype) (r.comap p.subtype) := by
  simpa [p.mapIic.isCompl_iff, Iic.isCompl_iff] using Iic.isCompl_inf_inf_of_isCompl_of_le h₁ h₂

end AddCommGroup

section AddCommGroup

variable [Semiring R] [Semiring R₂]
variable [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

theorem comap_map_eq (f : F) (p : Submodule R M) : comap f (map f p) = p ⊔ LinearMap.ker f := by
  refine le_antisymm ?_ (sup_le (le_comap_map _ _) (comap_mono bot_le))
  rintro x ⟨y, hy, e⟩
  exact mem_sup.2 ⟨y, hy, x - y, by simpa using sub_eq_zero.2 e.symm, by simp⟩

theorem comap_map_eq_self {f : F} {p : Submodule R M} (h : LinearMap.ker f ≤ p) :
    comap f (map f p) = p := by rw [Submodule.comap_map_eq, sup_of_le_left h]

lemma _root_.LinearMap.range_domRestrict_eq_range_iff {f : M →ₛₗ[τ₁₂] M₂} {S : Submodule R M} :
    LinearMap.range (f.domRestrict S) = LinearMap.range f ↔ S ⊔ (LinearMap.ker f) = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [eq_top_iff]
    intro x _
    have : f x ∈ LinearMap.range f := LinearMap.mem_range_self f x
    rw [← h] at this
    obtain ⟨y, hy⟩ : ∃ y : S, f.domRestrict S y = f x := this
    have : (y : M) + (x - y) ∈ S ⊔ (LinearMap.ker f) := Submodule.add_mem_sup y.2 (by simp [← hy])
    simpa using this
  · refine le_antisymm (LinearMap.range_domRestrict_le_range f S) ?_
    rintro x ⟨y, rfl⟩
    obtain ⟨s, hs, t, ht, rfl⟩ : ∃ s, s ∈ S ∧ ∃ t, t ∈ LinearMap.ker f ∧ s + t = y :=
      Submodule.mem_sup.1 (by simp [h])
    exact ⟨⟨s, hs⟩, by simp [LinearMap.mem_ker.1 ht]⟩

@[simp] lemma _root_.LinearMap.surjective_domRestrict_iff
    {f : M →ₛₗ[τ₁₂] M₂} {S : Submodule R M} (hf : Surjective f) :
    Surjective (f.domRestrict S) ↔ S ⊔ LinearMap.ker f = ⊤ := by
  rw [← LinearMap.range_eq_top] at hf ⊢
  rw [← hf]
  exact LinearMap.range_domRestrict_eq_range_iff

@[simp]
lemma biSup_comap_subtype_eq_top {ι : Type*} (s : Set ι) (p : ι → Submodule R M) :
    ⨆ i ∈ s, (p i).comap (⨆ i ∈ s, p i).subtype = ⊤ := by
  refine eq_top_iff.mpr fun ⟨x, hx⟩ _ ↦ ?_
  suffices x ∈ (⨆ i ∈ s, (p i).comap (⨆ i ∈ s, p i).subtype).map (⨆ i ∈ s, (p i)).subtype by
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp this
    exact hy
  suffices ∀ i ∈ s, (comap (⨆ i ∈ s, p i).subtype (p i)).map (⨆ i ∈ s, p i).subtype = p i by
    simpa only [map_iSup, biSup_congr this]
  intro i hi
  rw [map_comap_eq, range_subtype, inf_eq_right]
  exact le_biSup p hi

lemma biSup_comap_eq_top_of_surjective {ι : Type*} (s : Set ι) (hs : s.Nonempty)
    (p : ι → Submodule R₂ M₂) (hp : ⨆ i ∈ s, p i = ⊤)
    (f : M →ₛₗ[τ₁₂] M₂) (hf : Surjective f) :
    ⨆ i ∈ s, (p i).comap f = ⊤ := by
  obtain ⟨k, hk⟩ := hs
  suffices (⨆ i ∈ s, (p i).comap f) ⊔ LinearMap.ker f = ⊤ by
    rw [← this, left_eq_sup]; exact le_trans f.ker_le_comap (le_biSup (fun i ↦ (p i).comap f) hk)
  rw [iSup_subtype'] at hp ⊢
  rw [← comap_map_eq, map_iSup_comap_of_sujective hf, hp, comap_top]

lemma biSup_comap_eq_top_of_range_eq_biSup
    {R R₂ : Type*} [Ring R] [Ring R₂] {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]
    [Module R M] [Module R₂ M₂] {ι : Type*} (s : Set ι) (hs : s.Nonempty)
    (p : ι → Submodule R₂ M₂) (f : M →ₛₗ[τ₁₂] M₂) (hf : LinearMap.range f = ⨆ i ∈ s, p i) :
    ⨆ i ∈ s, (p i).comap f = ⊤ := by
  suffices ⨆ i ∈ s, (p i).comap (LinearMap.range f).subtype = ⊤ by
    rw [← biSup_comap_eq_top_of_surjective s hs _ this _ f.surjective_rangeRestrict]; rfl
  exact hf ▸ biSup_comap_subtype_eq_top s p

end AddCommGroup

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- There is no vector subspace between `p` and `(K ∙ x) ⊔ p`, `WCovBy` version. -/
theorem wcovBy_span_singleton_sup (x : V) (p : Submodule K V) : WCovBy p ((K ∙ x) ⊔ p) := by
  refine ⟨le_sup_right, fun q hpq hqp ↦ hqp.not_le ?_⟩
  rcases SetLike.exists_of_lt hpq with ⟨y, hyq, hyp⟩
  obtain ⟨c, z, hz, rfl⟩ : ∃ c : K, ∃ z ∈ p, c • x + z = y := by
    simpa [mem_sup, mem_span_singleton] using hqp.le hyq
  rcases eq_or_ne c 0 with rfl | hc
  · simp [hz] at hyp
  · have : x ∈ q := by
      rwa [q.add_mem_iff_left (hpq.le hz), q.smul_mem_iff hc] at hyq
    simp [hpq.le, this]

/-- There is no vector subspace between `p` and `(K ∙ x) ⊔ p`, `CovBy` version. -/
theorem covBy_span_singleton_sup {x : V} {p : Submodule K V} (h : x ∉ p) : CovBy p ((K ∙ x) ⊔ p) :=
  ⟨by simpa, (wcovBy_span_singleton_sup _ _).2⟩

end DivisionRing

end Submodule

namespace LinearMap

open Submodule Function

section AddCommGroup

variable [Semiring R] [Semiring R₂]
variable [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

protected theorem map_le_map_iff (f : F) {p p'} : map f p ≤ map f p' ↔ p ≤ p' ⊔ ker f := by
  rw [map_le_iff_le_comap, Submodule.comap_map_eq]

theorem map_le_map_iff' {f : F} (hf : ker f = ⊥) {p p'} : map f p ≤ map f p' ↔ p ≤ p' := by
  rw [LinearMap.map_le_map_iff, hf, sup_bot_eq]

theorem map_injective {f : F} (hf : ker f = ⊥) : Injective (map f) := fun _ _ h =>
  le_antisymm ((map_le_map_iff' hf).1 (le_of_eq h)) ((map_le_map_iff' hf).1 (ge_of_eq h))

theorem map_eq_top_iff {f : F} (hf : range f = ⊤) {p : Submodule R M} :
    p.map f = ⊤ ↔ p ⊔ LinearMap.ker f = ⊤ := by
  simp_rw [← top_le_iff, ← hf, range_eq_map, LinearMap.map_le_map_iff]

end AddCommGroup

section

variable (R) (M) [Semiring R] [AddCommMonoid M] [Module R M]

/-- Given an element `x` of a module `M` over `R`, the natural map from
    `R` to scalar multiples of `x`. See also `LinearMap.ringLmapEquivSelf`. -/
@[simps!]
def toSpanSingleton (x : M) : R →ₗ[R] M :=
  LinearMap.id.smulRight x

/-- The range of `toSpanSingleton x` is the span of `x`. -/
theorem span_singleton_eq_range (x : M) : (R ∙ x) = range (toSpanSingleton R M x) :=
  Submodule.ext fun y => by
    refine Iff.trans ?_ LinearMap.mem_range.symm
    exact mem_span_singleton

theorem toSpanSingleton_one (x : M) : toSpanSingleton R M x 1 = x :=
  one_smul _ _

@[simp]
theorem toSpanSingleton_zero : toSpanSingleton R M 0 = 0 := by
  ext
  simp

variable {R M}

theorem toSpanSingleton_isIdempotentElem_iff {e : R} :
    IsIdempotentElem (toSpanSingleton R R e) ↔ IsIdempotentElem e := by
  simp_rw [IsIdempotentElem, LinearMap.ext_iff, mul_apply, toSpanSingleton_apply, smul_eq_mul,
    mul_assoc]
  exact ⟨fun h ↦ by conv_rhs => rw [← one_mul e, ← h, one_mul], fun h _ ↦ by rw [h]⟩

theorem isIdempotentElem_apply_one_iff {f : Module.End R R} :
    IsIdempotentElem (f 1) ↔ IsIdempotentElem f := by
  rw [IsIdempotentElem, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, IsIdempotentElem,
    LinearMap.ext_iff]
  simp_rw [mul_apply]
  exact ⟨fun h r ↦ by rw [← mul_one r, ← smul_eq_mul, map_smul, map_smul, h], (· 1)⟩

end

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [Semiring R₂] [AddCommMonoid M₂] [Module R₂ M₂]
variable {F : Type*} {σ₁₂ : R →+* R₂} [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂]
include σ₁₂

/-- Two linear maps are equal on `Submodule.span s` iff they are equal on `s`. -/
theorem eqOn_span_iff {s : Set M} {f g : F} : Set.EqOn f g (span R s) ↔ Set.EqOn f g s := by
  rw [← le_eqLocus, span_le]; rfl

/-- If two linear maps are equal on a set `s`, then they are equal on `Submodule.span s`.

This version uses `Set.EqOn`, and the hidden argument will expand to `h : x ∈ (span R s : Set M)`.
See `LinearMap.eqOn_span` for a version that takes `h : x ∈ span R s` as an argument. -/
theorem eqOn_span' {s : Set M} {f g : F} (H : Set.EqOn f g s) :
    Set.EqOn f g (span R s : Set M) :=
  eqOn_span_iff.2 H

/-- If two linear maps are equal on a set `s`, then they are equal on `Submodule.span s`.

See also `LinearMap.eqOn_span'` for a version using `Set.EqOn`. -/
theorem eqOn_span {s : Set M} {f g : F} (H : Set.EqOn f g s) ⦃x⦄ (h : x ∈ span R s) :
    f x = g x :=
  eqOn_span' H h

/-- If `s` generates the whole module and linear maps `f`, `g` are equal on `s`, then they are
equal. -/
theorem ext_on {s : Set M} {f g : F} (hv : span R s = ⊤) (h : Set.EqOn f g s) : f = g :=
  DFunLike.ext _ _ fun _ => eqOn_span h (eq_top_iff'.1 hv _)

/-- If the range of `v : ι → M` generates the whole module and linear maps `f`, `g` are equal at
each `v i`, then they are equal. -/
theorem ext_on_range {ι : Sort*} {v : ι → M} {f g : F} (hv : span R (Set.range v) = ⊤)
    (h : ∀ i, f (v i) = g (v i)) : f = g :=
  ext_on hv (Set.forall_mem_range.2 h)

end AddCommMonoid

section NoZeroDivisors

variable (R M)
variable [Ring R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]

theorem ker_toSpanSingleton {x : M} (h : x ≠ 0) : LinearMap.ker (toSpanSingleton R M x) = ⊥ :=
  SetLike.ext fun _ => smul_eq_zero.trans <| or_iff_left_of_imp fun h' => (h h').elim

end NoZeroDivisors

section Field

variable [Field K] [AddCommGroup V] [Module K V]

theorem span_singleton_sup_ker_eq_top (f : V →ₗ[K] K) {x : V} (hx : f x ≠ 0) :
    (K ∙ x) ⊔ ker f = ⊤ :=
  top_unique fun y _ =>
    Submodule.mem_sup.2
      ⟨(f y * (f x)⁻¹) • x, Submodule.mem_span_singleton.2 ⟨f y * (f x)⁻¹, rfl⟩,
        ⟨y - (f y * (f x)⁻¹) • x, by simp [hx]⟩⟩

end Field

end LinearMap

open LinearMap

namespace LinearEquiv

variable (R M)
variable [Ring R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] (x : M) (h : x ≠ 0)

/-- Given a nonzero element `x` of a torsion-free module `M` over a ring `R`, the natural
isomorphism from `R` to the span of `x` given by $r \mapsto r \cdot x$. -/
noncomputable
def toSpanNonzeroSingleton : R ≃ₗ[R] R ∙ x :=
  LinearEquiv.trans
    (LinearEquiv.ofInjective (LinearMap.toSpanSingleton R M x)
      (ker_eq_bot.1 <| ker_toSpanSingleton R M h))
    (LinearEquiv.ofEq (range <| toSpanSingleton R M x) (R ∙ x) (span_singleton_eq_range R M x).symm)

@[simp] theorem toSpanNonzeroSingleton_apply (t : R) :
    LinearEquiv.toSpanNonzeroSingleton R M x h t =
      (⟨t • x, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)⟩ : R ∙ x) := by
  rfl

theorem toSpanNonzeroSingleton_one :
    LinearEquiv.toSpanNonzeroSingleton R M x h 1 =
      (⟨x, Submodule.mem_span_singleton_self x⟩ : R ∙ x) := by simp

/-- Given a nonzero element `x` of a torsion-free module `M` over a ring `R`, the natural
isomorphism from the span of `x` to `R` given by $r \cdot x \mapsto r$. -/
noncomputable
abbrev coord : (R ∙ x) ≃ₗ[R] R :=
  (toSpanNonzeroSingleton R M x h).symm

theorem coord_self : (coord R M x h) (⟨x, Submodule.mem_span_singleton_self x⟩ : R ∙ x) = 1 := by
  rw [← toSpanNonzeroSingleton_one R M x h, LinearEquiv.symm_apply_apply]

theorem coord_apply_smul (y : Submodule.span R ({x} : Set M)) : coord R M x h y • x = y :=
  Subtype.ext_iff.1 <| (toSpanNonzeroSingleton R M x h).apply_symm_apply _

end LinearEquiv
