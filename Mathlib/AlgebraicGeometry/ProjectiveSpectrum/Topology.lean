/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Johan Commelin
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Data.Set.Subsingleton

/-!
# Projective spectrum of a graded ring

The projective spectrum of a graded commutative ring is the subtype of all homogeneous ideals that
are prime and do not contain the irrelevant ideal.
It is naturally endowed with a topology: the Zariski topology.

## Notation
- `A` is a commutative ring
- `σ` is a class of additive submonoids of `A`
- `𝒜 : ℕ → σ` is the grading of `A`;

## Main definitions

* `ProjectiveSpectrum 𝒜`: The projective spectrum of a graded ring `A`, or equivalently, the set of
  all homogeneous ideals of `A` that is both prime and relevant i.e. not containing irrelevant
  ideal. Henceforth, we call elements of projective spectrum *relevant homogeneous prime ideals*.
* `ProjectiveSpectrum.zeroLocus 𝒜 s`: The zero locus of a subset `s` of `A`
  is the subset of `ProjectiveSpectrum 𝒜` consisting of all relevant homogeneous prime ideals that
  contain `s`.
* `ProjectiveSpectrum.vanishingIdeal t`: The vanishing ideal of a subset `t` of
  `ProjectiveSpectrum 𝒜` is the intersection of points in `t` (viewed as relevant homogeneous prime
  ideals).
* `ProjectiveSpectrum.Top`: the topological space of `ProjectiveSpectrum 𝒜` endowed with the
  Zariski topology.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


noncomputable section

open DirectSum Pointwise SetLike TopCat TopologicalSpace CategoryTheory Opposite

variable {A σ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The projective spectrum of a graded commutative ring is the subtype of all homogeneous ideals
that are prime and do not contain the irrelevant ideal. -/
@[ext]
structure ProjectiveSpectrum where
  asHomogeneousIdeal : HomogeneousIdeal 𝒜
  isPrime : asHomogeneousIdeal.toIdeal.IsPrime
  not_irrelevant_le : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ asHomogeneousIdeal

attribute [instance] ProjectiveSpectrum.isPrime

namespace ProjectiveSpectrum

instance (x : ProjectiveSpectrum 𝒜) : Ideal.IsPrime x.asHomogeneousIdeal.toIdeal := x.isPrime

/-- The zero locus of a set `s` of elements of a commutative ring `A` is the set of all relevant
homogeneous prime ideals of the ring that contain the set `s`.

An element `f` of `A` can be thought of as a dependent function on the projective spectrum of `𝒜`.
At a point `x` (a homogeneous prime ideal) the function (i.e., element) `f` takes values in the
quotient ring `A` modulo the prime ideal `x`. In this manner, `zeroLocus s` is exactly the subset
of `ProjectiveSpectrum 𝒜` where all "functions" in `s` vanish simultaneously. -/
def zeroLocus (s : Set A) : Set (ProjectiveSpectrum 𝒜) :=
  { x | s ⊆ x.asHomogeneousIdeal }

@[simp]
theorem mem_zeroLocus (x : ProjectiveSpectrum 𝒜) (s : Set A) :
    x ∈ zeroLocus 𝒜 s ↔ s ⊆ x.asHomogeneousIdeal :=
  Iff.rfl

@[simp]
theorem zeroLocus_span (s : Set A) : zeroLocus 𝒜 (Ideal.span s) = zeroLocus 𝒜 s := by
  ext x
  exact (Submodule.gi _ _).gc s x.asHomogeneousIdeal.toIdeal

variable {𝒜}

/-- The vanishing ideal of a set `t` of points of the projective spectrum of a commutative ring `R`
is the intersection of all the relevant homogeneous prime ideals in the set `t`.

An element `f` of `A` can be thought of as a dependent function on the projective spectrum of `𝒜`.
At a point `x` (a homogeneous prime ideal) the function (i.e., element) `f` takes values in the
quotient ring `A` modulo the prime ideal `x`. In this manner, `vanishingIdeal t` is exactly the
ideal of `A` consisting of all "functions" that vanish on all of `t`. -/
def vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) : HomogeneousIdeal 𝒜 :=
  ⨅ (x : ProjectiveSpectrum 𝒜) (_ : x ∈ t), x.asHomogeneousIdeal

theorem coe_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) :
    (vanishingIdeal t : Set A) =
      { f | ∀ x : ProjectiveSpectrum 𝒜, x ∈ t → f ∈ x.asHomogeneousIdeal } := by
  ext f
  rw [vanishingIdeal, SetLike.mem_coe, ← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_iInf,
    Submodule.mem_iInf]
  refine forall_congr' fun x => ?_
  rw [HomogeneousIdeal.toIdeal_iInf, Submodule.mem_iInf, HomogeneousIdeal.mem_iff]

theorem mem_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) (f : A) :
    f ∈ vanishingIdeal t ↔ ∀ x : ProjectiveSpectrum 𝒜, x ∈ t → f ∈ x.asHomogeneousIdeal := by
  rw [← SetLike.mem_coe, coe_vanishingIdeal, Set.mem_setOf_eq]

@[simp]
theorem vanishingIdeal_singleton (x : ProjectiveSpectrum 𝒜) :
    vanishingIdeal ({x} : Set (ProjectiveSpectrum 𝒜)) = x.asHomogeneousIdeal := by
  simp [vanishingIdeal]

theorem subset_zeroLocus_iff_le_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) (I : Ideal A) :
    t ⊆ zeroLocus 𝒜 I ↔ I ≤ (vanishingIdeal t).toIdeal :=
  ⟨fun h _ k => (mem_vanishingIdeal _ _).mpr fun _ j => (mem_zeroLocus _ _ _).mpr (h j) k, fun h =>
    fun x j =>
    (mem_zeroLocus _ _ _).mpr (le_trans h fun _ h => ((mem_vanishingIdeal _ _).mp h) x j)⟩

variable (𝒜)

/-- `zeroLocus` and `vanishingIdeal` form a Galois connection. -/
theorem gc_ideal :
    @GaloisConnection (Ideal A) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _
      (fun I => zeroLocus 𝒜 I) fun t => (vanishingIdeal t).toIdeal :=
  fun I t => subset_zeroLocus_iff_le_vanishingIdeal t I

/-- `zeroLocus` and `vanishingIdeal` form a Galois connection. -/
theorem gc_set :
    @GaloisConnection (Set A) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _
      (fun s => zeroLocus 𝒜 s) fun t => vanishingIdeal t := by
  have ideal_gc : GaloisConnection Ideal.span _ := (Submodule.gi A _).gc
  simpa [zeroLocus_span, Function.comp_def] using GaloisConnection.compose ideal_gc (gc_ideal 𝒜)

theorem gc_homogeneousIdeal :
    @GaloisConnection (HomogeneousIdeal 𝒜) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _
      (fun I => zeroLocus 𝒜 I) fun t => vanishingIdeal t :=
  fun I t => by
  simpa [show I.toIdeal ≤ (vanishingIdeal t).toIdeal ↔ I ≤ vanishingIdeal t from Iff.rfl] using
    subset_zeroLocus_iff_le_vanishingIdeal t I.toIdeal

theorem subset_zeroLocus_iff_subset_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) (s : Set A) :
    t ⊆ zeroLocus 𝒜 s ↔ s ⊆ vanishingIdeal t :=
  (gc_set _) s t

theorem subset_vanishingIdeal_zeroLocus (s : Set A) : s ⊆ vanishingIdeal (zeroLocus 𝒜 s) :=
  (gc_set _).le_u_l s

theorem ideal_le_vanishingIdeal_zeroLocus (I : Ideal A) :
    I ≤ (vanishingIdeal (zeroLocus 𝒜 I)).toIdeal :=
  (gc_ideal _).le_u_l I

theorem homogeneousIdeal_le_vanishingIdeal_zeroLocus (I : HomogeneousIdeal 𝒜) :
    I ≤ vanishingIdeal (zeroLocus 𝒜 I) :=
  (gc_homogeneousIdeal _).le_u_l I

theorem subset_zeroLocus_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) :
    t ⊆ zeroLocus 𝒜 (vanishingIdeal t) :=
  (gc_ideal _).l_u_le t

theorem zeroLocus_anti_mono {s t : Set A} (h : s ⊆ t) : zeroLocus 𝒜 t ⊆ zeroLocus 𝒜 s :=
  (gc_set _).monotone_l h

theorem zeroLocus_anti_mono_ideal {s t : Ideal A} (h : s ≤ t) :
    zeroLocus 𝒜 (t : Set A) ⊆ zeroLocus 𝒜 (s : Set A) :=
  (gc_ideal _).monotone_l h

theorem zeroLocus_anti_mono_homogeneousIdeal {s t : HomogeneousIdeal 𝒜} (h : s ≤ t) :
    zeroLocus 𝒜 (t : Set A) ⊆ zeroLocus 𝒜 (s : Set A) :=
  (gc_homogeneousIdeal _).monotone_l h

theorem vanishingIdeal_anti_mono {s t : Set (ProjectiveSpectrum 𝒜)} (h : s ⊆ t) :
    vanishingIdeal t ≤ vanishingIdeal s :=
  (gc_ideal _).monotone_u h

theorem zeroLocus_bot : zeroLocus 𝒜 ((⊥ : Ideal A) : Set A) = Set.univ :=
  (gc_ideal 𝒜).l_bot

@[simp]
theorem zeroLocus_singleton_zero : zeroLocus 𝒜 ({0} : Set A) = Set.univ :=
  zeroLocus_bot _

@[simp]
theorem zeroLocus_empty : zeroLocus 𝒜 (∅ : Set A) = Set.univ :=
  (gc_set 𝒜).l_bot

@[simp]
theorem vanishingIdeal_univ : vanishingIdeal (∅ : Set (ProjectiveSpectrum 𝒜)) = ⊤ := by
  simpa using (gc_ideal _).u_top

theorem zeroLocus_empty_of_one_mem {s : Set A} (h : (1 : A) ∈ s) : zeroLocus 𝒜 s = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
    (inferInstance : x.asHomogeneousIdeal.toIdeal.IsPrime).ne_top <|
      x.asHomogeneousIdeal.toIdeal.eq_top_iff_one.mpr <| hx h

@[simp]
theorem zeroLocus_singleton_one : zeroLocus 𝒜 ({1} : Set A) = ∅ :=
  zeroLocus_empty_of_one_mem 𝒜 (Set.mem_singleton (1 : A))

@[simp]
theorem zeroLocus_univ : zeroLocus 𝒜 (Set.univ : Set A) = ∅ :=
  zeroLocus_empty_of_one_mem _ (Set.mem_univ 1)

theorem zeroLocus_sup_ideal (I J : Ideal A) :
    zeroLocus 𝒜 ((I ⊔ J : Ideal A) : Set A) = zeroLocus _ I ∩ zeroLocus _ J :=
  (gc_ideal 𝒜).l_sup

theorem zeroLocus_sup_homogeneousIdeal (I J : HomogeneousIdeal 𝒜) :
    zeroLocus 𝒜 ((I ⊔ J : HomogeneousIdeal 𝒜) : Set A) = zeroLocus _ I ∩ zeroLocus _ J :=
  (gc_homogeneousIdeal 𝒜).l_sup

theorem zeroLocus_union (s s' : Set A) : zeroLocus 𝒜 (s ∪ s') = zeroLocus _ s ∩ zeroLocus _ s' :=
  (gc_set 𝒜).l_sup

theorem vanishingIdeal_union (t t' : Set (ProjectiveSpectrum 𝒜)) :
    vanishingIdeal (t ∪ t') = vanishingIdeal t ⊓ vanishingIdeal t' := by
  ext1; exact (gc_ideal 𝒜).u_inf

theorem zeroLocus_iSup_ideal {γ : Sort*} (I : γ → Ideal A) :
    zeroLocus _ ((⨆ i, I i : Ideal A) : Set A) = ⋂ i, zeroLocus 𝒜 (I i) :=
  (gc_ideal 𝒜).l_iSup

theorem zeroLocus_iSup_homogeneousIdeal {γ : Sort*} (I : γ → HomogeneousIdeal 𝒜) :
    zeroLocus _ ((⨆ i, I i : HomogeneousIdeal 𝒜) : Set A) = ⋂ i, zeroLocus 𝒜 (I i) :=
  (gc_homogeneousIdeal 𝒜).l_iSup

theorem zeroLocus_iUnion {γ : Sort*} (s : γ → Set A) :
    zeroLocus 𝒜 (⋃ i, s i) = ⋂ i, zeroLocus 𝒜 (s i) :=
  (gc_set 𝒜).l_iSup

theorem zeroLocus_bUnion (s : Set (Set A)) :
    zeroLocus 𝒜 (⋃ s' ∈ s, s' : Set A) = ⋂ s' ∈ s, zeroLocus 𝒜 s' := by
  simp only [zeroLocus_iUnion]

theorem vanishingIdeal_iUnion {γ : Sort*} (t : γ → Set (ProjectiveSpectrum 𝒜)) :
    vanishingIdeal (⋃ i, t i) = ⨅ i, vanishingIdeal (t i) :=
  HomogeneousIdeal.toIdeal_injective <| by
    convert (gc_ideal 𝒜).u_iInf; exact HomogeneousIdeal.toIdeal_iInf _

theorem zeroLocus_inf (I J : Ideal A) :
    zeroLocus 𝒜 ((I ⊓ J : Ideal A) : Set A) = zeroLocus 𝒜 I ∪ zeroLocus 𝒜 J :=
  Set.ext fun x => x.isPrime.inf_le

theorem union_zeroLocus (s s' : Set A) :
    zeroLocus 𝒜 s ∪ zeroLocus 𝒜 s' = zeroLocus 𝒜 (Ideal.span s ⊓ Ideal.span s' : Ideal A) := by
  rw [zeroLocus_inf]
  simp

theorem zeroLocus_mul_ideal (I J : Ideal A) :
    zeroLocus 𝒜 ((I * J : Ideal A) : Set A) = zeroLocus 𝒜 I ∪ zeroLocus 𝒜 J :=
  Set.ext fun x => x.isPrime.mul_le

theorem zeroLocus_mul_homogeneousIdeal (I J : HomogeneousIdeal 𝒜) :
    zeroLocus 𝒜 ((I * J : HomogeneousIdeal 𝒜) : Set A) = zeroLocus 𝒜 I ∪ zeroLocus 𝒜 J :=
  Set.ext fun x => x.isPrime.mul_le

theorem zeroLocus_singleton_mul (f g : A) :
    zeroLocus 𝒜 ({f * g} : Set A) = zeroLocus 𝒜 {f} ∪ zeroLocus 𝒜 {g} :=
  Set.ext fun x => by simpa using x.isPrime.mul_mem_iff_mem_or_mem

@[simp]
theorem zeroLocus_singleton_pow (f : A) (n : ℕ) (hn : 0 < n) :
    zeroLocus 𝒜 ({f ^ n} : Set A) = zeroLocus 𝒜 {f} :=
  Set.ext fun x => by simpa using x.isPrime.pow_mem_iff_mem n hn

theorem sup_vanishingIdeal_le (t t' : Set (ProjectiveSpectrum 𝒜)) :
    vanishingIdeal t ⊔ vanishingIdeal t' ≤ vanishingIdeal (t ∩ t') := by
  intro r
  rw [← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_sup, mem_vanishingIdeal,
    Submodule.mem_sup]
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩
  rw [HomogeneousIdeal.mem_iff, mem_vanishingIdeal] at hf hg
  apply Submodule.add_mem <;> solve_by_elim

theorem mem_compl_zeroLocus_iff_notMem {f : A} {I : ProjectiveSpectrum 𝒜} :
    I ∈ (zeroLocus 𝒜 {f} : Set (ProjectiveSpectrum 𝒜))ᶜ ↔ f ∉ I.asHomogeneousIdeal := by
  rw [Set.mem_compl_iff, mem_zeroLocus, Set.singleton_subset_iff]; rfl

/-- The Zariski topology on the prime spectrum of a commutative ring is defined via the closed sets
of the topology: they are exactly those sets that are the zero locus of a subset of the ring. -/
instance zariskiTopology : TopologicalSpace (ProjectiveSpectrum 𝒜) :=
  TopologicalSpace.ofClosed (Set.range (ProjectiveSpectrum.zeroLocus 𝒜)) ⟨Set.univ, by simp⟩
    (by
      intro Zs h
      rw [Set.sInter_eq_iInter]
      let f : Zs → Set _ := fun i => Classical.choose (h i.2)
      have H : (Set.iInter fun i ↦ zeroLocus 𝒜 (f i)) ∈ Set.range (zeroLocus 𝒜) :=
        ⟨_, zeroLocus_iUnion 𝒜 _⟩
      convert H using 2
      funext i
      exact (Classical.choose_spec (h i.2)).symm)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      exact ⟨_, (union_zeroLocus 𝒜 s t).symm⟩)

/-- The underlying topology of `Proj` is the projective spectrum of graded ring `A`. -/
def top : TopCat :=
  TopCat.of (ProjectiveSpectrum 𝒜)

theorem isOpen_iff (U : Set (ProjectiveSpectrum 𝒜)) : IsOpen U ↔ ∃ s, Uᶜ = zeroLocus 𝒜 s := by
  simp only [@eq_comm _ Uᶜ]; rfl

theorem isClosed_iff_zeroLocus (Z : Set (ProjectiveSpectrum 𝒜)) :
    IsClosed Z ↔ ∃ s, Z = zeroLocus 𝒜 s := by rw [← isOpen_compl_iff, isOpen_iff, compl_compl]

theorem isClosed_zeroLocus (s : Set A) : IsClosed (zeroLocus 𝒜 s) := by
  rw [isClosed_iff_zeroLocus]
  exact ⟨s, rfl⟩

theorem zeroLocus_vanishingIdeal_eq_closure (t : Set (ProjectiveSpectrum 𝒜)) :
    zeroLocus 𝒜 (vanishingIdeal t : Set A) = closure t := by
  apply Set.Subset.antisymm
  · rintro x hx t' ⟨ht', ht⟩
    obtain ⟨fs, rfl⟩ : ∃ s, t' = zeroLocus 𝒜 s := by rwa [isClosed_iff_zeroLocus] at ht'
    rw [subset_zeroLocus_iff_subset_vanishingIdeal] at ht
    exact Set.Subset.trans ht hx
  · rw [(isClosed_zeroLocus _ _).closure_subset_iff]
    exact subset_zeroLocus_vanishingIdeal 𝒜 t

theorem vanishingIdeal_closure (t : Set (ProjectiveSpectrum 𝒜)) :
    vanishingIdeal (closure t) = vanishingIdeal t := by
  have : (vanishingIdeal (zeroLocus 𝒜 (vanishingIdeal t))).toIdeal = _ := (gc_ideal 𝒜).u_l_u_eq_u t
  ext1
  rw [zeroLocus_vanishingIdeal_eq_closure 𝒜 t] at this
  exact this

section BasicOpen

/-- `basicOpen r` is the open subset containing all prime ideals not containing `r`. -/
def basicOpen (r : A) : TopologicalSpace.Opens (ProjectiveSpectrum 𝒜) where
  carrier := { x | r ∉ x.asHomogeneousIdeal }
  is_open' := ⟨{r}, Set.ext fun _ => Set.singleton_subset_iff.trans <| Classical.not_not.symm⟩

@[simp]
theorem mem_basicOpen (f : A) (x : ProjectiveSpectrum 𝒜) :
    x ∈ basicOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal :=
  Iff.rfl

theorem mem_coe_basicOpen (f : A) (x : ProjectiveSpectrum 𝒜) :
    x ∈ (↑(basicOpen 𝒜 f) : Set (ProjectiveSpectrum 𝒜)) ↔ f ∉ x.asHomogeneousIdeal :=
  Iff.rfl

theorem isOpen_basicOpen {a : A} : IsOpen (basicOpen 𝒜 a : Set (ProjectiveSpectrum 𝒜)) :=
  (basicOpen 𝒜 a).isOpen

@[simp]
theorem basicOpen_eq_zeroLocus_compl (r : A) :
    (basicOpen 𝒜 r : Set (ProjectiveSpectrum 𝒜)) = (zeroLocus 𝒜 {r})ᶜ :=
  Set.ext fun x => by simp only [Set.mem_compl_iff, mem_zeroLocus, Set.singleton_subset_iff]; rfl

@[simp]
theorem basicOpen_one : basicOpen 𝒜 (1 : A) = ⊤ :=
  TopologicalSpace.Opens.ext <| by simp

@[simp]
theorem basicOpen_zero : basicOpen 𝒜 (0 : A) = ⊥ :=
  TopologicalSpace.Opens.ext <| by simp

theorem basicOpen_mul (f g : A) : basicOpen 𝒜 (f * g) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g :=
  TopologicalSpace.Opens.ext <| by simp [zeroLocus_singleton_mul]

theorem basicOpen_mul_le_left (f g : A) : basicOpen 𝒜 (f * g) ≤ basicOpen 𝒜 f := by
  rw [basicOpen_mul 𝒜 f g]
  exact inf_le_left

theorem basicOpen_mul_le_right (f g : A) : basicOpen 𝒜 (f * g) ≤ basicOpen 𝒜 g := by
  rw [basicOpen_mul 𝒜 f g]
  exact inf_le_right

@[simp]
theorem basicOpen_pow (f : A) (n : ℕ) (hn : 0 < n) : basicOpen 𝒜 (f ^ n) = basicOpen 𝒜 f :=
  TopologicalSpace.Opens.ext <| by simpa using zeroLocus_singleton_pow 𝒜 f n hn

theorem basicOpen_eq_union_of_projection (f : A) :
    basicOpen 𝒜 f = ⨆ i : ℕ, basicOpen 𝒜 (GradedRing.proj 𝒜 i f) :=
  TopologicalSpace.Opens.ext <|
    Set.ext fun z => by
      rw [mem_coe_basicOpen, mem_coe, iSup, TopologicalSpace.Opens.mem_sSup]
      constructor <;> intro hz
      · rcases show ∃ i, GradedRing.proj 𝒜 i f ∉ z.asHomogeneousIdeal by
          contrapose! hz with H
          classical
          rw [← DirectSum.sum_support_decompose 𝒜 f]
          apply Ideal.sum_mem _ fun i _ => H i with ⟨i, hi⟩
        exact ⟨basicOpen 𝒜 (GradedRing.proj 𝒜 i f), ⟨i, rfl⟩, by rwa [mem_basicOpen]⟩
      · obtain ⟨_, ⟨i, rfl⟩, hz⟩ := hz
        exact fun rid => hz (z.1.2 i rid)

theorem isTopologicalBasis_basic_opens :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun r : A => (basicOpen 𝒜 r : Set (ProjectiveSpectrum 𝒜))) := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨r, rfl⟩
    exact isOpen_basicOpen 𝒜
  · rintro p U hp ⟨s, hs⟩
    rw [← compl_compl U, Set.mem_compl_iff, ← hs, mem_zeroLocus, Set.not_subset] at hp
    obtain ⟨f, hfs, hfp⟩ := hp
    refine ⟨basicOpen 𝒜 f, ⟨f, rfl⟩, hfp, ?_⟩
    rw [← Set.compl_subset_compl, ← hs, basicOpen_eq_zeroLocus_compl, compl_compl]
    exact zeroLocus_anti_mono 𝒜 (Set.singleton_subset_iff.mpr hfs)

end BasicOpen

section Order

/-!
## The specialization order

We endow `ProjectiveSpectrum 𝒜` with a partial order,
where `x ≤ y` if and only if `y ∈ closure {x}`.
-/


instance : PartialOrder (ProjectiveSpectrum 𝒜) :=
  PartialOrder.lift asHomogeneousIdeal fun ⟨_, _, _⟩ ⟨_, _, _⟩ => by simp only [mk.injEq, imp_self]

@[simp]
theorem as_ideal_le_as_ideal (x y : ProjectiveSpectrum 𝒜) :
    x.asHomogeneousIdeal ≤ y.asHomogeneousIdeal ↔ x ≤ y :=
  Iff.rfl

@[simp]
theorem as_ideal_lt_as_ideal (x y : ProjectiveSpectrum 𝒜) :
    x.asHomogeneousIdeal < y.asHomogeneousIdeal ↔ x < y :=
  Iff.rfl

theorem le_iff_mem_closure (x y : ProjectiveSpectrum 𝒜) :
    x ≤ y ↔ y ∈ closure ({x} : Set (ProjectiveSpectrum 𝒜)) := by
  rw [← as_ideal_le_as_ideal, ← zeroLocus_vanishingIdeal_eq_closure, mem_zeroLocus,
    vanishingIdeal_singleton]
  simp only [as_ideal_le_as_ideal, coe_subset_coe]

end Order

end ProjectiveSpectrum
