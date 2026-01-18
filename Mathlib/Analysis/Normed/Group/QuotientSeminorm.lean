/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Analysis.Normed.Group.Seminorm
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Quotient group-seminorms and related constructions
-/

@[expose] public section

open Function Set

namespace GroupSeminorm

section map

variable {E F G : Type*} [Group E] [Group F] [Group G]
variable {p p' : GroupSeminorm E} {q : GroupSeminorm F} {f : E →* F} {g : F →* G}

@[to_additive map_aux0_add]
private lemma map_aux0 (hf : Surjective f) (x : F) :
    Set.Nonempty (p '' (f ⁻¹' {x})) :=
  singleton_nonempty x |>.preimage hf |>.image p

@[to_additive map_aux1_add]
private lemma map_aux1 (hf : Surjective f) (x : F) :
    IsGLB (p '' (f ⁻¹' {x})) (sInf (p '' (f ⁻¹' {x}))) :=
  isGLB_csInf (map_aux0 hf x) ⟨0, forall_mem_image.mpr fun _ _ ↦ apply_nonneg _ _⟩

variable (p f) in
@[to_additive]
protected noncomputable def map : GroupSeminorm F where
  toFun x := open scoped Classical in
    if Surjective f
    then sInf (p '' (f ⁻¹' {x}))
    else 0
  map_one' := by
    split_ifs
    · exact IsLeast.csInf_eq ⟨⟨1, map_one f, map_one_eq_zero p⟩,
        forall_mem_image.mpr fun _ _ ↦ apply_nonneg _ _⟩
    · rfl
  mul_le' x y := by
    split_ifs with hf
    · rw [le_isGLB_iff ((map_aux1 hf x).add (map_aux1 hf y)), mem_lowerBounds,
        ← image2_add, image2_image_left, image2_image_right, forall_mem_image2]
      intro a (ha : f a = x) b (hb : f b = y)
      exact (map_aux1 hf (x * y)).1 (mem_image_of_mem p (by simp [ha, hb]))
        |>.trans (map_mul_le_add p a b)
    · simp
  inv' x := by
    split_ifs with hf
    · congr 1
      refine subset_antisymm ?_ ?_ <;>
      exact image_subset_iff.mpr fun a (ha : f a = _) ↦ ⟨a⁻¹, by simp [ha]⟩
    · simp

open scoped Classical in
@[to_additive]
protected lemma map_def {x : F} :
    p.map f x = if Surjective f then sInf (p '' (f ⁻¹' {x})) else 0 :=
  rfl

@[to_additive]
lemma map_def_of_surjective (hf : Surjective f) {x : F} :
    p.map f x = sInf (p '' (f ⁻¹' {x})) := by
  simp [p.map_def, hf]

@[to_additive]
lemma isGLB_map (hf : Surjective f) (x : F) :
    IsGLB (p '' (f ⁻¹' {x})) (p.map f x) := by
  rw [map_def_of_surjective hf]
  exact map_aux1 hf x

@[to_additive]
lemma le_map_iff (hf : Surjective f) {x : F} {c : ℝ} :
    c ≤ p.map f x ↔ ∀ y ∈ f ⁻¹' {x}, c ≤ p y := by
  rw [le_isGLB_iff (isGLB_map hf x), mem_lowerBounds, forall_mem_image]

@[to_additive]
lemma map_lt_iff (hf : Surjective f) {x : F} {c : ℝ} :
    p.map f x < c ↔ ∃ y ∈ f ⁻¹' {x}, p y < c := by
  contrapose!
  exact le_map_iff hf

@[to_additive]
lemma map_eq_iff_le_iff (hf : Surjective f) {x : F} {c : ℝ} :
    p.map f x = c ↔ (∀ d, d ≤ c ↔ ∀ y ∈ f ⁻¹' {x}, d ≤ p y) :=
  ⟨fun eq d ↦ eq ▸ le_map_iff hf,
    fun H ↦ eq_of_forall_le_iff fun d ↦ by rw [H d, le_map_iff hf]⟩

@[to_additive]
lemma isGLB_map_dist_ker (hf : Surjective f) (y : E) :
    IsGLB ((fun k ↦ p (y / k)) '' (f.ker : Set E)) (p.map f (f y)) := by
  simp_rw [isGLB_iff_le_iff, mem_lowerBounds, forall_mem_image, le_map_iff hf]
  refine fun c ↦ ⟨fun H k hk ↦ H (y / k) (by simpa), fun H y' (hy' : f y' = f y) ↦ ?_⟩
  simpa using @H (y'⁻¹ * y) (by simp [hy'])

@[to_additive]
theorem gc_comp_map (hf : Surjective f) :
    GaloisConnection (fun q : GroupSeminorm F ↦ q.comp f) (fun p : GroupSeminorm E ↦ p.map f) := by
  intro p q
  simp_rw [GroupSeminorm.le_def, Pi.le_def, le_map_iff hf]
  exact ⟨fun H x y hxy ↦ hxy ▸ H y, fun H y ↦ H (f y) y rfl⟩

@[to_additive]
lemma le_map_iff_comp_le (hf : Surjective f) : q ≤ p.map f ↔ q.comp f ≤ p :=
  gc_comp_map hf |>.le_iff_le.symm

variable (f) in
@[to_additive]
lemma map_mono (h : p ≤ p') : p.map f ≤ p'.map f := by
  by_cases hf : Surjective f
  · exact gc_comp_map hf |>.monotone_u h
  · intro x
    simp [p.map_def, p'.map_def, hf]

variable (f) in
@[to_additive]
lemma map_apply_le {y : E} : p.map f (f y) ≤ p y := by
  by_cases hf : Surjective f
  · exact gc_comp_map hf |>.l_u_le p y
  · simp [p.map_def, hf]

@[to_additive]
noncomputable def gci_comp_map (hf : Surjective f) :
    GaloisCoinsertion (fun q : GroupSeminorm F ↦ q.comp f) (fun p : GroupSeminorm E ↦ p.map f) :=
  gc_comp_map hf |>.toGaloisCoinsertion fun p x ↦ by
    obtain ⟨y, hxy⟩ := hf x
    exact isGLB_map hf x |>.1 ⟨y, hxy, by simp [hxy]⟩

@[to_additive]
lemma map_comp_eq (hf : Surjective f) : (q.comp f).map f = q :=
  gci_comp_map hf |>.u_l_eq q

@[to_additive]
theorem map_map (hf : Surjective f) : (p.map f).map g = p.map (g.comp f) := by
  by_cases hg : Surjective g
  · exact (gc_comp_map hg).compose (gc_comp_map hf)
      |>.u_unique (gc_comp_map (f := g.comp f) (hg.comp hf)) (fun _ ↦ rfl)
  · have hg' : ¬Surjective (g ∘ f) := by rwa [hf.of_comp_iff]
    ext x
    simp [GroupSeminorm.map_def, hg, hg']

end map

section Quotient

variable {E : Type*} [Group E] {p p' : GroupSeminorm E} {S : Subgroup E} [S.Normal]
  {q : GroupSeminorm (E ⧸ S)}

variable (p S) in
@[to_additive]
protected noncomputable def quotient : GroupSeminorm (E ⧸ S) :=
  p.map (QuotientGroup.mk' S)

@[to_additive]
protected lemma quotient_def {x : E ⧸ S} :
    p.quotient S x = sInf (p '' {y : E | y = x}) := by
  simp [GroupSeminorm.quotient, p.map_def, QuotientGroup.mk_surjective]
  rfl

@[to_additive]
lemma isGLB_quotient (x : E ⧸ S) :
    IsGLB (p '' {y : E | y = x}) (p.quotient S x) :=
  p.isGLB_map (QuotientGroup.mk'_surjective S) x

@[to_additive]
lemma le_quotient_iff {x : E ⧸ S} {c : ℝ} :
    c ≤ p.quotient S x ↔ ∀ y : E, y = x → c ≤ p y :=
  p.le_map_iff (QuotientGroup.mk'_surjective S)

@[to_additive]
lemma quotient_lt_iff {x : E ⧸ S} {c : ℝ} :
    p.quotient S x < c ↔ ∃ y : E, y = x ∧ p y < c :=
  map_lt_iff (QuotientGroup.mk'_surjective S)

@[to_additive]
lemma quotient_eq_iff_le_iff {x : E ⧸ S} {c : ℝ} :
    p.quotient S x = c ↔ (∀ d, d ≤ c ↔ ∀ y : E, y = x → d ≤ p y) :=
  map_eq_iff_le_iff (QuotientGroup.mk'_surjective S)

variable (S) in
@[to_additive]
lemma isGLB_quotient_dist (y : E) :
    IsGLB ((fun k ↦ p (y / k)) '' S) (p.quotient S y) := by
  simpa using isGLB_map_dist_ker (QuotientGroup.mk'_surjective S) y

variable (S) in
@[to_additive]
theorem gc_comp_quotient :
    GaloisConnection
      (fun q : GroupSeminorm (E ⧸ S) ↦ q.comp (QuotientGroup.mk' S))
      (fun p : GroupSeminorm E ↦ p.quotient S) :=
  gc_comp_map (QuotientGroup.mk'_surjective S)

variable (S) in
@[to_additive]
lemma le_quotient_iff_comp_le : q ≤ p.quotient S ↔ q.comp (QuotientGroup.mk' S) ≤ p :=
  le_map_iff_comp_le (QuotientGroup.mk'_surjective S)

variable (S) in
@[to_additive]
lemma quotient_mono (h : p ≤ p') : p.quotient S ≤ p'.quotient S :=
  map_mono _ h

variable (S) in
@[to_additive]
lemma quotient_coe_le {y : E} : p.quotient S y ≤ p y :=
  map_apply_le _

variable (S) in
@[to_additive]
noncomputable def gci_comp_quotient :
    GaloisCoinsertion
      (fun q : GroupSeminorm (E ⧸ S) ↦ q.comp (QuotientGroup.mk' S))
      (fun p : GroupSeminorm E ↦ p.quotient S) :=
  gci_comp_map (QuotientGroup.mk'_surjective S)

@[to_additive]
lemma quotient_comp_eq : (q.comp (QuotientGroup.mk' S)).quotient S = q :=
  map_comp_eq (QuotientGroup.mk'_surjective S)

end Quotient

end GroupSeminorm

end
