/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module

public import Mathlib.Algebra.Category.LocExtCat.Cotangent
public import Mathlib.RingTheory.AdicCompletion.Noetherian

import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# The Base Category for Deformation Theory

This file introduces `BaseCat`, the base category used in formal deformation theory
(e.g., for Schlessinger's criteria and Artin's axioms). It is defined as the full subcategory
of `LocExtCat Λ k` consisting of Artinian local algebras.

## Main Results

* `BaseCat`: The full subcategory of `LocExtCat Λ k` consisting of objects
  whose underlying rings are artinian.

* `BaseCat.IsSmallExtension`: The typeclass representing a small extension.
  A morphism `f : A ⟶ B` is a small extension if it is surjective and its kernel is a principal
  ideal annihilated by the maximal ideal of `A`.

* `BaseCat.induction_on_isSmallExtension`: Any surjective morphism in `BaseCat` can
  be factored into a finite composition of small extensions.

-/

@[expose] public section

universe v u

noncomputable section

open IsLocalRing CategoryTheory Function Algebra

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The base category for deformation theory over `Λ`. This is the full subcategory of
`LocExtCat Λ k` consisting of Artinian local `Λ`-algebras with residue field `k`. -/
@[stacks 06GC]
abbrev BaseCat (Λ : Type u) [CommRing Λ] (k : Type u) [Field k] [Algebra Λ k] : Type _ :=
  ObjectProperty.FullSubcategory fun A : LocExtCat Λ k ↦ IsArtinianRing A

namespace BaseCat

instance (A : BaseCat Λ k) : IsArtinianRing A.obj := A.property

instance coeExtension : CoeOut (BaseCat Λ k) (Extension.{u} Λ k) := ⟨fun A ↦ A.obj.toExtension⟩

instance coeRing : CoeSort (BaseCat Λ k) (Type u) := ⟨fun A ↦ A.obj.Ring⟩

variable {A B C : BaseCat Λ k} {f : A ⟶ B}

variable (Λ k) in
/-- Lift an unbundled extension whose underlying ring is local and Artinian
to an object in `BaseCat Λ k`. -/
abbrev of (X : Extension.{u} Λ k) [IsLocalRing X.Ring] [IsArtinianRing X.Ring] :
    BaseCat Λ k := ⟨.of Λ k X, inferInstance⟩

lemma coe_of (X : Extension.{u} Λ k) [IsLocalRing X.Ring] [IsArtinianRing X.Ring] :
    (of Λ k X : Type u) = X.Ring := rfl

/-- The object in `BaseCat` obtained from the quotient by a proper ideal. -/
def ofQuot (A : BaseCat Λ k) (I : Ideal A) [Nontrivial (A ⧸ I)] : BaseCat Λ k :=
  ⟨A.obj.ofQuot I, Ideal.Quotient.mk_surjective.isArtinianRing⟩

/-- Upgrades the canonical quotient map `A → A ⧸ I` to a morphism in `BaseCat`. -/
abbrev toOfQuot (A : BaseCat Λ k) (I : Ideal A) [Nontrivial (A ⧸ I)] :
    A ⟶ A.ofQuot I := ObjectProperty.homMk (A.obj.toOfQuot I)

/-- The morphism between quotient objects in `BaseCat` induced by a morphism `f : A ⟶ B`.
This is the categorical counterpart to `Ideal.quotientMapₐ` in the Artinian setting. -/
abbrev mapOfQuot (f : A ⟶ B) {I : Ideal A} {J : Ideal B} [Nontrivial (A ⧸ I)]
    [Nontrivial (B ⧸ J)] (hf : I ≤ J.comap f.hom.toAlgHom) : A.ofQuot I ⟶ B.ofQuot J :=
  ObjectProperty.homMk <| LocExtCat.mapOfQuot f.hom hf

lemma toOfQuot_comp_mapOfQuot (f : A ⟶ B) {I : Ideal A} {J : Ideal B}
    [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)] (hf : I ≤ J.comap f.hom.toAlgHom) :
    A.toOfQuot I ≫ mapOfQuot f hf = f ≫ B.toOfQuot J := rfl

/-- The quotient of a local Artinian algebra by the `n`-th power of its maximal ideal,
viewed as an object in `BaseCat`. -/
abbrev infinitesimal (n : ℕ) [NeZero n] (A : BaseCat Λ k) : BaseCat Λ k :=
  A.ofQuot (maximalIdeal A ^ n)

/-- The canonical quotient morphism from `A` to its infinitesimal neighborhood in `BaseCat`. -/
abbrev toInfinitesimal (n : ℕ) [NeZero n] (A : BaseCat Λ k) :
    A ⟶ A.infinitesimal n := toOfQuot ..

/-- The morphism between infinitesimal neighborhoods induced by a morphism in `BaseCat`. -/
abbrev mapInfinitesimal (m n : ℕ) [NeZero m] [NeZero n] (hmn : n ≤ m) (f : A ⟶ B) :
    A.infinitesimal m ⟶ B.infinitesimal n :=
  ObjectProperty.homMk (LocExtCat.mapInfinitesimal m n hmn f.hom)

/-- The special fiber of `A` over `Λ` when `Λ` is a local ring, defined as the quotient by
the extended maximal ideal of `Λ`, viewed as an object in `BaseCat`. -/
abbrev specialFiber [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (A : BaseCat Λ k) :
    BaseCat Λ k :=
  ⟨A.obj.specialFiber, Ideal.Quotient.mk_surjective.isArtinianRing⟩

/-- The canonical morphism from `A` to its special fiber in `BaseCat`. -/
abbrev toSpecialFiber [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (A : BaseCat Λ k) :
    A ⟶ A.specialFiber :=
  ObjectProperty.homMk A.obj.toSpecialFiber

/-- The morphism between special fibers induced by a morphism in `BaseCat`. -/
abbrev mapSpecialFiber [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (f : A ⟶ B) :
    A.specialFiber ⟶ B.specialFiber :=
  ObjectProperty.homMk (LocExtCat.mapSpecialFiber f.hom)

/-- A morphism `f : A ⟶ B` in `BaseCat` is a small extension if it is a surjective map
whose kernel is a principal ideal annihilated by the maximal ideal of `A`. -/
@[stacks 06GD]
class IsSmallExtension (f : A ⟶ B) : Prop where
  private mk ::
  surjective (f) : Function.Surjective f.hom.toAlgHom
  isPrincipal_ker (f) : (RingHom.ker f.hom.toAlgHom).IsPrincipal
  le_annihilator_ker (f) : maximalIdeal A ≤ (RingHom.ker f.hom.toAlgHom).annihilator

variable (f) in
theorem isSmallExtenstion_iff : IsSmallExtension f ↔ Surjective f.hom.toAlgHom ∧
    ∃ x : A, Ideal.span {x} = RingHom.ker f.hom.toAlgHom ∧ ∀ y ∈ maximalIdeal A, x * y = 0 := by
  refine ⟨fun ⟨_, ⟨x, hx⟩, h⟩ ↦ ⟨IsSmallExtension.surjective f, x, ?_, fun y y_in ↦ ?_⟩,
    fun ⟨h, x, x_span, hx⟩ ↦ ⟨h, ⟨x, ?_⟩, ?_⟩⟩
  · simp [hx]
  · rw [mul_comm, ← smul_eq_mul, ← Submodule.mem_annihilator_span_singleton, ← hx]
    exact h y_in
  · simp [← x_span]
  · intro y y_in
    rw [← x_span, Ideal.span, Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_comm]
    exact hx y y_in

theorem isSmallExtension_of_bijective (h : Bijective f.hom.toAlgHom) : IsSmallExtension f :=
  (isSmallExtenstion_iff f).mpr ⟨h.surjective, 0, by
    have := h.injective
    rw [RingHom.injective_iff_ker_eq_bot] at this
    simp [this]⟩

instance IsSmallExtension.hom_iso (e : A ≅ B) : IsSmallExtension e.hom :=
  isSmallExtension_of_bijective <| ConcreteCategory.bijective_of_isIso e.hom

theorem IsSmallExtension.toOfQuot_span_singleton (A : BaseCat Λ k) (x : A)
    [Nontrivial (A ⧸ (Ideal.span {x}))] (h : ∀ y ∈ maximalIdeal A, x * y = 0) :
    IsSmallExtension (A.toOfQuot (Ideal.span {x})) := by
  rw [isSmallExtenstion_iff]
  refine ⟨Ideal.Quotient.mk_surjective, x, ?_, h⟩
  change _ = RingHom.ker (A.obj.toOfQuot (Ideal.span {x})).toAlgHom
  rw [LocExtCat.ker_toAlgHom_toOfQuot]

open Submodule in
@[elab_as_elim, stacks 06GE]
theorem induction_on_isSmallExtension (hf : Surjective f.hom.toAlgHom)
    {P : ∀ {A B : BaseCat Λ k} (f : A ⟶ B), Surjective f.hom.toAlgHom → Prop}
    (small_ext : ∀ {X Y : BaseCat Λ k} (f : X ⟶ Y) [IsSmallExtension f],
      P f (IsSmallExtension.surjective f))
    (comp : ∀ {A B C : BaseCat Λ k} (f : A ⟶ B) (g : B ⟶ C) [IsSmallExtension f]
      (hg : Surjective g.hom.toAlgHom), P g hg →
    P (f ≫ g) (hg.comp (IsSmallExtension.surjective f))) : P f hf := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = Module.length A A :=
    ENat.ne_top_iff_exists.mp Module.length_ne_top
  revert A; induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A f hf hlen
    have hn : n ≠ 0 := by
      intro hn; revert hlen
      rw [imp_false, hn, Nat.cast_zero, eq_comm, Module.length_eq_zero_iff,
        ← not_nontrivial_iff_subsingleton, not_not]
      infer_instance
    let I := RingHom.ker f.hom.toAlgHom
    by_cases hI : I = ⊥
    · rw [← RingHom.injective_iff_ker_eq_bot] at hI
      have : IsSmallExtension f := isSmallExtension_of_bijective ⟨hI, hf⟩
      exact small_ext f
    obtain ⟨x, hx, x_ne⟩ := (Submodule.ne_bot_iff _).mp (Ideal.annihilator_inf_ne_bot
      ((isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance) hI)
    have x_in : x ∈ I := (mem_inf.mp hx).right
    replace hx : ∀ y ∈ maximalIdeal A, x * y = 0 := mem_annihilator.mp (mem_inf.mp hx).left
    have : Nontrivial (A ⧸ Ideal.span {x}) := by
      rw [Ideal.Quotient.nontrivial_iff]
      refine Ideal.span_singleton_ne_top (le_maximalIdeal ?_ x_in)
      rw [Ideal.ne_top_iff_exists_maximal]
      exact ⟨maximalIdeal A, maximalIdeal.isMaximal A, le_maximalIdeal
        (RingHom.ker_ne_top f.hom.toAlgHom)⟩
    have : IsLocalRing (A ⧸ Ideal.span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    let C := A.ofQuot (Ideal.span {x})
    let g : A ⟶ C := A.toOfQuot (Ideal.span {x})
    have hg : IsSmallExtension g := IsSmallExtension.toOfQuot_span_singleton A x hx
    let f' : C ⟶ B := ObjectProperty.homMk (LocExtCat.liftToOfQuot (Ideal.span {x}) f.hom
      (by simpa [← RingHom.mem_ker, ← SetLike.le_def]))
    have g_comp : g ≫ f' = f := by ext1; simpa using LocExtCat.toOfQuot_comp_liftToOfQuot ..
    obtain ⟨m, hm⟩ : ∃ n : ℕ, n = Module.length C C :=
      ENat.ne_top_iff_exists.mp Module.length_ne_top
    suffices h : m < n by
      simp_rw [← g_comp]
      refine comp g f' ?_ (ih m h _ hm)
      exact Ideal.Quotient.lift_surjective_of_surjective (Ideal.span {x}) (by
        simpa [← RingHom.mem_ker, ← SetLike.le_def]) hf
    have := Submodule.length_le_length_restrictScalars (R := (A ⧸ Ideal.span {x}))
      (M := (A ⧸ Ideal.span {x})) A ⊤
    rw [Module.length_top, restrictScalars_top, Module.length_top] at this
    rw [← ENat.coe_lt_coe, hlen, hm]
    exact this.trans_lt (length_quotient_lt (Ideal.span {x}) (by simpa))

/-- A morphism `f : A ⟶ B` in the base category is called minimally surjective if its
underlying algebra homomorphism is surjective, and it satisfies the following minimality
condition: for any object `C` and morphism `g : C ⟶ A` in `BaseCat`, if the composition
`g ≫ f` is surjective, then `g` itself must be surjective. -/
@[stacks 06GF, mk_iff]
class IsMinimallySurjective (f : A ⟶ B) : Prop where
  surjective (f) : Surjective f.hom.toAlgHom
  surjective_of_comp_left (f) {C : BaseCat Λ k} (g : C ⟶ A) :
    Surjective (g ≫ f).hom.toAlgHom → Surjective g.hom.toAlgHom

instance IsMinimallySurjective.hom_iso (e : A ≅ B) : IsMinimallySurjective e.hom := by
  refine ⟨(ConcreteCategory.bijective_of_isIso e.hom).surjective, fun {C} g hg ↦ ?_⟩
  rw [ObjectProperty.FullSubcategory.comp_hom, LocExtCat.toAlgHom_comp, AlgHom.coe_comp] at hg
  exact Surjective.of_comp_left hg (ConcreteCategory.bijective_of_isIso e.hom).injective

instance IsMinimallySurjective.comp (f : A ⟶ B) (g : B ⟶ C) [IsMinimallySurjective f]
    [IsMinimallySurjective g] : IsMinimallySurjective (f ≫ g) :=
  ⟨by simpa using .comp (IsMinimallySurjective.surjective g) (IsMinimallySurjective.surjective f),
  fun _ h ↦ IsMinimallySurjective.surjective_of_comp_left f _
    (IsMinimallySurjective.surjective_of_comp_left g _ h)⟩

theorem isMinimallySurjective_toOfQuot_of_le {I : Ideal A} [Nontrivial (A ⧸ I)]
    (h : I ≤ maximalIdeal A ^ 2) : IsMinimallySurjective (A.toOfQuot I) := by
  rw [← LocExtCat.bijective_mapCotangent_toOfQuot_iff] at h
  refine ⟨Ideal.Quotient.mk_surjective, fun {C} g hg ↦ ?_⟩
  apply LocExtCat.surjective_of_surjective_mapCotangent
  apply Surjective.of_comp_left (f := LocExtCat.mapCotangent (A.obj.toOfQuot I))
  · rw [← LinearMap.coe_comp, ← LocExtCat.mapCotangent_comp]
    exact LocExtCat.surjective_mapCotangent_of_surjective hg
  · exact h.injective

section IsLocalRing

variable [IsLocalRing Λ] [Module.Finite Λ k]

/-- Given morphisms `f : A ⟶ C` and `g : B ⟶ C` in `BaseCat` where `g.hom.toAlgHom` is surjective,
`ofPullback` is the object in `BaseCat` obtained from the pullback of the underlying
algebra homomorphisms`. -/
@[stacks 06GH "(1)"]
def ofPullback (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) : BaseCat Λ k :=
  ⟨.ofPullback f.hom g.hom hg, LocExtCat.isArtinianRing_ofPullback ..⟩

/-- Upgrades the first projection map from the pullback algebra to a morphism in `BaseCat`. -/
abbrev pullbackFst (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) :
    ofPullback f g hg ⟶ A := ObjectProperty.homMk (LocExtCat.pullbackFst f.hom g.hom hg)

/-- Upgrades the second projection map from the pullback algebra to a morphism in `BaseCat`. -/
abbrev pullbackSnd (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) :
    ofPullback f g hg ⟶ B := ObjectProperty.homMk (LocExtCat.pullbackSnd f.hom g.hom hg)

lemma pullback_comm_sq (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) :
    pullbackFst f g hg ≫ f = pullbackSnd f g hg ≫ g := by
  ext1; simpa using LocExtCat.pullback_comm_sq f.hom g.hom hg

@[stacks 06GH "(2)"]
instance pullbackFst_isSmallExtension (f : A ⟶ C) (g : B ⟶ C) [IsSmallExtension g] :
    IsSmallExtension (pullbackFst f g (IsSmallExtension.surjective g)) := by
  have : IsLocalRing ↥(f.hom.toAlgHom.pullback g.hom.toAlgHom) :=
    RingHom.isLocalRing_pullback f.hom.toAlgHom.toRingHom g.hom.toAlgHom.toRingHom
      ⟨(IsSmallExtension.surjective g).isLocalHom.map_nonunit⟩
  obtain ⟨x, x_span, hx⟩ := ((isSmallExtenstion_iff g).mp ‹_›).right
  have g_apply : g.hom.toAlgHom x = 0 := by
    rw [← RingHom.mem_ker, ← x_span]
    exact Ideal.mem_span_singleton_self x
  rw [isSmallExtenstion_iff]
  refine ⟨(f.hom.toAlgHom.surjective_pullbackFst_of_surjective g.hom.toAlgHom
    (IsSmallExtension.surjective g)), ?_⟩
  change ∃ x : f.hom.toAlgHom.pullback g.hom.toAlgHom, Ideal.span {x} =
    RingHom.ker (AlgHom.pullbackFst ..) ∧
      ∀ y ∈ maximalIdeal (f.hom.toAlgHom.pullback g.hom.toAlgHom), x * y = 0
  refine ⟨⟨(0, x), by simpa using g_apply.symm⟩, ?_, fun ⟨⟨a, b⟩, hab⟩ h ↦ ?_⟩
  · ext ⟨⟨u, v⟩, h⟩
    suffices (∃ a b, f.hom.toAlgHom a = g.hom.toAlgHom b ∧ 0 = u ∧ b * x = v) ↔ u = 0 by
      simpa [Ideal.mem_span_singleton']
    simp_rw [and_left_comm, eq_comm, exists_and_left, and_iff_left_iff_imp]
    intro u_eq
    replace h : 0 = g.hom.toAlgHom v := by simpa [u_eq] using h
    rw [eq_comm, ← RingHom.mem_ker, ← x_span, Ideal.mem_span_singleton'] at h
    rcases h with ⟨w, hw⟩
    obtain ⟨z, m, m_in, hm⟩ := LocExtCat.exists_mem_maximalIdeal_toAlgHom_apply_add_eq
      g.hom f.hom w (IsSmallExtension.surjective g)
    exact ⟨z, w + m, hm.symm, by rw [add_mul, hw, mul_comm, hx m m_in, add_zero]⟩
  · suffices x * b = 0 by simpa [← Subtype.val_inj]
    simp only [mem_maximalIdeal, mem_nonunits_iff, AlgHom.isUnit_pullback_mk_iff, not_and] at h
    simp only [AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply, AlgHom.fst_apply,
      AlgHom.snd_apply] at hab
    apply hx; intro hb; revert h
    simpa [hb] using f.hom.isLocalHom_toAlgHom.map_nonunit a (hab ▸ IsUnit.map g.hom.toAlgHom hb)

open ObjectProperty.FullSubcategory in
@[stacks 06S5]
theorem isMinimallySurjective_iff_isMinimallySurjective_mapOfQuot (f : A ⟶ B) {I : Ideal A}
    {J : Ideal B} [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)] (hI : I ≤ maximalIdeal A ^ 2)
    (hJ : J ≤ maximalIdeal B ^ 2) (hf : I ≤ J.comap f.hom.toAlgHom) :
    IsMinimallySurjective f ↔ IsMinimallySurjective (mapOfQuot f hf) := by
  refine ⟨fun h ↦ ⟨?_, fun {C} g hg ↦ ?_⟩, fun h ↦ ⟨?_, fun {C} g hg ↦ ?_⟩⟩
  · apply Surjective.of_comp (g := (A.toOfQuot I).hom.toAlgHom)
    rw [← AlgHom.coe_comp, ← LocExtCat.toAlgHom_comp, ← comp_hom, toOfQuot_comp_mapOfQuot]
    simpa using Surjective.comp (B.obj.surjective_toAlgHom_toOfQuot (I := J)) h.surjective
  · let C' := ofPullback g (A.toOfQuot I) Ideal.Quotient.mk_surjective
    let p : C' ⟶ C := pullbackFst g (A.toOfQuot I) Ideal.Quotient.mk_surjective
    apply Surjective.of_comp (g := p.hom.toAlgHom)
    rw [← AlgHom.coe_comp, ← LocExtCat.toAlgHom_comp, ← comp_hom, pullback_comm_sq, comp_hom,
      LocExtCat.toAlgHom_comp, AlgHom.coe_comp]
    refine Surjective.comp Ideal.Quotient.mk_surjective ?_
    apply isMinimallySurjective_toOfQuot_of_le at hJ
    apply IsMinimallySurjective.surjective_of_comp_left (f ≫ B.toOfQuot J)
    rw [← toOfQuot_comp_mapOfQuot (I := I) f hf, Category.assoc', ← pullback_comm_sq,
      Category.assoc, comp_hom, LocExtCat.toAlgHom_comp, AlgHom.coe_comp]
    exact hg.comp (LocExtCat.surjective_pullbackFst _ _ (fun _ ↦ Ideal.Quotient.mk_surjective _))
  · apply LocExtCat.surjective_of_surjective_mapCotangent
    apply Surjective.of_comp_left (f := LocExtCat.mapCotangent (B.toOfQuot J).hom)
    · rw [← LinearMap.coe_comp, ← LocExtCat.mapCotangent_comp, ← comp_hom,
        ← toOfQuot_comp_mapOfQuot (I := I) f hf, comp_hom, LocExtCat.mapCotangent_comp,
        LinearMap.coe_comp]
      exact Surjective.comp (LocExtCat.surjective_mapCotangent_of_surjective h.surjective)
        (LocExtCat.surjective_mapCotangent_of_surjective Ideal.Quotient.mk_surjective)
    · exact ((LocExtCat.bijective_mapCotangent_toOfQuot_iff J).mpr hJ).injective
  · apply isMinimallySurjective_toOfQuot_of_le at hI
    apply IsMinimallySurjective.surjective_of_comp_left (A.toOfQuot I ≫ (mapOfQuot f hf))
    rw [toOfQuot_comp_mapOfQuot, Category.assoc', comp_hom, LocExtCat.toAlgHom_comp,
      AlgHom.coe_comp]
    exact Ideal.Quotient.mk_surjective.comp hg

end IsLocalRing

end BaseCat
