/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Submodule

/-!
# Lie Ideals

This file defines Lie ideals, which are Lie submodules of a Lie algebra over itself.
They are defined as a special case of `LieSubmodule`, and inherit much of their structure from it.

We also prove some basic properties of Lie ideals, including how they behave under
Lie algebra homomorphisms (`map`, `comap`) and how they relate to the lattice structure
on Lie submodules.

## Main definitions

* `LieIdeal`
* `LieIdeal.map`
* `LieIdeal.comap`

## Tags

Lie algebra, ideal, submodule, Lie submodule
-/


universe u v w w₁ w₂

section LieSubmodule

variable (R : Type u) (L : Type v) (M : Type w)
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M]

section LieIdeal
variable [LieAlgebra R L] [LieModule R L M]

/-- An ideal of a Lie algebra is a Lie submodule of the Lie algebra as a Lie module over itself. -/
abbrev LieIdeal :=
  LieSubmodule R L L

theorem lie_mem_right (I : LieIdeal R L) (x y : L) (h : y ∈ I) : ⁅x, y⁆ ∈ I :=
  I.lie_mem h

theorem lie_mem_left (I : LieIdeal R L) (x y : L) (h : x ∈ I) : ⁅x, y⁆ ∈ I := by
  rw [← lie_skew, ← neg_lie]; apply lie_mem_right; assumption

/-- An ideal of a Lie algebra is a Lie subalgebra. -/
def LieIdeal.toLieSubalgebra (I : LieIdeal R L) : LieSubalgebra R L :=
  { I.toSubmodule with lie_mem' := by intro x y _ hy; apply lie_mem_right; exact hy }

@[deprecated (since := "2025-01-02")] alias lieIdealSubalgebra := LieIdeal.toLieSubalgebra

instance : Coe (LieIdeal R L) (LieSubalgebra R L) :=
  ⟨LieIdeal.toLieSubalgebra R L⟩

@[simp]
theorem LieIdeal.coe_toLieSubalgebra (I : LieIdeal R L) : ((I : LieSubalgebra R L) : Set L) = I :=
  rfl

@[deprecated (since := "2024-12-30")]
alias LieIdeal.coe_toSubalgebra := LieIdeal.coe_toLieSubalgebra

@[simp]
theorem LieIdeal.toLieSubalgebra_toSubmodule (I : LieIdeal R L) :
    ((I : LieSubalgebra R L) : Submodule R L) = LieSubmodule.toSubmodule I :=
  rfl

@[deprecated (since := "2025-01-02")]
alias LieIdeal.coe_toLieSubalgebra_toSubmodule := LieIdeal.toLieSubalgebra_toSubmodule

@[deprecated (since := "2024-12-30")]
alias LieIdeal.coe_to_lieSubalgebra_to_submodule := LieIdeal.toLieSubalgebra_toSubmodule

/-- An ideal of `L` is a Lie subalgebra of `L`, so it is a Lie ring. -/
instance LieIdeal.lieRing (I : LieIdeal R L) : LieRing I :=
  LieSubalgebra.lieRing R L ↑I

/-- Transfer the `LieAlgebra` instance from the coercion `LieIdeal → LieSubalgebra`. -/
instance LieIdeal.lieAlgebra (I : LieIdeal R L) : LieAlgebra R I :=
  LieSubalgebra.lieAlgebra R L ↑I

/-- Transfer the `LieRingModule` instance from the coercion `LieIdeal → LieSubalgebra`. -/
instance LieIdeal.lieRingModule {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) [LieRingModule L M] : LieRingModule I M :=
  LieSubalgebra.lieRingModule (I : LieSubalgebra R L)

@[simp]
theorem LieIdeal.coe_bracket_of_module {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) [LieRingModule L M] (x : I) (m : M) :
    ⁅x, m⁆ = ⁅(↑x : L), m⁆ :=
  LieSubalgebra.coe_bracket_of_module (I : LieSubalgebra R L) x m

/-- Transfer the `LieModule` instance from the coercion `LieIdeal → LieSubalgebra`. -/
instance LieIdeal.lieModule (I : LieIdeal R L) : LieModule R I M :=
  LieSubalgebra.lieModule (I : LieSubalgebra R L)

instance (I : LieIdeal R L) : IsLieTower I L M where
  leibniz_lie x y m := leibniz_lie x.val y m

instance (I : LieIdeal R L) : IsLieTower L I M where
  leibniz_lie x y m := leibniz_lie x y.val m

end LieIdeal

namespace LieSubalgebra

variable {L}
variable [LieAlgebra R L]
variable (K : LieSubalgebra R L)

theorem exists_lieIdeal_coe_eq_iff :
    (∃ I : LieIdeal R L, ↑I = K) ↔ ∀ x y : L, y ∈ K → ⁅x, y⁆ ∈ K := by
  simp only [← toSubmodule_inj, LieIdeal.toLieSubalgebra_toSubmodule,
    Submodule.exists_lieSubmodule_coe_eq_iff L, mem_toSubmodule]

theorem exists_nested_lieIdeal_coe_eq_iff {K' : LieSubalgebra R L} (h : K ≤ K') :
    (∃ I : LieIdeal R K', ↑I = ofLe h) ↔ ∀ x y : L, x ∈ K' → y ∈ K → ⁅x, y⁆ ∈ K := by
  simp only [exists_lieIdeal_coe_eq_iff, coe_bracket, mem_ofLe]
  constructor
  · intro h' x y hx hy; exact h' ⟨x, hx⟩ ⟨y, h hy⟩ hy
  · rintro h' ⟨x, hx⟩ ⟨y, hy⟩ hy'; exact h' x y hx hy'

end LieSubalgebra

end LieSubmodule

section LieSubmoduleMapAndComap

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}
variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']
variable [AddCommGroup M] [Module R M] [LieRingModule L M]
variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

namespace LieIdeal

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']
variable (f : L →ₗ⁅R⁆ L') (I I₂ : LieIdeal R L) (J : LieIdeal R L')

@[simp]
theorem top_toLieSubalgebra : ((⊤ : LieIdeal R L) : LieSubalgebra R L) = ⊤ :=
  rfl

@[deprecated (since := "2024-12-30")] alias top_coe_lieSubalgebra := top_toLieSubalgebra

/-- A morphism of Lie algebras `f : L → L'` pushes forward Lie ideals of `L` to Lie ideals of `L'`.

Note that unlike `LieSubmodule.map`, we must take the `lieSpan` of the image. Mathematically
this is because although `f` makes `L'` into a Lie module over `L`, in general the `L` submodules of
`L'` are not the same as the ideals of `L'`. -/
def map : LieIdeal R L' :=
  LieSubmodule.lieSpan R L' <| (I : Submodule R L).map (f : L →ₗ[R] L')

/-- A morphism of Lie algebras `f : L → L'` pulls back Lie ideals of `L'` to Lie ideals of `L`.

Note that `f` makes `L'` into a Lie module over `L` (turning `f` into a morphism of Lie modules)
and so this is a special case of `LieSubmodule.comap` but we do not exploit this fact. -/
def comap : LieIdeal R L :=
  { (J : Submodule R L').comap (f : L →ₗ[R] L') with
    lie_mem := fun {x y} h ↦ by
      suffices ⁅f x, f y⁆ ∈ J by
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          Submodule.mem_toAddSubmonoid, Submodule.mem_comap, LieHom.coe_toLinearMap, LieHom.map_lie,
          LieSubalgebra.mem_toSubmodule]
        exact this
      apply J.lie_mem h }

@[simp]
theorem map_toSubmodule (h : ↑(map f I) = f '' I) :
    LieSubmodule.toSubmodule (map f I) = (LieSubmodule.toSubmodule I).map (f : L →ₗ[R] L') := by
  rw [SetLike.ext'_iff, LieSubmodule.coe_toSubmodule, h, Submodule.map_coe]; rfl

@[deprecated (since := "2024-12-30")] alias map_coeSubmodule := map_toSubmodule

@[simp]
theorem comap_toSubmodule :
    (LieSubmodule.toSubmodule (comap f J)) = (LieSubmodule.toSubmodule J).comap (f : L →ₗ[R] L') :=
  rfl

@[deprecated (since := "2024-12-30")] alias comap_coeSubmodule := comap_toSubmodule

theorem map_le : map f I ≤ J ↔ f '' I ⊆ J :=
  LieSubmodule.lieSpan_le

variable {f I I₂ J}

theorem mem_map {x : L} (hx : x ∈ I) : f x ∈ map f I := by
  apply LieSubmodule.subset_lieSpan
  use x
  exact ⟨hx, rfl⟩

@[simp]
theorem mem_comap {x : L} : x ∈ comap f J ↔ f x ∈ J :=
  Iff.rfl

theorem map_le_iff_le_comap : map f I ≤ J ↔ I ≤ comap f J := by
  rw [map_le]
  exact Set.image_subset_iff

variable (f) in
theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ ↦ map_le_iff_le_comap

@[simp]
theorem map_sup : (I ⊔ I₂).map f = I.map f ⊔ I₂.map f :=
  (gc_map_comap f).l_sup

theorem map_comap_le : map f (comap f J) ≤ J := by rw [map_le_iff_le_comap]

/-- See also `LieIdeal.map_comap_eq`. -/
theorem comap_map_le : I ≤ comap f (map f I) := by rw [← map_le_iff_le_comap]

@[mono]
theorem map_mono : Monotone (map f) := fun I₁ I₂ h ↦ by
  rw [SetLike.le_def] at h
  apply LieSubmodule.lieSpan_mono (Set.image_subset (⇑f) h)

@[mono]
theorem comap_mono : Monotone (comap f) := fun J₁ J₂ h ↦ by
  rw [← SetLike.coe_subset_coe] at h ⊢
  dsimp only [SetLike.coe]
  exact Set.preimage_mono h

theorem map_of_image (h : f '' I = J) : I.map f = J := by
  apply le_antisymm
  · rw [map, LieSubmodule.lieSpan_le, Submodule.map_coe]
    /- I'm uncertain how to best resolve this `erw`.
    ```
    have : (↑(toLieSubalgebra R L I).toSubmodule : Set L) = I := rfl
    rw [this]
    simp [h]
    ```
    works, but still feels awkward. There are missing `simp` lemmas here.`
    -/
    erw [h]
  · rw [← SetLike.coe_subset_coe, ← h]; exact LieSubmodule.subset_lieSpan

/-- Note that this is not a special case of `LieSubmodule.subsingleton_of_bot`. Indeed, given
`I : LieIdeal R L`, in general the two lattices `LieIdeal R I` and `LieSubmodule R L I` are
different (though the latter does naturally inject into the former).

In other words, in general, ideals of `I`, regarded as a Lie algebra in its own right, are not the
same as ideals of `L` contained in `I`. -/
instance subsingleton_of_bot : Subsingleton (LieIdeal R (⊥ : LieIdeal R L)) := by
  apply subsingleton_of_bot_eq_top
  ext ⟨x, hx⟩
  rw [LieSubmodule.mem_bot] at hx
  subst hx
  simp only [LieSubmodule.mk_eq_zero, LieSubmodule.mem_bot, LieSubmodule.mem_top]

end LieIdeal

namespace LieHom
variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']
variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

/-- The kernel of a morphism of Lie algebras, as an ideal in the domain. -/
def ker : LieIdeal R L :=
  LieIdeal.comap f ⊥

/-- The range of a morphism of Lie algebras as an ideal in the codomain. -/
def idealRange : LieIdeal R L' :=
  LieSubmodule.lieSpan R L' f.range

theorem idealRange_eq_lieSpan_range : f.idealRange = LieSubmodule.lieSpan R L' f.range :=
  rfl

theorem idealRange_eq_map : f.idealRange = LieIdeal.map f ⊤ := by
  ext
  simp only [idealRange, range_eq_map]
  rfl

/-- The condition that the range of a morphism of Lie algebras is an ideal. -/
def IsIdealMorphism : Prop :=
  (f.idealRange : LieSubalgebra R L') = f.range

theorem isIdealMorphism_def : f.IsIdealMorphism ↔ (f.idealRange : LieSubalgebra R L') = f.range :=
  Iff.rfl

variable {f} in
theorem IsIdealMorphism.eq (hf : f.IsIdealMorphism) : f.idealRange = f.range := hf

theorem isIdealMorphism_iff : f.IsIdealMorphism ↔ ∀ (x : L') (y : L), ∃ z : L, ⁅x, f y⁆ = f z := by
  simp only [isIdealMorphism_def, idealRange_eq_lieSpan_range, ←
    LieSubalgebra.toSubmodule_inj, ← f.range.coe_toSubmodule,
    LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.coe_lieSpan_submodule_eq_iff,
    LieSubalgebra.mem_toSubmodule, mem_range, exists_imp,
    Submodule.exists_lieSubmodule_coe_eq_iff]
  constructor
  · intro h x y; obtain ⟨z, hz⟩ := h x (f y) y rfl; use z; exact hz.symm
  · intro h x y z hz; obtain ⟨w, hw⟩ := h x z; use w; rw [← hw, hz]

theorem range_subset_idealRange : (f.range : Set L') ⊆ f.idealRange :=
  LieSubmodule.subset_lieSpan

theorem map_le_idealRange : I.map f ≤ f.idealRange := by
  rw [f.idealRange_eq_map]
  exact LieIdeal.map_mono le_top

theorem ker_le_comap : f.ker ≤ J.comap f :=
  LieIdeal.comap_mono bot_le

@[simp]
theorem ker_toSubmodule : LieSubmodule.toSubmodule (ker f) = LinearMap.ker (f : L →ₗ[R] L') :=
  rfl

@[deprecated (since := "2024-12-30")] alias ker_coeSubmodule := ker_toSubmodule

variable {f} in
@[simp]
theorem mem_ker {x : L} : x ∈ ker f ↔ f x = 0 :=
  show x ∈ LieSubmodule.toSubmodule (f.ker) ↔ _ by
    simp only [ker_toSubmodule, LinearMap.mem_ker, coe_toLinearMap]

theorem mem_idealRange (x : L) : f x ∈ idealRange f := by
  rw [idealRange_eq_map]
  exact LieIdeal.mem_map (LieSubmodule.mem_top x)

@[simp]
theorem mem_idealRange_iff (h : IsIdealMorphism f) {y : L'} :
    y ∈ idealRange f ↔ ∃ x : L, f x = y := by
  rw [f.isIdealMorphism_def] at h
  rw [← LieSubmodule.mem_coe, ← LieIdeal.coe_toLieSubalgebra, h, f.range_coe, Set.mem_range]

theorem le_ker_iff : I ≤ f.ker ↔ ∀ x, x ∈ I → f x = 0 := by
  constructor <;> intro h x hx
  · specialize h hx; rw [mem_ker] at h; exact h
  · rw [mem_ker]; apply h x hx

theorem ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f := by
  rw [← LieSubmodule.toSubmodule_inj, ker_toSubmodule, LieSubmodule.bot_toSubmodule,
    LinearMap.ker_eq_bot, coe_toLinearMap]

@[simp]
theorem range_toSubmodule : (f.range : Submodule R L') = LinearMap.range (f : L →ₗ[R] L') :=
  rfl

@[deprecated (since := "2024-12-30")] alias range_coeSubmodule := range_toSubmodule

theorem range_eq_top : f.range = ⊤ ↔ Function.Surjective f := by
  rw [← LieSubalgebra.toSubmodule_inj, range_toSubmodule, LieSubalgebra.top_toSubmodule]
  exact LinearMap.range_eq_top

@[simp]
theorem idealRange_eq_top_of_surjective (h : Function.Surjective f) : f.idealRange = ⊤ := by
  rw [← f.range_eq_top] at h
  rw [idealRange_eq_lieSpan_range, h, ← LieSubalgebra.coe_toSubmodule, ←
    LieSubmodule.toSubmodule_inj, LieSubmodule.top_toSubmodule,
    LieSubalgebra.top_toSubmodule, LieSubmodule.coe_lieSpan_submodule_eq_iff]
  use ⊤
  exact LieSubmodule.top_toSubmodule

theorem isIdealMorphism_of_surjective (h : Function.Surjective f) : f.IsIdealMorphism := by
  rw [isIdealMorphism_def, f.idealRange_eq_top_of_surjective h, f.range_eq_top.mpr h,
    LieIdeal.top_toLieSubalgebra]

end LieHom

namespace LieIdeal
variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']
variable {f : L →ₗ⁅R⁆ L'} {I : LieIdeal R L} {J : LieIdeal R L'}

@[simp]
theorem map_eq_bot_iff : I.map f = ⊥ ↔ I ≤ f.ker := by
  rw [← le_bot_iff]
  exact LieIdeal.map_le_iff_le_comap

theorem coe_map_of_surjective (h : Function.Surjective f) :
    LieSubmodule.toSubmodule (I.map f) = (LieSubmodule.toSubmodule I).map (f : L →ₗ[R] L') := by
  let J : LieIdeal R L' :=
    { (I : Submodule R L).map (f : L →ₗ[R] L') with
      lie_mem := fun {x y} hy ↦ by
        have hy' : ∃ x : L, x ∈ I ∧ f x = y := by simpa [hy]
        obtain ⟨z₂, hz₂, rfl⟩ := hy'
        obtain ⟨z₁, rfl⟩ := h x
        simp only [LieHom.coe_toLinearMap, SetLike.mem_coe, Set.mem_image,
          LieSubmodule.mem_toSubmodule, Submodule.mem_carrier, Submodule.map_coe]
        use ⁅z₁, z₂⁆
        exact ⟨I.lie_mem hz₂, f.map_lie z₁ z₂⟩ }
  rw [map, toLieSubalgebra_toSubmodule, LieSubmodule.coe_lieSpan_submodule_eq_iff]
  exact ⟨J, rfl⟩

theorem mem_map_of_surjective {y : L'} (h₁ : Function.Surjective f) (h₂ : y ∈ I.map f) :
    ∃ x : I, f x = y := by
  rw [← LieSubmodule.mem_toSubmodule, coe_map_of_surjective h₁, Submodule.mem_map] at h₂
  obtain ⟨x, hx, rfl⟩ := h₂
  use ⟨x, hx⟩
  rw [LieHom.coe_toLinearMap]

theorem bot_of_map_eq_bot {I : LieIdeal R L} (h₁ : Function.Injective f) (h₂ : I.map f = ⊥) :
    I = ⊥ := by
  rw [← f.ker_eq_bot, LieHom.ker] at h₁
  rw [eq_bot_iff, map_le_iff_le_comap, h₁] at h₂
  rw [eq_bot_iff]; exact h₂

/-- Given two nested Lie ideals `I₁ ⊆ I₂`, the inclusion `I₁ ↪ I₂` is a morphism of Lie algebras. -/
def inclusion {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) : I₁ →ₗ⁅R⁆ I₂ where
  __ := Submodule.inclusion (show I₁.toSubmodule ≤ I₂.toSubmodule from h)
  map_lie' := rfl

@[simp]
theorem coe_inclusion {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) (x : I₁) : (inclusion h x : L) = x :=
  rfl

theorem inclusion_apply {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) (x : I₁) :
    inclusion h x = ⟨x.1, h x.2⟩ :=
  rfl

theorem inclusion_injective {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) :
    Function.Injective (inclusion h) :=
  fun x y ↦ by
  simp only [inclusion_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]

theorem map_sup_ker_eq_map : LieIdeal.map f (I ⊔ f.ker) = LieIdeal.map f I := by
  suffices LieIdeal.map f (I ⊔ f.ker) ≤ LieIdeal.map f I by
    exact le_antisymm this (LieIdeal.map_mono le_sup_left)
  apply LieSubmodule.lieSpan_mono
  rintro x ⟨y, hy₁, hy₂⟩
  rw [← hy₂]
  erw [LieSubmodule.mem_sup] at hy₁
  obtain ⟨z₁, hz₁, z₂, hz₂, hy⟩ := hy₁
  rw [← hy]
  rw [f.coe_toLinearMap, f.map_add, LieHom.mem_ker.mp hz₂, add_zero]; exact ⟨z₁, hz₁, rfl⟩

@[simp]
theorem map_sup_ker_eq_map' :
    LieIdeal.map f I ⊔ LieIdeal.map f (LieHom.ker f) = LieIdeal.map f I := by
  simpa using map_sup_ker_eq_map (f := f)

@[simp]
theorem map_comap_eq (h : f.IsIdealMorphism) : map f (comap f J) = f.idealRange ⊓ J := by
  apply le_antisymm
  · rw [le_inf_iff]; exact ⟨f.map_le_idealRange _, map_comap_le⟩
  · rw [f.isIdealMorphism_def] at h
    rw [← SetLike.coe_subset_coe, LieSubmodule.inf_coe, ← coe_toLieSubalgebra, h]
    rintro y ⟨⟨x, h₁⟩, h₂⟩; rw [← h₁] at h₂ ⊢; exact mem_map h₂

@[simp]
theorem comap_map_eq (h : ↑(map f I) = f '' I) : comap f (map f I) = I ⊔ f.ker := by
  rw [← LieSubmodule.toSubmodule_inj, comap_toSubmodule, I.map_toSubmodule f h,
    LieSubmodule.sup_toSubmodule, f.ker_toSubmodule, Submodule.comap_map_eq]

variable (f I J)

/-- Regarding an ideal `I` as a subalgebra, the inclusion map into its ambient space is a morphism
of Lie algebras. -/
def incl : I →ₗ⁅R⁆ L :=
  (I : LieSubalgebra R L).incl

@[simp]
theorem incl_range : I.incl.range = I :=
  (I : LieSubalgebra R L).incl_range

@[simp]
theorem incl_apply (x : I) : I.incl x = x :=
  rfl

@[simp]
theorem incl_coe : (I.incl.toLinearMap : I →ₗ[R] L) = (I : Submodule R L).subtype :=
  rfl

lemma incl_injective (I : LieIdeal R L) : Function.Injective I.incl :=
  Subtype.val_injective

@[simp]
theorem comap_incl_self : comap I.incl I = ⊤ := by ext; simp

@[simp]
theorem ker_incl : I.incl.ker = ⊥ := by ext; simp

@[simp]
theorem incl_idealRange : I.incl.idealRange = I := by
  rw [LieHom.idealRange_eq_lieSpan_range, ← LieSubalgebra.coe_toSubmodule, ←
    LieSubmodule.toSubmodule_inj, incl_range, toLieSubalgebra_toSubmodule,
    LieSubmodule.coe_lieSpan_submodule_eq_iff]
  use I

theorem incl_isIdealMorphism : I.incl.IsIdealMorphism := by
  rw [I.incl.isIdealMorphism_def, incl_idealRange]
  exact (I : LieSubalgebra R L).incl_range.symm

end LieIdeal

end LieSubmoduleMapAndComap

section TopEquiv

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L]
variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M]
variable {R L}
variable [LieAlgebra R L] [LieModule R L M]

/-- The natural equivalence between the 'top' Lie ideal and the enclosing Lie algebra.
This is the Lie ideal version of `Submodule.topEquiv`. -/
def LieIdeal.topEquiv : (⊤ : LieIdeal R L) ≃ₗ⁅R⁆ L :=
  LieSubalgebra.topEquiv

theorem LieIdeal.topEquiv_apply (x : (⊤ : LieIdeal R L)) : LieIdeal.topEquiv x = x :=
  rfl

end TopEquiv
