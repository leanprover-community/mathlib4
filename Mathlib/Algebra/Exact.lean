/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient

/-! # Exactness of a pair

* For two maps `f : M → N` and `g : N → P`, with `Zero P`,
`Function.Exact f g` says that `Set.range f = Set.preimage g {0}`

* For additive maps `f : M →+ N`  and `g : N →+ P`,
`Exact f g` says that `range f = ker g`

* For linear maps `f : M →ₗ[R] N`  and `g : N →ₗ[R] P`,
`Exact f g` says that `range f = ker g`

## TODO :

* generalize to `SemilinearMap`, even `SemilinearMapClass`

* add the multiplicative case (`Function.Exact` will become `Function.AddExact`?)
-/



variable {R M M' N N' P P' : Type*}

namespace Function

variable (f : M → N) (g : N → P) (g' : P → P')

/-- The maps `f` and `g` form an exact pair :
  `g y = 0` iff `y` belongs to the image of `f` -/
def Exact [Zero P] : Prop := ∀ y, g y = 0 ↔ y ∈ Set.range f

variable {f g}

namespace Exact

lemma apply_apply_eq_zero [Zero P] (h : Exact f g) (x : M) :
    g (f x) = 0 := (h _).mpr <| Set.mem_range_self _

lemma comp_eq_zero [Zero P] (h : Exact f g) : g.comp f = 0 :=
  funext h.apply_apply_eq_zero

lemma of_comp_of_mem_range [Zero P] (h1 : g ∘ f = 0)
    (h2 : ∀ x, g x = 0 → x ∈ Set.range f) : Exact f g :=
  fun y => Iff.intro (h2 y) <|
    Exists.rec ((forall_apply_eq_imp_iff (p := (g · = 0))).mpr (congrFun h1) y)

lemma comp_injective [Zero P] [Zero P'] (exact : Exact f g)
    (inj : Function.Injective g') (h0 : g' 0 = 0) :
    Exact f (g' ∘ g) := by
  intro x
  refine ⟨fun H => exact x |>.mp <| inj <| h0 ▸ H, ?_⟩
  intro H
  rw [Function.comp_apply, exact x |>.mpr H, h0]

lemma of_comp_eq_zero_of_ker_in_range [Zero P] (hc : g.comp f = 0)
    (hr : ∀ y, g y = 0 → y ∈ Set.range f) :
    Exact f g :=
  fun y ↦ ⟨hr y, fun ⟨x, hx⟩ ↦ hx ▸ congrFun hc x⟩

end Exact

end Function

section AddMonoidHom

variable [AddGroup M] [AddGroup N] [AddGroup P] {f : M →+ N} {g : N →+ P}

namespace AddMonoidHom

open Function

lemma exact_iff :
    Exact f g ↔ ker g = range f :=
  Iff.symm SetLike.ext_iff

lemma exact_of_comp_eq_zero_of_ker_le_range
    (h1 : g.comp f = 0) (h2 : ker g ≤ range f) : Exact f g :=
  Exact.of_comp_of_mem_range (congrArg DFunLike.coe h1) h2

lemma exact_of_comp_of_mem_range
    (h1 : g.comp f = 0) (h2 : ∀ x, g x = 0 → x ∈ range f) : Exact f g :=
  exact_of_comp_eq_zero_of_ker_le_range h1 h2

end AddMonoidHom

namespace Function.Exact

open AddMonoidHom

lemma addMonoidHom_ker_eq (hfg : Exact f g) :
    ker g = range f :=
  SetLike.ext hfg

lemma addMonoidHom_comp_eq_zero (h : Exact f g) : g.comp f = 0 :=
  DFunLike.coe_injective h.comp_eq_zero

section

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [AddCommMonoid X₁] [AddCommMonoid X₂] [AddCommMonoid X₃]
  [AddCommMonoid Y₁] [AddCommMonoid Y₂] [AddCommMonoid Y₃]
  (e₁ : X₁ ≃+ Y₁) (e₂ : X₂ ≃+ Y₂) (e₃ : X₃ ≃+ Y₃)
  {f₁₂ : X₁ →+ X₂} {f₂₃ : X₂ →+ X₃} {g₁₂ : Y₁ →+ Y₂} {g₂₃ : Y₂ →+ Y₃}

lemma of_ladder_addEquiv_of_exact (comm₁₂ : g₁₂.comp e₁ = AddMonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = AddMonoidHom.comp e₃ f₂₃) (H : Exact f₁₂ f₂₃) : Exact g₁₂ g₂₃ := by
  have h₁₂ := DFunLike.congr_fun comm₁₂
  have h₂₃ := DFunLike.congr_fun comm₂₃
  dsimp at h₁₂ h₂₃
  apply of_comp_eq_zero_of_ker_in_range
  · ext y₁
    obtain ⟨x₁, rfl⟩ := e₁.surjective y₁
    dsimp
    rw [h₁₂, h₂₃, H.apply_apply_eq_zero, map_zero]
  · intro y₂ hx₂
    obtain ⟨x₂, rfl⟩ := e₂.surjective y₂
    obtain ⟨x₁, rfl⟩ := (H x₂).1 (e₃.injective (by rw [← h₂₃, hx₂, map_zero]))
    exact ⟨e₁ x₁, by rw [h₁₂]⟩

lemma of_ladder_addEquiv_of_exact' (comm₁₂ : g₁₂.comp e₁ = AddMonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = AddMonoidHom.comp e₃ f₂₃) (H : Exact g₁₂ g₂₃) : Exact f₁₂ f₂₃ := by
  refine of_ladder_addEquiv_of_exact e₁.symm e₂.symm e₃.symm ?_ ?_ H
  · ext y₁
    obtain ⟨x₁, rfl⟩ := e₁.surjective y₁
    apply e₂.injective
    simpa using DFunLike.congr_fun comm₁₂.symm x₁
  · ext y₂
    obtain ⟨x₂, rfl⟩ := e₂.surjective y₂
    apply e₃.injective
    simpa using DFunLike.congr_fun comm₂₃.symm x₂

lemma iff_of_ladder_addEquiv (comm₁₂ : g₁₂.comp e₁ = AddMonoidHom.comp e₂ f₁₂)
    (comm₂₃ : g₂₃.comp e₂ = AddMonoidHom.comp e₃ f₂₃) : Exact g₁₂ g₂₃ ↔ Exact f₁₂ f₂₃ := by
  constructor
  · exact of_ladder_addEquiv_of_exact' e₁ e₂ e₃ comm₁₂ comm₂₃
  · exact of_ladder_addEquiv_of_exact e₁ e₂ e₃ comm₁₂ comm₂₃

end

end Function.Exact

end AddMonoidHom

section LinearMap

open Function

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

namespace LinearMap

lemma exact_iff :
    Exact f g ↔ LinearMap.ker g = LinearMap.range f :=
  Iff.symm SetLike.ext_iff

lemma exact_of_comp_eq_zero_of_ker_le_range
    (h1 : g ∘ₗ f = 0) (h2 : ker g ≤ range f) : Exact f g :=
  Exact.of_comp_of_mem_range (congrArg DFunLike.coe h1) h2

lemma exact_of_comp_of_mem_range
    (h1 : g ∘ₗ f = 0) (h2 : ∀ x, g x = 0 → x ∈ range f) : Exact f g :=
  exact_of_comp_eq_zero_of_ker_le_range h1 h2

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]

lemma exact_subtype_mkQ (Q : Submodule R N) :
    Exact (Submodule.subtype Q) (Submodule.mkQ Q) := by
  rw [exact_iff, Submodule.ker_mkQ, Submodule.range_subtype Q]

lemma exact_map_mkQ_range (f : M →ₗ[R] N) :
    Exact f (Submodule.mkQ (range f)) :=
  exact_iff.mpr <| Submodule.ker_mkQ _

lemma exact_subtype_ker_map (g : N →ₗ[R] P) :
    Exact (Submodule.subtype (ker g)) g :=
  exact_iff.mpr <| (Submodule.range_subtype _).symm

end LinearMap

variable (f g) in
lemma LinearEquiv.conj_exact_iff_exact (e : N ≃ₗ[R] N') :
    Function.Exact (e ∘ₗ f) (g ∘ₗ (e.symm : N' →ₗ[R] N)) ↔ Exact f g := by
  simp_rw [LinearMap.exact_iff, LinearMap.ker_comp, ← e.map_eq_comap, LinearMap.range_comp]
  exact (Submodule.map_injective_of_injective e.injective).eq_iff

namespace Function

open LinearMap

lemma Exact.linearMap_ker_eq (hfg : Exact f g) : ker g = range f :=
  SetLike.ext hfg

lemma Exact.linearMap_comp_eq_zero (h : Exact f g) : g.comp f = 0 :=
  DFunLike.coe_injective h.comp_eq_zero

lemma Surjective.comp_exact_iff_exact {p : M' →ₗ[R] M} (h : Surjective p) :
    Exact (f ∘ₗ p) g ↔ Exact f g :=
  iff_of_eq <| forall_congr fun x =>
    congrArg (g x = 0 ↔ x ∈ ·) (h.range_comp f)

lemma Injective.comp_exact_iff_exact {i : P →ₗ[R] P'} (h : Injective i) :
    Exact f (i ∘ₗ g) ↔ Exact f g :=
  forall_congr' fun _ => iff_congr (LinearMap.map_eq_zero_iff _ h) Iff.rfl

variable
    {f₁₂ : M →ₗ[R] N} {f₂₃ : N →ₗ[R] P} {g₁₂ : M' →ₗ[R] N'}
    {g₂₃ : N' →ₗ[R] P'} {e₁ : M ≃ₗ[R] M'} {e₂ : N ≃ₗ[R] N'} {e₃ : P ≃ₗ[R] P'}

lemma Exact.iff_of_ladder_linearEquiv
    (h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃) :
    Exact g₁₂ g₂₃ ↔ Exact f₁₂ f₂₃ :=
  iff_of_ladder_addEquiv e₁.toAddEquiv e₂.toAddEquiv e₃.toAddEquiv
    (f₁₂ := f₁₂) (f₂₃ := f₂₃) (g₁₂ := g₁₂) (g₂₃ := g₂₃)
    (congr_arg LinearMap.toAddMonoidHom h₁₂) (congr_arg LinearMap.toAddMonoidHom h₂₃)

lemma Exact.of_ladder_linearEquiv_of_exact
    (h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃)
    (H : Exact f₁₂ f₂₃) : Exact g₁₂ g₂₃ := by
  rwa [iff_of_ladder_linearEquiv h₁₂ h₂₃]

end Function

end LinearMap

namespace Function

section split

variable [Semiring R]
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

open LinearMap

/-- Given an exact sequence `0 → M → N → P`, giving a section `P → N` is equivalent to giving a
splitting `N ≃ M × P`. -/
noncomputable
def Exact.splitSurjectiveEquiv (h : Function.Exact f g) (hf : Function.Injective f) :
    { l // g ∘ₗ l = .id } ≃
      { e : N ≃ₗ[R] M × P // f = e.symm ∘ₗ inl R M P ∧ g = snd R M P ∘ₗ e } := by
  refine
  { toFun := fun l ↦ ⟨(LinearEquiv.ofBijective (f ∘ₗ fst R M P + l.1 ∘ₗ snd R M P) ?_).symm, ?_⟩
    invFun := fun e ↦ ⟨e.1.symm ∘ₗ inr R M P, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h₁ : ∀ x, g (l.1 x) = x := LinearMap.congr_fun l.2
    have h₂ : ∀ x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · intros x y e
      simp only [add_apply, coe_comp, comp_apply, fst_apply, snd_apply] at e
      suffices x.2 = y.2 from Prod.ext (hf (by rwa [this, add_left_inj] at e)) this
      simpa [h₁, h₂] using DFunLike.congr_arg g e
    · intro x
      obtain ⟨y, hy⟩ := (h (x - l.1 (g x))).mp (by simp [h₁, g.map_sub])
      exact ⟨⟨y, g x⟩, by simp [hy]⟩
  · have h₁ : ∀ x, g (l.1 x) = x := LinearMap.congr_fun l.2
    have h₂ : ∀ x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · ext; simp
    · rw [LinearEquiv.eq_comp_toLinearMap_symm]
      ext <;> simp [h₁, h₂]
  · rw [← LinearMap.comp_assoc, (LinearEquiv.eq_comp_toLinearMap_symm _ _).mp e.2.2]; rfl
  · intro; ext; simp
  · rintro ⟨e, rfl, rfl⟩
    ext1
    apply LinearEquiv.symm_bijective.injective
    ext
    apply e.injective
    ext <;> simp

/-- Given an exact sequence `M → N → P → 0`, giving a retraction `N → M` is equivalent to giving a
splitting `N ≃ M × P`. -/
noncomputable
def Exact.splitInjectiveEquiv
    {R M N P} [Semiring R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) (hg : Function.Surjective g) :
    { l // l ∘ₗ f = .id } ≃
      { e : N ≃ₗ[R] M × P // f = e.symm ∘ₗ inl R M P ∧ g = snd R M P ∘ₗ e } := by
  refine
  { toFun := fun l ↦ ⟨(LinearEquiv.ofBijective (l.1.prod g) ?_), ?_⟩
    invFun := fun e ↦ ⟨fst R M P ∘ₗ e.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h₁ : ∀ x, l.1 (f x) = x := LinearMap.congr_fun l.2
    have h₂ : ∀ x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · intros x y e
      simp only [prod_apply, Pi.prod, Prod.mk.injEq] at e
      obtain ⟨z, hz⟩ := (h (x - y)).mp (by simpa [sub_eq_zero] using e.2)
      suffices z = 0 by rw [← sub_eq_zero, ← hz, this, map_zero]
      rw [← h₁ z, hz, map_sub, e.1, sub_self]
    · rintro ⟨x, y⟩
      obtain ⟨y, rfl⟩ := hg y
      refine ⟨f x + y - f (l.1 y), by ext <;> simp [h₁, h₂]⟩
  · have h₁ : ∀ x, l.1 (f x) = x := LinearMap.congr_fun l.2
    have h₂ : ∀ x, g (f x) = 0 := congr_fun h.comp_eq_zero
    constructor
    · rw [LinearEquiv.eq_toLinearMap_symm_comp]
      ext <;> simp [h₁, h₂]
    · ext; simp
  · rw [LinearMap.comp_assoc, (LinearEquiv.eq_toLinearMap_symm_comp _ _).mp e.2.1]; rfl
  · intro; ext; simp
  · rintro ⟨e, rfl, rfl⟩
    ext x <;> simp

theorem Exact.split_tfae' (h : Function.Exact f g) :
    List.TFAE [
      Function.Injective f ∧ ∃ l, g ∘ₗ l = LinearMap.id,
      Function.Surjective g ∧ ∃ l, l ∘ₗ f = LinearMap.id,
      ∃ e : N ≃ₗ[R] M × P, f = e.symm ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ e] := by
  tfae_have 1 → 3
  | ⟨hf, l, hl⟩ => ⟨_, (h.splitSurjectiveEquiv hf ⟨l, hl⟩).2⟩
  tfae_have 2 → 3
  | ⟨hg, l, hl⟩ => ⟨_, (h.splitInjectiveEquiv hg ⟨l, hl⟩).2⟩
  tfae_have 3 → 1
  | ⟨e, e₁, e₂⟩ => by
    have : Function.Injective f := e₁ ▸ e.symm.injective.comp LinearMap.inl_injective
    exact ⟨this, ⟨_, ((h.splitSurjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
  tfae_have 3 → 2
  | ⟨e, e₁, e₂⟩ => by
    have : Function.Surjective g := e₂ ▸ Prod.snd_surjective.comp e.surjective
    exact ⟨this, ⟨_, ((h.splitInjectiveEquiv this).symm ⟨e, e₁, e₂⟩).2⟩⟩
  tfae_finish

/-- Equivalent characterizations of split exact sequences. Also known as the **Splitting lemma**. -/
theorem Exact.split_tfae
    {R M N P} [Semiring R] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    List.TFAE [
      ∃ l, g ∘ₗ l = LinearMap.id,
      ∃ l, l ∘ₗ f = LinearMap.id,
      ∃ e : N ≃ₗ[R] M × P, f = e.symm ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ e] := by
  tfae_have 1 ↔ 3 := by
    simpa using (h.splitSurjectiveEquiv hf).nonempty_congr
  tfae_have 2 ↔ 3 := by
    simpa using (h.splitInjectiveEquiv hg).nonempty_congr
  tfae_finish

end split

section Prod

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

lemma Exact.inr_fst : Function.Exact (LinearMap.inr R M N) (LinearMap.fst R M N) := by
  rintro ⟨x, y⟩
  simp only [LinearMap.fst_apply, @eq_comm _ x, LinearMap.coe_inr, Set.mem_range, Prod.mk.injEq,
    exists_eq_right]

lemma Exact.inl_snd : Function.Exact (LinearMap.inl R M N) (LinearMap.snd R M N) := by
  rintro ⟨x, y⟩
  simp only [LinearMap.snd_apply, @eq_comm _ y, LinearMap.coe_inl, Set.mem_range, Prod.mk.injEq,
    exists_eq_left]

end Prod

section Ring

open LinearMap Submodule

variable [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]

/-- A necessary and sufficient condition for an exact sequence to descend to a quotient. -/
lemma Exact.exact_mapQ_iff {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hfg : Exact f g) {p q r} (hpq : p ≤ comap f q) (hqr : q ≤ comap g r) :
    Exact (mapQ p q f hpq) (mapQ q r g hqr) ↔ range g ⊓ r ≤ map g q := by
  rw [exact_iff, ← (comap_injective_of_surjective (mkQ_surjective _)).eq_iff]
  dsimp only [mapQ]
  rw [← ker_comp, range_liftQ, liftQ_mkQ, ker_comp, range_comp, comap_map_eq,
    ker_mkQ, ker_mkQ, ← hfg.linearMap_ker_eq, sup_comm,
    ← LE.le.le_iff_eq (sup_le hqr (ker_le_comap g)),
    ← comap_map_eq, ← map_le_iff_le_comap, map_comap_eq]

end Ring

end Function
