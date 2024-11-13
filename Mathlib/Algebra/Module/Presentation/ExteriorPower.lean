/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Module.Presentation.PiTensor
import Mathlib.LinearAlgebra.ExteriorPower.Generators

/-!
# Presentation of the exterior power

Given a presentation of a `R`-module `M`, we obtain a presentation of `⋀[R]^n M`.

-/

universe w

namespace MultilinearMap

open Function

/-- Better constructor for `MultilinearMap` when the index type has a `DecidableEq` instance. -/
@[simps]
def mk' {R : Type*} {ι : Type*} [DecidableEq ι]
    {M₁ : ι → Type*} {M₂ : Type*} [Semiring R]
    [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)] [Module R M₂]
    (f : (∀ i, M₁ i) → M₂)
    (map_update_add : ∀ (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i),
      f (update m i (x + y)) = f (update m i x) + f (update m i y))
    (map_update_smul : ∀ (m : (i : ι) → M₁ i) (i : ι) (c : R) (x : M₁ i),
      f (update m i (c • x)) = c • f (update m i x)):
    MultilinearMap R M₁ M₂ where
  toFun := f
  map_update_add' m i x y := by convert map_update_add m i x y
  map_update_smul' m i c x := by convert map_update_smul m i c x

end MultilinearMap

namespace Function

section

variable {ι α : Type*} [DecidableEq ι]

lemma update_comp (f : ι → α) (i : ι) (x : α) {β : Type*} (g : α → β) :
    update (g ∘ f) i (g x) = g ∘ update f i x := by
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp only [update_noteq h, comp_apply]

lemma update_update (f : ι → α) (i j : ι) (a b : α) (hij : i ≠ j) :
    update (update f i a) j b = update (update f j b) i a := by
  ext x
  by_cases h : x = i
  · subst h
    rw [update_same, update_noteq hij, update_same]
  · by_cases h' : x = j
    · subst h'
      rw [update_same, update_noteq hij.symm, update_same]
    · rw [update_noteq h, update_noteq h', update_noteq h, update_noteq h']

variable (f : ι → α) (i j : ι) (k : ι)

def swapValues (f : ι → α) (i j : ι) : ι → α :=
  update (update f i (f j)) j (f i)

lemma swapValues_eq_update_update :
    swapValues f i j = update (update f i (f j)) j (f i) :=
  rfl

@[simp] lemma swapValues_fst : swapValues f i j i = f j := by
  rw [swapValues_eq_update_update]
  by_cases h : i = j
  · subst h
    rw [update_eq_self, update_same]
  · rw [update_update _ _ _ _ _ h, update_same]

@[simp] lemma swapValues_snd : swapValues f i j j = f i := by
  rw [swapValues_eq_update_update, update_same]

lemma swapValues_apply (hi : k ≠ i) (hj : k ≠ j) :
    swapValues f i j k = f k := by
  rw [swapValues_eq_update_update]
  rw [update_noteq hj, update_noteq hi]

lemma swapValues_comp {β : Type*} (g : α → β) :
    swapValues (g.comp f) i j = g ∘ swapValues f i j := by
  simp only [swapValues_eq_update_update, comp_apply, ← update_comp]
end

section

variable {ι : Type*} [DecidableEq ι] {M : ι → Type*} {i₀ i₁ : ι} (hi : i₀ ≠ i₁)
  (f : ∀ (i : ({i₀, i₁}ᶜ : Set ι)), M i) (x₀ : M i₀) (x₁ : M i₁)

def extendComplPair (i : ι) : M i :=
  extendComplSingleton _
    (extendComplSingleton (ι := ({i₀}ᶜ : Set ι)) (M := fun j ↦ M j)
      (i₀ := ⟨i₁, by simpa using hi.symm⟩) (fun ⟨j, hj⟩ ↦ f ⟨j, by
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        constructor
        · simpa [-Subtype.coe_prop] using j.2
        · obtain ⟨j, hj'⟩ := j
          rw [Set.mem_compl_iff] at hj
          intro hj''
          obtain rfl : j = i₁ := by simpa using hj''
          exact hj (Set.mem_singleton _)
        ⟩) x₁) x₀ i

@[simp]
lemma extendComplPair_zero : extendComplPair hi f x₀ x₁ i₀ = x₀ := by
  simp [extendComplPair]

@[simp]
lemma extendComplPair_one : extendComplPair hi f x₀ x₁ i₁ = x₁ := by
  dsimp [extendComplPair]
  rw [extendComplSingleton_of_neq _ _ _ _ hi.symm,
    extendComplSingleton_self]

lemma extendComplPair_of_neq (i : ι) (h₀ : i ≠ i₀) (h₁ : i ≠ i₁):
    extendComplPair hi f x₀ x₁ i = f ⟨i, by
      rw [Set.mem_compl_iff, Not, Set.mem_insert_iff, Set.mem_singleton_iff,
        imp_false, not_or]
      exact ⟨h₀, h₁⟩⟩ := by
  dsimp [extendComplPair]
  rw [extendComplSingleton_of_neq _ _ _ _ h₀,
    extendComplSingleton_of_neq _ _ _ _ (by simpa using h₁)]

@[simp]
lemma extendComplPair_restriction (φ : ∀ i, M i) :
    extendComplPair hi (fun i ↦ φ i) (φ i₀) (φ i₁) = φ := by
  ext i
  by_cases h₀ : i = i₀
  · subst h₀
    simp
  · by_cases h₁ : i = i₁
    · subst h₁
      simp
    · rw [extendComplPair_of_neq _ _ _ _ _ h₀ h₁]

lemma extendComplPair_update (k : ({i₀, i₁}ᶜ : Set ι)) (x : M k) :
    extendComplPair hi (update f k x) x₀ x₁ =
      update (extendComplPair hi f x₀ x₁) k x := by
  obtain ⟨k, hk⟩ := k
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hk
  ext i
  by_cases h₀ : i = i₀
  · subst h₀
    rw [extendComplPair_zero, update_noteq (Ne.symm hk.1), extendComplPair_zero]
  · by_cases h₁ : i = i₁
    · subst h₁
      rw [extendComplPair_one, update_noteq (Ne.symm hk.2), extendComplPair_one]
    · rw [extendComplPair_of_neq _ _ _ _ _ h₀ h₁]
      by_cases hik : i = k
      · subst hik
        simp
      · rw [update_noteq (by simpa using hik),
          update_noteq (by simpa using hik),
          extendComplPair_of_neq _ _ _ _ _ h₀ h₁]

@[simp]
lemma update_extendComplPair₀ (x₀' : M i₀) :
    update (extendComplPair hi f x₀ x₁) i₀ x₀' = extendComplPair hi f x₀' x₁ := by
  ext i
  by_cases h₀ : i = i₀
  · subst h₀
    simp only [update_same, extendComplPair_zero]
  · by_cases h₁ : i = i₁
    · subst h₁
      simp only [update_noteq hi.symm, extendComplPair_one]
    · simp only [update_noteq h₀, extendComplPair_of_neq _ _ _ _ _ h₀ h₁]

@[simp]
lemma update_extendComplPair₁ (x₁' : M i₁) :
    update (extendComplPair hi f x₀ x₁) i₁ x₁' = extendComplPair hi f x₀ x₁' := by
  ext i
  by_cases h₁ : i = i₁
  · subst h₁
    simp only [update_same, extendComplPair_one]
  · by_cases h₀ : i = i₀
    · subst h₀
      simp only [update_noteq hi, extendComplPair_zero]
    · simp only [update_noteq h₁, extendComplPair_of_neq _ _ _ _ _ h₀ h₁]

lemma extendComplPair_comp {α : Type*} (f : ({i₀, i₁}ᶜ : Set ι) → α) {β : Type*} (g : α → β)
    (x₀ x₁ : α) :
    extendComplPair (M := fun _ ↦ β) hi (g.comp f) (g x₀) (g x₁) =
      g ∘ extendComplPair (M := fun _ ↦ α) hi f x₀ x₁ := by
  ext i
  by_cases h₀ : i = i₀
  · subst h₀
    simp
  · by_cases h₁ : i = i₁
    · subst h₁
      simp
    · simp [extendComplPair_of_neq _ _ _ _ _ h₀ h₁]

lemma swapValues_extendComplPair {α : Type*} (f : ({i₀, i₁}ᶜ : Set ι) → α) (x₀ x₁ : α):
    swapValues (extendComplPair hi f x₀ x₁) i₀ i₁ = extendComplPair hi f x₁ x₀ := by
  ext i
  by_cases h₀ : i = i₀
  · subst h₀
    simp
  · by_cases h₁ : i = i₁
    · subst h₁
      simp
    · rw [swapValues_apply _ _ _ _ h₀ h₁, extendComplPair_of_neq _ _ _ _ _ h₀ h₁,
        extendComplPair_of_neq _ _ _ _ _ h₀ h₁]

end

end Function

open Function

lemma AlternatingMap.antisymmetry {R M N ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [DecidableEq ι]
    (f : AlternatingMap R M N ι) (x : ι → M) (i j : ι) (hij : i ≠ j) :
    f (Function.swapValues x i j) = - f x := by
  have := f.map_eq_zero_of_eq
    (Function.update (Function.update x i (x i + x j)) j (x i + x j))
    (by simp [update_noteq hij]) hij
  rw [map_update_add, update_update _ _ _ _ _ hij, map_update_add,
    update_update _ _ _ _ _ hij, map_update_add] at this
  nth_rw 1 [f.map_eq_zero_of_eq (hij := hij)] at this; swap
  · rw [update_same, update_update _ _ _ _ _ hij.symm, update_same]
  nth_rw 3 [f.map_eq_zero_of_eq (hij := hij)] at this; swap
  · rw [update_same, update_update _ _ _ _ _ hij.symm, update_same]
  rw [zero_add, add_zero, ← eq_neg_iff_add_eq_zero, update_eq_self, update_eq_self] at this
  rw [swapValues_eq_update_update, update_update _ _ _ _ _ hij]
  exact this

lemma LinearMap.alternating_of_generators {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] M →ₗ[R] N) {γ : Type*} {g : γ → M}
    (hg : Submodule.span R (Set.range g) = ⊤)
    (hf₁ : ∀ i , f (g i) (g i) = 0) (hf₂ : ∀ i j, f (g j) (g i) = - f (g i) (g j))
    (v : M) : f v v = 0 := by
  have antisym (v w : M) : f w v = - f v w := by
    suffices f.flip = -f from DFunLike.congr_fun (DFunLike.congr_fun this v) w
    rw [Submodule.linearMap_eq_iff_of_span_eq_top (hM := hg)]
    rintro ⟨_, ⟨i, rfl⟩⟩
    rw [Submodule.linearMap_eq_iff_of_span_eq_top (hM := hg)]
    rintro ⟨_, ⟨j, rfl⟩⟩
    exact hf₂ i j
  have hv : v ∈ Submodule.span R (Set.range g) := by simp only [hg, Submodule.mem_top]
  induction hv using Submodule.span_induction with
  | mem m hm =>
      obtain ⟨v, rfl⟩ := hm
      exact hf₁ v
  | zero => simp
  | add m₁ m₂ hm₁ hm₂ h₁ h₂ => simp [h₁, h₂, antisym m₁ m₂]
  | smul a m hm h => simp [h]

namespace MultilinearMap

variable {R : Type*} [CommRing R]
    {ι : Type*} [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    {N : Type*} [AddCommGroup N] [Module R N]
    (f : MultilinearMap R M N) {i j : ι} (hij : i ≠ j)

def curry₂ :
    M i →ₗ[R] M j →ₗ[R] MultilinearMap R (fun (k : ({i, j}ᶜ : Set ι)) ↦ M k) N where
  toFun := fun mi ↦
    { toFun := fun mj ↦ MultilinearMap.mk' (fun m ↦ f (extendComplPair hij m mi mj))
        (fun m k m₀ m₁ ↦ by
          dsimp
          simp only [Function.extendComplPair_update, f.map_update_add])
        (fun m k r m₀ ↦ by
          dsimp
          simp only [Function.extendComplPair_update, f.map_update_smul])
      map_add' := fun mj mj' ↦ by
        ext m
        simpa only [update_extendComplPair₁] using
          f.map_update_add (extendComplPair hij m mi 0) j mj mj'
      map_smul' := fun r mj ↦ by
        ext m
        simpa only [update_extendComplPair₁] using
          f.map_update_smul (extendComplPair hij m mi 0) j r mj }
  map_add' mi mi' := by
    ext mj m
    simpa only [update_extendComplPair₀] using
      f.map_update_add (extendComplPair hij m 0 mj) i mi mi'
  map_smul' r mi := by
    ext mj m
    simpa only [update_extendComplPair₀] using
      f.map_update_smul (extendComplPair hij m 0 mj) i r mi

lemma curry₂_apply (mi : M i) (mj : M j) (v : (k : ({i, j}ᶜ : Set ι)) → M k) :
    curry₂ f hij mi mj v = f (extendComplPair hij v mi mj) :=
  rfl

lemma curry₂_apply_restriction (v : (i : ι) → M i) :
    curry₂ f hij (v i) (v j) (fun k ↦ v k) = f v := by
  simp [curry₂]

variable [DecidableEq ι]
lemma map_eq_zero_of_eq_of_generators {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] {ι : Type*} [DecidableEq ι] [Finite ι]
    (f : MultilinearMap R (fun (_ : ι) ↦ M) N) {γ : Type*} {g : γ → M}
    (hg : Submodule.span R (Set.range g) = ⊤)
    {i j : ι} (hij : i ≠ j) (hf₁ : ∀ (k : ι → γ) (_ : k i = k j), f (g ∘ k) = 0)
    (hf₂ : ∀ (k : ι → γ), f (swapValues (g ∘ k) i j) = -f (g ∘ k))
    (v : ι → M) (hv : v i = v j) :
    f v = 0 := by
  rw [← curry₂_apply_restriction _ hij, ← hv]
  rw [LinearMap.alternating_of_generators (curry₂ f hij) hg, zero_apply]
  · intro k
    apply MultilinearMap.ext_of_span_eq_top (hg := fun _ ↦ hg)
    intro g'
    dsimp
    rw [curry₂_apply]
    have := hf₁ (extendComplPair (hi := hij) (M := fun _ ↦ γ) g' k k) (by simp)
    rw [← extendComplPair_comp] at this
    exact this
  · intro k₁ k₂
    apply MultilinearMap.ext_of_span_eq_top (hg := fun _ ↦ hg)
    intro g'
    dsimp
    have := hf₂ (extendComplPair (hi := hij) (M := fun _ ↦ γ) g' k₁ k₂)
    rw [swapValues_comp, swapValues_extendComplPair,
      ← extendComplPair_comp, ← extendComplPair_comp] at this
    rw [curry₂_apply, curry₂_apply]
    exact this

end MultilinearMap

namespace Module

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

namespace Relations

variable {R}
variable (relation : Relations R) (n : ℕ)

namespace exteriorPower

variable (n : ℕ)
inductive Rels
  | piTensor (i₀ : Fin n) (r : relation.R) (g : ∀ (i : Fin n) (_ : i ≠ i₀), relation.G)
  | antisymmetry (g : Fin n → relation.G) (i j : Fin n) (hg : i ≠ j)
  | alternate (g : Fin n → relation.G) (i j : Fin n) (hg : g i = g j) (hij : i ≠ j)

end exteriorPower

@[simps]
noncomputable def exteriorPower : Relations R where
  G := Fin n → relation.G
  R := exteriorPower.Rels relation n
  relation x := match x with
    | .piTensor i₀ r g => (piTensor (fun _ ↦ relation)).relation
          (⟨i₀, r, fun ⟨a, ha⟩ ↦ g a ha⟩)
    | .antisymmetry g i j _ => Finsupp.single (swapValues g i j) 1 + Finsupp.single g 1
    | .alternate g _ _ _ _ => Finsupp.single g 1

namespace Solution

variable {M}
variable {relation} (s : relation.Solution M)

@[simps var]
def exteriorPower (n : ℕ) : (relation.exteriorPower n).Solution
    (ExteriorAlgebra.exteriorPower R n M) where
  var g := exteriorPower.ιMulti _ _ (s.var ∘ g)
  linearCombination_var_relation := by
    rintro (⟨i₀, r, g⟩ | ⟨g, i, j, hij⟩ | ⟨g, i, j, hg, hij⟩)
    · have := ((Relations.Solution.piTensor (fun (i : Fin n) ↦ s)).postcomp
        (exteriorPower.fromTensorPower R M n)).linearCombination_var_relation
        ⟨i₀, r, fun ⟨i, hi⟩ ↦ g i hi⟩
      dsimp at this ⊢
      simp only [Finsupp.linearCombination_embDomain] at this ⊢
      convert this
      aesop
    · dsimp
      simp only [map_add, Finsupp.linearCombination_single, one_smul,
        ← swapValues_comp, AlternatingMap.antisymmetry _ _ _ _ hij, neg_add_cancel]
    · dsimp
      simp only [Finsupp.linearCombination_single, one_smul]
      exact AlternatingMap.map_eq_zero_of_eq _ _ (by simp [hg]) hij

variable {s}

namespace isPresentationCore

variable {N : Type*} [AddCommGroup N] [Module R N]
  (h : s.IsPresentation) {n : ℕ} (t : (relation.exteriorPower n).Solution N)

noncomputable def descAsMultilinearMap :
    MultilinearMap R (fun (_ : Fin n) ↦ M) N :=
      LinearMap.compMultilinearMap (
        (IsPresentation.piTensor (fun (_ : Fin n) ↦ h)).desc
          { var := t.var
            linearCombination_var_relation := by
              rintro ⟨i₀, r, g⟩
              exact t.π_relation (.piTensor i₀ r (fun i hi ↦ g ⟨i, hi⟩)) })
        (PiTensorProduct.tprod (R := R) )

@[simp]
lemma descAsMultilinearMap_apply (g : Fin n → relation.G) :
    descAsMultilinearMap h t (s.var ∘ g) = t.var g :=
  IsPresentation.desc_var _ _ _

lemma map_eq_zero_of_eq (v : Fin n → M) (i j : Fin n) (hv : v i = v j) (hij : i ≠ j) :
    descAsMultilinearMap h t v = 0 := by
  apply MultilinearMap.map_eq_zero_of_eq_of_generators (hg := h.span_var_eq_top)
    (hij := hij) (v := v) (hv := hv)
  · intro k hk
    have := t.π_relation (.alternate k i j hk hij)
    dsimp at this
    erw [π_single] at this
    simpa only [descAsMultilinearMap_apply] using this
  · intro k
    have := t.π_relation (.antisymmetry k i j hij)
    dsimp at this
    rw [map_add] at this
    erw [π_single, π_single] at this
    simpa only [swapValues_comp, descAsMultilinearMap_apply, eq_neg_iff_add_eq_zero] using this

end isPresentationCore

open isPresentationCore in
noncomputable def isPresentationCore (h : s.IsPresentation) (n : ℕ) :
    IsPresentationCore.{w} (s.exteriorPower n) where
  desc t := exteriorPower.alternatingMapLinearEquiv
    { toMultilinearMap := descAsMultilinearMap h t
      map_eq_zero_of_eq' := map_eq_zero_of_eq h t }
  postcomp_desc t := by aesop
  postcomp_injective {N _ _ f f'} hff' := by
    rw [Submodule.linearMap_eq_iff_of_span_eq_top
      (hM := exteriorPower.span_ιMulti_of_span_eq_top (hg := h.span_var_eq_top) n)]
    rintro ⟨_, ⟨g, rfl⟩⟩
    simpa using congr_var hff' g

lemma IsPresentation.exteriorPower (h : s.IsPresentation) (n : ℕ) :
    (s.exteriorPower n).IsPresentation :=
  (isPresentationCore h n).isPresentation

end Solution

end Relations

namespace Presentation

variable {R M} (pres : Presentation R M) (n : ℕ)

@[simps! R G relation var]
noncomputable def exteriorPower : Presentation R (ExteriorAlgebra.exteriorPower R n M) where
  toSolution := pres.toSolution.exteriorPower n
  toIsPresentation := pres.toIsPresentation.exteriorPower n

end Presentation

end Module
