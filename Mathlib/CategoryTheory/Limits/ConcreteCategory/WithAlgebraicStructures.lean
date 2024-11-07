/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
import Mathlib.Tactic.ApplyFun

/-!

# Colimits in concrete categories with algebraic structures

Let `C` be a concrete category and `F : J ⥤ C` a filtered diagram in `C`. We discuss some results
about `colimit F` when objects and morphisms in `C` have some algebraic structures.

## Main results
- `CategoryTheory.Limits.Concrete.colimit_rep_eq_zero`: Let `C` be a category where its objects have
  zero elements and morphisms preserve zero. If `x : Fⱼ` is mapped to `0` in the colimit, then
  there exists a `i ⟶ j` such that `x` restricted to `i` is already `0`.

- `CategoryTheory.Limits.Concrete.colimit_no_zero_smul_divisor`: Let `C` be a category where its
  objects are `R`-modules and morphisms `R`-linear maps. Let `r : R` be an element without zero
  smul divisors for all small sections, i.e. there exists some `j : J` such that for all `j ⟶ i`
  and `x : Fᵢ` we have `r • x = 0` implies `x = 0`, then if `r • x = 0` for `x : colimit F`, then
  `x = 0`.

Let `R` be the filtered colimit of rings `{Rⱼ}` and `M` be the filtered colimit of abelian groups
`{Mⱼ}`  with `j` running through the same filtered index category `J`. If for each `j ∈ J`, `Mⱼ` is
an `Rⱼ`-module such that the `Rⱼ`-actions are compatible, then `M` is an `Rⱼ`-module for all `j`
and `M` is an `R`-module.

- `Module.overFilteredColimits.moduleColimitColimit`: Let `R` and `M` be as above, then `M` is an
  `R`-module.

- `Module.overFilteredColimits.smul_spec`: Let `R` and `M` be as above, then the `R`-action on `M`
  is given by the following: if `s : Rⱼ₁` and `t : Mⱼ₂` where `j₁ ≤ j₃` and `j₂ ≤ j₃`, then
  `[s] • [m]` is equal to `[s|ⱼ₃ • m |ⱼ₃]` where `[...]` is the equivalence class in the colimit.

## Implementation notes on `Module.overFilteredColimits`

1. We choose not to use `PresheafOfModules` to avoid code duplication:
consider `R : J ⥤ CommRingCat` and `M : J ⥤ AddCommGrp`, then `colimit M` is both a
`colimit R`-module and a `colimit (R ⋙ forget₂ CommRingCat RingCat)`-module; the two module
structures are virtually the same. This situation manifests in stalks of sheaves of modules:
for any ringed space `X` and a sheaf of `𝒪_X`-module `ℳ`, we want to think the stalk `ℳₓ` as an
`𝒪_{X,x}`-module. But since `PresheafOfModules` requires a presheaf of `RingCat` not `CommRingCat`,
we need to compose the sheaf with forgetful functors, but we don't want to think about the
difference between `𝒪_{X, x}` as a colimit in `CommRing` and `𝒪_{X, x}` as a colimit in `RingCat`
all the time. So we ask `R` and `M` to be functors into concrete categories which behaves like rings
and abelian groups respectively.

2. Other than `Module.overFilteredColimits.{moduleColimitColimit, smul_spec}`, everything else in
this namespace is implementation details and is probably not very useful.

-/

universe t w v v' u u' r uc₁ uc₂

open CategoryTheory

namespace CategoryTheory.Limits.Concrete

attribute [local instance] ConcreteCategory.instFunLike ConcreteCategory.hasCoeToSort

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{max t w} C] {J : Type w} [Category.{r} J]

section zero

theorem colimit_rep_eq_zero
    (F : J ⥤ C) [PreservesColimit F (forget C)] [IsFiltered J]
    [∀ c : C, Zero c] [∀ {c c' : C}, ZeroHomClass (c ⟶ c') c c'] [HasColimit F]
    (j : J) (x : F.obj j) (hx : colimit.ι F j x = 0) :
    ∃ (j' : J) (i : j ⟶ j'), F.map i x = 0 := by
  rw [show 0 = colimit.ι F j 0 by simp, colimit_rep_eq_iff_exists] at hx
  obtain ⟨j', i, y, g⟩ := hx
  exact ⟨j', i, g ▸ by simp⟩

end zero

section module

/--
if `r` has no zero smul divisors for all small-enough sections, then `r` has no zero smul divisors
in the colimit.
-/
lemma colimit_no_zero_smul_divisor
    (F : J ⥤ C) [PreservesColimit F (forget C)] [IsFiltered J] [HasColimit F]
    (R : Type*) [Semiring R]
    [∀ c : C, AddCommMonoid c] [∀ c : C, Module R c]
    [∀ {c c' : C}, LinearMapClass (c ⟶ c') R c c']
    (r : R) (H : ∃ (j' : J), ∀ (j : J) (_ : j' ⟶ j), ∀ (c : F.obj j), r • c = 0 → c = 0)
    (x : (forget C).obj (colimit F)) (hx : r • x = 0) : x = 0 := by
  classical
  obtain ⟨j, x, rfl⟩ := Concrete.colimit_exists_rep F x
  rw [← map_smul] at hx
  obtain ⟨j', i, h⟩ := Concrete.colimit_rep_eq_zero (hx := hx)
  obtain ⟨j'', H⟩ := H
  simpa [elementwise_of% (colimit.w F), map_zero] using congr(colimit.ι F _
    $(H (IsFiltered.sup {j, j', j''} { ⟨j, j', by simp, by simp, i⟩ })
      (IsFiltered.toSup _ _ <| by simp)
      (F.map (IsFiltered.toSup _ _ <| by simp) x)
      (by rw [← IsFiltered.toSup_commutes (f := i) (mY := by simp) (mf := by simp), F.map_comp,
        comp_apply, ← map_smul, ← map_smul, h, map_zero])))

end module

section module_over_filtered_colimit

/-!
# Module structure of `colim Mᵢ` over `colim Rᵢ`

Let `R` be the filtered colimit of rings `{Rⱼ}` and `M` be the filtered colimit of abelian groups
`{Mⱼ}`  with `j` running through the same filtered index category `J`. If for each `j ∈ J`, `Mⱼ` is
an `Rⱼ`-module such that the `Rⱼ`-actions are compatible, then `M` is an `Rⱼ`-module for all `j`
and `M` is an `R`-module. We put a module structure on `colim Mᵢ` over `colim Rᵢ` where the scalar
multiplication is given by `r • m = [a|ₛ • b|ₛ]` where `a : Rᵢ` and `b : Mⱼ` represent `r` and `m`
and `s` refines both `i` and `j`.

-/

variable {ℜ𝔦𝔫𝔤 : Type u} [Category.{u'} ℜ𝔦𝔫𝔤] [ConcreteCategory.{max uc₁ w} ℜ𝔦𝔫𝔤]
variable {𝔄𝔟 : Type v} [Category.{v'} 𝔄𝔟] [ConcreteCategory.{max uc₂ w} 𝔄𝔟]
variable (ℛ : J ⥤ ℜ𝔦𝔫𝔤) (ℳ : J ⥤ 𝔄𝔟)

variable [∀ x : ℜ𝔦𝔫𝔤, Semiring x] [∀ x : 𝔄𝔟, AddCommMonoid x]
variable [∀ x y : ℜ𝔦𝔫𝔤, RingHomClass (x ⟶ y) x y]
variable [∀ x y : 𝔄𝔟, AddMonoidHomClass (x ⟶ y) x y]

variable [HasColimit ℛ] [HasColimit ℳ]
variable [PreservesColimit ℛ (forget ℜ𝔦𝔫𝔤)] [PreservesColimit ℳ (forget 𝔄𝔟)]

variable [∀ c, Module (ℛ.obj c) (ℳ.obj c)]
variable [compatible_smul : Fact <| ∀ {c₁ c₂ : J} (i₁ : c₁ ⟶ c₂) (r : ℛ.obj c₁) (m : ℳ.obj c₁),
    ℳ.map i₁ (r • m) = ℛ.map i₁ r • ℳ.map i₁ m]

variable [IsFiltered J]

namespace Module.overFilteredColimits

variable {ℛ ℳ} in
/--
Let `R` be the filtered colimit of rings `{Rⱼ}` and `M` be the filtered colimit of
abelian groups `{Mⱼ}`  with the same filtered indexing category `J`, if for each `j ∈ J`,
`Mⱼ` is an `Rⱼ`-module such that the `Rⱼ`-actions are compatible, then there is a heterogeneous
scalar multiplication `Rᵢ → Mⱼ → Mₖ` for every `i → j` and `i → k`.
-/
def hSMul {c₁ c₂ c₃ : J} (i₁ : c₁ ⟶ c₃) (i₂ : c₂ ⟶ c₃)
    (r : ℛ.obj c₁) (m : ℳ.obj c₂) : ℳ.obj c₃ :=
  (ℛ.map i₁ r) • (ℳ.map i₂ m)

section hSMul

variable {c₁ c₂ c₃ : J} (i₁ : c₁ ⟶ c₃) (i₂ : c₂ ⟶ c₃)
variable (r : ℛ.obj c₁) (m : ℳ.obj c₂)

omit [∀ (x y : 𝔄𝔟), AddMonoidHomClass (x ⟶ y) x y]
  [HasColimit ℛ] [HasColimit ℳ]
  [PreservesColimit ℛ (forget ℜ𝔦𝔫𝔤)] [PreservesColimit ℳ (forget 𝔄𝔟)]
  compatible_smul [IsFiltered J] in
@[simp]
lemma one_hSMul :
    hSMul i₁ i₂ (1 : ℛ.obj c₁) m = (ℳ.map i₂ m) := by
  simp [hSMul]

omit [∀ (x y : 𝔄𝔟), AddMonoidHomClass (x ⟶ y) x y]
  [HasColimit ℛ] [HasColimit ℳ]
  [PreservesColimit ℛ (forget ℜ𝔦𝔫𝔤)] [PreservesColimit ℳ (forget 𝔄𝔟)]
  compatible_smul [IsFiltered J] in
lemma mul_hSMul (r₁ r₂ : ℛ.obj c₁) : hSMul i₁ i₂ (r₁ * r₂) m =
    hSMul i₁ (𝟙 _) r₁ (hSMul i₁ i₂ r₂ m) := by
  simp only [hSMul, map_mul, mul_smul]
  rw [ℳ.map_id, id_apply]

omit [∀ (x y : ℜ𝔦𝔫𝔤), RingHomClass (x ⟶ y) x y]
  [HasColimit ℛ] [HasColimit ℳ]
  [PreservesColimit ℛ (forget ℜ𝔦𝔫𝔤)] [PreservesColimit ℳ (forget 𝔄𝔟)]
  compatible_smul [IsFiltered J] in
@[simp]
lemma hSMul_zero : hSMul (ℳ := ℳ) i₁ i₂ r 0 = 0 := by
  simp [hSMul]

omit [∀ (x y : ℜ𝔦𝔫𝔤), RingHomClass (x ⟶ y) x y]
  [HasColimit ℛ] [HasColimit ℳ]
  [PreservesColimit ℛ (forget ℜ𝔦𝔫𝔤)] [PreservesColimit ℳ (forget 𝔄𝔟)]
  compatible_smul [IsFiltered J] in
lemma hSMul_add (m₁ m₂ : ℳ.obj c₂) : hSMul i₁ i₂ r (m₁ + m₂) =
    hSMul i₁ i₂ r m₁ + hSMul i₁ i₂ r m₂ := by
  simp [hSMul, smul_add]

omit [∀ (x y : 𝔄𝔟), AddMonoidHomClass (x ⟶ y) x y]
  [HasColimit ℛ] [HasColimit ℳ]
  [PreservesColimit ℛ (forget ℜ𝔦𝔫𝔤)] [PreservesColimit ℳ (forget 𝔄𝔟)]
  compatible_smul [IsFiltered J] in
lemma add_hSMul (r₁ r₂ : ℛ.obj c₁) (m : ℳ.obj c₂) :
    hSMul i₁ i₂ (r₁ + r₂) m = hSMul i₁ i₂ r₁ m + hSMul i₁ i₂ r₂ m := by
  simp [hSMul, add_smul]

omit [∀ (x y : 𝔄𝔟), AddMonoidHomClass (x ⟶ y) x y]
  [HasColimit ℛ] [HasColimit ℳ]
  [PreservesColimit ℛ (forget ℜ𝔦𝔫𝔤)] [PreservesColimit ℳ (forget 𝔄𝔟)]
  compatible_smul [IsFiltered J] in
@[simp]
lemma zero_hSMul : hSMul i₁ i₂ (0 : ℛ.obj c₁) m = 0 := by
  simp [hSMul]

omit [∀ (x y : ℜ𝔦𝔫𝔤), RingHomClass (x ⟶ y) x y] [∀ (x y : 𝔄𝔟), AddMonoidHomClass (x ⟶ y) x y] in
lemma hSMul_respect_ι
    {c₁ c₂ c₃ : J} (i₁ : c₁ ⟶ c₃) (i₂ : c₂ ⟶ c₃)
    (r : ℛ.obj c₁) (x : ℳ.obj c₂)
    {d₁ d₂ d₃ : J} (j₁ : d₁ ⟶ d₃) (j₂ :  d₂ ⟶ d₃)
    (r' : ℛ.obj d₁) (x' : ℳ.obj d₂)
    (hrr' : colimit.ι ℛ _ r = colimit.ι ℛ _ r')
    (hmm' : colimit.ι ℳ _ x = colimit.ι ℳ _ x') :
    colimit.ι ℳ _ (hSMul i₁ i₂ r x) =
    colimit.ι ℳ _ (hSMul j₁ j₂ r' x') := by
  classical
  obtain ⟨m, fm₁, fm₂, hm⟩ := Concrete.colimit_exists_of_rep_eq (h := hrr')
  obtain ⟨n, fn₁, fn₂, hn⟩ := Concrete.colimit_exists_of_rep_eq (h := hmm')
  rw [Concrete.colimit_rep_eq_iff_exists]
  let O : Finset J := { c₁, c₂, c₃, d₁, d₂, d₃, m, n }
  let H : Finset ((X : J) ×' (Y : J) ×' (_ : X ∈ O) ×' (_ : Y ∈ O) ×' (X ⟶ Y)) :=
  { ⟨c₁, m, by simp [O], by simp [O], fm₁⟩,
    ⟨d₁, m, by simp [O], by simp [O], fm₂⟩,
    ⟨c₂, n, by simp [O], by simp [O], fn₁⟩,
    ⟨d₂, n, by simp [O], by simp [O], fn₂⟩,
    ⟨c₁, c₃, by simp [O], by simp [O], i₁⟩,
    ⟨c₂, c₃, by simp [O], by simp [O], i₂⟩,
    ⟨d₁, d₃, by simp [O], by simp [O], j₁⟩,
    ⟨d₂, d₃, by simp [O], by simp [O], j₂⟩ }

  let S := IsFiltered.sup O H

  refine ⟨S, IsFiltered.toSup O H (by simp [O]), IsFiltered.toSup _ _ (by simp [O]), ?_⟩
  delta hSMul
  rw [compatible_smul.out, compatible_smul.out]
  apply_fun ℛ.map (IsFiltered.toSup O H (by simp [O])) at hm
  rw [← comp_apply, ← comp_apply, ← ℛ.map_comp, ← ℛ.map_comp] at hm

  apply_fun ℳ.map (IsFiltered.toSup O H (by simp [O])) at hn
  rw [← comp_apply, ← comp_apply, ← ℳ.map_comp, ← ℳ.map_comp] at hn

  rw [← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply, ← ℛ.map_comp, ← ℛ.map_comp,
    ← ℳ.map_comp, ← ℳ.map_comp]
  convert congr($hm • $hn) using 1 <;> congr 3
  · rw [IsFiltered.toSup_commutes O H (f := i₁), IsFiltered.toSup_commutes O H (f := fm₁)]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, O]
    · simp only [Finset.mem_insert, PSigma.mk.injEq, heq_eq_eq, true_and, Finset.mem_singleton,
      true_or, O, H]
    · simp only [Finset.mem_insert, PSigma.mk.injEq, heq_eq_eq, true_and, Finset.mem_singleton,
      true_or, or_true, O, H]
  · rw [IsFiltered.toSup_commutes O H (f := i₂), IsFiltered.toSup_commutes O H (f := fn₁)]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, O]
    · simp only [Finset.mem_insert, PSigma.mk.injEq, heq_eq_eq, true_and, Finset.mem_singleton,
      true_or, or_true, O, H]
    · simp only [Finset.mem_insert, PSigma.mk.injEq, heq_eq_eq, true_and, Finset.mem_singleton,
      true_or, or_true, O, H]
  · rw [IsFiltered.toSup_commutes O H (f := j₁), IsFiltered.toSup_commutes O H (f := fm₂)]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, O]
    · simp only [Finset.mem_insert, PSigma.mk.injEq, heq_eq_eq, true_and, Finset.mem_singleton,
      true_or, or_true, O, H]
    · simp only [Finset.mem_insert, PSigma.mk.injEq, heq_eq_eq, true_and, Finset.mem_singleton,
      true_or, or_true, O, H]
  · rw [IsFiltered.toSup_commutes O H (f := j₂), IsFiltered.toSup_commutes O H (f := fn₂)]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, O]
    · simp only [Finset.mem_insert, PSigma.mk.injEq, Finset.mem_singleton, heq_eq_eq, true_and,
      true_or, or_true, O, H]
    · simp only [Finset.mem_insert, PSigma.mk.injEq, heq_eq_eq, true_and, Finset.mem_singleton,
      or_true, O, H]

end hSMul

variable {ℛ ℳ} in
/--
Let `R` be the filtered colimit of rings `{Rⱼ}` and `M` be the filtered colimit of
abelian groups `{Mⱼ}` with the same filtered indexing category `j ∈ J`, if for each `j ∈ J`,
`Mⱼ` is an `Rⱼ`-module such that the `Rⱼ`-actions are compatible with the morphisms in `J`,
then there is a scalar multiplication `Rⱼ → M → M` for every `j ∈ J`.
-/
noncomputable def smulColimit {c : J} (r : ℛ.obj c) (m : colimit (C := 𝔄𝔟) ℳ) :
    colimit (C := 𝔄𝔟) ℳ :=
  colimit.ι ℳ (IsFiltered.max c (Concrete.indexRepColimit ℳ m))
   (hSMul (IsFiltered.leftToMax _ _) (IsFiltered.rightToMax _ _)
    r (Concrete.repColimit ℳ m))

section smulColimit

omit [∀ (x y : ℜ𝔦𝔫𝔤), RingHomClass (x ⟶ y) x y] [∀ (x y : 𝔄𝔟), AddMonoidHomClass (x ⟶ y) x y] in
@[simp]
lemma smulColimit_smul_rep (c₁ c₂ : J) (r : ℛ.obj c₁) (m : ℳ.obj c₂) :
    smulColimit r (colimit.ι ℳ c₂ m) =
    colimit.ι ℳ (IsFiltered.max c₁ c₂)
    (hSMul (IsFiltered.leftToMax _ _) (IsFiltered.rightToMax _ _) r m) := by
  apply hSMul_respect_ι
  · rfl
  · rw [Concrete.ι_repColimit_eq]

omit [∀ (x y : 𝔄𝔟), AddMonoidHomClass (x ⟶ y) x y] in
@[simp]
lemma smulColimit_one_smul (c : J) (m : colimit (C := 𝔄𝔟) ℳ) :
    smulColimit (1 : ℛ.obj c) m = m := by
  rw [show m = colimit.ι ℳ (Concrete.indexRepColimit ℳ m) _ by
    rw [Concrete.ι_repColimit_eq], smulColimit_smul_rep, one_hSMul, colimit.w_apply]

omit [∀ (x y : 𝔄𝔟), AddMonoidHomClass (x ⟶ y) x y] in
lemma smulColimit_mul_smul (c : J) (r₁ r₂ : ℛ.obj c)
    (m : colimit (C := 𝔄𝔟) ℳ) :
    smulColimit (r₁ * r₂) m = smulColimit r₁ (smulColimit r₂ m) := by
  simp only [show m = colimit.ι ℳ (Concrete.indexRepColimit ℳ m) _ by
    rw [Concrete.ι_repColimit_eq], smulColimit_smul_rep, mul_hSMul]
  apply hSMul_respect_ι
  · rfl
  · apply hSMul_respect_ι
    · rfl
    · rw [Concrete.ι_repColimit_eq]


omit [∀ (x y : ℜ𝔦𝔫𝔤), RingHomClass (x ⟶ y) x y] in
@[simp]
lemma smulColimit_smul_zero (c : J) (r : ℛ.obj c) : smulColimit (ℳ := ℳ) r 0 = 0 := by
  rw [show (0 : colimit (C := 𝔄𝔟) ℳ) = colimit.ι (C := 𝔄𝔟) ℳ c 0 by rw [map_zero],
    smulColimit_smul_rep, hSMul_zero, map_zero, map_zero]

omit [∀ (x y : ℜ𝔦𝔫𝔤), RingHomClass (x ⟶ y) x y] in
lemma smulColimit_smul_add (c : J) (r : ℛ.obj c) (m₁ m₂ : colimit (C := 𝔄𝔟) ℳ) :
    smulColimit r (m₁ + m₂) = smulColimit r m₁ + smulColimit r m₂ := by
  classical
  let O : Finset J :=
    { c, Concrete.indexRepColimit ℳ m₁, Concrete.indexRepColimit ℳ m₂ }
  let j : J := IsFiltered.sup O ∅

  have eq₁ : m₁ = colimit.ι ℳ j
      (ℳ.map (IsFiltered.toSup O ∅ <| by simp [O]) (Concrete.repColimit ℳ m₁)) := by
    simp only [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₂ : m₂ = colimit.ι ℳ j
      (ℳ.map (IsFiltered.toSup O ∅ <| by simp [O]) (Concrete.repColimit ℳ m₂)) := by
    simp only [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₃ : m₁ + m₂ = colimit.ι ℳ j
      (ℳ.map (IsFiltered.toSup O ∅ <| by simp [O]) (Concrete.repColimit ℳ m₁) +
       ℳ.map (IsFiltered.toSup O ∅ <| by simp [O]) (Concrete.repColimit ℳ m₂)) := by
    simp only [map_add, colimit.w_apply, Concrete.ι_repColimit_eq]

  rw [eq₃]
  conv_rhs => rw [eq₁]; rhs; rw [eq₂]
  rw [smulColimit_smul_rep, smulColimit_smul_rep, smulColimit_smul_rep, hSMul_add, map_add]

lemma smulColimit_add_smul (c : J) (r₁ r₂ : ℛ.obj c) (m : colimit (C := 𝔄𝔟) ℳ) :
    smulColimit (r₁ + r₂) m = smulColimit r₁ m + smulColimit r₂ m := by
  simp only [show m = colimit.ι ℳ (Concrete.indexRepColimit ℳ m) _ by
    rw [Concrete.ι_repColimit_eq], smulColimit_smul_rep, add_hSMul, map_add]

@[simp]
lemma smulColimit_zero_smul (c : J) (m : colimit (C := 𝔄𝔟) ℳ) :
    smulColimit (ℳ := ℳ) (0 : ℛ.obj c) m = 0 := by
  simp only [show m = colimit.ι ℳ (Concrete.indexRepColimit ℳ m) _ by
    rw [Concrete.ι_repColimit_eq], smulColimit_smul_rep, zero_hSMul, map_zero]

end smulColimit

noncomputable instance moduleObjColimit (j : J) :
    Module (ℛ.obj j) (colimit (C := 𝔄𝔟) ℳ) where
  smul := smulColimit
  one_smul := smulColimit_one_smul _ _ _
  mul_smul := smulColimit_mul_smul _ _ _
  smul_zero := smulColimit_smul_zero _ _ _
  smul_add := smulColimit_smul_add _ _ _
  add_smul := smulColimit_add_smul _ _ _
  zero_smul := smulColimit_zero_smul _ _ _

variable {ℛ ℳ} in
/--
Let `R` be the filtered colimit of rings `{Rⱼ}` and `M` be the filtered colimit of
abelian groups `{Mⱼ}`  with the same filtered indexing category `J`. If for each `j ∈ J`, `Mⱼ` is an
`Rⱼ`-module such that the `Rⱼ`-actions are compatible with the morphisms in `J`, then there is a
natural scalar multiplication `R → M → M`.
-/
noncomputable def colimitsmulColimit (r : colimit (C := ℜ𝔦𝔫𝔤) ℛ) (m : colimit (C := 𝔄𝔟) ℳ) :
    colimit (C := 𝔄𝔟) ℳ :=
  (smulColimit (Concrete.repColimit ℛ r) m)

section colimitsmulColimit

omit [∀ (x y : ℜ𝔦𝔫𝔤), RingHomClass (x ⟶ y) x y] [∀ (x y : 𝔄𝔟), AddMonoidHomClass (x ⟶ y) x y] in
@[simp]
lemma colimitsmulColimit_rep_smul {c : J} (r : ℛ.obj c) (m : colimit (C := 𝔄𝔟) ℳ) :
    colimitsmulColimit (colimit.ι ℛ c r) m = smulColimit r m := by
  rw [show m = colimit.ι ℳ (Concrete.indexRepColimit ℳ m) _ by
    rw [Concrete.ι_repColimit_eq], smulColimit_smul_rep]
  apply hSMul_respect_ι
  · rw [Concrete.ι_repColimit_eq]
  · rw [Concrete.ι_repColimit_eq, Concrete.ι_repColimit_eq]

omit [∀ (x y : 𝔄𝔟), AddMonoidHomClass (x ⟶ y) x y] in
@[simp]
lemma colimitsmulColimit_one_smul (m : colimit (C := 𝔄𝔟) ℳ) :
    colimitsmulColimit (1 : colimit (C := ℜ𝔦𝔫𝔤) ℛ) m = m := by
  let c : J := (inferInstance : IsFiltered J).2.some
  rw [show (1 : colimit (C := ℜ𝔦𝔫𝔤) ℛ) = colimit.ι ℛ c 1 by
    rw [map_one], colimitsmulColimit_rep_smul, smulColimit_one_smul]

omit [∀ (x y : 𝔄𝔟), AddMonoidHomClass (x ⟶ y) x y] in
lemma colimitsmulColimit_mul_smul
    (r₁ r₂ : colimit (C := ℜ𝔦𝔫𝔤) ℛ) (m : colimit (C := 𝔄𝔟) ℳ) :
    colimitsmulColimit (r₁ * r₂) m = colimitsmulColimit r₁ (colimitsmulColimit r₂ m) := by
  classical
  let O : Finset J :=
    {  Concrete.indexRepColimit ℛ r₁, Concrete.indexRepColimit ℛ r₂ }
  let j : J := IsFiltered.sup O ∅
  have eq₁ : r₁ = colimit.ι ℛ j
      (ℛ.map (IsFiltered.toSup O ∅ <| by simp [O]) (Concrete.repColimit ℛ r₁)) := by
    rw [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₂ : r₂ = colimit.ι ℛ j
      (ℛ.map (IsFiltered.toSup O ∅ <| by simp [O]) (Concrete.repColimit ℛ r₂)) := by
    rw [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₃ : r₁ * r₂ = colimit.ι ℛ j
      (ℛ.map (IsFiltered.toSup O ∅ <| by simp [O]) (Concrete.repColimit ℛ r₁) *
       ℛ.map (IsFiltered.toSup O ∅ <| by simp [O]) (Concrete.repColimit ℛ r₂)) := by
    rw [map_mul, colimit.w_apply, colimit.w_apply, Concrete.ι_repColimit_eq,
      Concrete.ι_repColimit_eq]
  rw [eq₃]
  conv_rhs => rw [eq₁]; rhs; rw [eq₂]
  rw [colimitsmulColimit_rep_smul, colimitsmulColimit_rep_smul, colimitsmulColimit_rep_smul,
    smulColimit_mul_smul]

omit [∀ (x y : ℜ𝔦𝔫𝔤), RingHomClass (x ⟶ y) x y] in
@[simp]
lemma colimitsmulColimit_smul_zero (r : colimit (C := ℜ𝔦𝔫𝔤) ℛ) :
    colimitsmulColimit (ℳ := ℳ) r 0 = 0 := by
  rw [show r = colimit.ι ℛ (Concrete.indexRepColimit ℛ r) _ by
    rw [Concrete.ι_repColimit_eq], colimitsmulColimit_rep_smul, smulColimit_smul_zero]

omit [∀ (x y : ℜ𝔦𝔫𝔤), RingHomClass (x ⟶ y) x y] in
lemma colimitsmulColimit_smul_add (r : colimit (C := ℜ𝔦𝔫𝔤) ℛ) (m₁ m₂ : colimit (C := 𝔄𝔟) ℳ) :
    colimitsmulColimit r (m₁ + m₂) = colimitsmulColimit r m₁ + colimitsmulColimit r m₂ := by
  simp only [show r = colimit.ι ℛ (Concrete.indexRepColimit ℛ r) _ by
      rw [Concrete.ι_repColimit_eq],
    colimitsmulColimit_rep_smul, smulColimit_smul_add]

lemma colimitsmulColimit_add_smul (r₁ r₂ : colimit (C := ℜ𝔦𝔫𝔤) ℛ) (m : colimit (C := 𝔄𝔟) ℳ) :
    colimitsmulColimit (r₁ + r₂) m = colimitsmulColimit r₁ m + colimitsmulColimit r₂ m := by
  classical
  let O : Finset J :=
    {  Concrete.indexRepColimit ℛ r₁, Concrete.indexRepColimit ℛ r₂ }
  let j : J := IsFiltered.sup O ∅
  have eq₁ : r₁ = colimit.ι ℛ j
      (ℛ.map (IsFiltered.toSup O ∅ <| by simp [O]) (Concrete.repColimit ℛ r₁)) := by
    rw [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₂ : r₂ = colimit.ι ℛ j
      (ℛ.map (IsFiltered.toSup O ∅ <| by simp [O]) (Concrete.repColimit ℛ r₂)) := by
    rw [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₃ : r₁ + r₂ = colimit.ι ℛ j
      (ℛ.map (IsFiltered.toSup O ∅ <| by simp [O]) (Concrete.repColimit ℛ r₁) +
       ℛ.map (IsFiltered.toSup O ∅ <| by simp [O]) (Concrete.repColimit ℛ r₂)) := by
    rw [map_add]
    rw [colimit.w_apply, colimit.w_apply, Concrete.ι_repColimit_eq, Concrete.ι_repColimit_eq]
  rw [eq₃]
  conv_rhs => rw [eq₁]; rhs; rw [eq₂]
  rw [colimitsmulColimit_rep_smul, colimitsmulColimit_rep_smul, colimitsmulColimit_rep_smul,
    smulColimit_add_smul]

@[simp]
lemma colimitsmulColimit_zero_smul (m : colimit (C := 𝔄𝔟) ℳ) :
    colimitsmulColimit (0 : colimit (C := ℜ𝔦𝔫𝔤) ℛ) m = 0 := by
  let c : J := (inferInstance : IsFiltered J).2.some
  rw [show (0 : colimit (C := ℜ𝔦𝔫𝔤) ℛ) = colimit.ι ℛ c 0 by rw [map_zero],
    colimitsmulColimit_rep_smul, smulColimit_zero_smul]

end colimitsmulColimit

noncomputable instance moduleColimitColimit :
    Module (colimit (C := ℜ𝔦𝔫𝔤) ℛ) (colimit (C := 𝔄𝔟) ℳ) where
  smul := colimitsmulColimit
  one_smul := colimitsmulColimit_one_smul _ _
  mul_smul := colimitsmulColimit_mul_smul _ _
  smul_zero := colimitsmulColimit_smul_zero _ _
  smul_add := colimitsmulColimit_smul_add _ _
  add_smul := colimitsmulColimit_add_smul _ _
  zero_smul := colimitsmulColimit_zero_smul _ _

lemma smul_spec
    (j₁ j₂ j₃ : J) (i₁ : j₁ ⟶ j₃) (i₂ : j₂ ⟶ j₃)
    (s : ℛ.obj j₁) (t : ℳ.obj j₂) :
    colimit.ι ℛ j₁ s • colimit.ι ℳ j₂ t = colimit.ι ℳ j₃ (ℛ.map i₁ s • ℳ.map i₂ t) :=
  show colimitsmulColimit _ _ = colimit.ι ℳ j₃ (ℛ.map i₁ s • ℳ.map i₂ t) by
    rw [colimitsmulColimit_rep_smul, smulColimit_smul_rep]
    apply hSMul_respect_ι <;> rfl

/--
an alternative to `Module.overFilteredColimits.smul_spec` that assumes the same index throughout.
-/
lemma smul_spec' {j : J} (s : ℛ.obj j) (t : ℳ.obj j) :
    colimit.ι ℛ j s • colimit.ι ℳ j t = colimit.ι ℳ j (s • t) := by
  simp only [smul_spec _ _ j j j (𝟙 _) (𝟙 _), CategoryTheory.Functor.map_id, id_apply]

end Module.overFilteredColimits

end module_over_filtered_colimit

end CategoryTheory.Limits.Concrete
