/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.CategoryTheory.Limits.ConcreteCategory
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

open CategoryTheory Category Limits Opposite

/-!
# Module structures of filtered colimits of abelian groups over filtered colimts of rings

Let `R` be the filtered colimit of rings `{Rⱼ}` and `M` be the filtered colimit of
abelian groups `{Mⱼ}`  with the same indexing set `j ∈ J`, if for each `j ∈ J`, `Mⱼ` is an `Rⱼ` such
that the `Rⱼ`-action is compatible, then `M` is an `Rⱼ`-module for all `j` and `M` is an `R`-module.

## Implementation notes

We choose not to use `PresheafOfModules` to avoid code duplication:
consider `R : J ⥤ CommRingCat` and `M : J ⥤ AddCommGrp`, then `colimit M` is both a
`colimit R`-module and a `colimt (R ⋙ forget₂ CommRingCat RingCat)`-module; the two module
structures are virtually the same. This situation manifests in stalks of sheaves of modules:
for any ringed space `X` and a sheaf of `𝒪_X`-module `ℳ`, we want to think the stalk `ℳₓ` as an
`𝒪_{X,x}`-module. But since `PresheafOfModules` requires a presheaf of `RingCat` not `CommRingCat`,
we need to compose the sheaf with forgetful functors, but we don't want to think about the
difference between `𝒪_{X, x}` as a colimit in `CommRing` and `𝒪_{X, x}` as a colimit in `RingCat`
all the time. So we ask `R` and `M` to be functors into concrete categories which behaves like rings
and abelian groups respectively.

-/

universe u u' v v' w

section

variable {J : Type w} [Category J] [IsFiltered J]
variable {ℜ𝔦𝔫𝔤 : Type u} [Category.{u'} ℜ𝔦𝔫𝔤] [ConcreteCategory.{w} ℜ𝔦𝔫𝔤]
variable {𝔄𝔟 : Type v} [Category.{v'} 𝔄𝔟] [ConcreteCategory.{w} 𝔄𝔟]

attribute [local instance] ConcreteCategory.hasCoeToSort
attribute [local instance] ConcreteCategory.instFunLike

variable [∀ x : ℜ𝔦𝔫𝔤, Semiring x] [∀ x : 𝔄𝔟, AddCommMonoid x]
variable [∀ x y : ℜ𝔦𝔫𝔤, RingHomClass (x ⟶ y) x y]
variable [∀ x y : 𝔄𝔟, AddMonoidHomClass (x ⟶ y) x y]

variable (ℛ : J ⥤ ℜ𝔦𝔫𝔤) (ℳ : J ⥤ 𝔄𝔟)
variable [HasColimit ℛ] [HasColimit ℳ]
variable [PreservesColimit ℛ (forget ℜ𝔦𝔫𝔤)] [PreservesColimit ℳ (forget 𝔄𝔟)]

variable [∀ c, Module (ℛ.obj c) (ℳ.obj c)]
variable [compatible_smul : Fact $ ∀ {c₁ c₂ : J} (i₁ : c₁ ⟶ c₂) (r : ℛ.obj c₁) (m : ℳ.obj c₁),
    ℳ.map i₁ (r • m) = ℛ.map i₁ r • ℳ.map i₁ m]

namespace Module.overFilteredColimits

variable {ℛ ℳ} in
/--
Let `R` be the filtered colimit of rings `{Rⱼ}` and `M` be the filtered colimit of
abelian groups `{Mⱼ}`  with the same indexing set `j ∈ J`, if for each `j ∈ J`, `Mⱼ` is an `Rⱼ` such
that the `Rⱼ`-action is compatible, then there is a heterogeneous scalar multiplication
`Rᵢ → Mⱼ → Mₖ` for every `i → j` and `i → k`.
-/
def hsmul {c₁ c₂ c₃ : J} (i₁ : c₁ ⟶ c₃) (i₂ : c₂ ⟶ c₃)
    (r : ℛ.obj c₁) (m : ℳ.obj c₂) : ℳ.obj c₃ :=
  (ℛ.map i₁ r) • (ℳ.map i₂ m)

namespace hsmul

variable {c₁ c₂ c₃ : J} (i₁ : c₁ ⟶ c₃) (i₂ : c₂ ⟶ c₃)
variable (r : ℛ.obj c₁) (m : ℳ.obj c₂)

protected lemma one_smul :
    hsmul i₁ i₂ (1 : ℛ.obj c₁) m = (ℳ.map i₂ m) := by
  simp [hsmul]

protected lemma mul_smul (r₁ r₂ : ℛ.obj c₁) : hsmul i₁ i₂ (r₁ * r₂) m =
    hsmul i₁ (𝟙 _) r₁ (hsmul i₁ i₂ r₂ m) := by
  simp only [hsmul, map_mul, mul_smul]
  erw [ℳ.map_id, id_apply]

protected lemma smul_zero : hsmul (ℳ := ℳ) i₁ i₂ r 0 = 0 := by
  simp [hsmul]

protected lemma smul_add (m₁ m₂ : ℳ.obj c₂) : hsmul i₁ i₂ r (m₁ + m₂) =
    hsmul i₁ i₂ r m₁ + hsmul i₁ i₂ r m₂ := by
  simp [hsmul, smul_add]

protected lemma add_smul (r₁ r₂ : ℛ.obj c₁) (m : ℳ.obj c₂) :
    hsmul i₁ i₂ (r₁ + r₂) m = hsmul i₁ i₂ r₁ m + hsmul i₁ i₂ r₂ m := by
  simp [hsmul, add_smul]

protected lemma zero_smul : hsmul i₁ i₂ (0 : ℛ.obj c₁) m = 0 := by
  simp [hsmul]

set_option maxHeartbeats 800000 in
lemma respect_ι
    {c₁ c₂ c₃ : J} (i₁ : c₁ ⟶ c₃) (i₂ : c₂ ⟶ c₃)
    (r : ℛ.obj c₁) (x : ℳ.obj c₂)
    {d₁ d₂ d₃ : J} (j₁ : d₁ ⟶ d₃) (j₂ :  d₂ ⟶ d₃)
    (r' : ℛ.obj d₁) (x' : ℳ.obj d₂)
    (hrr' : colimit.ι ℛ _ r = colimit.ι ℛ _ r')
    (hmm' : colimit.ι ℳ _ x = colimit.ι ℳ _ x') :
    colimit.ι ℳ _ (hsmul i₁ i₂ r x) =
    colimit.ι ℳ _ (hsmul j₁ j₂ r' x') := by
  classical
  obtain ⟨m, fm₁, fm₂, hm⟩ := Concrete.colimit_exists_of_rep_eq (h := hrr')
  obtain ⟨n, fn₁, fn₂, hn⟩ := Concrete.colimit_exists_of_rep_eq (h := hmm')
  erw [Concrete.colimit_rep_eq_iff_exists]
  delta hsmul
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
  erw [compatible_smul.out, compatible_smul.out]
  apply_fun ℛ.map (IsFiltered.toSup O H (by simp [O])) at hm
  rw [← comp_apply, ← comp_apply, ← ℛ.map_comp, ← ℛ.map_comp] at hm

  apply_fun ℳ.map (IsFiltered.toSup O H (by simp [O])) at hn
  rw [← comp_apply, ← comp_apply, ← ℳ.map_comp, ← ℳ.map_comp] at hn

  rw [← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply, ← ℛ.map_comp, ← ℛ.map_comp,
    ← ℳ.map_comp, ← ℳ.map_comp]
  convert congr($hm • $hn) using 1 <;> congr 3
  · erw [IsFiltered.toSup_commutes O H (f := i₁), IsFiltered.toSup_commutes O H (f := fm₁)] <;>
    simp [O, H]
  · erw [IsFiltered.toSup_commutes O H (f := i₂), IsFiltered.toSup_commutes O H (f := fn₁)] <;>
    simp [O, H]
  · erw [IsFiltered.toSup_commutes O H (f := j₁), IsFiltered.toSup_commutes O H (f := fm₂)] <;>
    simp [O, H]
  · erw [IsFiltered.toSup_commutes O H (f := j₂), IsFiltered.toSup_commutes O H (f := fn₂)] <;>
    simp [O, H]

end hsmul

variable {ℛ ℳ} in
/--
Let `R` be the filtered colimit of rings `{Rⱼ}` and `M` be the filtered colimit of
abelian groups `{Mⱼ}`  with the same indexing set `j ∈ J`, if for each `j ∈ J`, `Mⱼ` is an `Rⱼ` such
that the `Rⱼ`-action is compatible, then there is a scalar multiplication
`Rⱼ → M → M` for every `j ∈ J`.
-/
noncomputable def smulColimit {c : J} (r : ℛ.obj c) (m : colimit (C := 𝔄𝔟) ℳ) :
    colimit (C := 𝔄𝔟) ℳ :=
  colimit.ι ℳ (IsFiltered.max c (Concrete.indexRepColimit ℳ m))
   (hsmul (IsFiltered.leftToMax _ _) (IsFiltered.rightToMax _ _)
    r (Concrete.repColimit ℳ m))

namespace smulColimit

lemma smul_rep (c₁ c₂ : J) (r : ℛ.obj c₁) (m : ℳ.obj c₂) :
    smulColimit r (colimit.ι ℳ c₂ m) =
    colimit.ι ℳ (IsFiltered.max c₁ c₂)
    (hsmul (IsFiltered.leftToMax _ _) (IsFiltered.rightToMax _ _) r m) := by
  delta smulColimit
  apply hsmul.respect_ι
  · rfl
  · erw [Concrete.ι_repColimit_eq]

protected lemma one_smul (c : J) (m : colimit (C := 𝔄𝔟) ℳ) :
    smulColimit (1 : ℛ.obj c) m = m := by
  rw [show m = colimit.ι ℳ (Concrete.indexRepColimit ℳ m) _ by
    erw [Concrete.ι_repColimit_eq], smul_rep, hsmul.one_smul]
  erw [colimit.w_apply]

protected lemma mul_smul (c : J) (r₁ r₂ : ℛ.obj c)
    (m : colimit (C := 𝔄𝔟) ℳ) :
    smulColimit (r₁ * r₂) m = smulColimit r₁ (smulColimit r₂ m) := by
  rw [show m = colimit.ι ℳ (Concrete.indexRepColimit ℳ m) _ by
    erw [Concrete.ι_repColimit_eq], smul_rep, hsmul.mul_smul, smul_rep, smul_rep]
  apply hsmul.respect_ι
  · rfl
  · apply hsmul.respect_ι
    · rfl
    · erw [Concrete.ι_repColimit_eq]

lemma smul_zero (c : J) (r : ℛ.obj c) : smulColimit (ℳ := ℳ) r 0 = 0 := by
  rw [show (0 : colimit (C := 𝔄𝔟) ℳ) = colimit.ι (C := 𝔄𝔟) ℳ c 0 by rw [map_zero],
    smul_rep, hsmul.smul_zero, map_zero, map_zero]

lemma smul_add (c : J) (r : ℛ.obj c) (m₁ m₂ : colimit (C := 𝔄𝔟) ℳ) :
    smulColimit r (m₁ + m₂) = smulColimit r m₁ + smulColimit r m₂ := by
  classical
  let O : Finset J :=
    { c, Concrete.indexRepColimit ℳ m₁, Concrete.indexRepColimit ℳ m₂ }
  let H : Finset ((X : J) ×' (Y : J) ×' (_ : X ∈ O) ×' (_ : Y ∈ O) ×' (X ⟶ Y)) := {}
  let j : J := IsFiltered.sup O H

  have eq₁ : m₁ = colimit.ι ℳ j
      (ℳ.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit ℳ m₁)) := by
    erw [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₂ : m₂ = colimit.ι ℳ j
      (ℳ.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit ℳ m₂)) := by
    erw [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₃ : m₁ + m₂ = colimit.ι ℳ j
      (ℳ.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit ℳ m₁) +
       ℳ.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit ℳ m₂)) := by
    rw [map_add]
    erw [colimit.w_apply, colimit.w_apply, Concrete.ι_repColimit_eq, Concrete.ι_repColimit_eq]

  rw [eq₃]
  conv_rhs => rw [eq₁]; rhs; rw [eq₂]
  rw [smul_rep, smul_rep, smul_rep, hsmul.smul_add, map_add]

lemma add_smul (c : J) (r₁ r₂ : ℛ.obj c) (m : colimit (C := 𝔄𝔟) ℳ) :
    smulColimit (r₁ + r₂) m = smulColimit r₁ m + smulColimit r₂ m := by
  rw [show m = colimit.ι ℳ (Concrete.indexRepColimit ℳ m) _ by
    erw [Concrete.ι_repColimit_eq], smul_rep, hsmul.add_smul, smul_rep, smul_rep, map_add]

lemma zero_smul (c : J) (m : colimit (C := 𝔄𝔟) ℳ) :
    smulColimit (ℳ := ℳ) (0 : ℛ.obj c) m = 0 := by
  rw [show m = colimit.ι ℳ (Concrete.indexRepColimit ℳ m) _ by
    erw [Concrete.ι_repColimit_eq], smul_rep, hsmul.zero_smul, map_zero]

end smulColimit

noncomputable instance moduleObjColimit (j : J) :
    Module (ℛ.obj j) (colimit (C := 𝔄𝔟) ℳ) where
  smul := smulColimit
  one_smul := smulColimit.one_smul _ _ _
  mul_smul := smulColimit.mul_smul _ _ _
  smul_zero := smulColimit.smul_zero _ _ _
  smul_add := smulColimit.smul_add _ _ _
  add_smul := smulColimit.add_smul _ _ _
  zero_smul := smulColimit.zero_smul _ _ _

variable {ℛ ℳ} in
/--
Let `R` be the filtered colimit of rings `{Rⱼ}` and `M` be the filtered colimit of
abelian groups `{Mⱼ}`  with the same indexing set `j ∈ J`, if for each `j ∈ J`, `Mⱼ` is an `Rⱼ` such
that the `Rⱼ`-action is compatible, then there is a scalar multiplication
`R → M → M`.
-/
noncomputable def colimitSMulColimit (r : colimit (C := ℜ𝔦𝔫𝔤) ℛ) (m : colimit (C := 𝔄𝔟) ℳ) :
    colimit (C := 𝔄𝔟) ℳ :=
  (smulColimit (Concrete.repColimit ℛ r) m)

namespace colimitSMulColimit

lemma rep_smul {c : J} (r : ℛ.obj c) (m : colimit (C := 𝔄𝔟) ℳ) :
    colimitSMulColimit (colimit.ι ℛ c r) m = smulColimit r m := by
  delta colimitSMulColimit
  rw [show m = colimit.ι ℳ (Concrete.indexRepColimit ℳ m) _ by
    erw [Concrete.ι_repColimit_eq], smulColimit.smul_rep]
  apply hsmul.respect_ι
  · erw [Concrete.ι_repColimit_eq]
  · erw [Concrete.ι_repColimit_eq, Concrete.ι_repColimit_eq]

protected lemma one_smul (m : colimit (C := 𝔄𝔟) ℳ) :
    colimitSMulColimit (1 : colimit (C := ℜ𝔦𝔫𝔤) ℛ) m = m := by
  let c : J := (inferInstance : IsFiltered J).2.some
  rw [show (1 : colimit (C := ℜ𝔦𝔫𝔤) ℛ) = colimit.ι ℛ c 1 by
    rw [map_one], rep_smul, smulColimit.one_smul]

protected lemma mul_smul
      (r₁ r₂ : colimit (C := ℜ𝔦𝔫𝔤) ℛ) (m : colimit (C := 𝔄𝔟) ℳ) :
    colimitSMulColimit (r₁ * r₂) m = colimitSMulColimit r₁ (colimitSMulColimit r₂ m) := by
  classical
  let O : Finset J :=
    {  Concrete.indexRepColimit ℛ r₁, Concrete.indexRepColimit ℛ r₂ }
  let H : Finset ((X : J) ×' (Y : J) ×' (_ : X ∈ O) ×' (_ : Y ∈ O) ×' (X ⟶ Y)) := {}
  let j : J := IsFiltered.sup O H
  have eq₁ : r₁ = colimit.ι ℛ j
      (ℛ.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit ℛ r₁)) := by
    erw [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₂ : r₂ = colimit.ι ℛ j
      (ℛ.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit ℛ r₂)) := by
    erw [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₃ : r₁ * r₂ = colimit.ι ℛ j
      (ℛ.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit ℛ r₁) *
       ℛ.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit ℛ r₂)) := by
    rw [map_mul]
    erw [colimit.w_apply, colimit.w_apply, Concrete.ι_repColimit_eq, Concrete.ι_repColimit_eq]
  rw [eq₃]
  conv_rhs => rw [eq₁]; rhs; rw [eq₂]
  rw [rep_smul, rep_smul, rep_smul, smulColimit.mul_smul]

lemma smul_zero (r : colimit (C := ℜ𝔦𝔫𝔤) ℛ) : colimitSMulColimit (ℳ := ℳ) r 0 = 0 := by
  rw [show r = colimit.ι ℛ (Concrete.indexRepColimit ℛ r) _ by
    erw [Concrete.ι_repColimit_eq], rep_smul, smulColimit.smul_zero]

lemma smul_add (r : colimit (C := ℜ𝔦𝔫𝔤) ℛ) (m₁ m₂ : colimit (C := 𝔄𝔟) ℳ) :
    colimitSMulColimit r (m₁ + m₂) = colimitSMulColimit r m₁ + colimitSMulColimit r m₂ := by
  rw [show r = colimit.ι ℛ (Concrete.indexRepColimit ℛ r) _ by
    erw [Concrete.ι_repColimit_eq], rep_smul, rep_smul, rep_smul, smulColimit.smul_add]

lemma add_smul (r₁ r₂ : colimit (C := ℜ𝔦𝔫𝔤) ℛ) (m : colimit (C := 𝔄𝔟) ℳ) :
    colimitSMulColimit (r₁ + r₂) m = colimitSMulColimit r₁ m + colimitSMulColimit r₂ m := by
  classical
  let O : Finset J :=
    {  Concrete.indexRepColimit ℛ r₁, Concrete.indexRepColimit ℛ r₂ }
  let H : Finset ((X : J) ×' (Y : J) ×' (_ : X ∈ O) ×' (_ : Y ∈ O) ×' (X ⟶ Y)) := {}
  let j : J := IsFiltered.sup O H
  have eq₁ : r₁ = colimit.ι ℛ j
      (ℛ.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit ℛ r₁)) := by
    erw [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₂ : r₂ = colimit.ι ℛ j
      (ℛ.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit ℛ r₂)) := by
    erw [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₃ : r₁ + r₂ = colimit.ι ℛ j
      (ℛ.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit ℛ r₁) +
       ℛ.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit ℛ r₂)) := by
    rw [map_add]
    erw [colimit.w_apply, colimit.w_apply, Concrete.ι_repColimit_eq, Concrete.ι_repColimit_eq]
  rw [eq₃]
  conv_rhs => rw [eq₁]; rhs; rw [eq₂]
  rw [rep_smul, rep_smul, rep_smul, smulColimit.add_smul]

lemma zero_smul (m : colimit (C := 𝔄𝔟) ℳ) :
    colimitSMulColimit (0 : colimit (C := ℜ𝔦𝔫𝔤) ℛ) m = 0 := by
  let c : J := (inferInstance : IsFiltered J).2.some
  rw [show (0 : colimit (C := ℜ𝔦𝔫𝔤) ℛ) = colimit.ι ℛ c 0 by rw [map_zero], rep_smul,
    smulColimit.zero_smul]

end colimitSMulColimit

noncomputable instance moduleColimitColimit :
    Module (colimit (C := ℜ𝔦𝔫𝔤) ℛ) (colimit (C := 𝔄𝔟) ℳ) where
  smul := colimitSMulColimit
  one_smul := colimitSMulColimit.one_smul _ _
  mul_smul := colimitSMulColimit.mul_smul _ _
  smul_zero := colimitSMulColimit.smul_zero _ _
  smul_add := colimitSMulColimit.smul_add _ _
  add_smul := colimitSMulColimit.add_smul _ _
  zero_smul := colimitSMulColimit.zero_smul _ _

lemma smul_spec
    (r : colimit (C := ℜ𝔦𝔫𝔤) ℛ) (m : colimit (C := 𝔄𝔟) ℳ)
    (j₁ j₂ j₃ : J) (i₁ : j₁ ⟶ j₃) (i₂ : j₂ ⟶ j₃)
    (s : ℛ.obj j₁) (t : ℳ.obj j₂)
    (h₁ : colimit.ι ℛ j₁ s = r) (h₂ : colimit.ι ℳ j₂ t = m) :
    r • m = colimit.ι ℳ j₃ (ℛ.map i₁ s • ℳ.map i₂ t) :=
  show colimitSMulColimit r m = colimit.ι ℳ j₃ (ℛ.map i₁ s • ℳ.map i₂ t) by
    rw [← h₁, ← h₂]
    rw [colimitSMulColimit.rep_smul, smulColimit.smul_rep]
    apply hsmul.respect_ι <;> rfl

end Module.overFilteredColimits
