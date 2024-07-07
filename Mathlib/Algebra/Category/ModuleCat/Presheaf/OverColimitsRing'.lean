import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.CategoryTheory.Limits.ConcreteCategory

open CategoryTheory Category Limits Opposite

universe u v

section


variable {C : Type u} [Category.{u} C] [IsCofiltered C]
variable {ring : Type u} [Category.{u+1} ring] [ConcreteCategory.{u+1} ring]
variable {ab : Type u} [Category.{u+1} ab] [ConcreteCategory.{u+1} ab]
attribute [local instance] ConcreteCategory.hasCoeToSort
attribute [local instance] ConcreteCategory.instFunLike

variable [∀ x : ring, Ring x] [∀ x : ab, AddCommGroup x]
variable [∀ x y : ring, RingHomClass (x ⟶ y) x y]
variable [∀ x y : ab, AddMonoidHomClass (x ⟶ y) x y]
variable (R : Cᵒᵖ ⥤ ring) (M : Cᵒᵖ ⥤ ab)
variable [HasColimit R] [HasColimit M]
variable [PreservesColimit R (forget ring)] [PreservesColimit M (forget ab)]
variable [∀ c, Module (R.obj c) (M.obj c)]
variable (compatible_smul : ∀ {c₁ c₂ : Cᵒᵖ} (i₁ : c₁ ⟶ c₂) (r : R.obj $ c₁) (m : M.obj $ c₁),
    M.map i₁ (r • m) = R.map i₁ r • M.map i₁ m)

namespace Module.overColimits

variable {R M} in

def hsmul {c₁ c₂ c₃ : C} (i₁ : c₃ ⟶ c₁) (i₂ : c₃ ⟶ c₂)
    (r : R.obj $ op c₁) (m : M.obj $ op c₂) : M.obj $ op c₃ :=
  (R.map (op i₁) r) • (M.map (op i₂) m)

namespace hsmul

variable {c₁ c₂ c₃ : C} (i₁ : c₃ ⟶ c₁) (i₂ : c₃ ⟶ c₂)
variable (r : R.obj $ op c₁) (m : M.obj $ op c₂)

protected lemma one_smul :
    hsmul i₁ i₂ (1 : R.obj $ op c₁) m = (M.map (op i₂) m) := by
  simp [hsmul]

protected lemma mul_smul (r₁ r₂ : R.obj $ op c₁) : hsmul i₁ i₂ (r₁ * r₂) m =
    hsmul i₁ (𝟙 _) r₁ (hsmul i₁ i₂ r₂ m) := by
  simp only [hsmul, map_mul, mul_smul]
  erw [M.map_id, id_apply]

protected lemma smul_zero : hsmul (M := M) i₁ i₂ r 0 = 0 := by
  simp [hsmul]

protected lemma smul_add (m₁ m₂ : M.obj $ op c₂) : hsmul i₁ i₂ r (m₁ + m₂) =
    hsmul i₁ i₂ r m₁ + hsmul i₁ i₂ r m₂ := by
  simp [hsmul]

protected lemma add_smul (r₁ r₂ : R.obj $ op c₁) (m : M.obj $ op c₂) :
    hsmul i₁ i₂ (r₁ + r₂) m = hsmul i₁ i₂ r₁ m + hsmul i₁ i₂ r₂ m := by
  simp [hsmul, add_smul]

protected lemma zero_smul : hsmul i₁ i₂ (0 : R.obj $ op c₁) m = 0 := by
  simp [hsmul]

set_option maxHeartbeats 500000 in
lemma respect_ι
    {c₁ c₂ c₃ : C} (i₁ : c₃ ⟶ c₁) (i₂ : c₃ ⟶ c₂)
    (r : R.obj $ op c₁) (x : M.obj $ op c₂)
    {d₁ d₂ d₃ : C} (j₁ : d₃ ⟶ d₁) (j₂ : d₃ ⟶ d₂)
    (r' : R.obj $ op d₁) (x' : M.obj $ op d₂)
    (hrr' : colimit.ι R _ r = colimit.ι R _ r')
    (hmm' : colimit.ι M _ x = colimit.ι M _ x') :
    colimit.ι M _ (hsmul i₁ i₂ r x) =
    colimit.ι M _ (hsmul j₁ j₂ r' x') := by
  classical
  obtain ⟨m, fm₁, fm₂, hm⟩ := Concrete.colimit_exists_of_rep_eq.{u+1} (h := hrr')
  obtain ⟨n, fn₁, fn₂, hn⟩ := Concrete.colimit_exists_of_rep_eq.{u+1} (h := hmm')
  erw [Concrete.colimit_rep_eq_iff_exists.{u+1}]
  delta hsmul
  let O : Finset Cᵒᵖ := { op c₁, op c₂, op c₃, op d₁, op d₂, op d₃, m, n }
  let H : Finset ((X : Cᵒᵖ) ×' (Y : Cᵒᵖ) ×' (_ : X ∈ O) ×' (_ : Y ∈ O) ×' (X ⟶ Y)) :=
  { ⟨op c₁, m, by simp [O], by simp [O], fm₁⟩,
    ⟨op d₁, m, by simp [O], by simp [O], fm₂⟩,
    ⟨op c₂, n, by simp [O], by simp [O], fn₁⟩,
    ⟨op d₂, n, by simp [O], by simp [O], fn₂⟩,
    ⟨op c₁, op c₃, by simp [O], by simp [O], i₁.op⟩,
    ⟨op c₂, op c₃, by simp [O], by simp [O], i₂.op⟩,
    ⟨op d₁, op d₃, by simp [O], by simp [O], j₁.op⟩,
    ⟨op d₂, op d₃, by simp [O], by simp [O], j₂.op⟩ }

  let S := IsFiltered.sup O H

  refine ⟨S, IsFiltered.toSup O H (by simp [O]), IsFiltered.toSup _ _ (by simp [O]), ?_⟩
  erw [compatible_smul, compatible_smul]
  apply_fun R.map (IsFiltered.toSup O H (by simp [O])) at hm
  rw [← comp_apply, ← comp_apply, ← R.map_comp, ← R.map_comp] at hm

  apply_fun M.map (IsFiltered.toSup O H (by simp [O])) at hn
  rw [← comp_apply, ← comp_apply, ← M.map_comp, ← M.map_comp] at hn

  rw [← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply, ← R.map_comp, ← R.map_comp,
    ← M.map_comp, ← M.map_comp]
  convert congr($hm • $hn) using 1 <;> congr 3
  · erw [IsFiltered.toSup_commutes O H (f := i₁.op), IsFiltered.toSup_commutes O H (f := fm₁)]
  · erw [IsFiltered.toSup_commutes O H (f := i₂.op), IsFiltered.toSup_commutes O H (f := fn₁)]
  · erw [IsFiltered.toSup_commutes O H (f := j₁.op), IsFiltered.toSup_commutes O H (f := fm₂)]
  · erw [IsFiltered.toSup_commutes O H (f := j₂.op), IsFiltered.toSup_commutes O H (f := fn₂)]

end hsmul

variable {R M} in
noncomputable def smulColimit {c : Cᵒᵖ} (r : R.obj c) (m : colimit (C := ab) M) :
    colimit (C := ab) M :=
  colimit.ι M (IsFiltered.max c (Concrete.indexRepColimit M m))
   (hsmul (IsFiltered.leftToMax _ _).unop (IsFiltered.rightToMax _ _).unop
    r (Concrete.repColimit M m))

namespace smulColimit

lemma smul_rep (c₁ c₂ : Cᵒᵖ) (r : R.obj c₁) (m : M.obj c₂) :
    smulColimit r (colimit.ι M c₂ m) =
    colimit.ι M (IsFiltered.max c₁ c₂)
    (hsmul (IsFiltered.leftToMax _ _).unop (IsFiltered.rightToMax _ _).unop r m) := by
  delta smulColimit
  apply hsmul.respect_ι
  · assumption
  · rfl
  · erw [Concrete.ι_repColimit_eq]

protected lemma one_smul (c : Cᵒᵖ) (m : colimit (C := ab) M) :
    smulColimit (1 : R.obj c) m = m := by
  rw [show m = colimit.ι M (Concrete.indexRepColimit M m) _ by
    erw [Concrete.ι_repColimit_eq], smul_rep, hsmul.one_smul]
  pick_goal 2
  · assumption
  erw [colimit.w_apply]

protected lemma mul_smul (c : Cᵒᵖ) (r₁ r₂ : R.obj c)
    (m : colimit (C := ab) M) :
    smulColimit (r₁ * r₂) m = smulColimit r₁ (smulColimit r₂ m) := by
  rw [show m = colimit.ι M (Concrete.indexRepColimit M m) _ by
    erw [Concrete.ι_repColimit_eq], smul_rep, hsmul.mul_smul, smul_rep, smul_rep]
  <;> try assumption
  apply hsmul.respect_ι
  · assumption
  · rfl
  · apply hsmul.respect_ι
    · assumption
    · rfl
    · erw [Concrete.ι_repColimit_eq]

lemma smul_zero (c : Cᵒᵖ) (r : R.obj c) : smulColimit (M := M) r 0 = 0 := by
  rwa [show (0 : colimit (C := ab) M) = colimit.ι (C := ab) M c 0 by rw [map_zero],
    smul_rep, hsmul.smul_zero, map_zero, map_zero]

lemma smul_add (c : Cᵒᵖ) (r : R.obj c) (m₁ m₂ : colimit (C := ab) M) :
    smulColimit r (m₁ + m₂) = smulColimit r m₁ + smulColimit r m₂ := by
  classical
  let O : Finset Cᵒᵖ :=
    { c, Concrete.indexRepColimit M m₁, Concrete.indexRepColimit M m₂ }
  let H : Finset ((X : Cᵒᵖ) ×' (Y : Cᵒᵖ) ×' (_ : X ∈ O) ×' (_ : Y ∈ O) ×' (X ⟶ Y)) := {}
  let j : Cᵒᵖ := IsFiltered.sup O H

  have eq₁ : m₁ = colimit.ι M j
      (M.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit M m₁)) := by
    erw [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₂ : m₂ = colimit.ι M j
      (M.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit M m₂)) := by
    erw [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₃ : m₁ + m₂ = colimit.ι M j
      (M.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit M m₁) +
       M.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit M m₂)) := by
    rw [map_add]
    erw [colimit.w_apply, colimit.w_apply, Concrete.ι_repColimit_eq, Concrete.ι_repColimit_eq]

  rw [eq₃]
  conv_rhs => rw [eq₁]; rhs; rw [eq₂]
  rw [smul_rep, smul_rep, smul_rep, hsmul.smul_add, map_add] <;> assumption

lemma add_smul (c : Cᵒᵖ) (r₁ r₂ : R.obj c) (m : colimit (C := ab) M) :
    smulColimit (r₁ + r₂) m = smulColimit r₁ m + smulColimit r₂ m := by
  rw [show m = colimit.ι M (Concrete.indexRepColimit M m) _ by
    erw [Concrete.ι_repColimit_eq], smul_rep, hsmul.add_smul, smul_rep, smul_rep, map_add] <;>
  assumption

lemma zero_smul (c : Cᵒᵖ) (m : colimit (C := ab) M) :
    smulColimit (M := M) (0 : R.obj c) m = 0 := by
  rw [show m = colimit.ι M (Concrete.indexRepColimit M m) _ by
    erw [Concrete.ι_repColimit_eq], smul_rep, hsmul.zero_smul, map_zero] <;>
  assumption

end smulColimit

noncomputable instance moduleObjColimit (j : Cᵒᵖ) :
    Module (R.obj j) (colimit (C := ab) M) where
  smul := smulColimit
  one_smul := smulColimit.one_smul _ _ compatible_smul _
  mul_smul := smulColimit.mul_smul _ _ compatible_smul _
  smul_zero := smulColimit.smul_zero _ _ compatible_smul _
  smul_add := smulColimit.smul_add _ _ compatible_smul _
  add_smul := smulColimit.add_smul _ _ compatible_smul _
  zero_smul := smulColimit.zero_smul _ _ compatible_smul _

variable {R M} in
noncomputable def colimitSMulColimit (r : colimit (C := ring) R) (m : colimit (C := ab) M) :
    colimit (C := ab) M :=
  (smulColimit (Concrete.repColimit R r) m)

namespace colimitSMulColimit

lemma rep_smul {c : Cᵒᵖ} (r : R.obj c) (m : colimit (C := ab) M) :
    colimitSMulColimit (colimit.ι R c r) m = smulColimit r m := by
  delta colimitSMulColimit
  rw [show m = colimit.ι M (Concrete.indexRepColimit M m) _ by
    erw [Concrete.ι_repColimit_eq], smulColimit.smul_rep] <;>
  try assumption
  apply hsmul.respect_ι
  · assumption
  · erw [Concrete.ι_repColimit_eq]
  · erw [Concrete.ι_repColimit_eq, Concrete.ι_repColimit_eq]

protected lemma one_smul (m : colimit (C := ab) M) :
    colimitSMulColimit (1 : colimit (C := ring) R) m = m := by
  let c : Cᵒᵖ := (inferInstance : IsFiltered Cᵒᵖ).2.some
  rw [show (1 : colimit (C := ring) R) = colimit.ι R c 1 by
    rw [map_one], rep_smul, smulColimit.one_smul] <;>
  assumption

protected lemma mul_smul
      (r₁ r₂ : colimit (C := ring) R) (m : colimit (C := ab) M) :
    colimitSMulColimit (r₁ * r₂) m = colimitSMulColimit r₁ (colimitSMulColimit r₂ m) := by
  classical
  let O : Finset Cᵒᵖ :=
    {  Concrete.indexRepColimit R r₁, Concrete.indexRepColimit R r₂ }
  let H : Finset ((X : Cᵒᵖ) ×' (Y : Cᵒᵖ) ×' (_ : X ∈ O) ×' (_ : Y ∈ O) ×' (X ⟶ Y)) := {}
  let j : Cᵒᵖ := IsFiltered.sup O H
  have eq₁ : r₁ = colimit.ι R j
      (R.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit R r₁)) := by
    erw [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₂ : r₂ = colimit.ι R j
      (R.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit R r₂)) := by
    erw [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₃ : r₁ * r₂ = colimit.ι R j
      (R.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit R r₁) *
       R.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit R r₂)) := by
    rw [map_mul]
    erw [colimit.w_apply, colimit.w_apply, Concrete.ι_repColimit_eq, Concrete.ι_repColimit_eq]
  rw [eq₃]
  conv_rhs => rw [eq₁]; rhs; rw [eq₂]
  rw [rep_smul, rep_smul, rep_smul, smulColimit.mul_smul]

lemma smul_zero (r : colimit (C := ring) R) : colimitSMulColimit (M := M) r 0 = 0 := by
  rw [show r = colimit.ι R (Concrete.indexRepColimit R r) _ by
    erw [Concrete.ι_repColimit_eq], rep_smul, smulColimit.smul_zero] <;> assumption

lemma smul_add (r : colimit (C := ring) R) (m₁ m₂ : colimit (C := ab) M) :
    colimitSMulColimit r (m₁ + m₂) = colimitSMulColimit r m₁ + colimitSMulColimit r m₂ := by
  rw [show r = colimit.ι R (Concrete.indexRepColimit R r) _ by
    erw [Concrete.ι_repColimit_eq], rep_smul, rep_smul, rep_smul, smulColimit.smul_add] <;>
  assumption

lemma add_smul (r₁ r₂ : colimit (C := ring) R) (m : colimit (C := ab) M) :
    colimitSMulColimit (r₁ + r₂) m = colimitSMulColimit r₁ m + colimitSMulColimit r₂ m := by
  classical
  let O : Finset Cᵒᵖ :=
    {  Concrete.indexRepColimit R r₁, Concrete.indexRepColimit R r₂ }
  let H : Finset ((X : Cᵒᵖ) ×' (Y : Cᵒᵖ) ×' (_ : X ∈ O) ×' (_ : Y ∈ O) ×' (X ⟶ Y)) := {}
  let j : Cᵒᵖ := IsFiltered.sup O H
  have eq₁ : r₁ = colimit.ι R j
      (R.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit R r₁)) := by
    erw [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₂ : r₂ = colimit.ι R j
      (R.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit R r₂)) := by
    erw [colimit.w_apply, Concrete.ι_repColimit_eq]
  have eq₃ : r₁ + r₂ = colimit.ι R j
      (R.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit R r₁) +
       R.map (IsFiltered.toSup O H $ by simp [O]) (Concrete.repColimit R r₂)) := by
    rw [map_add]
    erw [colimit.w_apply, colimit.w_apply, Concrete.ι_repColimit_eq, Concrete.ι_repColimit_eq]
  rw [eq₃]
  conv_rhs => rw [eq₁]; rhs; rw [eq₂]
  rw [rep_smul, rep_smul, rep_smul, smulColimit.add_smul] <;>
  assumption

lemma zero_smul (m : colimit (C := ab) M) :
    colimitSMulColimit (0 : colimit (C := ring) R) m = 0 := by
  let c : Cᵒᵖ := (inferInstance : IsFiltered Cᵒᵖ).2.some
  rw [show (0 : colimit (C := ring) R) = colimit.ι R c 0 by rw [map_zero], rep_smul,
    smulColimit.zero_smul] <;> assumption

end colimitSMulColimit

noncomputable instance : Module (colimit (C := ring) R) (colimit (C := ab) M) where
  smul := colimitSMulColimit
  one_smul := colimitSMulColimit.one_smul _ _ compatible_smul
  mul_smul := colimitSMulColimit.mul_smul _ _ compatible_smul
  smul_zero := colimitSMulColimit.smul_zero _ _ compatible_smul
  smul_add := colimitSMulColimit.smul_add _ _ compatible_smul
  add_smul := colimitSMulColimit.add_smul _ _ compatible_smul
  zero_smul := colimitSMulColimit.zero_smul _ _ compatible_smul

end Module.overColimits
