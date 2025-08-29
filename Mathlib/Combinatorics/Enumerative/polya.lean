import Mathlib.GroupTheory.GroupAction.Basic--
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Perm.Cycle.Basic--1
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.BigOperators.Fin

open MvPolynomial

open MulAction Finset Equiv BigOperators
section

namespace DistinctColorings

variable  { X Y : Type*}  [MulAction (Equiv.Perm X)  X]
variable [Fintype X] [Fintype Y]
variable (c : X → Y)
/-X：被着色的对象集合（如正方形的顶点、项链的珠子等）
  Y：颜色集合（如红、蓝、绿）-/

instance : MulAction (Equiv.Perm X) (X → Y) where
  smul g c := fun x ↦ c (g⁻¹ • x)
  one_smul := by
    intro c--单位元作用不变
    ext x
    simp [HSMul.hSMul]
    show c ((1 : (Equiv.Perm X) ) • x) = c x
    rw [one_smul (Equiv.Perm X)  x]
  mul_smul := by
    intro g g' f
    ext x
    simp [HSMul.hSMul]
    show f ((g'⁻¹ * g⁻¹) • x) = f (g'⁻¹ • (g⁻¹ • x))
    rw [mul_smul g'⁻¹ g⁻¹ x]


-- 主要定理：g • c = f • c ↔ f⁻¹ * g ∈ G(c)14.2.1
theorem smul_eq_iff_mem_stabilizer_conj (f g : (Equiv.Perm X) ) :
    g • c = f • c ↔ f⁻¹ * g ∈ MulAction.stabilizer (Equiv.Perm X)  c := by

  -- g • c = f • c ↔ (f⁻¹ * g) • c = c

  constructor
  intro h_eq
  simp [stabilizer]
 -- rw [MulAction.mul_smul, h_eq, ←MulAction.mul_smul]
  ext x
  simp only [MulAction.mul_smul]
  rw[h_eq]
  show c (f⁻¹ • (f • x)) = c x
  rw [inv_smul_smul]
  intro h
  simp only [stabilizer, Subgroup.mem_mk, Set.mem_setOf_eq] at h
  have : g = f * (f⁻¹ * g) := by group
  rw [this, mul_smul]
  rw [h]

def coloring_equiv (c₁ c₂ : X → Y) : Prop :=
  ∃ f : Equiv.Perm X, f • c₁ = c₂

-- 着色等价关系的性质（G 固定为 Equiv.Perm X）
theorem coloring_equiv_equivalence [Fintype X] [Fintype Y]:
    Equivalence (coloring_equiv (X := X) (Y := Y)) where
  refl c := ⟨1, by simp⟩
  symm  := by intro c₁ c₂ ⟨f, h⟩; use f⁻¹; rw [←h]; simp
  trans := by intro c₁ c₂ c₃ ⟨f, h₁⟩ ⟨g, h₂⟩; use g * f; rw [←h₂, ←h₁];exact mul_smul g f c₁

--推论14.2.2
instance : Group (Equiv.Perm X) := inferInstance


theorem orbit_size_eq_index (c : X → Y)[Fintype (Equiv.Perm X)]  [Fintype (MulAction.orbit (Equiv.Perm X) c)][Fintype (MulAction.stabilizer (Equiv.Perm X)  c)] :
  Fintype.card (MulAction.orbit (Equiv.Perm X) c) = Fintype.card (Equiv.Perm X) / Fintype.card (MulAction.stabilizer (Equiv.Perm X)  c) :=by


  have h :Fintype.card (MulAction.orbit (Equiv.Perm X) c)* Fintype.card (MulAction.stabilizer (Equiv.Perm X)  c) = Fintype.card (Equiv.Perm X) :=by



    rw[MulAction.card_orbit_mul_card_stabilizer_eq_card_group]
  have one_mem : (1 : Equiv.Perm X) ∈ MulAction.stabilizer (Equiv.Perm X) c := by
    simp [MulAction.stabilizer]
    exact
      Subgroup.one_mem
        { toSubmonoid := stabilizerSubmonoid (Perm X) c,
          inv_mem' :=
            @stabilizer._proof_38 (Perm X) (X → Y) instGroupPerm_my_idt
              instMulActionPermForall_my_idt c }
  have hb : 0 < Fintype.card (MulAction.stabilizer (Equiv.Perm X)  c) := by
    simpa using (Fintype.card_pos_iff.mpr ⟨1, one_mem⟩)
  -- 将 `0 < ...` 转为 `... ≠ 0`，然后使用 `Nat.mul_div_cancel_left`
  have : Fintype.card (Equiv.Perm X) / Fintype.card (MulAction.stabilizer (Equiv.Perm X)  c) =
             Fintype.card (MulAction.orbit (Equiv.Perm X) c) := by
    rw [← h]
    simp -- 把分子换成 orbit_card * stabilizer_card

  exact this.symm
