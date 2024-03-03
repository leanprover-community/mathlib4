import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.TensorProduct

open TensorProduct FreeAddMonoid

universe u v

variable {R : Type u} {M N : Type*}
  [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

namespace TensorProduct

section mem_FG

theorem mem_of_fg_freeAddMonoid (x : FreeAddMonoid (M × N)) :
    ∃ (M' : Submodule R M), Submodule.FG M' ∧
      ∃ (N' : Submodule R N), Submodule.FG N' ∧
        ∃ x' : FreeAddMonoid (M' × N'),
          x = FreeAddMonoid.map (Prod.map (M'.subtype) (N'.subtype)) x' := by
  induction x using FreeAddMonoid.recOn with
  | h0 =>
    use ⊥, Submodule.fg_bot, ⊥, Submodule.fg_bot, 0
    simp
  | ih x y ih =>
    obtain ⟨M', hM', N', hN', y', rfl⟩ := ih
    rcases x with ⟨m, n⟩
    let M'₁ := Submodule.span R {m} ⊔ M'
    let N'₁ := Submodule.span R {n} ⊔ N'
    use M'₁, Submodule.FG.sup (Submodule.fg_span_singleton m) hM'
    use N'₁, Submodule.FG.sup (Submodule.fg_span_singleton n) hN'
    let m' := (⟨m, le_sup_left (b := M') (Submodule.mem_span_singleton_self m)⟩ : M'₁)
    let n' := (⟨n, le_sup_left (b := N') (Submodule.mem_span_singleton_self n)⟩ : N'₁)
    use FreeAddMonoid.of (m', n') +
      FreeAddMonoid.map
        (Prod.map
          (Submodule.inclusion (le_sup_right (a := Submodule.span R {m})))
          (Submodule.inclusion (le_sup_right (a := Submodule.span R {n})))) y'
    simp only [map_add, FreeAddMonoid.map_of, Prod_map, add_right_inj]
    simp only [← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp]
    simp only [Prod.map_comp_map]
    simp only [← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
    exact rfl

lemma addCon_map_eq_map_addCon
    {R : Type*} [CommSemiring R]
    {M N M' N' : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M'] [AddCommMonoid N']
    [Module R M] [Module R N] [Module R M'] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (sx : FreeAddMonoid (M × N)) :
    (AddCon.mk' (addConGen (TensorProduct.Eqv R M' N'))
      (FreeAddMonoid.map (Prod.map f g) sx) : TensorProduct R M' N')
      = TensorProduct.map f g (AddCon.mk' (addConGen (TensorProduct.Eqv R M N)) sx : TensorProduct R M N) := by
  induction sx using FreeAddMonoid.recOn with
  | h0 => simp only [_root_.map_zero]
  | ih x y ih =>
    simp only [AddCon.coe_mk'] at ih
    simp only [map_add, FreeAddMonoid.map_of, Prod_map, AddCon.coe_mk', ih]
    apply congr_arg₂ _ _ rfl
    rfl


-- Redo by just using FreeAddMonoid (induction already done)
def mem_map_subtype_of_exists_FG (x : M ⊗[R] N) :
    ∃ M₀, Submodule.FG M₀ ∧ ∃ N₀, Submodule.FG N₀ ∧
    x ∈ LinearMap.range
        (TensorProduct.map (Submodule.subtype M₀) (Submodule.subtype N₀)) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    use ⊥, Submodule.fg_bot, ⊥, Submodule.fg_bot
    apply zero_mem
  | tmul m n =>
    use Submodule.span R {m}, Submodule.fg_span_singleton m
    use Submodule.span R {n}, Submodule.fg_span_singleton n
    use ⟨m, Submodule.mem_span_singleton_self m⟩ ⊗ₜ ⟨n, Submodule.mem_span_singleton_self n⟩
    simp only [map_tmul, Submodule.coeSubtype]
  | add t t' ht ht' =>
    obtain ⟨M₀, hM₀, N₀, hN₀, ht⟩ := ht
    obtain ⟨M'₀, hM'₀, N'₀, hN'₀, ht'⟩ := ht'
    use M₀ ⊔ M'₀, Submodule.FG.sup hM₀ hM'₀
    use N₀ ⊔ N'₀, Submodule.FG.sup hN₀ hN'₀
    apply add_mem
    · suffices h : LinearMap.range _ ≤ LinearMap.range _ by refine h ht
      simp only [← Submodule.subtype_comp_inclusion M₀ (M₀ ⊔ M'₀) le_sup_left]
      simp only [← Submodule.subtype_comp_inclusion N₀ (N₀ ⊔ N'₀) le_sup_left]
      rw [TensorProduct.map_comp]
      apply LinearMap.range_comp_le_range
    · suffices h : LinearMap.range _ ≤ LinearMap.range _ by refine h ht'
      simp only [← Submodule.subtype_comp_inclusion M'₀ (M₀ ⊔ M'₀) le_sup_right]
      simp only [← Submodule.subtype_comp_inclusion N'₀ (N₀ ⊔ N'₀) le_sup_right]
      rw [TensorProduct.map_comp]
      apply LinearMap.range_comp_le_range

def TensorProduct.le_map_subtype_of_exists_FG (P : Submodule R (M ⊗[R] N)) (hP : Submodule.FG P) :
    ∃ M₀, Submodule.FG M₀ ∧ ∃ N₀, Submodule.FG N₀ ∧
      P ≤ LinearMap.range
        (TensorProduct.map (Submodule.subtype M₀) (Submodule.subtype N₀)) := by
  apply Submodule.fg_induction _ _ _ _ _ P hP
  · intro x
    simp only [Submodule.span_singleton_le_iff_mem, LinearMap.mem_range]
    apply TensorProduct.mem_map_subtype_of_exists_FG
  · rintro P₁ P₂ ⟨M₁, hM₁, N₁, hN₁, hP₁⟩ ⟨M₂, hM₂, N₂, hN₂, hP₂⟩
    use M₁ ⊔ M₂, Submodule.FG.sup hM₁ hM₂
    use N₁ ⊔ N₂, Submodule.FG.sup hN₁ hN₂
    simp only [sup_le_iff]
    constructor
    · apply le_trans hP₁
      simp only [← Submodule.subtype_comp_inclusion M₁ (M₁ ⊔ M₂) le_sup_left]
      simp only [← Submodule.subtype_comp_inclusion N₁ (N₁ ⊔ N₂) le_sup_left]
      rw [TensorProduct.map_comp]
      apply LinearMap.range_comp_le_range
    · apply le_trans hP₂
      simp only [← Submodule.subtype_comp_inclusion M₂ (M₁ ⊔ M₂) le_sup_right]
      simp only [← Submodule.subtype_comp_inclusion N₂ (N₁ ⊔ N₂) le_sup_right]
      rw [TensorProduct.map_comp]
      apply LinearMap.range_comp_le_range

-- rTensor
-- lTensor
-- variant? : if the stuff lives somewhere, it can be defined there

end mem_FG

end TensorProduct

namespace List

def toProp {α : Type*} (p : α → Prop) (l : List α) : Prop :=
  match l with
  | nil => True
  | cons a l => p a ∧ (l.toProp p)

lemma toProp_nil {α : Type*} {p : α → Prop} :
    nil.toProp p = True := rfl

lemma toProp_cons {α : Type*} {p : α → Prop}
    {a : α} {l : List α} :
    (a :: l).toProp p ↔ (p a) ∧ (l.toProp p) := by
  simp only [toProp]

end List

namespace FreeAddMonoid

def toProp {α : Type*} (p : α → Prop) (x : FreeAddMonoid α) :
    Prop := by
  induction x using recOn with
  | h0 => exact True
  | ih a _ hx => exact (p a ∧ hx)

@[simp]
lemma toProp_zero {α : Type*} {p : α → Prop} :
    (0 : FreeAddMonoid α).toProp p = True := rfl

@[simp]
lemma toProp_of_add {α : Type*} {p : α → Prop}
    {a : α} {x : FreeAddMonoid α} :
    (of a + x).toProp p ↔ (p a) ∧ (x.toProp p) := by
  simp only [toProp, recOn_of_add]

@[simp]
lemma toProp_of {α : Type*} {p : α → Prop} {a : α}:
    (of a).toProp p ↔ p a := by
  rw [← add_zero (of a), toProp_of_add, toProp_zero, and_true]

@[simp]
lemma toProp_add_iff {α : Type*} (p : α → Prop)
    {x y : FreeAddMonoid α} :
    (x+y).toProp p ↔ (x.toProp p ∧ y.toProp p) := by
  constructor
  · intro h
    constructor
    · induction x using recOn generalizing y with
      | h0 => simp only [toProp_zero]
      | ih a x ih =>
        rw [add_assoc, toProp_of_add] at h
        rw [toProp_of_add]
        exact ⟨h.1, ih h.2⟩
    · induction x using recOn generalizing y with
      | h0 => simpa only [zero_add] using h
      | ih a x ih =>
        simp only [add_assoc, toProp_of_add] at h
        exact ih h.2
  · rintro ⟨hx, hy⟩
    induction x using recOn generalizing y with
    | h0 =>
      simp
      exact hy
    | ih a x ih =>
      rw [add_assoc, toProp_of_add]
      rw [toProp_of_add] at hx
      exact ⟨hx.1, ih hx.2 hy⟩

theorem toProp_imp {α : Type*} {p q : α → Prop} (hpq : ∀ {a}, p a → q a)
    {x : FreeAddMonoid α} (hx : x.toProp p) : x.toProp q := by
  induction x using recOn with
  | h0 => simp only [toProp_zero]
  | ih a x ih =>
    simp only [toProp_add_iff, toProp_of] at hx ⊢
    exact ⟨hpq hx.1, ih hx.2⟩

theorem toProp_iff {α : Type*} {p q : α → Prop} (hpq : ∀ {a}, p a ↔ q a)
    {x : FreeAddMonoid α} : x.toProp p ↔ x.toProp q :=
  ⟨toProp_imp hpq.mp, toProp_imp hpq.mpr⟩

end FreeAddMonoid

namespace Submodule

open FreeAddMonoid

example (M' : Submodule R M) (N' : Submodule R N) (x : FreeAddMonoid (M × N)) :
    x ∈ AddMonoidHom.mrange (FreeAddMonoid.map (Prod.map M'.subtype N'.subtype))
    ↔ ∀ p ∈ FreeAddMonoid.toList x, p.1 ∈ M' ∧ p.2 ∈ N' := by
  induction x using recOn with
  | h0 =>
    simp only [toList_zero, List.not_mem_nil,
      IsEmpty.forall_iff, Prod.forall, forall_const, iff_true, zero_mem]
  | ih p x ih =>
    simp only [toList_add, toList_of, List.singleton_append,
      List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨y', hy'⟩
      suffices ∃ q y, y' = of q + y by
        obtain ⟨q, y, rfl⟩ := this
        simp only [coeSubtype, map_add, map_of] at hy'
        sorry
      sorry
    · rintro ⟨hp, hx⟩
      apply add_mem
      · rw [AddMonoidHom.mem_mrange]
        use of ⟨⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩⟩
        simp only [coeSubtype, map_of, Prod_map, Prod.mk.eta]
      · simpa only [← ih] using hx


private def h (M' : Submodule R M) (N' : Submodule R N) : (M × N) → Prop :=
  fun ⟨m, n⟩ ↦ m ∈ M' ∧ n ∈ N'

private theorem h_mono {M' M'' : Submodule R M} {N' N'' : Submodule R N}
    (hM : M' ≤ M'') (hN : N' ≤ N'') {x : M × N} (hx : (h M' N') x) :
    h M'' N'' x := ⟨hM hx.1, hN hx.2⟩

theorem mem_mrange_of {M' : Submodule R M} {N' : Submodule R N}
    {x : FreeAddMonoid (M × N)} (hx : x.toProp (h M' N')) :
    x ∈ AddMonoidHom.mrange (FreeAddMonoid.map (Prod.map M'.subtype N'.subtype)) := by
  induction x using FreeAddMonoid.recOn with
  | h0 => apply zero_mem
  | ih a x ih =>
    rcases a with ⟨m, n⟩
    simp only [toProp_add_iff, toProp_of, h] at hx
    refine add_mem ?_ (ih hx.2)
    simp only [Submodule.coeSubtype, AddMonoidHom.mem_mrange]
    use of (⟨⟨m, hx.1.1⟩, ⟨n, hx.1.2⟩⟩ : M' × N')
    simp only [map_of, Prod_map]

theorem toProp_h_iff_mem_mrange {M' : Submodule R M} {N' : Submodule R N}
    {x : FreeAddMonoid (M × N)} :
    x.toProp (h M' N') ↔
      x ∈ AddMonoidHom.mrange
        (FreeAddMonoid.map (Prod.map M'.subtype N'.subtype)) := by
  constructor
  exact mem_mrange_of
  intro hx
  induction x using FreeAddMonoid.recOn with
  | h0 =>
    simp only [toProp_zero]
  | ih a x ih =>
    simp only [toProp_add_iff, toProp_of]
    simp only [Submodule.coeSubtype, AddMonoidHom.mem_mrange] at hx
    obtain ⟨y', hy'⟩ := hx
    suffices ∃ (a' : M' × N') (x' : FreeAddMonoid (M' × N')), of a' + x' = y' by
      obtain ⟨a', x', rfl⟩ := this
      simp only [map_add, map_of, Prod_map] at hy'
      rw [← toList.injective.eq_iff] at hy'
      simp only [toList_add, toList_of, List.singleton_append, List.cons.injEq,
        EmbeddingLike.apply_eq_iff_eq] at hy'
      constructor
      · rw [← hy'.1]
        exact ⟨Submodule.coe_mem a'.1, Submodule.coe_mem a'.2⟩
      · exact ih (Exists.intro x' hy'.2)
    induction y' using FreeAddMonoid.casesOn with
    | h0 =>
      rw [map_zero, ← toList.injective.eq_iff] at hy'
      simp only [toList_zero, toList_add, toList_of, List.singleton_append] at hy'
    | ih a' x' => use a', x'

theorem mem_of_exists_fg (x : FreeAddMonoid (M × N)) :
    ∃ (M' : Submodule R M), M'.FG ∧
      ∃ (N' : Submodule R N), N'.FG ∧
        x ∈ AddMonoidHom.mrange (FreeAddMonoid.map (Prod.map M'.subtype N'.subtype)) := by
  simp only [← toProp_h_iff_mem_mrange]
  induction x using FreeAddMonoid.recOn with
  | h0 =>
    use ⊥, Submodule.fg_bot
    use ⊥, Submodule.fg_bot
    simp only [toProp_zero]
  | ih a x ih =>
    rcases a with ⟨m, n⟩
    obtain ⟨M', hM', N', hN', ih⟩ := ih
    use M' ⊔ Submodule.span R {m},
      Submodule.FG.sup hM' (Submodule.fg_span_singleton m)
    use N' ⊔ Submodule.span R {n},
    Submodule.FG.sup hN' (Submodule.fg_span_singleton n)
    simp only [toProp_of_add]
    constructor
    · apply h_mono le_sup_right le_sup_right
      exact ⟨Submodule.mem_span_singleton_self m,
        Submodule.mem_span_singleton_self n⟩
    · exact toProp_imp (h_mono le_sup_left le_sup_left) ih

theorem FreeAddMonoid.of_add_neq_zero {α : Type*} (a : α) (x : FreeAddMonoid α) :
    ¬ (of a + x = 0) := by
  exact List.cons_ne_nil a x

theorem FreeAddMonoid.neq_zero_iff_exists {α : Type*} {x : FreeAddMonoid α} :
    ¬ (x = 0) ↔ ∃ a y, x = of a + y := by
  constructor
  · intro h
    obtain ⟨a, y, rfl⟩ := List.exists_cons_of_ne_nil h
    use a, y
    rfl
  · rintro ⟨a, y, rfl⟩
    apply List.cons_ne_nil

theorem FreeAddMonoid.of_add_eq_iff {α : Type*} {a b : α} {x y : FreeAddMonoid α} :
    of a + x = of b + y ↔ a = b ∧ x = y := List.cons_eq_cons

theorem FreeAddMonoid.of_add_eq_of_iff {α : Type*} {a b : α} {x : FreeAddMonoid α} :
    of a + x = of b ↔ a = b ∧ x = 0 := by
  rw [← add_zero (of b), of_add_eq_iff]

theorem FreeAddMonoid.map_eq_zero_iff {α β : Type*} {f : α → β}
    {x : FreeAddMonoid α} :
    (FreeAddMonoid.map f x = 0) ↔ (x = 0) :=
  List.map_eq_nil

theorem FreeAddMonoid.map_eq_of_add_iff_exists {α β : Type*} {f : α → β}
    {x : FreeAddMonoid α} {b : β} {y : FreeAddMonoid β} :
    (FreeAddMonoid.map f x = of b + y) ↔
      ∃ a z, f a = b ∧ FreeAddMonoid.map f z = y ∧ x = of a + z := by
  constructor
  · intro h
    induction x using FreeAddMonoid.recOn generalizing y with
    | h0 =>
      rw [map_zero] at h
      exact False.elim (of_add_neq_zero _ _ h.symm)
    | ih a z _ =>
      rw [map_add, map_of, of_add_eq_iff] at h
      exact ⟨a, z, h.1, h.2, rfl⟩
  · rintro ⟨a, z, rfl, rfl, rfl⟩
    simp only [map_add, map_of]

theorem FreeAddMonoid.map_eq_of_iff_exists {α β : Type*} {f : α → β}
    {x : FreeAddMonoid α} {b : β} :
    (FreeAddMonoid.map f x = of b) ↔
      ∃ a, f a = b ∧ x = of a := by
  rw [← add_zero (of b), map_eq_of_add_iff_exists]
  simp only [exists_and_left]
  constructor
  · rintro ⟨a, rfl, x, hx, rfl⟩
    use a, rfl
    simp only [of_add_eq_of_iff, true_and]
    simpa only [map_eq_zero_iff] using hx
  · rintro ⟨a, rfl, rfl⟩
    exact ⟨a, rfl, 0, by simp only [map_zero, add_zero, and_self]⟩

theorem FreeAddMonoid.map_eq_add_iff_exists {α β : Type*} {f : α → β}
  {x : FreeAddMonoid α} {y₁ y₂ : FreeAddMonoid β} :
    FreeAddMonoid.map f x = y₁ + y₂ ↔
    ∃ x₁ x₂, x = x₁ + x₂ ∧ FreeAddMonoid.map f x₁ = y₁ ∧ FreeAddMonoid.map f x₂ = y₂ := by
  constructor
  · exact List.map_eq_append_split
  · rintro ⟨x₁, x₂, rfl, rfl, rfl⟩
    rw [map_add]

theorem FreeAddMonoid.map_injective_iff {α β : Type*} {f : α → β} :
    (Function.Injective (FreeAddMonoid.map f)) ↔ Function.Injective f :=
  List.map_injective_iff

theorem TensorProduct.Eqv_subtype_injective
    {M' : Submodule R M} {N' : Submodule R N} :
    Function.Injective (FreeAddMonoid.map (Prod.map (M'.subtype) (N'.subtype))) := by
  rw [FreeAddMonoid.map_injective_iff]
  simp only [Prod.map_injective]
  exact ⟨Submodule.injective_subtype M', Submodule.injective_subtype N'⟩

theorem Eqv_subtype_iff {M' : Submodule R M} {N' : Submodule R N}
    {x y : FreeAddMonoid (M' × N')} :
    (Eqv R M' N') x y ↔
      (Eqv R M N)
        (FreeAddMonoid.map (Prod.map M'.subtype N'.subtype) x)
        (FreeAddMonoid.map (Prod.map M'.subtype N'.subtype) y) := by
  constructor
  · intro h
    induction h with
    | of_zero_left n => apply Eqv.of_zero_left
    | of_zero_right m => apply Eqv.of_zero_right
    | of_add_left m₁ m₂ n => apply Eqv.of_add_left
    | of_add_right m n₁ n₂ => apply Eqv.of_add_right
    | of_smul r m n => apply Eqv.of_smul
    | add_comm x y =>
      simp only [Submodule.coeSubtype, map_add]
      apply Eqv.add_comm
  · intro h
    generalize hx' : ((FreeAddMonoid.map (Prod.map ⇑(Submodule.subtype M') ⇑(Submodule.subtype N'))) x) = x'
    generalize hy' : ((FreeAddMonoid.map (Prod.map ⇑(Submodule.subtype M') ⇑(Submodule.subtype N'))) y) = y'
    rw [hx', hy'] at h
    induction h with
    | of_zero_left n =>
      obtain ⟨⟨m', n'⟩, h, rfl⟩ := map_eq_of_iff_exists.mp hx'
      simp only [Submodule.coeSubtype, Prod_map, Prod.mk.injEq, ZeroMemClass.coe_eq_zero] at h
      rw [FreeAddMonoid.map_eq_zero_iff] at hy'
      rw [h.1, hy']
      apply Eqv.of_zero_left n'

    | of_zero_right m =>
      obtain ⟨⟨m', n'⟩, h, rfl⟩ := map_eq_of_iff_exists.mp hx'
      simp only [Submodule.coeSubtype, Prod_map, Prod.mk.injEq, ZeroMemClass.coe_eq_zero] at h
      rw [FreeAddMonoid.map_eq_zero_iff] at hy'
      rw [h.2, hy']
      apply Eqv.of_zero_right m'

    | of_add_left m₁ m₂ n =>
      rw [map_eq_of_add_iff_exists] at hx'
      obtain ⟨⟨m'₁, n'₁⟩, x', h1, hx', rfl⟩ := hx'
      simp only [map_add, map_of, Prod_map, of_add_eq_iff,
        map_eq_of_iff_exists] at hx'
      obtain ⟨⟨m'₂, n'₂⟩, h2, rfl⟩ := hx'
      rw [map_eq_of_iff_exists] at hy'
      obtain ⟨⟨m'₃, n'₃⟩, h3, rfl⟩ := hy'
      simp only [Submodule.coeSubtype, map_of, Prod_map, of_injective.eq_iff, Prod.mk.injEq] at h1 h2 h3
      have : n'₂ = n'₁ ∧ n'₃ = n'₁ := by
        simp only [← Subtype.coe_injective.eq_iff]
        simp_rw [h2.2, h1.2, h3.2, and_self]
      rw [this.1, this.2]
      have : m'₃ = m'₁ + m'₂ := by
        apply Subtype.coe_injective
        simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid]
        simp_rw [h3.1, h1.1, h2.1]
      rw [this]
      apply Eqv.of_add_left

    | of_add_right m n₁ n₂ =>
      rw [map_eq_of_add_iff_exists] at hx'
      obtain ⟨⟨m'₁, n'₁⟩, x', h1, hx', rfl⟩ := hx'
      simp only [map_add, map_of, Prod_map, of_add_eq_iff,
        map_eq_of_iff_exists] at hx'
      obtain ⟨⟨m'₂, n'₂⟩, h2, rfl⟩ := hx'
      rw [map_eq_of_iff_exists] at hy'
      obtain ⟨⟨m'₃, n'₃⟩, h3, rfl⟩ := hy'
      simp only [Submodule.coeSubtype, map_of, Prod_map, of_injective.eq_iff, Prod.mk.injEq] at h1 h2 h3
      have : m'₂ = m'₁ ∧ m'₃ = m'₁ := by
        simp only [← Subtype.coe_injective.eq_iff]
        simp_rw [h2.1, h1.1, h3.1, and_self]
      rw [this.1, this.2]
      have : n'₃ = n'₁ + n'₂ := by
        apply Subtype.coe_injective
        simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid]
        simp only [h3.2, h1.2, h2.2]
      rw [this]
      apply Eqv.of_add_right

    | of_smul r m n =>
      simp only [map_eq_of_iff_exists] at hx' hy'
      obtain ⟨⟨m'₁, n'₁⟩, hx', rfl⟩ := hx'
      obtain ⟨⟨m'₂, n'₂⟩, hy', rfl⟩ := hy'
      simp only [Submodule.coeSubtype, map_of, Prod_map, of_injective.eq_iff, Prod.mk.injEq] at hx' hy'
      have : m'₁ = r • m'₂ := by
        apply Subtype.coe_injective
        simp only [hx'.1, SetLike.val_smul, hy'.1]
      rw [this]
      have : n'₂ = r • n'₁ := by
        apply Subtype.coe_injective
        simp only [hx'.2, SetLike.val_smul, hy'.2]
      rw [this]
      apply Eqv.of_smul

    | add_comm a b =>
      rw [map_eq_add_iff_exists] at hx' hy'
      obtain ⟨a', b', rfl, ha', hb'⟩ := hx'
      obtain ⟨c', d', rfl, hc', hd'⟩ := hy'
      have : c' = b' := by
        apply TensorProduct.Eqv_subtype_injective
        rw [hc', hb']
      rw [this]
      have : d' = a' := by
        apply TensorProduct.Eqv_subtype_injective -- nom pourri
        rw [ha', hd']
      rw [this]
      apply Eqv.add_comm

theorem addConGen_Eqv_mono
    {M' M'' : Submodule R M} {N' N'' : Submodule R N}
    (hM : M' ≤ M'') (hN : N' ≤ N'')
    {x y : FreeAddMonoid (M' × N')}
    (hxy : addConGen (Eqv R M' N') x y) :
    (addConGen (Eqv R M'' N''))
        (FreeAddMonoid.map (Prod.map (Submodule.inclusion hM) (Submodule.inclusion hN)) x)
        (FreeAddMonoid.map (Prod.map (Submodule.inclusion hM) (Submodule.inclusion hN)) y) := by
  induction hxy with
  | of x y h =>
    apply AddConGen.Rel.of
    rw [Eqv_subtype_iff]
    simp only [← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp,
      Prod.map_comp_map, ← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
    rw [← Eqv_subtype_iff]
    exact h
  | refl x => exact AddConGen.Rel.refl _
  | symm _ ih => exact AddConGen.Rel.symm ih
  | trans _ _ ih ih' => exact AddConGen.Rel.trans ih ih'
  | add h h' ih ih' =>
    simp only [map_add]
    exact AddConGen.Rel.add ih ih'

theorem exists_fg_of_Eqv {sx sy : FreeAddMonoid (M × N)}
    (hxy : (Eqv R M N) sx sy) :
    ∃ (M' : Submodule R M), Submodule.FG M' ∧
    ∃ (N' : Submodule R N), Submodule.FG N' ∧
    ∃ (sx' : FreeAddMonoid (M' × N')) (sy' : FreeAddMonoid (M' × N')),
    FreeAddMonoid.map (Prod.map (Submodule.subtype M') (Submodule.subtype N')) sx' = sx
      ∧ FreeAddMonoid.map (Prod.map (Submodule.subtype M') (Submodule.subtype N')) sy' = sy
      ∧ (Eqv R M' N') sx' sy' := by
  obtain ⟨M', hM', N', hN', hx⟩ := mem_of_exists_fg (R := R) sx
  obtain ⟨M'', hM'', N'', hN'', hy⟩ := mem_of_exists_fg (R := R) sy
  use M' ⊔ M'', Submodule.FG.sup hM' hM''
  use N' ⊔ N'', Submodule.FG.sup hN' hN''
  have hx : sx.toProp (h (M' ⊔ M'') (N' ⊔ N'')) := by
    rw [← toProp_h_iff_mem_mrange] at hx
    exact toProp_imp (h_mono le_sup_left le_sup_left) hx
  have hy : sy.toProp (h (M' ⊔ M'') (N' ⊔ N'')) := by
    rw [← toProp_h_iff_mem_mrange] at hy
    exact toProp_imp (h_mono le_sup_right le_sup_right) hy
  rw [toProp_h_iff_mem_mrange] at hx hy
  obtain ⟨sx', rfl⟩ := hx
  obtain ⟨sy', rfl⟩ := hy
  use sx', sy'
  simp only [Submodule.coeSubtype, true_and]
  rw [← Eqv_subtype_iff] at hxy
  exact hxy


theorem exists_fg_of_addConGenEqv {x y : FreeAddMonoid (M × N)}
    (hxy : addConGen (Eqv R M N) x y) :
    ∃ (M' : Submodule R M), Submodule.FG M' ∧
    ∃ (N' : Submodule R N), Submodule.FG N' ∧
    ∃ (x' : FreeAddMonoid (M' × N')) (y' : FreeAddMonoid (M' × N')),
    FreeAddMonoid.map (Prod.map (Submodule.subtype M') (Submodule.subtype N')) x' = x
      ∧ FreeAddMonoid.map (Prod.map (Submodule.subtype M') (Submodule.subtype N')) y' = y
      ∧ (addConGen (Eqv R M' N')) x' y' := by
  classical
  induction hxy with
  | of x y hxy =>
    obtain ⟨M', hM', N', hN', x', y', hx', hy', h⟩ := exists_fg_of_Eqv hxy
    use M', hM', N', hN', x', y', hx', hy'
    exact AddConGen.Rel.of x' y' h
  | refl x =>
    obtain ⟨M', hM', N', hN', x', hx'⟩ := mem_of_fg (R := R) x
    use M', hM', N', hN', x', x', hx'.symm, hx'.symm
    exact AddConGen.Rel.refl x'
  | symm _ ih =>
    obtain ⟨M', hM', N', hN', x', y', rfl, rfl, h'⟩ := ih
    use M', hM', N', hN', y', x', rfl, rfl
    exact AddConGen.Rel.symm h'
  | trans h h' ih ih' =>
    obtain ⟨M', hM', N', hN', x', y', rfl, rfl, ih⟩ := ih
    obtain ⟨M'', hM'', N'', hN'', x'', y'', hx''y', rfl, ih'⟩ := ih'
    let P := M' ⊔ M''
    use P, Submodule.FG.sup hM' hM''
    let Q := N' ⊔ N''
    use Q, Submodule.FG.sup hN' hN''
    let x := (FreeAddMonoid.map (Prod.map
          (Submodule.inclusion le_sup_left)
          (Submodule.inclusion le_sup_left)) x' : FreeAddMonoid (P × Q))
    let y := (FreeAddMonoid.map (Prod.map
          (Submodule.inclusion le_sup_left)
          (Submodule.inclusion le_sup_left)) y' : FreeAddMonoid (P × Q))
    let y2 := (FreeAddMonoid.map (Prod.map
          (Submodule.inclusion le_sup_right)
          (Submodule.inclusion le_sup_right)) x'' : FreeAddMonoid (P × Q))
    let z := (FreeAddMonoid.map (Prod.map
          (Submodule.inclusion le_sup_right)
          (Submodule.inclusion le_sup_right)) y'' : FreeAddMonoid (P × Q))
    use x, z
    constructor
    simp only [x,
      ← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp,
      Prod.map_comp_map, ← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
    constructor
    simp only [z,
      ← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp,
      Prod.map_comp_map, ← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
    have : y2 = y := by
      apply TensorProduct.Eqv_subtype_injective
      simp only [y, y2,
        ← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp,
        Prod.map_comp_map, ← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
      exact hx''y'
    suffices addConGen (Eqv R P Q) x y ∧ addConGen (Eqv R P Q) y z by
      apply AddConGen.Rel.trans this.1 this.2
    constructor
    · simp only [x, y]
      exact addConGen_Eqv_mono _ _ ih
    · simp only [← this, y2, z]
      exact addConGen_Eqv_mono _ _ ih'

  | add h h' ih ih' =>
    obtain ⟨M', hM', N', hN', x', y', rfl, rfl, ih⟩ := ih
    obtain ⟨M'', hM'', N'', hN'', x'', y'', rfl, rfl, ih'⟩ := ih'
    let P := M' ⊔ M''
    use P, Submodule.FG.sup hM' hM''
    let Q := N' ⊔ N''
    use Q, Submodule.FG.sup hN' hN''
    let x := (FreeAddMonoid.map (Prod.map
          (Submodule.inclusion le_sup_left)
          (Submodule.inclusion le_sup_left)) x' : FreeAddMonoid (P × Q)) +
      (FreeAddMonoid.map (Prod.map
          (Submodule.inclusion le_sup_right)
          (Submodule.inclusion le_sup_right)) x'' : FreeAddMonoid (P × Q))
    let y := (FreeAddMonoid.map (Prod.map
          (Submodule.inclusion le_sup_left)
          (Submodule.inclusion le_sup_left)) y' : FreeAddMonoid (P × Q)) +
      (FreeAddMonoid.map (Prod.map
          (Submodule.inclusion le_sup_right)
          (Submodule.inclusion le_sup_right)) y'' : FreeAddMonoid (P × Q))
    use x, y
    constructor
    · simp only [x, map_add]
      simp only [← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp, Prod.map_comp_map, ← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
    constructor
    · simp only [y, map_add]
      simp only [← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp, Prod.map_comp_map, ← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
    · simp only [x, y]
      apply AddConGen.Rel.add
      exact addConGen_Eqv_mono _ _ ih
      exact addConGen_Eqv_mono _ _ ih'

theorem Submodule.exists_le_fg_of_map_eq
    (M₁ : Submodule R M) (hM₁ : Submodule.FG M₁)
    (N₁ : Submodule R N) (hN₁ : Submodule.FG N₁)
    (x y : M₁ ⊗[R] N₁)
    (h : TensorProduct.map (Submodule.subtype M₁) (Submodule.subtype N₁) x = TensorProduct.map (Submodule.subtype M₁) (Submodule.subtype N₁) y) :
    ∃ M₀, Submodule.FG M₀ ∧ ∃ (hM : M₁ ≤ M₀),
      ∃ N₀, Submodule.FG N₀ ∧ ∃ (hN : N₁ ≤ N₀),
        TensorProduct.map (Submodule.inclusion hM) (Submodule.inclusion hN) x =
        TensorProduct.map (Submodule.inclusion hM) (Submodule.inclusion hN) y := by
  obtain ⟨sx, rfl⟩ := AddCon.mk'_surjective x
  obtain ⟨sy, rfl⟩ := AddCon.mk'_surjective y
  rw [← TensorProduct.map_lift_eq (Submodule.subtype M₁) (Submodule.subtype N₁) sx,
    ← TensorProduct.map_lift_eq (Submodule.subtype M₁) (Submodule.subtype N₁) sy] at h
  erw [← AddCon.ker_apply, AddCon.mk'_ker] at h
  obtain ⟨M₂, hM₂, N₂, hN₂, sx', sy', hsx, hsy, h⟩ :=
    exists_fg_of_addConGenEqv h
  let M' := M₁ ⊔ M₂
  use M', FG.sup hM₁ hM₂, le_sup_left
  let N' := N₁ ⊔ N₂
  use N', FG.sup hN₁ hN₂, le_sup_left
  simp only [← TensorProduct.map_lift_eq]
  rw [← AddCon.ker_apply (f := (AddCon.mk' (addConGen (Eqv R ↥(M₁ ⊔ M₂) ↥(N₁ ⊔ N₂))))), AddCon.mk'_ker]
  have : (FreeAddMonoid.map (Prod.map ⇑(inclusion (le_sup_left : M₁ ≤ M₁ ⊔ M₂)) ⇑(inclusion (le_sup_left : N₁ ≤ N₁ ⊔ N₂)))) sx =
    (FreeAddMonoid.map (Prod.map ⇑(inclusion (le_sup_right : M₂ ≤ M₁ ⊔ M₂)) ⇑(inclusion (le_sup_right : N₂ ≤ N₁ ⊔ N₂)))) sx'  := by
    apply TensorProduct.Eqv_subtype_injective
    simp only [← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp, Prod.map_comp_map, ← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
    exact hsx.symm
  rw [this]
  have : (FreeAddMonoid.map (Prod.map ⇑(inclusion (le_sup_left : M₁ ≤ M₁ ⊔ M₂)) ⇑(inclusion (le_sup_left : N₁ ≤ N₁ ⊔ N₂)))) sy =
    (FreeAddMonoid.map (Prod.map ⇑(inclusion (le_sup_right : M₂ ≤ M₁ ⊔ M₂)) ⇑(inclusion (le_sup_right : N₂ ≤ N₁ ⊔ N₂)))) sy'  := by
    apply TensorProduct.Eqv_subtype_injective
    simp only [← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp, Prod.map_comp_map, ← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
    exact hsy.symm
  rw [this]
  exact addConGen_Eqv_mono _ _ h

theorem Subalgebra.subtype_comp_inclusion
    {S : Type*} [Semiring S] [Algebra R S]{A B : Subalgebra R S} (h : A ≤ B) :
    AlgHom.comp (val B) (Subalgebra.inclusion h) = val A := by
  ext a
  rfl

example [Semiring R] [Module R M]
    (P : Submodule R M) (Q : Submodule R P) : Submodule R M :=
  Submodule.map (P.subtype) Q

theorem Subalgebra.exists_le_fg_of_map_eq
    (S : Type v) [CommSemiring S] [Algebra R S]
    (S₁ : Subalgebra R S) (hS₁ : Subalgebra.FG S₁)
    (x y : S₁ ⊗[R] M)
    (hxy : LinearMap.rTensor M (Subalgebra.val S₁).toLinearMap x =
      LinearMap.rTensor M (Subalgebra.val S₁).toLinearMap y) :
    ∃ S₀, Subalgebra.FG S₀ ∧ ∃ (hS : S₁ ≤ S₀),
        LinearMap.rTensor M (Subalgebra.inclusion hS).toLinearMap x =
        LinearMap.rTensor M (Subalgebra.inclusion hS).toLinearMap y := by
  classical
  -- the tensors x and y live on fin. gen. Px ⊗[R] Qx and Py ⊗[R] Qy
  obtain ⟨Px, hPx, Qx, hQx, ⟨x', hx'⟩⟩ := TensorProduct.mem_map_subtype_of_FG x
  obtain ⟨Py, hPy, Qy, hQy, ⟨y', hy'⟩⟩ := TensorProduct.mem_map_subtype_of_FG y
  -- they both live on the fin gen P ⊗[R] Q
  -- P is a submodule of S which is contained in S₁
  let P := Submodule.map (Subalgebra.toSubmodule S₁).subtype (Px ⊔ Py)
  have hP : Submodule.FG P := Submodule.FG.map _ (Submodule.FG.sup hPx hPy)
  let Q := Qx ⊔ Qy
  have hQ : Submodule.FG Q := Submodule.FG.sup hQx hQy
  -- the canonical injections from Px and Py to P
  let jx : Px →ₗ[R] P :=
    LinearMap.restrict (Subalgebra.toSubmodule S₁).subtype (fun p hp => by
      simp only [Submodule.coeSubtype, Submodule.map_sup]
      apply Submodule.mem_sup_left
      use p
      simp only [SetLike.mem_coe]
      exact ⟨hp, rfl⟩)
  let jy : Py →ₗ[R] P :=
    LinearMap.restrict (Subalgebra.toSubmodule S₁).subtype (fun p hp => by
      simp only [Submodule.coeSubtype, Submodule.map_sup]
      apply Submodule.mem_sup_right
      use p
      simp only [SetLike.mem_coe]
      exact ⟨hp, rfl⟩)
  -- we map x' and y' to P ⊗[R] Q, getting xPQ and yPQ
  set xPQ := TensorProduct.map jx (Submodule.inclusion (le_sup_left : Qx ≤ Q)) x' with hxPQ
  set yPQ := TensorProduct.map jy (Submodule.inclusion (le_sup_right : Qy ≤ Q)) y' with hyPQ
  -- xPQ and yPQ are equal in S ⊗[R] M
  have : TensorProduct.map P.subtype Q.subtype xPQ
    = TensorProduct.map P.subtype Q.subtype yPQ := by
    rw [hxPQ, hyPQ]
    have jkx : P.subtype ∘ₗ jx = (val S₁).toLinearMap ∘ₗ Px.subtype := by
      ext p
      rfl
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, jkx]
    have jky : P.subtype ∘ₗ jy = (val S₁).toLinearMap ∘ₗ Py.subtype := by
      ext p
      rfl
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, jky]
    simp only [Submodule.subtype_comp_inclusion]
    rw [← LinearMap.id_comp (Submodule.subtype Qx)]
    rw [← LinearMap.id_comp (Submodule.subtype Qy)]
    simp only [TensorProduct.map_comp, LinearMap.comp_apply]
    simp only [LinearMap.rTensor] at hxy
    rw [hx', hy']
    exact hxy
  -- xPQ and yPQ are equal in a finitely generated P' ⊗[R] Q'
  obtain ⟨P', hP', P_le_P', Q', _, Q_le_Q', h⟩ :=
    Submodule.exists_le_fg_of_map_eq P hP Q hQ xPQ yPQ this
  obtain ⟨s, hs⟩ := hP'
  obtain ⟨t, ht⟩ := hS₁
  -- We define S₀, a fin generated algebra that contains S₁ and P'
  let S₀ := Algebra.adjoin R ((s ∪ t : Finset S) : Set S)
  use S₀, Subalgebra.fg_adjoin_finset _
  have hS₁_le_S₀ : S₁ ≤ S₀ := by
    simp only [S₀, ← ht]
    apply Algebra.adjoin_mono
    simp only [Finset.coe_union, Set.subset_union_right]
  use hS₁_le_S₀
  have hS₁_le_S₀' : (Subalgebra.toSubmodule S₁ : Submodule R S) ≤ Subalgebra.toSubmodule S₀ := hS₁_le_S₀
  have hk : AlgHom.toLinearMap (Subalgebra.inclusion hS₁_le_S₀) = Submodule.inclusion hS₁_le_S₀' := by
    ext s
    rfl
  -- We factor the tensor products as S₁ → S₀ → M
  simp only [LinearMap.rTensor]
  rw [← hx', ← hy', hk]
  simp only [← LinearMap.comp_apply, ← LinearMap.coe_comp, ← TensorProduct.map_comp, LinearMap.id_comp]
  -- we factor the map Px → S₁ → S₀ via Px → P → P' → S₀
  -- Px → S₁ is Px.subtype
  -- Px → P is jx
  -- P → P' is Submodule.inclusion (P_le_P')
  -- Define P' → S₀
  have P'_le_S₀ : P' ≤ Subalgebra.toSubmodule S₀ := by
    simp only [← hs, Submodule.span_le, Finset.coe_union, coe_toSubmodule]
    exact le_trans (Set.subset_union_left _ _) (Algebra.subset_adjoin)
  have hkx : (Submodule.inclusion hS₁_le_S₀') ∘ₗ Px.subtype
    = Submodule.inclusion (R := R) (P'_le_S₀)  ∘ₗ (Submodule.inclusion (R := R) P_le_P') ∘ₗ jx := by
    ext p
    rfl
  have hky : (Submodule.inclusion hS₁_le_S₀') ∘ₗ Py.subtype
    = Submodule.inclusion (R := R) (P'_le_S₀)  ∘ₗ (Submodule.inclusion (R := R) P_le_P') ∘ₗ jy := by
    ext p
    rfl
  rw [hkx, hky]
  rw [← LinearMap.id_comp (Submodule.subtype Qx),
    ← LinearMap.id_comp (Submodule.subtype Qy)]
  rw [TensorProduct.map_comp, LinearMap.comp_apply]
  rw [TensorProduct.map_comp, LinearMap.comp_apply]
  apply congr_arg
  -- Now we have x' and y' pushed in P' ⊗[R] M
  -- We know that x' and y' pushed to P ⊗[R] Q  give xPQ and yPQ
  rw [← Submodule.subtype_comp_inclusion _ _ (le_sup_left : Qx ≤ Q)]
  rw [← Submodule.subtype_comp_inclusion _ _ (le_sup_right : Qy ≤ Q)]
  rw [TensorProduct.map_comp, LinearMap.comp_apply]
  rw [TensorProduct.map_comp, LinearMap.comp_apply]
  rw [← hxPQ, ← hyPQ]
  -- Now we have xPQ and yPQ pushed in P' ⊗[R] M
  -- They coincide in P' ⊗[R] Q'
  rw [← Submodule.subtype_comp_inclusion _ _ Q_le_Q']
  rw [← LinearMap.id_comp (Submodule.inclusion P_le_P')]
  rw [TensorProduct.map_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [h]
  done

end FG

section Lift

namespace AlgHom

variable {R : Type u} [CommSemiring R]
    {S : Type v} [Semiring S] [Algebra R S]
    {T : Type w} [Semiring T] [Algebra R T]

theorem range_top_iff_surjective {f : S →ₐ[R] T} :
    f.range = (⊤ : Subalgebra R T) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <|
    Iff.trans (by rw [coe_range, Algebra.coe_top]) Set.range_iff_surjective

theorem range_top_of_surjective (f : S →ₐ[R] T) (hf : Function.Surjective f) :
    f.range = ⊤ :=
  range_top_iff_surjective.2 hf

lemma LiftDown_of_FiniteType  {R : Type u} [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    (B : Subalgebra R S) [hFT : Algebra.FiniteType R B] :
    ∃ (A : Type u), ∃ (hCR : CommRing A), ∃ (hAlg : Algebra R A),
    ∃ (_ : A ≃ₐ[R] B), True := by
  obtain ⟨n, ⟨f, hf⟩⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hFT
  exact ⟨_, Ideal.Quotient.commRing (RingHom.ker f), Ideal.Quotient.algebra R,
    (Ideal.quotientKerEquivRange f).trans (range_top_of_surjective f hf ▸ Subalgebra.topEquiv),
    trivial⟩

end AlgHom

end Lift
