/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.FixedPoint

#align_import set_theory.cardinal.cofinality from "leanprover-community/mathlib"@"7c2ce0c2da15516b4e65d0c9e254bb6dc93abd1f"

/-!
# Cofinality

This file contains the definition of cofinality of an ordinal number and regular cardinals

## Main Definitions

* `Ordinal.cof o` is the cofinality of the ordinal `o`.
  If `o` is the order type of the relation `<` on `α`, then `o.cof` is the smallest cardinality of a
  subset `s` of α that is *cofinal* in `α`, i.e. `∀ x : α, ∃ y ∈ s, ¬ y < x`.
* `Cardinal.IsStrongLimit c` means that `c` is a strong limit cardinal:
  `c ≠ 0 ∧ ∀ x < c, 2 ^ x < c`.
* `Cardinal.IsRegular c` means that `c` is a regular cardinal: `ℵ₀ ≤ c ∧ c.ord.cof = c`.
* `Cardinal.IsInaccessible c` means that `c` is strongly inaccessible:
  `ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c`.

## Main Statements

* `Ordinal.infinite_pigeonhole_card`: the infinite pigeonhole principle
* `Cardinal.lt_power_cof`: A consequence of König's theorem stating that `c < c ^ c.ord.cof` for
  `c ≥ ℵ₀`
* `Cardinal.univ_inaccessible`: The type of ordinals in `Type u` form an inaccessible cardinal
  (in `Type v` with `v > u`). This shows (externally) that in `Type u` there are at least `u`
  inaccessible cardinals.

## Implementation Notes

* The cofinality is defined for ordinals.
  If `c` is a cardinal number, its cofinality is `c.ord.cof`.

## Tags

cofinality, regular cardinals, limits cardinals, inaccessible cardinals,
infinite pigeonhole principle
-/


noncomputable section

open Function Cardinal Set Order

open Classical Cardinal Ordinal

universe u v w

variable {α : Type*} {r : α → α → Prop}

/-! ### Cofinality of orders -/


namespace Order

/-- Cofinality of a reflexive order `≼`. This is the smallest cardinality
  of a subset `S : Set α` such that `∀ a, ∃ b ∈ S, a ≼ b`. -/
def cof (r : α → α → Prop) : Cardinal :=
  sInf { c | ∃ S : Set α, (∀ a, ∃ b ∈ S, r a b) ∧ #S = c }
#align order.cof Order.cof

/-- The set in the definition of `Order.cof` is nonempty. -/
theorem cof_nonempty (r : α → α → Prop) [IsRefl α r] :
    { c | ∃ S : Set α, (∀ a, ∃ b ∈ S, r a b) ∧ #S = c }.Nonempty :=
  ⟨_, Set.univ, fun a => ⟨a, ⟨⟩, refl _⟩, rfl⟩
#align order.cof_nonempty Order.cof_nonempty

theorem cof_le (r : α → α → Prop) {S : Set α} (h : ∀ a, ∃ b ∈ S, r a b) : cof r ≤ #S :=
  csInf_le' ⟨S, h, rfl⟩
#align order.cof_le Order.cof_le

theorem le_cof {r : α → α → Prop} [IsRefl α r] (c : Cardinal) :
    c ≤ cof r ↔ ∀ {S : Set α}, (∀ a, ∃ b ∈ S, r a b) → c ≤ #S := by
  rw [cof, le_csInf_iff'' (cof_nonempty r)]
  -- ⊢ (∀ (b : Cardinal.{u_1}), b ∈ {c | ∃ S, (∀ (a : α), ∃ b, b ∈ S ∧ r a b) ∧ #↑S …
  use fun H S h => H _ ⟨S, h, rfl⟩
  -- ⊢ (∀ {S : Set α}, (∀ (a : α), ∃ b, b ∈ S ∧ r a b) → c ≤ #↑S) → ∀ (b : Cardinal …
  rintro H d ⟨S, h, rfl⟩
  -- ⊢ c ≤ #↑S
  exact H h
  -- 🎉 no goals
#align order.le_cof Order.le_cof

end Order

theorem RelIso.cof_le_lift {α : Type u} {β : Type v} {r : α → α → Prop} {s} [IsRefl β s]
    (f : r ≃r s) : Cardinal.lift.{max u v} (Order.cof r) ≤
    Cardinal.lift.{max u v} (Order.cof s) := by
  rw [Order.cof, Order.cof, lift_sInf, lift_sInf,
    le_csInf_iff'' (nonempty_image_iff.2 (Order.cof_nonempty s))]
  rintro - ⟨-, ⟨u, H, rfl⟩, rfl⟩
  -- ⊢ sInf (Cardinal.lift.{max u v, u} '' {c | ∃ S, (∀ (a : α), ∃ b, b ∈ S ∧ r a b …
  apply csInf_le'
  -- ⊢ Cardinal.lift.{max u v, v} #↑u ∈ Cardinal.lift.{max u v, u} '' {c | ∃ S, (∀  …
  refine'
    ⟨_, ⟨f.symm '' u, fun a => _, rfl⟩,
      lift_mk_eq.{u, v, max u v}.2 ⟨(f.symm.toEquiv.image u).symm⟩⟩
  rcases H (f a) with ⟨b, hb, hb'⟩
  -- ⊢ ∃ b, b ∈ ↑(RelIso.symm f) '' u ∧ r a b
  refine' ⟨f.symm b, mem_image_of_mem _ hb, f.map_rel_iff.1 _⟩
  -- ⊢ s (↑f a) (↑f (↑(RelIso.symm f) b))
  rwa [RelIso.apply_symm_apply]
  -- 🎉 no goals
#align rel_iso.cof_le_lift RelIso.cof_le_lift

theorem RelIso.cof_eq_lift {α : Type u} {β : Type v} {r s} [IsRefl α r] [IsRefl β s] (f : r ≃r s) :
    Cardinal.lift.{max u v} (Order.cof r) = Cardinal.lift.{max u v} (Order.cof s) :=
  (RelIso.cof_le_lift f).antisymm (RelIso.cof_le_lift f.symm)
#align rel_iso.cof_eq_lift RelIso.cof_eq_lift

theorem RelIso.cof_le {α β : Type u} {r : α → α → Prop} {s} [IsRefl β s] (f : r ≃r s) :
    Order.cof r ≤ Order.cof s :=
  lift_le.1 (RelIso.cof_le_lift f)
#align rel_iso.cof_le RelIso.cof_le

theorem RelIso.cof_eq {α β : Type u} {r s} [IsRefl α r] [IsRefl β s] (f : r ≃r s) :
    Order.cof r = Order.cof s :=
  lift_inj.1 (RelIso.cof_eq_lift f)
#align rel_iso.cof_eq RelIso.cof_eq

/-- Cofinality of a strict order `≺`. This is the smallest cardinality of a set `S : Set α` such
that `∀ a, ∃ b ∈ S, ¬ b ≺ a`. -/
def StrictOrder.cof (r : α → α → Prop) : Cardinal :=
  Order.cof (swap rᶜ)
#align strict_order.cof StrictOrder.cof

/-- The set in the definition of `Order.StrictOrder.cof` is nonempty. -/
theorem StrictOrder.cof_nonempty (r : α → α → Prop) [IsIrrefl α r] :
    { c | ∃ S : Set α, Unbounded r S ∧ #S = c }.Nonempty :=
  @Order.cof_nonempty α _ (IsRefl.swap rᶜ)
#align strict_order.cof_nonempty StrictOrder.cof_nonempty

/-! ### Cofinality of ordinals -/


namespace Ordinal

/-- Cofinality of an ordinal. This is the smallest cardinal of a
  subset `S` of the ordinal which is unbounded, in the sense
  `∀ a, ∃ b ∈ S, a ≤ b`. It is defined for all ordinals, but
  `cof 0 = 0` and `cof (succ o) = 1`, so it is only really
  interesting on limit ordinals (when it is an infinite cardinal). -/
def cof (o : Ordinal.{u}) : Cardinal.{u} :=
  o.liftOn (fun a => StrictOrder.cof a.r)
    (by
      rintro ⟨α, r, wo₁⟩ ⟨β, s, wo₂⟩ ⟨⟨f, hf⟩⟩
      -- ⊢ (fun a => StrictOrder.cof a.r) { α := α, r := r, wo := wo₁ } = (fun a => Str …
      haveI := wo₁; haveI := wo₂
      -- ⊢ (fun a => StrictOrder.cof a.r) { α := α, r := r, wo := wo₁ } = (fun a => Str …
                    -- ⊢ (fun a => StrictOrder.cof a.r) { α := α, r := r, wo := wo₁ } = (fun a => Str …
      dsimp only
      -- ⊢ StrictOrder.cof r = StrictOrder.cof s
      apply @RelIso.cof_eq _ _ _ _ ?_ ?_
      · constructor
        -- ⊢ ∀ {a b : α}, swap sᶜ (↑?mk.mk.intro.mk.toEquiv a) (↑?mk.mk.intro.mk.toEquiv  …
        exact @fun a b => not_iff_not.2 hf
        -- 🎉 no goals
      · dsimp only [swap]
        -- ⊢ IsRefl α fun y x => rᶜ x y
        exact ⟨fun _ => irrefl _⟩
        -- 🎉 no goals
      · dsimp only [swap]
        -- ⊢ IsRefl β fun y x => sᶜ x y
        exact ⟨fun _ => irrefl _⟩)
        -- 🎉 no goals
#align ordinal.cof Ordinal.cof

theorem cof_type (r : α → α → Prop) [IsWellOrder α r] : (type r).cof = StrictOrder.cof r :=
  rfl
#align ordinal.cof_type Ordinal.cof_type

theorem le_cof_type [IsWellOrder α r] {c} : c ≤ cof (type r) ↔ ∀ S, Unbounded r S → c ≤ #S :=
  (le_csInf_iff'' (StrictOrder.cof_nonempty r)).trans
    ⟨fun H S h => H _ ⟨S, h, rfl⟩, by
      rintro H d ⟨S, h, rfl⟩
      -- ⊢ c ≤ #↑S
      exact H _ h⟩
      -- 🎉 no goals
#align ordinal.le_cof_type Ordinal.le_cof_type

theorem cof_type_le [IsWellOrder α r] {S : Set α} (h : Unbounded r S) : cof (type r) ≤ #S :=
  le_cof_type.1 le_rfl S h
#align ordinal.cof_type_le Ordinal.cof_type_le

theorem lt_cof_type [IsWellOrder α r] {S : Set α} : #S < cof (type r) → Bounded r S := by
  simpa using not_imp_not.2 cof_type_le
  -- 🎉 no goals
#align ordinal.lt_cof_type Ordinal.lt_cof_type

theorem cof_eq (r : α → α → Prop) [IsWellOrder α r] : ∃ S, Unbounded r S ∧ #S = cof (type r) :=
  csInf_mem (StrictOrder.cof_nonempty r)
#align ordinal.cof_eq Ordinal.cof_eq

theorem ord_cof_eq (r : α → α → Prop) [IsWellOrder α r] :
    ∃ S, Unbounded r S ∧ type (Subrel r S) = (cof (type r)).ord := by
  let ⟨S, hS, e⟩ := cof_eq r
  -- ⊢ ∃ S, Unbounded r S ∧ type (Subrel r S) = ord (cof (type r))
  let ⟨s, _, e'⟩ := Cardinal.ord_eq S
  -- ⊢ ∃ S, Unbounded r S ∧ type (Subrel r S) = ord (cof (type r))
  let T : Set α := { a | ∃ aS : a ∈ S, ∀ b : S, s b ⟨_, aS⟩ → r b a }
  -- ⊢ ∃ S, Unbounded r S ∧ type (Subrel r S) = ord (cof (type r))
  suffices : Unbounded r T
  -- ⊢ ∃ S, Unbounded r S ∧ type (Subrel r S) = ord (cof (type r))
  · refine' ⟨T, this, le_antisymm _ (Cardinal.ord_le.2 <| cof_type_le this)⟩
    -- ⊢ type (Subrel r T) ≤ ord (cof (type r))
    rw [← e, e']
    -- ⊢ type (Subrel r T) ≤ type s
    refine'
      (RelEmbedding.ofMonotone
          (fun a : T =>
            (⟨a,
                let ⟨aS, _⟩ := a.2
                aS⟩ :
              S))
          fun a b h => _).ordinal_type_le
    rcases a with ⟨a, aS, ha⟩
    -- ⊢ s ((fun a => { val := ↑a, property := (_ : ↑a ∈ S) }) { val := a, property : …
    rcases b with ⟨b, bS, hb⟩
    -- ⊢ s ((fun a => { val := ↑a, property := (_ : ↑a ∈ S) }) { val := a, property : …
    change s ⟨a, _⟩ ⟨b, _⟩
    -- ⊢ s { val := a, property := (_ : ↑{ val := a, property := (_ : ∃ aS, ∀ (b : ↑S …
    refine' ((trichotomous_of s _ _).resolve_left fun hn => _).resolve_left _
    -- ⊢ False
    · exact asymm h (ha _ hn)
      -- 🎉 no goals
    · intro e
      -- ⊢ False
      injection e with e
      -- ⊢ False
      subst b
      -- ⊢ False
      exact irrefl _ h
      -- 🎉 no goals
  · intro a
    -- ⊢ ∃ b, b ∈ T ∧ ¬r b a
    have : { b : S | ¬r b a }.Nonempty :=
      let ⟨b, bS, ba⟩ := hS a
      ⟨⟨b, bS⟩, ba⟩
    let b := (IsWellFounded.wf : WellFounded s).min _ this
    -- ⊢ ∃ b, b ∈ T ∧ ¬r b a
    have ba : ¬r b a := IsWellFounded.wf.min_mem _ this
    -- ⊢ ∃ b, b ∈ T ∧ ¬r b a
    refine' ⟨b, ⟨b.2, fun c => not_imp_not.1 fun h => _⟩, ba⟩
    -- ⊢ ¬s c { val := ↑b, property := (_ : ↑b ∈ S) }
    rw [show ∀ b : S, (⟨b, b.2⟩ : S) = b by intro b; cases b; rfl]
    -- ⊢ ¬s c b
    exact IsWellFounded.wf.not_lt_min _ this (IsOrderConnected.neg_trans h ba)
    -- 🎉 no goals
#align ordinal.ord_cof_eq Ordinal.ord_cof_eq

/-! ### Cofinality of suprema and least strict upper bounds -/


private theorem card_mem_cof {o} : ∃ (ι : _) (f : ι → Ordinal), lsub.{u, u} f = o ∧ #ι = o.card :=
  ⟨_, _, lsub_typein o, mk_ordinal_out o⟩

/-- The set in the `lsub` characterization of `cof` is nonempty. -/
theorem cof_lsub_def_nonempty (o) :
    { a : Cardinal | ∃ (ι : _) (f : ι → Ordinal), lsub.{u, u} f = o ∧ #ι = a }.Nonempty :=
  ⟨_, card_mem_cof⟩
#align ordinal.cof_lsub_def_nonempty Ordinal.cof_lsub_def_nonempty

theorem cof_eq_sInf_lsub (o : Ordinal.{u}) : cof o =
    sInf { a : Cardinal | ∃ (ι : Type u) (f : ι → Ordinal), lsub.{u, u} f = o ∧ #ι = a } := by
  refine' le_antisymm (le_csInf (cof_lsub_def_nonempty o) _) (csInf_le' _)
  -- ⊢ ∀ (b : Cardinal.{u}), b ∈ {a | ∃ ι f, lsub f = o ∧ #ι = a} → cof o ≤ b
  · rintro a ⟨ι, f, hf, rfl⟩
    -- ⊢ cof o ≤ #ι
    rw [← type_lt o]
    -- ⊢ cof (type fun x x_1 => x < x_1) ≤ #ι
    refine'
      (cof_type_le fun a => _).trans
        (@mk_le_of_injective _ _
          (fun s : typein ((· < ·) : o.out.α → o.out.α → Prop) ⁻¹' Set.range f =>
            Classical.choose s.prop)
          fun s t hst => by
          let H := congr_arg f hst
          rwa [Classical.choose_spec s.prop, Classical.choose_spec t.prop, typein_inj,
            Subtype.coe_inj] at H)
    have := typein_lt_self a
    -- ⊢ ∃ b, b ∈ (typein fun x x_1 => x < x_1) ⁻¹' range f ∧ ¬b < a
    simp_rw [← hf, lt_lsub_iff] at this
    -- ⊢ ∃ b, b ∈ (typein fun x x_1 => x < x_1) ⁻¹' range f ∧ ¬b < a
    cases' this with i hi
    -- ⊢ ∃ b, b ∈ (typein fun x x_1 => x < x_1) ⁻¹' range f ∧ ¬b < a
    refine' ⟨enum (· < ·) (f i) _, _, _⟩
    · rw [type_lt, ← hf]
      -- ⊢ f i < lsub f
      apply lt_lsub
      -- 🎉 no goals
    · rw [mem_preimage, typein_enum]
      -- ⊢ f i ∈ range f
      exact mem_range_self i
      -- 🎉 no goals
    · rwa [← typein_le_typein, typein_enum]
      -- 🎉 no goals
  · rcases cof_eq (· < · : (Quotient.out o).α → (Quotient.out o).α → Prop) with ⟨S, hS, hS'⟩
    -- ⊢ cof o ∈ {a | ∃ ι f, lsub f = o ∧ #ι = a}
    let f : S → Ordinal := fun s => typein LT.lt s.val
    -- ⊢ cof o ∈ {a | ∃ ι f, lsub f = o ∧ #ι = a}
    refine'
      ⟨S, f, le_antisymm (lsub_le fun i => typein_lt_self i) (le_of_forall_lt fun a ha => _), by
        rwa [type_lt o] at hS'⟩
    rw [← type_lt o] at ha
    -- ⊢ a < lsub f
    rcases hS (enum (· < ·) a ha) with ⟨b, hb, hb'⟩
    -- ⊢ a < lsub f
    rw [← typein_le_typein, typein_enum] at hb'
    -- ⊢ a < lsub f
    exact hb'.trans_lt (lt_lsub.{u, u} f ⟨b, hb⟩)
    -- 🎉 no goals
#align ordinal.cof_eq_Inf_lsub Ordinal.cof_eq_sInf_lsub

@[simp]
theorem lift_cof (o) : Cardinal.lift.{u, v} (cof o) = cof (Ordinal.lift.{u, v} o) := by
  refine' inductionOn o _
  -- ⊢ ∀ (α : Type v) (r : α → α → Prop) [inst : IsWellOrder α r], Cardinal.lift.{u …
  intro α r _
  -- ⊢ Cardinal.lift.{u, v} (cof (type r)) = cof (lift.{u, v} (type r))
  apply le_antisymm
  -- ⊢ Cardinal.lift.{u, v} (cof (type r)) ≤ cof (lift.{u, v} (type r))
  · refine' le_cof_type.2 fun S H => _
    -- ⊢ Cardinal.lift.{u, v} (cof (type r)) ≤ #↑S
    have : Cardinal.lift.{u, v} #(ULift.up ⁻¹' S) ≤ #(S : Type (max u v)) := by
      rw [← Cardinal.lift_umax.{v, u}, ← Cardinal.lift_id'.{v, u} #S]
      refine mk_preimage_of_injective_lift.{v, max u v} ULift.up S (ULift.up_injective.{u, v})
    refine' (Cardinal.lift_le.2 <| cof_type_le _).trans this
    -- ⊢ Unbounded r (ULift.up ⁻¹' S)
    exact fun a =>
      let ⟨⟨b⟩, bs, br⟩ := H ⟨a⟩
      ⟨b, bs, br⟩
  · rcases cof_eq r with ⟨S, H, e'⟩
    -- ⊢ cof (lift.{u, v} (type r)) ≤ Cardinal.lift.{u, v} (cof (type r))
    have : #(ULift.down.{u, v} ⁻¹' S) ≤ Cardinal.lift.{u, v} #S :=
      ⟨⟨fun ⟨⟨x⟩, h⟩ => ⟨⟨x, h⟩⟩, fun ⟨⟨x⟩, h₁⟩ ⟨⟨y⟩, h₂⟩ e => by
          simp at e; congr⟩⟩
    rw [e'] at this
    -- ⊢ cof (lift.{u, v} (type r)) ≤ Cardinal.lift.{u, v} (cof (type r))
    refine' (cof_type_le _).trans this
    -- ⊢ Unbounded (ULift.down ⁻¹'o { α := α, r := r, wo := inst✝ }.r) (ULift.down ⁻¹ …
    exact fun ⟨a⟩ =>
      let ⟨b, bs, br⟩ := H a
      ⟨⟨b⟩, bs, br⟩
#align ordinal.lift_cof Ordinal.lift_cof

theorem cof_le_card (o) : cof o ≤ card o := by
  rw [cof_eq_sInf_lsub]
  -- ⊢ sInf {a | ∃ ι f, lsub f = o ∧ #ι = a} ≤ card o
  exact csInf_le' card_mem_cof
  -- 🎉 no goals
#align ordinal.cof_le_card Ordinal.cof_le_card

theorem cof_ord_le (c : Cardinal) : c.ord.cof ≤ c := by simpa using cof_le_card c.ord
                                                        -- 🎉 no goals
#align ordinal.cof_ord_le Ordinal.cof_ord_le

theorem ord_cof_le (o : Ordinal.{u}) : o.cof.ord ≤ o :=
  (ord_le_ord.2 (cof_le_card o)).trans (ord_card_le o)
#align ordinal.ord_cof_le Ordinal.ord_cof_le

theorem exists_lsub_cof (o : Ordinal) :
    ∃ (ι : _) (f : ι → Ordinal), lsub.{u, u} f = o ∧ #ι = cof o := by
  rw [cof_eq_sInf_lsub]
  -- ⊢ ∃ ι f, lsub f = o ∧ #ι = sInf {a | ∃ ι f, lsub f = o ∧ #ι = a}
  exact csInf_mem (cof_lsub_def_nonempty o)
  -- 🎉 no goals
#align ordinal.exists_lsub_cof Ordinal.exists_lsub_cof

theorem cof_lsub_le {ι} (f : ι → Ordinal) : cof (lsub.{u, u} f) ≤ #ι := by
  rw [cof_eq_sInf_lsub]
  -- ⊢ sInf {a | ∃ ι_1 f_1, lsub f_1 = lsub f ∧ #ι_1 = a} ≤ #ι
  exact csInf_le' ⟨ι, f, rfl, rfl⟩
  -- 🎉 no goals
#align ordinal.cof_lsub_le Ordinal.cof_lsub_le

theorem cof_lsub_le_lift {ι} (f : ι → Ordinal) :
    cof (lsub.{u, v} f) ≤ Cardinal.lift.{v, u} #ι := by
  rw [← mk_uLift.{u, v}]
  -- ⊢ cof (lsub f) ≤ #(ULift ι)
  convert cof_lsub_le.{max u v} fun i : ULift.{v, u} ι => f i.down
  -- ⊢ lsub f = lsub fun i => f i.down
  exact
    lsub_eq_of_range_eq.{u, max u v, max u v}
      (Set.ext fun x => ⟨fun ⟨i, hi⟩ => ⟨ULift.up.{v, u} i, hi⟩, fun ⟨i, hi⟩ => ⟨_, hi⟩⟩)
#align ordinal.cof_lsub_le_lift Ordinal.cof_lsub_le_lift

theorem le_cof_iff_lsub {o : Ordinal} {a : Cardinal} :
    a ≤ cof o ↔ ∀ {ι} (f : ι → Ordinal), lsub.{u, u} f = o → a ≤ #ι := by
  rw [cof_eq_sInf_lsub]
  -- ⊢ a ≤ sInf {a | ∃ ι f, lsub f = o ∧ #ι = a} ↔ ∀ {ι : Type u} (f : ι → Ordinal. …
  exact
    (le_csInf_iff'' (cof_lsub_def_nonempty o)).trans
      ⟨fun H ι f hf => H _ ⟨ι, f, hf, rfl⟩, fun H b ⟨ι, f, hf, hb⟩ => by
        rw [← hb]
        exact H _ hf⟩
#align ordinal.le_cof_iff_lsub Ordinal.le_cof_iff_lsub

theorem lsub_lt_ord_lift {ι} {f : ι → Ordinal} {c : Ordinal}
    (hι : Cardinal.lift.{v, u} #ι < c.cof)
    (hf : ∀ i, f i < c) : lsub.{u, v} f < c :=
  lt_of_le_of_ne (lsub_le.{v, u} hf) fun h => by
    subst h
    -- ⊢ False
    exact (cof_lsub_le_lift.{u, v} f).not_lt hι
    -- 🎉 no goals
#align ordinal.lsub_lt_ord_lift Ordinal.lsub_lt_ord_lift

theorem lsub_lt_ord {ι} {f : ι → Ordinal} {c : Ordinal} (hι : #ι < c.cof) :
    (∀ i, f i < c) → lsub.{u, u} f < c :=
  lsub_lt_ord_lift (by rwa [(#ι).lift_id])
                       -- 🎉 no goals
#align ordinal.lsub_lt_ord Ordinal.lsub_lt_ord

theorem cof_sup_le_lift {ι} {f : ι → Ordinal} (H : ∀ i, f i < sup.{u, v} f) :
    cof (sup.{u, v} f) ≤ Cardinal.lift.{v, u} #ι := by
  rw [← sup_eq_lsub_iff_lt_sup.{u, v}] at H
  -- ⊢ cof (sup f) ≤ Cardinal.lift.{v, u} #ι
  rw [H]
  -- ⊢ cof (lsub fun i => f i) ≤ Cardinal.lift.{v, u} #ι
  exact cof_lsub_le_lift f
  -- 🎉 no goals
#align ordinal.cof_sup_le_lift Ordinal.cof_sup_le_lift

theorem cof_sup_le {ι} {f : ι → Ordinal} (H : ∀ i, f i < sup.{u, u} f) :
    cof (sup.{u, u} f) ≤ #ι := by
  rw [← (#ι).lift_id]
  -- ⊢ cof (sup f) ≤ Cardinal.lift.{u, u} #ι
  exact cof_sup_le_lift H
  -- 🎉 no goals
#align ordinal.cof_sup_le Ordinal.cof_sup_le

theorem sup_lt_ord_lift {ι} {f : ι → Ordinal} {c : Ordinal} (hι : Cardinal.lift.{v, u} #ι < c.cof)
    (hf : ∀ i, f i < c) : sup.{u, v} f < c :=
  (sup_le_lsub.{u, v} f).trans_lt (lsub_lt_ord_lift hι hf)
#align ordinal.sup_lt_ord_lift Ordinal.sup_lt_ord_lift

theorem sup_lt_ord {ι} {f : ι → Ordinal} {c : Ordinal} (hι : #ι < c.cof) :
    (∀ i, f i < c) → sup.{u, u} f < c :=
  sup_lt_ord_lift (by rwa [(#ι).lift_id])
                      -- 🎉 no goals
#align ordinal.sup_lt_ord Ordinal.sup_lt_ord

theorem iSup_lt_lift {ι} {f : ι → Cardinal} {c : Cardinal}
    (hι : Cardinal.lift.{v, u} #ι < c.ord.cof)
    (hf : ∀ i, f i < c) : iSup.{max u v + 1, u + 1} f < c := by
  rw [← ord_lt_ord, iSup_ord (Cardinal.bddAbove_range.{u, v} _)]
  -- ⊢ ⨆ (i : ι), ord (f i) < ord c
  refine' sup_lt_ord_lift hι fun i => _
  -- ⊢ ord (f i) < ord c
  rw [ord_lt_ord]
  -- ⊢ f i < c
  apply hf
  -- 🎉 no goals
#align ordinal.supr_lt_lift Ordinal.iSup_lt_lift

theorem iSup_lt {ι} {f : ι → Cardinal} {c : Cardinal} (hι : #ι < c.ord.cof) :
    (∀ i, f i < c) → iSup f < c :=
  iSup_lt_lift (by rwa [(#ι).lift_id])
                   -- 🎉 no goals
#align ordinal.supr_lt Ordinal.iSup_lt

theorem nfpFamily_lt_ord_lift {ι} {f : ι → Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c)
    (hc' : Cardinal.lift.{v, u} #ι < cof c) (hf : ∀ (i), ∀ b < c, f i b < c) {a} (ha : a < c) :
    nfpFamily.{u, v} f a < c := by
  refine' sup_lt_ord_lift ((Cardinal.lift_le.2 (mk_list_le_max ι)).trans_lt _) fun l => _
  -- ⊢ Cardinal.lift.{v, u} (max ℵ₀ #ι) < cof c
  · rw [lift_max]
    -- ⊢ max (Cardinal.lift.{v, u} ℵ₀) (Cardinal.lift.{v, u} #ι) < cof c
    apply max_lt _ hc'
    -- ⊢ Cardinal.lift.{v, u} ℵ₀ < cof c
    rwa [Cardinal.lift_aleph0]
    -- 🎉 no goals
  · induction' l with i l H
    -- ⊢ List.foldr f a [] < c
    · exact ha
      -- 🎉 no goals
    · exact hf _ _ H
      -- 🎉 no goals
#align ordinal.nfp_family_lt_ord_lift Ordinal.nfpFamily_lt_ord_lift

theorem nfpFamily_lt_ord {ι} {f : ι → Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c) (hc' : #ι < cof c)
    (hf : ∀ (i), ∀ b < c, f i b < c) {a} : a < c → nfpFamily.{u, u} f a < c :=
  nfpFamily_lt_ord_lift hc (by rwa [(#ι).lift_id]) hf
                               -- 🎉 no goals
#align ordinal.nfp_family_lt_ord Ordinal.nfpFamily_lt_ord

theorem nfpBFamily_lt_ord_lift {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c)
    (hc' : Cardinal.lift.{v, u} o.card < cof c) (hf : ∀ (i hi), ∀ b < c, f i hi b < c) {a} :
    a < c → nfpBFamily.{u, v} o f a < c :=
  nfpFamily_lt_ord_lift hc (by rwa [mk_ordinal_out]) fun i => hf _ _
                               -- 🎉 no goals
#align ordinal.nfp_bfamily_lt_ord_lift Ordinal.nfpBFamily_lt_ord_lift

theorem nfpBFamily_lt_ord {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c)
    (hc' : o.card < cof c) (hf : ∀ (i hi), ∀ b < c, f i hi b < c) {a} :
    a < c → nfpBFamily.{u, u} o f a < c :=
  nfpBFamily_lt_ord_lift hc (by rwa [o.card.lift_id]) hf
                                -- 🎉 no goals
#align ordinal.nfp_bfamily_lt_ord Ordinal.nfpBFamily_lt_ord

theorem nfp_lt_ord {f : Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c) (hf : ∀ i < c, f i < c) {a} :
    a < c → nfp f a < c :=
  nfpFamily_lt_ord_lift hc (by simpa using Cardinal.one_lt_aleph0.trans hc) fun _ => hf
                               -- 🎉 no goals
#align ordinal.nfp_lt_ord Ordinal.nfp_lt_ord

theorem exists_blsub_cof (o : Ordinal) :
    ∃ f : ∀ a < (cof o).ord, Ordinal, blsub.{u, u} _ f = o := by
  rcases exists_lsub_cof o with ⟨ι, f, hf, hι⟩
  -- ⊢ ∃ f, blsub (ord (cof o)) f = o
  rcases Cardinal.ord_eq ι with ⟨r, hr, hι'⟩
  -- ⊢ ∃ f, blsub (ord (cof o)) f = o
  rw [← @blsub_eq_lsub' ι r hr] at hf
  -- ⊢ ∃ f, blsub (ord (cof o)) f = o
  rw [← hι, hι']
  -- ⊢ ∃ f, blsub (type r) f = o
  exact ⟨_, hf⟩
  -- 🎉 no goals
#align ordinal.exists_blsub_cof Ordinal.exists_blsub_cof

theorem le_cof_iff_blsub {b : Ordinal} {a : Cardinal} :
    a ≤ cof b ↔ ∀ {o} (f : ∀ a < o, Ordinal), blsub.{u, u} o f = b → a ≤ o.card :=
  le_cof_iff_lsub.trans
    ⟨fun H o f hf => by simpa using H _ hf, fun H ι f hf => by
                        -- 🎉 no goals
      rcases Cardinal.ord_eq ι with ⟨r, hr, hι'⟩
      -- ⊢ a ≤ #ι
      rw [← @blsub_eq_lsub' ι r hr] at hf
      -- ⊢ a ≤ #ι
      simpa using H _ hf⟩
      -- 🎉 no goals
#align ordinal.le_cof_iff_blsub Ordinal.le_cof_iff_blsub

theorem cof_blsub_le_lift {o} (f : ∀ a < o, Ordinal) :
    cof (blsub.{u, v} o f) ≤ Cardinal.lift.{v, u} o.card := by
  rw [← mk_ordinal_out o]
  -- ⊢ cof (blsub o f) ≤ Cardinal.lift.{v, u} #(Quotient.out o).α
  exact cof_lsub_le_lift _
  -- 🎉 no goals
#align ordinal.cof_blsub_le_lift Ordinal.cof_blsub_le_lift

theorem cof_blsub_le {o} (f : ∀ a < o, Ordinal) : cof (blsub.{u, u} o f) ≤ o.card := by
  rw [← o.card.lift_id]
  -- ⊢ cof (blsub o f) ≤ Cardinal.lift.{u, u} (card o)
  exact cof_blsub_le_lift f
  -- 🎉 no goals
#align ordinal.cof_blsub_le Ordinal.cof_blsub_le

theorem blsub_lt_ord_lift {o : Ordinal.{u}} {f : ∀ a < o, Ordinal} {c : Ordinal}
    (ho : Cardinal.lift.{v, u} o.card < c.cof) (hf : ∀ i hi, f i hi < c) : blsub.{u, v} o f < c :=
  lt_of_le_of_ne (blsub_le hf) fun h =>
    ho.not_le (by simpa [← iSup_ord, hf, h] using cof_blsub_le_lift.{u, v} f)
                  -- 🎉 no goals
#align ordinal.blsub_lt_ord_lift Ordinal.blsub_lt_ord_lift

theorem blsub_lt_ord {o : Ordinal} {f : ∀ a < o, Ordinal} {c : Ordinal} (ho : o.card < c.cof)
    (hf : ∀ i hi, f i hi < c) : blsub.{u, u} o f < c :=
  blsub_lt_ord_lift (by rwa [o.card.lift_id]) hf
                        -- 🎉 no goals
#align ordinal.blsub_lt_ord Ordinal.blsub_lt_ord

theorem cof_bsup_le_lift {o : Ordinal} {f : ∀ a < o, Ordinal} (H : ∀ i h, f i h < bsup.{u, v} o f) :
    cof (bsup.{u, v} o f) ≤ Cardinal.lift.{v, u} o.card := by
  rw [← bsup_eq_blsub_iff_lt_bsup.{u, v}] at H
  -- ⊢ cof (bsup o f) ≤ Cardinal.lift.{v, u} (card o)
  rw [H]
  -- ⊢ cof (blsub o fun i h => f i h) ≤ Cardinal.lift.{v, u} (card o)
  exact cof_blsub_le_lift.{u, v} f
  -- 🎉 no goals
#align ordinal.cof_bsup_le_lift Ordinal.cof_bsup_le_lift

theorem cof_bsup_le {o : Ordinal} {f : ∀ a < o, Ordinal} :
    (∀ i h, f i h < bsup.{u, u} o f) → cof (bsup.{u, u} o f) ≤ o.card := by
  rw [← o.card.lift_id]
  -- ⊢ (∀ (i : Ordinal.{u}) (h : i < o), f i h < bsup o f) → cof (bsup o f) ≤ Cardi …
  exact cof_bsup_le_lift
  -- 🎉 no goals
#align ordinal.cof_bsup_le Ordinal.cof_bsup_le

theorem bsup_lt_ord_lift {o : Ordinal} {f : ∀ a < o, Ordinal} {c : Ordinal}
    (ho : Cardinal.lift.{v, u} o.card < c.cof) (hf : ∀ i hi, f i hi < c) : bsup.{u, v} o f < c :=
  (bsup_le_blsub f).trans_lt (blsub_lt_ord_lift ho hf)
#align ordinal.bsup_lt_ord_lift Ordinal.bsup_lt_ord_lift

theorem bsup_lt_ord {o : Ordinal} {f : ∀ a < o, Ordinal} {c : Ordinal} (ho : o.card < c.cof) :
    (∀ i hi, f i hi < c) → bsup.{u, u} o f < c :=
  bsup_lt_ord_lift (by rwa [o.card.lift_id])
                       -- 🎉 no goals
#align ordinal.bsup_lt_ord Ordinal.bsup_lt_ord

/-! ### Basic results -/


@[simp]
theorem cof_zero : cof 0 = 0 := by
  refine LE.le.antisymm  ?_ (Cardinal.zero_le _)
  -- ⊢ cof 0 ≤ 0
  rw [← card_zero]
  -- ⊢ cof 0 ≤ card 0
  exact cof_le_card 0
  -- 🎉 no goals
#align ordinal.cof_zero Ordinal.cof_zero

@[simp]
theorem cof_eq_zero {o} : cof o = 0 ↔ o = 0 :=
  ⟨inductionOn o fun α r _ z =>
      let ⟨S, hl, e⟩ := cof_eq r
      type_eq_zero_iff_isEmpty.2 <|
        ⟨fun a =>
          let ⟨b, h, _⟩ := hl a
          (mk_eq_zero_iff.1 (e.trans z)).elim' ⟨_, h⟩⟩,
    fun e => by simp [e]⟩
                -- 🎉 no goals
#align ordinal.cof_eq_zero Ordinal.cof_eq_zero

theorem cof_ne_zero {o} : cof o ≠ 0 ↔ o ≠ 0 :=
  cof_eq_zero.not
#align ordinal.cof_ne_zero Ordinal.cof_ne_zero

@[simp]
theorem cof_succ (o) : cof (succ o) = 1 := by
  apply le_antisymm
  -- ⊢ cof (succ o) ≤ 1
  · refine' inductionOn o fun α r _ => _
    -- ⊢ cof (succ (type r)) ≤ 1
    change cof (type _) ≤ _
    -- ⊢ cof (type (Sum.Lex r EmptyRelation)) ≤ 1
    rw [← (_ : #_ = 1)]
    apply cof_type_le
    · refine' fun a => ⟨Sum.inr PUnit.unit, Set.mem_singleton _, _⟩
      -- ⊢ ¬Sum.Lex r EmptyRelation (Sum.inr PUnit.unit) a
      rcases a with (a | ⟨⟨⟨⟩⟩⟩) <;> simp [EmptyRelation]
      -- ⊢ ¬Sum.Lex r EmptyRelation (Sum.inr PUnit.unit) (Sum.inl a)
                                     -- 🎉 no goals
                                     -- 🎉 no goals
    · rw [Cardinal.mk_fintype, Set.card_singleton]
      -- ⊢ ↑1 = 1
      simp
      -- 🎉 no goals
  · rw [← Cardinal.succ_zero, succ_le_iff]
    -- ⊢ 0 < cof (succ o)
    simpa [lt_iff_le_and_ne, Cardinal.zero_le] using fun h =>
      succ_ne_zero o (cof_eq_zero.1 (Eq.symm h))
#align ordinal.cof_succ Ordinal.cof_succ

@[simp]
theorem cof_eq_one_iff_is_succ {o} : cof.{u} o = 1 ↔ ∃ a, o = succ a :=
  ⟨inductionOn o fun α r _ z => by
      skip
      -- ⊢ ∃ a, type r = succ a
      rcases cof_eq r with ⟨S, hl, e⟩; rw [z] at e
      -- ⊢ ∃ a, type r = succ a
                                       -- ⊢ ∃ a, type r = succ a
      cases' mk_ne_zero_iff.1 (by rw [e]; exact one_ne_zero) with a
      -- ⊢ ∃ a, type r = succ a
      refine'
        ⟨typein r a,
          Eq.symm <|
            Quotient.sound
              ⟨RelIso.ofSurjective (RelEmbedding.ofMonotone _ fun x y => _) fun x => _⟩⟩
      · apply Sum.rec <;> [exact Subtype.val; exact fun _ => a]
        -- 🎉 no goals
      · rcases x with (x | ⟨⟨⟨⟩⟩⟩) <;> rcases y with (y | ⟨⟨⟨⟩⟩⟩) <;>
        -- ⊢ Sum.Lex (Subrel r {b | r b ↑a}) EmptyRelation (Sum.inl x) y → r (Sum.rec Sub …
                                       -- ⊢ Sum.Lex (Subrel r {b | r b ↑a}) EmptyRelation (Sum.inl x) (Sum.inl y) → r (S …
                                       -- ⊢ Sum.Lex (Subrel r {b | r b ↑a}) EmptyRelation (Sum.inr PUnit.unit) (Sum.inl  …
          simp [Subrel, Order.Preimage, EmptyRelation]
          -- 🎉 no goals
          -- ⊢ r ↑x ↑a
          -- 🎉 no goals
          -- 🎉 no goals
        exact x.2
        -- 🎉 no goals
      · suffices : r x a ∨ ∃ _ : PUnit.{u}, ↑a = x
        -- ⊢ ∃ a_1, ↑(RelEmbedding.ofMonotone (Sum.rec Subtype.val fun x => ↑a) (_ : ∀ (x …
        · convert this
          -- ⊢ (∃ a_1, ↑(RelEmbedding.ofMonotone (Sum.rec Subtype.val fun x => ↑a) (_ : ∀ ( …
          dsimp [RelEmbedding.ofMonotone]; simp
          -- ⊢ (∃ a_1, Sum.rec Subtype.val (fun x => ↑a) a_1 = x) ↔ r x ↑a ∨ ∃ x_1, ↑a = x
                                           -- 🎉 no goals
        rcases trichotomous_of r x a with (h | h | h)
        · exact Or.inl h
          -- 🎉 no goals
        · exact Or.inr ⟨PUnit.unit, h.symm⟩
          -- 🎉 no goals
        · rcases hl x with ⟨a', aS, hn⟩
          -- ⊢ r x ↑a ∨ ∃ x_1, ↑a = x
          rw [(_ : ↑a = a')] at h
          -- ⊢ r x ↑a ∨ ∃ x_1, ↑a = x
          · exact absurd h hn
            -- 🎉 no goals
          refine' congr_arg Subtype.val (_ : a = ⟨a', aS⟩)
          -- ⊢ a = { val := a', property := aS }
          haveI := le_one_iff_subsingleton.1 (le_of_eq e)
          -- ⊢ a = { val := a', property := aS }
          apply Subsingleton.elim,
          -- 🎉 no goals
    fun ⟨a, e⟩ => by simp [e]⟩
                     -- 🎉 no goals
#align ordinal.cof_eq_one_iff_is_succ Ordinal.cof_eq_one_iff_is_succ

/-- A fundamental sequence for `a` is an increasing sequence of length `o = cof a` that converges at
    `a`. We provide `o` explicitly in order to avoid type rewrites. -/
def IsFundamentalSequence (a o : Ordinal.{u}) (f : ∀ b < o, Ordinal.{u}) : Prop :=
  o ≤ a.cof.ord ∧ (∀ {i j} (hi hj), i < j → f i hi < f j hj) ∧ blsub.{u, u} o f = a
#align ordinal.is_fundamental_sequence Ordinal.IsFundamentalSequence

namespace IsFundamentalSequence

variable {a o : Ordinal.{u}} {f : ∀ b < o, Ordinal.{u}}

protected theorem cof_eq (hf : IsFundamentalSequence a o f) : a.cof.ord = o :=
  hf.1.antisymm' <| by
    rw [← hf.2.2]
    -- ⊢ ord (cof (blsub o f)) ≤ o
    exact (ord_le_ord.2 (cof_blsub_le f)).trans (ord_card_le o)
    -- 🎉 no goals
#align ordinal.is_fundamental_sequence.cof_eq Ordinal.IsFundamentalSequence.cof_eq

protected theorem strict_mono (hf : IsFundamentalSequence a o f) {i j} :
    ∀ hi hj, i < j → f i hi < f j hj :=
  hf.2.1
#align ordinal.is_fundamental_sequence.strict_mono Ordinal.IsFundamentalSequence.strict_mono

theorem blsub_eq (hf : IsFundamentalSequence a o f) : blsub.{u, u} o f = a :=
  hf.2.2
#align ordinal.is_fundamental_sequence.blsub_eq Ordinal.IsFundamentalSequence.blsub_eq

theorem ord_cof (hf : IsFundamentalSequence a o f) :
    IsFundamentalSequence a a.cof.ord fun i hi => f i (hi.trans_le (by rw [hf.cof_eq])) := by
                                                                       -- 🎉 no goals
  have H := hf.cof_eq
  -- ⊢ IsFundamentalSequence a (ord (cof a)) fun i hi => f i (_ : i < o)
  subst H
  -- ⊢ IsFundamentalSequence a (ord (cof a)) fun i hi => f i (_ : i < ord (cof a))
  exact hf
  -- 🎉 no goals
#align ordinal.is_fundamental_sequence.ord_cof Ordinal.IsFundamentalSequence.ord_cof

theorem id_of_le_cof (h : o ≤ o.cof.ord) : IsFundamentalSequence o o fun a _ => a :=
  ⟨h, @fun _ _ _ _ => id, blsub_id o⟩
#align ordinal.is_fundamental_sequence.id_of_le_cof Ordinal.IsFundamentalSequence.id_of_le_cof

protected theorem zero {f : ∀ b < (0 : Ordinal), Ordinal} : IsFundamentalSequence 0 0 f :=
  ⟨by rw [cof_zero, ord_zero], @fun i j hi => (Ordinal.not_lt_zero i hi).elim, blsub_zero f⟩
      -- 🎉 no goals
#align ordinal.is_fundamental_sequence.zero Ordinal.IsFundamentalSequence.zero

protected theorem succ : IsFundamentalSequence (succ o) 1 fun _ _ => o := by
  refine' ⟨_, @fun i j hi hj h => _, blsub_const Ordinal.one_ne_zero o⟩
  -- ⊢ 1 ≤ ord (cof (succ o))
  · rw [cof_succ, ord_one]
    -- 🎉 no goals
  · rw [lt_one_iff_zero] at hi hj
    -- ⊢ (fun x x => o) i hi✝ < (fun x x => o) j hj✝
    rw [hi, hj] at h
    -- ⊢ (fun x x => o) i hi✝ < (fun x x => o) j hj✝
    exact h.false.elim
    -- 🎉 no goals
#align ordinal.is_fundamental_sequence.succ Ordinal.IsFundamentalSequence.succ

protected theorem monotone (hf : IsFundamentalSequence a o f) {i j : Ordinal} (hi : i < o)
    (hj : j < o) (hij : i ≤ j) : f i hi ≤ f j hj := by
  rcases lt_or_eq_of_le hij with (hij | rfl)
  -- ⊢ f i hi ≤ f j hj
  · exact (hf.2.1 hi hj hij).le
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align ordinal.is_fundamental_sequence.monotone Ordinal.IsFundamentalSequence.monotone

theorem trans {a o o' : Ordinal.{u}} {f : ∀ b < o, Ordinal.{u}} (hf : IsFundamentalSequence a o f)
    {g : ∀ b < o', Ordinal.{u}} (hg : IsFundamentalSequence o o' g) :
    IsFundamentalSequence a o' fun i hi =>
      f (g i hi) (by rw [← hg.2.2]; apply lt_blsub) := by
                     -- ⊢ g i hi < blsub o' g
                                    -- 🎉 no goals
  refine' ⟨_, @fun i j _ _ h => hf.2.1 _ _ (hg.2.1 _ _ h), _⟩
  -- ⊢ o' ≤ ord (cof a)
  · rw [hf.cof_eq]
    -- ⊢ o' ≤ o
    exact hg.1.trans (ord_cof_le o)
    -- 🎉 no goals
  · rw [@blsub_comp.{u, u, u} o _ f (@IsFundamentalSequence.monotone _ _ f hf)]
    -- ⊢ blsub o f = a
    exact hf.2.2
    -- ⊢ (blsub o' fun i hi => g i hi) = o
    exact hg.2.2
    -- 🎉 no goals
#align ordinal.is_fundamental_sequence.trans Ordinal.IsFundamentalSequence.trans

end IsFundamentalSequence

/-- Every ordinal has a fundamental sequence. -/
theorem exists_fundamental_sequence (a : Ordinal.{u}) :
    ∃ f, IsFundamentalSequence a a.cof.ord f := by
  suffices h : ∃ o f, IsFundamentalSequence a o f
  -- ⊢ ∃ f, IsFundamentalSequence a (ord (cof a)) f
  · rcases h with ⟨o, f, hf⟩
    -- ⊢ ∃ f, IsFundamentalSequence a (ord (cof a)) f
    exact ⟨_, hf.ord_cof⟩
    -- 🎉 no goals
  rcases exists_lsub_cof a with ⟨ι, f, hf, hι⟩
  -- ⊢ ∃ o f, IsFundamentalSequence a o f
  rcases ord_eq ι with ⟨r, wo, hr⟩
  -- ⊢ ∃ o f, IsFundamentalSequence a o f
  haveI := wo
  -- ⊢ ∃ o f, IsFundamentalSequence a o f
  let r' := Subrel r { i | ∀ j, r j i → f j < f i }
  -- ⊢ ∃ o f, IsFundamentalSequence a o f
  let hrr' : r' ↪r r := Subrel.relEmbedding _ _
  -- ⊢ ∃ o f, IsFundamentalSequence a o f
  haveI := hrr'.isWellOrder
  -- ⊢ ∃ o f, IsFundamentalSequence a o f
  refine'
    ⟨_, _, hrr'.ordinal_type_le.trans _, @fun i j _ h _ => (enum r' j h).prop _ _,
      le_antisymm (blsub_le fun i hi => lsub_le_iff.1 hf.le _) _⟩
  · rw [← hι, hr]
    -- 🎉 no goals
  · change r (hrr'.1 _) (hrr'.1 _)
    -- ⊢ r (↑hrr'.toEmbedding (enum r' i x✝¹)) (↑hrr'.toEmbedding (enum r' j h))
    rwa [hrr'.2, @enum_lt_enum _ r']
    -- 🎉 no goals
  · rw [← hf, lsub_le_iff]
    -- ⊢ ∀ (i : ι), f i < blsub (type r') fun j h => f ↑(enum r' j h)
    intro i
    -- ⊢ f i < blsub (type r') fun j h => f ↑(enum r' j h)
    suffices h : ∃ i' hi', f i ≤ bfamilyOfFamily' r' (fun i => f i) i' hi'
    -- ⊢ f i < blsub (type r') fun j h => f ↑(enum r' j h)
    · rcases h with ⟨i', hi', hfg⟩
      -- ⊢ f i < blsub (type r') fun j h => f ↑(enum r' j h)
      exact hfg.trans_lt (lt_blsub _ _ _)
      -- 🎉 no goals
    by_cases h : ∀ j, r j i → f j < f i
    -- ⊢ ∃ i' hi', f i ≤ bfamilyOfFamily' r' (fun i => f ↑i) i' hi'
    · refine' ⟨typein r' ⟨i, h⟩, typein_lt_type _ _, _⟩
      -- ⊢ f i ≤ bfamilyOfFamily' r' (fun i => f ↑i) (typein r' { val := i, property := …
      rw [bfamilyOfFamily'_typein]
      -- 🎉 no goals
    · push_neg at h
      -- ⊢ ∃ i' hi', f i ≤ bfamilyOfFamily' r' (fun i => f ↑i) i' hi'
      cases' wo.wf.min_mem _ h with hji hij
      -- ⊢ ∃ i' hi', f i ≤ bfamilyOfFamily' r' (fun i => f ↑i) i' hi'
      refine' ⟨typein r' ⟨_, fun k hkj => lt_of_lt_of_le _ hij⟩, typein_lt_type _ _, _⟩
      -- ⊢ f k < f i
      · by_contra' H
        -- ⊢ False
        exact (wo.wf.not_lt_min _ h ⟨IsTrans.trans _ _ _ hkj hji, H⟩) hkj
        -- 🎉 no goals
      · rwa [bfamilyOfFamily'_typein]
        -- 🎉 no goals
#align ordinal.exists_fundamental_sequence Ordinal.exists_fundamental_sequence

@[simp]
theorem cof_cof (a : Ordinal.{u}) : cof (cof a).ord = cof a := by
  cases' exists_fundamental_sequence a with f hf
  -- ⊢ cof (ord (cof a)) = cof a
  cases' exists_fundamental_sequence a.cof.ord with g hg
  -- ⊢ cof (ord (cof a)) = cof a
  exact ord_injective (hf.trans hg).cof_eq.symm
  -- 🎉 no goals
#align ordinal.cof_cof Ordinal.cof_cof

protected theorem IsNormal.isFundamentalSequence {f : Ordinal.{u} → Ordinal.{u}} (hf : IsNormal f)
    {a o} (ha : IsLimit a) {g} (hg : IsFundamentalSequence a o g) :
    IsFundamentalSequence (f a) o fun b hb => f (g b hb) := by
  refine' ⟨_, @fun i j _ _ h => hf.strictMono (hg.2.1 _ _ h), _⟩
  -- ⊢ o ≤ ord (cof (f a))
  · rcases exists_lsub_cof (f a) with ⟨ι, f', hf', hι⟩
    -- ⊢ o ≤ ord (cof (f a))
    rw [← hg.cof_eq, ord_le_ord, ← hι]
    -- ⊢ cof a ≤ #ι
    suffices (lsub.{u, u} fun i => sInf { b : Ordinal | f' i ≤ f b }) = a by
      rw [← this]
      apply cof_lsub_le
    have H : ∀ i, ∃ b < a, f' i ≤ f b := fun i => by
      have := lt_lsub.{u, u} f' i
      rw [hf', ← IsNormal.blsub_eq.{u, u} hf ha, lt_blsub_iff] at this
      simpa using this
    refine' (lsub_le fun i => _).antisymm (le_of_forall_lt fun b hb => _)
    -- ⊢ sInf {b | f' i ≤ f b} < a
    · rcases H i with ⟨b, hb, hb'⟩
      -- ⊢ sInf {b | f' i ≤ f b} < a
      exact lt_of_le_of_lt (csInf_le' hb') hb
      -- 🎉 no goals
    · have := hf.strictMono hb
      -- ⊢ b < lsub fun i => sInf {b | f' i ≤ f b}
      rw [← hf', lt_lsub_iff] at this
      -- ⊢ b < lsub fun i => sInf {b | f' i ≤ f b}
      cases' this with i hi
      -- ⊢ b < lsub fun i => sInf {b | f' i ≤ f b}
      rcases H i with ⟨b, _, hb⟩
      -- ⊢ b✝ < lsub fun i => sInf {b | f' i ≤ f b}
      exact
        ((le_csInf_iff'' ⟨b, by exact hb⟩).2 fun c hc =>
          hf.strictMono.le_iff_le.1 (hi.trans hc)).trans_lt (lt_lsub _ i)
  · rw [@blsub_comp.{u, u, u} a _ (fun b _ => f b) (@fun i j _ _ h => hf.strictMono.monotone h) g
        hg.2.2]
    exact IsNormal.blsub_eq.{u, u} hf ha
    -- 🎉 no goals
#align ordinal.is_normal.is_fundamental_sequence Ordinal.IsNormal.isFundamentalSequence

theorem IsNormal.cof_eq {f} (hf : IsNormal f) {a} (ha : IsLimit a) : cof (f a) = cof a :=
  let ⟨_, hg⟩ := exists_fundamental_sequence a
  ord_injective (hf.isFundamentalSequence ha hg).cof_eq
#align ordinal.is_normal.cof_eq Ordinal.IsNormal.cof_eq

theorem IsNormal.cof_le {f} (hf : IsNormal f) (a) : cof a ≤ cof (f a) := by
  rcases zero_or_succ_or_limit a with (rfl | ⟨b, rfl⟩ | ha)
  · rw [cof_zero]
    -- ⊢ 0 ≤ cof (f 0)
    exact zero_le _
    -- 🎉 no goals
  · rw [cof_succ, Cardinal.one_le_iff_ne_zero, cof_ne_zero, ← Ordinal.pos_iff_ne_zero]
    -- ⊢ 0 < f (succ b)
    exact (Ordinal.zero_le (f b)).trans_lt (hf.1 b)
    -- 🎉 no goals
  · rw [hf.cof_eq ha]
    -- 🎉 no goals
#align ordinal.is_normal.cof_le Ordinal.IsNormal.cof_le

@[simp]
theorem cof_add (a b : Ordinal) : b ≠ 0 → cof (a + b) = cof b := fun h => by
  rcases zero_or_succ_or_limit b with (rfl | ⟨c, rfl⟩ | hb)
  · contradiction
    -- 🎉 no goals
  · rw [add_succ, cof_succ, cof_succ]
    -- 🎉 no goals
  · exact (add_isNormal a).cof_eq hb
    -- 🎉 no goals
#align ordinal.cof_add Ordinal.cof_add

theorem aleph0_le_cof {o} : ℵ₀ ≤ cof o ↔ IsLimit o := by
  rcases zero_or_succ_or_limit o with (rfl | ⟨o, rfl⟩ | l)
  · simp [not_zero_isLimit, Cardinal.aleph0_ne_zero]
    -- 🎉 no goals
  · simp [not_succ_isLimit, Cardinal.one_lt_aleph0]
    -- 🎉 no goals
  · simp [l]
    -- ⊢ ℵ₀ ≤ cof o
    refine' le_of_not_lt fun h => _
    -- ⊢ False
    cases' Cardinal.lt_aleph0.1 h with n e
    -- ⊢ False
    have := cof_cof o
    -- ⊢ False
    rw [e, ord_nat] at this
    -- ⊢ False
    cases n
    -- ⊢ False
    · simp at e
      -- ⊢ False
      simp [e, not_zero_isLimit] at l
      -- 🎉 no goals
    · rw [nat_cast_succ, cof_succ] at this
      -- ⊢ False
      rw [← this, cof_eq_one_iff_is_succ] at e
      -- ⊢ False
      rcases e with ⟨a, rfl⟩
      -- ⊢ False
      exact not_succ_isLimit _ l
      -- 🎉 no goals
#align ordinal.aleph_0_le_cof Ordinal.aleph0_le_cof

@[simp]
theorem aleph'_cof {o : Ordinal} (ho : o.IsLimit) : (aleph' o).ord.cof = o.cof :=
  aleph'_isNormal.cof_eq ho
#align ordinal.aleph'_cof Ordinal.aleph'_cof

@[simp]
theorem aleph_cof {o : Ordinal} (ho : o.IsLimit) : (aleph o).ord.cof = o.cof :=
  aleph_isNormal.cof_eq ho
#align ordinal.aleph_cof Ordinal.aleph_cof

@[simp]
theorem cof_omega : cof ω = ℵ₀ :=
  (aleph0_le_cof.2 omega_isLimit).antisymm' <| by
    rw [← card_omega]
    -- ⊢ cof ω ≤ card ω
    apply cof_le_card
    -- 🎉 no goals
#align ordinal.cof_omega Ordinal.cof_omega

theorem cof_eq' (r : α → α → Prop) [IsWellOrder α r] (h : IsLimit (type r)) :
    ∃ S : Set α, (∀ a, ∃ b ∈ S, r a b) ∧ #S = cof (type r) :=
  let ⟨S, H, e⟩ := cof_eq r
  ⟨S, fun a =>
    let a' := enum r _ (h.2 _ (typein_lt_type r a))
    let ⟨b, h, ab⟩ := H a'
    ⟨b, h,
      (IsOrderConnected.conn a b a' <|
            (typein_lt_typein r).1
              (by
                rw [typein_enum]
                -- ⊢ typein r a < succ (typein r a)
                exact lt_succ (typein _ _))).resolve_right
                -- 🎉 no goals
        ab⟩,
    e⟩
#align ordinal.cof_eq' Ordinal.cof_eq'

@[simp]
theorem cof_univ : cof univ.{u, v} = Cardinal.univ.{u, v} :=
  le_antisymm (cof_le_card _)
    (by
      refine' le_of_forall_lt fun c h => _
      -- ⊢ c < cof univ
      rcases lt_univ'.1 h with ⟨c, rfl⟩
      -- ⊢ Cardinal.lift.{max (u + 1) v, u} c < cof univ
      rcases @cof_eq Ordinal.{u} (· < ·) _ with ⟨S, H, Se⟩
      -- ⊢ Cardinal.lift.{max (u + 1) v, u} c < cof univ
      rw [univ, ← lift_cof, ← Cardinal.lift_lift.{u+1, v, u}, Cardinal.lift_lt, ← Se]
      -- ⊢ Cardinal.lift.{u + 1, u} c < #↑S
      refine' lt_of_not_ge fun h => _
      -- ⊢ False
      cases' Cardinal.lift_down h with a e
      -- ⊢ False
      refine' Quotient.inductionOn a (fun α e => _) e
      -- ⊢ False
      cases' Quotient.exact e with f
      -- ⊢ False
      have f := Equiv.ulift.symm.trans f
      -- ⊢ False
      let g a := (f a).1
      -- ⊢ False
      let o := succ (sup.{u, u} g)
      -- ⊢ False
      rcases H o with ⟨b, h, l⟩
      -- ⊢ False
      refine' l (lt_succ_iff.2 _)
      -- ⊢ b ≤ sup g
      rw [← show g (f.symm ⟨b, h⟩) = b by simp]
      -- ⊢ g (↑f.symm { val := b, property := h }) ≤ sup g
      apply le_sup)
      -- 🎉 no goals
#align ordinal.cof_univ Ordinal.cof_univ

/-! ### Infinite pigeonhole principle -/


/-- If the union of s is unbounded and s is smaller than the cofinality,
  then s has an unbounded member -/
theorem unbounded_of_unbounded_sUnion (r : α → α → Prop) [wo : IsWellOrder α r] {s : Set (Set α)}
    (h₁ : Unbounded r <| ⋃₀ s) (h₂ : #s < StrictOrder.cof r) : ∃ x ∈ s, Unbounded r x := by
  by_contra' h
  -- ⊢ False
  simp_rw [not_unbounded_iff] at h
  -- ⊢ False
  let f : s → α := fun x : s => wo.wf.sup x (h x.1 x.2)
  -- ⊢ False
  refine' h₂.not_le (le_trans (csInf_le' ⟨range f, fun x => _, rfl⟩) mk_range_le)
  -- ⊢ ∃ b, b ∈ range f ∧ swap rᶜ x b
  rcases h₁ x with ⟨y, ⟨c, hc, hy⟩, hxy⟩
  -- ⊢ ∃ b, b ∈ range f ∧ swap rᶜ x b
  exact ⟨f ⟨c, hc⟩, mem_range_self _, fun hxz => hxy (Trans.trans (wo.wf.lt_sup _ hy) hxz)⟩
  -- 🎉 no goals
#align ordinal.unbounded_of_unbounded_sUnion Ordinal.unbounded_of_unbounded_sUnion

/-- If the union of s is unbounded and s is smaller than the cofinality,
  then s has an unbounded member -/
theorem unbounded_of_unbounded_iUnion {α β : Type u} (r : α → α → Prop) [wo : IsWellOrder α r]
    (s : β → Set α) (h₁ : Unbounded r <| ⋃ x, s x) (h₂ : #β < StrictOrder.cof r) :
    ∃ x : β, Unbounded r (s x) := by
  rw [← sUnion_range] at h₁
  -- ⊢ ∃ x, Unbounded r (s x)
  rcases unbounded_of_unbounded_sUnion r h₁ (mk_range_le.trans_lt h₂) with ⟨_, ⟨x, rfl⟩, u⟩
  -- ⊢ ∃ x, Unbounded r (s x)
  exact ⟨x, u⟩
  -- 🎉 no goals
#align ordinal.unbounded_of_unbounded_Union Ordinal.unbounded_of_unbounded_iUnion

/-- The infinite pigeonhole principle -/
theorem infinite_pigeonhole {β α : Type u} (f : β → α) (h₁ : ℵ₀ ≤ #β) (h₂ : #α < (#β).ord.cof) :
    ∃ a : α, #(f ⁻¹' {a}) = #β := by
  have : ∃ a, #β ≤ #(f ⁻¹' {a}) := by
    by_contra' h
    apply mk_univ.not_lt
    rw [← preimage_univ, ← iUnion_of_singleton, preimage_iUnion]
    exact
      mk_iUnion_le_sum_mk.trans_lt
        ((sum_le_iSup _).trans_lt <| mul_lt_of_lt h₁ (h₂.trans_le <| cof_ord_le _) (iSup_lt h₂ h))
  cases' this with x h
  -- ⊢ ∃ a, #↑(f ⁻¹' {a}) = #β
  refine' ⟨x, h.antisymm' _⟩
  -- ⊢ #↑(f ⁻¹' {x}) ≤ #β
  rw [le_mk_iff_exists_set]
  -- ⊢ ∃ p, #↑p = #↑(f ⁻¹' {x})
  exact ⟨_, rfl⟩
  -- 🎉 no goals
#align ordinal.infinite_pigeonhole Ordinal.infinite_pigeonhole

/-- Pigeonhole principle for a cardinality below the cardinality of the domain -/
theorem infinite_pigeonhole_card {β α : Type u} (f : β → α) (θ : Cardinal) (hθ : θ ≤ #β)
    (h₁ : ℵ₀ ≤ θ) (h₂ : #α < θ.ord.cof) : ∃ a : α, θ ≤ #(f ⁻¹' {a}) := by
  rcases le_mk_iff_exists_set.1 hθ with ⟨s, rfl⟩
  -- ⊢ ∃ a, #↑s ≤ #↑(f ⁻¹' {a})
  cases' infinite_pigeonhole (f ∘ Subtype.val : s → α) h₁ h₂ with a ha
  -- ⊢ ∃ a, #↑s ≤ #↑(f ⁻¹' {a})
  use a; rw [← ha, @preimage_comp _ _ _ Subtype.val f]
  -- ⊢ #↑s ≤ #↑(f ⁻¹' {a})
         -- ⊢ #↑(Subtype.val ⁻¹' (f ⁻¹' {a})) ≤ #↑(f ⁻¹' {a})
  exact mk_preimage_of_injective _ _ Subtype.val_injective
  -- 🎉 no goals
#align ordinal.infinite_pigeonhole_card Ordinal.infinite_pigeonhole_card

theorem infinite_pigeonhole_set {β α : Type u} {s : Set β} (f : s → α) (θ : Cardinal)
    (hθ : θ ≤ #s) (h₁ : ℵ₀ ≤ θ) (h₂ : #α < θ.ord.cof) :
    ∃ (a : α) (t : Set β) (h : t ⊆ s), θ ≤ #t ∧ ∀ ⦃x⦄ (hx : x ∈ t), f ⟨x, h hx⟩ = a := by
  cases' infinite_pigeonhole_card f θ hθ h₁ h₂ with a ha
  -- ⊢ ∃ a t h, θ ≤ #↑t ∧ ∀ ⦃x : β⦄ (hx : x ∈ t), f { val := x, property := (_ : x  …
  refine' ⟨a, { x | ∃ h, f ⟨x, h⟩ = a }, _, _, _⟩
  · rintro x ⟨hx, _⟩
    -- ⊢ x ∈ s
    exact hx
    -- 🎉 no goals
  · refine'
      ha.trans
        (ge_of_eq <|
          Quotient.sound ⟨Equiv.trans _ (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm⟩)
    simp only [coe_eq_subtype, mem_singleton_iff, mem_preimage, mem_setOf_eq]
    -- ⊢ { x // ∃ h, f { val := x, property := h } = a } ≃ { a_1 // ∃ h, f { val := a …
    rfl
    -- 🎉 no goals
  rintro x ⟨_, hx'⟩; exact hx'
  -- ⊢ f { val := x, property := (_ : x ∈ s) } = a
                     -- 🎉 no goals
#align ordinal.infinite_pigeonhole_set Ordinal.infinite_pigeonhole_set

end Ordinal

/-! ### Regular and inaccessible cardinals -/


namespace Cardinal

open Ordinal

--Porting note: commented out, doesn't seem necessary
-- mathport name: cardinal.pow
--local infixr:0 "^" => @HPow.hPow Cardinal Cardinal Cardinal instHPow

/-- A cardinal is a strong limit if it is not zero and it is
  closed under powersets. Note that `ℵ₀` is a strong limit by this definition. -/
def IsStrongLimit (c : Cardinal) : Prop :=
  c ≠ 0 ∧ ∀ x < c, (2^x) < c
#align cardinal.is_strong_limit Cardinal.IsStrongLimit

theorem IsStrongLimit.ne_zero {c} (h : IsStrongLimit c) : c ≠ 0 :=
  h.1
#align cardinal.is_strong_limit.ne_zero Cardinal.IsStrongLimit.ne_zero

theorem IsStrongLimit.two_power_lt {x c} (h : IsStrongLimit c) : x < c → (2^x) < c :=
  h.2 x
#align cardinal.is_strong_limit.two_power_lt Cardinal.IsStrongLimit.two_power_lt

theorem isStrongLimit_aleph0 : IsStrongLimit ℵ₀ :=
  ⟨aleph0_ne_zero, fun x hx => by
    rcases lt_aleph0.1 hx with ⟨n, rfl⟩
    -- ⊢ 2 ^ ↑n < ℵ₀
    exact_mod_cast nat_lt_aleph0 (2 ^ n)⟩
    -- 🎉 no goals
#align cardinal.is_strong_limit_aleph_0 Cardinal.isStrongLimit_aleph0

protected theorem IsStrongLimit.isSuccLimit {c} (H : IsStrongLimit c) : IsSuccLimit c :=
  isSuccLimit_of_succ_lt fun x h => (succ_le_of_lt <| cantor x).trans_lt (H.two_power_lt h)
#align cardinal.is_strong_limit.is_succ_limit Cardinal.IsStrongLimit.isSuccLimit

theorem IsStrongLimit.isLimit {c} (H : IsStrongLimit c) : IsLimit c :=
  ⟨H.ne_zero, H.isSuccLimit⟩
#align cardinal.is_strong_limit.is_limit Cardinal.IsStrongLimit.isLimit

theorem isStrongLimit_beth {o : Ordinal} (H : IsSuccLimit o) : IsStrongLimit (beth o) := by
  rcases eq_or_ne o 0 with (rfl | h)
  -- ⊢ IsStrongLimit (beth 0)
  · rw [beth_zero]
    -- ⊢ IsStrongLimit ℵ₀
    exact isStrongLimit_aleph0
    -- 🎉 no goals
  · refine' ⟨beth_ne_zero o, fun a ha => _⟩
    -- ⊢ 2 ^ a < beth o
    rw [beth_limit ⟨h, isSuccLimit_iff_succ_lt.1 H⟩] at ha
    -- ⊢ 2 ^ a < beth o
    rcases exists_lt_of_lt_ciSup' ha with ⟨⟨i, hi⟩, ha⟩
    -- ⊢ 2 ^ a < beth o
    have := power_le_power_left two_ne_zero ha.le
    -- ⊢ 2 ^ a < beth o
    rw [← beth_succ] at this
    -- ⊢ 2 ^ a < beth o
    exact this.trans_lt (beth_lt.2 (H.succ_lt hi))
    -- 🎉 no goals
#align cardinal.is_strong_limit_beth Cardinal.isStrongLimit_beth

theorem mk_bounded_subset {α : Type*} (h : ∀ x < #α, (2^x) < #α) {r : α → α → Prop}
    [IsWellOrder α r] (hr : (#α).ord = type r) : #{ s : Set α // Bounded r s } = #α := by
  rcases eq_or_ne #α 0 with (ha | ha)
  -- ⊢ #{ s // Bounded r s } = #α
  · rw [ha]
    -- ⊢ #{ s // Bounded r s } = 0
    haveI := mk_eq_zero_iff.1 ha
    -- ⊢ #{ s // Bounded r s } = 0
    rw [mk_eq_zero_iff]
    -- ⊢ IsEmpty { s // Bounded r s }
    constructor
    -- ⊢ { s // Bounded r s } → False
    rintro ⟨s, hs⟩
    -- ⊢ False
    exact (not_unbounded_iff s).2 hs (unbounded_of_isEmpty s)
    -- 🎉 no goals
  have h' : IsStrongLimit #α := ⟨ha, h⟩
  -- ⊢ #{ s // Bounded r s } = #α
  have ha := h'.isLimit.aleph0_le
  -- ⊢ #{ s // Bounded r s } = #α
  apply le_antisymm
  -- ⊢ #{ s // Bounded r s } ≤ #α
  · have : { s : Set α | Bounded r s } = ⋃ i, 𝒫{ j | r j i } := setOf_exists _
    -- ⊢ #{ s // Bounded r s } ≤ #α
    rw [← coe_setOf, this]
    -- ⊢ #↑(⋃ (i : α), 𝒫{j | r j i}) ≤ #α
    refine mk_iUnion_le_sum_mk.trans ((sum_le_iSup (fun i => #(𝒫{ j | r j i }))).trans
      ((mul_le_max_of_aleph0_le_left ha).trans ?_))
    rw [max_eq_left]
    -- ⊢ ⨆ (i : α), #↑(𝒫{j | r j i}) ≤ #α
    apply ciSup_le' _
    -- ⊢ ∀ (i : α), #↑(𝒫{j | r j i}) ≤ #α
    intro i
    -- ⊢ #↑(𝒫{j | r j i}) ≤ #α
    rw [mk_powerset]
    -- ⊢ 2 ^ #↑{j | r j i} ≤ #α
    apply (h'.two_power_lt _).le
    -- ⊢ #↑{j | r j i} < #α
    rw [coe_setOf, card_typein, ← lt_ord, hr]
    -- ⊢ typein (fun x => r x) i < type r
    apply typein_lt_type
    -- 🎉 no goals
  · refine' @mk_le_of_injective α _ (fun x => Subtype.mk {x} _) _
    -- ⊢ Bounded r {x}
    · apply bounded_singleton
      -- ⊢ Ordinal.IsLimit (type r)
      rw [← hr]
      -- ⊢ Ordinal.IsLimit (ord #α)
      apply ord_isLimit ha
      -- 🎉 no goals
    · intro a b hab
      -- ⊢ a = b
      simpa [singleton_eq_singleton_iff] using hab
      -- 🎉 no goals
#align cardinal.mk_bounded_subset Cardinal.mk_bounded_subset

theorem mk_subset_mk_lt_cof {α : Type*} (h : ∀ x < #α, (2^x) < #α) :
    #{ s : Set α // #s < cof (#α).ord } = #α := by
  rcases eq_or_ne #α 0 with (ha | ha)
  -- ⊢ #{ s // #↑s < Ordinal.cof (ord #α) } = #α
  · rw [ha]
    -- ⊢ #{ s // #↑s < Ordinal.cof (ord 0) } = 0
    simp [fun s => (Cardinal.zero_le s).not_lt]
    -- 🎉 no goals
  have h' : IsStrongLimit #α := ⟨ha, h⟩
  -- ⊢ #{ s // #↑s < Ordinal.cof (ord #α) } = #α
  rcases ord_eq α with ⟨r, wo, hr⟩
  -- ⊢ #{ s // #↑s < Ordinal.cof (ord #α) } = #α
  haveI := wo
  -- ⊢ #{ s // #↑s < Ordinal.cof (ord #α) } = #α
  apply le_antisymm
  -- ⊢ #{ s // #↑s < Ordinal.cof (ord #α) } ≤ #α
  · conv_rhs => rw [← mk_bounded_subset h hr]
    -- ⊢ #{ s // #↑s < Ordinal.cof (ord #α) } ≤ #{ s // Bounded r s }
    apply mk_le_mk_of_subset
    -- ⊢ (fun x => Quotient.liftOn₂ (#↑x) (Ordinal.cof (ord #α)) (fun α β => Nonempty …
    intro s hs
    -- ⊢ s ∈ fun x => ∃ a, ∀ (b : α), b ∈ x → r b a
    rw [hr] at hs
    -- ⊢ s ∈ fun x => ∃ a, ∀ (b : α), b ∈ x → r b a
    exact lt_cof_type hs
    -- 🎉 no goals
  · refine' @mk_le_of_injective α _ (fun x => Subtype.mk {x} _) _
    -- ⊢ #↑{x} < Ordinal.cof (ord #α)
    · rw [mk_singleton]
      -- ⊢ 1 < Ordinal.cof (ord #α)
      exact one_lt_aleph0.trans_le (aleph0_le_cof.2 (ord_isLimit h'.isLimit.aleph0_le))
      -- 🎉 no goals
    · intro a b hab
      -- ⊢ a = b
      simpa [singleton_eq_singleton_iff] using hab
      -- 🎉 no goals
#align cardinal.mk_subset_mk_lt_cof Cardinal.mk_subset_mk_lt_cof

/-- A cardinal is regular if it is infinite and it equals its own cofinality. -/
def IsRegular (c : Cardinal) : Prop :=
  ℵ₀ ≤ c ∧ c ≤ c.ord.cof
#align cardinal.is_regular Cardinal.IsRegular

theorem IsRegular.aleph0_le {c : Cardinal} (H : c.IsRegular) : ℵ₀ ≤ c :=
  H.1
#align cardinal.is_regular.aleph_0_le Cardinal.IsRegular.aleph0_le

theorem IsRegular.cof_eq {c : Cardinal} (H : c.IsRegular) : c.ord.cof = c :=
  (cof_ord_le c).antisymm H.2
#align cardinal.is_regular.cof_eq Cardinal.IsRegular.cof_eq

theorem IsRegular.pos {c : Cardinal} (H : c.IsRegular) : 0 < c :=
  aleph0_pos.trans_le H.1
#align cardinal.is_regular.pos Cardinal.IsRegular.pos

theorem IsRegular.ord_pos {c : Cardinal} (H : c.IsRegular) : 0 < c.ord := by
  rw [Cardinal.lt_ord, card_zero]
  -- ⊢ 0 < c
  exact H.pos
  -- 🎉 no goals
#align cardinal.is_regular.ord_pos Cardinal.IsRegular.ord_pos

theorem isRegular_cof {o : Ordinal} (h : o.IsLimit) : IsRegular o.cof :=
  ⟨aleph0_le_cof.2 h, (cof_cof o).ge⟩
#align cardinal.is_regular_cof Cardinal.isRegular_cof

theorem isRegular_aleph0 : IsRegular ℵ₀ :=
  ⟨le_rfl, by simp⟩
              -- 🎉 no goals
#align cardinal.is_regular_aleph_0 Cardinal.isRegular_aleph0

theorem isRegular_succ {c : Cardinal.{u}} (h : ℵ₀ ≤ c) : IsRegular (succ c) :=
  ⟨h.trans (le_succ c),
    succ_le_of_lt
      (by
        cases' Quotient.exists_rep (@succ Cardinal _ _ c) with α αe; simp at αe
        -- ⊢ c < Ordinal.cof (ord (succ c))
                                                                     -- ⊢ c < Ordinal.cof (ord (succ c))
        rcases ord_eq α with ⟨r, wo, re⟩; skip
        -- ⊢ c < Ordinal.cof (ord (succ c))
                                          -- ⊢ c < Ordinal.cof (ord (succ c))
        have := ord_isLimit (h.trans (le_succ _))
        -- ⊢ c < Ordinal.cof (ord (succ c))
        rw [← αe, re] at this ⊢
        -- ⊢ c < Ordinal.cof (type r)
        rcases cof_eq' r this with ⟨S, H, Se⟩
        -- ⊢ c < Ordinal.cof (type r)
        rw [← Se]
        -- ⊢ c < #↑S
        apply lt_imp_lt_of_le_imp_le fun h => mul_le_mul_right' h c
        -- ⊢ c * c < #↑S * c
        rw [mul_eq_self h, ← succ_le_iff, ← αe, ← sum_const']
        -- ⊢ #α ≤ sum fun x => c
        refine' le_trans _ (sum_le_sum (fun (x : S) => card (typein r (x : α))) _ fun i => _)
        -- ⊢ #α ≤ sum fun x => card (typein r ↑x)
        · simp only [← card_typein, ← mk_sigma]
          -- ⊢ #α ≤ #((i : ↑S) × { y // r y ↑i })
          exact
            ⟨Embedding.ofSurjective (fun x => x.2.1) fun a =>
                let ⟨b, h, ab⟩ := H a
                ⟨⟨⟨_, h⟩, _, ab⟩, rfl⟩⟩
        · rw [← lt_succ_iff, ← lt_ord, ← αe, re]
          -- ⊢ typein r ↑i < type r
          apply typein_lt_type)⟩
          -- 🎉 no goals
#align cardinal.is_regular_succ Cardinal.isRegular_succ

theorem isRegular_aleph_one : IsRegular (aleph 1) := by
  rw [← succ_aleph0]
  -- ⊢ IsRegular (succ ℵ₀)
  exact isRegular_succ le_rfl
  -- 🎉 no goals
#align cardinal.is_regular_aleph_one Cardinal.isRegular_aleph_one

theorem isRegular_aleph'_succ {o : Ordinal} (h : ω ≤ o) : IsRegular (aleph' (succ o)) := by
  rw [aleph'_succ]
  -- ⊢ IsRegular (succ (aleph' o))
  exact isRegular_succ (aleph0_le_aleph'.2 h)
  -- 🎉 no goals
#align cardinal.is_regular_aleph'_succ Cardinal.isRegular_aleph'_succ

theorem isRegular_aleph_succ (o : Ordinal) : IsRegular (aleph (succ o)) := by
  rw [aleph_succ]
  -- ⊢ IsRegular (succ (aleph o))
  exact isRegular_succ (aleph0_le_aleph o)
  -- 🎉 no goals
#align cardinal.is_regular_aleph_succ Cardinal.isRegular_aleph_succ

/-- A function whose codomain's cardinality is infinite but strictly smaller than its domain's
has a fiber with cardinality strictly great than the codomain.
-/
theorem infinite_pigeonhole_card_lt {β α : Type u} (f : β → α) (w : #α < #β) (w' : ℵ₀ ≤ #α) :
    ∃ a : α, #α < #(f ⁻¹' {a}) := by
  simp_rw [← succ_le_iff]
  -- ⊢ ∃ a, succ #α ≤ #↑(f ⁻¹' {a})
  exact
    Ordinal.infinite_pigeonhole_card f (succ #α) (succ_le_of_lt w) (w'.trans (lt_succ _).le)
      ((lt_succ _).trans_le (isRegular_succ w').2.ge)
#align cardinal.infinite_pigeonhole_card_lt Cardinal.infinite_pigeonhole_card_lt

/-- A function whose codomain's cardinality is infinite but strictly smaller than its domain's
has an infinite fiber.
-/
theorem exists_infinite_fiber {β α : Type _} (f : β → α) (w : #α < #β) (w' : Infinite α) :
    ∃ a : α, Infinite (f ⁻¹' {a}) := by
  simp_rw [Cardinal.infinite_iff] at w' ⊢
  -- ⊢ ∃ a, ℵ₀ ≤ #↑(f ⁻¹' {a})
  cases' infinite_pigeonhole_card_lt f w w' with a ha
  -- ⊢ ∃ a, ℵ₀ ≤ #↑(f ⁻¹' {a})
  exact ⟨a, w'.trans ha.le⟩
  -- 🎉 no goals
#align cardinal.exists_infinite_fiber Cardinal.exists_infinite_fiber

/-- If an infinite type `β` can be expressed as a union of finite sets,
then the cardinality of the collection of those finite sets
must be at least the cardinality of `β`.
-/
theorem le_range_of_union_finset_eq_top {α β : Type*} [Infinite β] (f : α → Finset β)
    (w : ⋃ a, (f a : Set β) = ⊤) : #β ≤ #(range f) := by
  have k : _root_.Infinite (range f) := by
    rw [infinite_coe_iff]
    apply mt (union_finset_finite_of_range_finite f)
    rw [w]
    exact infinite_univ
  by_contra h
  -- ⊢ False
  simp only [not_le] at h
  -- ⊢ False
  let u : ∀ b, ∃ a, b ∈ f a := fun b => by simpa using (w.ge : _) (Set.mem_univ b)
  -- ⊢ False
  let u' : β → range f := fun b => ⟨f (u b).choose, by simp⟩
  -- ⊢ False
  have v' : ∀ a, u' ⁻¹' {⟨f a, by simp⟩} ≤ f a := by
    rintro a p m
    simp at m
    rw [← m]
    apply fun b => (u b).choose_spec
  obtain ⟨⟨-, ⟨a, rfl⟩⟩, p⟩ := exists_infinite_fiber u' h k
  -- ⊢ False
  exact (@Infinite.of_injective _ _ p (inclusion (v' a)) (inclusion_injective _)).false
  -- 🎉 no goals
#align cardinal.le_range_of_union_finset_eq_top Cardinal.le_range_of_union_finset_eq_top

theorem lsub_lt_ord_lift_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) : (∀ i, f i < c.ord) → Ordinal.lsub.{u, v} f < c.ord :=
  lsub_lt_ord_lift (by rwa [hc.cof_eq])
                       -- 🎉 no goals
#align cardinal.lsub_lt_ord_lift_of_is_regular Cardinal.lsub_lt_ord_lift_of_isRegular

theorem lsub_lt_ord_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (∀ i, f i < c.ord) → Ordinal.lsub f < c.ord :=
  lsub_lt_ord (by rwa [hc.cof_eq])
                  -- 🎉 no goals
#align cardinal.lsub_lt_ord_of_is_regular Cardinal.lsub_lt_ord_of_isRegular

theorem sup_lt_ord_lift_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) : (∀ i, f i < c.ord) → Ordinal.sup.{u, v} f < c.ord :=
  sup_lt_ord_lift (by rwa [hc.cof_eq])
                      -- 🎉 no goals
#align cardinal.sup_lt_ord_lift_of_is_regular Cardinal.sup_lt_ord_lift_of_isRegular

theorem sup_lt_ord_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (∀ i, f i < c.ord) → Ordinal.sup f < c.ord :=
  sup_lt_ord (by rwa [hc.cof_eq])
                 -- 🎉 no goals
#align cardinal.sup_lt_ord_of_is_regular Cardinal.sup_lt_ord_of_isRegular

theorem blsub_lt_ord_lift_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (ho : Cardinal.lift.{v, u} o.card < c) :
    (∀ i hi, f i hi < c.ord) → Ordinal.blsub.{u, v} o f < c.ord :=
  blsub_lt_ord_lift (by rwa [hc.cof_eq])
                        -- 🎉 no goals
#align cardinal.blsub_lt_ord_lift_of_is_regular Cardinal.blsub_lt_ord_lift_of_isRegular

theorem blsub_lt_ord_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (ho : o.card < c) : (∀ i hi, f i hi < c.ord) → Ordinal.blsub o f < c.ord :=
  blsub_lt_ord (by rwa [hc.cof_eq])
                   -- 🎉 no goals
#align cardinal.blsub_lt_ord_of_is_regular Cardinal.blsub_lt_ord_of_isRegular

theorem bsup_lt_ord_lift_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} o.card < c) :
    (∀ i hi, f i hi < c.ord) → Ordinal.bsup.{u, v} o f < c.ord :=
  bsup_lt_ord_lift (by rwa [hc.cof_eq])
                       -- 🎉 no goals
#align cardinal.bsup_lt_ord_lift_of_is_regular Cardinal.bsup_lt_ord_lift_of_isRegular

theorem bsup_lt_ord_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (hι : o.card < c) : (∀ i hi, f i hi < c.ord) → Ordinal.bsup o f < c.ord :=
  bsup_lt_ord (by rwa [hc.cof_eq])
                  -- 🎉 no goals
#align cardinal.bsup_lt_ord_of_is_regular Cardinal.bsup_lt_ord_of_isRegular

theorem iSup_lt_lift_of_isRegular {ι} {f : ι → Cardinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) : (∀ i, f i < c) → iSup.{max u v + 1, u + 1} f < c :=
  iSup_lt_lift.{u, v} (by rwa [hc.cof_eq])
                          -- 🎉 no goals
#align cardinal.supr_lt_lift_of_is_regular Cardinal.iSup_lt_lift_of_isRegular

theorem iSup_lt_of_isRegular {ι} {f : ι → Cardinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (∀ i, f i < c) → iSup f < c :=
  iSup_lt (by rwa [hc.cof_eq])
              -- 🎉 no goals
#align cardinal.supr_lt_of_is_regular Cardinal.iSup_lt_of_isRegular

theorem sum_lt_lift_of_isRegular {ι : Type u} {f : ι → Cardinal} {c : Cardinal} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hf : ∀ i, f i < c) : sum f < c :=
  (sum_le_iSup_lift _).trans_lt <| mul_lt_of_lt hc.1 hι (iSup_lt_lift_of_isRegular hc hι hf)
#align cardinal.sum_lt_lift_of_is_regular Cardinal.sum_lt_lift_of_isRegular

theorem sum_lt_of_isRegular {ι : Type u} {f : ι → Cardinal} {c : Cardinal} (hc : IsRegular c)
    (hι : #ι < c) : (∀ i, f i < c) → sum f < c :=
  sum_lt_lift_of_isRegular.{u, u} hc (by rwa [lift_id])
                                         -- 🎉 no goals
#align cardinal.sum_lt_of_is_regular Cardinal.sum_lt_of_isRegular

theorem nfpFamily_lt_ord_lift_of_isRegular {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hc' : c ≠ ℵ₀) (hf : ∀ (i), ∀ b < c.ord, f i b < c.ord) {a}
    (ha : a < c.ord) : nfpFamily.{u, v} f a < c.ord := by
  apply nfpFamily_lt_ord_lift.{u, v} _ _ hf ha <;> rw [hc.cof_eq]
  -- ⊢ ℵ₀ < Ordinal.cof (ord c)
                                                   -- ⊢ ℵ₀ < c
                                                   -- ⊢ lift.{v, u} #ι < c
  exact lt_of_le_of_ne hc.1 hc'.symm
  -- ⊢ lift.{v, u} #ι < c
  exact hι
  -- 🎉 no goals
#align cardinal.nfp_family_lt_ord_lift_of_is_regular Cardinal.nfpFamily_lt_ord_lift_of_isRegular

theorem nfpFamily_lt_ord_of_isRegular {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : #ι < c) (hc' : c ≠ ℵ₀) {a} (hf : ∀ (i), ∀ b < c.ord, f i b < c.ord) :
    a < c.ord → nfpFamily.{u, u} f a < c.ord :=
  nfpFamily_lt_ord_lift_of_isRegular hc (by rwa [lift_id]) hc' hf
                                            -- 🎉 no goals
#align cardinal.nfp_family_lt_ord_of_is_regular Cardinal.nfpFamily_lt_ord_of_isRegular

theorem nfpBFamily_lt_ord_lift_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c}
    (hc : IsRegular c) (ho : Cardinal.lift.{v, u} o.card < c) (hc' : c ≠ ℵ₀)
    (hf : ∀ (i hi), ∀ b < c.ord, f i hi b < c.ord) {a} :
    a < c.ord → nfpBFamily.{u, v} o f a < c.ord :=
  nfpFamily_lt_ord_lift_of_isRegular hc (by rwa [mk_ordinal_out]) hc' fun i => hf _ _
                                            -- 🎉 no goals
#align cardinal.nfp_bfamily_lt_ord_lift_of_is_regular Cardinal.nfpBFamily_lt_ord_lift_of_isRegular

theorem nfpBFamily_lt_ord_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c}
    (hc : IsRegular c) (ho : o.card < c) (hc' : c ≠ ℵ₀)
    (hf : ∀ (i hi), ∀ b < c.ord, f i hi b < c.ord) {a} :
    a < c.ord → nfpBFamily.{u, u} o f a < c.ord :=
  nfpBFamily_lt_ord_lift_of_isRegular hc (by rwa [lift_id]) hc' hf
                                             -- 🎉 no goals
#align cardinal.nfp_bfamily_lt_ord_of_is_regular Cardinal.nfpBFamily_lt_ord_of_isRegular

theorem nfp_lt_ord_of_isRegular {f : Ordinal → Ordinal} {c} (hc : IsRegular c) (hc' : c ≠ ℵ₀)
    (hf : ∀ i < c.ord, f i < c.ord) {a} : a < c.ord → nfp f a < c.ord :=
  nfp_lt_ord
    (by
      rw [hc.cof_eq]
      -- ⊢ ℵ₀ < c
      exact lt_of_le_of_ne hc.1 hc'.symm)
      -- 🎉 no goals
    hf
#align cardinal.nfp_lt_ord_of_is_regular Cardinal.nfp_lt_ord_of_isRegular

theorem derivFamily_lt_ord_lift {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hc' : c ≠ ℵ₀)
    (hf : ∀ (i), ∀ b < c.ord, f i b < c.ord) {a} :
    a < c.ord → derivFamily.{u, v} f a < c.ord := by
  have hω : ℵ₀ < c.ord.cof := by
    rw [hc.cof_eq]
    exact lt_of_le_of_ne hc.1 hc'.symm
  induction a using limitRecOn with
  | H₁ =>
    rw [derivFamily_zero]
    exact nfpFamily_lt_ord_lift hω (by rwa [hc.cof_eq]) hf
  | H₂ b hb =>
    intro hb'
    rw [derivFamily_succ]
    exact
      nfpFamily_lt_ord_lift hω (by rwa [hc.cof_eq]) hf
        ((ord_isLimit hc.1).2 _ (hb ((lt_succ b).trans hb')))
  | H₃ b hb H =>
    intro hb'
    rw [derivFamily_limit f hb]
    exact
      bsup_lt_ord_of_isRegular.{u, v} hc (ord_lt_ord.1 ((ord_card_le b).trans_lt hb')) fun o' ho' =>
        H o' ho' (ho'.trans hb')
#align cardinal.deriv_family_lt_ord_lift Cardinal.derivFamily_lt_ord_lift

theorem derivFamily_lt_ord {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c) (hι : #ι < c)
    (hc' : c ≠ ℵ₀) (hf : ∀ (i), ∀ b < c.ord, f i b < c.ord) {a} :
    a < c.ord → derivFamily.{u, u} f a < c.ord :=
  derivFamily_lt_ord_lift hc (by rwa [lift_id]) hc' hf
                                 -- 🎉 no goals
#align cardinal.deriv_family_lt_ord Cardinal.derivFamily_lt_ord

theorem derivBFamily_lt_ord_lift {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c}
    (hc : IsRegular c) (hι : Cardinal.lift.{v, u} o.card < c) (hc' : c ≠ ℵ₀)
    (hf : ∀ (i hi), ∀ b < c.ord, f i hi b < c.ord) {a} :
    a < c.ord → derivBFamily.{u, v} o f a < c.ord :=
  derivFamily_lt_ord_lift hc (by rwa [mk_ordinal_out]) hc' fun i => hf _ _
                                 -- 🎉 no goals
#align cardinal.deriv_bfamily_lt_ord_lift Cardinal.derivBFamily_lt_ord_lift

theorem derivBFamily_lt_ord {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : o.card < c) (hc' : c ≠ ℵ₀) (hf : ∀ (i hi), ∀ b < c.ord, f i hi b < c.ord) {a} :
    a < c.ord → derivBFamily.{u, u} o f a < c.ord :=
  derivBFamily_lt_ord_lift hc (by rwa [lift_id]) hc' hf
                                  -- 🎉 no goals
#align cardinal.deriv_bfamily_lt_ord Cardinal.derivBFamily_lt_ord

theorem deriv_lt_ord {f : Ordinal.{u} → Ordinal} {c} (hc : IsRegular c) (hc' : c ≠ ℵ₀)
    (hf : ∀ i < c.ord, f i < c.ord) {a} : a < c.ord → deriv f a < c.ord :=
  derivFamily_lt_ord_lift hc
    (by simpa using Cardinal.one_lt_aleph0.trans (lt_of_le_of_ne hc.1 hc'.symm)) hc' fun _ => hf
        -- 🎉 no goals
#align cardinal.deriv_lt_ord Cardinal.deriv_lt_ord

/-- A cardinal is inaccessible if it is an uncountable regular strong limit cardinal. -/
def IsInaccessible (c : Cardinal) :=
  ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c
#align cardinal.is_inaccessible Cardinal.IsInaccessible

theorem IsInaccessible.mk {c} (h₁ : ℵ₀ < c) (h₂ : c ≤ c.ord.cof) (h₃ : ∀ x < c, (2^x) < c) :
    IsInaccessible c :=
  ⟨h₁, ⟨h₁.le, h₂⟩, (aleph0_pos.trans h₁).ne', h₃⟩
#align cardinal.is_inaccessible.mk Cardinal.IsInaccessible.mk

-- Lean's foundations prove the existence of ℵ₀ many inaccessible cardinals
theorem univ_inaccessible : IsInaccessible univ.{u, v} :=
  IsInaccessible.mk (by simpa using lift_lt_univ' ℵ₀) (by simp) fun c h => by
                        -- 🎉 no goals
                                                          -- 🎉 no goals
    rcases lt_univ'.1 h with ⟨c, rfl⟩
    -- ⊢ 2 ^ lift.{max (u + 1) v, u} c < univ
    rw [← lift_two_power.{u, max (u + 1) v}]
    -- ⊢ lift.{max (u + 1) v, u} (2 ^ c) < univ
    apply lift_lt_univ'
    -- 🎉 no goals
#align cardinal.univ_inaccessible Cardinal.univ_inaccessible

theorem lt_power_cof {c : Cardinal.{u}} : ℵ₀ ≤ c → c < (c^cof c.ord) :=
  Quotient.inductionOn c fun α h => by
    rcases ord_eq α with ⟨r, wo, re⟩; skip
    -- ⊢ Quotient.mk isEquivalent α < Quotient.mk isEquivalent α ^ Ordinal.cof (ord ( …
                                      -- ⊢ Quotient.mk isEquivalent α < Quotient.mk isEquivalent α ^ Ordinal.cof (ord ( …
    have := ord_isLimit h
    -- ⊢ Quotient.mk isEquivalent α < Quotient.mk isEquivalent α ^ Ordinal.cof (ord ( …
    rw [mk'_def, re] at this ⊢
    -- ⊢ #α < #α ^ Ordinal.cof (type r)
    rcases cof_eq' r this with ⟨S, H, Se⟩
    -- ⊢ #α < #α ^ Ordinal.cof (type r)
    have := sum_lt_prod (fun a : S => #{ x // r x a }) (fun _ => #α) fun i => ?_
    -- ⊢ #α < #α ^ Ordinal.cof (type r)
    · simp only [Cardinal.prod_const, Cardinal.lift_id, ← Se, ← mk_sigma, power_def] at this ⊢
      -- ⊢ #α < #(↑S → α)
      refine' lt_of_le_of_lt _ this
      -- ⊢ #α ≤ #((i : ↑S) × { x // r x ↑i })
      refine' ⟨Embedding.ofSurjective _ _⟩
      -- ⊢ (i : ↑S) × { x // r x ↑i } → α
      · exact fun x => x.2.1
        -- 🎉 no goals
      · exact fun a =>
          let ⟨b, h, ab⟩ := H a
          ⟨⟨⟨_, h⟩, _, ab⟩, rfl⟩
    · have := typein_lt_type r i
      -- ⊢ (fun a => #{ x // r x ↑a }) i < (fun x => #α) i
      rwa [← re, lt_ord] at this
      -- 🎉 no goals
#align cardinal.lt_power_cof Cardinal.lt_power_cof

theorem lt_cof_power {a b : Cardinal} (ha : ℵ₀ ≤ a) (b1 : 1 < b) : a < cof (b^a).ord := by
  have b0 : b ≠ 0 := (zero_lt_one.trans b1).ne'
  -- ⊢ a < Ordinal.cof (ord (b ^ a))
  apply lt_imp_lt_of_le_imp_le (power_le_power_left <| power_ne_zero a b0)
  -- ⊢ (b ^ a) ^ a < (b ^ a) ^ Ordinal.cof (ord (b ^ a))
  rw [← power_mul, mul_eq_self ha]
  -- ⊢ b ^ a < (b ^ a) ^ Ordinal.cof (ord (b ^ a))
  exact lt_power_cof (ha.trans <| (cantor' _ b1).le)
  -- 🎉 no goals
#align cardinal.lt_cof_power Cardinal.lt_cof_power

end Cardinal
