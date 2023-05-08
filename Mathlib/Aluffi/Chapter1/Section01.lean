import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Partition.Stirling
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-
Prove that is ~ is a relation on a set `S`, then the corresponding family
`𝒫_~` is indeed a partition of `S`: that is, its elements are nonempty,
disjoint, and their union is `S`.
-/
example {S : Type _} (r : Setoid S) : Setoid.IsPartition r.classes := by
  rw [Setoid.IsPartition, Setoid.classes]
  refine' ⟨_, λ a => _⟩
  { rintro ⟨a, ha⟩
    have : a ∈ (∅ : Set S)
    { rw [ha]
      exact r.refl' a }
    exact (Set.mem_empty_iff_false _).mp this }
  { refine' ⟨{b | r.Rel b a}, _, _⟩
    { simp only [Set.mem_setOf_eq, exists_unique_iff_exists, exists_prop]
      constructor
      · use a
      · rfl  }
    { intros t
      simp only [Set.mem_setOf_eq, exists_unique_iff_exists, exists_prop, and_imp,
                 forall_exists_index]
      rintro b rfl (ha : r.Rel a b)
      ext c
      constructor <;> intro h
      · exact r.trans' h (Setoid.symm ha)
      · exact r.trans' h ha  } }

/-
Given a partition `𝒫` on a set `S`, show how to define a relation `~` on `S` such that `𝒫`
is the corresponding partition.
-/
def RelationOf {S : Type _} (P : Set (Set S)) (hP : Setoid.IsPartition P) :
  Setoid S :=
⟨λ a b => ∃ (c : Set S) (_ : c ∈ P), a ∈ c ∧ b ∈ c,
  λ a => Exists₂.imp (λ s _ ha => ⟨ha, ha⟩) (hP.right a).exists₂,
  Exists₂.imp λ s _ => And.symm,
  λ {a b c} ⟨s, hs, hs'⟩ ⟨t, ht, ht'⟩ => by
    refine' ⟨s, hs, hs'.left, _⟩
    suffices : t = s
    { subst this
      exact ht'.right }
    refine' (hP.right b).unique _ _
    · simp [ht, ht'.left]
    · simp [hs, hs'.right]⟩

lemma relation_of_eq_classes {S : Type _} (P : Set (Set S)) (hP : Setoid.IsPartition P) :
    (RelationOf P hP).classes = P := by
  ext s
  constructor
  { rintro ⟨a, rfl⟩
    obtain ⟨t, ht⟩ := hP.right a
    simp only [exists_unique_iff_exists, exists_prop, and_imp] at ht
    suffices : t = {x : S | (RelationOf P hP).Rel x a}
    { rw [←this]
      exact ht.left.left }
    ext b
    constructor
    { intro hb
      exact ⟨t, ht.left.left, hb, ht.left.right⟩ }
    { rintro ⟨u, hu, hu'⟩
      rw [←ht.right u hu hu'.right]
      exact hu'.left } }
  { intro hs
    rcases s.eq_empty_or_nonempty with rfl|⟨a, ha⟩
    { exact absurd hs hP.left }
    refine' ⟨a, _⟩
    ext b
    constructor
    { intro hb
      exact ⟨s, hs, hb, ha⟩ }
    { rintro ⟨u, hu, hu'⟩
      obtain ⟨t, ht⟩ := hP.right a
      simp only [exists_unique_iff_exists, exists_prop, and_imp] at ht
      rw [ht.right s hs ha, ←ht.right u hu hu'.right]
      exact hu'.left } }

section

variable {X : Type _} [Fintype X] [∀ r : X → X → Prop, DecidableRel r]

instance : DecidablePred (@Equivalence X) :=
λ r => decidable_of_iff ((∀ x, r x x) ∧ (∀ {x y}, r x y → r y x) ∧ ∀ {x y z}, r x y → r y z → r x z)
    <| by
  constructor <;>
  · rintro ⟨refl, symm, trans⟩
    exact ⟨refl, symm, trans⟩

def Setoid.EquivRelSubtype (X : Type _ ) : Setoid X ≃ {r : X → X → Prop // Equivalence r} :=
⟨λ ⟨r, hr⟩ => ⟨r, hr⟩, λ ⟨r, hr⟩ => ⟨r, hr⟩, λ _ => rfl, λ _ => rfl⟩

instance : Fintype (Setoid X) :=
Fintype.ofEquiv {r : X → X → Prop // Equivalence r} (Setoid.EquivRelSubtype X).symm

-- instance [@DecidablePred (Set (Set X)) Setoid.IsPartition] : Fintype (Setoid X) :=
-- Fintype.ofEquiv {C : Set (Set X) // Setoid.IsPartition C} (Setoid.Partition.orderIso X).symm

end

-- How many different equivalence relations may be defined on the set `{1, 2, 3}`
section

@[simps]
noncomputable
def set_finset_orderIso (α : Type _) [Fintype α] :
    Set α ≃o Finset α where
  toFun := λ s => Set.Finite.toFinset (Set.finite_univ.subset (by simp) : s.Finite)
  invFun := λ s => s
  left_inv := λ s => by simp
  right_inv := λ s => by simp
  map_rel_iff' := by simp

@[simp] lemma set_finset_orderIso_apply' {α : Type _} [Fintype α] (s : Set α) :
    (set_finset_orderIso α : Set α ≃ Finset α) s =
      Set.Finite.toFinset (Set.finite_univ.subset (by simp) : s.Finite) := rfl

@[simp] lemma set_finset_orderIso_symm_apply' {α : Type _} [Fintype α] (s : Finset α) :
    ((set_finset_orderIso α).symm : Finset α ≃ Set α) s = (s : Set α) := rfl

@[simp] lemma coe_set_finset_orderIso_apply {α : Type _} [Fintype α] (s : Set α) :
    ((set_finset_orderIso α : Set α ≃ Finset α) s : Set α)= s := by simp

@[simp] lemma OrderIso.equiv_symm {α β : Type _} [LE α] [LE β] (e : α ≃o β) :
    Equiv.symm (e : α ≃ β) = e.symm := rfl

@[simp] lemma Finset.filter_univ_mem {α : Type _} [Fintype α] (s : Finset α) [DecidablePred (· ∈ s)]:
    Finset.filter (· ∈ s) Finset.univ = s := by
  ext
  simp

lemma Finset.map_univ_fin_eq_range (n : ℕ) :
    (Finset.univ : Finset (Fin n)).map Fin.valEmbedding = Finset.range n := by
  ext x
  simp only [mem_map, mem_univ, Fin.valEmbedding_apply, true_and, mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact x.prop
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

lemma Finset.map_univ_equivFin_eq_range (α : Type _) [Fintype α] :
    (Finset.univ : Finset α).map ((Fintype.equivFinOfCardEq rfl).toEmbedding.trans Fin.valEmbedding)
    = Finset.range (Fintype.card α) := by
  ext x
  simp only [mem_map, mem_univ, Fin.valEmbedding_apply, true_and, mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro hx
    refine' ⟨(Fintype.equivFinOfCardEq rfl).symm ⟨x, hx⟩, _⟩
    simp


-- lemma Disjoint.orderEmbedding {α β : Type _}
--     {s t : Finset α} (h : Disjoint s t) (e : Finset α ↪o Finset β) :
--     Disjoint (e s) (e t) := by
--   intro b hbs hbt x hxb
--   specialize hbs hxb
--   specialize hbt hxb
--   simp at hbs

noncomputable
def Finpartition.equiv_subtype_setoid_ispartition (α : Type _) [Fintype α] [DecidableEq α] :
    Finpartition (Finset.univ : Finset α) ≃
    {C : Finset (Set α) // Setoid.IsPartition (C : Set (Set α))} where
  toFun P := by
    refine' ⟨P.parts.map (set_finset_orderIso α).symm, _⟩
    let P' : Finpartition (Set.univ : Set α) :=
      (P.equiv (set_finset_orderIso α).symm).copy ?_
    · have := P'.isPartition_parts
      simp only [Finset.coe_map, Equiv.coe_toEmbedding]
      constructor
      · simp only [Set.mem_image, Finset.mem_coe, not_exists, not_and]
        intros x hx
        have hx' := P.ne_bot hx
        contrapose! hx'
        simp only [ne_eq, not_not] at hx'
        rw [←(set_finset_orderIso α).symm.injective.eq_iff, OrderIso.map_bot,
            Set.bot_eq_empty, ←hx']
        rfl
      · intro a
        obtain ⟨s, ⟨hs, _, _⟩, _⟩ := this.right a
        refine' (this.right a).imp (λ t => And.imp _ _)
        · simp only [Finset.le_eq_subset, Set.le_eq_subset, exists_unique_iff_exists,
                     Finset.mem_coe, exists_prop, set_finset_orderIso_symm_apply',
                     Set.mem_image, and_imp]
          intro ht hat
          rw [Finpartition.copy_parts] at ht
          · simp only [Finpartition.parts_equiv, Finset.mem_map_equiv] at ht
            refine' ⟨⟨set_finset_orderIso α t, ht, _⟩, hat⟩
            simp
          · rw [←Finset.top_eq_univ, OrderIso.map_top, Set.top_eq_univ]
        · simp
  invFun := λ ⟨C, hC⟩ => by
    refine' (hC.finpartition.equiv (set_finset_orderIso α)).copy _
    simp
  left_inv := by
    intro
    ext
    simp
  right_inv := by
    rintro ⟨C, hC⟩
    ext
    simp

noncomputable
def Finpartition.equiv_range_fintype_card (α : Type _) [Fintype α] [DecidableEq α] :
    Finpartition (Finset.univ : Finset α) ≃
    Finpartition (Finset.range (Fintype.card α)) where
  toFun C := by
    refine' ⟨C.parts.map (Finset.mapEmbedding
      ((Fintype.equivFinOfCardEq rfl).toEmbedding.trans Fin.valEmbedding)).toEmbedding, _, _, _⟩
    · simp only [Finset.le_eq_subset, Finset.supIndep_map, Function.comp.left_id]
      intro s hs x hCx hsx
      intro k hkx hks n hn
      specialize hkx hn
      specialize hks hn
      simp only [Finset.mapEmbedding_apply, Finset.mem_map, Fin.valEmbedding_apply] at hkx
      simp only [Finset.mem_sup, Finset.mapEmbedding_apply, Finset.mem_map,
                  Fin.valEmbedding_apply] at hks
      obtain ⟨m, hm, rfl⟩ := hkx
      obtain ⟨y, hy, ⟨l, hl, hl'⟩⟩ := hks
      simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
                 Fin.valEmbedding_apply, Fin.val_eq_val, EmbeddingLike.apply_eq_iff_eq] at hl'
      subst hl'
      have : {l} ≤ s.sup id
      · simp only [Finset.le_eq_subset, Finset.singleton_subset_iff, Finset.mem_sup, id_eq]
        exact ⟨y, hy, hl⟩
      simpa using C.supIndep hs hCx hsx (Finset.singleton_subset_iff.mpr hm) this
    · rw [←Finset.map_univ_equivFin_eq_range,
          congr_arg (Finset.map ((Fintype.equivFinOfCardEq rfl).toEmbedding.trans Fin.valEmbedding))
          C.supParts.symm]
      ext
      simp only [Finset.le_eq_subset, Finset.sup_map, Function.comp.left_id, Finset.mem_sup,
                 Finset.mapEmbedding_apply, Finset.mem_map, Function.Embedding.trans_apply,
                 Equiv.coe_toEmbedding, Fin.valEmbedding_apply, id_eq]
      constructor
      · rintro ⟨v, hv, a, ha, rfl⟩
        exact ⟨a, ⟨v, hv, ha⟩, rfl⟩
      · rintro ⟨a, ⟨v, hv, ha⟩, rfl⟩
        exact ⟨v, hv, a, ha, rfl⟩
    · simpa using C.not_bot_mem
  invFun C := by
    refine' ⟨C.parts.attach.map _, _, _, _⟩
    · refine' ⟨λ ⟨t, ht⟩ => t.attach.map ⟨λ ⟨n, hn⟩ =>
        (Fintype.equivFinOfCardEq rfl).symm ⟨n, _⟩, _⟩, _⟩
      swap
      · simpa using Finpartition.subset_of_mem_parts ht hn
      · rintro ⟨x, hx⟩ ⟨y, hy⟩
        simp
      · rintro ⟨x, hx⟩ ⟨y, hy⟩
        simp only [Subtype.mk.injEq]
        intro H
        obtain ⟨n, hn⟩ := Finpartition.nonempty_of_mem_parts _ hx
        simp only [Finset.ext_iff, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk,
                   true_and, Subtype.exists] at H
        specialize H ((Fintype.equivFinOfCardEq rfl).symm
          ⟨n, by simpa using Finpartition.subset_of_mem_parts hx hn⟩)
        simp only [Fin.mk.injEq, exists_prop, exists_eq_right, EmbeddingLike.apply_eq_iff_eq] at H
        exact Finpartition.eq_of_mem_of_mem hx hy hn (H.mp hn)
    · rintro u hu i hCi hiu j hji hju n hnj
      simp only [Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and,
                  Subtype.exists] at hCi
      obtain ⟨i', hi, hi'⟩ := hCi
      specialize hji hnj
      specialize hju hnj
      simp only [Finset.mem_sup, id_eq] at hju
      simp only [← hi', id_eq, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk,
                 Fin.mk.injEq, true_and, Subtype.exists, exists_prop, exists_eq_right] at hji
      obtain ⟨v, hv, hnv⟩ := hju
      specialize hu hv
      simp only [Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and,
                 Subtype.exists] at hu
      obtain ⟨w, hw, hw'⟩ := hu
      simp only [← hw', Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk,
                Fin.mk.injEq, true_and, Subtype.exists, exists_prop, exists_eq_right] at hnv
      rcases eq_or_ne i' w with rfl|H
      · rw [←hi', hw'] at hiu
        exact absurd hv hiu
      · rcases hji with ⟨X, hji, hX⟩
        rcases hnv with ⟨Y, hnv, hY⟩
        rw [←hX] at hY
        simp only [EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq] at hY
        subst hY
        exact absurd (Finpartition.eq_of_mem_of_mem hi hw hji hnv) H
    · ext n
      have := C.supParts
      rw [Finset.ext_iff] at this
      specialize this (Fintype.equivFinOfCardEq rfl n)
      simp only [Finset.mem_sup, id_eq, Finset.mem_range, Fin.is_lt, iff_true] at this
      obtain ⟨v, hv, hv'⟩ := this
      simp only [Finset.sup_map, Function.Embedding.coeFn_mk, Function.comp.left_id, Finset.mem_sup,
                 Finset.mem_attach, Finset.mem_map, true_and, Subtype.exists, Finset.mem_univ,
                 iff_true]
      refine' ⟨v, hv, Fintype.equivFinOfCardEq rfl n, hv', _⟩
      simp
    · simpa using C.not_bot_mem
  left_inv := by
    · intro C
      ext t
      simp only [Finset.le_eq_subset, Eq.ndrec, id_eq, Finset.mapEmbedding_apply,
                 Function.comp.left_id, Fin.valEmbedding_apply, eq_mpr_eq_cast, cast_eq,
                 Finset.bot_eq_empty, Finset.mem_map, Finset.mem_attach,
                 Function.Embedding.coeFn_mk, true_and, Subtype.exists, Finset.mapEmbedding_apply]
      constructor
      · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
        simp only [Finset.mapEmbedding_apply, Finset.map_eq_image, Function.Embedding.coeFn_mk]
        have hv' : ∀ x : (Finset.map
          ((Fintype.equivFinOfCardEq rfl).toEmbedding.trans Fin.valEmbedding) v),
          (x : ℕ) < Fintype.card α
        · rintro ⟨x, hx⟩
          simp only [Finset.mem_map, Fin.valEmbedding_apply] at hx
          obtain ⟨y, _, rfl⟩ := hx
          simp
        suffices : Finset.image
          (λ (x : { x // x ∈ (Finset.map
            ((Fintype.equivFinOfCardEq rfl).toEmbedding.trans Fin.valEmbedding) v)}) =>
            (Fintype.equivFinOfCardEq rfl).symm ⟨↑x, hv' x⟩)
          (Finset.attach (Finset.map
            ((Fintype.equivFinOfCardEq rfl).toEmbedding.trans Fin.valEmbedding) v)) = v
        · rw [this]
          exact hv
        ext x
        simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, Finset.mem_map,
                   Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Fin.valEmbedding_apply]
        constructor
        · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
          simp [hy]
        · rintro hx
          refine' ⟨_, ⟨x, hx, rfl⟩, _⟩
          simp
      · intro ht
        refine' ⟨t.map ((Fintype.equivFinOfCardEq rfl).toEmbedding.trans Fin.valEmbedding),
          ⟨t, ht, rfl⟩, _⟩
        ext x
        simp only [Finset.mapEmbedding_apply, Finset.mem_map, Finset.mem_attach,
                   Function.Embedding.coeFn_mk, Fin.mk.injEq, true_and, Subtype.exists,
                   Fin.valEmbedding_apply, exists_prop, exists_eq_right]
        constructor
        · rintro ⟨_, ⟨_, ha, rfl⟩, rfl⟩
          simp [ha]
        · intro ha
          refine' ⟨_, ⟨_, ha, rfl⟩, _⟩
          simp
  right_inv := by
    intro C
    ext t
    simp only [Finset.le_eq_subset, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk,
               true_and, Subtype.exists, Finset.mapEmbedding_apply]
    constructor
    · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
      simp only [Finset.map_eq_image, Function.Embedding.coeFn_mk, Finset.image_image]
      convert hw
      ext
      simp only [Finset.mem_image, Finset.mem_attach, Function.comp_apply,
                 Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.apply_symm_apply,
                 Fin.valEmbedding_apply, true_and, Subtype.exists, exists_prop, exists_eq_right]
    · intro ht
      have ht' : ∀ x ∈ t, x < Fintype.card α
      · intros x hx
        simpa using Finpartition.subset_of_mem_parts ht hx
      refine' ⟨t.attach.image (λ ⟨x, hx⟩ => (Fintype.equivFinOfCardEq rfl).symm ⟨x, ht' x hx⟩),
        ⟨t, ht, _⟩, _⟩
      · ext
        simp
      · ext x
        simp only [Finset.mem_map, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
                   Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Fin.valEmbedding_apply]
        constructor
        · rintro ⟨_, ⟨_, hx, rfl⟩, rfl⟩
          simp [hx]
        · intro hx
          refine' ⟨_, ⟨_, hx, rfl⟩, _⟩
          simp

-- 1.4
example [∀ r : Fin 3 → Fin 3 → Prop, DecidableRel r]
  [@DecidablePred (Set (Set (Fin 3))) Setoid.IsPartition] :
    Fintype.card (Setoid (Fin 3)) = 5 := by
  suffices :
    Fintype.card {C : Finset (Set (Fin 3)) // Setoid.IsPartition (C : (Set (Set (Fin 3))))} = 5
  · rw [←this, Fintype.card_eq]
    refine' ⟨(Setoid.Partition.orderIso (Fin 3)).toEquiv.trans _⟩
    refine' Equiv.subtypeEquiv (set_finset_orderIso (Set (Fin 3))) _
    intro
    simp
  suffices :
    Fintype.card (Finpartition (Finset.univ : Finset (Fin 3))) = 5
  · rw [←this, Fintype.card_eq]
    exact ⟨(Finpartition.equiv_subtype_setoid_ispartition (Fin 3)).symm⟩
  suffices :
    Fintype.card (Finpartition (Finset.range 3)) = 5
  · rw [←this, Fintype.card_eq]
    exact ⟨(Finpartition.equiv_range_fintype_card _)⟩
  have key : (Finset.univ : Finset (Finpartition (Finset.range 3))) =
    (Finset.univ : Finset (Finpartition (Finset.range 3))).filter (λ a => a.parts.card = 0) ∪
    (Finset.univ : Finset (Finpartition (Finset.range 3))).filter (λ a => a.parts.card = 1) ∪
    (Finset.univ : Finset (Finpartition (Finset.range 3))).filter (λ a => a.parts.card = 2) ∪
    (Finset.univ : Finset (Finpartition (Finset.range 3))).filter (λ a => a.parts.card = 3)
  · ext C
    simp only [Finset.mem_univ, true_iff, ←Finset.filter_or, Finset.mem_filter, true_and]
    have hC : C.parts.card ≤ 3 := C.card_parts_le_card
    rcases hC.eq_or_lt with hC|hC
    · simp [hC]
    rw [Nat.lt_succ_iff] at hC
    rcases hC.eq_or_lt with hC|hC
    · simp [hC]
    rw [Nat.lt_succ_iff] at hC
    rcases hC.eq_or_lt with hC|hC
    · simp [hC]
    rw [Nat.lt_succ_iff] at hC
    rcases hC.eq_or_lt with hC|hC
    · simp [hC]
    simp at hC
  rw [Fintype.card, key, Finset.card_union_eq, Finset.card_union_eq, Finset.card_union_eq]
  · have := Finpartition.card_range_filter_card_eq_self 2
    rw [Finpartition.card_range_succ_filter_card_zero,
        Finpartition.card_range_succ_filter_card_eq_one,
        Finpartition.card_range_filter_card_eq_self,
        Finpartition.stirling,
        Finpartition.card_range_succ_filter_card_eq_one,
        show (1 + 1 = 2) from rfl]
    sorry
        -- Finpartition.card_range_filter_card_eq_self 2]
  · refine' Finset.disjoint_filter_filter' _ _ _
    intro p hl hr x hx
    specialize hl x
    specialize hr x
    simp only [hx, le_Prop_eq, forall_true_left] at hl hr
    simp [hr] at hl
  · rw [←Finset.filter_or]
    refine' Finset.disjoint_filter_filter' _ _ _
    intro p hl hr x hx
    specialize hl x
    specialize hr x
    simp only [hx, le_Prop_eq, forall_true_left] at hl hr
    simp [hr] at hl
  · rw [←Finset.filter_or, ←Finset.filter_or]
    refine' Finset.disjoint_filter_filter' _ _ _
    intro p hl hr x hx
    specialize hl x
    specialize hr x
    simp only [hx, le_Prop_eq, forall_true_left] at hl hr
    simp [hr] at hl

end

-- Give an example of a relation that is reflexive and symmetric but not transitive.
-- What happens if you attempt to use this relation to define a partition on the set?
-- 1.5
abbrev rel15 (a b : ℤ) : Prop := max a b ≤ min a b + 1

example : (Quot.mk rel15 3) = (Quot.mk rel15 4) := by
  refine' Quot.sound _
  rw [rel15]
  simp

example : (Quot.mk rel15 4) = (Quot.mk rel15 5) := by
  refine' Quot.sound _
  rw [rel15]
  simp

lemma rel15_refl (a : ℤ) : rel15 a a := by
  simp [rel15]

lemma rel15_comm {a b : ℤ} : rel15 a b ↔ rel15 b a := by
  rw [rel15, rel15, max_comm, min_comm]

lemma rel15_add_one (a : ℤ) : rel15 a (a + 1) := by
  simp [rel15]

lemma rel15_sub_one (a : ℤ) : rel15 a (a - 1) := by
  simp [rel15]

lemma rel15_all (a b : ℤ) : Quot.mk rel15 a = Quot.mk rel15 b := by
  refine' Quot.EqvGen_sound _
  induction' hc : b - a using Int.induction_on with c IH c IH generalizing a b
  · rw [sub_eq_zero] at hc
    subst hc
    exact EqvGen.refl _
  · rw [←sub_eq_iff_eq_add, sub_sub] at hc
    have := EqvGen.rel _ _ (rel15_comm.mpr (rel15_sub_one (a + 1)))
    simpa using this.trans _ _ _ (IH _ _ hc)
  · rw [eq_comm, sub_eq_iff_eq_add, eq_comm, sub_add] at hc
    have := EqvGen.rel _ _ (rel15_comm.mpr (rel15_add_one (a - 1)))
    simpa using this.trans _ _ _ (IH _ _ hc)

-- Define a relation - on the set R of real numbers by setting a ~ b <=> b - a ∈ Z.
-- Prove that this is an equivalence relation, and find a `compelling' descriptionfor R/~.
-- Do the same for the relation on the plane R x R defined by declaring
-- (al, a2) ≈ (b1, b2) <=> b1 - a1 ∈ Z and b2 - a2 ∈ Z.
-- 1.6
def rel16 (a b : ℝ) : Prop := ∃ z : ℤ, b - a = z

instance : Setoid ℝ where
  r := rel16
  iseqv := by
    simp_rw [rel16]
    refine' ⟨_, _, _⟩
    · intro
      use 0
      simp
    · rintro _ _ ⟨z, hz⟩
      refine' ⟨-z, _⟩
      simp [←hz]
    · rintro _ _ _ ⟨z, hz⟩ ⟨w, hw⟩
      refine' ⟨w + z, _⟩
      simp [←hz, ←hw]

-- it is `add_circle`

def rel16b (a b : ℝ × ℝ) : Prop := ∃ z : ℤ × ℤ, b.1 - a.1 = z.1 ∧ b.2 - a.2 = z.2

instance : Setoid (ℝ × ℝ) where
  r := rel16b
  iseqv := by
    simp_rw [rel16b]
    refine' ⟨_, _, _⟩
    · intro
      refine' ⟨⟨0, 0⟩, _⟩
      simp
    · rintro ⟨x1, x2⟩ ⟨y1, y2⟩ ⟨⟨z11, z12⟩, hz1, hz2⟩
      refine' ⟨⟨-z11, -z12⟩, _⟩
      dsimp only at hz1 hz2
      simp [←hz1, ←hz2]
    · rintro ⟨x1, x2⟩ ⟨y1, y2⟩ ⟨z1, z2⟩ ⟨⟨a1, a2⟩, ha1, ha2⟩ ⟨⟨b1, b2⟩, hb1, hb2⟩
      dsimp only at ha1 ha2 hb1 hb2
      refine' ⟨⟨a1 + b1, a2 + b2⟩, _⟩
      simp [←ha1, ←ha2, ←hb1, ←hb2]

-- it is a torus
