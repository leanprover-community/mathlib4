import Mathlib.SetTheory.SmallSet

universe u v

-- Note to reviewer: Is there a standard identifier for edge labels? (e.g. in graph theory?)
/-- `PreWFTree.{u} η` is the type of well-founded trees with edges labelled by `η`
  and children indexed by arbitrary types in `u`.

Unlike `WFTree`, `PreWFTree` is sensitive to the order and multiplicity of children.
In other words, `PreWFTree` is to `WFTree` as `List` is to `Finset`.-/
inductive PreWFTree (η : Type v) : Type (max (u + 1) v) where
  | mk : (η → (ι : Type u) × (ι → PreWFTree η)) → PreWFTree η

namespace PreWFTree

variable {η : Type v}

abbrev Index : PreWFTree.{u} η → η → Type u
  | ⟨f⟩, e => (f e).1

abbrev child : (t : PreWFTree.{u} η) → (e : η) → t.Index e → PreWFTree.{u} η
  | ⟨f⟩, e, i => (f e).2 i

noncomputable def children (t : PreWFTree.{u} η) (e : η) : SmallSet.{u} (PreWFTree.{u} η) :=
  SmallSet.range (t.child e)

noncomputable def ofChildren (f : η → SmallSet.{u} (PreWFTree.{u} η)) : PreWFTree.{u} η :=
  ⟨fun e ↦ ⟨Shrink.{u} (f e), fun x ↦ (equivShrink (f e)).symm x⟩⟩

@[simp]
lemma children_ofChildren (f : η → SmallSet.{u} (PreWFTree.{u} η)) :
    children (ofChildren f) = f := by
  ext e
  simp only [children, ofChildren, SmallSet.mem_range, child]
  refine ⟨fun ⟨i, h⟩ ↦ ?_, fun h ↦ ?_⟩
  · generalize ht : (equivShrink ↥(f e)).symm i = t
    rw [ht] at h
    subst h
    simp
  · use (equivShrink (f e)) ⟨_, h⟩
    simp

-- Not true!
-- @[simp]
-- lemma ofChildren_children (t : PreWFTree.{u} η) : ofChildren (children t) = t :=
--   sorry

noncomputable def children' : (t : PreWFTree.{u} η) → (e : η) → Set (PreWFTree.{u} η)
  | ⟨f⟩, e => Set.range (f e).2

instance small_children' : ∀ (t : PreWFTree.{u} η) (e : η), Small.{u} (t.children' e)
  | ⟨f⟩, e => inferInstanceAs (Small.{u} (Set.range (f e).2))

noncomputable def ofChildren' (f : η → Set (PreWFTree.{u} η)) [∀ e, Small.{u} (f e)] :
    PreWFTree.{u} η :=
  ⟨fun e ↦ ⟨Shrink.{u} (f e), fun x ↦ (equivShrink (f e)).symm x⟩⟩

@[simp]
lemma children'_mk (f : (η → (ι : Type u) × (ι → PreWFTree η))) :
    children' (mk f) = fun e ↦ Set.range (f e).2 := rfl

@[simp]
lemma children'_ofChildren' (f : η → Set (PreWFTree.{u} η)) [∀ e, Small.{u} (f e)] :
    children' (ofChildren' f) = f := by
  simp only [ofChildren', children'_mk]
  funext e
  have := EquivLike.range_comp (fun x : f e ↦ (x : PreWFTree.{u} η)) (equivShrink ↑(f e)).symm
  rw [Function.comp_def] at this
  simp [this]

#check PLift

def IsChildOf (t₁ t₂ : PreWFTree.{u} η) : Prop :=
  ∃ e, t₁ ∈ t₂.children' e

instance : WellFoundedRelation (PreWFTree.{u} η) where
  rel := IsChildOf
  wf := by
    constructor
    intro t
    apply PreWFTree.recOn (motive_1 := Acc IsChildOf) (motive_2 := fun ⟨ι, f⟩ ↦ ∀ i : ι, Acc IsChildOf (f i))
    · intro f ih
      constructor
      intro t' ⟨e, ht'⟩
      simp at ht'
      specialize ih e
      generalize f e = p at ih ht'
      rcases p with ⟨ι, f'⟩
      dsimp at ih ht'
      specialize ih ht'.choose
      rw [ht'.choose_spec] at ih
      exact ih
    · intro ι f ih
      intro i
      apply ih

def Equiv (t₁ t₂ : PreWFTree.{u} η) : Prop :=
  ∀ e, Relator.BiTotal fun (⟨c₁, h₁⟩ : t₁.children' e) (⟨c₂, _⟩ : t₂.children' e) ↦
    have : c₁.IsChildOf t₁ := ⟨e, h₁⟩
    Equiv c₁ c₂
termination_by t₁

-- theorem equiv_iff (t₁ t₂ : PreWFTree.{u} η) :
--     Equiv t₁ t₂ ↔ ∀ e, Relator.BiTotal
--       fun (⟨c₁, _⟩ : t₁.children' e)
--         (⟨c₂, _⟩ : t₂.children' e) ↦ Equiv c₁ c₂ := by
--   rw [Equiv]

theorem equiv_iff' (t₁ t₂ : PreWFTree.{u} η) :
    Equiv t₁ t₂ ↔ ∀ e,
      (∀ c₁ ∈ t₁.children' e, ∃ c₂ ∈ t₂.children' e, Equiv c₁ c₂) ∧
      ∀ c₂ ∈ t₂.children' e, ∃ c₁ ∈ t₁.children' e, Equiv c₁ c₂ := by
  rw [Equiv]
  simp [Relator.BiTotal, Relator.LeftTotal, Relator.RightTotal]

@[refl]
protected theorem Equiv.refl (t : PreWFTree.{u} η) : Equiv t t := by
  rw [equiv_iff']
  intro e
  constructor
  <;> exact fun c hc ↦ ⟨c, hc, have : c.IsChildOf t := ⟨e, hc⟩; Equiv.refl c⟩
termination_by t

protected theorem Equiv.euc {x y z : PreWFTree.{u} η} : Equiv x y → Equiv z y → Equiv x z := by
  rw [equiv_iff' x y, equiv_iff' z y, equiv_iff' x z]
  intro hxy hzy e
  specialize hxy e
  specialize hzy e
  constructor
  · peel hxy.left with cx hcx h
    rcases h with ⟨cy, hcy, hcxy⟩
    peel hzy.right cy hcy with cz hcz hcxz
    have : cx.IsChildOf x := ⟨e, hcx⟩
    exact Equiv.euc hcxy hcxz
  · peel hzy.left with cz hcz h
    rcases h with ⟨cy, hcy, hczy⟩
    peel hxy.right cy hcy with cx hcx hcxy
    have : cx.IsChildOf x := ⟨e, hcx⟩
    exact Equiv.euc hcxy hczy
termination_by x

@[symm]
protected theorem Equiv.symm {x y : PreWFTree.{u} η} : Equiv x y → Equiv y x :=
  (Equiv.refl y).euc

protected theorem Equiv.comm {x y : PreWFTree.{u} η} : Equiv x y ↔ Equiv y x :=
  ⟨Equiv.symm, Equiv.symm⟩

@[trans]
protected theorem Equiv.trans {x y z : PreWFTree.{u} η} (h1 : Equiv x y) (h2 : Equiv y z) :
    Equiv x z :=
  h1.euc h2.symm

instance setoid : Setoid (PreWFTree.{u} η) :=
  ⟨Equiv, Equiv.refl, Equiv.symm, Equiv.trans⟩

theorem equiv_iff {x y : PreWFTree.{u} η} :
    Equiv x y ↔ ∀ e c,
      (∃ c₁ ∈ x.children' e, Equiv c₁ c) ↔
      (∃ c₂ ∈ y.children' e, Equiv c₂ c) := by
  rw [equiv_iff', forall_congr']
  intro e
  constructor
  · intro ⟨hxy, hyx⟩ z
    constructor
    · intro ⟨cx, hcx, hcxz⟩
      have ⟨cy, hcy, hcxy⟩ := hxy cx hcx
      use cy, hcy, hcxy.symm.euc hcxz.symm
    · intro ⟨cy, hcy, hcyz⟩
      have ⟨cx, hcx, hcxy⟩ := hyx cy hcy
      use cx, hcx, Equiv.trans hcxy hcyz
  · intro h
    constructor
    · intro cx hcx
      conv => congr; ext; rw [Equiv.comm]
      rw [← h]
      use cx, hcx, Equiv.refl cx
    · intro cy hcy
      rw [h]
      use cy, hcy, Equiv.refl cy


-- inductive Equiv' : PreWFTree.{u} η → PreWFTree.{u} η → Prop where
-- | intro {t t'} (f : (e : η) → (t e).1 → (t' e).1) (g : (e : η) → (t' e).1 → (t e).1)
--   (hf : ∀ e, ∀ i₁, Equiv' ((t e).2 i₁) ((t' e).2 (f e i₁)))
--   (hg : ∀ e, ∀ i₂, Equiv' ((t e).2 (g e i₂)) ((t' e).2 i₂)) : Equiv' ⟨t⟩ ⟨t'⟩

end PreWFTree

/-- `WFTree.{u} η` is the type of well-founded trees with edges labelled by `η`
  and children as `u`-small sets. -/
def WFTree (η : Type v) : Type (max (u + 1) v) :=
  Quotient (PreWFTree.setoid.{u} (η := η))

namespace WFTree

variable {η : Type v}

noncomputable def children' (t : WFTree.{u} η) (e : η) : Set (WFTree.{u} η) :=
  Quotient.liftOn t (fun t ↦ (⟦·⟧) '' t.children' e) fun x y h ↦ by
    ext z
    induction' z using Quotient.ind with z
    simp only [Set.mem_image]
    convert PreWFTree.equiv_iff.mp h e z
    <;> rw [Quotient.eq] -- simp [Quotient.eq] fails.. discrtree bug?
    <;> rfl

instance small_children' (t : WFTree.{u} η) (e : η) : Small.{u} (t.children' e) := by
  induction' t using Quotient.ind with t
  simp only [children', Quotient.lift_mk]
  exact inferInstance

noncomputable def ofChildren' (f : η → Set (WFTree.{u} η)) [∀ e, Small.{u} (f e)] : WFTree.{u} η :=
  ⟦PreWFTree.ofChildren' fun e ↦ Quotient.out '' f e⟧

@[simp]
lemma children'_ofChildren' (f : η → Set (WFTree.{u} η)) [∀ e, Small.{u} (f e)] :
    children' (ofChildren' f) = f := by
  ext e t
  simp [children', ofChildren', Quotient.mk'_eq_mk]

@[ext]
lemma ext {t₁ t₂ : WFTree.{u} η} (h : t₁.children' = t₂.children') : t₁ = t₂ := by
  induction' t₁ using Quotient.ind with t₁
  induction' t₂ using Quotient.ind with t₂
  apply Quotient.sound
  change t₁.Equiv t₂
  rw [PreWFTree.equiv_iff]
  simp_rw [Function.funext_iff, Set.ext_iff] at h
  peel h with e h
  erw [Quotient.forall] at h
  simp [children'] at h
  convert h
  <;> rw [Quotient.eq]
  <;> rfl

@[simp]
lemma ofChildren'_children (t : WFTree.{u} η) : ofChildren' (children' t) = t := by
  ext
  simp

noncomputable def ofChildren_equiv :
    { f : η → Set (WFTree.{u} η) // ∀ e, Small.{u} (f e)} ≃ WFTree.{u} η where
  toFun := fun ⟨f, hf⟩ ↦ ofChildren' f
  invFun t := ⟨t.children', inferInstance⟩
  left_inv := fun ⟨f, hf⟩ ↦ by simp
  right_inv t := by simp

end WFTree
