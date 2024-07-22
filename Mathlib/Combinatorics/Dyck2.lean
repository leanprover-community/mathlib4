import Mathlib.Tactic.GeneralizeProofs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Sigma.Basic

set_option autoImplicit true

/--
`Dyck k l n` represents a planar matching in a rectangle,
with `k` points along the top edge, `l` points along the bottom edge,
and `n` points along the right edge (no points are allowed on the left edge),
such that points along the top and right edges are always matched wit
points along the bottom edge.

In later applications we will only be interested in `Dyck 0 l 0`,
representing a "capform" with `l` points (necessarily even),
or `Dyck k l 0`, representing a "Temperley-Lieb epimorphism",
i.e. a Temperley-Lieb diagram with `k` points along the top (and no cups)
and `l` points along the bottom (and `(l - k)/2` caps).
-/
inductive Dyck : Nat → Nat → Nat → Type
| nil : Dyck 0 0 0
| up {k l n} : Dyck k l n → Dyck k (l + 1) (n + 1)
| down {k l n} : Dyck k l (n + 1) → Dyck k (l + 1) n
| thru {k l} : Dyck k l 0 → Dyck (k + 1) (l + 1) 0

namespace Dyck

example : Dyck 0 2 0 := nil.up.down
example : Dyck 1 5 0 := nil.up.down.thru.up.down
example : Dyck 2 6 2 := nil.thru.up.down.thru.up.up

def cast (hk : k₁ = k₂) (hl : l₁ = l₂) (hn : n₁ = n₂) : Dyck k₁ l₁ n₁ → Dyck k₂ l₂ n₂ := by
  cases hk
  cases hl
  cases hn
  exact id

notation "♮" d => cast (by omega) (by omega) (by omega) d

@[simp] theorem cast_refl {k l n} (d : Dyck k l n) : (♮d) = d := by
  induction d <;> simp_all [cast]

@[simp] theorem cast_cast {k₁ k₂ k₃ l₁ l₂ l₃ n₁ n₂ n₃}
    (h₁ : k₁ = k₂) (h₂ : k₂ = k₃) (h₃ : l₁ = l₂) (h₄ : l₂ = l₃) (h₅ : n₁ = n₂) (h₆ : n₂ = n₃)
    (d : Dyck k₁ l₁ n₁) : cast h₂ h₄ h₆ (cast h₁ h₃ h₅ d) = ♮d := by
  cases h₁
  cases h₂
  cases h₃
  cases h₄
  cases h₅
  cases h₆
  rfl

@[simp] theorem up_cast {hk : k₁ = k₂} {hl : l₁ = l₂} {hn : n₁ = n₂} :
    up (cast hk hl hn d) = ♮(up d) := by
  subst hk; subst hl; subst hn; rfl

@[simp] theorem down_cast {hk : k₁ = k₂} {hl : l₁ = l₂} {hn : n₁ + 1 = n₂ + 1} :
    down (cast hk hl hn d) = ♮(down d) := by
  subst hk; subst hl; cases hn; rfl

@[simp] theorem thru_cast {hk : k₁ = k₂} {hl : l₁ = l₂} :
    thru (cast hk hl rfl d) = ♮(thru d) := by
  subst hk; subst hl; rfl

def allThru (n : Nat) : Dyck n n 0 :=
  match n with
  | 0 => .nil
  | n+1 => .thru (allThru n)

/-- Put two diagrams side-by-side. The left diagram must have no points along its right edge. -/
def juxta (d : Dyck k₁ l₁ 0) (d' : Dyck k₂ l₂ n) : Dyck (k₁ + k₂) (l₁ + l₂) n :=
  match d' with
  | nil     => d
  | up d'   => (juxta d d').up
  | down d' => (juxta d d').down
  | thru d' => (juxta d d').thru

@[simp] theorem nil_juxta {k l n} (d : Dyck k l n) :
    juxta nil d = ♮d := by
  induction d <;> simp_all [juxta]

@[simp] theorem juxta_nil : juxta d nil = d := rfl

@[simp] theorem juxta_cast {hk : k₁ = k₁'} {hl : l₁ = l₁'}
    (d : Dyck k₁ l₁ 0) (d' : Dyck k₂ l₂ n) :
    juxta (cast hk hl rfl d) d' = ♮(juxta d d') := by
  cases hk; cases hl; rfl

@[simp] theorem cast_juxta {hk : k₂ = k₂'} {hl : l₂ = l₂'} {hn : n = n'}
    (d : Dyck k₁ l₁ 0) (d' : Dyck k₂ l₂ n) :
    juxta d (cast hk hl hn d') = ♮(juxta d d') := by
  cases hk; cases hl; cases hn; rfl

theorem juxta_assoc (d₁ : Dyck k₁ l₁ 0) (d₂ : Dyck k₂ l₂ 0) (d₃ : Dyck k₃ l₃ n) :
    juxta (juxta d₁ d₂) d₃ = ♮(juxta d₁ (juxta d₂ d₃)) := by
  induction d₃ <;> simp_all [juxta]

example : nil.up.down.juxta nil.up.down = nil.up.down.up.down := rfl

/--
Stack two diagrams vertically.
The number of points along the top edge of the first diagram must match
the number of points along the bottom edge of the second diagram.
-/
def comp {k₁ k₂ l₁ n₁ n₂} (d₁ : Dyck k₁ l₁ n₁) (d₂ : Dyck k₂ k₁ n₂) : Dyck k₂ l₁ (n₁ + n₂) :=
  match d₁, d₂ with
  | nil, nil => nil
  | up d₁, d₂ => ♮(up (comp d₁ d₂))
  | down d₁, d₂ => down (♮(comp d₁ d₂))
  | thru d₁, up d₂ => up (comp d₁ d₂)
  | thru d₁, down d₂ => down (♮(comp d₁ d₂))
  | thru d₁, thru d₂ => thru (comp d₁ d₂)

example : nil.thru.up.down.thru.comp nil.up.down = nil.up.up.down.down := rfl

@[simp] theorem cast_comp {hl : l₁ = l₁'} {hn : n₁ = n₁'}
    {d₁ : Dyck k₁ l₁ n₁} {d₂ : Dyck k₂ k₁ n₂} :
    comp (cast rfl hl hn d₁) d₂ = ♮ comp d₁ d₂ := by
  cases hl; cases hn; rfl

@[simp] theorem comp_cast {hk : k₂ = k₂'} {hn : n₂ = n₂'}
    {d₁ : Dyck k₁ l₁ n₁} {d₂ : Dyck k₂ k₁ n₂} :
    comp d₁ (cast hk rfl hn d₂) = ♮ comp d₁ d₂ := by
  cases hk; cases hn; rfl

@[simp] theorem cast_comp_cast {hk₁ : k₁ = k₁'} {hl : l₁ = l₁'} {hn₁ : n₁ = n₁'}
    {hk₂ : k₂ = k₂'} {hn₂ : n₂ = n₂'} {d₁ : Dyck k₁ l₁ n₁} {d₂ : Dyck k₂ k₁ n₂} :
    comp (cast hk₁ hl hn₁ d₁) (cast hk₂ hk₁ hn₂ d₂) = ♮ comp d₁ d₂ := by
  cases hk₁; cases hl; cases hn₁; cases hk₂; cases hn₂; rfl

theorem comp_assoc {d₁ : Dyck k₁ l₂ n₁} {d₂ : Dyck k₂ k₁ n₂} {d₃ : Dyck k₃ k₂ n₃} :
    (d₁.comp d₂).comp d₃ = ♮ d₁.comp (d₂.comp d₃) :=
  match d₁, d₂, d₃ with
  | nil, nil, nil => rfl
  | up _, _, _
  | down _, _, _
  | thru _, up _, _
  | thru _, down _, _
  | thru _, thru _, up _
  | thru _, thru _, down _
  | thru _, thru _, thru _ => by cases n₃ <;> simp [comp, comp_assoc]

theorem allThru_comp {d : Dyck k l n} : comp (allThru _) d = ♮ d := sorry
theorem comp_allThru {d : Dyck k l n} : comp d (allThru _) = d := sorry

theorem juxta_comp {d₁ : Dyck k₁ l₁ 0} {d₂ : Dyck k₂ k₁ 0}
    {d₃ : Dyck k₃ l₃ n₃} {d₄ : Dyck k₄ k₃ n₄} :
    juxta (comp d₁ d₂) (comp d₃ d₄) = comp (juxta d₁ d₃) (juxta d₂ d₄) :=
  match d₃, d₄ with
  | nil, nil => rfl
  | up _, _ => by simp [juxta, comp, juxta_comp]
  | down _, _ => by simp [juxta, comp, juxta_comp]
  | thru _, up _ => by simp [juxta, comp, juxta_comp]
  | thru _, down _ => by simp [juxta, comp, juxta_comp]
  | thru _, thru _ => by simp [juxta, comp, juxta_comp]

def capRight (d : Dyck k l (n + 2)) (m : Nat := 0) (w : m ≤ n := by omega) : Dyck k l n :=
  match n, d, m, w with
  | _, up d, 0, _ => down d
  | n + 1, up d, (m + 1), _ => up (capRight d m)
  | _, down d, m, _ => down (capRight d m)

-- TODO: theorem capRight_juxta : capRight (juxta d₁ d₂) m w = juxta d₁ (capRight d₂ m w) := sorry
-- TODO: `capRight_capRight`
-- TODO: There are three cases of `capRight_comp`; one requires `capTop` to state.

/-- Pull the topmost point on the right edge to the left end of the top edge. -/
def pullUp (d : Dyck k l (n + 1)) : Dyck (k + 1) l n :=
  match n, d with
  | 0, up d => thru d
  | _, down d => down (pullUp d)
  | _ + 1, up d => up (pullUp d)

/-- Pull the leftmost point on the top edge to the upper end of the right edge. -/
def pullDown (d : Dyck (k + 1) l n) : Dyck k l (n + 1) :=
  match d with
  | thru d => up d
  | up d => up (pullDown d)
  | down d => down (pullDown d)

-- TODO: `pullDown_pullUp` and `pullUp_pullDown`

/--
Given two diagrams with the same number of points along their bottoms edges,
and the same number of points along their right edges,
we flip the first diagram vertically, then stack the second diagram above it,
and then pair up all the points along the right edge, in a nested fashion.

This results in a diagram containing some number of closed loops.
We count these as `δ`, then remove them.
The remaining diagram can be uniquely decomposed as a diagram `d₁'`
(with no points on the right edge,
and as usual all points on the top edge are paired with points on the bottom edge)
with the flip of another such diagram `d₂'` stacked above it.

We return the quadruple `⟨δ, k', d₁', d₂'⟩`, where `k'` is
the (common) number of points along the top edges of `d₁'` and `d₂'`.
-/
def revComp (d₁ : Dyck k₁ l n) (d₂ : Dyck k₂ l n) : Nat × (k' : Nat) × Dyck k' k₁ 0 × Dyck k' k₂ 0 :=
  match k₁, k₂, d₁, d₂ with
  | _, _, nil, nil => ⟨0, 0, nil, nil⟩
  | _, _, up d₁, up d₂ => match revComp d₁ d₂ with
    | ⟨δ, _, d₁', d₂'⟩ => ⟨δ + 1, _, d₁', d₂'⟩
  | _, _, up d₁, down d₂ => revComp d₁ (capRight d₂)
  | _, _, down d₁, up d₂ => revComp (capRight d₁) d₂
  | _, _, down d₁, down d₂ => revComp d₁ d₂
  | _, _, down d₁, thru d₂ => match revComp (pullUp d₁) d₂ with
    | ⟨δ, _, down d₁', d₂'⟩ => ⟨δ, _, pullUp d₁', thru d₂'⟩
    | ⟨δ, _, thru d₁', d₂'⟩ => ⟨δ, _, d₁', down (pullDown d₂')⟩
  | _, _, thru d₁, down d₂ => match revComp d₁ (pullUp d₂) with
    | ⟨δ, _, d₁', down d₂'⟩ => ⟨δ, _, thru d₁', pullUp d₂'⟩
    | ⟨δ, _, d₁', thru d₂'⟩ => ⟨δ, _, down (pullDown d₁'), d₂'⟩
  | _, _, thru d₁, thru d₂ => match revComp d₁ d₂ with
    | ⟨δ, _, d₁', d₂'⟩ => ⟨δ, _, thru d₁', thru d₂'⟩

example : revComp nil.up.down nil.up.down = ⟨1, _, nil, nil⟩ := rfl
example : revComp nil.up.up.down.down nil.up.up.down.down = ⟨2, _, nil, nil⟩ := rfl
example : revComp nil.up.up.down.down nil.up.down.up.down = ⟨1, _, nil, nil⟩ := rfl
example : revComp nil.thru nil.thru = ⟨0, _, nil.thru, nil.thru⟩ := rfl
example : revComp nil.thru.up.down nil.up.down.thru = ⟨0, _, nil.thru, nil.thru⟩ := rfl
example : revComp nil.thru.up.down nil.thru.up.down = ⟨1, _, nil.thru, nil.thru⟩ := rfl

theorem allThru_revComp (d : Dyck k l 0) : revComp (allThru l) d = ⟨0, k, d, allThru k⟩ := sorry
theorem revComp_allThru (d : Dyck k l 0) : revComp d (allThru l) = ⟨0, k, allThru k, d⟩ := sorry

theorem Sigma.ext_iff' {β : α → Type*} {x₀ x₁ : Sigma β} :
  x₀ = x₁ ↔ Nonempty ((h : x₀.fst = x₁.fst) ×' x₀.snd = h ▸ x₁.snd) := sorry

example {α α' : Type u} {β β' : Type b} (h : (α × β) = (α' × β')) : α = α' := by


theorem fst_rec (h : (α × β) = (α' × β')) (p : α × β) : (h ▸ p).1 = ()

@[simp] theorem allThru_revComp_fst : (revComp (allThru _) d).1 = 0 := by simp [allThru_revComp]
@[simp] theorem revComp_allThru_fst : (revComp a (allThru _)).1 = 0 := by simp [revComp_allThru]
@[simp] theorem allThru_revComp_snd_fst (d : Dyck k l 0) : (revComp (allThru _) d).2.1 = k := by
  simp [allThru_revComp]
@[simp] theorem revComp_allThru_snd_fst (d : Dyck k l 0) : (revComp d (allThru _)).2.1 = k := by
  simp [revComp_allThru]
@[simp] theorem allThru_revComp_snd_snd_fst {d : Dyck k l 0} :
    (revComp (allThru l) d).2.2.1 = (have := allThru_revComp_snd_fst d; ♮ d) := by
  have := congrArg Prod.snd (allThru_revComp d)
  simp [Sigma.ext_iff'] at this
  simp [this]
  sorry


@[simp] theorem revComp_allThru_fst : (revComp a (allThru _)).1 = 0 := by simp [revComp_allThru]

end Dyck

structure TLDiagram (src tgt : Nat) where
  loops : Nat := 0
  girth : Nat
  epi : Dyck girth src 0
  mono : Dyck girth tgt 0

namespace TLDiagram

open Dyck

@[ext] theorem ext {x y : TLDiagram n m}
    (hloops : x.loops = y.loops) (hgirth : x.girth = y.girth)
    (hepi : x.epi = ♮ y.epi) (hmono : x.mono = ♮ y.mono) : x = y := by
  cases x
  cases y
  cases hgirth
  simp_all

@[simps]
def id (n : Nat) : TLDiagram n n where
  epi := allThru n
  mono := allThru n

@[simps]
def comp (x : TLDiagram n m) (y : TLDiagram m k) : TLDiagram n k :=
  match revComp x.mono y.epi with
  | ⟨loops', _, epi', mono'⟩ =>
    { loops := x.loops + y.loops + loops'
      epi := Dyck.comp x.epi epi'
      mono := Dyck.comp y.mono mono' }

@[simp] theorem id_comp : comp (id _) x = x := by
  ext
  · simp
  · simp
  · simp
    rw [allThru_revComp]


@[simp] theorem comp_id : comp x (id _) = x := sorry

@[simp] theorem comp_assoc : comp (comp x y) z = comp x (comp y z) := sorry

end TLDiagram

def TL := Nat

namespace TL

open TLDiagram CategoryTheory

instance : Category TL where
  Hom := TLDiagram
  id := id
  comp := comp

end TL
