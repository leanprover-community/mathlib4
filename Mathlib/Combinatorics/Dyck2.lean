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

@[simp] theorem rec₁_cast {h : k₁ = k₂} {d : Dyck k₁ l n} : h ▸ d = ♮ d := by
  cases h
  simp
@[simp] theorem rec₂_cast {h : l₁ = l₂} {d : Dyck k l₁ n} : h ▸ d = ♮ d := by
  cases h
  simp
@[simp] theorem rec₃_cast {h : n₁ = n₂} {d : Dyck k l n₁} : h ▸ d = ♮ d := by
  cases h
  simp

def allThru (n : Nat) : Dyck n n 0 :=
  match n with
  | 0 => .nil
  | n+1 => .thru (allThru n)

@[simp] theorem allThru_zero : allThru 0 = .nil := rfl
@[simp] theorem allThru_succ : allThru (n+1) = .thru (allThru n) := rfl

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

@[simp] theorem nil_comp {d : Dyck k 0 n} : comp nil d = ♮ d := by cases d; rfl
@[simp] theorem comp_nil : comp d nil = nil := by cases d; rfl
@[simp] theorem up_comp {d₁ : Dyck k₁ l n₁} {d₂ : Dyck k₂ k₁ n₂} :
    comp (up d₁) d₂ = ♮(up (comp d₁ d₂)) := rfl
@[simp] theorem down_comp {d₁ : Dyck k₁ l (n₁+1)} {d₂ : Dyck k₂ k₁ n₂} :
    comp (down d₁) d₂ = down (♮(comp d₁ d₂)) := rfl
@[simp] theorem thru_comp_up : comp (thru d₁) (up d₂) = up (comp d₁ d₂) := rfl
@[simp] theorem thru_comp_down {d₁ : Dyck k₁ l 0} {d₂ : Dyck k₂ k₁ (n₂+1)} :
    comp (thru d₁) (down d₂) = down (♮(comp d₁ d₂)) := rfl
@[simp] theorem thru_comp_thru : comp (thru d₁) (thru d₂) = thru (comp d₁ d₂) := rfl

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

theorem down_comp_zero {a : Dyck k l (n+1)} {b : Dyck k' k 0} :
    down (n := n) (comp (n₁ := n+1) a b) = comp (down a) b := sorry

theorem allThru_comp {d : Dyck k l n} : comp (allThru _) d = ♮ d := by
  induction l generalizing k n with
  | zero => cases d <;> rfl
  | succ l ih => cases d <;> simp_all [comp]

theorem comp_allThru {d : Dyck k l n} : comp d (allThru _) = d := by
  induction l generalizing k n with
  | zero => cases d <;> rfl
  | succ l ih => cases d <;> simp_all [comp]

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

@[simp] theorem capRight_comp_zero {d₁ : Dyck k l (n + 2)} {d₂ : Dyck k' k 0} :
    capRight (n := n) (comp (n₁ := n + 2) d₁ d₂) 0 = comp (capRight d₁ 0) d₂ := sorry

-- TODO: theorem capRight_juxta : capRight (juxta d₁ d₂) m w = juxta d₁ (capRight d₂ m w) := sorry
-- TODO: `capRight_capRight`
-- TODO: There are more cases of `capRight_comp`; one requires `capTop` to state.

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

@[simp] theorem pullDown_pullUp {d : Dyck k l (n + 1)} : pullDown (pullUp d) = d := by
  match n, d with
  | 0, .up d => simp [pullUp, pullDown]
  | _, .down d => simp [pullUp, pullDown, pullDown_pullUp]
  | _ + 1, up d => simp [pullUp, pullDown, pullDown_pullUp]
@[simp] theorem pullUp_pullDown : pullUp (pullDown d) = d := by
  match d with
  | .thru d => simp [pullUp, pullDown]
  | .up d => simp [pullUp, pullDown, pullUp_pullDown]
  | .down d => simp [pullUp, pullDown, pullUp_pullDown]

@[simp] theorem pullUp_comp {a : Dyck k l (n + 1)} {b : Dyck k' k 0} :
    pullUp (n := n) (comp (n₁ := n + 1) a b) = comp (pullUp a) (thru b) := sorry

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

theorem ext_iff {x y : TLDiagram n m} :
    x = y ↔ x.loops = y.loops ∧
      Nonempty ((h : x.girth = y.girth) ×' (x.epi = ♮ y.epi) ∧ (x.mono = ♮ y.mono)) :=
  sorry

@[simps] def addLoops (d : TLDiagram n m) (k : Nat) : TLDiagram n m :=
  { d with loops := d.loops + k }

@[simp] theorem addLoops_zero : addLoops d 0 = d := rfl
@[simp] theorem addLoops_addLoops : addLoops (addLoops d k₁) k₂ = addLoops d (k₁ + k₂) := by
  ext <;> simp <;> omega
@[simp] theorem addLoops_inj : addLoops d k = addLoops d' k ↔ d = d' := sorry

@[simps]
def thru (d : TLDiagram n m) : TLDiagram (n+1) (m+1) where
  loops := d.loops
  girth := d.girth + 1
  epi := d.epi.thru
  mono := d.mono.thru

@[simp] theorem thru_addLoops : (addLoops d k).thru = d.thru.addLoops k := sorry

def pullUp (d : TLDiagram (n+1) m) : TLDiagram n (m+1) :=
  match d with
  | ⟨δ, _, .down x, y⟩ => ⟨δ, _, x.pullUp, y.thru⟩
  | ⟨δ, _, .thru x, y⟩ => ⟨δ, _, x, y.pullDown.down⟩

@[simp] theorem pullUp_loops : (pullUp d).loops = d.loops := sorry
@[simp] theorem pullUp_addLoops : (addLoops d k).pullUp = d.pullUp.addLoops k := sorry
@[simp] theorem pullUp_down : pullUp ⟨δ, _, .down x, y⟩ = ⟨δ, _, x.pullUp, y.thru⟩ := rfl
@[simp] theorem pullUp_thru : pullUp ⟨δ, _, .thru x, y⟩ = ⟨δ, _, x, y.pullDown.down⟩ := rfl

def pullDown (d : TLDiagram n (m+1)) : TLDiagram (n+1) m :=
  match d with
  | ⟨δ, _, x, .down y⟩ => ⟨δ, _, x.thru, y.pullUp⟩
  | ⟨δ, _, x, .thru y⟩ => ⟨δ, _, x.pullDown.down, y⟩

@[simp] theorem pullDown_loops : (pullDown d).loops = d.loops := sorry
@[simp] theorem pullDown_addLoops : (addLoops d k).pullDown = d.pullDown.addLoops k := sorry
@[simp] theorem pullDown_down : pullDown ⟨δ, _, x, .down y⟩ = ⟨δ, _, x.thru, y.pullUp⟩ := rfl
@[simp] theorem pullDown_thru : pullDown ⟨δ, _, x, .thru y⟩ = ⟨δ, _, x.pullDown.down, y⟩ := rfl

end TLDiagram

namespace Dyck

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
def revComp (d₁ : Dyck k₁ l n) (d₂ : Dyck k₂ l n) : TLDiagram k₁ k₂ :=
  match k₁, k₂, d₁, d₂ with
  | _, _, nil, nil => ⟨0, 0, nil, nil⟩
  | _, _, up d₁, up d₂ => (revComp d₁ d₂).addLoops 1
  | _, _, up d₁, down d₂ => revComp d₁ (capRight d₂)
  | _, _, down d₁, up d₂ => revComp (capRight d₁) d₂
  | _, _, down d₁, down d₂ => revComp d₁ d₂
  | _, _, down d₁, thru d₂ => (revComp (pullUp d₁) d₂).pullUp
  | _, _, thru d₁, down d₂ => (revComp d₁ (pullUp d₂)).pullDown
  | _, _, thru d₁, thru d₂ => (revComp d₁ d₂).thru

example : revComp nil.up.down nil.up.down = ⟨1, _, nil, nil⟩ := rfl
example : revComp nil.up.up.down.down nil.up.up.down.down = ⟨2, _, nil, nil⟩ := rfl
example : revComp nil.up.up.down.down nil.up.down.up.down = ⟨1, _, nil, nil⟩ := rfl
example : revComp nil.thru nil.thru = ⟨0, _, nil.thru, nil.thru⟩ := rfl
example : revComp nil.thru.up.down nil.up.down.thru = ⟨0, _, nil.thru, nil.thru⟩ := rfl
example : revComp nil.thru.up.down nil.thru.up.down = ⟨1, _, nil.thru, nil.thru⟩ := rfl


-- theorem Sigma.ext_iff' {β : α → Type*} {x₀ x₁ : Sigma β} :
--     x₀ = x₁ ↔ Nonempty ((h : x₀.fst = x₁.fst) ×' x₀.snd = h ▸ x₁.snd) := by
--   constructor
--   · rintro rfl; simp
--   · rcases x₀ with ⟨a₀, b₀⟩
--     rcases x₁ with ⟨a₁, b₁⟩
--     rintro ⟨h, w⟩
--     simp at h
--     subst h
--     simp_all

-- theorem Sigma.prod_ext_iff {β₁ β₂ : α → Type*} {x₀ x₁ : Σ a, β₁ a × β₂ a} :
--     x₀ = x₁ ↔
--       Nonempty ((h : x₀.fst = x₁.fst) ×' (x₀.2.1 = h ▸ x₁.2.1) ∧ (x₀.2.2 = h ▸ x₁.2.2)) := by
--   constructor
--   · rintro rfl; simp
--   · rcases x₀ with ⟨a₀, b₀, c₀⟩
--     rcases x₁ with ⟨a₁, b₁, c₁⟩
--     rintro ⟨h, w₁, w₂⟩
--     simp at h
--     subst h
--     simp_all

theorem allThru_revComp (d : Dyck k l 0) : revComp (allThru l) d = ⟨0, k, d, allThru k⟩ := by
  induction l generalizing k with
  | zero => cases d <;> simp [revComp]
  | succ l ih =>
    cases d with
    | down => simp_all only [revComp, allThru_succ, TLDiagram.pullDown_thru, pullDown_pullUp]
    | thru d =>
      specialize ih d
      rw [TLDiagram.ext_iff] at ih
      obtain ⟨h₀, ⟨h, w₁, h₂⟩⟩ := ih
      simp_all [revComp, TLDiagram.ext_iff]
theorem revComp_allThru (d : Dyck k l 0) : revComp d (allThru l) = ⟨0, k, allThru k, d⟩ := by
  induction l generalizing k with
  | zero => cases d <;> simp [revComp]
  | succ l ih =>
    cases d with
    | down => simp_all only [revComp, allThru_succ, TLDiagram.pullUp_thru, pullDown_pullUp]
    | thru d =>
      specialize ih d
      rw [TLDiagram.ext_iff] at ih
      obtain ⟨h₀, ⟨h, w₁, h₂⟩⟩ := ih
      simp_all [revComp, TLDiagram.ext_iff]

@[simp] theorem allThru_revComp_loops : (revComp (allThru _) d).loops = 0 := by
  simp [allThru_revComp]
@[simp] theorem revComp_allThru_loops : (revComp a (allThru _)).loops = 0 := by
  simp [revComp_allThru]
@[simp] theorem allThru_revComp_girth (d : Dyck k l 0) : (revComp (allThru _) d).girth = k := by
  simp [allThru_revComp]
@[simp] theorem revComp_allThru_girth (d : Dyck k l 0) : (revComp d (allThru _)).girth = k := by
  simp [revComp_allThru]
@[simp] theorem allThru_revComp_epi {d : Dyck k l 0} :
    (revComp (allThru l) d).epi = (have := allThru_revComp_girth d; ♮ d) := by
  have := allThru_revComp d
  simp_all [TLDiagram.ext_iff]
@[simp] theorem allThru_revComp_mono {d : Dyck k l 0} :
    (revComp (allThru l) d).mono = (have := allThru_revComp_girth d; ♮(allThru k)) := by
  have := allThru_revComp d
  simp_all [TLDiagram.ext_iff]
@[simp] theorem revComp_allThru_epi {d : Dyck k l 0} :
    (revComp d (allThru l)).epi = (have := revComp_allThru_girth d; ♮(allThru k)) := by
  have := revComp_allThru d
  simp_all [TLDiagram.ext_iff]
@[simp] theorem revComp_allThru_mono {d : Dyck k l 0} :
    (revComp d (allThru l)).mono = (have := revComp_allThru_girth d; ♮ d) := by
  have := revComp_allThru d
  simp_all [TLDiagram.ext_iff]

end Dyck

namespace TLDiagram

open Dyck

@[simps]
def dyckComp (d₁ : Dyck k₂ k₁ 0) (d₂ : TLDiagram k₂ k₃) : TLDiagram k₁ k₃ where
  loops := d₂.loops
  girth := d₂.girth
  epi := d₁.comp d₂.epi
  mono := d₂.mono

@[simps]
def compDyck (d₁ : TLDiagram k₁ k₂) (d₂ : Dyck k₂ k₃ 0) : TLDiagram k₁ k₃ where
  loops := d₁.loops
  girth := d₁.girth
  epi := d₁.epi
  mono := d₂.comp d₁.mono

@[simp] theorem dyckComp_thru_thru : dyckComp d₁.thru d₂.thru = (dyckComp d₁ d₂).thru := sorry

-- @[simp] theorem dyckComp_inj : dyckComp d₁ d₂ = dyckComp d₁ d₃ ↔ d₂ = d₃ := sorry
-- @[simp] theorem compDyck_inj : compDyck d₁ d₃ = compDyck d₂ d₃ ↔ d₁ = d₂ := sorry

def dyckRevComp (d₁ : Dyck k₁ k₂ 0) (d₂ : TLDiagram k₂ k₃) : TLDiagram k₁ k₃ :=
  compDyck (revComp d₁ d₂.epi) d₂.mono

def compDyckRev (d₁ : TLDiagram k₁ k₂) (d₂ : Dyck k₃ k₂ 0) : TLDiagram k₁ k₃ :=
  dyckComp d₁.epi (revComp d₁.mono d₂)

def comp (d₁ : TLDiagram k₁ k₂) (d₂ : TLDiagram k₂ k₃) : TLDiagram k₁ k₃ :=
  dyckComp d₁.epi (dyckRevComp d₁.mono d₂)

def comp' (d₁ : TLDiagram k₁ k₂) (d₂ : TLDiagram k₂ k₃) : TLDiagram k₁ k₃ :=
  compDyck (compDyckRev d₁ d₂.epi) d₂.mono

theorem dyckComp_compDyck : compDyck (dyckComp d₁ d₂) d₃ = dyckComp d₁ (compDyck d₂ d₃) := sorry

theorem comp'_eq_comp : comp' d₁ d₂ = comp d₁ d₂ := dyckComp_compDyck ..

theorem dyckComp_compDyckRev : compDyckRev (dyckComp d₁ d₂) d₃ = dyckComp d₁ (compDyckRev d₂ d₃) :=
  sorry

theorem dyckRevComp_compDyck : dyckRevComp d₁ (compDyck d₂ d₃) = compDyck (dyckRevComp d₁ d₂) d₃ :=
  sorry

end TLDiagram

open TLDiagram

namespace Dyck

theorem revComp_comp {a : Dyck k₁ k₂ n} {b : Dyck k₃ k₂ n} {c : Dyck k₄ k₃ 0} :
    revComp a (comp b c) =
      (dyckComp (revComp a b).epi (revComp (revComp a b).mono c)).addLoops (revComp a b).loops := by
  match k₂, k₃, k₄, n, b, c with
  | _, _ ,_ ,_ , nil, nil => cases a; simp [revComp, dyckComp]
  | _, _ ,_ ,_ , up b, c =>
    simp only [up_comp, Nat.add_zero, cast_refl]
    match k₁, a with
    | _, up a => simp [revComp, revComp_comp]
    | _, down a => simp [revComp, revComp_comp]
  | _, _ ,_ , n, down b, c =>
    simp only [down_comp, Nat.add_zero, cast_refl]
    match n, k₁, a with
    | _, _, up a => simp [revComp, revComp_comp]
    | _, _, down a => simp [revComp, revComp_comp]
    | _, _, thru a =>
      rw [revComp]
      rw [pullUp_comp]
      rw [revComp_comp]
      rw [revComp]
      simp
      sorry
  | _, _ ,_ ,_ , thru b, down c =>
    simp only [thru_comp_down, Nat.add_zero, Nat.reduceAdd, cast_refl]
    match n, k₁, a with
    | _, _, down a =>
      rw [revComp]
      sorry
    | _, _, thru a =>
      rw [revComp]
      sorry
  | _, _ ,_ ,_ , thru b, thru c =>
    simp
    match n, k₁, a with
    | _, _, down a =>
      rw [revComp]
      sorry
    | _, _, thru a => simp [revComp, revComp_comp]

@[simp] theorem revComp_comp_loops {a : Dyck k₁ k₂ n} {b : Dyck k₃ k₂ n} {c : Dyck k₄ k₃ 0} :
    (revComp a (comp b c)).loops = (revComp a b).loops + (revComp (revComp a b).mono c).loops :=
  sorry

@[simp] theorem revComp_comp_girth (a : Dyck k₁ k₂ n) (b : Dyck k₃ k₂ n) (c : Dyck k₄ k₃ 0) :
    (revComp a (comp b c)).girth = (revComp (revComp a b).mono c).girth := sorry

@[simp] theorem revComp_comp_epi {a : Dyck k₁ k₂ n} {b : Dyck k₃ k₂ n} {c : Dyck k₄ k₃ 0} :
    (revComp a (comp b c)).epi =
      (have := revComp_comp_girth a b c;
       ♮((revComp a b).epi.comp (revComp (revComp a b).mono c).epi)) :=
  sorry

@[simp] theorem revComp_comp_mono {a : Dyck k₁ k₂ n} {b : Dyck k₃ k₂ n} {c : Dyck k₄ k₃ 0} :
    (revComp a (comp b c)).mono =
      (have := revComp_comp_girth a b c;
       ♮(revComp (revComp a b).mono c).mono) :=
  sorry

@[simp] theorem comp_revComp_loops {a : Dyck k₁ k₂ n} {b : Dyck k₃ k₁ 0} {c : Dyck k₄ k₂ n} :
    (revComp (comp a b) c).loops = (revComp a c).loops + (revComp b (revComp a c).epi).loops :=
  sorry

@[simp] theorem comp_revComp_girth (a : Dyck k₁ k₂ n) (b : Dyck k₃ k₁ 0) (c : Dyck k₄ k₂ n) :
    (revComp (comp a b) c).girth = (revComp b (revComp a c).epi).girth :=
  sorry

@[simp] theorem comp_revComp_epi {a : Dyck k₁ k₂ n} {b : Dyck k₃ k₁ 0} {c : Dyck k₄ k₂ n} :
    (revComp (comp a b) c).epi =
      (have := comp_revComp_girth a b c;
       ♮(revComp b (revComp a c).epi).epi) :=
  sorry

@[simp] theorem comp_revComp_mono {a : Dyck k₁ k₂ n} {b : Dyck k₃ k₁ 0} {c : Dyck k₄ k₂ n} :
    (revComp (comp a b) c).mono =
      (have := comp_revComp_girth a b c;
       ♮((revComp a c).mono.comp (revComp b (revComp a c).epi).mono)) :=
  sorry

variable (a : Dyck k₁ k₂ n) (b : Dyck k₃ k₂ n) (c : Dyck k₃ k₄ n') (d : Dyck k₅ k₄ n')

theorem loops :
    (c.revComp d).loops + (a.revComp (b.comp (c.revComp d).epi)).loops =
      (a.revComp b).loops + ((c.comp (a.revComp b).mono).revComp d).loops := by
  rw [revComp_comp_loops, comp_revComp_loops]
  omega

-- theorem foo :
--     dyckComp (revComp a b).epi (revComp (comp c (revComp a b).mono) d) =
--       compDyck (revComp a (comp b (revComp c d).epi)) (revComp c d).mono := by
--   ext
--   · sorry
--   · sorry
--   · simp
--   · simp

end Dyck

namespace TLDiagram

theorem dyckRevComp_compDyckRev :
    compDyckRev (dyckRevComp x y) z = dyckRevComp x (compDyckRev y z) := by
  dsimp [dyckRevComp, compDyckRev]
  ext
  · sorry
  · simp
  · simp
  · simp

@[simp] theorem comp_assoc : comp (comp x y) z = comp x (comp y z) := by
  nth_rewrite 4 [← comp'_eq_comp]
  nth_rewrite 1 [← comp'_eq_comp]
  dsimp [comp, comp']
  rw [dyckComp_compDyckRev, dyckComp_compDyck, dyckRevComp_compDyck, dyckRevComp_compDyckRev]

open Dyck

@[simps]
def id (n : Nat) : TLDiagram n n where
  epi := allThru n
  mono := allThru n

-- @[simps]
-- def comp (x : TLDiagram n m) (y : TLDiagram m k) : TLDiagram n k :=
--   match revComp x.mono y.epi with
--   | ⟨loops', _, epi', mono'⟩ =>
--     { loops := x.loops + y.loops + loops'
--       epi := Dyck.comp x.epi epi'
--       mono := Dyck.comp y.mono mono' }

@[simp] theorem id_comp : comp (id _) x = x := by
  ext <;> simp [allThru_comp, comp_allThru]

@[simp] theorem comp_id : comp x (id _) = x := by
  ext <;> simp [allThru_comp, comp_allThru]

-- @[simp] theorem comp_assoc : comp (comp x y) z = comp x (comp y z) := by
--   ext <;> simp_all

end TLDiagram

def TL := Nat

namespace TL

open TLDiagram CategoryTheory

instance : Category TL where
  Hom := TLDiagram
  id := id
  comp := comp

end TL
