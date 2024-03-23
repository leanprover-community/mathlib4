import Mathlib.Data.Bool.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic
/-!
# Graphs (a la Serre)

This file defines graphs, as defined by Serre in his book Trees. A graph is a type `V` of vertices, a type `E` of edges, and functions `ι : E → V` and `bar : E → E` satisfying some axioms.

We also define paths of graphs and homotopy between paths via reduction. To define paths it is useful to define a type for edges between two vertices.

We show that paths are determined by their initial vertices and list of edges. This is convenient as it allows us to avoid some of the subtleties of indexed inductive types.
-/
universe u v

/--
Graph a la Serre.
-/
@[class] structure SerreGraph (V : Type u) (E : Type v) where
  /-- The initial vertex of an edge in the Graph `G`. -/
  ι : E → V
  /-- Edge with reversed orientation. -/
  bar : E → E
  /-- Reversing the orientation of an edge is an involution. -/
  bar_bar : ∀ e, bar (bar e) = e
  /-- An edge reversed is different from itself. -/
  bar_ne_self : ∀ e, e ≠ bar e

namespace SerreGraph

variable {V V₁ : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
(G : SerreGraph V E)
variable {u u' v w : V}

attribute [simp] bar_bar

/-- Terminal vertex of an edge in the graph `G`-/
def τ (e : E) : V := G.ι (G.bar e)

@[simp] theorem ι_bar (e : E) :  G.ι (G.bar e) = G.τ e := rfl

@[simp] theorem τ_bar (e : E) :  G.τ (G.bar e) = G.ι e := by
  aesop (add norm unfold [τ])

/-- Edge with given initial vertex in the graph `G` -/
@[ext] structure EdgeFrom (v : V) where
  /-- The edge -/
  edge : E
  /-- `edge` has initial vertex `v`  -/
  init_eq : G.ι edge = v
deriving DecidableEq

/-- Edge with given initial and terminal vertice in the graph `G` -/
@[ext] structure EdgeBetween (v w : V) where
  edge : E
  init_eq : G.ι edge = v
  term_eq : G.τ edge = w
deriving DecidableEq

attribute [aesop safe forward] EdgeBetween.init_eq EdgeBetween.term_eq

variable {G} (e : G.EdgeBetween v w)

/-- Reversing the orientation for an edge between `v` and `w`. -/
def EdgeBetween.bar (e : G.EdgeBetween v w) : G.EdgeBetween w v :=
  { edge := G.bar e.edge
  , init_eq := by aesop
  , term_eq := by aesop
  }

/-- Edge as edge between specified vertices. -/
def EdgeBetween.ofEdge (e : E) : G.EdgeBetween (G.ι e) (G.τ e) where
  edge := e
  init_eq := rfl
  term_eq := rfl

@[simp] lemma EdgeBetween.ofEdge_eq_self (e : E) :
  (EdgeBetween.ofEdge (G := G) e).edge = e := rfl

@[simp] theorem EdgeBetween.bar_eq_bar : e.bar.edge = G.bar e.edge := rfl

@[simp] theorem EdgeBetween.bar_bar : e.bar.bar = e := by
    ext; aesop (add norm simp [EdgeBetween.bar])

-- @[aesop unsafe [cases, constructors]]
/-- A path consisting of edges of the graph `G` between specified vertices. -/
inductive EdgePath (G : SerreGraph V E) : V → V → Type _ where
  | nil (v) : G.EdgePath v v
  | cons {v w u} : G.EdgeBetween v w → G.EdgePath w u → G.EdgePath v u
deriving DecidableEq

/-- Path with a single edge -/
abbrev singletonPath (e : G.EdgeBetween u v) := EdgePath.cons e (.nil v)

namespace EdgePath

/-- Length of a path -/
def length {v w : V} : G.EdgePath v w → ℕ
  | nil _ => 0
  | cons _ p'  => p'.length.succ

/-- Concatenation of an edge between `w` and `u` to a path between `v` and `w`. -/
def concat {v w u : V} (p : G.EdgePath v w) (e : G.EdgeBetween w u) : G.EdgePath v u :=
  match p with
  | nil .(v) => cons e (nil u)
  | cons  e' p'  => cons e' (concat p' e)

@[simp] theorem concat_cons {v w u u': V} (e: G.EdgeBetween v w) (p: G.EdgePath w u) (e': G.EdgeBetween u u')  :
    concat (cons e p) e' = cons e (concat p e') := by rfl

/-- Reverse of a path -/
def reverse {v w : V} (p : G.EdgePath v w) : G.EdgePath w v :=
  match p with
  | nil .(v) =>
      nil v
  | cons  e p  =>
      concat (reverse p) e.bar

@[simp] theorem reverse_nil {v : V} :
  reverse (.nil (G := G) v) = .nil (G := G) v := by rfl

theorem reverse_cons {v w u : V} (e : G.EdgeBetween v w) (p : G.EdgePath w u) :
    reverse (cons e p) = concat (reverse p) e.bar := by rfl

theorem reverse_concat {v w u : V} (p: G.EdgePath v w) (e: G.EdgeBetween w u) :
    reverse (concat p e) = cons e.bar (reverse p) := by
    induction p <;> aesop (add norm simp [concat_cons, reverse_cons])

/-- Appending a path between `w` and `u` to a path between `v` and `w` -/
def append { v w u : V}
    (p : G.EdgePath v w) (q : G.EdgePath w u) : G.EdgePath v u :=
  match p with
  | nil .(v) => q
  | cons  e' p'  =>
      cons e' <| append p' q

/-- Folding a function along a path -/
def fold {A : Type _}(φ : {u v : V} → G.EdgeBetween u v → A) (comp : A → A → A) (init : A) {v w : V} : G.EdgePath v w → A
  | .nil _ => init
  | .cons e p => comp (φ e) (fold φ comp init p)

/--Appending paths using `_++_` -/
instance  G.edgePathAppend {v w u : V} {G : SerreGraph V E} :
  HAppend (G.EdgePath v w) (G.EdgePath w u) (G.EdgePath v u) :=
    ⟨append⟩

@[simp] theorem nil_append  {u v : V} (p: G.EdgePath u v) :
  EdgePath.nil (G := G) u ++ p = p := rfl

@[simp] theorem append_nil  {u v : V} (p: G.EdgePath u v) :
  p ++ EdgePath.nil (G := G) v = p := by
    show append _ _ = _
    induction p <;> aesop (add norm simp [append])

@[simp] theorem cons_append {v' v w u : V}
    (e: G.EdgeBetween v' v)(p: G.EdgePath v w)(q: G.EdgePath w u) :
    (cons e p) ++ q = cons e (p ++ q) := by rfl

@[simp] theorem concat_append { v w w' u : V}
    (e : G.EdgeBetween w w')(p: G.EdgePath v w)(q: G.EdgePath w' u) :
    (concat p e) ++ q = p ++ (cons e q) := by
    induction p <;> aesop

theorem append_concat {v w w' u : V} (e : EdgeBetween G w' u)(p: EdgePath G v w)(q: EdgePath G w w') :
  p ++ (concat q e) = concat (p ++ q) e := by
  induction p <;> aesop

theorem cons_eq_append_singletonPath {u v w : V} (e : G.EdgeBetween u v) (p : G.EdgePath v w) :
    EdgePath.cons e p = G.singletonPath e ++ p := rfl

theorem singletonPath_bar (e : G.EdgeBetween u v) : G.singletonPath e.bar = reverse (G.singletonPath e) := rfl

theorem concat_eq_append_edge {v w u : V} (e : G.EdgeBetween w u) (p : G.EdgePath v w) :
    p.concat e = p ++ (cons e (nil u)) := by
  have := concat_append e p (.nil _)
  aesop

theorem append_assoc { v w u u' :  V}
  (p: G.EdgePath v w)(q: G.EdgePath w u)(r: G.EdgePath u u') :
    (p ++ q) ++ r = p ++ (q ++ r) := by
    induction p <;> aesop

@[simp] theorem reverse_reverse {v w : V} (p : G.EdgePath v w) :
  p.reverse.reverse = p := by
  induction p <;> aesop (add norm simp [reverse_cons, reverse_concat])

theorem reverse_append {u v w : V} (p : G.EdgePath u v)
  (q : G.EdgePath v w) :
    (p ++ q).reverse = q.reverse ++ p.reverse := by
  induction p <;>
    aesop (add norm simp [reverse_cons, concat_eq_append_edge, append_assoc])

/-!
## Lists of edges

We associate lists of edges to paths in the obvious way. Note that lists of edges are not typically associated to paths. However, they determine the paths.

This makes proofs of paths much easier by avoiding the need to reason about indexed inductive types.
-/

def toList {G : SerreGraph V E} {v w : V} (p : EdgePath G v w) :
  List E :=
  match p with
  | nil _ => []
  | cons e p' =>  e.edge :: p'.toList

theorem nil_toList {G : SerreGraph V E} {v : V}  :
  (nil v : EdgePath G v v).toList = [] := rfl

theorem cons_toList {G: SerreGraph V E} {v w u: V} (e : EdgeBetween G v w)
    (p : EdgePath G w u) :
  (cons e p).toList = e.edge :: p.toList := rfl

theorem append_toList {G : SerreGraph V E}{v w u : V} (p₁ : EdgePath G v w) (p₂ : EdgePath G w u) :
    (p₁ ++ p₂).toList = p₁.toList ++ p₂.toList := by
    induction p₁ with
    | nil v =>
      simp [nil_toList]
    | cons e p' ih =>
      simp [cons_toList]
      apply ih

theorem concat_toList {G : SerreGraph V E}{v w u : V} (p : EdgePath G v w) (e : EdgeBetween G w u) :
    (concat p e).toList = List.concat p.toList e.edge := by
    induction p with
    | nil v =>
      simp [nil_toList]
      rw [concat, cons_toList, nil_toList]
    | cons e p' ih =>
      simp [cons_toList, ih]

theorem reverse_toList {G : SerreGraph V E}{v w : V} (p : EdgePath G v w):
  p.reverse.toList  = p.toList.reverse.map (G.bar) := by
  induction p with
  | nil _ =>
    simp [nil_toList]
  | cons e p' ih =>
    simp [cons_toList, reverse_cons, concat_toList]
    simp [ih, EdgeBetween.bar]

theorem toList_reverse {G : SerreGraph V E}{v w : V} (p : EdgePath G v w):
  p.toList.reverse = p.reverse.toList.map (G.bar) := by
  induction p with
  | nil _ =>
    simp [nil_toList]
  | cons e p' ih =>
    simp [cons_toList, reverse_cons, concat_toList]
    simp [ih, EdgeBetween.bar]

/--
Initial vertices of a path.
-/
def initVerts (p : G.EdgePath u v) : List V :=
  p.toList.map G.ι

/--
Terminal vertices of a path.
-/
def termVerts (p : G.EdgePath u v) : List V :=
  p.toList.map G.τ

@[ext] theorem eq_of_toList_eq {G: SerreGraph V E}{v w: V}
  (p₁ p₂ : EdgePath G v w) : p₁.toList = p₂.toList → p₁ = p₂ := by
  induction p₁ with
  | nil v =>
    match p₂ with
    | EdgePath.nil v =>
      intro h
      rw [nil_toList] at h
    | EdgePath.cons e₂ p₂  =>
      intro h
      simp [cons_toList, nil_toList] at h
  | cons e₁ p₁' ih =>
    intro h
    induction p₂ with
    | nil w =>
      simp [cons_toList, nil_toList] at h
    | cons e₂ p₂'  =>
      simp [cons_toList] at h
      have e1t := e₁.term_eq
      have e2t := e₂.term_eq
      rw [h.1] at e1t
      rw [e1t] at e2t
      cases e2t
      congr
      · ext
        exact h.1
      · apply ih
        exact h.2

theorem eq_of_edge_eq {G: SerreGraph V E}{v w: V}
  (e₁ e₂ : EdgeBetween G v w) : e₁.edge = e₂.edge → e₁ = e₂ := by
      intro h
      ext
      exact h

theorem terminal_eq_of_toList_eq {G: SerreGraph V E}{v₁ v₂ w₁ w₂: V}
  (p₁ : EdgePath G v₁ w₁) (p₂ : EdgePath G v₂ w₂) : p₁.toList = p₂.toList → (v₁ = v₂) → (w₁ = w₂)  := by
  induction p₁ with
  | nil v₁' =>
    match p₂ with
    | EdgePath.nil v =>
      intro h heq
      rw [nil_toList] at h
      exact heq
    | EdgePath.cons e₂ p₂  =>
      intro h
      simp [cons_toList, nil_toList] at h
  | cons e p₁' ih =>
    intro h heq
    match p₂ with
    | EdgePath.nil w =>
      simp [cons_toList, nil_toList] at h
    | EdgePath.cons e₂ p₂' =>
      simp [cons_toList] at h
      apply terminal_eq_of_toList_eq p₁' p₂' h.right
      rw [←e₂.term_eq, ←e.term_eq, h.left]

/--
Edgepath obtained by shifting the target of an edgepath along an equality.
-/
def shiftTarget {G: SerreGraph V E}{v w w' : V}
  (p : EdgePath G v w)(eql : w = w'):  EdgePath G v w' := by
  match p, w', eql with
  | nil _, _, rfl =>
    exact (nil v)
  | cons e p', w', eql =>
    exact cons e (shiftTarget p' eql)

theorem toList_shiftTarget {G: SerreGraph V E}{v w w' : V}
  (p : EdgePath G v w)(eql : w = w'):
  (shiftTarget p eql).toList = p.toList := by
  match p, w', eql with
  | nil _, _, rfl =>
    rename_i v'
    simp only [shiftTarget]
  | cons e p', w', eql =>
    simp only [shiftTarget, cons_toList, toList_shiftTarget]

/--
Edgepath obtained by shifting the ends of an edgepath along equalities.
-/
def shiftEnds {G: SerreGraph V E}{v v' w w' : V}
  (p : EdgePath G v w)(eqlv : v = v')(eqlw : w = w'):
    EdgePath G v' w' := by
  match p, w', eqlv, eqlw with
  | nil _, _, rfl, rfl =>
    exact (nil v)
  | cons e p', w', rfl,  eqlw =>
    exact cons e (shiftTarget p' eqlw)

theorem toList_shiftEnds {G: SerreGraph V E}{v v' w w' : V}
  (p : EdgePath G v w)(eqlv : v = v')(eqlw : w = w'):
  (shiftEnds p eqlv eqlw).toList = p.toList := by
  match p, w', eqlv, eqlw with
  | nil _, _, rfl, rfl =>
    simp only [shiftEnds]
  | cons e p', w', rfl,  eqlw =>
    simp only [shiftEnds, cons_toList, toList_shiftTarget]


/-- Sequence of reductions of a path by cancelling adjacent edges that are inverses. -/
@[aesop safe [constructors, cases]]
inductive Reduction {v w : V}:
      G.EdgePath v w →  G.EdgePath v w →  Prop where
  /-- A cancellation of adjacent edges that are reductions -/
  | step (u u' : V)(e : G.EdgeBetween u u') (p₁ : G.EdgePath v u) (p₂ : G.EdgePath u w) :
      Reduction (p₁ ++ (cons e (cons e.bar p₂))) (p₁ ++ p₂)

/-- A path being reduced, i.e., admitting no reductions. -/
def reduced  {v w : V} (p : G.EdgePath v w) : Prop :=
  ∀ p', ¬ Reduction p p'

/-- Reduction data and the corresponding relation -/
theorem Reduction.property {v w : V} {p' : G.EdgePath v w}(p : G.EdgePath v w) :
  Reduction p p' →
  ∃ u u': V, ∃ e : G.EdgeBetween u u',
    ∃ p₁ : G.EdgePath v u,
    ∃ p₂ : G.EdgePath u w,
      p₁ ++ (cons e (cons e.bar p₂)) = p
| Reduction.step u u' e' p₁ p₂ => by
  use u, u', e', p₁, p₂

end EdgePath

open EdgePath

theorem not_reduced_of_split {v w u u': V}{p : G.EdgePath v w}
    {e : G.EdgeBetween u u'}{p₁ : G.EdgePath v u}{p₂ : G.EdgePath u w} :
    p = p₁ ++ (cons e (cons e.bar p₂)) → ¬ reduced p := by
  intro eqn red
  have red' := red (p₁ ++ p₂)
  rw [eqn] at red'
  apply red'
  apply Reduction.step

theorem tail_reduced {u v w : V} (e: EdgeBetween G u v)
    (p : G.EdgePath v w) : reduced (cons e p) → reduced p := by
  intro red p' red'
  let ⟨u, u', e', p₁, p₂, eqn⟩   := red'.property
  let eqn' : (cons e p₁) ++ cons e' (cons e'.bar p₂) =
    cons e p := by
      simp [cons_append]
      exact eqn
  let h' := not_reduced_of_split (Eq.symm eqn')
  contradiction

theorem reverse_reduced {v w : V} (p : G.EdgePath v w): reduced p →   reduced p.reverse := by
  intro red rev_targ rev_red
  let ⟨u, u', e, p₁, p₂, eqn⟩   := rev_red.property
  apply red (reverse p₂ ++ reverse p₁)
  let eqn' := congrArg reverse eqn
  simp [reverse_reverse] at eqn'
  have eqn'' : (reverse p₂) ++ (cons e (cons e.bar (reverse p₁))) =
    p := by
      rw [←eqn', reverse_append]
      simp [reverse_cons]
  rw [←eqn'']
  apply Reduction.step

theorem reverse_reduced_iff {v w : V} (p : G.EdgePath v w) :
  reduced p ↔ reduced p.reverse := by
  apply Iff.intro
  · exact reverse_reduced p
  · intro h
    rw [← reverse_reverse p]
    apply reverse_reduced
    assumption

/-- Paths up to the equivalence relation generated by reduction. -/
abbrev PathClass (G: SerreGraph V E) (v w : V)  :=
    Quot <| @Reduction _ _ G v w

/-- The class of a path up to the equivalence generated by reduction. -/
abbrev homotopyClass  {v w : V} (p : G.EdgePath v w) :
   PathClass G v w  :=
  Quot.mk _ p

notation "[[" p "]]" => homotopyClass p

attribute [aesop safe apply] Quot.sound

@[simp] theorem append_cons_bar_cons (e : G.EdgeBetween u u') (p₁ : G.EdgePath v u) (p₂ : G.EdgePath u w) :
    [[p₁ ++ (p₂ |>.cons e.bar |>.cons e)]] = [[p₁ ++ p₂]] := by
  have := Reduction.step _ _ e p₁ p₂
  aesop

@[simp] theorem append_cons_cons_bar (e : G.EdgeBetween u' u) (p₁ : G.EdgePath v u) (p₂ : G.EdgePath u w) :
  [[p₁ ++ (p₂ |>.cons e |>.cons e.bar)]] = [[p₁ ++ p₂]] := by
  have := append_cons_bar_cons e.bar p₁ p₂
  aesop

theorem left_append_step {v w u : V} (a : G.EdgePath v w)  (b₁ b₂ : G.EdgePath w u)  (rel : Reduction  b₁ b₂) :
   [[a ++ b₁]] = [[a ++ b₂]] := by
    induction rel
    repeat (rw [← append_assoc])
    aesop

theorem right_append_step {v w u : V} (a₁ a₂ : G.EdgePath v w)  (b : G.EdgePath w u) (rel : Reduction  a₁ a₂) :
    [[a₁ ++ b]] = [[a₂ ++ b]] := by
  aesop (add norm simp [append_assoc])

theorem reverse_step {v w : V} (a₁ a₂ : G.EdgePath v w) (rel : Reduction a₁ a₂) :
    [[a₁.reverse]] = [[a₂.reverse]] := by
  induction rel
  aesop (add norm simp [reverse_append, reverse_cons])

@[simp] theorem reverse_append_self {v w : V}
(p : G.EdgePath v w) :
    [[p.reverse ++ p]] = [[.nil w]] := by
    induction p <;>
      aesop (add norm simp [reverse_cons, reverse_concat, cons_append])

@[simp] theorem self_append_reverse {v w : V} (p : G.EdgePath w v) :
    [[p ++ p.reverse]] = [[.nil w]] := by
  have := reverse_append_self p.reverse
  aesop

namespace PathClass

/--
The constant path, identity in the fundamental group.
-/
@[aesop norm unfold]
protected def id {G : SerreGraph V E} (v : V) : G.PathClass v v :=
  [[.nil v]]

/--
The constant path, identity in the fundamental group, with graph explicit.
-/
@[aesop norm unfold]
protected def id' (G : SerreGraph V E) (v : V) : G.PathClass v v :=
  [[.nil v]]

protected def mul {v w u : V} :
    G.PathClass v w → G.PathClass w u → G.PathClass v u := by
  apply Quot.lift₂ (fun p₁ p₂ ↦ [[ p₁ ++ p₂ ]])
  · rename_i _ _ u_1 v_1 w_1
    intro a b₁ b₂ a_1
    apply SerreGraph.left_append_step
    simp_all only
  · rename_i _ _ u_1 v_1 w_1
    intro a₁ a₂ b a
    apply SerreGraph.right_append_step
    simp_all only


@[aesop norm unfold]
protected def inv {u v : V} : G.PathClass u v → G.PathClass v u :=
  Quot.lift ([[·.reverse]]) reverse_step

theorem inv_equiv_reverse {v w : V} (η : EdgePath G v w):
  [[ η ]].inv = [[ η.reverse ]] := by
    rfl

instance {v w u: V}: HMul (G.PathClass v w) (G.PathClass w u) (G.PathClass v u) where
  hMul := PathClass.mul

end PathClass


@[local simp] lemma mul_path_path (p : G.EdgePath u v) (p' : G.EdgePath v w) :
  [[p]] * [[p']] = [[p ++ p']] := rfl

theorem cons_equiv_of_equiv{G: SerreGraph V E}{v w u : V} (a : EdgeBetween G v w)  (b₁ b₂ : EdgePath G w u) : [[b₁]] = [[b₂]] →
   [[cons a  b₁]] = [[cons a b₂]] := by
  intro r
  rw [show cons a b₁ = cons a (nil _) ++ b₁ by rfl,
      show cons a b₂ = cons a (nil _) ++ b₂ by rfl,
      ← mul_path_path, ← mul_path_path, r]

theorem concat_equiv_of_equiv {G: SerreGraph V E}{v w u : V} (a₁ a₂ : EdgePath G v w)  (b : EdgeBetween G w u) : [[a₁]] = [[a₂]] →
   [[concat a₁ b]] = [[concat a₂ b]] := by
  intro r
  have: concat a₁  b = a₁ ++ (concat (nil _) b) := by
    rw [append_concat, append_nil]
  rw [this]
  have: concat a₂  b = a₂ ++ (concat (nil _) b) := by
    rw [append_concat, append_nil]
  rw [this, ← mul_path_path, ← mul_path_path, r]

abbrev π₁ (G: SerreGraph V E) (v : V) := G.PathClass v v

@[local simp] lemma mul_path_path' (p : G.EdgePath u v) (p' : G.EdgePath v w) :
  .mul [[p]] [[p']] = [[p ++ p']] := rfl


namespace PathClass

protected theorem mul_assoc { v w u u' :  V}:
  (p : G.PathClass v w) → (q : G.PathClass w  u) →
  (r : G.PathClass u  u') →
    (p * q) * r = p * (q * r) := by
    apply Quot.ind
    intro a
    apply Quot.ind
    intro b
    apply Quot.ind
    intro c
    simp [append_assoc]

def ind {β : (PathClass G u v) → Prop} :
   (∀ p : G.EdgePath u v, β [[p]]) → (∀ q : PathClass G u v, β q) :=
  Quot.ind

@[simp] protected theorem id_mul  {u v : V} : ∀ p : PathClass G u v,
  (PathClass.id' G u) * p = p := by
    apply PathClass.ind; aesop

@[simp] protected theorem mul_id  {u v : V} : ∀ p : PathClass G u v,
    p * (PathClass.id' G v) = p := by
  apply PathClass.ind; aesop

@[simp] protected theorem inv_mul {u v : V} : ∀ p : PathClass G u v,
    p.inv * p = PathClass.id' G v := by
  apply PathClass.ind; aesop

@[simp] protected theorem mul_inv {u v : V} : ∀ p : PathClass G u v,
    p * p.inv = PathClass.id' G u := by
  apply PathClass.ind; aesop

protected theorem inv_eq : ∀ {p : G.PathClass u v} {q : G.PathClass v u},
    p.inv = q → p = q.inv := by
  apply PathClass.ind; aesop

protected theorem eq_inv {p : G.PathClass u v} {q : G.PathClass v u} :
    p = q.inv → p.inv = q := fun h ↦
  (PathClass.inv_eq h.symm).symm

instance : Group (π₁ G v) where
  mul := PathClass.mul
  mul_assoc := PathClass.mul_assoc
  one := .id v
  one_mul := PathClass.id_mul
  mul_one := PathClass.mul_id
  inv := PathClass.inv
  mul_left_inv := PathClass.inv_mul

def wedgeCircles (S: Type) : SerreGraph Unit (S × Bool) := {
  ι := fun _ ↦ ()
  bar := fun (e, b) ↦ (e, !b)
  bar_bar := by aesop
  bar_ne_self := by aesop
}

@[ext]
structure PathClassFrom (G : SerreGraph V E) (v : V) where
  τ  : V
  pathClass : PathClass G v τ
