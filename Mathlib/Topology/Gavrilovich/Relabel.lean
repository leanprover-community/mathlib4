/-
Copyright (c) 2026 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.Tactic.Gavrilovich.Elab.Full

/-!
# Isomorphisms between finite spaces

The names of points are part of the type of a space, so `⌜o → c⌟` and `⌜T → F⌟` are different
(isomorphic) objects of `TopCat`. This file relates such spaces, and morphisms of them.

* `Space.relabel : Space L E ⟶ Space L' E'` is the canonical isomorphism between two spaces of the
  same shape, found automatically (by `gav_relabel`): the analogue of `eqToHom` for spaces that
  differ only in the names of their points. E.g. `(Space.relabel : ⌜o → c⌟ ⟶ ⌜T → F⌟)`. `simp`
  evaluates it at points and normalizes it: `relabel ≫ relabel = relabel`, and `relabel = 𝟙` when it
  is the identity; likewise pointwise, `relabel (relabel x) = relabel x`, also with diagram
  morphisms. `Space.relabelIso` is the same as an isomorphism, and `Space.relabelHomeo` as a
  homeomorphism, which can also change universes.
* `Space.iso f` (and `Space.homeo f`) is the isomorphism (homeomorphism) given by a bijection `f`
  between the points of two spaces, whose inverse is computed, e.g.
  `Space.iso fun | pt(o) => pt(F) | pt(c) => pt(T)`.
* `Space.arrowIso : Arrow.mk f ≅ Arrow.mk f'` is an isomorphism between two morphisms of the same
  shape, found automatically (by `gav_arrow_iso`). E.g.
  `(Space.arrowIso : Arrow.mk (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) ≅ Arrow.mk (⌜T → F⌟ ⇢ ⌜T ↔ F⌟))`. This transports
  lifting properties, by `HasLiftingProperty.iff_of_arrow_iso_left` and its variants. Sides that
  aren't spaces (`⊤_ TopCat`, say) must agree, and are related by the identity.

Morphisms between spaces have decidable equality, so `decide` proves equations between them, such
as naturality squares. They are also a `Fintype` (and `FinEnum`), enumerated as diagram morphisms
`Space.homOfTable t _ _`, so `decide` proves statements about all of them, and `fin_cases f` (or
`pt_cases f`) splits a morphism `f` into its possible values, printed as `(⌜…⌟ ⇢ ⌜…⌟)`.
-/

public meta section

namespace Gavrilovich

/-- The name of a point, as in `pt(o)`. -/
syntax gavName := ident <|> num <|> str

/-- `x ↦ o`: the point named `x` goes to the point named `o`. -/
syntax gavRenaming := gavName " ↦ " gavName

/-- `gav_relabel` proves a goal `Space.Relabelling L E L' E'`, i.e. finds an isomorphism between
two spaces of the same shape. It keeps as many names as possible, and otherwise keeps points in
order (sorted by name).

`gav_relabel [x ↦ o, y ↦ c]` finds one that sends the point named `x` to the point named `o`, and
`y` to `c`. The points not mentioned are chosen as before. -/
syntax (name := gavRelabel) "gav_relabel" (" [" gavRenaming,* "]")? : tactic

/-- `relabel[x ↦ o, y ↦ c]` is `Space.relabel` with the relabelling sending `x` to `o` and `y` to
`c` (and the points not mentioned chosen by `gav_relabel`). It is scoped to
`Mathlib.Tactic.Gavrilovich`.

If it names the image of every point, then it determines its target from its source (or its
source from its target), so `f ≫ relabel[o ↦ x, c ↦ y]` needs no type ascription. -/
scoped syntax (name := relabelStx) "relabel[" gavRenaming,* "]" : term

/-- `relabelIso[x ↦ o, y ↦ c]` is `Space.relabelIso` with the given relabelling, as for
`relabel[…]`. -/
scoped syntax (name := relabelIsoStx) "relabelIso[" gavRenaming,* "]" : term

/-- `relabelHomeo[x ↦ o, y ↦ c]` is `Space.relabelHomeo` with the given relabelling, as for
`relabel[…]`. -/
scoped syntax (name := relabelHomeoStx) "relabelHomeo[" gavRenaming,* "]" : term

/-- `gav_relabelling%[x ↦ o, …]` elaborates to the relabelling (of the expected type
`Space.Relabelling L E L' E'`) asked for by the renaming, as `gav_relabel [x ↦ o, …]` would.

The relabelling is computed as soon as possible, rather than in a tactic block, which would run
last: otherwise, in `simpa using f ≫ relabel[…]` say, `simp` would see the relabelling (and perhaps
a space) as a metavariable. That is, when both spaces are known, or one is and the renaming
determines the other; otherwise it waits, and if that doesn't help, it completes a partial renaming
(see `completeSpace`) or, with neither space known, leaves it to `gav_relabel`. -/
syntax (name := gavRelabelling) "gav_relabelling%[" gavRenaming,* "]" : term

/-- `gav_relabel_of` proves a goal `Space.RelabellingOf f`, i.e. computes the relabelling given by a
bijection `f` between the points of two spaces, checking that it and its inverse are continuous. -/
syntax (name := gavRelabelOf) "gav_relabel_of" : tactic

/-- `gav_arrow_iso` proves a goal `Arrow.mk f ≅ Arrow.mk f'`, where `f : A ⟶ B` and `f' : A' ⟶ B'`
are morphisms of the same shape: each of `A`, `A'` and `B`, `B'` is either a pair of isomorphic
spaces (related by `Space.relabelIso`), or the same object (related by the identity). It prefers
isomorphisms that keep points with the same names. -/
syntax (name := gavArrowIso) "gav_arrow_iso" : tactic

end Gavrilovich

end

@[expose] public section

universe u v

namespace Gavrilovich

open _root_.CategoryTheory

namespace Space
variable {α β : Type} {L : List (List α)} {L' : List (List β)} {E E' : List (ℕ × ℕ)}

/-- Morphisms between spaces are determined by their values at the (finitely many) points. -/
instance : DecidableEq (Space.{u} L E ⟶ Space.{u} L' E') := fun f g =>
  decidable_of_iff (∀ x ∈ all, f x = g x) Space.hom_ext_iff.symm

/-! ### Enumerating morphisms -/

/-- For each `j < m`, the indices reachable from `j` along `E'`: the points below the `j`-th point
of a space with edges `E'`. -/
def reachTable (m : ℕ) (E' : List (ℕ × ℕ)) : List (List ℕ) :=
  (List.range m).map fun j => reach (E'.length + 1) E' [j]

lemma mem_getD_reachTable {m j k : ℕ} (hj : j < m) :
    k ∈ (reachTable m E').getD j [] ↔ Relation.ReflTransGen (fun a b => (a, b) ∈ E') j k := by
  simp [reachTable, hj, mem_reach_iff]

/-- The pairs `(a, b)` of distinct indices `< n` such that `b` is reachable from `a` along `E`: for
`n = L.length`, the relations `b ≤ a` between distinct points of `Space L E`. -/
def lePairs (n : ℕ) (E : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun a =>
    ((reach (E.length + 1) E [a]).filter fun b => b < n && b != a).map (a, ·)

lemma mem_lePairs {n a b : ℕ} : (a, b) ∈ lePairs n E ↔
    a < n ∧ b < n ∧ b ≠ a ∧ Relation.ReflTransGen (fun a b => (a, b) ∈ E) a b := by
  simp [lePairs, mem_reach_iff]; grind

/-- The table `t`, listing the images of the points from the `o`-th on, respects the relation `p`
(with `R = reachTable m E'`). -/
def PairOK (R : List (List ℕ)) (o : ℕ) (t : List ℕ) (p : ℕ × ℕ) : Bool :=
  (R.getD (t.getD (p.1 - o) 0) []).contains (t.getD (p.2 - o) 0)

lemma pairOK_cons {R : List (List ℕ)} {o o' i : ℕ} {s : List ℕ} {p : ℕ × ℕ} (ho : o' = o + 1)
    (h₁ : o' ≤ p.1) (h₂ : o' ≤ p.2) : PairOK R o (i :: s) p = PairOK R o' s p := by
  subst ho
  obtain ⟨a, b⟩ := p
  simp only [PairOK]
  rw [show a - o = a - (o + 1) + 1 by omega, show b - o = b - (o + 1) + 1 by omega]
  simp

/-- The tables of the morphisms `Space L E ⟶ Space L' E'` restricted to the last `k` of the
`n = L.length` points, for `P = lePairs n E` and `R = reachTable L'.length E'`, in lexicographic
order. They are built an entry at a time, from the last, checking each relation as soon as both of
its points have entries, so that only tables of morphisms (of the last points) are extended,
rather than all `m ^ k` lists. -/
def monoTables (m n : ℕ) (P : List (ℕ × ℕ)) (R : List (List ℕ)) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 =>
    let ts := monoTables m n P R k
    let P := P.filter fun p => min p.1 p.2 == n - (k + 1)
    (List.range m).flatMap fun i => ts.filterMap fun t =>
      if P.all (PairOK R (n - (k + 1)) (i :: t)) then some (i :: t) else none

lemma mem_monoTables {m n : ℕ} {P : List (ℕ × ℕ)} {R : List (List ℕ)} :
    ∀ {k : ℕ} {t : List ℕ}, k ≤ n → t.length = k → (∀ i ∈ t, i < m) →
      (∀ p ∈ P, n - k ≤ min p.1 p.2 → PairOK R (n - k) t p) → t ∈ monoTables m n P R k
  | 0, t, _, ht, _, _ => by simp_all [monoTables]
  | k + 1, [], _, ht, _, _ => by simp at ht
  | k + 1, i :: s, hk, ht, hm, hP => by
    simp only [monoTables, List.mem_flatMap, List.mem_range, List.mem_filterMap]
    refine ⟨i, hm i (by simp), s, mem_monoTables (by omega) (by simpa using ht)
      (fun j hj => hm j (by simp [hj])) (fun p hp hp' => ?_), ?_⟩
    · rw [← pairOK_cons (o := n - (k + 1)) (i := i) (by omega) (by omega) (by omega)]
      exact hP p hp (by omega)
    · have : (P.filter fun p => min p.1 p.2 == n - (k + 1)).all
          (PairOK R (n - (k + 1)) (i :: s)) := by
        simpa using fun a b hp =>
          or_iff_not_imp_left.2 fun h => hP (a, b) hp (by simp at h ⊢; omega)
      simp [this]

lemma nodup_monoTables (m n : ℕ) (P : List (ℕ × ℕ)) (R : List (List ℕ)) :
    ∀ k, (monoTables m n P R k).Nodup
  | 0 => by simp [monoTables]
  | k + 1 => by
    rw [monoTables, List.nodup_flatMap]
    refine ⟨fun i _ => (nodup_monoTables m n P R k).filterMap fun t t' u h h' => ?_, ?_⟩
    · simp only [Option.mem_def, Option.ite_none_right_eq_some, Option.some.injEq] at h h'
      exact (List.cons_eq_cons.1 (h.2.trans h'.2.symm)).2
    · exact List.nodup_range.pairwise_of_forall_ne fun i _ j _ hij => by
        simp only [Function.onFun, List.disjoint_left, List.mem_filterMap,
          Option.ite_none_right_eq_some, Option.some.injEq]
        rintro _ ⟨t, -, -, rfl⟩ ⟨t', -, -, h⟩
        exact hij (List.cons_eq_cons.1 h).1.symm

/-- The continuity condition of `Space.homOfTable` for the table `t`. -/
abbrev TableMono (L : List (List α)) (E : List (ℕ × ℕ)) (L' : List (List β)) (E' : List (ℕ × ℕ))
    (h : 0 < L'.length) (t : List ℕ) : Prop :=
  ∀ x y : Pts.{0} L E, x ≤ y →
    (Pts.ofNat h (t.getD x.idx 0) : Pts.{0} L' E') ≤ Pts.ofNat h (t.getD y.idx 0)

/-- A table with entries `< L'.length` is monotone iff it respects the relations `lePairs`. -/
lemma tableMono_iff {h : 0 < L'.length} {t : List ℕ} (ht : ∀ i ∈ t, i < L'.length) :
    TableMono L E L' E' h t ↔
      ∀ p ∈ lePairs L.length E, PairOK (reachTable L'.length E') 0 t p := by
  have hlt (k : ℕ) : t.getD k 0 < L'.length := by
    rw [List.getD_eq_getElem?_getD]
    cases hk : t[k]? with
    | none => simpa using h
    | some i => simpa using ht i (List.mem_of_getElem? hk)
  have hmod (k : ℕ) : t.getD k 0 % L'.length = t.getD k 0 := Nat.mod_eq_of_lt (hlt k)
  simp only [TableMono, Pts.le_iff, Pts.ofNat, hmod]
  constructor
  · rintro hm ⟨a, b⟩ hp
    obtain ⟨ha, hb, -, hab⟩ := mem_lePairs.1 hp
    rw [PairOK, Nat.sub_zero, Nat.sub_zero, List.contains_iff_mem, mem_getD_reachTable (hlt _)]
    exact hm ⟨⟨b, hb⟩⟩ ⟨⟨a, ha⟩⟩ hab
  · rintro hm ⟨⟨b, hb⟩⟩ ⟨⟨a, ha⟩⟩ hab
    dsimp only at hab ⊢
    by_cases hba : b = a
    · subst hba; exact .refl
    · have := hm (a, b) (mem_lePairs.2 ⟨ha, hb, hba, hab⟩)
      rwa [PairOK, Nat.sub_zero, Nat.sub_zero, List.contains_iff_mem,
        mem_getD_reachTable (hlt _)] at this

/-- `t` is the table of a morphism `Space L E ⟶ Space L' E'` (see `tableMono_iff`). -/
abbrev IsTable (L : List (List α)) (E : List (ℕ × ℕ)) (L' : List (List β)) (E' : List (ℕ × ℕ))
    (t : List ℕ) : Prop :=
  t.length = L.length ∧ (∀ i ∈ t, i < L'.length) ∧
    ∀ p ∈ lePairs L.length E, PairOK (reachTable L'.length E') 0 t p

/-- All morphisms `Space L E ⟶ Space L' E'`, as `Space.homOfTable t _ _`, in lexicographic order
of their tables `t`. (The tables are written with `List.cons` and numerals, and validity is
checked rather than carried along, so that the elements reduce to `Space.homOfTable [i, j, …] _ _`
for `fin_cases`.) -/
def homList (h : 0 < L'.length) : List (Space.{u} L E ⟶ Space.{u} L' E') :=
  (monoTables L'.length L.length (lePairs L.length E) (reachTable L'.length E') L.length).filterMap
    fun t => if hm : IsTable L E L' E' t then
      some (homOfTable t h ((tableMono_iff hm.2.1).2 hm.2.2)) else none

/-- `Space.homOfTable` at a point. (`simp` evaluates it at points without this, when the table is
a literal list; see `Space.reduceTableApply`.) -/
lemma homOfTable_apply (tbl : List ℕ) (h : 0 < L'.length) (mono) (x : Space.{u} L E) :
    homOfTable (E' := E') tbl h mono x = mk (tbl.getD x.idx 0 % L'.length) (Nat.mod_lt _ h) :=
  rfl

/-- The table of a morphism: the indices of the images of the points. -/
def tableOf (f : Space.{u} L E ⟶ Space.{u} L' E') : List ℕ :=
  List.ofFn fun i : Fin L.length => (f (mk i.val i.isLt)).idx.val

lemma homOfTable_tableOf (h : 0 < L'.length) (f : Space.{u} L E ⟶ Space.{u} L' E')
    (hm : TableMono L E L' E' h (tableOf f)) : homOfTable (tableOf f) h hm = f := by
  ext x -
  rw [homOfTable_apply]
  rcases x with ⟨⟨i, hi⟩⟩
  simp [tableOf, hi, Nat.mod_eq_of_lt (f _).idx.isLt]
  rfl

lemma tableMono_tableOf (h : 0 < L'.length) (f : Space.{u} L E ⟶ Space.{u} L' E') :
    TableMono L E L' E' h (tableOf f) := by
  have hf : Monotone f := Topology.IsUpperSet.monotone_iff_continuous.2 f.hom.continuous
  rintro ⟨⟨i, hi⟩⟩ ⟨⟨j, hj⟩⟩ hij
  have := Pts.le_iff.1 (show (f (mk i hi) : Pts.{u} L' E') ≤ f (mk j hj) from hf hij)
  rw [Pts.le_iff]
  simpa [tableOf, Pts.ofNat, hi, hj, Nat.mod_eq_of_lt (f _).idx.isLt] using this

lemma mem_homList (h : 0 < L'.length) (f : Space.{u} L E ⟶ Space.{u} L' E') :
    f ∈ homList h := by
  have hl : (tableOf f).length = L.length := by simp [tableOf]
  have hb : ∀ i ∈ tableOf f, i < L'.length := by simp [tableOf, (f _).idx.isLt]
  have hm := (tableMono_iff hb).1 (tableMono_tableOf h f)
  rw [homList, List.mem_filterMap]
  refine ⟨tableOf f, mem_monoTables le_rfl hl hb fun p hp _ => by simpa using hm p hp, ?_⟩
  rw [dite_eq_left_of_eq_true (eq_true ⟨hl, hb, hm⟩)]
  simp [homOfTable_tableOf]

lemma nodup_homList (h : 0 < L'.length) : (homList.{u} (L := L) (E := E) (E' := E') h).Nodup := by
  refine (nodup_monoTables _ _ _ _ _).filterMap ?_
  intro t t' f hf hf'
  simp only [Option.mem_def, Option.dite_none_right_eq_some, Option.some.injEq] at hf hf'
  obtain ⟨ht, rfl⟩ := hf; obtain ⟨ht', e⟩ := hf'
  apply List.ext_getElem (ht.1.trans ht'.1.symm)
  intro i hi hi'
  have := congrArg (fun g : Space.{u} L E ⟶ Space.{u} L' E' => (g (mk i (ht.1 ▸ hi))).idx.val) e
  dsimp only at this
  rw [homOfTable_apply, homOfTable_apply] at this
  simp [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
    Nat.mod_eq_of_lt (ht.2.1 _ (List.getElem_mem hi)),
    Nat.mod_eq_of_lt (ht'.2.1 _ (List.getElem_mem hi'))] at this
  exact this.symm

/-- The morphism out of a space without points. -/
def homOfEmpty (hL : L.length = 0) : Space.{u} L E ⟶ Space.{u} L' E' :=
  TopCat.ofHom ⟨fun x => absurd x.idx.isLt (by simp [hL]), by
    rw [continuous_def]; intro s _; convert isOpen_empty
    ext x; exact absurd x.idx.isLt (by simp [hL])⟩

/-- All morphisms `Space L E ⟶ Space L' E'`: as `Space.homOfTable t _ _`, in lexicographic order
of their tables `t` (when `Space L' E'` has points). -/
def homs : List (Space.{u} L E ⟶ Space.{u} L' E') :=
  if h : 0 < L'.length then homList h
  else if hL : L.length = 0 then [homOfEmpty hL] else []

lemma mem_homs (f : Space.{u} L E ⟶ Space.{u} L' E') : f ∈ homs := by
  unfold homs
  split
  · exact mem_homList _ f
  split
  · rename_i hL
    simp only [List.mem_singleton]
    ext x -; exact absurd x.idx.isLt (by simp [hL])
  · rename_i h hL
    exact absurd (f (mk 0 (by omega))).idx.isLt (by omega)

lemma nodup_homs : (homs.{u} (L := L) (E := E) (L' := L') (E' := E')).Nodup := by
  unfold homs
  split
  · exact nodup_homList _
  split <;> simp

/-- The morphisms are enumerated as `Space.homOfTable t _ _`, so that `fin_cases` (and `pt_cases`)
produce them as diagram morphisms (printed as `(⌜…⌟ ⇢ ⌜…⌟)`). -/
instance : Fintype (Space.{u} L E ⟶ Space.{u} L' E') where
  elems := ⟨(homs.{u} : List (Space.{u} L E ⟶ Space.{u} L' E')), Multiset.coe_nodup.2 nodup_homs⟩
  complete f := Multiset.mem_coe.2 (mem_homs f)

instance : FinEnum (Space.{u} L E ⟶ Space.{u} L' E') := .ofNodupList homs mem_homs nodup_homs

/-- The map sending the `i`-th point to the `tbl[i]`-th point, read as for `homOfTable` (indices
are taken modulo `L'.length`, and missing entries default to `0`). Unlike `homOfTable`, it can
change universes. -/
def mapOfTable (tbl : List ℕ) (h : 0 < L'.length) (x : Space.{u} L E) : Space.{v} L' E' :=
  mk (tbl.getD x.idx 0 % L'.length) (Nat.mod_lt _ h)

@[simp, grind =]
lemma mapOfTable_mk (tbl : List ℕ) (h : 0 < L'.length) (k : ℕ) (hk : k < L.length) :
    mapOfTable.{u, v} (E := E) (E' := E') tbl h (mk k hk) =
      mk (tbl.getD k 0 % L'.length) (Nat.mod_lt _ h) :=
  rfl

/-! ### Relabellings -/

/-- An isomorphism between the specialization preorders of `Space L E` and `Space L' E'`, as a
pair of tables of indices `fwd` and `bwd` (read as for `Space.homOfTable`), which are monotone and
mutually inverse. The conditions are stated in `Type`, so that `decide` checks them.

`gav_relabel` finds one. -/
structure Relabelling (L : List (List α)) (E : List (ℕ × ℕ)) (L' : List (List β))
    (E' : List (ℕ × ℕ)) where
  /-- The image of the `i`-th point. -/
  fwd : List ℕ
  /-- The preimage of the `i`-th point. -/
  bwd : List ℕ
  pos : 0 < L.length
  pos' : 0 < L'.length
  mono : ∀ x y : Pts.{0} L E, x ≤ y →
    (Pts.ofNat pos' (fwd.getD x.idx 0) : Pts.{0} L' E') ≤ Pts.ofNat pos' (fwd.getD y.idx 0)
  mono' : ∀ x y : Pts.{0} L' E', x ≤ y →
    (Pts.ofNat pos (bwd.getD x.idx 0) : Pts.{0} L E) ≤ Pts.ofNat pos (bwd.getD y.idx 0)
  left_inv : ∀ x : Pts.{0} L E,
    (Pts.ofNat pos (bwd.getD (fwd.getD x.idx 0 % L'.length) 0) : Pts.{0} L E) = x
  right_inv : ∀ y : Pts.{0} L' E',
    (Pts.ofNat pos' (fwd.getD (bwd.getD y.idx 0 % L.length) 0) : Pts.{0} L' E') = y

/-- The inverse relabelling. -/
def Relabelling.symm (σ : Relabelling L E L' E') : Relabelling L' E' L E :=
  ⟨σ.bwd, σ.fwd, σ.pos', σ.pos, σ.mono', σ.mono, σ.right_inv, σ.left_inv⟩

@[simp, grind =] lemma Relabelling.symm_fwd (σ : Relabelling L E L' E') : σ.symm.fwd = σ.bwd := rfl
@[simp, grind =] lemma Relabelling.symm_bwd (σ : Relabelling L E L' E') : σ.symm.bwd = σ.fwd := rfl

/-- The homeomorphism between two spaces of the same shape, possibly in different universes, e.g.
`(Space.relabelHomeo : ⌜o → c⌟ ≃ₜ ⌜T → F⌟)`. The relabelling is found by `gav_relabel`, which
prefers to keep points with the same names; for a particular one (if the spaces have
automorphisms), use `Space.homeo` instead. -/
def relabelHomeo (σ : Relabelling L E L' E' := by gav_relabel) :
    Space.{u} L E ≃ₜ Space.{v} L' E' where
  toFun := mapOfTable σ.fwd σ.pos'
  invFun := mapOfTable σ.bwd σ.pos
  left_inv x :=
    congrArg (fun p : Pts.{0} L E => (mk p.idx.val p.idx.isLt : Space.{u} L E)) (σ.left_inv ⟨x.idx⟩)
  right_inv y :=
    congrArg (fun p : Pts.{0} L' E' => (mk p.idx.val p.idx.isLt : Space.{v} L' E'))
      (σ.right_inv ⟨y.idx⟩)
  continuous_toFun := Topology.IsUpperSet.monotone_iff_continuous.1 fun x y hxy =>
    σ.mono ⟨x.idx⟩ ⟨y.idx⟩ hxy
  continuous_invFun := Topology.IsUpperSet.monotone_iff_continuous.1 fun x y hxy =>
    σ.mono' ⟨x.idx⟩ ⟨y.idx⟩ hxy

@[simp, grind =] lemma relabelHomeo_apply (σ : Relabelling L E L' E') (x : Space.{u} L E) :
    relabelHomeo.{u, v} σ x = mapOfTable.{u, v} σ.fwd σ.pos' x := rfl

@[simp, grind =]
lemma relabelHomeo_symm_apply (σ : Relabelling L E L' E') (y : Space.{v} L' E') :
    (relabelHomeo.{u, v} σ).symm y = mapOfTable.{v, u} σ.bwd σ.pos y := rfl

/-- The morphism between two spaces of the same shape, e.g. `(Space.relabel : ⌜o → c⌟ ⟶ ⌜T → F⌟)`,
which is an isomorphism (`Space.relabelIso`). This is the analogue of `eqToHom` for spaces that
differ only in the names of their points. The relabelling is found by `gav_relabel`, which prefers
to keep points with the same names; for a particular one (if the spaces have automorphisms), use
`Space.iso` instead.

`simp` evaluates it at points, and normalizes it: `relabel ≫ relabel` becomes `relabel`, and
`relabel` becomes `𝟙` when it is the identity (`Space.reduceRelabel`, `Space.reduceRelabelComp`).
Morphisms between spaces have decidable equality, so other equations between them (such as
naturality squares) can be proved by `decide`. -/
def relabel (σ : Relabelling L E L' E' := by gav_relabel) : Space.{u} L E ⟶ Space.{u} L' E' :=
  homOfTable σ.fwd σ.pos' σ.mono

@[grind =] lemma relabel_apply (σ : Relabelling L E L' E') (x : Space.{u} L E) :
    relabel σ x = mapOfTable.{u, u} σ.fwd σ.pos' x := rfl

/-- `Space.relabel` as an isomorphism. -/
def relabelIso (σ : Relabelling L E L' E' := by gav_relabel) :
    Space.{u} L E ≅ Space.{u} L' E' where
  hom := relabel σ
  inv := relabel σ.symm
  hom_inv_id := hom_ext _ _ fun x _ => (relabelHomeo.{u, u} σ).left_inv x
  inv_hom_id := hom_ext _ _ fun y _ => (relabelHomeo.{u, u} σ).right_inv y

@[simp, grind =] lemma relabelIso_hom (σ : Relabelling L E L' E') :
    (relabelIso.{u} σ).hom = relabel σ := rfl

@[simp, grind =] lemma relabelIso_inv (σ : Relabelling L E L' E') :
    (relabelIso.{u} σ).inv = relabel σ.symm := rfl

instance (σ : Relabelling L E L' E') : IsIso (relabel.{u} σ) := (relabelIso σ).isIso_hom

@[simp, grind =]
lemma inv_relabel (σ : Relabelling L E L' E') : inv (relabel.{u} σ) = relabel σ.symm :=
  IsIso.inv_eq_of_hom_inv_id (relabelIso σ).hom_inv_id

@[simp, grind =] lemma relabel_symm_apply_relabel (σ : Relabelling L E L' E') (x : Space.{u} L E) :
    relabel σ.symm (relabel σ x) = x :=
  (relabelIso σ).hom_inv_id_apply x

@[simp, grind =] lemma relabel_apply_relabel_symm (σ : Relabelling L E L' E')
    (y : Space.{u} L' E') : relabel σ (relabel σ.symm y) = y :=
  (relabelIso σ).inv_hom_id_apply y

/-! ### Applying morphisms given by tables

`simp` normalizes `f (g x)`, where `f` and `g` are relabellings or diagram morphisms, to `h x` with
`h` their composite, as it does `g ≫ f` (see `Space.reduceTableApply`); and likewise for
`mapOfTable` (`Space.reduceMapOfTable`), which `relabelHomeo` evaluates to. These are the lemmas
behind them. -/

lemma apply_eq_of_eq {X Y : TopCat.{u}} {f g : X ⟶ Y} (e : f = g) (x : X) : f x = g x := by
  subst e; rfl

lemma apply_eq_self_of_eq_id {X : TopCat.{u}} {f : X ⟶ X} (e : f = 𝟙 X) (x : X) : f x = x := by
  subst e; rfl

lemma apply_apply_eq_of_comp_eq {X Y Z : TopCat.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    (e : f ≫ g = h) (x : X) : g (f x) = h x := by
  subst e; rfl

lemma apply_apply_eq_self_of_comp_eq_id {X Y : TopCat.{u}} {f : X ⟶ Y} {g : Y ⟶ X}
    (e : f ≫ g = 𝟙 X) (x : X) : g (f x) = x := by
  rw [apply_apply_eq_of_comp_eq e]; rfl

lemma homOfTable_apply_eq_of_forall (tbl : List ℕ) (h : 0 < L'.length)
    (mono : ∀ x y : Pts.{0} L E, x ≤ y →
      (Pts.ofNat h (tbl.getD x.idx 0) : Pts.{0} L' E') ≤ Pts.ofNat h (tbl.getD y.idx 0))
    (k : ℕ) (hk : k < L'.length) (H : ∀ i < L.length, tbl.getD i 0 % L'.length = k)
    (x : Space.{u} L E) : homOfTable tbl h mono x = mk k hk := by
  simp only [homOfTable, TopCat.hom_ofHom, ContinuousMap.coe_mk, H _ x.idx.isLt]

lemma mapOfTable_mapOfTable.{w} {γ : Type} {L'' : List (List γ)} {E'' : List (ℕ × ℕ)}
    (t t' ρ : List ℕ) (h : 0 < L''.length) (h' : 0 < L'.length) (hρ : 0 < L''.length)
    (H : ∀ i < L.length, t.getD (t'.getD i 0 % L'.length) 0 % L''.length =
      ρ.getD i 0 % L''.length) (x : Space.{u} L E) :
    mapOfTable.{v, w} (E := E') (E' := E'') t h (mapOfTable.{u, v} (E' := E') t' h' x) =
      mapOfTable.{u, w} ρ hρ x := by
  simp only [mapOfTable, idx_mk, H _ x.idx.isLt]

lemma mapOfTable_eq_self (t : List ℕ) (h : 0 < L.length)
    (H : ∀ i < L.length, t.getD i 0 % L.length = i) (x : Space.{u} L E) :
    mapOfTable.{u, u} (E' := E) t h x = x := by
  simp only [mapOfTable, H _ x.idx.isLt]; rfl

/-! ### Bijections -/

/-- A relabelling that agrees with a map `f` between the points of two spaces. `gav_relabel_of`
finds it, if `f` is a bijection and it and its inverse are continuous. -/
structure RelabellingOf (f : Space.{u} L E → Space.{v} L' E') extends Relabelling L E L' E' where
  spec : ∀ x, f x = mapOfTable.{u, v} fwd pos' x

/-- The homeomorphism given by a bijection `f` between the points of two spaces (possibly in
different universes), e.g. `Space.homeo fun | pt(o) => pt(F) | pt(c) => pt(T)`. It is
`Space.relabelHomeo` of the relabelling that agrees with `f`, which `gav_relabel_of` computes,
checking that `f` and its inverse are continuous. -/
abbrev homeo (f : Space.{u} L E → Space.{v} L' E') (σ : RelabellingOf f := by gav_relabel_of) :
    Space.{u} L E ≃ₜ Space.{v} L' E' :=
  relabelHomeo σ.toRelabelling

@[grind =]
lemma homeo_apply (f : Space.{u} L E → Space.{v} L' E') (σ : RelabellingOf f) (x : Space.{u} L E) :
    homeo f σ x = f x :=
  (σ.spec x).symm

/-- The isomorphism given by a bijection `f` between the points of two spaces, e.g.
`Space.iso fun | pt(o) => pt(F) | pt(c) => pt(T)`. It is `Space.relabelIso` of the relabelling
that agrees with `f`, which `gav_relabel_of` computes, checking that `f` and its inverse are
continuous. -/
abbrev iso (f : Space.{u} L E → Space.{u} L' E') (σ : RelabellingOf f := by gav_relabel_of) :
    Space.{u} L E ≅ Space.{u} L' E' :=
  relabelIso σ.toRelabelling

@[grind =] lemma iso_hom_apply (f : Space.{u} L E → Space.{u} L' E') (σ : RelabellingOf f)
    (x : Space.{u} L E) : (iso f σ).hom x = f x :=
  (σ.spec x).symm

/-- An isomorphism between two morphisms `f`, `f'` of the same shape, e.g.
`(Space.arrowIso : Arrow.mk (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) ≅ Arrow.mk (⌜T → F⌟ ⇢ ⌜T ↔ F⌟))`, found by
`gav_arrow_iso`. Use it to transport lifting properties, by
`HasLiftingProperty.iff_of_arrow_iso_left` and its variants. Both `f` and `f'` must be known by the
time it is elaborated. -/
abbrev arrowIso {A B A' B' : TopCat.{u}} {f : A ⟶ B} {f' : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk f' := by gav_arrow_iso) : Arrow.mk f ≅ Arrow.mk f' :=
  e

end Space

end Gavrilovich

end

/-! ### Morphisms between models -/

@[expose] public section

universe u

namespace Gavrilovich.Model
open _root_.CategoryTheory

variable {α β : Type} {L : List (List α)} {E : List (ℕ × ℕ)} {L' : List (List β)}
  {E' : List (ℕ × ℕ)}

/-- Morphisms between models, as morphisms between their diagram spaces. -/
def homEquiv (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] [Model X L E]
    [Model Y L' E'] : (TopCat.of X ⟶ TopCat.of Y) ≃ (Space.{u} L E ⟶ Space.{u} L' E') :=
  (iso X).homCongr (iso Y)

instance (priority := low) {X Y : TopCat.{u}} [Model X L E] [Model Y L' E'] :
    DecidableEq (X ⟶ Y) :=
  (homEquiv X Y).decidableEq

instance (priority := low) {X Y : TopCat.{u}} [Model X L E] [Model Y L' E'] :
    Fintype (X ⟶ Y) :=
  .ofEquiv _ (homEquiv X Y).symm

end Gavrilovich.Model

end
