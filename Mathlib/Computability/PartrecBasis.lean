/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Data.Set.Subsingleton

/-!
# A simplified basis for partial recursive functions

This file defines `Nat.Partrec'`, an inductive predicate that provides an
alternative, structural basis for partial recursive functions using vectors.
It establishes the equivalence between this vector-based definition and the
standard `Partrec` definition.
-/

@[expose] public section

open List (Vector)
open Encodable Denumerable

namespace Nat

open Vector Part

/-- A simplified basis for `Partrec`.
Note: Since `PFun` is a structure, all underlying partial functions in the constructors
are explicitly wrapped in `PFun.mk` or `PFun.lift`. -/
inductive Partrec' : ∀ {n}, (List.Vector ℕ n →. ℕ) → Prop
  | prim {n f} : @Primrec' n f → @Partrec' n (PFun.lift f)
  | comp {m n f} (g : Fin n → List.Vector ℕ m →. ℕ) :
    Partrec' f → (∀ i, Partrec' (g i)) →
      Partrec' (PFun.mk fun v => (List.Vector.mOfFn fun i => g i v) >>= f)
  | rfind {n} {f : List.Vector ℕ (n + 1) → ℕ} :
    @Partrec' (n + 1) (PFun.lift f) →
      Partrec' (PFun.mk fun v => Nat.rfind (PFun.lift fun n => decide (f (n ::ᵥ v) = 0)))

end Nat

namespace Nat.Partrec'

open List.Vector Partrec Computable Nat.Partrec'

theorem to_part {n f} (pf : @Partrec' n f) : Partrec f := by
  induction pf with
  | prim hf => exact hf.to_prim.to_comp
  | @comp m n' f' g _ _ ihf ihg =>
    exact (Partrec.vector_mOfFn ihg).bind (ihf.comp snd)
  | @rfind n' f' _ ihf =>
    exact _root_.Partrec.rfind <|
       (Primrec.eq.decide.comp _root_.Primrec.id (α := ℕ)
        (_root_.Primrec.const 0)).to_comp.comp (ihf.comp (vector_cons.comp snd fst))

theorem of_eq {n} {f g : List.Vector ℕ n →. ℕ} (hf : Partrec' f) (H : ∀ i, f i = g i) :
    Partrec' g :=
  (DFunLike.ext _ _ H : f = g) ▸ hf

theorem of_prim {n} {f : List.Vector ℕ n → ℕ} (hf : Primrec f) : @Partrec' n (PFun.lift f) :=
  prim (Nat.Primrec'.of_prim hf)

theorem head {n : ℕ} : @Partrec' n.succ (PFun.lift (@head ℕ n)) :=
  prim Nat.Primrec'.head

theorem tail {n f} (hf : @Partrec' n f) : @Partrec' n.succ (PFun.mk fun v => f v.tail) :=
  (hf.comp _ fun i => @prim _ _ <| Nat.Primrec'.get i.succ).of_eq fun v => by
    have h_vec : List.Vector.ofFn (fun i => v.get i.succ) = v.tail := by
      ext i; rw [List.Vector.get_ofFn]; exact (List.Vector.get_tail v i).symm
    ext b; simp [h_vec]

protected theorem bind {n f g} (hf : @Partrec' n f) (hg : @Partrec' (n + 1) g) :
    @Partrec' n (PFun.mk fun v => (f v).bind fun a => g (a ::ᵥ v)) :=
  (@comp n (n + 1) g (Fin.cases f (fun i => PFun.lift fun v => v.get i)) hg <|
    Fin.cases (by simpa using hf) (fun i => by simpa using prim (Nat.Primrec'.get i))).of_eq
    fun v => by ext b; simp [mOfFn, Part.bind_assoc, pure]

protected theorem map {n f} {g : List.Vector ℕ (n + 1) → ℕ} (hf : @Partrec' n f)
    (hg : @Partrec' (n + 1) (PFun.lift g)) :
    @Partrec' n (PFun.mk fun v => (f v).map fun a => g (a ::ᵥ v)) := by
  simpa [(Part.bind_some_eq_map _ _).symm] using hf.bind hg

/-- Predicate for partial recursive vector-valued functions. -/
def Vec {n m} (f : List.Vector ℕ n → List.Vector ℕ m) :=
  ∀ i, Partrec' (PFun.lift fun v => (f v).get i)

nonrec theorem Vec.prim {n m f} (hf : @Nat.Primrec'.Vec n m f) : Vec f := fun i => prim <| hf i

protected theorem nil {n} : @Vec n 0 fun _ => nil := fun i => Fin.elim0 i

protected theorem cons {n m} {f : List.Vector ℕ n → ℕ} {g} (hf : @Partrec' n (PFun.lift f))
    (hg : @Vec n m g) : Vec fun v => f v ::ᵥ g v := fun i =>
  Fin.cases (by simpa using hf) (fun i => by simp only [hg i, get_cons_succ]) i

theorem idv {n} : @Vec n n id :=
  Vec.prim Nat.Primrec'.idv

theorem comp' {n m f g} (hf : @Partrec' m f) (hg : @Vec n m g) :
    Partrec' (PFun.mk fun v => f (g v)) :=
  (hf.comp _ hg).of_eq fun v => by simp [List.Vector.ofFn_get]

theorem comp₁ {n} (f : ℕ →. ℕ) {g : List.Vector ℕ n → ℕ}
    (hf : @Partrec' 1 (PFun.mk fun v => f v.head))
    (hg : @Partrec' n (PFun.lift g)) : @Partrec' n (PFun.mk fun v => f (g v)) := by
  simpa using hf.comp' (Partrec'.cons hg Partrec'.nil)

-- TODO(PFun-refactor): golf this proof once global simp sets for PFun are established
theorem rfindOpt {n} {f : List.Vector ℕ (n + 1) → ℕ} (hf : @Partrec' (n + 1) (PFun.lift f)) :
    @Partrec' n (PFun.mk fun v => Nat.rfindOpt fun a => ofNat (Option ℕ) (f (a ::ᵥ v))) :=
  ((rfind <|
    (of_prim (Primrec.nat_sub.comp (_root_.Primrec.const 1) Primrec.vector_head)).comp₁
          (PFun.lift fun n => 1 - n) hf).bind
    ((prim Nat.Primrec'.pred).comp₁ (PFun.lift Nat.pred) hf)).of_eq
    fun v => by
      ext b
      simp only [PFun.coe_mk, Nat.rfindOpt, Part.mem_bind_iff, PFun.lift_apply, Part.mem_some_iff]
      have h_rfind : (fun n => decide (1 - f (n ::ᵥ v) = 0)) =
          fun n => (ofNat (Option ℕ) (f (n ::ᵥ v))).isSome := by
        funext x
        cases hx : f (x ::ᵥ v) with
        | zero => rfl
        | succ m =>
          have h1 : 1 - (m + 1) = 0 := by omega
          rw [h1]
          rfl
      simp only [h_rfind]
      refine exists_congr fun a => and_congr_right fun h1 => ?_
      cases hfa : f (a ::ᵥ v) with
      | zero =>
        have h_spec := Nat.rfind_spec h1
        simp only [PFun.lift_apply, Part.mem_some_iff, hfa] at h_spec
        have h_false : (ofNat (Option ℕ) 0).isSome = false := rfl
        rw [h_false] at h_spec
        contradiction
      | succ m =>
        have h_ofNat : ofNat (Option ℕ) (m + 1) = Option.some m := rfl
        simp [h_ofNat]
open Nat.Partrec.Code

theorem of_part : ∀ {n f}, Partrec f → @Partrec' n f :=
  @(suffices ∀ f, Nat.Partrec f → @Partrec' 1 (PFun.mk fun v => f v.head) from fun {n f} hf => by
      let g := fun n₁ =>
        (Part.ofOption (decode (α := List.Vector ℕ n) n₁)).bind (fun a => Part.map encode (f a))
      exact
        (comp₁ (PFun.mk g) (this (PFun.mk g) hf) (prim Nat.Primrec'.encode)).of_eq fun i => by
          simp [g, encodek, Part.map_id']
    fun f hf => by
    obtain ⟨c, rfl⟩ := exists_code.1 hf
    simpa [eval_eq_rfindOpt, PFun.coe_mk] using
      rfindOpt <|
        of_prim <|
          Primrec.encode_iff.2 <|
            primrec_evaln.comp <|
              (Primrec.vector_head.pair (_root_.Primrec.const c)).pair <|
                Primrec.vector_head.comp Primrec.vector_tail)

theorem part_iff {n f} : @Partrec' n f ↔ Partrec f :=
  ⟨to_part, of_part⟩

theorem part_iff₁ {f : ℕ →. ℕ} : (@Partrec' 1 (PFun.mk fun v => f v.head)) ↔ Partrec f :=
  part_iff.trans
    ⟨fun h =>
      (h.comp <| (Primrec.vector_ofFn fun _ => _root_.Primrec.id).to_comp).of_eq
        fun v => by simp [head_ofFn],
      fun h => h.comp vector_head⟩

theorem part_iff₂ {f : ℕ → ℕ →. ℕ} :
    (@Partrec' 2 (PFun.mk fun v => f v.head v.tail.head)) ↔ Partrec₂ f :=
  part_iff.trans
    ⟨fun h =>
      (h.comp <| vector_cons.comp fst <| vector_cons.comp snd (const nil)).of_eq
        fun v => by ext b; simp,
      fun h => h.comp vector_head (vector_head.comp vector_tail)⟩

theorem vec_iff {m n f} : @Vec m n f ↔ Computable f :=
  ⟨fun h => by simpa only [ofFn_get] using vector_ofFn fun i => to_part (h i), fun h i =>
    of_part <| vector_get.comp h (const i)⟩

end Nat.Partrec'
