import Mathlib.Tactic.Micromega.Basic
import Std.Data.HashSet

open Std (HashSet)

namespace Micromega

structure Monomial :=
  /--
  Compact representation `#[d, e₀, v₀, ..., eₙ, vₙ]` where
    * `d = Σi v_i` is the multi-degree
    * `e_i` gives the variable number as a diff, i.e. the variable at position `i`
          is `Σi e_i`, and `e_i ≠ 0` for all `i > 0`
    * `v_i` is the degree of `e_i`, must be `≠ 0`
  -/
  data : Array UInt32

namespace Monomial

def const : Monomial := ⟨#[0]⟩
instance : Inhabited Monomial := ⟨const⟩

def isConst : Monomial → Bool
| ⟨#[_]⟩ => true
| _ => false

def isVar (m : Monomial) : Bool := m.data[0]! == 1

def getVar : Monomial → Option UInt32
| ⟨#[1, x, _]⟩ => some x
| _ => none

partial def mul : @& Monomial → @& Monomial → Monomial
| ⟨m₁⟩, ⟨m₂⟩ =>
  let len₁ := m₁.size
  let len₂ := m₂.size
  let rec nvars (acc : Nat) (cur₁ cur₂ : UInt32) (i₁ i₂ : Nat) : Nat :=
    if h₁ : i₁ < len₁ then
      if h₂ : i₂ < len₂ then
        let ncur₁ := cur₁ + m₁[i₁]
        let ncur₂ := cur₂ + m₂[i₂]
        if ncur₁ < ncur₂ then nvars (acc + 2) ncur₁ cur₂ (i₁ + 2) i₂ else
        if ncur₂ < ncur₁ then nvars (acc + 2) cur₁ ncur₂ i₁ (i₂ + 2) else
        nvars (acc + 2) ncur₁ ncur₂ (i₁ + 2) (i₂ + 2)
      else acc + (len₁ - i₁)
    else if i₂ < len₂ then acc + (len₂ - i₂) else acc
  let rec write (cur cur₁ cur₂ : UInt32) (i i₁ i₂ : Nat) (m : Array UInt32) : Monomial :=
    if h₁ : i₁ < len₁ then
      let ncur₁ := cur₁ + m₁[i₁]
      if h₂ : i₂ < len₂ then
        let ncur₂ := cur₂ + m₂[i₂]
        if ncur₁ < ncur₂ then
          write ncur₁ ncur₁ cur₂ (i+2) (i₁+2) i₂ $ m.set! i (ncur₁ - cur) |>.set! (i+1) m₁[i₁+1]!
        else if ncur₂ < ncur₁ then
          write ncur₂ cur₁ ncur₂ (i+2) i₁ (i₂+2) $ m.set! i (ncur₁ - cur) |>.set! (i+1) m₂[i₂+1]!
        else
          write ncur₁ ncur₁ ncur₂ (i+2) (i₁+2) (i₂+2) $
            m.set! i (ncur₁ - cur) |>.set! (i+1) (m₁[i₁+1]! + m₂[i₂+1]!)
      else
        write ncur₁ ncur₁ cur₂ (i+2) (i₁+2) i₂ $ m.set! i (ncur₁ - cur) |>.set! (i+1) m₁[i₁+1]!
    else if h₂ : i₂ < len₂ then
      let ncur₂ := cur₂ + m₂[i₂]
      write ncur₂ cur₁ ncur₂ (i+2) i₁ (i₂+2) $ m.set! i (ncur₂ - cur) |>.set! (i+1) m₂[i₂+1]!
    else ⟨m⟩
  write 0 0 0 1 1 1 $ (Array.mkArray (nvars 1 0 0 1 1) 0).set! 0 (m₁[0]! + m₂[0]!)

instance : Mul Monomial := ⟨mul⟩

/-- `factor m x` returns `none` if `x` does not appear in `m`,
and decreases its exponent by one otherwise -/
partial def factor : @& Monomial → UInt32 → Option Monomial
| ⟨m⟩, x =>
  let len := m.size
  let rec factor cur i :=
    if h : i < len then
      let ncur := cur + m[i]
      let k := m[i+1]!
      if ncur < x then factor ncur (i+2) else
      if x < cur then none else do
      if k == 1 then
        let mut ans := Array.mkEmpty (len - 2)
        ans := ans.push (m[0]! - 1)
        for j in [1:i] do ans := ans.push m[j]!
        for j in [i+2:len] do ans := ans.push m[j]!
        if i + 2 < len then
          ans := ans.set! i (ans[i]! + m[i]!)
        some ⟨ans⟩
      else
        let ans := m.set! 0 (m[0]! - 1)
        some ⟨ans.set! (i+1) (ans[i+1]! - 1)⟩
    else none
  factor 0 1

instance : _root_.Ord Monomial where compare
  | ⟨m₁⟩, ⟨m₂⟩ => Id.run do
    match compare m₁.size m₂.size with
    | Ordering.eq =>
      for i in [0:m₁.size] do
        match compare m₁[i]! m₂[i]! with
        | Ordering.eq => ()
        | c => return c
      Ordering.eq
    | c => c

partial def sqrt : Monomial → Option Monomial
| ⟨#[_]⟩ => some const
| ⟨m⟩ =>
  let rec set i (m : Array UInt32) := do
    if h : i < m.size then
      let v := m.get ⟨i, h⟩
      if v % 2 == 0 then
        set (i+2) $ m.set! (i+1) (v >>> 1)
      else none
    else some ⟨m⟩
  set 1 $ m.set! 0 (m[0]! / 2)

def degree (m : Monomial) : UInt32 := m.data[0]!

partial def fold (f : UInt32 → UInt32 → α → α) (m : Monomial) : α → α :=
  let m := m.data
  let rec fold' (i cur acc) :=
    if h : i < m.size then
      let cur := cur + m.get ⟨i, h⟩
      let acc := f cur m[i+1]! acc
      fold' (i+2) cur acc
    else acc
  fold' 1 0

def variables (m : Monomial) : HashSet UInt32 := fold (fun x _ => (·.insert x)) m ∅
