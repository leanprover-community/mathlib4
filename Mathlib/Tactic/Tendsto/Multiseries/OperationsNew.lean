import Mathlib.Tactic.Tendsto.Multiseries.BasicNew

namespace TendstoTactic

namespace PreMS

def neg {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => -ms
  | _ :: _ =>
    ms.map fun (deg, coef) => (deg, coef.neg)


def lol : PreMS [id] where
  val := fun i => .some (i, i)
  property := sorry

def kek := lol.neg

#eval lol.val 123
#eval kek.val 123

noncomputable def add {basis : Basis} (a b : PreMS basis) : PreMS basis :=
  match basis with
  | [] => a + b
  | basid_hd :: basis_tl =>
    let T := (PreMS (basid_hd :: basis_tl)) × (PreMS (basid_hd :: basis_tl))
    let g : T → CoList.OutType (ℝ × PreMS basis_tl) T := fun (x, y) =>
      x.casesOn'
        (nil := .nil)
        (cons := fun (x_deg, x_coef) x_tl =>
          y.casesOn'
          (nil := .nil)
          (cons := fun (y_deg, y_coef) y_tl =>
            if y_deg < x_deg then
              .cons (x_deg, x_coef) (x_tl, y)
            else if x_deg < y_deg then
              .cons (y_deg, y_coef) (x, y_tl)
            else
              .cons (x_deg, x_coef.add y_coef) (x_tl, y_tl)
          )
        )
    CoList.corec g (a, b)


-- def nextAt (n : ℕ) (li : CoList (CoList ℕ)) : CoList (CoList ℕ) :=
--   match n with
--   | 0 => CoList.cons li.head.get!.tail li.tail
--   | m + 1 => CoList.cons li.head.get! (nextAt m li.tail)

/-- Collect leading terms from the list of terms. -/
noncomputable def leadingTerms {basis : Basis} (terms : List (ℝ × PreMS basis)) : Option (ℝ × List (PreMS basis × ℕ)) :=
  match terms with
  | [] => .none
  | (hd_deg, hd_coef) :: tl =>
    .some <| tl.foldlIdx (init := (hd_deg, [(hd_coef, 0)])) fun idx' (maxDeg, ans) (deg, coef) =>
      let idx := idx' + 1 -- we took tail
      if maxDeg < deg then
        (deg, [(coef, idx)])
      else if maxDeg = deg then
        (deg, (coef, idx) :: ans)
      else
        (maxDeg, ans)

-- TODO: rename?
/-- Given CoList of PreMS (which are also CoLists), merge them into single PreMS while maintaining
the correct order. At the step `n` it considers only first `n` elements of `s`. -/
noncomputable def merge1 {basis_hd : ℝ → ℝ} {basis_tl : Basis} (s : CoList (PreMS (basis_hd :: basis_tl))) : PreMS (basis_hd :: basis_tl) :=
  let T := ℕ × CoList (PreMS (basis_hd :: basis_tl))
  let g : T → CoList.OutType (ℝ × PreMS basis_tl) T := fun (k, li) =>
    let heads : List (ℝ × PreMS basis_tl) :=
      let t := li.take k
      t.filterMap (·.head)
    match leadingTerms heads with
    | .none => .nil
    | .some (deg, terms) =>
      let coef := terms.tail.foldl (init := terms.head!.1) fun acc (curCoef, _) =>
        add acc curCoef
      let next : CoList (PreMS (basis_hd :: basis_tl)) := terms.foldl (init := li) fun acc (_, idx) =>
        acc.modify idx (·.tail)
      .cons (deg, coef) (k + 1, next)
  CoList.corec g (1, s)

mutual
  noncomputable def mul {basis : Basis} (a b : PreMS basis) : PreMS basis :=
    match basis with
    | [] => a * b
    | basis_hd :: basis_tl =>
      let ab := a.map fun (deg, coef) => mulMonomial b coef deg
      merge1 ab

  noncomputable def mulMonomial {basis_hd : _} {basis_tl : _} (b : PreMS (basis_hd :: basis_tl))
      (m_coef : PreMS basis_tl) (m_deg : ℝ)
      : PreMS (basis_hd :: basis_tl) :=
    b.map fun (deg, coef) => (m_deg + deg, mul m_coef coef)
end

end PreMS

end TendstoTactic
