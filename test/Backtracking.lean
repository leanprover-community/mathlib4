import Lean
import Mathlib.Tactic.Backtracking
open Lean Mathlib.Tactic BacktrackOptimize

abbrev M (α : Type) := StateT (List (Nat × Nat × Nat)) MetaM α

instance : MonadBacktrack (List (Nat × Nat × Nat)) M where
  saveState := get
  restoreState := set

instance : MonadStateOf (List (Nat × Nat × Nat)) M where
  get := get
  set := set
  modifyGet := modifyGet

inductive A (α : Type) : Type where
| node : α → List (List (A α)) → A α
| leaf : α → A α
deriving Repr

def getData : A α → α
| .node a _ => a
| .leaf a => a

instance : ToMessageData (A (Nat × Nat × Nat)) where
  toMessageData a := Repr.reprPrec a 0

def alternatives (a : A (Nat × Nat × Nat)) : M (List (M (List (A (Nat × Nat × Nat))))) := do
  match a with
  | .node a as => do let s ← get; set (a :: s); pure <| as.map pure
  | .leaf _ => failure

def init : List (A (Nat × Nat × Nat)):= [
  .leaf (0,0,1),
  .leaf (0,0,2),
  .node (0,0,3) [
    [
      .node (1,0,0) [
        [
          .node (2,0,0) [
            [
              .leaf (3,0,0),
              .leaf (3,0,1)
            ],
            [
              .leaf (3,1,0) -- part of 1st min
            ],
            [
              .leaf (3,2,0),
              .leaf (3,2,1)
            ]
          ],
          .node (2,0,1) [
            [
              .leaf (3,0,0) -- part of 1st min
            ]
          ]
        ],
        [
          .leaf (2,1,0), -- part of 2nd min, = the 1st, discarded
          .node (2,1,1) [
            [
              .leaf (3,0,0) -- part of 2nd min, = the 1st, discarded
            ]
          ]
        ]
      ]
    ],
    [ -- Not a min
      .leaf (1,1,0),
      .leaf (1,1,1),
      .leaf (1,1,2),
      .leaf (1,1,3)
    ]
  ]
]

def minimizeTestConfig : MinimizeItemsConfig M (A (Nat × Nat × Nat)) where
  fromAltsFailure := fun a _ => do
    let s ← get; set ((getData a) :: s)
    pure a

def M.run (x : M α) := StateT.run x

-- set_option trace.Backtrack.Minimize true
-- No point in actually running this with every build, since we can't test against `#eval` outputs.
-- Expected output:
-- ([A.leaf (3, 0, 0), A.leaf (3, 1, 0), A.leaf (0, 0, 2), A.leaf (0, 0, 1)],
--   [(3, 0, 0), (2, 0, 1), (3, 1, 0), (2, 0, 0), (1, 0, 0), (0, 0, 3), (0, 0, 2), (0, 0, 1)])
-- #eval M.run (minimizeItems init alternatives minimizeTestConfig) []

def testCurrent : List (A (Nat × Nat × Nat)):= [
  .leaf (0,0,0),
  .leaf (0,0,1),
  .leaf (0,0,2),
  .node (0,0,3) [
    [
      .leaf (1,0,0)
    ],
    [
      .leaf (1,1,0)
    ]
  ]
]

-- set_option trace.Backtrack.Minimize true
-- Expected output:
-- ([A.leaf (1, 0, 0), A.leaf (0, 0, 2), A.leaf (0, 0, 1), A.leaf (0, 0, 0)],
--   [(1, 0, 0), (0, 0, 3), (0, 0, 2), (0, 0, 1), (0, 0, 0)])
-- #eval M.run (minimizeItems testCurrent alternatives minimizeTestConfig) []
