import Lean

namespace List

def joinSep (ss : List String) (sep : String) : String :=
  match ss with
  | [] => ""
  | [a] => a
  | a :: as =>
  as.foldl (· ++ sep ++ ·) a

end List

namespace Array

def joinSep (ss : Array String) (sep : String) : String :=
  ss.toList.joinSep sep

end Array
