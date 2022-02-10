import Lean

def Std.PHashSet.toList [BEq α] [Hashable α] (s : Std.PHashSet α) : List α :=
  s.1.toList.map (·.1)

namespace Lean

open Meta DiscrTree

partial def Meta.DiscrTree.Trie.getElements : Trie α → Array α
  | Trie.node vs children =>
    vs ++ children.concatMap fun (_, child) => child.getElements

def Meta.DiscrTree.getElements (d : DiscrTree α) : Array α :=
  d.1.toList.toArray.concatMap fun (_, child) => child.getElements

instance : ToFormat SimpTheorems where
  format s :=
f!"pre:
{s.pre.getElements.toList}
post:
{s.post.getElements.toList}
lemmaNames:
{s.lemmaNames.toList}
toUnfold: {s.toUnfold.toList}
erased: {s.erased.toList}
toUnfoldThms: {s.toUnfoldThms.toList}"
