import Cache.Requests

open Cache

def main : List String → IO UInt32
  | ["put"]  => Requests.putCache
  | ["put!"] => Requests.putCache!
  | ["get"]  => Requests.getCache
  | ["get!"] => Requests.getCache!
  | ["set"]  => sorry
  | ["del"]  => sorry
  | ["del!"] => sorry
  | _ => sorry
