import Cache.Requests

open Cache

def main : List String → IO UInt32
  | ["mk"]   => do discard $ IO.zipCache (← Hashing.getHashes); return 0
  | ["put"]  => Requests.putCache
  | ["put!"] => Requests.putCache!
  | ["get"]  => Requests.getCache
  | ["get!"] => Requests.getCache!
  | ["set"]  => do IO.setCache (← Hashing.getHashes)
  | ["clr"]  => sorry
  | ["clr!"] => sorry
  | _ => sorry
