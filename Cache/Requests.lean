namespace Cache

open System

def TOKENPATH : FilePath :=
  ⟨"azure.token"⟩

def getToken : IO String :=
  return (← IO.FS.readFile TOKENPATH).trim

end Cache
