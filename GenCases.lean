import MergeLaws.Merge

/-!
Random three-way merges with the outcome the proven model expects, one JSON object per line.
`diff/run.py` turns each into three real files, merges them with the weave binary and checks
that weave agrees.

Each case has `entities` functions. A function's body is one of a few values, or it is absent;
base, ours and theirs each pick independently, so every kind of entity merge appears
(both changed, one changed, added, deleted, modify against delete, both added differently).
-/

open Weave

/-- A small deterministic generator, so a failing case can be reproduced from its number. -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % (2 ^ 64)

def pick (s : Nat) : Option String :=
  match (s / 65536) % 5 with
  | 0 => none
  | 1 => some "a"
  | 2 => some "b"
  | 3 => some "c"
  | _ => some "d"

def jsonOpt : Option String → String
  | none   => "null"
  | some v => "\"" ++ v ++ "\""

def jsonOutcome : Outcome String → String
  | .clean v        => "{\"clean\":" ++ jsonOpt v ++ "}"
  | .conflict _ _   => "\"conflict\""

def jsonList (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

def main (args : List String) : IO Unit := do
  let cases := (args.head? >>= String.toNat?).getD 2000
  let entities := 5
  let mut s := 42
  for i in [0:cases] do
    let mut base := #[]
    let mut ours := #[]
    let mut theirs := #[]
    for _ in [0:entities] do
      s := lcg s; base := base.push (pick s)
      s := lcg s; ours := ours.push (pick s)
      s := lcg s; theirs := theirs.push (pick s)
    let expect := (List.range entities).map fun k =>
      jsonOutcome (decide base[k]! ours[k]! theirs[k]!)
    IO.println ("{\"case\":" ++ toString i ++
      ",\"base\":" ++ jsonList (base.toList.map jsonOpt) ++
      ",\"ours\":" ++ jsonList (ours.toList.map jsonOpt) ++
      ",\"theirs\":" ++ jsonList (theirs.toList.map jsonOpt) ++
      ",\"expect\":" ++ jsonList expect ++ "}")
