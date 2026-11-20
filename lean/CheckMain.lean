import A113258Check.Checker
import A113258Check.CertData

open A113258 in
def main (args : List String) : IO Unit := do
  let k := (args.head?.bind String.toNat?).getD certTable.length
  let t0 ← IO.monoMsNow
  let tbl := certTable.take k
  let ok := tableOK tbl
  let t1 ← IO.monoMsNow
  IO.println s!"entries={tbl.length} tableOK={ok} time={(t1 - t0)}ms"
  if k == certTable.length then
    IO.println s!"coverOK(4463)={coverOK certTable 4463}"
