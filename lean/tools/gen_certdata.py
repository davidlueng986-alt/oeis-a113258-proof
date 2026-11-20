import sys

src, out = sys.argv[1], sys.argv[2]
lines = [l.strip() for l in open(src) if l.strip() and not l.startswith("#")]
assert len(lines) == 1, len(lines)
entries = [e for e in lines[0].split(";") if e.strip()]
rows = []
prev = 0
for e in entries:
    parts = e.split("|")
    h = parts[0].split()
    ell, q1 = int(h[0]), int(h[1])
    assert ell > prev
    prev = ell
    exc = []
    for p in parts[1:]:
        t = list(map(int, p.split()))
        exc.append((t[0], t[1:]))
    rows.append((ell, q1, exc))

def fmt_exc(exc):
    return "[" + ", ".join("(%d, [%s])" % (q, ", ".join(map(str, ns))) for q, ns in exc) + "]"

with open(out, "w") as f:
    f.write("import Mathlib.Data.List.Defs\n\n")
    f.write("/-!\n# Certificate data\n\n")
    f.write("Table `ℓ ↦ (q₁, [(q₂, [n…]), (q₃, [n…])])` for all primes `7 ≤ ℓ ≤ 4500`:\n")
    f.write("`q₁` certifies every `n ∈ [7, ℓ]` not listed in an exception list; each exception\n")
    f.write("`(q, ns)` certifies the `n ∈ ns`. Generated from `certificates/certificates_l_le_4500.txt`.\n-/\n\n")
    f.write("namespace A113258\n\n")
    f.write("def certTable : List (Nat × Nat × List (Nat × List Nat)) := [\n")
    f.write(",\n".join("  (%d, %d, %s)" % (ell, q1, fmt_exc(exc)) for ell, q1, exc in rows))
    f.write("\n]\n\nend A113258\n")
print("entries:", len(rows), "last ell:", rows[-1][0])
