# Convert full certificate lines "ell q n1 n2 ..." into compact form:
#   ell q1 [| q2 n.. [| q3 n..]]   where q1 certifies every n in [7,ell] not listed after a later '|'.
# expand(): inverse map, reproducing the full per-q lists (used to re-run verify_direct).
import sys
from collections import OrderedDict
def compact(lines, nlo=7):
    by=OrderedDict()
    for l in lines:
        t=l.split(); ell=int(t[0]); q=int(t[1]); ns=list(map(int,t[2:]))
        by.setdefault(ell,[]).append((q,ns))
    out=[]
    for ell,qs in by.items():
        q1,ns1=qs[0]
        rest=[(q,ns) for q,ns in qs[1:]]
        covered=set(ns1)
        assert all(n not in covered for q,ns in rest for n in ns)
        assert covered|{n for q,ns in rest for n in ns}==set(range(nlo,ell+1)), ell
        s=f"{ell} {q1}"+"".join(f" | {q} "+" ".join(map(str,ns)) for q,ns in rest)
        out.append(s)
    return out
def expand(clines, nlo=7):
    out=[]
    for l in clines:
        parts=l.split('|'); h=parts[0].split(); ell=int(h[0]); q1=int(h[1])
        rest=[]
        for p in parts[1:]:
            t=list(map(int,p.split())); rest.append((t[0],t[1:]))
        excl={n for q,ns in rest for n in ns}
        out.append(f"{ell} {q1} "+" ".join(str(n) for n in range(nlo,ell+1) if n not in excl))
        for q,ns in rest: out.append(f"{ell} {q} "+" ".join(map(str,ns)))
    return out
if __name__=='__main__':
    mode=sys.argv[1]
    lines=[l.strip() for l in open(sys.argv[2]) if l.strip()]
    res=compact(lines) if mode=='compact' else expand(lines)
    print("\n".join(res))
