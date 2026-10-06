# Summaries of out/g_*.jsonl (see README.md).
import json, glob, sys, collections
files = sorted(glob.glob(sys.argv[1] if len(sys.argv) > 1 else 'out/g_*.jsonl'))
def load(fn): return [json.loads(l) for l in open(fn)]
def tot(d, key): return 1 + sum(e[key] for e in d['edges'])
def wrong(d): return any(e['need'] > e['c2po'] for e in d['edges'])
print(f"{'cell':12} {'n':>5} {'c2 wrong':>9} {'val wrong':>9} | correct: {'ours/c2':>7} {'need/c2':>7} | wrong: {'ours/c2':>7} {'need/c2':>7} {'need/ours':>9}")
ALL = []
for fn in files:
    D = load(fn); ALL += D
    ok = [d for d in D if not wrong(d)]; bad = [d for d in D if wrong(d)]
    r = lambda S, a, b: sum(tot(d, a) for d in S) / max(1, sum(tot(d, b) for d in S))
    vw = sum(1 for d in D if d['c2_val_wrong'] or d['adv_val_wrong'])
    print(f"{fn[6:-6]:12} {len(D):5} {len(bad):9} {vw:9} | {'':9}{r(ok,'ours','c2po'):7.2f} {r(ok,'need','c2po'):7.2f} | {'':7}{r(bad,'ours','c2po'):7.2f} {r(bad,'need','c2po'):7.2f} {r(bad,'need','ours'):9.2f}")
