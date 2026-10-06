# Cross-check with the real r2u2_core: for formulas where our model with C2PO's
# sizes gives a wrong verdict (bin/v4 c2cex), compile with real C2PO
# (--no-rewrite --no-cse, default sizes) and run r2u2_core on the same trace.
# Usage: python3 real.py <jsonl with "pre"> <max formulas> [scq-constant]
import json, sys, subprocess, os, tempfile
C2PO = '/Users/wangzili/Documents/MLTL_R2U2-/r2u2/compiler/c2po.py'
DRV = '/Users/wangzili/Documents/rust-mltl/src/r2u2/benchmarks/build/r2u2_core_driver/target/release/driver'
def tree(toks):
    t = toks.pop(0)
    if t == '!': return f'!({tree(toks)})'
    if t == '&': l = tree(toks); r = tree(toks); return f'(({l}) && ({r}))'
    if t == 'U': a, b = toks.pop(0), toks.pop(0); l = tree(toks); r = tree(toks); return f'(({l}) U[{a},{b}] ({r}))'
    return 's' + t[1:]
tmp = tempfile.mkdtemp()
def real(pre, rows, const):
    na = len(rows[0])
    open(f'{tmp}/m.map', 'w').write(''.join(f's{i}:{i}\n' for i in range(na)))
    open(f'{tmp}/c.c2po', 'w').write(f"INPUT\n    {','.join(f's{i}' for i in range(na))}: bool;\n\nFTSPEC\n    {tree(pre.split())};\n")
    r = subprocess.run(['python3', C2PO, '--impl', 'rust', '--no-rewrite', '--no-cse', '--scq-constant', str(const), '-q',
                        '--map', f'{tmp}/m.map', '-o', f'{tmp}/c.bin', f'{tmp}/c.c2po'], capture_output=True, text=True)
    if r.returncode: return None
    open(f'{tmp}/t.txt', 'w').write(''.join(x + '\n' for x in rows))
    subprocess.run([DRV, f'{tmp}/c.bin', f'{tmp}/t.txt', f'{tmp}/o.txt'], capture_output=True, text=True, check=True)
    return ''.join(open(f'{tmp}/o.txt').read().split())
D = [json.loads(l) for l in open(sys.argv[1])]
const = int(sys.argv[3]) if len(sys.argv) > 3 else 0
n = agree_wrong = real_ok = model_ok = fail = 0; ex = None
for d in D:
    if n >= int(sys.argv[2]): break
    if not any(e['need'] > e['c2po'] for e in d.get('edges', [])): continue
    out = subprocess.run(['./bin/v4', 'c2cex', d['pre'], '20000', '1'], capture_output=True, text=True).stdout.split('\n')
    if out[0] == 'none': model_ok += 1; continue
    rows = out[0].split()[1:]; ref = out[1].split()[1]; c2 = out[2].split()[1]
    rv = real(d['pre'], rows, const)
    if rv is None: fail += 1; continue
    n += 1
    m = min(len(rv), len(ref))
    real_wrong = any(rv[j] != ref[j] for j in range(m))
    model_vs_real = rv[:m] == c2[:m]
    if real_wrong: agree_wrong += 1
    else: real_ok += 1
    if real_wrong and ex is None: ex = (d['f'], ' '.join(rows), ref, rv)
    print(f"{d['f'][:90]:90} real wrong {real_wrong}  real==model(c2po sizes) {model_vs_real}", flush=True)
print(f'tested {n}: real r2u2_core also wrong {agree_wrong}, real right {real_ok}; model found no bad trace {model_ok}; c2po failed {fail}')
if ex: print('example:', ex[0], '\ntrace', ex[1], '\nref ', ex[2], '\nreal', ex[3])
