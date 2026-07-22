"""Representation analysis (#2g): how close are the REAL logits to a Fourier clock?

The extensional checker proves *that* the net computes (a+b) mod 113. This asks
*why*: it decomposes the realized logits into

    L[a,b,c]  =  (junk independent of c)          -- irrelevant to argmax
               + clock[(a+b-c) mod p]             -- the mechanism
               + defect[a,b,c]                    -- what we must bound

and reports, at each stage, the sup-norm of what was thrown away. The decisive
number is whether the clock's own margin exceeds 2*defect: by
`failureSet_subset_smallMargin` in Flean/Operations/ModAddClock.lean that alone
certifies 100% accuracy *through the mechanism*, with no per-input recomputation.
"""
import numpy as np
import torch
import torch.nn.functional as F

P = 113
data = torch.load('large_files/full_run_data.pth', map_location='cpu', weights_only=False)
sd = data['model']
W_E, W_pos = sd['embed.W_E'], sd['pos_embed.W_pos']
W_K, W_Q = sd['blocks.0.attn.W_K'], sd['blocks.0.attn.W_Q']
W_V, W_O = sd['blocks.0.attn.W_V'], sd['blocks.0.attn.W_O']
W_in, b_in = sd['blocks.0.mlp.W_in'], sd['blocks.0.mlp.b_in']
W_out, b_out = sd['blocks.0.mlp.W_out'], sd['blocks.0.mlp.b_out']
W_U = sd['unembed.W_U']


def forward(tokens):
    x = W_E[:, tokens].permute(1, 2, 0) + W_pos
    k = torch.einsum('ihd,bpd->biph', W_K, x)
    q = torch.einsum('ihd,bpd->biph', W_Q, x)
    v = torch.einsum('ihd,bpd->biph', W_V, x)
    scores = torch.einsum('biph,biqh->biqp', k, q)
    mask = torch.tril(torch.ones(3, 3))
    scores = torch.tril(scores) - 1e10 * (1 - mask)
    attn = F.softmax(scores / np.sqrt(32), dim=-1)
    z = torch.einsum('biph,biqp->biqh', v, attn)
    z_flat = z.permute(0, 2, 1, 3).reshape(tokens.shape[0], 3, 128)
    x = x + torch.einsum('df,bqf->bqd', W_O, z_flat)
    h = F.relu(torch.einsum('md,bpd->bpm', W_in, x) + b_in)
    x = x + torch.einsum('dm,bpm->bpd', W_out, h) + b_out
    return x @ W_U


a = torch.arange(P).repeat_interleave(P)
b = torch.arange(P).repeat(P)
tokens = torch.stack([a, b, torch.full_like(a, P)], dim=1)
with torch.no_grad():
    logits = torch.cat([forward(tokens[i:i + 1000]) for i in range(0, len(tokens), 1000)])

# (a, b, c) cube in float64, classes restricted to 0..112
L = logits[:, -1, :P].double().numpy().reshape(P, P, P)


def margin_of(cube):
    """min over inputs of (logit at a+b) - (best wrong logit)."""
    idx = (np.arange(P)[:, None] + np.arange(P)[None, :]) % P
    correct = np.take_along_axis(cube, idx[:, :, None], axis=2)[:, :, 0]
    masked = cube.copy()
    np.put_along_axis(masked, idx[:, :, None], -np.inf, axis=2)
    return (correct - masked.max(axis=2)).min()


print(f"realized fp64 margin (baseline)        : {margin_of(L):+.6f}")

# --- stage 0: drop the part independent of c (cannot affect any argmax) ---
L0 = L - L.mean(axis=2, keepdims=True)
print(f"after removing c-independent part      : {margin_of(L0):+.6f}  (unchanged by construction)")
print(f"  size of removed part (sup)           : {np.abs(L.mean(axis=2)).max():.4f}")

# --- stage 1: does it depend on (a,b) only through s = a+b ? ---
s_idx = (np.arange(P)[:, None] + np.arange(P)[None, :]) % P
M = np.zeros((P, P))
for s in range(P):
    M[s] = L0[s_idx == s].mean(axis=0)
compose_defect = np.abs(L0 - M[s_idx]).max()
print(f"\n[1] composition defect  |L0 - M[a+b]|  : {compose_defect:.6f}")

# --- stage 2: does M[s,c] depend only on t = s - c ? ---
t_idx = (np.arange(P)[:, None] - np.arange(P)[None, :]) % P
g = np.array([M[t_idx == t].mean() for t in range(P)])
shift_defect = np.abs(M - g[t_idx]).max()
print(f"[2] shift defect        |M - g[s-c]|   : {shift_defect:.6f}")

# --- stage 3: how many Fourier modes does g need? ---
G = np.fft.rfft(g) / P
power = np.abs(G) ** 2
order = np.argsort(power[1:])[::-1] + 1        # skip DC
print(f"[3] top frequencies of g (k, |amp|, cumulative power %):")
tot = power[1:].sum()
cum = 0.0
for k in order[:8]:
    cum += power[k]
    print(f"      k={k:3d}  |G_k|={np.abs(G[k]):8.4f}   cum={100 * cum / tot:6.2f}%")

for K in (1, 3, 5, 6, 8):
    keep = set(order[:K])
    Gk = np.array([G[i] if i in keep else 0 for i in range(len(G))])
    gk = np.fft.irfft(Gk * P, n=P)
    approx = gk[(s_idx[:, :, None] - np.arange(P)[None, None, :]) % P]
    eps = np.abs(L0 - approx).max()
    m_clock = gk[0] - np.delete(gk, 0).max()
    print(f"\n  K={K} frequencies {sorted(keep)}")
    print(f"    total defect eps = |L0 - clock|_sup : {eps:.6f}")
    print(f"    clock margin  g(0) - max_{{t!=0}} g(t): {m_clock:.6f}")
    print(f"    certificate  margin - 2*eps         : {m_clock - 2 * eps:+.6f}"
          f"   {'CERTIFIES 100%' if m_clock - 2 * eps > 0 else 'insufficient'}")

# --- stage 4: per-input certificate (the sup-norm bound above is far too lossy) ---
# Correctness at (a,b) needs only: clockMargin > defect[a,b,s] - defect[a,b,c] for
# wrong c, so a per-input bound d(a,b) = max_c |defect[a,b,c]| suffices, and the
# failure set is {(a,b) : clockMargin <= 2 d(a,b)} -- exactly the margin-vs-error
# discipline of ModAddClock.failureSet_subset_smallMargin.
print("\n=== per-input certificate (K=5) ===")
keep = set(order[:5])
Gk = np.array([G[i] if i in keep else 0 for i in range(len(G))])
gk = np.fft.irfft(Gk * P, n=P)
approx = gk[(s_idx[:, :, None] - np.arange(P)[None, None, :]) % P]
defect = L0 - approx
m_clock = gk[0] - np.delete(gk, 0).max()

d_input = np.abs(defect).max(axis=2)                  # (a,b) -> sup over classes
certified = m_clock - 2 * d_input > 0
print(f"clock margin                     : {m_clock:.4f}")
print(f"per-input defect d(a,b): mean {d_input.mean():.4f}  median {np.median(d_input):.4f}"
      f"  p99 {np.quantile(d_input, 0.99):.4f}  max {d_input.max():.4f}")
print(f"certified by 2*d bound           : {certified.sum()}/{P*P}"
      f"  ({100*certified.mean():.2f}%)")

# sharper: the bound only needs correct-vs-wrong differences, not a symmetric sup
idx = s_idx[:, :, None]
d_correct = np.take_along_axis(defect, idx, axis=2)[:, :, 0]
d_wrong = defect.copy()
np.put_along_axis(d_wrong, idx, -np.inf, axis=2)
slack = m_clock + d_correct - d_wrong.max(axis=2)     # exact realized margin lower bound
print(f"sharp bound  m_clock + d_s - max_wrong d: min {slack.min():+.4f}"
      f"  certified {int((slack > 0).sum())}/{P*P} ({100*(slack > 0).mean():.2f}%)")
