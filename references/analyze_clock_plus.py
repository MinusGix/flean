"""Does allowing single-token terms absorb the composition defect?

analyze_clock.py fitted L[a,b,c] ~ clock[(a+b-c) mod p] and found a sup-norm
defect of 12.41 -- about 47% of the ideal margin. analyze_defect_origin.py
showed the leftover lives on the OFF-DIAGONAL (k,0)/(0,k) modes, i.e. on terms
depending on a alone or b alone. A clock can never represent those, so adding
frequencies to the clock cannot help (confirmed: K=6 made it marginally worse).

The right question is whether the richer model

    L[a,b,c] ~ clock[(a+b-c)] + u[a,c] + v[b,c]

absorbs it. In the 3D Fourier basis these three families are simply the mode
sets {ka = kb = -kc}, {kb = 0} and {ka = 0}, so the fit is a single mask.
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
L = logits[:, -1, :P].double().numpy().reshape(P, P, P)
L0 = L - L.mean(axis=2, keepdims=True)          # drop c-independent part

s_idx = (np.arange(P)[:, None] + np.arange(P)[None, :]) % P


def certify(name, model):
    """Report defect and both certificates for a fitted model."""
    defect = L0 - model
    eps = np.abs(defect).max()
    idx = s_idx[:, :, None]
    m_correct = np.take_along_axis(model, idx, axis=2)[:, :, 0]
    m_wrong = model.copy()
    np.put_along_axis(m_wrong, idx, -np.inf, axis=2)
    m_margin = m_correct - m_wrong.max(axis=2)          # per-input model margin
    d_input = np.abs(defect).max(axis=2)
    glob = m_margin.min() - 2 * eps
    per = (m_margin - 2 * d_input > 0)
    print(f"\n{name}")
    print(f"  sup defect eps                    : {eps:.6f}")
    print(f"  model margin: min {m_margin.min():.4f}  mean {m_margin.mean():.4f}")
    print(f"  GLOBAL   min_margin - 2*eps       : {glob:+.4f}"
          f"   {'CERTIFIES 100%' if glob > 0 else 'insufficient'}")
    print(f"  PER-INPUT margin > 2*d(a,b)       : {per.sum()}/{P*P} ({100*per.mean():.2f}%)")
    return eps


ka = np.arange(P)[:, None, None]
kb = np.arange(P)[None, :, None]
kc = np.arange(P)[None, None, :]
Fl = np.fft.fftn(L0) / P**3

# model A: clock only  (functions of a+b-c  <=>  ka = kb = -kc)
mask_clock = (ka == kb) & ((ka + kc) % P == 0)
A = np.real(np.fft.ifftn(np.where(mask_clock, Fl, 0) * P**3))
certify("A. clock only  (all frequencies)", A)

# restricted to the five learned frequencies (plus DC)
K5 = [14, 35, 41, 42, 52]
K5pm = set(K5) | {(-k) % P for k in K5} | {0}
mask_k5 = mask_clock & np.isin(ka, list(K5pm))
A5 = np.real(np.fft.ifftn(np.where(mask_k5, Fl, 0) * P**3))
certify("B. clock, five frequencies only", A5)

# model C: clock + single-token terms u[a,c] + v[b,c]
mask_uv = (kb == 0) | (ka == 0)
C = np.real(np.fft.ifftn(np.where(mask_clock | mask_uv, Fl, 0) * P**3))
certify("C. clock + u[a,c] + v[b,c]", C)

# model D: five-frequency clock + single-token terms
D = np.real(np.fft.ifftn(np.where(mask_k5 | mask_uv, Fl, 0) * P**3))
certify("D. five-freq clock + u[a,c] + v[b,c]", D)

# how much power does each family hold?
tot = (np.abs(Fl) ** 2).sum()
for nm, m in [("clock (all freq)", mask_clock), ("clock (5 freq)", mask_k5),
              ("single-token u,v", mask_uv), ("clock+uv", mask_clock | mask_uv),
              ("5freq clock+uv", mask_k5 | mask_uv)]:
    print(f"  power in {nm:22s}: {100 * (np.abs(np.where(m, Fl, 0))**2).sum() / tot:6.2f}%")
