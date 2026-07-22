"""Where does the composition defect come from? (follow-up to analyze_clock.py)

The clock mechanism is: embeddings carry cos(wa), sin(wa) and cos(wb), sin(wb);
the MLP forms products, yielding cos(w(a+b)); the unembed reads that out. In the
2D Fourier basis over (a,b), a perfect clock puts ALL its power on the DIAGONAL
modes k_a = k_b = k (that is exactly what "depends only on a+b" means). Any
power off the diagonal is the product-forming failing.

So we take the 2D DFT of the logit cube over (a,b) for each class c and ask where
the power sits: on-diagonal at the five known frequencies, on-diagonal elsewhere,
or off-diagonal entirely.
"""
import numpy as np
import torch
import torch.nn.functional as F

P = 113
K5 = [14, 35, 41, 42, 52]
data = torch.load('large_files/full_run_data.pth', map_location='cpu', weights_only=False)
sd = data['model']
W_E, W_pos = sd['embed.W_E'], sd['pos_embed.W_pos']
W_K, W_Q = sd['blocks.0.attn.W_K'], sd['blocks.0.attn.W_Q']
W_V, W_O = sd['blocks.0.attn.W_V'], sd['blocks.0.attn.W_O']
W_in, b_in = sd['blocks.0.mlp.W_in'], sd['blocks.0.mlp.b_in']
W_out, b_out = sd['blocks.0.mlp.W_out'], sd['blocks.0.mlp.b_out']
W_U = sd['unembed.W_U']


def forward(tokens):
    """Returns (resid_mid, hidden, resid_post, logits) at the readout position."""
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
    resid_mid = x + torch.einsum('df,bqf->bqd', W_O, z_flat)
    h = F.relu(torch.einsum('md,bpd->bpm', W_in, resid_mid) + b_in)
    resid_post = resid_mid + torch.einsum('dm,bpm->bpd', W_out, h) + b_out
    return (resid_mid[:, -1], h[:, -1], resid_post[:, -1], (resid_post @ W_U)[:, -1])


a = torch.arange(P).repeat_interleave(P)
b = torch.arange(P).repeat(P)
tokens = torch.stack([a, b, torch.full_like(a, P)], dim=1)
with torch.no_grad():
    outs = [forward(tokens[i:i + 1000]) for i in range(0, len(tokens), 1000)]
resid_mid, hidden, resid_post, logits = [
    torch.cat([o[j] for o in outs]).double().numpy().reshape(P, P, -1) for j in range(4)]


def spectrum_report(name, cube):
    """2D DFT over (a,b); report where the power lives."""
    X = cube - cube.mean(axis=(0, 1), keepdims=True)      # drop the (a,b)-constant part
    F2 = np.fft.fft2(X, axes=(0, 1)) / P                  # (ka, kb, feature)
    power = (np.abs(F2) ** 2).sum(axis=2)                 # (ka, kb)
    tot = power.sum()
    ka, kb = np.meshgrid(np.arange(P), np.arange(P), indexing='ij')
    # "depends only on a+b" == power confined to ka == kb
    diag = (ka == kb)
    anti = (ka == (-kb) % P)
    diag5 = diag & np.isin(ka, K5 + [(-k) % P for k in K5])
    print(f"\n{name}  (total power {tot:.4g})")
    print(f"  on-diagonal  k_a =  k_b            : {100 * power[diag].sum() / tot:6.2f}%")
    print(f"    of which at the five frequencies : {100 * power[diag5].sum() / tot:6.2f}%")
    print(f"  anti-diagonal k_a = -k_b (a-b dep) : {100 * power[anti].sum() / tot:6.2f}%")
    off = tot - power[diag].sum() - power[anti].sum() + power[diag & anti].sum()
    print(f"  everything else                    : {100 * off / tot:6.2f}%")
    # strongest off-diagonal modes
    p2 = power.copy()
    p2[diag] = 0
    p2[anti] = 0
    flat = np.argsort(p2.ravel())[::-1][:5]
    tops = [(int(i // P), int(i % P), p2.ravel()[i] / tot * 100) for i in flat]
    print("  top off-diagonal modes (k_a, k_b, % of total):")
    for x, y, pc in tops:
        print(f"      ({x:3d},{y:3d})  {pc:.3f}%")


for nm, cube in [("resid_mid (post-attention)", resid_mid),
                 ("hidden (post-ReLU MLP)", hidden),
                 ("resid_post (pre-unembed)", resid_post),
                 ("logits", logits)]:
    spectrum_report(nm, cube)
