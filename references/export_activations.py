"""Export precomputed activations of the grokked mod-113 net as FLEANTEN.

Runs the float32 forward pass on all p^2 = 12769 pairs (row index = a*113 + b,
same as eval_modadd.py) and dumps:
  logits : (12769, 114)  final-position logits
  resid  : (12769, 128)  final-position residual stream just before unembed

These are checker INPUTS (data, not proof-data): the Lean checker verifies
properties of them (argmax/margin; later, that logits = resid @ W_U in exact
Binary32) with a parametric soundness theorem.

Usage: python export_activations.py  (from references/)
"""
import struct
import torch
import torch.nn.functional as F
import numpy as np

P = 113
data = torch.load('large_files/full_run_data.pth', map_location='cpu', weights_only=False)
sd = data['model']

W_E = sd['embed.W_E']
W_pos = sd['pos_embed.W_pos']
W_K = sd['blocks.0.attn.W_K']
W_Q = sd['blocks.0.attn.W_Q']
W_V = sd['blocks.0.attn.W_V']
W_O = sd['blocks.0.attn.W_O']
W_in = sd['blocks.0.mlp.W_in']
b_in = sd['blocks.0.mlp.b_in']
W_out = sd['blocks.0.mlp.W_out']
b_out = sd['blocks.0.mlp.b_out']
W_U = sd['unembed.W_U']


def forward_resid(tokens):
    x = W_E[:, tokens].permute(1, 2, 0)
    x = x + W_pos
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
    return x[:, -1, :]  # (B, 128) final-position residual


a = torch.arange(P).repeat_interleave(P)
b = torch.arange(P).repeat(P)
eq = torch.full_like(a, P)
tokens = torch.stack([a, b, eq], dim=1)

with torch.no_grad():
    resid = torch.cat([forward_resid(tokens[i:i + 1000])
                       for i in range(0, len(tokens), 1000)])
    logits = resid @ W_U

labels = (a + b) % P
acc = (logits.argmax(dim=-1) == labels).float().mean().item()
correct = logits[torch.arange(len(labels)), labels]
wrong = logits.clone()
wrong[torch.arange(len(labels)), labels] = -1e30
margin = (correct - wrong.max(dim=-1).values)
print(f'sanity: acc={acc:.6f}, min margin={margin.min().item():.4f}')

TENSORS = [('logits', logits), ('resid', resid)]
out = 'large_files/modadd_activations.fleanten'
with open(out, 'wb') as f:
    f.write(b'FLEANTEN')
    f.write(struct.pack('<II', 1, len(TENSORS)))
    for name, t in TENSORS:
        m = t.detach().float().contiguous()
        rows, cols = m.shape
        nb = name.encode()
        f.write(struct.pack('<I', len(nb)))
        f.write(nb)
        f.write(struct.pack('<II', rows, cols))
        f.write(m.view(torch.uint32).numpy().astype('<u4').tobytes())
        print(f'{name}: {rows} x {cols}')
print(f'wrote {out}')
