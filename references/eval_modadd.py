"""Extensional evaluation of Nanda's grokked mod-113 addition transformer.

Runs the full forward pass on all p^2 = 12769 input pairs in float32,
reports accuracy and the logit-margin distribution (correct - best wrong),
i.e. exactly the quantities the Lean certificate is about.
"""
import torch
import torch.nn.functional as F
import numpy as np

P = 113
data = torch.load('large_files/full_run_data.pth', map_location='cpu', weights_only=False)
sd = data['model']

W_E = sd['embed.W_E']          # (128, 114)
W_pos = sd['pos_embed.W_pos']  # (3, 128)
W_K = sd['blocks.0.attn.W_K']  # (4, 32, 128)
W_Q = sd['blocks.0.attn.W_Q']
W_V = sd['blocks.0.attn.W_V']
W_O = sd['blocks.0.attn.W_O']  # (128, 128)
W_in = sd['blocks.0.mlp.W_in']   # (512, 128)
b_in = sd['blocks.0.mlp.b_in']
W_out = sd['blocks.0.mlp.W_out'] # (128, 512)
b_out = sd['blocks.0.mlp.b_out']
W_U = sd['unembed.W_U']        # (128, 114)

def forward(tokens):
    # tokens: (B, 3) long
    x = W_E[:, tokens].permute(1, 2, 0)          # (B,3,128)
    x = x + W_pos                                 # broadcast (3,128)
    # attention
    k = torch.einsum('ihd,bpd->biph', W_K, x)
    q = torch.einsum('ihd,bpd->biph', W_Q, x)
    v = torch.einsum('ihd,bpd->biph', W_V, x)
    scores = torch.einsum('biph,biqh->biqp', k, q)
    mask = torch.tril(torch.ones(3, 3))
    scores = torch.tril(scores) - 1e10 * (1 - mask)
    attn = F.softmax(scores / np.sqrt(32), dim=-1)
    z = torch.einsum('biph,biqp->biqh', v, attn)   # (B, i, q, h)
    z_flat = z.permute(0, 2, 1, 3).reshape(tokens.shape[0], 3, 128)
    x = x + torch.einsum('df,bqf->bqd', W_O, z_flat)
    # mlp
    h = F.relu(torch.einsum('md,bpd->bpm', W_in, x) + b_in)
    x = x + torch.einsum('dm,bpm->bpd', W_out, h) + b_out
    return x @ W_U                                # (B,3,114)

a = torch.arange(P).repeat_interleave(P)
b = torch.arange(P).repeat(P)
eq = torch.full_like(a, P)
tokens = torch.stack([a, b, eq], dim=1)  # (12769, 3)

with torch.no_grad():
    logits = torch.cat([forward(tokens[i:i+1000]) for i in range(0, len(tokens), 1000)])
final = logits[:, -1, :]      # (12769, 114)
labels = (a + b) % P

pred_full = final.argmax(dim=-1)
pred_113 = final[:, :P].argmax(dim=-1)
acc_full = (pred_full == labels).float().mean().item()
acc_113 = (pred_113 == labels).float().mean().item()
print(f"accuracy (argmax over all 114): {acc_full:.6f}  errors={int((pred_full!=labels).sum())}")
print(f"accuracy (argmax over 0..112):  {acc_113:.6f}  errors={int((pred_113!=labels).sum())}")

# margin: correct logit - best wrong logit (over 0..112)
correct = final.gather(1, labels[:, None]).squeeze(1)
masked = final[:, :P].clone()
masked.scatter_(1, labels[:, None], -1e30)
best_wrong = masked.max(dim=-1).values
margin = correct - best_wrong
print(f"margin: min={margin.min().item():.4f} mean={margin.mean().item():.4f} max={margin.max().item():.4f}")
print(f"margin quantiles 0.1%/1%/10%: {np.quantile(margin.numpy(), [0.001, 0.01, 0.1])}")
# how big is the '=' (113) logit relative to wrong answers?
print(f"logit[113] beats best_wrong on {int((final[:,113] > best_wrong).sum())} inputs")
# logit scale
print(f"logit magnitude: |correct| mean {correct.abs().mean():.2f}, overall final std {final.std():.2f}")
