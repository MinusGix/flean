"""Export the grokked mod-113 checkpoint to the trivial FLEANTEN raw format.

Format (all integers little-endian):
  magic   : 8 bytes  b"FLEANTEN"
  version : u32      = 1
  count   : u32      number of tensors
  per tensor:
    nameLen : u32
    name    : nameLen bytes UTF-8
    rows    : u32
    cols    : u32
    data    : rows*cols u32 words = float32 bit patterns, row-major

2-D only. 1-D tensors are stored as 1 x n. The (4, 32, 128) attention tensors
are flattened head-major to (128, 128), matching references/export_weights.py.

Usage: python export_raw_tensors.py  (from references/)
Writes large_files/modadd_weights.fleanten
"""
import struct
import torch

P = 113
data = torch.load('large_files/full_run_data.pth', map_location='cpu', weights_only=False)
sd = data['model']


def as2d(t):
    t = t.detach().float()
    if t.dim() == 1:
        t = t.unsqueeze(0)
    elif t.dim() == 3:  # (heads, d_head, d_model) -> (heads*d_head, d_model)
        t = t.reshape(-1, t.shape[-1])
    assert t.dim() == 2
    return t.contiguous()


TENSORS = [
    ('W_E',   sd['embed.W_E']),
    ('W_pos', sd['pos_embed.W_pos']),
    ('W_K',   sd['blocks.0.attn.W_K']),
    ('W_Q',   sd['blocks.0.attn.W_Q']),
    ('W_V',   sd['blocks.0.attn.W_V']),
    ('W_O',   sd['blocks.0.attn.W_O']),
    ('W_in',  sd['blocks.0.mlp.W_in']),
    ('b_in',  sd['blocks.0.mlp.b_in']),
    ('W_out', sd['blocks.0.mlp.W_out']),
    ('b_out', sd['blocks.0.mlp.b_out']),
    ('W_U',   sd['unembed.W_U']),
]

out = 'large_files/modadd_weights.fleanten'
total = 0
with open(out, 'wb') as f:
    f.write(b'FLEANTEN')
    f.write(struct.pack('<II', 1, len(TENSORS)))
    for name, t in TENSORS:
        m = as2d(t)
        rows, cols = m.shape
        nb = name.encode()
        f.write(struct.pack('<I', len(nb)))
        f.write(nb)
        f.write(struct.pack('<II', rows, cols))
        words = m.view(torch.uint32).numpy().astype('<u4')
        f.write(words.tobytes())
        total += rows * cols
        print(f'{name}: {rows} x {cols}')
print(f'total params: {total}')
print(f'wrote {out}')
