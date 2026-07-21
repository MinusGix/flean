"""Inspect Nanda's grokking full_run_data.pth: structure, config, final weights."""
import torch

data = torch.load('large_files/full_run_data.pth', map_location='cpu', weights_only=False)
print("top-level type:", type(data))
if isinstance(data, dict):
    for k, v in data.items():
        if isinstance(v, torch.Tensor):
            print(f"  {k}: Tensor {tuple(v.shape)} {v.dtype}")
        elif isinstance(v, list):
            print(f"  {k}: list len={len(v)} elem0type={type(v[0]) if v else None}")
        elif isinstance(v, dict):
            print(f"  {k}: dict keys={list(v.keys())[:20]}")
        else:
            print(f"  {k}: {type(v)} = {v if not hasattr(v,'__len__') or len(str(v))<200 else str(v)[:200]}")
