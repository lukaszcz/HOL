# TASK29B native bootstrap probe

`receipt.json.gz` rebuilds the sealed Poly/ML 5.9.2 distribution through all
bootstrap stages. `hol-receipt.json.gz` additionally rebuilds HOL through
`upto-parallel` with that compiler, with no copied `.uo` files, heaps or
caches. Both record success at `8b972c274`.

These prove the lineage is reproducible. They are not allocation evidence and
close no gate. `bootstrap_probe.py` is the driver; `run_controls.py
--bootstrap-hol` uses the same steps ahead of the counter controls.
