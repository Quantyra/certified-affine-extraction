# Axiom Audit

The release audit surface is `lean/PvNP/Audit.lean`.

Run:

```bash
lake env lean lean/PvNP/Audit.lean
```

Current guarded declarations:

| Declaration | Axioms reported |
| --- | --- |
| `PvNP.TseitinCNFData.allFin_map_get` | `propext`, `Quot.sound` |
| `PvNP.TseitinCNFData.edgeAt_allFin_map_eq_edges` | `propext`, `Quot.sound` |
| `PvNP.TseitinCNFData.incidentIndices_length_eq_degree` | `propext`, `Quot.sound` |
| `PvNP.TseitinCNFData.TseitinCycleGF2NormalizationSurface_correctnessInvariant` | `propext`, `Classical.choice`, `Quot.sound` |
| `PvNP.TseitinCNFData.TseitinCycleCNFFormula_length` | `propext`, `Classical.choice`, `Quot.sound` |
| `PvNP.TseitinCNFData.TseitinCycleGF2NormalizationSurface_resourceCounts` | `propext`, `Classical.choice`, `Quot.sound` |

`Lean.ofReduceBool` is not in the guarded theorem path.  Older finite
canonical-extractor smoke tests may still rely on computed witnesses; those are
not the exported clean theorem path.
