# Axiom Audit

The release audit surface is `lean/CertifiedAffine/Audit.lean`.

Run:

```bash
lake env lean lean/CertifiedAffine/Audit.lean
```

Current guarded declarations:

| Declaration | Axioms reported |
| --- | --- |
| `CertifiedAffine.TseitinCNFData.allFin_map_get` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.edgeAt_allFin_map_eq_edges` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.incidentIndices_length_eq_degree` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.TseitinCycleGF2NormalizationSurface_correctnessInvariant` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.TseitinCycleCNFFormula_length` | `propext`, `Classical.choice`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.TseitinParityFormulaFromEncoding_length` | `propext`, `Quot.sound` |
| `CertifiedAffine.TseitinCNFData.TseitinCycleGF2NormalizationSurface_resourceCounts` | `propext`, `Classical.choice`, `Quot.sound` |

`Lean.ofReduceBool` is not in the guarded theorem path.  Older finite
canonical-extractor smoke tests may still rely on computed witnesses; those are
not the exported clean theorem path.
