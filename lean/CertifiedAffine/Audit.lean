import CertifiedAffine.TseitinCNFData

/-!
# CertifiedAffine Audit Surface

This module is intended for publication/release CI.  It guards the current
exported uniform direct-cycle GF(2) theorem path against accidental trust-base
drift.  The older finite canonical-extractor path is still documented as an
internal trust boundary and is not included in this clean audit surface yet.
-/

/-- info: 'CertifiedAffine.TseitinCNFData.allFin_map_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.allFin_map_get

/-- info: 'CertifiedAffine.TseitinCNFData.edgeAt_allFin_map_eq_edges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.edgeAt_allFin_map_eq_edges

/-- info: 'CertifiedAffine.TseitinCNFData.incidentIndices_length_eq_degree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.incidentIndices_length_eq_degree

/-- info: 'CertifiedAffine.TseitinCNFData.TseitinCycleGF2NormalizationSurface_correctnessInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.TseitinCycleGF2NormalizationSurface_correctnessInvariant

/-- info: 'CertifiedAffine.TseitinCNFData.TseitinCycleCNFFormula_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.TseitinCycleCNFFormula_length

/-- info: 'CertifiedAffine.TseitinCNFData.TseitinParityFormulaFromEncoding_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.TseitinParityFormulaFromEncoding_length

/-- info: 'CertifiedAffine.TseitinCNFData.TseitinCycleGF2NormalizationSurface_resourceCounts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CertifiedAffine.TseitinCNFData.TseitinCycleGF2NormalizationSurface_resourceCounts
