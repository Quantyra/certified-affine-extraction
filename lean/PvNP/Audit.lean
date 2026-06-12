import PvNP.TseitinCNFData

/-!
# PvNP Audit Surface

This module is intended for publication/release CI.  It guards the current
exported uniform direct-cycle GF(2) theorem path against accidental trust-base
drift.  The older finite canonical-extractor path is still documented as an
internal trust boundary and is not included in this clean audit surface yet.
-/

/-- info: 'PvNP.TseitinCNFData.allFin_map_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.TseitinCNFData.allFin_map_get

/-- info: 'PvNP.TseitinCNFData.edgeAt_allFin_map_eq_edges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.TseitinCNFData.edgeAt_allFin_map_eq_edges

/-- info: 'PvNP.TseitinCNFData.incidentIndices_length_eq_degree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.TseitinCNFData.incidentIndices_length_eq_degree

/-- info: 'PvNP.TseitinCNFData.TseitinCycleGF2NormalizationSurface_correctnessInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.TseitinCNFData.TseitinCycleGF2NormalizationSurface_correctnessInvariant

/-- info: 'PvNP.TseitinCNFData.TseitinCycleCNFFormula_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.TseitinCNFData.TseitinCycleCNFFormula_length

/-- info: 'PvNP.TseitinCNFData.TseitinCycleGF2NormalizationSurface_resourceCounts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.TseitinCNFData.TseitinCycleGF2NormalizationSurface_resourceCounts
