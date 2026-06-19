/-
Extractor-completeness for SIMPLE graphs with LOW-degree vertices.

SCOPED CERTIFIED EXTRACTION.  This module pushes VERIFIED TRACTABILITY of the
certified GF(2)/Tseitin extractor to graph families that contain low-degree
(directed degree 1 or 2) vertices — paths, trees, cycles-with-pendants, open
chains — which the existing simple-min-degree>2 theorem
(`semanticExtractorCompleteOn_tseitinCNFFormula_of_simple_minDegreeTwo`)
genuinely EXCLUDES.  It does NOT touch the conjecture: the object is still the
affine/XOR (parity) fragment, which is already polynomial.

KEY OBSERVATION.  The proven `native_decide`-free engine
`AtomicClassBridge.semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos`
consumes only:
  * `hfresh`: distinct in-range vertices (in vertex-range order `prior < v`) have
    DISTINCT canonical incident-support keys (a direct freshness condition), and
  * `hdegree`: every in-range vertex has POSITIVE directed degree.
Neither is a `2 < degree` bound.  The existing simple-graph module derives
`hfresh` from `simple + (2 < degree)`; that degree bound is what rules out
paths.  Here we discharge `hfresh` directly from a degree-free structural
hypothesis:

  * INCIDENT-DISTINCTNESS (in-range): for any two DISTINCT IN-RANGE vertices
    `a`, `b`, there is an edge index incident to EXACTLY ONE of them (it lies in
    the symmetric difference of their incident-index sets); i.e. no two in-range
    vertices have identical incident directed-edge-index sets.  For a SIMPLE
    graph this is the faithful "no two vertices share the same incidence"
    condition; crucially it holds for vertices of directed degree 1 or 2 (e.g.
    the two endpoints of a path), which the old `2 < degree` hypothesis cannot
    reach.  Note the symmetric-difference (two-sided) form is necessary: in a
    path the incident set of an endpoint is a PROPER SUBSET of its interior
    neighbour's incident set, so the distinguishing index may live on EITHER
    side.  Restricting to in-range vertices is faithful and necessary: an
    out-of-range vertex has an EMPTY incident list, and the freshness obligation
    is only ever raised for in-range `prior < v < n`.

The genuinely new content is `incidentCanonicalKeys_ne_of_distinctIncident`: if
two vertices have one incident edge index not shared, their canonical incident-
support keys differ — with NO degree bound.  Everything else is plumbing into
the engine.  The concrete NEWLY-COVERED witness is the path `P3` (vertices
0-1-2): its endpoints have directed degree 2, so it fails `2 < degree` and is
NOT covered by `semanticExtractorCompleteOn_tseitinCNFFormula_of_simple_minDegreeTwo`.
-/
import CertifiedAffine.AtomicClassBridge

namespace CertifiedAffine
namespace TseitinCNFData
namespace AtomicClassBridge

open TseitinModel

/--
INCIDENT-DISTINCTNESS hypothesis (IN-RANGE) on a graph encoding: any two DISTINCT
IN-RANGE vertices `a`, `b` differ in their incident directed-edge-index sets,
witnessed by an edge index `i` incident to `a` but NOT to `b`.

Phrased asymmetrically (an index of `a` missing from `b`) because that is exactly
what is needed at a freshness obligation `v ≠ prior`: we exhibit an incident
index of `v` not incident to `prior`.  This is a DEGREE-FREE condition — it holds
for vertices of directed degree 1 or 2 (e.g. the endpoints of a path), unlike the
`2 < degree` hypothesis of the simple-min-degree>2 theorem.  The in-range
restriction is faithful: an out-of-range vertex has an empty incident list, so no
witness index can exist, and the engine only ever raises the obligation for
in-range vertices.
-/
def DistinctIncidentSets
    (G : TseitinModel.Graph) (hme : G.m = G.edges.length) : Prop :=
  forall a b : Nat,
    a < G.n ->
      b < G.n ->
        a ≠ b ->
          exists i : Fin G.m,
            (List.Mem i (incidentIndices G hme a) /\
              TseitinModel.UEdge.incident (edgeAt G hme i) b = false)
            \/
            (List.Mem i (incidentIndices G hme b) /\
              TseitinModel.UEdge.incident (edgeAt G hme i) a = false)

/--
KEY LEMMA (the genuinely new, DEGREE-FREE content).

If vertex `v` has some incident edge index `i` that is NOT incident to vertex
`prior`, then `v` and `prior` have DIFFERENT canonical incident-support keys.

Intuition: the value `i.val` is recorded in `v`'s canonical key (it is the value
of an incident index).  If the canonical keys were equal, `i.val` would also be
in `prior`'s key, and — because edge indices are `Fin G.m`, so equal values mean
equal indices — `i` itself would be incident to `prior`, contradicting that `i`
misses `prior`.  No degree bound is used anywhere.
-/
theorem incidentCanonicalKeys_ne_of_distinctIncident
    (G : TseitinModel.Graph) (hme : G.m = G.edges.length)
    (v prior : Nat)
    (i : Fin G.m)
    (hi : List.Mem i (incidentIndices G hme v))
    (hmiss : TseitinModel.UEdge.incident (edgeAt G hme i) prior = false) :
    Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
      GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)) := by
  intro hkey
  -- `i.val` is in `v`'s canonical key (it is the value of an incident index).
  have hkv :
      List.Mem i.val
        (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v)) :=
    (mem_canonicalSupportKeyForVars_iff (incidentIndices G hme v) i.val).2
      (Exists.intro i (And.intro hi rfl))
  -- Transport to `prior`'s key via the key equality.
  have hkp :
      List.Mem i.val
        (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)) := by
    rw [hkey] at hkv; exact hkv
  -- Read membership back: some index `j` of `prior` has value `i.val`.
  rcases (mem_canonicalSupportKeyForVars_iff
    (incidentIndices G hme prior) i.val).1 hkp with ⟨j, hjmem, hjval⟩
  -- `j.val = i.val` with both `Fin G.m` forces `j = i`.
  have hji : j = i := Fin.ext hjval
  rw [hji] at hjmem
  -- So `i` is incident to `prior`: contradiction with `hmiss`.
  have hinc : TseitinModel.UEdge.incident (edgeAt G hme i) prior = true :=
    incident_of_mem_incidentIndex hjmem
  rw [hinc] at hmiss
  exact Bool.noConfusion hmiss

/--
GENERAL freshness from incident-distinctness (DEGREE-FREE): in a graph whose
distinct in-range vertices have distinct incident-index sets, the canonical
incident-support keys are fresh in vertex-range order.  This is exactly the side
condition consumed by the engine — discharged WITHOUT any `2 < degree`
hypothesis.  Note both `v` and `prior` are in range here (`prior < v < G.n`), so
the in-range restriction of `DistinctIncidentSets` applies.
-/
theorem incidentKeyFresh_of_distinctIncident
    (G : TseitinModel.Graph) (hme : G.m = G.edges.length)
    (hdistinct : DistinctIncidentSets G hme) :
    forall v prior : Nat,
      v < G.n ->
        prior < v ->
          Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
            GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)) := by
  intro v prior hv hprior
  rcases hdistinct v prior hv (by omega) (by omega) with ⟨i, hcase⟩
  rcases hcase with ⟨hi, hmiss⟩ | ⟨hi, hmiss⟩
  · -- distinguishing index incident to `v`, missing `prior`: direct.
    exact incidentCanonicalKeys_ne_of_distinctIncident G hme v prior i hi hmiss
  · -- distinguishing index incident to `prior`, missing `v`: flip the keys.
    intro hkey
    exact incidentCanonicalKeys_ne_of_distinctIncident G hme prior v i hi hmiss
      hkey.symm

/--
PRIVATE-INCIDENT hypothesis (IN-RANGE): every pair of distinct in-range vertices
has an incident directed-edge index on one side that is not incident to the other.
This packages the graph-local "some side has a private incident edge" certificate
used by non-cycle simple-graph families such as paths and trees with distinct
incidence profiles.  The symmetric form is necessary: in a path an endpoint's
incident set may be a proper subset of its neighbor's incident set.
-/
def PrivateIncidentWitnesses
    (G : TseitinModel.Graph) (hme : G.m = G.edges.length) : Prop :=
  forall a b : Nat,
    a < G.n ->
      b < G.n ->
        a ≠ b ->
          exists i : Fin G.m,
            (List.Mem i (incidentIndices G hme a) ∧
              TseitinModel.UEdge.incident (edgeAt G hme i) b = false)
            \/
            (List.Mem i (incidentIndices G hme b) ∧
              TseitinModel.UEdge.incident (edgeAt G hme i) a = false)

/-- A private incident-edge witness immediately gives incident-distinctness. -/
theorem distinctIncidentSets_of_privateIncidentWitnesses
    (G : TseitinModel.Graph) (hme : G.m = G.edges.length)
    (hprivate : PrivateIncidentWitnesses G hme) :
    DistinctIncidentSets G hme := by
  intro a b ha hb hne
  exact hprivate a b ha hb hne

/-- Fresh canonical incident keys from the graph-local private-incident condition. -/
theorem incidentKeyFresh_of_privateIncidentWitnesses
    (G : TseitinModel.Graph) (hme : G.m = G.edges.length)
    (hprivate : PrivateIncidentWitnesses G hme) :
    forall v prior : Nat,
      v < G.n ->
        prior < v ->
          Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
            GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)) := by
  exact incidentKeyFresh_of_distinctIncident G hme
    (distinctIncidentSets_of_privateIncidentWitnesses G hme hprivate)

/--
MAIN THEOREM (LOW-DEGREE COVERAGE).

For any graph encoding `enc` and per-vertex charge, IF distinct in-range vertices
have DISTINCT incident directed-edge-index sets (incident-distinctness) AND every
in-range vertex has POSITIVE directed degree, THEN the semantic + executable
extractor is complete on the Tseitin CNF / parity formulas built from `enc`.

Compared with `semanticExtractorCompleteOn_tseitinCNFFormula_of_simple_minDegreeTwo`,
this DROPS the `2 < degree` hypothesis, replacing it with the degree-free
incident-distinctness condition (plus only positivity of degree, which the engine
genuinely needs so that each vertex contributes a parity block).  It therefore
covers graphs with directed-degree-1 or directed-degree-2 vertices.
-/
theorem semanticExtractorCompleteOn_tseitinCNFFormula_of_distinctIncident_degreePos
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hdistinct :
      DistinctIncidentSets
        (TseitinModel.GraphEncodingData.toGraph enc)
        (TseitinModel.m_eq_edges_length_of_encoding enc))
    (hdeg :
      forall v : Nat,
        v < (TseitinModel.GraphEncodingData.toGraph enc).n ->
          0 < TseitinModel.degree (TseitinModel.GraphEncodingData.toGraph enc) v) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) := by
  refine
    semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos
      enc charge ?_ ?_
  · exact incidentKeyFresh_of_distinctIncident
      (TseitinModel.GraphEncodingData.toGraph enc)
      (TseitinModel.m_eq_edges_length_of_encoding enc) hdistinct
  · intro G' v hv
    exact hdeg v hv

/--
PUBLIC-SURFACE BRIDGE (PRIVATE-INCIDENT FORM).

For any graph encoding, a graph-local private-incident certificate plus positive
in-range degree suffices for certified affine extraction completeness.  This is a
reusable simple-graph/Tseitin extraction lemma beyond cycle-specific wrappers: it
routes a local incidence certificate to the existing public `CertifiedAffine`
semantic extractor surface without search or new axioms.
-/
theorem semanticExtractorCompleteOn_tseitinCNFFormula_of_privateIncident_degreePos
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hprivate :
      PrivateIncidentWitnesses
        (TseitinModel.GraphEncodingData.toGraph enc)
        (TseitinModel.m_eq_edges_length_of_encoding enc))
    (hdeg :
      forall v : Nat,
        v < (TseitinModel.GraphEncodingData.toGraph enc).n ->
          0 < TseitinModel.degree (TseitinModel.GraphEncodingData.toGraph enc) v) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) := by
  exact semanticExtractorCompleteOn_tseitinCNFFormula_of_distinctIncident_degreePos
    enc charge
    (distinctIncidentSets_of_privateIncidentWitnesses
      (TseitinModel.GraphEncodingData.toGraph enc)
      (TseitinModel.m_eq_edges_length_of_encoding enc) hprivate)
    hdeg

/-! ## NEWLY-COVERED witness family: the path `P3` (0 - 1 - 2)

`P3` is the undirected path on three vertices with edges `{0,1}` and `{1,2}`,
encoded in the `TseitinModel` symmetric-pair convention as the four directed
edges `⟨0,1⟩, ⟨1,0⟩, ⟨1,2⟩, ⟨2,1⟩`.  Its endpoints `0` and `2` have directed
degree `2`, so it FAILS the `2 < degree` hypothesis and is NOT an instance of
`semanticExtractorCompleteOn_tseitinCNFFormula_of_simple_minDegreeTwo`. -/

/-- The path `P3` on vertices `0 - 1 - 2`, symmetric-pair encoded. -/
def encoding_path3 : TseitinModel.GraphEncodingData :=
  { n := 3
    edges :=
      [ UEdge.mk 0 1, UEdge.mk 1 0
      , UEdge.mk 1 2, UEdge.mk 2 1 ]
    undirected := by
      intro e he
      simp at he
      rcases he with h | h | h | h <;> simp [h]
    no_self_loops := by
      intro e he
      simp at he
      rcases he with h | h | h | h <;> simp [h]
    endpoints_in_range := by
      intro e he
      simp at he
      rcases he with h | h | h | h <;> simp [h]
    n_le_edges_length := by decide }

/--
NEWLY-COVERED witness, DEGREE side.  In `P3`, the endpoint vertices `0` and `2`
have directed degree exactly `2`.  This is the concrete obstruction that excludes
`P3` from the simple-min-degree>2 theorem (whose hypothesis demands `2 < degree`).
A `native_decide`-free `decide` on this finite encoding.
-/
theorem path3_endpoint_degree_eq_two :
    TseitinModel.degree encoding_path3.toGraph 0 = 2
      ∧ TseitinModel.degree encoding_path3.toGraph 2 = 2 := by
  constructor <;> decide

/--
NEWLY-COVERED witness, POSITIVITY side.  Every in-range vertex of `P3` has
positive directed degree (`0`, `1`, `2` have degree `2`, `4`, `2`), satisfying
the engine's positive-degree obligation.
-/
theorem path3_degree_pos :
    forall v : Nat,
      v < encoding_path3.toGraph.n ->
        0 < TseitinModel.degree encoding_path3.toGraph v := by
  intro v hv
  have hv3 : v = 0 ∨ v = 1 ∨ v = 2 := by
    have hlt : v < 3 := hv
    omega
  rcases hv3 with rfl | rfl | rfl <;> decide

/--
NEWLY-COVERED witness, INCIDENT-DISTINCTNESS side.  `P3` satisfies
`DistinctIncidentSets`: there are finitely many in-range distinct ordered pairs
(`a, b ∈ {0,1,2}`, `a ≠ b`), each discharged by a concrete incident-index witness
via `decide`.  A `native_decide`-free finite check.
-/
theorem path3_distinctIncidentSets :
    DistinctIncidentSets encoding_path3.toGraph
      (TseitinModel.m_eq_edges_length_of_encoding _) := by
  -- `encoding_path3` has `m = 4`.  Edges (indices 0..3): ⟨0,1⟩,⟨1,0⟩,⟨1,2⟩,⟨2,1⟩.
  -- Incident-index sets: vtx0 = {0,1}, vtx1 = {0,1,2,3}, vtx2 = {2,3}.
  -- For each distinct ordered in-range pair we give an explicit distinguishing
  -- index and pick the appropriate side of the symmetric difference; the
  -- resulting conjunction (with a FIXED `i`) is a finite, decidable check.
  intro a b ha hb hab
  have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by
    have : a < 3 := ha
    omega
  have hb3 : b = 0 ∨ b = 1 ∨ b = 2 := by
    have : b < 3 := hb
    omega
  -- Membership in an incident-index list is obtained from the (decidable, Bool)
  -- incidence test via `incidentIndex_mem_of_incident`; the missing-incidence
  -- side is a plain `decide` on the Bool test.
  rcases ha3 with rfl | rfl | rfl <;> rcases hb3 with rfl | rfl | rfl
  · exact absurd rfl hab
  · -- (0,1): vtx1 \ vtx0 ∋ index 2; right disjunct.
    exact ⟨⟨2, by decide⟩, Or.inr ⟨incidentIndex_mem_of_incident (by decide), by decide⟩⟩
  · -- (0,2): vtx0 \ vtx2 ∋ index 0; left disjunct.
    exact ⟨⟨0, by decide⟩, Or.inl ⟨incidentIndex_mem_of_incident (by decide), by decide⟩⟩
  · -- (1,0): vtx1 \ vtx0 ∋ index 2; left disjunct.
    exact ⟨⟨2, by decide⟩, Or.inl ⟨incidentIndex_mem_of_incident (by decide), by decide⟩⟩
  · exact absurd rfl hab
  · -- (1,2): vtx1 \ vtx2 ∋ index 0; left disjunct.
    exact ⟨⟨0, by decide⟩, Or.inl ⟨incidentIndex_mem_of_incident (by decide), by decide⟩⟩
  · -- (2,0): vtx2 \ vtx0 ∋ index 2; left disjunct.
    exact ⟨⟨2, by decide⟩, Or.inl ⟨incidentIndex_mem_of_incident (by decide), by decide⟩⟩
  · -- (2,1): vtx1 \ vtx2 ∋ index 0; right disjunct.
    exact ⟨⟨0, by decide⟩, Or.inr ⟨incidentIndex_mem_of_incident (by decide), by decide⟩⟩
  · exact absurd rfl hab

/-- `P3` also satisfies the named private-incident certificate. -/
theorem path3_privateIncidentWitnesses :
    PrivateIncidentWitnesses encoding_path3.toGraph
      (TseitinModel.m_eq_edges_length_of_encoding _) :=
  path3_distinctIncidentSets

/--
The path `P3` is a concrete instance of the LOW-DEGREE theorem: its Tseitin
extractor is complete.  This witnesses non-vacuity end-to-end for a graph family
NOT covered by the simple-min-degree>2 theorem (its endpoints have directed
degree `2`, see `path3_endpoint_degree_eq_two`).
-/
theorem semanticExtractorCompleteOn_path3
    (charge : Nat -> Bool) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding encoding_path3 charge)
      (TseitinParityFormulaFromEncoding encoding_path3 charge) :=
  semanticExtractorCompleteOn_tseitinCNFFormula_of_distinctIncident_degreePos
    encoding_path3 charge
    path3_distinctIncidentSets
    path3_degree_pos

/-- The same `P3` witness routed through the new private-incident public bridge. -/
theorem semanticExtractorCompleteOn_path3_privateIncident
    (charge : Nat -> Bool) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding encoding_path3 charge)
      (TseitinParityFormulaFromEncoding encoding_path3 charge) :=
  semanticExtractorCompleteOn_tseitinCNFFormula_of_privateIncident_degreePos
    encoding_path3 charge
    path3_privateIncidentWitnesses
    path3_degree_pos

/-! ## Axiom audit -/

-- Expected: [propext, Classical.choice, Quot.sound]; NO sorryAx.
-- `decide` on the finite `P3` witness is kernel reduction, NOT `native_decide`,
-- so NO `Lean.ofReduceBool` is expected either.
#print axioms semanticExtractorCompleteOn_tseitinCNFFormula_of_distinctIncident_degreePos
#print axioms incidentCanonicalKeys_ne_of_distinctIncident
#print axioms incidentKeyFresh_of_distinctIncident
#print axioms semanticExtractorCompleteOn_path3
#print axioms path3_distinctIncidentSets
#print axioms path3_endpoint_degree_eq_two

end AtomicClassBridge
end TseitinCNFData
end CertifiedAffine
