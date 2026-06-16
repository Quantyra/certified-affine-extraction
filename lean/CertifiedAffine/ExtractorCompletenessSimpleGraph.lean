/-
General extractor-completeness for simple graphs of bounded directed degree.

This module proves a single GENERAL freshness theorem that discharges the
per-vertex canonical-incident-key freshness side condition required by the
already-proven, `native_decide`-free engine
`AtomicClassBridge.semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos`,
directly from two graph-structural hypotheses:

  * SIMPLICITY: any two DISTINCT vertices share at most TWO incident
    directed-edge indices.  Because the `TseitinModel` encoding represents each
    undirected edge as a symmetric pair of `UEdge`s, "at most one undirected
    edge between a pair of vertices" is exactly "at most two shared incident
    directed-edge indices".  This is the genuine simple-graph hypothesis.

  * DEGREE: every vertex has directed incident degree strictly greater than 2
    (`2 < TseitinModel.degree G v`).  In the symmetric-pair encoding this is the
    faithful rendering of undirected min-degree >= 2 (each undirected neighbor
    contributes two directed indices, so >= 2 distinct neighbors => directed
    degree >= 4 > 2).  NOTE: a naive `directed degree >= 2` is genuinely
    INSUFFICIENT here — `encoding_two_cycle` (the 2-vertex graph with the single
    undirected edge {0,1}) has every vertex of directed degree 2, yet vertices 0
    and 1 have IDENTICAL incident-index sets and freshness FAILS.  `2 < degree`
    is the honest minimal sufficient degree bound.

The new content is `incidentCanonicalKeys_ne_of_simple_degree`: in a simple
graph, two distinct vertices of directed degree > 2 have different canonical
incident-support keys.  Everything else is plumbing into the engine.
-/
import CertifiedAffine.AtomicClassBridge

namespace CertifiedAffine
namespace TseitinCNFData
namespace AtomicClassBridge

open TseitinModel

/--
SIMPLE-GRAPH hypothesis on a graph encoding: any two DISTINCT vertices `a`, `b`
share at most two incident directed-edge indices.

In the `TseitinModel` symmetric-pair encoding an undirected edge `{a,b}` is the
two directed edges `⟨a,b⟩`, `⟨b,a⟩`, so "at most two shared incident indices" is
exactly "at most one undirected edge between `a` and `b`": the standard
simple-graph (no multi-edge) condition phrased over the actual encoding API.
-/
def SimpleSharedIncidence
    (G : TseitinModel.Graph) (hme : G.m = G.edges.length) : Prop :=
  forall a b : Nat,
    a ≠ b ->
      ((incidentIndices G hme a).filter
        (fun i => TseitinModel.UEdge.incident (edgeAt G hme i) b)).length ≤ 2

/--
The list of edge indices incident to a vertex `v` is duplicate-free: it is a
`filter` of the duplicate-free finite-index enumeration `allFin`.
-/
theorem incidentIndices_nodup
    (G : TseitinModel.Graph) (hme : G.m = G.edges.length) (v : Nat) :
    (incidentIndices G hme v).Nodup := by
  unfold incidentIndices
  exact (allFin_nodup G.m).filter _

/--
KEY LEMMA (the genuinely new content).

In a SIMPLE graph (`SimpleSharedIncidence`), two DISTINCT vertices whose directed
incident degree exceeds `2` have DIFFERENT canonical incident-support keys.

Intuition: if the canonical keys were equal, then — because the canonical key
records exactly the value-set of the incident-index list and edge indices are
`Fin G.m` (so distinct values mean distinct indices) — vertex `v` and vertex
`prior` would have the SAME set of incident edge indices.  Every incident index
of `v` would then also be incident to `prior`, i.e. shared between the two
vertices.  Simplicity caps the number of shared incident indices at `2`, forcing
`degree v ≤ 2`, contradicting `2 < degree v`.
-/
theorem incidentCanonicalKeys_ne_of_simple_degree
    (G : TseitinModel.Graph) (hme : G.m = G.edges.length)
    (hsimple : SimpleSharedIncidence G hme)
    (v prior : Nat) (hne : v ≠ prior)
    (hdeg : 2 < TseitinModel.degree G v) :
    Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
      GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)) := by
  intro hkey
  -- From key-equality, every incident index of `v` is also incident to `prior`.
  have hmem_iff :
      forall i : Fin G.m,
        List.Mem i (incidentIndices G hme v) ->
          List.Mem i (incidentIndices G hme prior) := by
    intro i hi
    -- `i.val` is in `v`'s canonical key (it is the value of an incident index).
    have hkv :
        List.Mem i.val
          (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v)) :=
      (mem_canonicalSupportKeyForVars_iff (incidentIndices G hme v) i.val).2
        (Exists.intro i (And.intro hi rfl))
    -- Transport to `prior`'s key via the key equality, then read membership back.
    have hkp :
        List.Mem i.val
          (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)) := by
      rw [hkey] at hkv; exact hkv
    rcases (mem_canonicalSupportKeyForVars_iff
      (incidentIndices G hme prior) i.val).1 hkp with ⟨j, hjmem, hjval⟩
    -- `j.val = i.val` with both `Fin G.m` forces `j = i`.
    have hji : j = i := Fin.ext hjval
    rw [hji] at hjmem
    exact hjmem
  -- Hence `v`'s incident-index list equals its `prior`-incident sublist.
  have hfilter_eq :
      (incidentIndices G hme v).filter
        (fun i => TseitinModel.UEdge.incident (edgeAt G hme i) prior)
        = incidentIndices G hme v := by
    apply List.filter_eq_self.2
    intro i hi
    -- `i` incident to `prior`: it lies in `incidentIndices prior`.
    exact incident_of_mem_incidentIndex (hmem_iff i hi)
  -- So `degree v = length (incidentIndices v) = length (shared list) ≤ 2`.
  have hlen :
      TseitinModel.degree G v
        = ((incidentIndices G hme v).filter
            (fun i => TseitinModel.UEdge.incident (edgeAt G hme i) prior)).length := by
    rw [hfilter_eq]
    exact (incidentIndices_length_eq_degree G hme v).symm
  have hle :
      ((incidentIndices G hme v).filter
        (fun i => TseitinModel.UEdge.incident (edgeAt G hme i) prior)).length ≤ 2 :=
    hsimple v prior hne
  omega

/--
GENERAL freshness: in a simple graph of directed min-degree `> 2`, the canonical
incident-support keys are fresh in vertex-range order, the exact side condition
consumed by the engine theorems.
-/
theorem incidentKeyFresh_of_simple_minDegree
    (G : TseitinModel.Graph) (hme : G.m = G.edges.length)
    (hsimple : SimpleSharedIncidence G hme)
    (hdeg : forall v : Nat, v < G.n -> 2 < TseitinModel.degree G v) :
    forall v prior : Nat,
      v < G.n ->
        prior < v ->
          Not (GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme v) =
            GroupFrame.canonicalSupportKeyForVars (incidentIndices G hme prior)) := by
  intro v prior hv hprior
  exact incidentCanonicalKeys_ne_of_simple_degree G hme hsimple v prior
    (by omega) (hdeg v hv)

/--
MAIN THEOREM.

For any graph encoding `enc` and per-vertex charge, IF the graph is SIMPLE
(any two distinct vertices share at most two incident directed-edge indices —
i.e. at most one undirected edge) AND every vertex has directed incident degree
strictly greater than `2`, THEN the semantic + executable extractor is complete
on the Tseitin CNF / parity formulas built from `enc`.

This discharges the bespoke per-family freshness obligation for a broad class of
simple graphs (cycle, circulant, theta, figure-eight, chorded cycle, ...) with a
single structural hypothesis, routed through the proven `native_decide`-free
engine.
-/
theorem semanticExtractorCompleteOn_tseitinCNFFormula_of_simple_minDegreeTwo
    (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool)
    (hsimple :
      SimpleSharedIncidence
        (TseitinModel.GraphEncodingData.toGraph enc)
        (TseitinModel.m_eq_edges_length_of_encoding enc))
    (hdeg :
      forall v : Nat,
        v < (TseitinModel.GraphEncodingData.toGraph enc).n ->
          2 < TseitinModel.degree (TseitinModel.GraphEncodingData.toGraph enc) v) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding enc charge)
      (TseitinParityFormulaFromEncoding enc charge) := by
  refine
    semanticExtractorCompleteOn_tseitinCNFFormulaFromEncoding_of_incidentKeyFresh_degree_pos
      enc charge ?_ ?_
  · -- freshness from simplicity + degree
    exact incidentKeyFresh_of_simple_minDegree
      (TseitinModel.GraphEncodingData.toGraph enc)
      (TseitinModel.m_eq_edges_length_of_encoding enc) hsimple hdeg
  · -- positive degree from `2 < degree` (strip the `let G := …` binder first)
    intro G' v hv
    exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) (Nat.le_of_lt (hdeg v hv))

/-! ## Out-of-range incidence is empty -/

/--
A vertex index at least as large as the vertex bound `G.n` has no incident edge
indices: every edge endpoint is `< G.n`, so no edge is incident to it.
-/
theorem incidentIndices_eq_nil_of_ge
    (G : TseitinModel.Graph) (hme : G.m = G.edges.length)
    (a : Nat) (ha : G.n ≤ a) :
    incidentIndices G hme a = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro i hi
  have hinc : TseitinModel.UEdge.incident (edgeAt G hme i) a = true :=
    incident_of_mem_incidentIndex hi
  have hmem : edgeAt G hme i ∈ G.edges := by
    unfold edgeAt
    exact List.get_mem _ _ _
  have hrange := G.endpoints_in_range _ hmem
  unfold TseitinModel.UEdge.incident at hinc
  have : (edgeAt G hme i).u = a ∨ (edgeAt G hme i).v = a := by
    simpa using hinc
  omega

/-! ## Non-vacuity witness: the triangle (3-cycle) -/

/--
NON-VACUITY WITNESS (degree side).  Every triangle vertex has directed incident
degree `4 > 2`, so the degree hypothesis of the main theorem is satisfiable.
-/
theorem triangle_degree_gt_two :
    forall v : Nat,
      v < (TseitinModel.encoding_cycle_derived 3 (by decide)).toGraph.n ->
        2 < TseitinModel.degree
          (TseitinModel.encoding_cycle_derived 3 (by decide)).toGraph v := by
  intro v hv
  rw [TseitinModel.cycle_degree_eq_four 3 v (by decide) hv]
  decide

/--
NON-VACUITY WITNESS (simplicity side).  The triangle satisfies
`SimpleSharedIncidence`: out-of-range vertices contribute the empty incident
list, and each of the finitely many in-range vertex pairs is checked by
evaluation.  Together with `triangle_degree_gt_two` this shows the hypotheses of
`semanticExtractorCompleteOn_tseitinCNFFormula_of_simple_minDegreeTwo` are
jointly inhabited, hence the main theorem is non-vacuous.
-/
theorem triangle_simpleSharedIncidence :
    SimpleSharedIncidence
      (TseitinModel.encoding_cycle_derived 3 (by decide)).toGraph
      (TseitinModel.m_eq_edges_length_of_encoding _) := by
  intro a b hab
  by_cases ha : 3 ≤ a
  · -- out-of-range source vertex: empty incident list.
    rw [incidentIndices_eq_nil_of_ge _ _ a ha]
    simp
  · push_neg at ha
    by_cases hb : 3 ≤ b
    · -- out-of-range target vertex: every both-incident index would lie in the
      -- empty incident list of `b`, so the filtered list is empty.
      have hbnil :
          incidentIndices (TseitinModel.encoding_cycle_derived 3 (by decide)).toGraph
            (TseitinModel.m_eq_edges_length_of_encoding _) b = [] :=
        incidentIndices_eq_nil_of_ge _ _ b hb
      have hfilt :
          (incidentIndices
              (TseitinModel.encoding_cycle_derived 3 (by decide)).toGraph
              (TseitinModel.m_eq_edges_length_of_encoding _) a).filter
            (fun i => TseitinModel.UEdge.incident
              (edgeAt _ (TseitinModel.m_eq_edges_length_of_encoding _) i) b) = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro i hi
        have hi' := List.mem_filter.1 hi
        have hinc :
            TseitinModel.UEdge.incident
              (edgeAt _ (TseitinModel.m_eq_edges_length_of_encoding _) i) b = true := by
          simpa using hi'.2
        have hib : List.Mem i
            (incidentIndices (TseitinModel.encoding_cycle_derived 3 (by decide)).toGraph
              (TseitinModel.m_eq_edges_length_of_encoding _) b) :=
          incidentIndex_mem_of_incident hinc
        rw [hbnil] at hib
        exact (List.not_mem_nil i) hib
      rw [hfilt]; decide
    · push_neg at hb
      -- both vertices in range (a, b < 3): a finite, decidable check.
      have ha2 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
      have hb2 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
      rcases ha2 with rfl | rfl | rfl <;>
        rcases hb2 with rfl | rfl | rfl <;>
          first
            | (exact absurd rfl hab)
            | decide

/--
The triangle (3-cycle) is a concrete instance of the general theorem: its Tseitin
extractor is complete.  This witnesses non-vacuity end-to-end.
-/
theorem semanticExtractorCompleteOn_triangle
    (charge : Nat -> Bool) :
    ExtractorCompleteness.SemanticExtractorCompleteOn
      (TseitinCNFFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived 3 (by decide)) charge)
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived 3 (by decide)) charge) :=
  semanticExtractorCompleteOn_tseitinCNFFormula_of_simple_minDegreeTwo
    (TseitinModel.encoding_cycle_derived 3 (by decide)) charge
    triangle_simpleSharedIncidence
    triangle_degree_gt_two

/-! ## Axiom audit -/

-- Expected: [propext, Classical.choice, Quot.sound]; NO sorryAx, NO Lean.ofReduceBool.
#print axioms semanticExtractorCompleteOn_tseitinCNFFormula_of_simple_minDegreeTwo
#print axioms incidentCanonicalKeys_ne_of_simple_degree
#print axioms semanticExtractorCompleteOn_triangle
#print axioms triangle_simpleSharedIncidence

end AtomicClassBridge
end TseitinCNFData
end CertifiedAffine
