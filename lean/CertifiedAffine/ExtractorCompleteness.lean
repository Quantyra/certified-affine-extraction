import Mathlib.Data.List.Permutation
import CertifiedAffine.ParityEncoded

/-!
# Canonical Extractor Completeness Scaffold

This module isolates the function-level part of the canonical splitter.  The
semantic `ParityEncoded.Class.sound` theorem is already structural; the hard
next obligation is to show that the executable extractor returns the expected
blocks.  The lemmas here reduce that obligation to two explicit facts:

* the CNF groups into canonical support components, and
* each component is recognized as a canonical parity block.
-/

namespace CertifiedAffine
namespace TseitinCNFData

namespace ExtractorCompleteness

/-- Ordinary CNF covered by a list of canonical support groups. -/
def canonicalSupportClauseGroupsCNF {m : Nat}
    (groups : List (CanonicalSupportClauseGroup m)) :
    CNFModel.CNF m :=
  groups.bind Prod.snd

/--
The canonical support groups recognized by the current splitter, paired with
the block list expected from `splitCanonicalSupportClauseGroups`.
-/
def GroupsRecognized {m : Nat} :
    List (CanonicalSupportClauseGroup m) ->
      List (CanonicalFingerprintRecognizedParityBlock m) -> Prop
  | [], [] => True
  | g :: groups, b :: blocks =>
      inferCanonicalParityBlock g.2 = some b /\
        GroupsRecognized groups blocks
  | _, _ => False

/-- A block inferred with a fixed charge covers exactly the input block CNF. -/
theorem blockCNF_eq_of_inferCanonicalParityBlockWithCharge
    {m : Nat} {f : CNFModel.CNF m} {charge : Bool}
    {b : CanonicalFingerprintRecognizedParityBlock m}
    (h : inferCanonicalParityBlockWithCharge f charge = some b) :
    b.blockCNF = f := by
  unfold inferCanonicalParityBlockWithCharge at h
  by_cases hsignal :
      canonicalParityBlockRecognitionSignal f
        (inferredCanonicalParityBlockSpec f charge) = true
  case pos =>
      simp [hsignal] at h
      cases h
      rfl
  case neg =>
      simp [hsignal] at h

/-- A block inferred by the two-charge recognizer covers exactly the input block CNF. -/
theorem blockCNF_eq_of_inferCanonicalParityBlock
    {m : Nat} {f : CNFModel.CNF m}
    {b : CanonicalFingerprintRecognizedParityBlock m}
    (h : inferCanonicalParityBlock f = some b) :
    b.blockCNF = f := by
  unfold inferCanonicalParityBlock at h
  cases hfalse :
      inferCanonicalParityBlockWithCharge f false with
  | some bfalse =>
      simp [hfalse] at h
      cases h
      exact blockCNF_eq_of_inferCanonicalParityBlockWithCharge hfalse
  | none =>
      simp [hfalse] at h
      exact blockCNF_eq_of_inferCanonicalParityBlockWithCharge h

/--
Splitting support groups preserves the ordinary clauses, moving recognized
groups into the core and unrecognized groups into residual CNF.
-/
theorem splitCanonicalSupportClauseGroups_expandedCNF_perm
    {m : Nat}
    (groups : List (CanonicalSupportClauseGroup m)) :
    List.Perm
      (splitCanonicalSupportClauseGroups groups).expandedCNF
      (canonicalSupportClauseGroupsCNF groups) := by
  induction groups with
  | nil =>
      simp [splitCanonicalSupportClauseGroups,
        CanonicalFingerprintGF2Decomposition.expandedCNF,
        CanonicalFingerprintGF2Decomposition.coreCNF,
        canonicalFingerprintRecognizedBlocksCNF,
        canonicalSupportClauseGroupsCNF]
  | cons g groups ih =>
      unfold splitCanonicalSupportClauseGroups
      cases hinfer : inferCanonicalParityBlock g.2 with
      | some b =>
          have hb : b.blockCNF = g.2 :=
            blockCNF_eq_of_inferCanonicalParityBlock hinfer
          simp [hinfer, CanonicalFingerprintGF2Decomposition.expandedCNF,
            CanonicalFingerprintGF2Decomposition.coreCNF,
            canonicalFingerprintRecognizedBlocksCNF,
            canonicalSupportClauseGroupsCNF, hb]
          exact List.Perm.append_left g.2 ih
      | none =>
          simp [hinfer, CanonicalFingerprintGF2Decomposition.expandedCNF,
            CanonicalFingerprintGF2Decomposition.coreCNF,
            canonicalFingerprintRecognizedBlocksCNF,
            canonicalSupportClauseGroupsCNF]
          have htail :
              List.Perm
                (((splitCanonicalSupportClauseGroups groups).blocks.bind
                  fun b => b.blockCNF) ++
                    (splitCanonicalSupportClauseGroups groups).residualCNF)
                (groups.bind Prod.snd) := by
            simpa [CanonicalFingerprintGF2Decomposition.expandedCNF,
              CanonicalFingerprintGF2Decomposition.coreCNF,
              canonicalFingerprintRecognizedBlocksCNF,
              canonicalSupportClauseGroupsCNF] using ih
          have hswap :
              List.Perm
                (((splitCanonicalSupportClauseGroups groups).blocks.bind
                  fun b => b.blockCNF) ++
                    (g.2 ++
                      (splitCanonicalSupportClauseGroups groups).residualCNF))
                (g.2 ++
                  (((splitCanonicalSupportClauseGroups groups).blocks.bind
                    fun b => b.blockCNF) ++
                      (splitCanonicalSupportClauseGroups groups).residualCNF)) := by
            simpa [List.append_assoc] using
              List.Perm.append_right
                (splitCanonicalSupportClauseGroups groups).residualCNF
                (List.perm_append_comm :
                  List.Perm
                    (((splitCanonicalSupportClauseGroups groups).blocks.bind
                      fun b => b.blockCNF) ++ g.2)
                    (g.2 ++
                      ((splitCanonicalSupportClauseGroups groups).blocks.bind
                        fun b => b.blockCNF)))
          have htailLeft :
              List.Perm
                (g.2 ++
                  (((splitCanonicalSupportClauseGroups groups).blocks.bind
                    fun b => b.blockCNF) ++
                      (splitCanonicalSupportClauseGroups groups).residualCNF))
                (g.2 ++ groups.bind Prod.snd) :=
            List.Perm.append_left g.2 htail
          exact List.Perm.trans hswap htailLeft

/-- Recognition evidence composes across concatenated support-group lists. -/
theorem GroupsRecognized.append
    {m : Nat}
    {leftGroups rightGroups : List (CanonicalSupportClauseGroup m)}
    {leftBlocks rightBlocks :
      List (CanonicalFingerprintRecognizedParityBlock m)}
    (hleft : GroupsRecognized leftGroups leftBlocks)
    (hright : GroupsRecognized rightGroups rightBlocks) :
    GroupsRecognized
      (leftGroups ++ rightGroups)
      (leftBlocks ++ rightBlocks) := by
  induction leftGroups generalizing leftBlocks with
  | nil =>
      cases leftBlocks with
      | nil =>
          exact hright
      | cons _ _ =>
          cases hleft
  | cons g leftGroups ih =>
      cases leftBlocks with
      | nil =>
          cases hleft
      | cons b leftBlocks =>
          exact
            And.intro hleft.1
              (ih hleft.2)

/-- Recognized groups split to exactly those blocks and no residual CNF. -/
theorem splitCanonicalSupportClauseGroups_of_groupsRecognized
    {m : Nat}
    {groups : List (CanonicalSupportClauseGroup m)}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (h : GroupsRecognized groups blocks) :
    splitCanonicalSupportClauseGroups groups =
      { blocks := blocks, residualCNF := [] } := by
  induction groups generalizing blocks with
  | nil =>
      cases blocks with
      | nil =>
          rfl
      | cons _ _ =>
          cases h
  | cons g groups ih =>
      cases blocks with
      | nil =>
          cases h
      | cons b blocks =>
          have hinfer : inferCanonicalParityBlock g.2 = some b := h.1
          have htail : GroupsRecognized groups blocks := h.2
          have hsplit := ih htail
          simp [splitCanonicalSupportClauseGroups, hinfer, hsplit]

/-- Compact GF(2) output for appended canonical block lists is list append. -/
theorem canonicalFingerprintRecognizedBlocksGF2_append
    {m : Nat}
    (left right : List (CanonicalFingerprintRecognizedParityBlock m)) :
    canonicalFingerprintRecognizedBlocksGF2 (left ++ right) =
      List.append (canonicalFingerprintRecognizedBlocksGF2 left)
        (canonicalFingerprintRecognizedBlocksGF2 right) := by
  simp [canonicalFingerprintRecognizedBlocksGF2]

/--
Residual-free support-group splits compose across appended group lists.  This is
the splitter-level frame lemma that lets already-complete fragments be reused
without re-opening their recognizer proofs.
-/
theorem splitCanonicalSupportClauseGroups_append_of_residual_free
    {m : Nat}
    {leftGroups rightGroups : List (CanonicalSupportClauseGroup m)}
    {leftBlocks rightBlocks :
      List (CanonicalFingerprintRecognizedParityBlock m)}
    (hleft :
      splitCanonicalSupportClauseGroups leftGroups =
        { blocks := leftBlocks, residualCNF := [] })
    (hright :
      splitCanonicalSupportClauseGroups rightGroups =
        { blocks := rightBlocks, residualCNF := [] }) :
    splitCanonicalSupportClauseGroups (leftGroups ++ rightGroups) =
      { blocks := leftBlocks ++ rightBlocks, residualCNF := [] } := by
  induction leftGroups generalizing leftBlocks with
  | nil =>
      simp [splitCanonicalSupportClauseGroups] at hleft
      cases hleft
      simpa [splitCanonicalSupportClauseGroups] using hright
  | cons g groups ih =>
      unfold splitCanonicalSupportClauseGroups at hleft
      cases hinfer : inferCanonicalParityBlock g.2 with
      | some b =>
          cases htail : splitCanonicalSupportClauseGroups groups with
          | mk tailBlocks tailResidual =>
              simp [hinfer, htail] at hleft
              cases leftBlocks with
              | nil =>
                  simp at hleft
              | cons b' leftBlocksTail =>
                  cases hleft with
                  | intro hblocks hresidual =>
                      cases hblocks
                      cases hresidual
                      have htailFree :
                          splitCanonicalSupportClauseGroups groups =
                            { blocks := tailBlocks, residualCNF := [] } := by
                        simpa using htail
                      have hih := ih htailFree
                      unfold splitCanonicalSupportClauseGroups
                      simp [hinfer, hih]
      | none =>
          cases htail : splitCanonicalSupportClauseGroups groups with
          | mk tailBlocks tailResidual =>
              simp [hinfer, htail] at hleft
              cases hleft with
              | intro hblocks hrest =>
                  cases hrest with
                  | intro hgempty hresidual =>
                      cases hblocks
                      cases hresidual
                      have htailFree :
                          splitCanonicalSupportClauseGroups groups =
                            { blocks := leftBlocks, residualCNF := [] } := by
                        simpa using htail
                      have hih := ih htailFree
                      have hinferEmpty :
                          inferCanonicalParityBlock
                            ([] : CNFModel.CNF m) = none := by
                        simpa [hgempty] using hinfer
                      unfold splitCanonicalSupportClauseGroups
                      simp [hih, hgempty, hinferEmpty]

/-- The executable extractor's residual-free output matches a GF(2) target. -/
def ExtractorCompleteOn {m : Nat}
    (f : CNFModel.CNF m) (s : ParityEncoded.GF2Formula m) : Prop :=
  exists blocks : List (CanonicalFingerprintRecognizedParityBlock m),
    splitArityFourParityCanonicalSupportGroups f =
      { blocks := blocks, residualCNF := [] } /\
    List.Perm (canonicalFingerprintRecognizedBlocksGF2 blocks) s

/--
Combined semantic/executable extraction claim.  This is the surface downstream
theorems should cite when they need both per-assignment CNF/GF(2) equivalence
and residual-free completeness of the executable splitter.
-/
def SemanticExtractorCompleteOn {m : Nat}
    (f : CNFModel.CNF m) (s : ParityEncoded.GF2Formula m) : Prop :=
  (forall a : CNFModel.Assignment m,
    CNFModel.cnfSat a f <->
      ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a s) /\
    ExtractorCompleteOn f s

/-- Residual-free extractor completeness is invariant under GF(2) output permutation. -/
theorem extractorCompleteOn_gf2_perm
    {m : Nat} {f : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hperm : List.Perm s t)
    (h : ExtractorCompleteOn f s) :
    ExtractorCompleteOn f t := by
  rcases h with ⟨blocks, hsplit, hgf2⟩
  exact ⟨blocks, hsplit, List.Perm.trans hgf2 hperm⟩

/--
Combined semantic/executable extraction is invariant under GF(2) output
permutation.
-/
theorem semanticExtractorCompleteOn_gf2_perm
    {m : Nat} {f : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hperm : List.Perm s t)
    (h : SemanticExtractorCompleteOn f s) :
    SemanticExtractorCompleteOn f t := by
  constructor
  case left =>
    intro a
    exact Iff.trans (h.1 a)
      (ParityEncoded.gf2Sat_iff_of_perm (a := a) hperm)
  case right =>
    exact extractorCompleteOn_gf2_perm hperm h.2

/--
A declarative class witness plus an executable extractor-completeness witness
gives the combined semantic/executable extraction claim.
-/
theorem semanticExtractorCompleteOn_of_class
    {m : Nat} {f : CNFModel.CNF m} {s : ParityEncoded.GF2Formula m}
    (hclass : ParityEncoded.Class m f s)
    (hextract : ExtractorCompleteOn f s) :
    SemanticExtractorCompleteOn f s :=
  And.intro (ParityEncoded.Class.sound hclass) hextract

/--
If the current support grouper returns recognized groups, then the full
canonical splitter is complete for the corresponding GF(2) target.
-/
theorem extractorCompleteOn_of_groupRecognition
    {m : Nat} {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    {groups : List (CanonicalSupportClauseGroup m)}
    {blocks : List (CanonicalFingerprintRecognizedParityBlock m)}
    (hgroups : groupClausesByCanonicalSupport f = groups)
    (hrec : GroupsRecognized groups blocks)
    (hgf2 : List.Perm (canonicalFingerprintRecognizedBlocksGF2 blocks) s) :
    ExtractorCompleteOn f s := by
  refine Exists.intro blocks ?_
  constructor
  case left =>
    unfold splitArityFourParityCanonicalSupportGroups
    rw [hgroups]
    exact splitCanonicalSupportClauseGroups_of_groupsRecognized hrec
  case right =>
    exact hgf2

/--
Single-group specialization for one canonical component.  This is the atom case
the future class-completeness proof should use after proving the component
grouping and inferred block facts for clause-complete parity expansions.
-/
theorem extractorCompleteOn_of_singleRecognizedGroup
    {m : Nat} {f : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    {key : CanonicalClauseSupportKey}
    {block : CanonicalFingerprintRecognizedParityBlock m}
    (hgroups : groupClausesByCanonicalSupport f = [(key, f)])
    (hinfer : inferCanonicalParityBlock f = some block)
    (hgf2 : List.Perm [block.compactGF2] s) :
    ExtractorCompleteOn f s := by
  apply extractorCompleteOn_of_groupRecognition
    (groups := [(key, f)])
    (blocks := [block])
  case hgroups =>
    exact hgroups
  case hrec =>
    exact And.intro hinfer True.intro
  case hgf2 =>
    exact hgf2

/--
Union-fragment completeness bridge.  Once the grouping pass for a concatenated
CNF is known to return the concatenation of the two recognized group lists, the
executable extractor is complete for the combined GF(2) target.
-/
theorem extractorCompleteOn_of_appendGroupRecognition
    {m : Nat} {f g : CNFModel.CNF m}
    {s : ParityEncoded.GF2Formula m}
    {leftGroups rightGroups : List (CanonicalSupportClauseGroup m)}
    {leftBlocks rightBlocks :
      List (CanonicalFingerprintRecognizedParityBlock m)}
    (hgroups :
      groupClausesByCanonicalSupport (f ++ g) =
        leftGroups ++ rightGroups)
    (hleft : GroupsRecognized leftGroups leftBlocks)
    (hright : GroupsRecognized rightGroups rightBlocks)
    (hgf2 :
      List.Perm
        (canonicalFingerprintRecognizedBlocksGF2
          (leftBlocks ++ rightBlocks))
        s) :
    ExtractorCompleteOn (f ++ g) s := by
  apply extractorCompleteOn_of_groupRecognition
    (groups := leftGroups ++ rightGroups)
    (blocks := leftBlocks ++ rightBlocks)
  case hgroups =>
    exact hgroups
  case hrec =>
    exact GroupsRecognized.append hleft hright
  case hgf2 =>
    exact hgf2

/--
Extractor completeness composes when the grouping pass itself frames the
append as the concatenation of the two fragment groupings.
-/
theorem extractorCompleteOn_append_of_groupAppend
    {m : Nat} {f g : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hgroups :
      groupClausesByCanonicalSupport (f ++ g) =
        groupClausesByCanonicalSupport f ++ groupClausesByCanonicalSupport g)
    (hleft : ExtractorCompleteOn f s)
    (hright : ExtractorCompleteOn g t) :
    ExtractorCompleteOn (f ++ g) (List.append s t) := by
  cases hleft with
  | intro leftBlocks hleftRest =>
      cases hleftRest with
      | intro hleftSplit hleftGF2 =>
          cases hright with
          | intro rightBlocks hrightRest =>
              cases hrightRest with
              | intro hrightSplit hrightGF2 =>
                  refine Exists.intro (leftBlocks ++ rightBlocks) ?_
                  constructor
                  case left =>
                    unfold splitArityFourParityCanonicalSupportGroups
                      at hleftSplit hrightSplit
                    unfold splitArityFourParityCanonicalSupportGroups
                    rw [hgroups]
                    exact
                      splitCanonicalSupportClauseGroups_append_of_residual_free
                        hleftSplit hrightSplit
                  case right =>
                    rw [canonicalFingerprintRecognizedBlocksGF2_append]
                    exact hleftGF2.append hrightGF2

/--
Combined semantic/executable extraction composes when the grouping pass itself
frames the append as the concatenation of the two fragment groupings.
-/
theorem semanticExtractorCompleteOn_append_of_groupAppend
    {m : Nat} {f g : CNFModel.CNF m}
    {s t : ParityEncoded.GF2Formula m}
    (hgroups :
      groupClausesByCanonicalSupport (f ++ g) =
        groupClausesByCanonicalSupport f ++ groupClausesByCanonicalSupport g)
    (hleft : SemanticExtractorCompleteOn f s)
    (hright : SemanticExtractorCompleteOn g t) :
    SemanticExtractorCompleteOn (f ++ g) (List.append s t) := by
  constructor
  case left =>
    intro a
    constructor
    case mp =>
      intro hsat
      have hsplit := (cnfSat_append_iff a f g).1 hsat
      exact
        (ParityEncoded.gf2Sat_append_iff a s t).2
          (And.intro
            ((hleft.1 a).1 hsplit.1)
            ((hright.1 a).1 hsplit.2))
    case mpr =>
      intro hsat
      have hsplit := (ParityEncoded.gf2Sat_append_iff a s t).1 hsat
      exact
        (cnfSat_append_iff a f g).2
          (And.intro
            ((hleft.1 a).2 hsplit.1)
            ((hright.1 a).2 hsplit.2))
  case right =>
    exact extractorCompleteOn_append_of_groupAppend hgroups hleft.2 hright.2

end ExtractorCompleteness
end TseitinCNFData
end CertifiedAffine
