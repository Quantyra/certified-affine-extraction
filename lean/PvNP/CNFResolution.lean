import PvNP.CNFModel

namespace PvNP
namespace CNFResolution

open CNFModel

def posLit {n : Nat} (v : Fin n) : Literal n :=
  { var := v, sign := true }

def negLit {n : Nat} (v : Fin n) : Literal n :=
  { var := v, sign := false }

def removePivotSign {n : Nat} (pivot : Fin n) (sign : Bool)
    (c : Clause n) : Clause n :=
  c.filter (fun l => !((decide (l.var = pivot)) && (decide (l.sign = sign))))

def resolveOn {n : Nat} (pivot : Fin n)
    (left right : Clause n) : Clause n :=
  removePivotSign pivot true left ++ removePivotSign pivot false right

inductive ResolutionDerivTree (n : Nat) : Type where
  | hyp : Clause n -> ResolutionDerivTree n
  | resolve : Fin n -> ResolutionDerivTree n -> ResolutionDerivTree n ->
      ResolutionDerivTree n

namespace ResolutionDerivTree

def conclusion {n : Nat} : ResolutionDerivTree n -> Clause n
  | hyp c => c
  | resolve pivot left right =>
      resolveOn pivot (conclusion left) (conclusion right)

def size {n : Nat} : ResolutionDerivTree n -> Nat
  | hyp _ => 1
  | resolve _ left right => 1 + size left + size right

/-- Tree-line view of a local derivation: one source line per tree node. -/
def sourceLineClauses {n : Nat} : ResolutionDerivTree n -> List (Clause n)
  | hyp c => [c]
  | resolve pivot left right =>
      sourceLineClauses left ++ sourceLineClauses right ++
        [resolveOn pivot (conclusion left) (conclusion right)]

inductive SourceLineTraceValid {n : Nat} (phi : CNF n) :
    List (Clause n) -> Clause n -> Prop where
  | hyp (c : Clause n) (hmem : List.Mem c phi) :
      SourceLineTraceValid phi [c] c
  | resolve (pivot : Fin n)
      {left right : Clause n} {leftLines rightLines : List (Clause n)}
      (hleft : SourceLineTraceValid phi leftLines left)
      (hright : SourceLineTraceValid phi rightLines right)
      (hpos : List.Mem (posLit pivot) left)
      (hneg : List.Mem (negLit pivot) right) :
      SourceLineTraceValid phi
        (leftLines ++ rightLines ++ [resolveOn pivot left right])
        (resolveOn pivot left right)

def Valid {n : Nat} (phi : CNF n) : ResolutionDerivTree n -> Prop
  | hyp c => List.Mem c phi
  | resolve pivot left right =>
      Valid phi left
        /\ Valid phi right
        /\ List.Mem (posLit pivot) (conclusion left)
        /\ List.Mem (negLit pivot) (conclusion right)

theorem sourceLineClauses_length_eq_size {n : Nat}
    (t : ResolutionDerivTree n) :
    (sourceLineClauses t).length = size t := by
  induction t with
  | hyp _ =>
      simp [sourceLineClauses, size]
  | resolve _ left right ihLeft ihRight =>
      simp [sourceLineClauses, size, ihLeft, ihRight,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem sourceLineClauses_traceValid {n : Nat} {phi : CNF n}
    {t : ResolutionDerivTree n} (h : Valid phi t) :
    SourceLineTraceValid phi (sourceLineClauses t) (conclusion t) := by
  induction t with
  | hyp c =>
      exact SourceLineTraceValid.hyp c h
  | resolve pivot left right ihLeft ihRight =>
      rcases h with ⟨hLeft, hRight, hPos, hNeg⟩
      exact SourceLineTraceValid.resolve pivot
        (ihLeft hLeft) (ihRight hRight) hPos hNeg

theorem size_pos {n : Nat} (t : ResolutionDerivTree n) : 1 <= size t := by
  induction t with
  | hyp _ =>
      simp [size]
  | resolve _ left right _ihLeft _ihRight =>
      simpa [size, Nat.add_assoc] using
        (Nat.succ_le_succ (Nat.zero_le (size left + size right)))

end ResolutionDerivTree

structure ResolutionRefutation {n : Nat} (phi : CNF n) where
  tree : ResolutionDerivTree n
  valid : ResolutionDerivTree.Valid phi tree
  derives_empty : ResolutionDerivTree.conclusion tree = []

def ResolutionRefutationSize {n : Nat} {phi : CNF n}
    (r : ResolutionRefutation phi) : Nat :=
  ResolutionDerivTree.size r.tree

def ResolutionRefutationSourceLineClauses {n : Nat} {phi : CNF n}
    (r : ResolutionRefutation phi) : List (Clause n) :=
  ResolutionDerivTree.sourceLineClauses r.tree

def ResolutionRefutationTreeSourceLineCount {n : Nat} {phi : CNF n}
    (r : ResolutionRefutation phi) : Nat :=
  (ResolutionRefutationSourceLineClauses r).length

theorem ResolutionRefutationTreeSourceLineCount_eq_size
    {n : Nat} {phi : CNF n} (r : ResolutionRefutation phi) :
    ResolutionRefutationTreeSourceLineCount r = ResolutionRefutationSize r := by
  simp [ResolutionRefutationTreeSourceLineCount,
    ResolutionRefutationSourceLineClauses, ResolutionRefutationSize,
    ResolutionDerivTree.sourceLineClauses_length_eq_size]

theorem ResolutionRefutationSourceLineTraceValid
    {n : Nat} {phi : CNF n} (r : ResolutionRefutation phi) :
    ResolutionDerivTree.SourceLineTraceValid phi
      (ResolutionRefutationSourceLineClauses r) [] := by
  have htrace :=
    ResolutionDerivTree.sourceLineClauses_traceValid
      (phi:=phi) (t:=r.tree) r.valid
  simpa [ResolutionRefutationSourceLineClauses, r.derives_empty] using htrace

def ResolutionSizeLowerBoundPremise {n : Nat} (phi : CNF n) (k : Nat) :
    Prop :=
  forall r : ResolutionRefutation phi, k <= ResolutionRefutationSize r

theorem le_resolutionSize_of_resolutionSizeLowerBoundPremise
    {n : Nat} {phi : CNF n} {k : Nat}
    (h : ResolutionSizeLowerBoundPremise phi k)
    (r : ResolutionRefutation phi) :
    k <= ResolutionRefutationSize r :=
  h r

theorem not_resolutionSizeLowerBoundPremise_of_small_refutation
    {n : Nat} {phi : CNF n} {k : Nat}
    (r : ResolutionRefutation phi) (hsmall : ResolutionRefutationSize r < k) :
    Not (ResolutionSizeLowerBoundPremise phi k) := by
  intro h
  exact (Nat.not_le_of_gt hsmall)
    (le_resolutionSize_of_resolutionSizeLowerBoundPremise h r)

structure ResolutionSizeFamilyTarget where
  Index : Type
  n : Index -> Nat
  phi : (i : Index) -> CNF (n i)
  threshold : Index -> Nat

def ResolutionSizeFamilyLowerBoundPremise
    (target : ResolutionSizeFamilyTarget) : Prop :=
  forall i : target.Index,
    ResolutionSizeLowerBoundPremise (target.phi i) (target.threshold i)

theorem not_resolutionSizeFamilyLowerBoundPremise_of_small_refutation
    (target : ResolutionSizeFamilyTarget) (i : target.Index)
    (r : ResolutionRefutation (target.phi i))
    (hsmall : ResolutionRefutationSize r < target.threshold i) :
    Not (ResolutionSizeFamilyLowerBoundPremise target) := by
  intro h
  exact (not_resolutionSizeLowerBoundPremise_of_small_refutation r hsmall) (h i)

inductive ResolutionProofObjectKind where
  | treeLike
  | dagLike
deriving Repr, DecidableEq

namespace ResolutionProofObjectKind

/--
Whether a source lower-bound proof-object class covers the local proof objects.
A lower bound for a broader proof system also lower-bounds a restricted local
system.  A tree-like source lower bound alone does not cover a DAG/general local
proof system.
-/
def covers : ResolutionProofObjectKind -> ResolutionProofObjectKind -> Prop
  | treeLike, treeLike => True
  | treeLike, dagLike => False
  | dagLike, treeLike => True
  | dagLike, dagLike => True

theorem treeLike_covers_treeLike : covers treeLike treeLike := by
  trivial

theorem dagLike_covers_treeLike : covers dagLike treeLike := by
  trivial

theorem dagLike_covers_dagLike : covers dagLike dagLike := by
  trivial

theorem not_treeLike_covers_dagLike : Not (covers treeLike dagLike) := by
  intro h
  cases h

end ResolutionProofObjectKind

def localResolutionProofObjectKind : ResolutionProofObjectKind :=
  ResolutionProofObjectKind.treeLike

structure ResolutionProofSystemMatch where
  sourceKind : ResolutionProofObjectKind
  localKind : ResolutionProofObjectKind
  lowerBoundTransfersToLocal : Prop
  sizeMeasureCompatible : Prop

/-- Proof-object kind compatibility required before importing a source lower bound. -/
def ResolutionProofSystemMatch.kindCompatible
    (m : ResolutionProofSystemMatch) : Prop :=
  ResolutionProofObjectKind.covers m.sourceKind m.localKind

/--
Checked boundary for proof-system transfer.  This keeps proof-object kind
coverage separate from the substantive source theorem transfer and size-measure
mapping obligations.
-/
def ResolutionProofSystemMatch.checkedBoundary
    (m : ResolutionProofSystemMatch) : Prop :=
  m.kindCompatible /\ m.lowerBoundTransfersToLocal /\ m.sizeMeasureCompatible

def ResolutionProofSystemMatch.asProp (m : ResolutionProofSystemMatch) : Prop :=
  m.checkedBoundary

/--
The common source-transfer shape where a general reusable-line resolution lower
bound is used for the local tree-shaped proof object.
-/
def ResolutionProofSystemMatch.generalSourceToLocalTree
    (lowerBoundTransfersToLocal sizeMeasureCompatible : Prop) :
    ResolutionProofSystemMatch where
  sourceKind := ResolutionProofObjectKind.dagLike
  localKind := localResolutionProofObjectKind
  lowerBoundTransfersToLocal := lowerBoundTransfersToLocal
  sizeMeasureCompatible := sizeMeasureCompatible

theorem ResolutionProofSystemMatch.generalSourceToLocalTree_kindCompatible
    (lowerBoundTransfersToLocal sizeMeasureCompatible : Prop) :
    (generalSourceToLocalTree
      lowerBoundTransfersToLocal sizeMeasureCompatible).kindCompatible := by
  trivial

theorem ResolutionProofSystemMatch.generalSourceToLocalTree_asProp_iff
    (lowerBoundTransfersToLocal sizeMeasureCompatible : Prop) :
    (generalSourceToLocalTree
      lowerBoundTransfersToLocal sizeMeasureCompatible).asProp
      <-> lowerBoundTransfersToLocal /\ sizeMeasureCompatible := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact And.intro
      (generalSourceToLocalTree_kindCompatible
        lowerBoundTransfersToLocal sizeMeasureCompatible)
      h

/-- Source-side size measure named by a theorem packet. -/
inductive ResolutionSourceSizeMeasureKind where
  | lineCount
  | treeLineCount
  | inferenceCount
  | asymptoticSize
deriving Repr, DecidableEq

/-- Source-side size parameter used by an asymptotic family theorem. -/
inductive ResolutionSourceSizeParameterKind where
  | formulaSize
  | variableCount
  | clauseCount
  | graphVertexCount
  | graphEdgeCount
  | explicitIndexMeasure
deriving Repr, DecidableEq

/-- Descriptive source theorem packet, kept separate from certified transfer. -/
structure ResolutionSourceTheoremPacket where
  sourceName : String
  theoremName : String
  sourceURL : String
  proofObjectKind : ResolutionProofObjectKind
  sizeMeasureKind : ResolutionSourceSizeMeasureKind
  theoremStatement : String
  assumptionStatement : String
  thresholdStatement : String

/-- Typed boundary for a source-side `2^Omega(parameter)` theorem. -/
structure ResolutionAsymptoticExponentialThreshold where
  sizeParameterKind : ResolutionSourceSizeParameterKind
  cNum : Nat
  cDen : Nat
  n0 : Nat
  threshold : Nat -> Nat
  constantPositive : 0 < cNum /\ 0 < cDen
  sourceOmegaStatement : Prop

def ResolutionAsymptoticExponentialThreshold.appliesAt
    (spec : ResolutionAsymptoticExponentialThreshold) (parameter : Nat) :
    Prop :=
  spec.n0 <= parameter

/-- Concrete arithmetic meaning of the stored exponential-threshold constants. -/
def ResolutionAsymptoticExponentialThreshold.concreteLowerBound
    (spec : ResolutionAsymptoticExponentialThreshold) : Prop :=
  forall n : Nat,
    spec.appliesAt n ->
      2 ^ ((spec.cNum * n) / spec.cDen) <= spec.threshold n

/-- Interprets a source asymptotic threshold as concrete target thresholds. -/
structure ResolutionFamilyThresholdInterpretation
    (target : ResolutionSizeFamilyTarget) where
  sourceThreshold : ResolutionAsymptoticExponentialThreshold
  parameter : target.Index -> Nat
  threshold_matches :
    forall i : target.Index,
      target.threshold i = sourceThreshold.threshold (parameter i)
  parameters_eventual :
    forall i : target.Index,
      sourceThreshold.appliesAt (parameter i)

/-- Source line count after translating a local refutation into the source model. -/
def ResolutionSourceLineCount {n : Nat} (phi : CNF n) : Type :=
  ResolutionRefutation phi -> Nat

def ResolutionSourceLineLowerBoundPremise {n : Nat} (phi : CNF n) (k : Nat)
    (sourceLineCount : ResolutionSourceLineCount phi) : Prop :=
  forall r : ResolutionRefutation phi, k <= sourceLineCount r

def ResolutionSourceLineCountTransfersToLocalTree {n : Nat} (phi : CNF n)
    (sourceLineCount : ResolutionSourceLineCount phi) : Prop :=
  forall r : ResolutionRefutation phi,
    sourceLineCount r <= ResolutionRefutationSize r

theorem resolutionSizeLowerBoundPremise_of_sourceLineLowerBound
    {n : Nat} {phi : CNF n} {k : Nat}
    {sourceLineCount : ResolutionSourceLineCount phi}
    (hsource : ResolutionSourceLineLowerBoundPremise phi k sourceLineCount)
    (htransfer :
      ResolutionSourceLineCountTransfersToLocalTree phi sourceLineCount) :
    ResolutionSizeLowerBoundPremise phi k := by
  intro r
  exact Nat.le_trans (hsource r) (htransfer r)

def ResolutionFamilySourceLineCount
    (target : ResolutionSizeFamilyTarget) : Type :=
  (i : target.Index) -> ResolutionRefutation (target.phi i) -> Nat

def ResolutionFamilyTreeSourceLineCount
    (target : ResolutionSizeFamilyTarget) :
    ResolutionFamilySourceLineCount target :=
  fun _ r => ResolutionRefutationTreeSourceLineCount r

def ResolutionFamilySourceLineLowerBoundPremise
    (target : ResolutionSizeFamilyTarget)
    (sourceLineCount : ResolutionFamilySourceLineCount target) : Prop :=
  forall (i : target.Index) (r : ResolutionRefutation (target.phi i)),
    target.threshold i <= sourceLineCount i r

/--
Source-line lower-bound premise stated at the interpreted source threshold,
before rewriting it to the local target threshold.
-/
def ResolutionFamilyInterpretedSourceLineLowerBoundPremise
    (target : ResolutionSizeFamilyTarget)
    (interpretation : ResolutionFamilyThresholdInterpretation target)
    (sourceLineCount : ResolutionFamilySourceLineCount target) : Prop :=
  forall (i : target.Index) (r : ResolutionRefutation (target.phi i)),
    interpretation.sourceThreshold.threshold (interpretation.parameter i) <=
      sourceLineCount i r

def ResolutionFamilyTraceLineLowerBoundPremise
    (target : ResolutionSizeFamilyTarget) : Prop :=
  forall (i : target.Index) (r : ResolutionRefutation (target.phi i)),
    ResolutionDerivTree.SourceLineTraceValid (target.phi i)
      (ResolutionRefutationSourceLineClauses r) [] ->
    target.threshold i <= ResolutionRefutationTreeSourceLineCount r

/--
Explicit exponential trace-line lower-bound premise induced by an interpreted
source threshold's stored constants.
-/
def ResolutionFamilyExplicitExponentialTraceLineLowerBoundPremise
    (target : ResolutionSizeFamilyTarget)
    (interpretation : ResolutionFamilyThresholdInterpretation target) : Prop :=
  forall (i : target.Index) (r : ResolutionRefutation (target.phi i)),
    ResolutionDerivTree.SourceLineTraceValid (target.phi i)
      (ResolutionRefutationSourceLineClauses r) [] ->
    2 ^ ((interpretation.sourceThreshold.cNum * interpretation.parameter i) /
        interpretation.sourceThreshold.cDen) <=
      ResolutionRefutationTreeSourceLineCount r

/--
Explicit exponential refutation-size lower-bound premise induced by an
interpreted source threshold's stored constants.
-/
def ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
    (target : ResolutionSizeFamilyTarget)
    (interpretation : ResolutionFamilyThresholdInterpretation target) : Prop :=
  forall (i : target.Index) (r : ResolutionRefutation (target.phi i)),
    2 ^ ((interpretation.sourceThreshold.cNum * interpretation.parameter i) /
        interpretation.sourceThreshold.cDen) <=
      ResolutionRefutationSize r

def ResolutionFamilySourceLineCountTransfersToLocalTree
    (target : ResolutionSizeFamilyTarget)
    (sourceLineCount : ResolutionFamilySourceLineCount target) : Prop :=
  forall (i : target.Index) (r : ResolutionRefutation (target.phi i)),
    sourceLineCount i r <= ResolutionRefutationSize r

theorem ResolutionFamilyTreeSourceLineCount_transfersToLocalTree
    (target : ResolutionSizeFamilyTarget) :
    ResolutionFamilySourceLineCountTransfersToLocalTree target
      (ResolutionFamilyTreeSourceLineCount target) := by
  intro _ r
  rw [ResolutionFamilyTreeSourceLineCount,
    ResolutionRefutationTreeSourceLineCount_eq_size]
  exact Nat.le_refl _

theorem ResolutionFamilySourceLineLowerBoundPremise_of_traceLineLowerBound
    {target : ResolutionSizeFamilyTarget}
    (hsource : ResolutionFamilyTraceLineLowerBoundPremise target) :
    ResolutionFamilySourceLineLowerBoundPremise target
      (ResolutionFamilyTreeSourceLineCount target) := by
  intro i r
  exact hsource i r (ResolutionRefutationSourceLineTraceValid r)

theorem ResolutionFamilySourceLineLowerBoundPremise_of_interpretedSourceLineLowerBound
    {target : ResolutionSizeFamilyTarget}
    {interpretation : ResolutionFamilyThresholdInterpretation target}
    {sourceLineCount : ResolutionFamilySourceLineCount target}
    (hsource :
      ResolutionFamilyInterpretedSourceLineLowerBoundPremise
        target interpretation sourceLineCount) :
    ResolutionFamilySourceLineLowerBoundPremise target sourceLineCount := by
  intro i r
  have h :=
    hsource i r
  simpa [interpretation.threshold_matches i] using h

theorem ResolutionFamilyTraceLineLowerBoundPremise_of_interpretedTreeSourceLineLowerBound
    {target : ResolutionSizeFamilyTarget}
    {interpretation : ResolutionFamilyThresholdInterpretation target}
    (hsource :
      ResolutionFamilyInterpretedSourceLineLowerBoundPremise
        target interpretation (ResolutionFamilyTreeSourceLineCount target)) :
    ResolutionFamilyTraceLineLowerBoundPremise target := by
  intro i r _htrace
  have h :=
    hsource i r
  simpa [ResolutionFamilyTreeSourceLineCount,
    interpretation.threshold_matches i] using h

theorem ResolutionFamilyExplicitExponentialTraceLineLowerBoundPremise_of_traceLineLowerBound
    {target : ResolutionSizeFamilyTarget}
    {interpretation : ResolutionFamilyThresholdInterpretation target}
    (hsource : ResolutionFamilyTraceLineLowerBoundPremise target)
    (hconcrete : interpretation.sourceThreshold.concreteLowerBound) :
    ResolutionFamilyExplicitExponentialTraceLineLowerBoundPremise
      target interpretation := by
  intro i r htrace
  have hthreshold := hsource i r htrace
  have hsourceThreshold :
      interpretation.sourceThreshold.threshold (interpretation.parameter i) <=
        ResolutionRefutationTreeSourceLineCount r := by
    simpa [interpretation.threshold_matches i] using hthreshold
  exact Nat.le_trans
    (hconcrete (interpretation.parameter i)
      (interpretation.parameters_eventual i))
    hsourceThreshold

theorem ResolutionFamilyExplicitExponentialSizeLowerBoundPremise_of_explicitTraceLineLowerBound
    {target : ResolutionSizeFamilyTarget}
    {interpretation : ResolutionFamilyThresholdInterpretation target}
    (hsource :
      ResolutionFamilyExplicitExponentialTraceLineLowerBoundPremise
        target interpretation) :
    ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      target interpretation := by
  intro i r
  have htrace :=
    hsource i r (ResolutionRefutationSourceLineTraceValid r)
  rw [ResolutionRefutationTreeSourceLineCount_eq_size] at htrace
  exact htrace

theorem ResolutionFamilyExplicitExponentialSizeLowerBoundPremise_of_traceLineLowerBound
    {target : ResolutionSizeFamilyTarget}
    {interpretation : ResolutionFamilyThresholdInterpretation target}
    (hsource : ResolutionFamilyTraceLineLowerBoundPremise target)
    (hconcrete : interpretation.sourceThreshold.concreteLowerBound) :
    ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      target interpretation := by
  exact
    ResolutionFamilyExplicitExponentialSizeLowerBoundPremise_of_explicitTraceLineLowerBound
      (ResolutionFamilyExplicitExponentialTraceLineLowerBoundPremise_of_traceLineLowerBound
        hsource hconcrete)

theorem resolutionSizeFamilyLowerBoundPremise_of_sourceLineLowerBound
    {target : ResolutionSizeFamilyTarget}
    {sourceLineCount : ResolutionFamilySourceLineCount target}
    (hsource :
      ResolutionFamilySourceLineLowerBoundPremise target sourceLineCount)
    (htransfer :
      ResolutionFamilySourceLineCountTransfersToLocalTree
        target sourceLineCount) :
    ResolutionSizeFamilyLowerBoundPremise target := by
  intro i r
  exact Nat.le_trans (hsource i r) (htransfer i r)

theorem resolutionSizeFamilyLowerBoundPremise_of_traceLineLowerBound
    {target : ResolutionSizeFamilyTarget}
    (hsource : ResolutionFamilyTraceLineLowerBoundPremise target) :
    ResolutionSizeFamilyLowerBoundPremise target := by
  exact resolutionSizeFamilyLowerBoundPremise_of_sourceLineLowerBound
    (target:=target)
    (sourceLineCount:=ResolutionFamilyTreeSourceLineCount target)
    (ResolutionFamilySourceLineLowerBoundPremise_of_traceLineLowerBound hsource)
    (ResolutionFamilyTreeSourceLineCount_transfersToLocalTree target)

structure ResolutionSourceBoundaryTarget where
  n : Nat
  phi : CNF n
  threshold : Nat
  sourceName : String
  sourceStatement : String
  proofSystemMatch : Prop
  encodingMatch : Prop
  sizeMeasureMatch : Prop
  thresholdMatch : Prop

def ResolutionSourceBoundaryTarget.lowerBoundPremise
    (target : ResolutionSourceBoundaryTarget) : Prop :=
  ResolutionSizeLowerBoundPremise target.phi target.threshold

structure ResolutionSourceBoundaryCertificate
    (target : ResolutionSourceBoundaryTarget) where
  proof_system_match : target.proofSystemMatch
  encoding_match : target.encodingMatch
  size_measure_match : target.sizeMeasureMatch
  threshold_match : target.thresholdMatch
  lower_bound : target.lowerBoundPremise

theorem resolutionSizeLowerBoundPremise_of_sourceBoundary
    {target : ResolutionSourceBoundaryTarget}
    (cert : ResolutionSourceBoundaryCertificate target) :
    ResolutionSizeLowerBoundPremise target.phi target.threshold :=
  cert.lower_bound

structure ResolutionFamilySourceBoundaryTarget where
  target : ResolutionSizeFamilyTarget
  sourceName : String
  sourceStatement : String
  proofSystemMatch : Prop
  encodingFamilyMatch : Prop
  sizeMeasureMatch : Prop
  thresholdFamilyMatch : Prop

def ResolutionFamilySourceBoundaryTarget.lowerBoundPremise
    (boundary : ResolutionFamilySourceBoundaryTarget) : Prop :=
  ResolutionSizeFamilyLowerBoundPremise boundary.target

structure ResolutionFamilySourceBoundaryCertificate
    (boundary : ResolutionFamilySourceBoundaryTarget) where
  proof_system_match : boundary.proofSystemMatch
  encoding_family_match : boundary.encodingFamilyMatch
  size_measure_match : boundary.sizeMeasureMatch
  threshold_family_match : boundary.thresholdFamilyMatch
  lower_bound : boundary.lowerBoundPremise

theorem resolutionSizeFamilyLowerBoundPremise_of_sourceBoundary
    {boundary : ResolutionFamilySourceBoundaryTarget}
    (cert : ResolutionFamilySourceBoundaryCertificate boundary) :
    ResolutionSizeFamilyLowerBoundPremise boundary.target :=
  cert.lower_bound

end CNFResolution
end PvNP
