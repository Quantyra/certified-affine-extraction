import Std
import CertifiedAffine.BasicDefs
import CertifiedAffine.DecisionTreeModel
import CertifiedAffine.CNFData
import CertifiedAffine.CNFDataSearchBridge

namespace CertifiedAffine
namespace DecisionTreeSearch

open Basic

/-!
Search-problem scaffold with CNFData correctness hook.
-/

structure SearchProblem where
  vars : Nat

/-- Canonical search problem placeholder associated with a CNF. -/
def CNFSearch (F : CNF) : SearchProblem :=
  { vars := F.vcount }

/-- A total assignment to `n` variables. -/
def Assignment (n : Nat) : Type := Fin n -> Bool

/-- Placeholder: a CNF is satisfied by any assignment (to be refined). -/
def CNFSat (_F : CNF) (_a : Assignment _F.vcount) : Prop := True

/-- A bundle that carries explicit clause data for a Basic.CNF. -/
structure CNFBundle where
  data : CNFData.CNFData

/-- CNF satisfiability for a bundled CNF using explicit clause data. -/
def CNFSatBundle (B : CNFBundle) (a : Assignment B.data.base.vcount) : Prop :=
  CNFData.cnfSat B.data a

/-- Typeclass to provide bundle semantics for a specific Basic.CNF. -/
class CNFBundleProvider (F : CNF) where
  bundle : CNFBundle
  base_eq : F = bundle.data.base

/-- Prefer bundle semantics when explicit clauses are available. -/
def CNFSatOfBundle (B : CNFBundle) (a : Assignment B.data.base.vcount) : Prop :=
  CNFSatBundle B a

/-- Preferred satisfiability when a bundle provider is available. -/
def CNFSatPreferred (F : CNF) (a : Assignment F.vcount)
    [p : CNFBundleProvider F] : Prop := by
  have h : F.vcount = p.bundle.data.base.vcount := by
    simp [p.base_eq]
  have a' : Assignment p.bundle.data.base.vcount := by
    simpa [Assignment, h] using a
  exact CNFSatBundle p.bundle (a := a')

/-- Placeholder: search output type. -/
structure SearchOutput where
  witness : Nat

/-- Default search correctness (still stub for Basic.CNF). -/
def SearchCorrect (_F : CNF) (_a : Assignment _F.vcount) (_out : SearchOutput) : Prop := True

/-- Decision trees solve a search problem by querying variable indices. -/
def DT (p : SearchProblem) : Type := DecisionTreeModel.DT p.vars

/-- Depth and leaves re-exported for convenience. -/
def DTdepth {p : SearchProblem} (t : DT p) : Nat :=
  DecisionTreeModel.depth t

def DTleaves {p : SearchProblem} (t : DT p) : Nat :=
  DecisionTreeModel.leaves t

/-- Solver scaffold with a correctness placeholder. -/
structure Solver (p : SearchProblem) where
  tree : DT p
  correct : Prop

/-- Depth of a concrete solver. -/
def DTdepth_of {p : SearchProblem} (s : Solver p) : Nat :=
  DTdepth s.tree

/-- Bundle-backed clause count for CNFs with explicit clause data. -/
def bundleClauseCount (F : CNF) [p : CNFBundleProvider F] : Nat :=
  p.bundle.data.clauses.length

/-- Optional stronger DT-depth provider sourced from a certified witness path. -/
class CertifiedDTdepthProvider (F : CNF) where
  certifiedDTdepth : Nat

/-- Preference source chosen for an additive DT-depth model. -/
inductive DTdepthPreferenceSource
  | certified
  | bundled
  | fallback
  deriving Repr, DecidableEq

/-- Additive DT-depth model that records which semantic source was chosen. -/
structure PreferredDTdepthModel (F : CNF) : Type where
  depth : Nat
  source : DTdepthPreferenceSource

/-- Preferred DT-depth when a certified provider is available. -/
def preferredDTdepthModelFromCertified (F : CNF) [p : CertifiedDTdepthProvider F] :
    PreferredDTdepthModel F :=
  { depth := p.certifiedDTdepth
    source := DTdepthPreferenceSource.certified }

/-- Preferred DT-depth when only bundle semantics are available. -/
def preferredDTdepthModelFromBundle (F : CNF) [p : CNFBundleProvider F] :
    PreferredDTdepthModel F :=
  { depth := p.bundle.data.clauses.length
    source := DTdepthPreferenceSource.bundled }

/-- Preferred DT-depth fallback when no richer semantics are available. -/
def preferredDTdepthModelFallback (F : CNF) : PreferredDTdepthModel F :=
  { depth := Basic.DTdepth F
    source := DTdepthPreferenceSource.fallback }

/-- Preferred DT-depth value from a certified provider. -/
def preferredDTdepthFromCertified (F : CNF) [CertifiedDTdepthProvider F] : Nat :=
  (preferredDTdepthModelFromCertified F).depth

/-- Preferred DT-depth value from a bundle provider. -/
def preferredDTdepthFromBundle (F : CNF) [CNFBundleProvider F] : Nat :=
  (preferredDTdepthModelFromBundle F).depth

/-- Preferred DT-depth fallback value. -/
def preferredDTdepthFallback (F : CNF) : Nat :=
  (preferredDTdepthModelFallback F).depth

theorem preferredDTdepthFromCertified_eq_certified (F : CNF)
    [p : CertifiedDTdepthProvider F] :
    preferredDTdepthFromCertified F = p.certifiedDTdepth := by
  rfl

theorem preferredDTdepthFromBundle_eq_clause_count (F : CNF) [p : CNFBundleProvider F] :
    preferredDTdepthFromBundle F = p.bundle.data.clauses.length := by
  rfl

theorem preferredDTdepthFallback_eq_DTdepth (F : CNF) :
    preferredDTdepthFallback F = Basic.DTdepth F := by
  rfl

/--
Additive bundle-aware DT-depth hook.
This does not replace `Basic.DTdepth`; it is the first semantic hook that can
depend on explicit clause payload when a `CNFBundleProvider` exists.
-/
def bundleAwareDTdepthModel (F : CNF) [p : CNFBundleProvider F] : Basic.DTdepthModel F :=
  { depth := bundleClauseCount F
    depth_matches := by trivial }

/-- Bundle-aware DT-depth value extracted from `bundleAwareDTdepthModel`. -/
def bundleAwareDTdepth (F : CNF) [p : CNFBundleProvider F] : Nat :=
  (bundleAwareDTdepthModel F).depth

theorem bundleAwareDTdepth_eq_clause_count (F : CNF) [p : CNFBundleProvider F] :
    bundleAwareDTdepth F = p.bundle.data.clauses.length := by
  rfl

/-- Lift CNFData correctness into the DecisionTreeSearch vocabulary. -/
def SearchCorrectFromData (F : CNFData.CNFData)
    (a : CNFData.Assignment F) (out : SearchOutput) : Prop :=
  CNFDataSearchBridge.SearchCorrect F a { witness := out.witness }

/-- Prefer bundle correctness when explicit clauses are available. -/
def SearchCorrectOfBundle (B : CNFBundle)
    (a : Assignment B.data.base.vcount) (out : SearchOutput) : Prop :=
  CNFDataSearchBridge.SearchCorrect B.data a { witness := out.witness }

/-- Preferred correctness when a bundle provider is available. -/
def SearchCorrectPreferred (F : CNF) (a : Assignment F.vcount) (out : SearchOutput)
    [p : CNFBundleProvider F] : Prop := by
  have h : F.vcount = p.bundle.data.base.vcount := by
    simp [p.base_eq]
  have a' : Assignment p.bundle.data.base.vcount := by
    simpa [Assignment, h] using a
  exact CNFDataSearchBridge.SearchCorrect p.bundle.data a'
    { witness := out.witness }

end DecisionTreeSearch
end CertifiedAffine
