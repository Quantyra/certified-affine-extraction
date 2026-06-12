import Std
import CertifiedAffine.CNFModel
import CertifiedAffine.ResoplusPDT

namespace CertifiedAffine
namespace CNFModelParityBridge

open ResoplusPDT

/-!
Minimal bridge from CNFModel clauses to parity clauses.
This is intentionally lossy: it embeds each literal as a unit parity clause
and forgets disjunction structure. This suffices for a placeholder SearchRel
adapter without changing existing semantics.
-/

/-- Encode a CNFModel literal as a parity clause over the same variable. -/
def litToParity {n : Nat} (l : CNFModel.Literal n) : ResoplusPDT.ParityClause (Basic.CNF.mk n) :=
  { vars := [l.var], rhs := !l.sign }

/-- Encode a CNFModel clause as a list of parity clauses (one per literal). -/
def clauseToParity {n : Nat} (c : CNFModel.Clause n) : List (ResoplusPDT.ParityClause (Basic.CNF.mk n)) :=
  c.map litToParity

/-- Encode a CNFModel CNF as a list of parity clauses by flattening literals. -/
def cnfToParity {n : Nat} (phi : CNFModel.CNF n) : List (ResoplusPDT.ParityClause (Basic.CNF.mk n)) :=
  phi.bind clauseToParity

/-- Search relation adapter for CNFModel CNFs (flattened literal witnesses). -/
def cnfModelSearchRel {n : Nat} (phi : CNFModel.CNF n) :
    ResoplusPDT.SearchRel (Basic.CNF.mk n) (ResoplusPDT.ParityClause (Basic.CNF.mk n)) :=
  ResoplusPDT.SearchRel.mk (fun a c => List.Mem c (cnfToParity phi) /\ ResoplusPDT.ClauseSat a c)

/-- Bridge lemma: CNFModel search relation is the standard parity CNF search relation. -/
theorem cnfModelSearchRel_eq_cnfSearchRel {n : Nat} (phi : CNFModel.CNF n) :
    cnfModelSearchRel (n := n) phi =
      ResoplusPDT.cnfSearchRel (F := Basic.CNF.mk n) (cnfToParity phi) := by
  rfl

end CNFModelParityBridge
end CertifiedAffine
