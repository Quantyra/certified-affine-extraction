import Std
import CertifiedAffine.CNFModel
import CertifiedAffine.CNFModelParityBridge
import CertifiedAffine.ResoplusPDT

namespace CertifiedAffine
namespace CNFModelLiftBridge

open ResoplusPDT

/-- Embed a variable into the first position of its block in the lifted space. -/
def embedVar {n b : Nat} (hb : 0 < b) (v : Fin n) : Fin (b * n) := by
  refine Fin.mk v.1 ?_
  have hle : n <= b * n := Nat.le_mul_of_pos_left n hb
  exact Nat.lt_of_lt_of_le v.isLt hle

/-- Lift a CNFModel literal by embedding its variable. -/
def liftLiteral {n b : Nat} (hb : 0 < b) (l : CNFModel.Literal n) : CNFModel.Literal (b * n) :=
  { var := embedVar hb l.var, sign := l.sign }

/-- Lift a CNFModel clause by embedding each literal. -/
def liftClause {n b : Nat} (hb : 0 < b) (c : CNFModel.Clause n) : CNFModel.Clause (b * n) :=
  c.map (liftLiteral hb)

/-- Lift a CNFModel CNF by embedding all clauses. -/
def liftCNF {n b : Nat} (hb : 0 < b) (phi : CNFModel.CNF n) : CNFModel.CNF (b * n) :=
  phi.map (liftClause hb)

/-- SearchRel adapter for a lifted CNFModel CNF. -/
def cnfModelLiftSearchRel {n b : Nat} (hb : 0 < b) (phi : CNFModel.CNF n) :
    ResoplusPDT.SearchRel (Basic.CNF.mk (b * n)) (ResoplusPDT.ParityClause (Basic.CNF.mk (b * n))) :=
  CNFModelParityBridge.cnfModelSearchRel (liftCNF hb phi)

end CNFModelLiftBridge
end CertifiedAffine
