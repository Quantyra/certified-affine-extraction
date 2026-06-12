import Std
import PvNP.BasicDefs
import PvNP.CNFModel

namespace PvNP
namespace CNFData

/-!
Wrapper for a CNF that carries explicit clause data without altering Basic.CNF.
-/

structure CNFData where
  base : Basic.CNF
  clauses : CNFModel.CNF base.vcount

abbrev Assignment (F : CNFData) := CNFModel.Assignment F.base.vcount

/-- CNF satisfaction for a CNFData instance. -/
def cnfSat (F : CNFData) (a : Assignment F) : Prop :=
  CNFModel.cnfSat a F.clauses

end CNFData
end PvNP
