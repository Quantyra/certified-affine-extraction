import Std
import PvNP.CNFData

namespace PvNP
namespace CNFDataSearchBridge

/-- A search output carries a witness (placeholder index). -/
structure Output where
  witness : Nat

/-- Define search correctness for CNFData via cnfSat (placeholder: sat iff true). -/
def SearchCorrect (F : CNFData.CNFData)
    (_a : CNFData.Assignment F) (_out : Output) : Prop :=
  CNFData.cnfSat F _a

/-- Bridge: DecisionTreeSearch.SearchCorrect can be instantiated from CNFData correctness. -/
def SearchCorrect_of_CNFData (F : CNFData.CNFData)
    (a : CNFData.Assignment F) (out : Output) : Prop :=
  SearchCorrect F a out

end CNFDataSearchBridge
end PvNP
