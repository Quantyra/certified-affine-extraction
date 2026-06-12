import Std

namespace CertifiedAffine
namespace DecisionTreeModel

/-!
Minimal decision tree model scaffold.
This will be extended to model canonical search problems for CNFs.
-/

inductive DT (n : Nat) : Type where
  | leaf : DT n
  | node : Fin n -> DT n -> DT n -> DT n

/-- Maximum query depth of a decision tree. -/
def depth {n : Nat} : DT n -> Nat
  | DT.leaf => 0
  | DT.node _ t f => Nat.succ (Nat.max (depth t) (depth f))

/-- Number of leaves in a decision tree. -/
def leaves {n : Nat} : DT n -> Nat
  | DT.leaf => 1
  | DT.node _ t f => leaves t + leaves f

end DecisionTreeModel
end CertifiedAffine
