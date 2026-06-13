import CertifiedAffine.TseitinCNFData
import Mathlib.Data.List.Sort

/-!
# Canonical Sort Invariance

This module isolates the project-generic permutation-invariance facts for the
canonical fingerprint sort.  The executable recognizer still uses the local
`sortByBool` implementation; the proofs below bridge that implementation to
mathlib's relation-based insertion sort and then use sorted-permutation
uniqueness.
-/

namespace CertifiedAffine
namespace TseitinCNFData

set_option linter.unusedVariables false

/-- Proposition-valued counterpart of `natListLexLE`. -/
def NatListLexLEProp : List Nat -> List Nat -> Prop
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => Or (x < y) (And (x = y) (NatListLexLEProp xs ys))

/-- Decidability for the proposition-valued lexicographic order. -/
def natListLexLEPropDecidable :
    (xs ys : List Nat) -> Decidable (NatListLexLEProp xs ys)
  | [], _ => isTrue trivial
  | _ :: _, [] => isFalse (fun h => h)
  | x :: xs, y :: ys => by
      by_cases hlt : x < y
      case pos =>
        exact isTrue (Or.inl hlt)
      case neg =>
        by_cases heq : x = y
        case pos =>
          cases natListLexLEPropDecidable xs ys with
          | isTrue htail =>
              exact isTrue (Or.inr (And.intro heq htail))
          | isFalse htail =>
              exact isFalse (fun h =>
                match h with
                | Or.inl hlt2 => hlt hlt2
                | Or.inr hrest =>
                    htail (by
                      cases hrest with
                      | intro _ hp => exact hp))
        case neg =>
          exact isFalse (fun h =>
            match h with
            | Or.inl hlt2 => hlt hlt2
            | Or.inr hrest => by
                cases hrest with
                | intro heq2 _ => exact heq heq2)

instance natListLexLEPropDecidableInst (xs ys : List Nat) :
    Decidable (NatListLexLEProp xs ys) :=
  natListLexLEPropDecidable xs ys

/-- The executable list-fingerprint comparator decides the proposition-valued lex order. -/
theorem natListLexLE_eq_decide_prop :
    forall xs ys : List Nat,
      natListLexLE xs ys = decide (NatListLexLEProp xs ys)
  | [], [] => by simp [natListLexLE, NatListLexLEProp]
  | [], y :: ys => by simp [natListLexLE, NatListLexLEProp]
  | x :: xs, [] => by simp [natListLexLE, NatListLexLEProp]
  | x :: xs, y :: ys => by
      rw [natListLexLE, natListLexLE_eq_decide_prop xs ys]
      by_cases hxy : x < y
      case pos =>
        simp [NatListLexLEProp, hxy]
      case neg =>
        by_cases hyx : y < x
        case pos =>
          have hne : Not (x = y) := by
            intro heq
            cases heq
            exact Nat.lt_irrefl x hyx
          simp [NatListLexLEProp, hxy, hyx, hne]
        case neg =>
          have hxy_eq : x = y :=
            Nat.le_antisymm (Nat.le_of_not_gt hyx) (Nat.le_of_not_gt hxy)
          subst y
          simp [NatListLexLEProp, hxy, hyx]

/-- `NatListLexLEProp` is total. -/
theorem natListLexLEProp_total : IsTotal (List Nat) NatListLexLEProp where
  total := by
    intro xs
    induction xs with
    | nil =>
        intro ys
        exact Or.inl trivial
    | cons x xs ih =>
        intro ys
        cases ys with
        | nil =>
            exact Or.inr trivial
        | cons y ys =>
            rcases Nat.lt_trichotomy x y with hlt | heq | hgt
            case inl =>
              exact Or.inl (Or.inl hlt)
            case inr.inl =>
              subst y
              cases ih ys with
              | inl hleft =>
                  exact Or.inl (Or.inr (And.intro rfl hleft))
              | inr hright =>
                  exact Or.inr (Or.inr (And.intro rfl hright))
            case inr.inr =>
              exact Or.inr (Or.inl hgt)

/-- `NatListLexLEProp` is transitive. -/
theorem natListLexLEProp_trans :
    forall {xs ys zs : List Nat},
      NatListLexLEProp xs ys ->
        NatListLexLEProp ys zs ->
          NatListLexLEProp xs zs
  | [], _, _, _, _ => trivial
  | _ :: _, [], _, hxy, _ => False.elim hxy
  | _ :: _, _ :: _, [], _, hyz => False.elim hyz
  | x :: xs, y :: ys, z :: zs, hxy, hyz => by
      cases hxy with
      | inl hxylt =>
          cases hyz with
          | inl hyzlt =>
              exact Or.inl (Nat.lt_trans hxylt hyzlt)
          | inr hyzrest =>
              cases hyzrest with
              | intro hyzeq _ =>
                  subst z
                  exact Or.inl hxylt
      | inr hxyrest =>
          cases hxyrest with
          | intro hxyeq hxys =>
              subst y
              cases hyz with
              | inl hxzlt =>
                  exact Or.inl hxzlt
              | inr hyzrest =>
                  cases hyzrest with
                  | intro hxzeq hyzs =>
                      subst z
                      exact Or.inr
                        (And.intro rfl (natListLexLEProp_trans hxys hyzs))

/-- `NatListLexLEProp` is antisymmetric. -/
theorem natListLexLEProp_antisymm :
    forall {xs ys : List Nat},
      NatListLexLEProp xs ys ->
        NatListLexLEProp ys xs ->
          xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, _, hyx => False.elim hyx
  | _ :: _, [], hxy, _ => False.elim hxy
  | x :: xs, y :: ys, hxy, hyx => by
      cases hxy with
      | inl hxylt =>
          cases hyx with
          | inl hyxlt =>
              exact False.elim (Nat.lt_asymm hxylt hyxlt)
          | inr hyxrest =>
              cases hyxrest with
              | intro _ _ =>
                  subst y
                  exact False.elim (Nat.lt_irrefl x hxylt)
      | inr hxyrest =>
          cases hxyrest with
          | intro hxyeq hxys =>
              subst y
              cases hyx with
              | inl hyxlt =>
                  exact False.elim (Nat.lt_irrefl x hyxlt)
              | inr hyxrest =>
                  cases hyxrest with
                  | intro _ hyxs =>
                      have htail : xs = ys :=
                        natListLexLEProp_antisymm hxys hyxs
                      subst ys
                      rfl

instance natListLexLEPropIsTotal : IsTotal (List Nat) NatListLexLEProp :=
  natListLexLEProp_total

instance natListLexLEPropIsTrans : IsTrans (List Nat) NatListLexLEProp where
  trans := fun _ _ _ => natListLexLEProp_trans

instance natListLexLEPropIsAntisymm : IsAntisymm (List Nat) NatListLexLEProp where
  antisymm := fun _ _ => natListLexLEProp_antisymm

/-- Boolean insertion into a decided relation agrees with mathlib ordered insertion. -/
theorem insertSortedBy_decide_eq_orderedInsert
    {alpha : Type} (r : alpha -> alpha -> Prop) [DecidableRel r]
    (x : alpha) :
    forall xs : List alpha,
      insertSortedBy (fun a b => decide (r a b)) x xs =
        List.orderedInsert r x xs
  | [] => rfl
  | y :: ys => by
      by_cases h : r x y
      case pos =>
        have hdec : decide (r x y) = true := by simp [h]
        simp [insertSortedBy, List.orderedInsert, h, hdec]
      case neg =>
        have hdec : decide (r x y) = false := by simp [h]
        simp [insertSortedBy, List.orderedInsert, h, hdec,
          insertSortedBy_decide_eq_orderedInsert r x ys]

/-- Boolean insertion sort over a decided relation agrees with mathlib insertion sort. -/
theorem sortByBool_decide_eq_insertionSort
    {alpha : Type} (r : alpha -> alpha -> Prop) [DecidableRel r] :
    forall xs : List alpha,
      sortByBool (fun a b => decide (r a b)) xs =
        List.insertionSort r xs
  | [] => rfl
  | x :: xs => by
      simp [sortByBool, List.insertionSort,
        sortByBool_decide_eq_insertionSort r xs,
        insertSortedBy_decide_eq_orderedInsert]

/--
If a boolean sort is driven by a total, transitive, antisymmetric decidable
relation, then it is invariant under `List.Perm`.
-/
theorem sortByBool_decide_eq_of_perm
    {alpha : Type} (r : alpha -> alpha -> Prop) [DecidableRel r]
    [IsTotal alpha r] [IsTrans alpha r] [IsAntisymm alpha r]
    {xs ys : List alpha} (hperm : List.Perm xs ys) :
    sortByBool (fun a b => decide (r a b)) xs =
      sortByBool (fun a b => decide (r a b)) ys := by
  rw [sortByBool_decide_eq_insertionSort r xs,
    sortByBool_decide_eq_insertionSort r ys]
  exact List.eq_of_perm_of_sorted
    ((List.perm_insertionSort r xs).trans
      (hperm.trans (List.perm_insertionSort r ys).symm))
    (List.sorted_insertionSort r xs)
    (List.sorted_insertionSort r ys)

/-- Canonical sorting of signed-literal atoms is invariant under permutation. -/
theorem sortNatFingerprintAtoms_eq_of_perm
    {xs ys : List Nat} (hperm : List.Perm xs ys) :
    sortNatFingerprintAtoms xs = sortNatFingerprintAtoms ys := by
  simpa [sortNatFingerprintAtoms, natFingerprintLE] using
    sortByBool_decide_eq_of_perm (r := fun a b : Nat => a <= b) hperm

/-- Canonical sorting of clause fingerprints is invariant under permutation. -/
theorem sortClauseFingerprints_eq_of_perm
    {xs ys : List (List Nat)} (hperm : List.Perm xs ys) :
    sortClauseFingerprints xs = sortClauseFingerprints ys := by
  have hfun :
      natListLexLE =
        (fun a b : List Nat => decide (NatListLexLEProp a b)) := by
    funext a b
    exact natListLexLE_eq_decide_prop a b
  unfold sortClauseFingerprints
  rw [hfun]
  exact sortByBool_decide_eq_of_perm (r := NatListLexLEProp) hperm

/-- Canonical sorting of finite variables by index is invariant under permutation. -/
theorem sortFinByVal_eq_of_perm
    {m : Nat} {xs ys : List (Fin m)} (hperm : List.Perm xs ys) :
    sortFinByVal xs = sortFinByVal ys := by
  unfold sortFinByVal
  haveI :
      IsTotal (Fin m) (fun a b : Fin m => a.val <= b.val) := {
    total := by
      intro a b
      exact Nat.le_total a.val b.val }
  haveI :
      IsTrans (Fin m) (fun a b : Fin m => a.val <= b.val) := {
    trans := by
      intro a b c hab hbc
      exact Nat.le_trans hab hbc }
  haveI :
      IsAntisymm (Fin m) (fun a b : Fin m => a.val <= b.val) := {
    antisymm := by
      intro a b hab hba
      exact Fin.ext (Nat.le_antisymm hab hba) }
  exact sortByBool_decide_eq_of_perm
    (r := fun a b : Fin m => a.val <= b.val) hperm

/-- Canonical support variables are invariant under literal permutation. -/
theorem canonicalClauseSupportVars_eq_of_perm
    {m : Nat} {c d : CNFModel.Clause m} (hperm : List.Perm c d) :
    canonicalClauseSupportVars c = canonicalClauseSupportVars d := by
  unfold canonicalClauseSupportVars
  rw [sortFinByVal_eq_of_perm (hperm.map (fun l => l.var))]

/-- Canonical support keys are invariant under literal permutation. -/
theorem canonicalClauseSupportKey_eq_of_perm
    {m : Nat} {c d : CNFModel.Clause m} (hperm : List.Perm c d) :
    canonicalClauseSupportKey c = canonicalClauseSupportKey d := by
  unfold canonicalClauseSupportKey
  rw [canonicalClauseSupportVars_eq_of_perm hperm]

/-- A clause fingerprint is invariant under literal permutation inside the clause. -/
theorem canonicalClauseFingerprint_eq_of_perm
    {m : Nat} {c d : CNFModel.Clause m} (hperm : List.Perm c d) :
    canonicalClauseFingerprint c = canonicalClauseFingerprint d := by
  unfold canonicalClauseFingerprint
  exact sortNatFingerprintAtoms_eq_of_perm (hperm.map canonicalLiteralAtom)

/-- A block fingerprint is invariant under clause permutation. -/
theorem canonicalBlockFingerprint_eq_of_perm
    {m : Nat} {f g : CNFModel.CNF m} (hperm : List.Perm f g) :
    canonicalBlockFingerprint f = canonicalBlockFingerprint g := by
  unfold canonicalBlockFingerprint
  exact sortClauseFingerprints_eq_of_perm (hperm.map canonicalClauseFingerprint)

/--
For a fixed candidate parity spec, canonical recognition is invariant under
clause permutation of the candidate block.
-/
theorem canonicalParityBlockRecognitionSignal_eq_of_block_perm
    {m : Nat}
    {f g : CNFModel.CNF m}
    (spec : ParityBlockSyntacticSpec m)
    (hperm : List.Perm f g) :
    canonicalParityBlockRecognitionSignal f spec =
      canonicalParityBlockRecognitionSignal g spec := by
  unfold canonicalParityBlockRecognitionSignal
  rw [canonicalBlockFingerprint_eq_of_perm hperm]

/--
The executable canonical parity-block recognizer accepts any clause
permutation of the target parity expansion.
-/
theorem canonicalParityBlockRecognitionSignal_of_perm
    {m : Nat}
    {blockCNF : CNFModel.CNF m}
    {spec : ParityBlockSyntacticSpec m}
    (hperm : List.Perm blockCNF spec.expandedCNF) :
    canonicalParityBlockRecognitionSignal blockCNF spec = true := by
  unfold canonicalParityBlockRecognitionSignal
  exact decide_eq_true (canonicalBlockFingerprint_eq_of_perm hperm)

end TseitinCNFData
end CertifiedAffine
