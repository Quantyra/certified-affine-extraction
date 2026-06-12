import Std
import Mathlib.Data.List.Join
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Dedup
import PvNP.BasicDefs
import PvNP.CNFData
import PvNP.CNFModel
import PvNP.CNFResolution
import PvNP.DecisionTreeSearch
import PvNP.TseitinModel
import PvNP.CNFModelParityBridge
import PvNP.CNFModelLiftBridge
import PvNP.ResoplusPDT

namespace PvNP
namespace TseitinCNFData

open Basic

/-- Parity of a list of booleans (xor fold). -/
def parity (bs : List Bool) : Bool :=
  bs.foldl (fun acc b => acc != b) false

theorem parity_foldl_acc (b : Bool) (xs : List Bool) :
    xs.foldl (fun acc x => acc != x) b = (b != parity xs) := by
  induction xs generalizing b with
  | nil =>
      cases b <;> rfl
  | cons x xs ih =>
      simp [List.foldl, parity]
      rw [ih (b := b != x), ih (b := x)]
      cases b <;> cases x <;> cases parity xs <;> rfl

theorem parity_append (xs ys : List Bool) :
    parity (xs ++ ys) = (parity xs != parity ys) := by
  unfold parity
  simpa [List.foldl_append, parity] using
    (parity_foldl_acc
      (b := List.foldl (fun acc x => acc != x) false xs)
      (xs := ys))

theorem parity_cons (b : Bool) (xs : List Bool) :
    parity (b :: xs) = (b != parity xs) := by
  unfold parity
  simp [List.foldl]
  exact parity_foldl_acc b xs

theorem parity_pair (b : Bool) : parity [b, b] = false := by
  cases b <;> rfl

theorem parity_perm {xs ys : List Bool} (hperm : List.Perm xs ys) :
    parity xs = parity ys := by
  have hfold :=
    (List.Perm.foldl_eq (f := fun acc x => acc != x) (p := hperm) false)
  simpa [parity] using hfold

theorem parity_bind_eq_parity_map_of_parity_eq
    {alpha : Type} (xs : List alpha) (f : alpha -> List Bool)
    (g : alpha -> Bool)
    (h : forall x : alpha, List.Mem x xs -> parity (f x) = g x) :
    parity (xs.bind f) = parity (xs.map g) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      have hx : parity (f x) = g x := h x (List.Mem.head _)
      have htail : forall y : alpha, List.Mem y xs -> parity (f y) = g y := by
        intro y hy
        exact h y (List.Mem.tail x hy)
      calc
        parity ((x :: xs).bind f)
            = parity (f x ++ xs.bind f) := by rfl
        _ = (parity (f x) != parity (xs.bind f)) :=
            parity_append (f x) (xs.bind f)
        _ = (g x != parity (xs.map g)) := by
            rw [hx, ih htail]
        _ = parity (g x :: xs.map g) := by
            exact (parity_cons (g x) (xs.map g)).symm
        _ = parity ((x :: xs).map g) := by rfl

private theorem bool_eq_of_beq_true {b c : Bool} :
    (b == c) = true -> b = c := by
  cases b <;> cases c <;> simp

theorem bool_beq_not_of_beq_true {b c : Bool} :
    (b == c) = true -> (b == !c) = false := by
  cases b <;> cases c <;> simp

/-- All boolean assignments of length n. -/
def allAssignments : Nat -> List (List Bool)
  | 0 => [[]]
  | Nat.succ k =>
      let rest := allAssignments k
      (rest.map (fun xs => false :: xs)) ++ (rest.map (fun xs => true :: xs))

theorem mem_allAssignments_of_length :
    forall {n : Nat} {bs : List Bool}, bs.length = n -> List.Mem bs (allAssignments n) := by
  intro n
  induction n with
  | zero =>
      intro bs hlen
      cases bs with
      | nil =>
          exact List.mem_singleton_self []
      | cons _ _ =>
          cases hlen
  | succ k ih =>
      intro bs hlen
      cases bs with
      | nil =>
          cases hlen
      | cons b bs =>
          have htail : bs.length = k := Nat.succ.inj hlen
          have hbs : List.Mem bs (allAssignments k) := ih htail
          cases b
          · have hmap :
                List.Mem (false :: bs)
                  ((allAssignments k).map (fun xs => false :: xs)) :=
              List.mem_map.2 (Exists.intro bs (And.intro hbs rfl))
            exact List.mem_append_left _ hmap
          · have hmap :
                List.Mem (true :: bs)
                  ((allAssignments k).map (fun xs => true :: xs)) :=
              List.mem_map.2 (Exists.intro bs (And.intro hbs rfl))
            exact List.mem_append_right _ hmap

/-- Build a clause forbidding a specific assignment on a list of variables. -/
def clauseForAssignment {m : Nat} : List (Fin m) -> List Bool -> CNFModel.Clause m
  | [], [] => []
  | v :: vs, b :: bs => { var := v, sign := (!b) } :: clauseForAssignment vs bs
  | _, _ => []

/-- A global assignment agrees with a local Boolean row on a vertex's variables. -/
def assignmentMatches {m : Nat} (a : CNFModel.Assignment m) :
    List (Fin m) -> List Bool -> Prop
  | [], [] => True
  | v :: vs, b :: bs => a v = b /\ assignmentMatches a vs bs
  | _, _ => False

theorem not_clauseSat_clauseForAssignment_of_assignmentMatches
    {m : Nat} (a : CNFModel.Assignment m) :
    forall vars bs,
      assignmentMatches a vars bs ->
      Not (CNFModel.clauseSat a (clauseForAssignment vars bs)) := by
  intro vars
  induction vars with
  | nil =>
      intro bs hmatch hsat
      cases bs with
      | nil =>
          rcases hsat with ⟨l, hmem, _⟩
          simp [clauseForAssignment] at hmem
      | cons _ _ =>
          cases hmatch
  | cons v vs ih =>
      intro bs hmatch hsat
      cases bs with
      | nil =>
          cases hmatch
      | cons b bs =>
          rcases hmatch with ⟨hv, htailmatch⟩
          rcases hsat with ⟨l, hmem, hlit⟩
          simp [clauseForAssignment] at hmem
          rcases hmem with hhead | htail
          · rw [hhead] at hlit
            cases b <;> simp [CNFModel.litEval, hv] at hlit
          · exact ih bs htailmatch ⟨l, htail, hlit⟩

/-- CNF clauses encoding a single vertex parity constraint from incident edges. -/
def clausesForVertex {m : Nat} (vars : List (Fin m)) (charge : Bool) :
    List (CNFModel.Clause m) :=
  (allAssignments vars.length).foldl
    (fun acc bs =>
      if parity bs == charge then
        acc
      else
        acc ++ [clauseForAssignment vars bs])
    []

private def clausesForVertexStep {m : Nat} (vars : List (Fin m)) (charge : Bool)
    (acc : List (CNFModel.Clause m)) (bs : List Bool) :
    List (CNFModel.Clause m) :=
  if parity bs == charge then
    acc
  else
    acc ++ [clauseForAssignment vars bs]

theorem clausesForVertex_length_of_length_three
    {m : Nat} {vars : List (Fin m)} {charge : Bool}
    (hlen : vars.length = 3) :
    (clausesForVertex vars charge).length = 4 := by
  cases charge <;> simp [clausesForVertex, hlen, allAssignments, parity]

/-- A four-variable parity constraint expands to eight ordinary CNF clauses. -/
theorem clausesForVertex_length_of_length_four
    {m : Nat} {vars : List (Fin m)} {charge : Bool}
    (hlen : vars.length = 4) :
    (clausesForVertex vars charge).length = 8 := by
  cases charge <;> simp [clausesForVertex, hlen, allAssignments, parity]

private theorem length_foldl_append_of_const_length
    {alpha beta : Type} (f : alpha -> List beta) (k : Nat) :
    forall (xs : List alpha) (acc : List beta),
      (forall x : alpha, List.Mem x xs -> (f x).length = k) ->
      (xs.foldl (fun acc x => acc ++ f x) acc).length =
        acc.length + xs.length * k := by
  intro xs
  induction xs with
  | nil =>
      intro acc _h
      simp
  | cons x xs ih =>
      intro acc h
      have hx : (f x).length = k := h x (List.Mem.head _)
      have htail : forall y : alpha, List.Mem y xs -> (f y).length = k := by
        intro y hy
        exact h y (List.Mem.tail x hy)
      calc
        ((x :: xs).foldl (fun acc x => acc ++ f x) acc).length
            = (xs.foldl (fun acc x => acc ++ f x) (acc ++ f x)).length := by
              rfl
        _ = (acc ++ f x).length + xs.length * k := ih (acc ++ f x) htail
        _ = acc.length + (x :: xs).length * k := by
              simp [List.length_append, hx, Nat.succ_mul, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm]

private theorem mem_foldl_clausesForVertexStep_of_mem_acc
    {m : Nat} (vars : List (Fin m)) (charge : Bool) :
    forall (rows : List (List Bool)) {acc : List (CNFModel.Clause m)}
      {c : CNFModel.Clause m},
      List.Mem c acc ->
      List.Mem c (rows.foldl (clausesForVertexStep vars charge) acc) := by
  intro rows
  induction rows with
  | nil =>
      intro acc c hmem
      simpa using hmem
  | cons row _rows ih =>
      intro acc c hmem
      apply ih
      by_cases hgood : parity row == charge
      · simp [clausesForVertexStep, hgood, hmem]
      · have hpersist :
            List.Mem c (acc ++ [clauseForAssignment vars row]) :=
          List.mem_append_left _ hmem
        simpa [clausesForVertexStep, hgood] using hpersist

private theorem mem_foldl_clausesForVertexStep_of_bad_row
    {m : Nat} (vars : List (Fin m)) (charge : Bool) :
    forall (rows : List (List Bool)) {acc : List (CNFModel.Clause m)}
      {bs : List Bool},
      List.Mem bs rows ->
      (parity bs == charge) = false ->
      List.Mem (clauseForAssignment vars bs)
        (rows.foldl (clausesForVertexStep vars charge) acc) := by
  intro rows
  induction rows with
  | nil =>
      intro acc bs hmem _hbad
      cases hmem
  | cons row rows ih =>
      intro acc bs hmem hbad
      cases hmem with
      | head =>
          apply mem_foldl_clausesForVertexStep_of_mem_acc vars charge rows
          have hmemStep :
              List.Mem (clauseForAssignment vars row)
                (acc ++ [clauseForAssignment vars row]) :=
            List.mem_append_right acc (List.mem_singleton_self _)
          simpa [clausesForVertexStep, hbad] using hmemStep
      | tail _ htail =>
          exact ih (acc := clausesForVertexStep vars charge acc row) htail hbad

theorem clauseForAssignment_mem_clausesForVertex_of_bad_row
    {m : Nat} {vars : List (Fin m)} {charge : Bool} {bs : List Bool}
    (hrow : List.Mem bs (allAssignments vars.length))
    (hbad : (parity bs == charge) = false) :
    List.Mem (clauseForAssignment vars bs) (clausesForVertex vars charge) := by
  unfold clausesForVertex
  exact mem_foldl_clausesForVertexStep_of_bad_row vars charge
    (allAssignments vars.length) hrow hbad

theorem clauseForAssignment_mem_clausesForVertex_of_bad_parity
    {m : Nat} {vars : List (Fin m)} {charge : Bool} {bs : List Bool}
    (hlen : bs.length = vars.length)
    (hbad : (parity bs == charge) = false) :
    List.Mem (clauseForAssignment vars bs) (clausesForVertex vars charge) := by
  exact clauseForAssignment_mem_clausesForVertex_of_bad_row
    (mem_allAssignments_of_length hlen) hbad

theorem not_cnfSat_clausesForVertex_of_bad_parity
    {m : Nat} (a : CNFModel.Assignment m) {vars : List (Fin m)}
    {charge : Bool} {bs : List Bool}
    (hlen : bs.length = vars.length)
    (hbad : (parity bs == charge) = false)
    (hmatch : assignmentMatches a vars bs) :
    Not (CNFModel.cnfSat a (clausesForVertex vars charge)) := by
  intro hsat
  have hmem :
      List.Mem (clauseForAssignment vars bs) (clausesForVertex vars charge) :=
    clauseForAssignment_mem_clausesForVertex_of_bad_parity hlen hbad
  exact (not_clauseSat_clauseForAssignment_of_assignmentMatches a vars bs hmatch)
    (hsat (clauseForAssignment vars bs) hmem)

/-- The local Boolean row induced by a global assignment on a list of variables. -/
def assignmentRow {m : Nat} (a : CNFModel.Assignment m) :
    List (Fin m) -> List Bool
  | [] => []
  | v :: vs => a v :: assignmentRow a vs

theorem assignmentRow_length {m : Nat} (a : CNFModel.Assignment m) :
    forall vars : List (Fin m), (assignmentRow a vars).length = vars.length := by
  intro vars
  induction vars with
  | nil =>
      rfl
  | cons _ _ ih =>
      simp [assignmentRow, ih]

theorem assignmentMatches_assignmentRow {m : Nat} (a : CNFModel.Assignment m) :
    forall vars : List (Fin m), assignmentMatches a vars (assignmentRow a vars) := by
  intro vars
  induction vars with
  | nil =>
      simp [assignmentMatches, assignmentRow]
  | cons _ _ ih =>
      simp [assignmentMatches, assignmentRow, ih]

theorem parity_eq_of_cnfSat_clausesForVertex
    {m : Nat} (a : CNFModel.Assignment m) {vars : List (Fin m)}
    {charge : Bool}
    (hsat : CNFModel.cnfSat a (clausesForVertex vars charge)) :
    (parity (assignmentRow a vars) == charge) = true := by
  cases hpar : (parity (assignmentRow a vars) == charge) with
  | false =>
      have hnot :
          Not (CNFModel.cnfSat a (clausesForVertex vars charge)) :=
        not_cnfSat_clausesForVertex_of_bad_parity
          a
          (vars := vars)
          (charge := charge)
          (bs := assignmentRow a vars)
          (assignmentRow_length a vars)
          hpar
          (assignmentMatches_assignmentRow a vars)
      exact False.elim (hnot hsat)
  | true =>
      rfl

theorem eq_assignmentRow_of_assignmentMatches
    {m : Nat} (a : CNFModel.Assignment m) :
    forall vars bs,
      assignmentMatches a vars bs ->
      bs = assignmentRow a vars := by
  intro vars
  induction vars with
  | nil =>
      intro bs hmatch
      cases bs with
      | nil =>
          rfl
      | cons _ _ =>
          cases hmatch
  | cons v vs ih =>
      intro bs hmatch
      cases bs with
      | nil =>
          cases hmatch
      | cons b bs =>
          rcases hmatch with ⟨hv, htail⟩
          have htailEq := ih bs htail
          simp [assignmentRow, hv, htailEq]

theorem clauseSat_clauseForAssignment_of_not_assignmentMatches
    {m : Nat} (a : CNFModel.Assignment m) :
    forall vars bs,
      bs.length = vars.length ->
      Not (assignmentMatches a vars bs) ->
      CNFModel.clauseSat a (clauseForAssignment vars bs) := by
  intro vars
  induction vars with
  | nil =>
      intro bs hlen hnot
      cases bs with
      | nil =>
          exact False.elim (hnot trivial)
      | cons _ _ =>
          cases hlen
  | cons v vs ih =>
      intro bs hlen hnot
      cases bs with
      | nil =>
          cases hlen
      | cons b bs =>
          have htailLen : bs.length = vs.length := Nat.succ.inj hlen
          by_cases hv : a v = b
          · have hnotTail : Not (assignmentMatches a vs bs) := by
              intro htail
              exact hnot ⟨hv, htail⟩
            rcases ih bs htailLen hnotTail with ⟨l, hmem, hlit⟩
            exact ⟨l, by simp [clauseForAssignment, hmem], hlit⟩
          · refine ⟨{ var := v, sign := (!b) }, ?_, ?_⟩
            · simp [clauseForAssignment]
            · cases b <;> cases ha : a v <;>
                simp [CNFModel.litEval, ha] at hv ⊢

theorem length_of_mem_allAssignments :
    forall {n : Nat} {bs : List Bool},
      List.Mem bs (allAssignments n) -> bs.length = n := by
  intro n
  induction n with
  | zero =>
      intro bs hmem
      cases hmem with
      | head =>
          rfl
      | tail _ htail =>
          cases htail
  | succ k ih =>
      intro bs hmem
      change List.Mem bs
        (((allAssignments k).map (fun xs => false :: xs)) ++
          ((allAssignments k).map (fun xs => true :: xs))) at hmem
      rcases List.mem_append.1 hmem with hleft | hright
      · rcases List.mem_map.1 hleft with ⟨tail, htail, hbs⟩
        rw [← hbs]
        simp [ih htail]
      · rcases List.mem_map.1 hright with ⟨tail, htail, hbs⟩
        rw [← hbs]
        simp [ih htail]

private theorem not_assignmentMatches_of_bad_parity
    {m : Nat} (a : CNFModel.Assignment m)
    {vars : List (Fin m)} {charge : Bool} {bs : List Bool}
    (hassign : (parity (assignmentRow a vars) == charge) = true)
    (hbad : (parity bs == charge) = false)
    (hmatch : assignmentMatches a vars bs) :
    False := by
  have hrow := eq_assignmentRow_of_assignmentMatches a vars bs hmatch
  rw [hrow] at hbad
  rw [hassign] at hbad
  cases hbad

private theorem cnfSat_foldl_clausesForVertexStep_of_good_assignment
    {m : Nat} (a : CNFModel.Assignment m)
    {vars : List (Fin m)} {charge : Bool}
    (hassign : (parity (assignmentRow a vars) == charge) = true) :
    forall (rows : List (List Bool)) (acc : List (CNFModel.Clause m)),
      (forall bs : List Bool, List.Mem bs rows -> bs.length = vars.length) ->
      CNFModel.cnfSat a acc ->
      CNFModel.cnfSat a
        (rows.foldl (clausesForVertexStep vars charge) acc) := by
  intro rows
  induction rows with
  | nil =>
      intro acc _hlen hacc
      simpa using hacc
  | cons row rows ih =>
      intro acc hlen hacc
      have htailLen :
          forall bs : List Bool,
            List.Mem bs rows -> bs.length = vars.length := by
        intro bs hbs
        exact hlen bs (List.Mem.tail row hbs)
      have hrowLen : row.length = vars.length := hlen row (List.Mem.head _)
      by_cases hbad : (parity row == charge) = false
      · apply ih (acc := clausesForVertexStep vars charge acc row)
          htailLen
        intro c hc
        have hc' :
            List.Mem c acc \/ c = clauseForAssignment vars row := by
          simpa [clausesForVertexStep, hbad] using hc
        rcases hc' with hmemAcc | hmemNew
        · exact hacc c hmemAcc
        · rw [hmemNew]
          exact
            clauseSat_clauseForAssignment_of_not_assignmentMatches
              a vars row hrowLen
              (by
                intro hmatch
                exact
                  not_assignmentMatches_of_bad_parity
                    a hassign hbad hmatch)
      · have hgood : (parity row == charge) = true := by
          cases hpar : (parity row == charge)
          · exact False.elim (hbad hpar)
          · rfl
        simpa [clausesForVertexStep, hgood] using
          ih (acc := acc) htailLen hacc

theorem cnfSat_clausesForVertex_of_good_parity
    {m : Nat} (a : CNFModel.Assignment m) {vars : List (Fin m)}
    {charge : Bool}
    (hassign : (parity (assignmentRow a vars) == charge) = true) :
    CNFModel.cnfSat a (clausesForVertex vars charge) := by
  unfold clausesForVertex
  exact
    cnfSat_foldl_clausesForVertexStep_of_good_assignment
      a hassign
      (allAssignments vars.length) []
      (by
        intro bs hmem
        exact length_of_mem_allAssignments hmem)
      (by
        intro c hmem
        cases hmem)

theorem cnfSat_clausesForVertex_iff_parity_eq
    {m : Nat} (a : CNFModel.Assignment m) {vars : List (Fin m)}
    {charge : Bool} :
    CNFModel.cnfSat a (clausesForVertex vars charge) <->
      (parity (assignmentRow a vars) == charge) = true := by
  exact
    Iff.intro
      (parity_eq_of_cnfSat_clausesForVertex a)
      (cnfSat_clausesForVertex_of_good_parity a)

theorem not_cnfSat_clausesForVertex_flip_charge_of_cnfSat
    {m : Nat} (a : CNFModel.Assignment m) {vars : List (Fin m)}
    {charge : Bool}
    (hsat : CNFModel.cnfSat a (clausesForVertex vars charge)) :
    Not (CNFModel.cnfSat a (clausesForVertex vars (!charge))) := by
  have hpar :
      (parity (assignmentRow a vars) == charge) = true :=
    parity_eq_of_cnfSat_clausesForVertex a hsat
  have hbad :
      (parity (assignmentRow a vars) == !charge) = false :=
    bool_beq_not_of_beq_true hpar
  exact
    not_cnfSat_clausesForVertex_of_bad_parity
      a
      (vars := vars)
      (charge := !charge)
      (bs := assignmentRow a vars)
      (assignmentRow_length a vars)
      hbad
      (assignmentMatches_assignmentRow a vars)

theorem cnfSat_clausesForVertex_false_charge_false
    {m : Nat} (vars : List (Fin m)) :
    CNFModel.cnfSat
      (fun _ => false : CNFModel.Assignment m)
      (clausesForVertex vars false) := by
  apply cnfSat_clausesForVertex_of_good_parity
  induction vars with
  | nil =>
      rfl
  | cons _ vars ih =>
      simp [assignmentRow, parity_cons]
      cases hpar :
          parity (assignmentRow
            (fun _ => false : CNFModel.Assignment m) vars) <;>
        simp [hpar] at ih ⊢

/-- Parity clause encoding a single vertex parity constraint from incident edges. -/
def parityClauseForVertex {m : Nat} (vars : List (Fin m)) (charge : Bool) :
    ResoplusPDT.ParityClause (Basic.CNF.mk m) :=
  { vars := vars, rhs := charge }

/-- Build Tseitin CNF clauses from incident lists (explicit parity CNF). -/
def tseitinClausesFromIncident (n m : Nat)
    (incident : Nat -> List (Fin m)) (charge : Nat -> Bool) :
    CNFModel.CNF m :=
  (List.range n).foldl
    (fun acc v => acc ++ clausesForVertex (incident v) (charge v))
    []

theorem tseitinClausesFromIncident_length_of_const_vertex_clause_count
    {n m k : Nat} {incident : Nat -> List (Fin m)}
    {charge : Nat -> Bool}
    (hcount : forall v : Nat, List.Mem v (List.range n) ->
      (clausesForVertex (incident v) (charge v)).length = k) :
    (tseitinClausesFromIncident n m incident charge).length = n * k := by
  unfold tseitinClausesFromIncident
  have hfold :=
    length_foldl_append_of_const_length
      (f := fun v => clausesForVertex (incident v) (charge v))
      (k := k)
      (xs := List.range n)
      (acc := ([] : List (CNFModel.Clause m)))
      hcount
  simpa using hfold

private theorem mem_foldl_append_of_mem_acc
    {alpha beta : Type} (f : alpha -> List beta) :
    forall (xs : List alpha) {acc : List beta} {c : beta},
      List.Mem c acc ->
      List.Mem c (xs.foldl (fun acc x => acc ++ f x) acc) := by
  intro xs
  induction xs with
  | nil =>
      intro acc c hmem
      simpa using hmem
  | cons x xs ih =>
      intro acc c hmem
      apply ih
      exact List.mem_append_left (f x) hmem

private theorem mem_foldl_append_of_mem_item
    {alpha beta : Type} (f : alpha -> List beta) :
    forall (xs : List alpha) {acc : List beta} {x : alpha} {c : beta},
      List.Mem x xs ->
      List.Mem c (f x) ->
      List.Mem c (xs.foldl (fun acc x => acc ++ f x) acc) := by
  intro xs
  induction xs with
  | nil =>
      intro acc x c hx _hc
      cases hx
  | cons y ys ih =>
      intro acc x c hx hc
      cases hx with
      | head =>
          apply mem_foldl_append_of_mem_acc f ys
          exact List.mem_append_right acc hc
      | tail _ htail =>
          exact ih (acc := acc ++ f y) htail hc

theorem mem_tseitinClausesFromIncident_of_mem_vertex
    {n m : Nat} {incident : Nat -> List (Fin m)} {charge : Nat -> Bool}
    {v : Nat} {c : CNFModel.Clause m}
    (hv : List.Mem v (List.range n))
    (hc : List.Mem c (clausesForVertex (incident v) (charge v))) :
    List.Mem c (tseitinClausesFromIncident n m incident charge) := by
  unfold tseitinClausesFromIncident
  exact mem_foldl_append_of_mem_item
    (fun v => clausesForVertex (incident v) (charge v))
    (List.range n) hv hc

theorem cnfSat_clausesForVertex_of_cnfSat_tseitinClausesFromIncident
    {n m : Nat} {incident : Nat -> List (Fin m)} {charge : Nat -> Bool}
    {a : CNFModel.Assignment m} {v : Nat}
    (hv : List.Mem v (List.range n))
    (hsat : CNFModel.cnfSat a (tseitinClausesFromIncident n m incident charge)) :
    CNFModel.cnfSat a (clausesForVertex (incident v) (charge v)) := by
  intro c hc
  exact hsat c (mem_tseitinClausesFromIncident_of_mem_vertex hv hc)

/-- Build Tseitin parity CNF formula from incident lists (direct parity clauses). -/
def tseitinParityFormulaFromIncident (n m : Nat)
    (incident : Nat -> List (Fin m)) (charge : Nat -> Bool) :
    ResoplusPDT.CNFFormula (Basic.CNF.mk m) :=
  (List.range n).map (fun v => parityClauseForVertex (incident v) (charge v))

/-- Placeholder CNFData encoding of Tseitin (explicit clauses to be refined). -/
def TseitinData (G : Basic.Graph) (c : Charge) : CNFData.CNFData :=
  let n := (Basic.Tseitin G c).vcount
  let clauses : CNFModel.CNF n :=
    -- Minimal non-empty encoding: a single unit clause when n > 0.
    match n with
    | 0 => []
    | Nat.succ k =>
        let fi : Fin (Nat.succ k) := Fin.mk 0 (Nat.succ_pos k)
        [[{ var := fi, sign := c fi }]]
  { base := Basic.Tseitin G c
    clauses := clauses }

/-- Tseitin CNFData from explicit incident lists (edge-based encoding). -/
def TseitinDataFromIncident (n m : Nat)
    (incident : Nat -> List (Fin m)) (charge : Nat -> Bool) : CNFData.CNFData :=
  { base := Basic.CNF.mk m
    clauses := tseitinClausesFromIncident n m incident charge }

/-- Enumerate Fin indices 0..m-1. -/
def allFin (m : Nat) : List (Fin m) :=
  List.pmap (fun i hi => (Fin.mk i hi : Fin m))
    (List.range m)
    (by
      intro i hi
      exact (List.mem_range).1 hi)

theorem mem_allFin {m : Nat} (i : Fin m) :
    List.Mem i (allFin m) := by
  unfold allFin
  refine List.mem_pmap.2 ?_
  exact Exists.intro i.val
    (Exists.intro ((List.mem_range).2 i.isLt) (Fin.ext rfl))

theorem allFin_nodup (m : Nat) : (allFin m).Nodup := by
  unfold allFin
  refine List.Nodup.pmap ?hf ?h
  case hf =>
    intro a _ha b _hb h
    exact congrArg Fin.val h
  case h =>
    exact List.nodup_range m

/-- Length of the local finite-index enumeration. -/
theorem allFin_length (m : Nat) : (allFin m).length = m := by
  unfold allFin
  simp

/--
The nth finite index enumerated by `allFin m` has value n.

This is the small locality bridge that lets later extraction arguments move
between finite-index scans and ordinary list positions without instance
enumeration.
-/
theorem allFin_get_val (m n : Nat) (hn : n < (allFin m).length) :
    ((List.get (allFin m) (Fin.mk n hn)) : Fin m).val = n := by
  unfold allFin
  rw [List.get_pmap]
  simp

/-- Mapping list lookup over all finite positions reconstructs the source list. -/
theorem allFin_map_get {alpha : Type} (xs : List alpha) :
    List.map (fun i : Fin xs.length => List.get xs i) (allFin xs.length) = xs := by
  apply List.ext_get
  case hl =>
    simp [allFin_length]
  case h =>
    intro n h1 h2
    rw [List.get_eq_getElem, List.getElem_map]
    have hidx : List.get (allFin xs.length)
        (Fin.mk n (by simpa [allFin_length] using h1)) = Fin.mk n h2 := by
      apply Fin.ext
      exact allFin_get_val xs.length n (by simpa [allFin_length] using h1)
    exact congrArg (fun i : Fin xs.length => List.get xs i) hidx

/-- Source-style graph for Tseitin CNF formulas: one variable per listed undirected edge. -/
structure StandardTseitinGraph where
  n : Nat
  edges : List TseitinModel.UEdge
  no_self_loops : TseitinModel.no_self_loops_pred edges
  endpoints_in_range : TseitinModel.endpoints_in_range_pred n edges
  one_variable_per_listed_edge : Prop

def canonicalUndirectedEdge (e : TseitinModel.UEdge) : TseitinModel.UEdge :=
  if e.u <= e.v then e else TseitinModel.UEdge.mk e.v e.u

def oneListedEdgePerUndirectedEdge
    (edges : List TseitinModel.UEdge) : Prop :=
  List.Nodup (edges.map canonicalUndirectedEdge)

theorem canonicalUndirectedEdge_reverse (e : TseitinModel.UEdge) :
    canonicalUndirectedEdge (TseitinModel.UEdge.mk e.v e.u) =
      canonicalUndirectedEdge e := by
  cases e with
  | mk u v =>
      simp [canonicalUndirectedEdge]
      by_cases huv : u <= v
      case pos =>
        simp [huv]
        by_cases hvu : v <= u
        case pos =>
          have heq : u = v := Nat.le_antisymm huv hvu
          subst v
          simp
        case neg =>
          simp [hvu]
      case neg =>
        have hvu : v <= u := Nat.le_of_not_ge huv
        simp [huv, hvu]

theorem not_oneListedEdgePerUndirectedEdge_of_reverse_pair
    {edges : List TseitinModel.UEdge} {e : TseitinModel.UEdge}
    (he : List.Mem e edges)
    (hrev : List.Mem (TseitinModel.UEdge.mk e.v e.u) edges)
    (hne : Not (e.u = e.v)) :
    Not (oneListedEdgePerUndirectedEdge edges) := by
  intro hnodup
  have hinj := List.inj_on_of_nodup_map
    (f := canonicalUndirectedEdge) hnodup
  have heqEdge : e = TseitinModel.UEdge.mk e.v e.u :=
    hinj he hrev (canonicalUndirectedEdge_reverse e).symm
  have hu : e.u = (TseitinModel.UEdge.mk e.v e.u).u :=
    congrArg TseitinModel.UEdge.u heqEdge
  have huv : e.u = e.v := by
    simpa using hu
  exact hne huv

theorem not_oneListedEdgePerUndirectedEdge_of_graphEncodingData_nonempty
    (enc : TseitinModel.GraphEncodingData) {e : TseitinModel.UEdge}
    (he : List.Mem e enc.edges) :
    Not (oneListedEdgePerUndirectedEdge enc.edges) := by
  exact not_oneListedEdgePerUndirectedEdge_of_reverse_pair
    he (enc.undirected e he) (enc.no_self_loops e he)

def standardTseitinGraphOfEncodingData
    (enc : TseitinModel.GraphEncodingData) :
    StandardTseitinGraph where
  n := enc.n
  edges := enc.edges
  no_self_loops := enc.no_self_loops
  endpoints_in_range := enc.endpoints_in_range
  one_variable_per_listed_edge := oneListedEdgePerUndirectedEdge enc.edges

/--
Build a source-style Tseitin graph directly from an edge list.  This is the
source-native constructor: it avoids the old `GraphEncodingData` convention
that stores both orientations of every undirected edge.
-/
def standardTseitinGraphOfEdgeList
    (n : Nat) (edges : List TseitinModel.UEdge)
    (hNoSelf : TseitinModel.no_self_loops_pred edges)
    (hEndpoints : TseitinModel.endpoints_in_range_pred n edges) :
    StandardTseitinGraph where
  n := n
  edges := edges
  no_self_loops := hNoSelf
  endpoints_in_range := hEndpoints
  one_variable_per_listed_edge := oneListedEdgePerUndirectedEdge edges

/-- Source-native four-cycle edge list: four undirected edge variables, not eight orientations. -/
def standardFourCycleEdges : List TseitinModel.UEdge :=
  [ TseitinModel.UEdge.mk 0 1
  , TseitinModel.UEdge.mk 1 2
  , TseitinModel.UEdge.mk 2 3
  , TseitinModel.UEdge.mk 3 0 ]

theorem standardFourCycle_noSelfLoops :
    TseitinModel.no_self_loops_pred standardFourCycleEdges := by
  intro e he
  simp [standardFourCycleEdges] at he
  rcases he with h | h | h | h
  case inl => subst e; decide
  case inr.inl => subst e; decide
  case inr.inr.inl => subst e; decide
  case inr.inr.inr => subst e; decide

theorem standardFourCycle_endpointsInRange :
    TseitinModel.endpoints_in_range_pred 4 standardFourCycleEdges := by
  intro e he
  simp [standardFourCycleEdges] at he
  rcases he with h | h | h | h
  case inl => subst e; decide
  case inr.inl => subst e; decide
  case inr.inr.inl => subst e; decide
  case inr.inr.inr => subst e; decide

/-- Finite source-native smoke graph for the standard Tseitin edge convention. -/
def standardFourCycleGraph : StandardTseitinGraph :=
  standardTseitinGraphOfEdgeList 4 standardFourCycleEdges
    standardFourCycle_noSelfLoops standardFourCycle_endpointsInRange

/-- Concrete odd charge for the source-native standard four-cycle. -/
def standardFourCycleCharge (v : Nat) : Bool :=
  v = 0

theorem standardFourCycle_oneListedEdgePerUndirectedEdge :
    oneListedEdgePerUndirectedEdge standardFourCycleEdges := by
  simp [oneListedEdgePerUndirectedEdge, standardFourCycleEdges,
    canonicalUndirectedEdge]

/-- Edge at a standard Tseitin source index. -/
def standardEdgeAt (G : StandardTseitinGraph) (i : Fin G.edges.length) :
    TseitinModel.UEdge :=
  G.edges.get i

/-- Incident edge-variable indices for a standard one-variable-per-edge Tseitin source graph. -/
def standardIncidentIndices (G : StandardTseitinGraph) (v : Nat) :
    List (Fin G.edges.length) :=
  (allFin G.edges.length).filter
    (fun i => TseitinModel.UEdge.incident (standardEdgeAt G i) v)

theorem standardIncidentIndex_mem_of_incident
    {G : StandardTseitinGraph} {i : Fin G.edges.length} {v : Nat}
    (hinc : TseitinModel.UEdge.incident (standardEdgeAt G i) v = true) :
    List.Mem i (standardIncidentIndices G v) := by
  unfold standardIncidentIndices
  apply List.mem_filter.2
  exact And.intro (mem_allFin i) hinc

theorem standardIncidentIndex_mem_left
    {G : StandardTseitinGraph} (i : Fin G.edges.length) :
    List.Mem i (standardIncidentIndices G (standardEdgeAt G i).u) := by
  apply standardIncidentIndex_mem_of_incident
  simp [TseitinModel.UEdge.incident]

theorem standardIncidentIndex_mem_right
    {G : StandardTseitinGraph} (i : Fin G.edges.length) :
    List.Mem i (standardIncidentIndices G (standardEdgeAt G i).v) := by
  apply standardIncidentIndex_mem_of_incident
  simp [TseitinModel.UEdge.incident]

theorem standardEdgeAt_mem_edges
    (G : StandardTseitinGraph) (i : Fin G.edges.length) :
    List.Mem (standardEdgeAt G i) G.edges := by
  unfold standardEdgeAt
  change List.Mem (G.edges.get (Fin.mk i.val i.2)) G.edges
  exact List.get_mem G.edges i.val i.2

theorem standardIncidentIndex_mem_iff_incident
    {G : StandardTseitinGraph} {i : Fin G.edges.length} {v : Nat} :
    List.Mem i (standardIncidentIndices G v) <->
      TseitinModel.UEdge.incident (standardEdgeAt G i) v = true := by
  constructor
  case mp =>
    intro hmem
    exact (List.mem_filter.1 hmem).2
  case mpr =>
    intro hinc
    exact standardIncidentIndex_mem_of_incident hinc

theorem standardIncidentIndex_contains_iff_incident
    {G : StandardTseitinGraph} {i : Fin G.edges.length} {v : Nat} :
    (standardIncidentIndices G v).contains i = true <->
      TseitinModel.UEdge.incident (standardEdgeAt G i) v = true := by
  constructor
  case mp =>
    intro hcontains
    exact (standardIncidentIndex_mem_iff_incident
      (G := G) (i := i) (v := v)).1
      (List.elem_iff.mp (by simpa [List.contains] using hcontains))
  case mpr =>
    intro hinc
    have hmem := (standardIncidentIndex_mem_iff_incident
      (G := G) (i := i) (v := v)).2 hinc
    simpa [List.contains] using (List.elem_iff.mpr hmem)

theorem standardEdgeIncidentVertexCount_eq_two
    (G : StandardTseitinGraph) (i : Fin G.edges.length) :
    (List.range G.n).countP
      (fun v => TseitinModel.UEdge.incident (standardEdgeAt G i) v) = 2 := by
  have hmem : List.Mem (standardEdgeAt G i) G.edges :=
    standardEdgeAt_mem_edges G i
  have hrange :
      And ((standardEdgeAt G i).u < G.n) ((standardEdgeAt G i).v < G.n) :=
    G.endpoints_in_range (standardEdgeAt G i) hmem
  have hnoloop : Not ((standardEdgeAt G i).u = (standardEdgeAt G i).v) :=
    G.no_self_loops (standardEdgeAt G i) hmem
  have hinc := TseitinModel.incident_count_in_range_eq_two
    G.n (standardEdgeAt G i) hrange hnoloop
  have hcount :
      TseitinModel.incident_count_in_range G.n (standardEdgeAt G i) =
        (List.range G.n).countP
          (fun v => TseitinModel.UEdge.incident (standardEdgeAt G i) v) := by
    simp [TseitinModel.incident_count_in_range,
      TseitinModel.foldl_indicator_eq_countP]
  exact hcount.symm.trans hinc

theorem standardIncidentIndexVertexContainsCount_eq_two
    (G : StandardTseitinGraph) (i : Fin G.edges.length) :
    (List.range G.n).countP
      (fun v => (standardIncidentIndices G v).contains i) = 2 := by
  have hcongr := List.countP_congr
    (l := List.range G.n)
    (p := fun v => (standardIncidentIndices G v).contains i)
    (q := fun v => TseitinModel.UEdge.incident (standardEdgeAt G i) v)
    (by
      intro v _hv
      exact standardIncidentIndex_contains_iff_incident
        (G := G) (i := i) (v := v))
  exact hcongr.trans (standardEdgeIncidentVertexCount_eq_two G i)

theorem standardIncidentIndices_nodup
    (G : StandardTseitinGraph) (v : Nat) :
    (standardIncidentIndices G v).Nodup := by
  unfold standardIncidentIndices
  exact (allFin_nodup G.edges.length).filter _

theorem sum_count_eq_countP_contains_of_nodup
    {alpha beta : Type} [DecidableEq beta]
    (xs : List alpha) (f : alpha -> List beta) (b : beta)
    (hnodup : forall x, (f x).Nodup) :
    Nat.sum (xs.map (fun x => (f x).count b)) =
      xs.countP (fun x => (f x).contains b) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.countP_cons]
      by_cases hmem : List.Mem b (f x)
      case pos =>
        simp [List.count_eq_of_nodup (hnodup x), hmem, ih, Nat.add_comm]
      case neg =>
        simp [List.count_eq_of_nodup (hnodup x), hmem, ih, Nat.add_comm]

theorem standardIncidentIndexFlattenedCount_eq_two
    (G : StandardTseitinGraph) (i : Fin G.edges.length) :
    ((List.range G.n).bind (standardIncidentIndices G)).count i = 2 := by
  rw [List.count_bind']
  have hsum := sum_count_eq_countP_contains_of_nodup
    (xs := List.range G.n)
    (f := standardIncidentIndices G)
    (b := i)
    (hnodup := fun v => standardIncidentIndices_nodup G v)
  exact hsum.trans (standardIncidentIndexVertexContainsCount_eq_two G i)

theorem count_bind_duplicate_pair
    {alpha : Type} [BEq alpha]
    (xs : List alpha) (x : alpha) :
    (xs.bind (fun y => [y, y])).count x = 2 * xs.count x := by
  induction xs with
  | nil =>
      rfl
  | cons y ys ih =>
      by_cases h : (y == x) = true
      case pos =>
        simp [List.count_append, List.count_cons, ih, h, Nat.mul_add,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        omega
      case neg =>
        simp [List.count_append, List.count_cons, ih, h, Nat.mul_add,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem allFin_count_eq_one {m : Nat} (i : Fin m) :
    (allFin m).count i = 1 := by
  exact List.count_eq_one_of_mem (allFin_nodup m) (mem_allFin i)

theorem allFin_bind_duplicatePair_count_eq_two {m : Nat} (i : Fin m) :
    ((allFin m).bind (fun j => [j, j])).count i = 2 := by
  calc
    ((allFin m).bind (fun j => [j, j])).count i =
        2 * (allFin m).count i :=
      count_bind_duplicate_pair (allFin m) i
    _ = 2 := by
      simp [allFin_count_eq_one i]

theorem standardIncidentIndexDoubleCountPerm
    (G : StandardTseitinGraph) :
    List.Perm
      ((List.range G.n).bind (standardIncidentIndices G))
      ((allFin G.edges.length).bind (fun i => [i, i])) := by
  apply List.perm_iff_count.2
  intro i
  exact (standardIncidentIndexFlattenedCount_eq_two G i).trans
    (allFin_bind_duplicatePair_count_eq_two i).symm

theorem assignmentRow_eq_map {m : Nat} (a : CNFModel.Assignment m) :
    forall vars : List (Fin m), assignmentRow a vars = vars.map a := by
  intro vars
  induction vars with
  | nil =>
      rfl
  | cons _ _ ih =>
      simp [assignmentRow, ih]

theorem resoplusParity_eq_parity (xs : List Bool) :
    ResoplusPDT.parity xs = parity xs := by
  simp [ResoplusPDT.parity, parity, Bool.xor]

theorem clauseSat_parityClauseForVertex_iff_parity_eq
    {m : Nat} (a : CNFModel.Assignment m) {vars : List (Fin m)}
    {charge : Bool} :
    ResoplusPDT.ClauseSat
        (F := Basic.CNF.mk m) a (parityClauseForVertex vars charge) <->
      (parity (assignmentRow a vars) == charge) = true := by
  rw [assignmentRow_eq_map a vars]
  simp [ResoplusPDT.ClauseSat, ResoplusPDT.clauseEval,
    parityClauseForVertex, resoplusParity_eq_parity]

theorem clauseSat_parityClauseForVertex_iff_cnfSat_clausesForVertex
    {m : Nat} (a : CNFModel.Assignment m) {vars : List (Fin m)}
    {charge : Bool} :
    ResoplusPDT.ClauseSat
        (F := Basic.CNF.mk m) a (parityClauseForVertex vars charge) <->
      CNFModel.cnfSat a (clausesForVertex vars charge) := by
  exact
    Iff.trans
      (clauseSat_parityClauseForVertex_iff_parity_eq a)
      (Iff.symm (cnfSat_clausesForVertex_iff_parity_eq a))

theorem parityClauseForVertex_mem_tseitinParityFormulaFromIncident
    {n m : Nat} {incident : Nat -> List (Fin m)} {charge : Nat -> Bool}
    {v : Nat} (hv : List.Mem v (List.range n)) :
    List.Mem (parityClauseForVertex (incident v) (charge v))
      (tseitinParityFormulaFromIncident n m incident charge) := by
  unfold tseitinParityFormulaFromIncident
  exact List.mem_map.2 (Exists.intro v (And.intro hv rfl))

/-- Standard source-style Tseitin CNF: variables are exactly the listed undirected edges. -/
def StandardTseitinCNFFormula (G : StandardTseitinGraph)
    (charge : Nat -> Bool) :
    CNFModel.CNF G.edges.length :=
  tseitinClausesFromIncident G.n G.edges.length
    (standardIncidentIndices G) charge

/-- A standard Tseitin vertex parity equation holds under an assignment. -/
def standardVertexParitySatisfied (G : StandardTseitinGraph)
    (charge : Nat -> Bool) (a : CNFModel.Assignment G.edges.length)
    (v : Nat) : Prop :=
  (parity (assignmentRow a (standardIncidentIndices G v)) == charge v) = true

theorem standardVertexParitySatisfied_of_cnfSat_standardFormula
    {G : StandardTseitinGraph} {charge : Nat -> Bool}
    {a : CNFModel.Assignment G.edges.length} {v : Nat}
    (hv : List.Mem v (List.range G.n))
    (hsat : CNFModel.cnfSat a (StandardTseitinCNFFormula G charge)) :
    standardVertexParitySatisfied G charge a v := by
  unfold standardVertexParitySatisfied
  exact parity_eq_of_cnfSat_clausesForVertex a
    (cnfSat_clausesForVertex_of_cnfSat_tseitinClausesFromIncident
      (n := G.n)
      (m := G.edges.length)
      (incident := standardIncidentIndices G)
      (charge := charge)
      (a := a)
      hv
      hsat)

def standardLocalTseitinAxiomCompatible
    (G : StandardTseitinGraph) (charge : Nat -> Bool) : Prop :=
  forall (a : CNFModel.Assignment G.edges.length) (v : Nat),
    List.Mem v (List.range G.n) ->
      List.Mem
        (parityClauseForVertex (standardIncidentIndices G v) (charge v))
        (tseitinParityFormulaFromIncident G.n G.edges.length
          (standardIncidentIndices G) charge) /\
      (ResoplusPDT.ClauseSat
          (F := Basic.CNF.mk G.edges.length) a
          (parityClauseForVertex (standardIncidentIndices G v) (charge v)) <->
        CNFModel.cnfSat a
          (clausesForVertex (standardIncidentIndices G v) (charge v)))

theorem standardLocalTseitinAxiomCompatible_of_graph
    (G : StandardTseitinGraph) (charge : Nat -> Bool) :
    standardLocalTseitinAxiomCompatible G charge := by
  intro a v hv
  exact And.intro
    (parityClauseForVertex_mem_tseitinParityFormulaFromIncident hv)
    (clauseSat_parityClauseForVertex_iff_cnfSat_clausesForVertex a)

def standardLocalParityTargetSensitive
    (G : StandardTseitinGraph) (charge : Nat -> Bool) : Prop :=
  forall (a : CNFModel.Assignment G.edges.length) (v : Nat),
    List.Mem v (List.range G.n) ->
    CNFModel.cnfSat a (StandardTseitinCNFFormula G charge) ->
    Not (CNFModel.cnfSat a
      (clausesForVertex (standardIncidentIndices G v) (!(charge v))))

theorem standardLocalParityTargetSensitive_of_graph
    (G : StandardTseitinGraph) (charge : Nat -> Bool) :
    standardLocalParityTargetSensitive G charge := by
  intro a v hv hsat
  have hpar :
      (parity (assignmentRow a (standardIncidentIndices G v)) == charge v) =
        true :=
    standardVertexParitySatisfied_of_cnfSat_standardFormula
      (G := G) (charge := charge) (a := a) (v := v) hv hsat
  have hbad :
      (parity (assignmentRow a (standardIncidentIndices G v)) ==
        !(charge v)) = false :=
    bool_beq_not_of_beq_true hpar
  exact
    not_cnfSat_clausesForVertex_of_bad_parity
      a
      (vars := standardIncidentIndices G v)
      (charge := !(charge v))
      (bs := assignmentRow a (standardIncidentIndices G v))
      (assignmentRow_length a (standardIncidentIndices G v))
      hbad
      (assignmentMatches_assignmentRow a (standardIncidentIndices G v))

/-- XOR of all standard vertex incident rows under a global edge assignment. -/
def standardIncidentParity (G : StandardTseitinGraph)
    (a : CNFModel.Assignment G.edges.length) : Bool :=
  parity ((List.range G.n).bind
    (fun v => assignmentRow a (standardIncidentIndices G v)))

/-- XOR of all vertex charges in the standard source graph. -/
def standardChargeParity (G : StandardTseitinGraph)
    (charge : Nat -> Bool) : Bool :=
  parity ((List.range G.n).map charge)

/-- Flip the Tseitin charge at one named vertex. -/
def standardFlipChargeAt (charge : Nat -> Bool) (v : Nat) : Nat -> Bool :=
  fun u => if u = v then !charge u else charge u

/-- Even total charge for the standard source graph. -/
def standardEvenTotalCharge (G : StandardTseitinGraph)
    (charge : Nat -> Bool) : Prop :=
  standardChargeParity G charge = false

theorem parity_map_const_false {alpha : Type} (xs : List alpha) :
    parity (xs.map (fun _ => false)) = false := by
  induction xs with
  | nil =>
      rfl
  | cons _ xs ih =>
      change parity (false :: xs.map (fun _ => false)) = false
      rw [parity_cons, ih]
      rfl

theorem standardEvenTotalCharge_false (G : StandardTseitinGraph) :
    standardEvenTotalCharge G (fun _ => false) := by
  unfold standardEvenTotalCharge standardChargeParity
  exact parity_map_const_false (List.range G.n)

/--
All local standard vertex equations fold to equality between the XOR of all
incident edge appearances and the XOR of all vertex charges.
-/
def standardVertexEquationsFoldToCharge
    (G : StandardTseitinGraph) (charge : Nat -> Bool) : Prop :=
  forall a : CNFModel.Assignment G.edges.length,
    (forall v : Nat, List.Mem v (List.range G.n) ->
      standardVertexParitySatisfied G charge a v) ->
    standardIncidentParity G a = standardChargeParity G charge

theorem standardVertexEquationsFoldToCharge_of_vertex_parities
    (G : StandardTseitinGraph) (charge : Nat -> Bool) :
    standardVertexEquationsFoldToCharge G charge := by
  intro a hvertices
  unfold standardIncidentParity standardChargeParity
  exact parity_bind_eq_parity_map_of_parity_eq
    (List.range G.n)
    (fun v => assignmentRow a (standardIncidentIndices G v))
    charge
    (by
      intro v hv
      exact bool_eq_of_beq_true (hvertices v hv))

/--
The source-side cancellation premise: after all vertex incident rows are XORed,
each listed undirected edge contributes twice and cancels.
-/
def standardIncidentParityCancels (G : StandardTseitinGraph) : Prop :=
  forall a : CNFModel.Assignment G.edges.length,
    standardIncidentParity G a = false

/--
Exact double-counting source-normalization obligation.  The vertex-grouped
incident rows must be a permutation of one duplicate pair for each edge
variable.
-/
def standardIncidentRowsDoubleCount (G : StandardTseitinGraph) : Prop :=
  forall a : CNFModel.Assignment G.edges.length,
    List.Perm
      ((List.range G.n).bind
        (fun v => assignmentRow a (standardIncidentIndices G v)))
      ((allFin G.edges.length).bind (fun i => [a i, a i]))

theorem standardIncidentRowsDoubleCount_of_graph
    (G : StandardTseitinGraph) :
    standardIncidentRowsDoubleCount G := by
  intro a
  have hidx := standardIncidentIndexDoubleCountPerm G
  simpa [List.map_bind, assignmentRow_eq_map] using hidx.map a

theorem parity_bind_pairs_false {m : Nat}
    (a : CNFModel.Assignment m) (idxs : List (Fin m)) :
    parity (idxs.bind (fun i => [a i, a i])) = false := by
  induction idxs with
  | nil =>
      rfl
  | cons i idxs ih =>
      calc
        parity ((i :: idxs).bind (fun i => [a i, a i]))
            = parity ([a i, a i] ++ idxs.bind (fun i => [a i, a i])) := by rfl
        _ = (parity [a i, a i] != parity (idxs.bind (fun i => [a i, a i]))) :=
            parity_append [a i, a i] (idxs.bind (fun i => [a i, a i]))
        _ = false := by
            simp [parity_pair, ih]

theorem standardIncidentParityCancels_of_doubleCount
    {G : StandardTseitinGraph}
    (hdouble : standardIncidentRowsDoubleCount G) :
    standardIncidentParityCancels G := by
  intro a
  unfold standardIncidentParity
  calc
    parity ((List.range G.n).bind
        (fun v => assignmentRow a (standardIncidentIndices G v)))
        = parity ((allFin G.edges.length).bind (fun i => [a i, a i])) :=
      parity_perm (hdouble a)
    _ = false := parity_bind_pairs_false a (allFin G.edges.length)

theorem standardIncidentParityCancels_of_graph
    (G : StandardTseitinGraph) :
    standardIncidentParityCancels G :=
  standardIncidentParityCancels_of_doubleCount
    (standardIncidentRowsDoubleCount_of_graph G)

/-- Odd total charge for the standard source graph. -/
def standardOddTotalCharge (G : StandardTseitinGraph)
    (charge : Nat -> Bool) : Prop :=
  standardChargeParity G charge = true

/-- Canonical local odd charge: exactly vertex zero is charged. -/
def standardSingletonZeroCharge (v : Nat) : Bool :=
  v = 0

theorem standardFlipChargeAt_singletonZero_zero_eq_false :
    standardFlipChargeAt standardSingletonZeroCharge 0 = fun _ => false := by
  funext u
  by_cases h : u = 0
  · simp [standardFlipChargeAt, standardSingletonZeroCharge, h]
  · simp [standardFlipChargeAt, standardSingletonZeroCharge, h]

theorem standardEvenTotalCharge_flip_singletonZero_zero
    (G : StandardTseitinGraph) :
    standardEvenTotalCharge G
      (standardFlipChargeAt standardSingletonZeroCharge 0) := by
  rw [standardFlipChargeAt_singletonZero_zero_eq_false]
  exact standardEvenTotalCharge_false G

private theorem cnfSat_foldl_append_of_sat_items
    {alpha : Type} {m : Nat} (a : CNFModel.Assignment m)
    (f : alpha -> List (CNFModel.Clause m)) :
    forall (xs : List alpha) (acc : List (CNFModel.Clause m)),
      CNFModel.cnfSat a acc ->
      (forall x : alpha, List.Mem x xs -> CNFModel.cnfSat a (f x)) ->
      CNFModel.cnfSat a (xs.foldl (fun acc x => acc ++ f x) acc) := by
  intro xs
  induction xs with
  | nil =>
      intro acc hacc _hitems
      simpa using hacc
  | cons x xs ih =>
      intro acc hacc hitems
      apply ih (acc := acc ++ f x)
      · intro c hc
        rcases List.mem_append.1 hc with hmemAcc | hmemItem
        · exact hacc c hmemAcc
        · exact hitems x (List.Mem.head _) c hmemItem
      · intro y hy
        exact hitems y (List.Mem.tail x hy)

theorem cnfSat_standardTseitinCNFFormula_false_charge_false
    (G : StandardTseitinGraph) :
    CNFModel.cnfSat
      (fun _ => false : CNFModel.Assignment G.edges.length)
      (StandardTseitinCNFFormula G (fun _ => false)) := by
  unfold StandardTseitinCNFFormula tseitinClausesFromIncident
  apply cnfSat_foldl_append_of_sat_items
  · intro c hmem
    cases hmem
  · intro v _hv
    exact cnfSat_clausesForVertex_false_charge_false
      (standardIncidentIndices G v)

theorem exists_cnfSat_standardTseitinCNFFormula_false_charge_false
    (G : StandardTseitinGraph) :
    Exists fun a : CNFModel.Assignment G.edges.length =>
      CNFModel.cnfSat a
        (StandardTseitinCNFFormula G (fun _ => false)) := by
  exact
    Exists.intro
      (fun _ => false : CNFModel.Assignment G.edges.length)
      (cnfSat_standardTseitinCNFFormula_false_charge_false G)

theorem exists_cnfSat_standardTseitinCNFFormula_flip_singletonZero_zero
    (G : StandardTseitinGraph) :
    Exists fun a : CNFModel.Assignment G.edges.length =>
      CNFModel.cnfSat a
        (StandardTseitinCNFFormula G
          (standardFlipChargeAt standardSingletonZeroCharge 0)) := by
  rw [standardFlipChargeAt_singletonZero_zero_eq_false]
  exact exists_cnfSat_standardTseitinCNFFormula_false_charge_false G

theorem cnfSat_of_clause_subset
    {m : Nat} {a : CNFModel.Assignment m}
    {sub full : CNFModel.CNF m}
    (hsat : CNFModel.cnfSat a full)
    (hsubset :
      forall c : CNFModel.Clause m,
        List.Mem c sub -> List.Mem c full) :
    CNFModel.cnfSat a sub := by
  intro c hc
  exact hsat c (hsubset c hc)

theorem exists_cnfSat_of_clause_subset
    {m : Nat} {sub full : CNFModel.CNF m}
    (hsat : Exists fun a : CNFModel.Assignment m =>
      CNFModel.cnfSat a full)
    (hsubset :
      forall c : CNFModel.Clause m,
        List.Mem c sub -> List.Mem c full) :
    Exists fun a : CNFModel.Assignment m =>
      CNFModel.cnfSat a sub := by
  rcases hsat with ⟨a, ha⟩
  exact ⟨a, cnfSat_of_clause_subset ha hsubset⟩

theorem standardSingletonZeroCharge_parity_range_succ (n : Nat) :
    parity ((List.range (Nat.succ n)).map standardSingletonZeroCharge) = true := by
  induction n with
  | zero =>
      native_decide
  | succ n ih =>
      calc
        parity ((List.range (Nat.succ (Nat.succ n))).map
            standardSingletonZeroCharge)
            = parity (((List.range (n + 1)).map
                standardSingletonZeroCharge) ++
                [standardSingletonZeroCharge (n + 1)]) := by
              simp [List.range_succ, List.map_append]
        _ = (parity ((List.range (n + 1)).map standardSingletonZeroCharge) !=
              parity [standardSingletonZeroCharge (n + 1)]) :=
            parity_append
              ((List.range (n + 1)).map standardSingletonZeroCharge)
              [standardSingletonZeroCharge (n + 1)]
        _ = true := by
            have ih' :
                parity ((List.range (n + 1)).map standardSingletonZeroCharge) =
                  true := by
              simpa [Nat.succ_eq_add_one] using ih
            have hlast :
                parity [standardSingletonZeroCharge (n + 1)] = false := by
              simp [standardSingletonZeroCharge, parity]
            simp [ih', hlast]

theorem standardOddTotalCharge_singletonZero_of_pos
    {G : StandardTseitinGraph} (hpos : 0 < G.n) :
    standardOddTotalCharge G standardSingletonZeroCharge := by
  cases hn : G.n with
  | zero =>
      omega
  | succ n =>
      simpa [standardOddTotalCharge, standardChargeParity, hn] using
        standardSingletonZeroCharge_parity_range_succ n

/-- Source-side degree in the one-variable-per-undirected-edge convention. -/
def standardVertexDegree (G : StandardTseitinGraph) (v : Nat) : Nat :=
  (standardIncidentIndices G v).length

/-- The BSW source packet uses 3-regular graphs. -/
def standardThreeRegular (G : StandardTseitinGraph) : Prop :=
  forall v : Nat, List.Mem v (List.range G.n) -> standardVertexDegree G v = 3

theorem StandardTseitinCNFFormula_length_of_standardThreeRegular
    {G : StandardTseitinGraph} {charge : Nat -> Bool}
    (hreg : standardThreeRegular G) :
    (StandardTseitinCNFFormula G charge).length = G.n * 4 := by
  unfold StandardTseitinCNFFormula
  apply tseitinClausesFromIncident_length_of_const_vertex_clause_count
  intro v hv
  exact clausesForVertex_length_of_length_three
    (by
      simpa [standardVertexDegree] using hreg v hv)

/-- Adjacency in the source-style undirected edge list. -/
def standardAdjacent (G : StandardTseitinGraph) (u v : Nat) : Prop :=
  u < G.n /\ v < G.n /\ Not (u = v) /\
    Exists fun e : TseitinModel.UEdge =>
      List.Mem e G.edges
        /\ TseitinModel.UEdge.incident e u = true
        /\ TseitinModel.UEdge.incident e v = true

/-- Reachability generated by source-style adjacency. -/
inductive standardReachable (G : StandardTseitinGraph) : Nat -> Nat -> Prop where
  | refl {v : Nat} (hv : v < G.n) : standardReachable G v v
  | step {u v w : Nat} :
      standardReachable G u v ->
      standardAdjacent G v w ->
      standardReachable G u w

/-- Connectedness predicate for the source-side graph family. -/
def standardConnected (G : StandardTseitinGraph) : Prop :=
  forall u v : Nat, u < G.n -> v < G.n -> standardReachable G u v

/-- Size of a Boolean vertex subset, restricted to vertices of the graph. -/
def standardVertexSetSize (G : StandardTseitinGraph) (S : Nat -> Bool) : Nat :=
  (List.range G.n).countP S

/-- Number of source edges crossing a Boolean vertex cut. -/
def standardCutEdgeCount (G : StandardTseitinGraph) (S : Nat -> Bool) : Nat :=
  G.edges.countP (fun e => Bool.xor (S e.u) (S e.v))

/-- Nonempty small side used in edge-expansion lower bounds. -/
def standardSmallSide (G : StandardTseitinGraph) (S : Nat -> Bool) : Prop :=
  0 < standardVertexSetSize G S /\ 2 * standardVertexSetSize G S <= G.n

/-- Positive rational expansion constant carried without division. -/
structure StandardTseitinEdgeExpansionConstant where
  numerator : Nat
  denominator : Nat
  positive : 0 < numerator /\ 0 < denominator

/-- Edge expansion by a fixed positive rational constant. -/
def standardEdgeExpansionAtLeast (G : StandardTseitinGraph)
    (c : StandardTseitinEdgeExpansionConstant) : Prop :=
  forall S : Nat -> Bool,
    standardSmallSide G S ->
      c.denominator * standardCutEdgeCount G S >=
        c.numerator * standardVertexSetSize G S

/-- Source-side 3-regular family premise. -/
def standardThreeRegularFamily {Index : Type}
    (graph : Index -> StandardTseitinGraph) : Prop :=
  forall i : Index, standardThreeRegular (graph i)

/-- Source-side connected-family premise. -/
def standardConnectedFamily {Index : Type}
    (graph : Index -> StandardTseitinGraph) : Prop :=
  forall i : Index, standardConnected (graph i)

/-- Source-side constant edge-expansion family premise. -/
def standardConstantEdgeExpansionFamily {Index : Type}
    (graph : Index -> StandardTseitinGraph) : Prop :=
  Exists fun c : StandardTseitinEdgeExpansionConstant =>
    forall i : Index, standardEdgeExpansionAtLeast (graph i) c

/-- Typed BSW graph-family premise: 3-regular, connected, constant edge expansion. -/
def standardBSWGraphFamilyPremise {Index : Type}
    (graph : Index -> StandardTseitinGraph) : Prop :=
  standardThreeRegularFamily graph
    /\ standardConnectedFamily graph
    /\ standardConstantEdgeExpansionFamily graph

theorem standardFourCycle_oddTotalCharge :
    standardOddTotalCharge standardFourCycleGraph standardFourCycleCharge := by
  simp [standardOddTotalCharge, standardChargeParity, standardFourCycleGraph,
    standardTseitinGraphOfEdgeList, standardFourCycleCharge]
  native_decide

theorem standardFourCycle_not_standardThreeRegular :
    Not (standardThreeRegular standardFourCycleGraph) := by
  intro h
  have hv : List.Mem 0 (List.range standardFourCycleGraph.n) := by
    change List.Mem 0 [0, 1, 2, 3]
    exact List.Mem.head _
  have h0 : standardVertexDegree standardFourCycleGraph 0 = 3 := h 0 hv
  have h2 : standardVertexDegree standardFourCycleGraph 0 = 2 := by
    native_decide
  omega

theorem standardFourCycle_not_standardBSWGraphFamilyPremise :
    Not (standardBSWGraphFamilyPremise (fun _ : Unit => standardFourCycleGraph)) := by
  intro h
  exact standardFourCycle_not_standardThreeRegular (h.1 ())

theorem not_cnfSat_standardTseitinCNFFormula_of_semantic_premises
    {G : StandardTseitinGraph} {charge : Nat -> Bool}
    (hfold : standardVertexEquationsFoldToCharge G charge)
    (hcancel : standardIncidentParityCancels G)
    (hodd : standardOddTotalCharge G charge) :
    Not (Exists fun a : CNFModel.Assignment G.edges.length =>
      CNFModel.cnfSat a (StandardTseitinCNFFormula G charge)) := by
  intro hsatExists
  rcases hsatExists with ⟨a, hsat⟩
  have hvertices :
      forall v : Nat, List.Mem v (List.range G.n) ->
        standardVertexParitySatisfied G charge a v := by
    intro v hv
    exact standardVertexParitySatisfied_of_cnfSat_standardFormula
      (G := G) (charge := charge) (a := a) (v := v) hv hsat
  have hfold_a : standardIncidentParity G a = standardChargeParity G charge :=
    hfold a hvertices
  have hcancel_a : standardIncidentParity G a = false :=
    hcancel a
  have hfalse_true : false = true := by
    calc
      false = standardIncidentParity G a := hcancel_a.symm
      _ = standardChargeParity G charge := hfold_a
      _ = true := hodd
  cases hfalse_true

theorem not_cnfSat_standardTseitinCNFFormula_of_doubleCount
    {G : StandardTseitinGraph} {charge : Nat -> Bool}
    (hdouble : standardIncidentRowsDoubleCount G)
    (hodd : standardOddTotalCharge G charge) :
    Not (Exists fun a : CNFModel.Assignment G.edges.length =>
      CNFModel.cnfSat a (StandardTseitinCNFFormula G charge)) :=
  not_cnfSat_standardTseitinCNFFormula_of_semantic_premises
    (standardVertexEquationsFoldToCharge_of_vertex_parities G charge)
    (standardIncidentParityCancels_of_doubleCount hdouble)
    hodd

theorem not_cnfSat_standardTseitinCNFFormula_of_graph
    {G : StandardTseitinGraph} {charge : Nat -> Bool}
    (hodd : standardOddTotalCharge G charge) :
    Not (Exists fun a : CNFModel.Assignment G.edges.length =>
      CNFModel.cnfSat a (StandardTseitinCNFFormula G charge)) :=
  not_cnfSat_standardTseitinCNFFormula_of_doubleCount
    (standardIncidentRowsDoubleCount_of_graph G)
    hodd

/-- Family target for source-style Tseitin CNF resolution lower-bound boundaries. -/
def StandardTseitinResolutionFamilyTarget
    {Index : Type} (G : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat) :
    CNFResolution.ResolutionSizeFamilyTarget where
  Index := Index
  n := fun i => (G i).edges.length
  phi := fun i => StandardTseitinCNFFormula (G i) (charge i)
  threshold := threshold

/-- Typed threshold match to a concrete asymptotic source-threshold interpretation. -/
def standardTseitinBSWThresholdFamilyMatch {Index : Type}
    (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat) : Prop :=
  Nonempty (CNFResolution.ResolutionFamilyThresholdInterpretation
    (StandardTseitinResolutionFamilyTarget graph charge threshold))

/--
Descriptive source packet selected by Stage1679.  This is not a lower-bound import;
it records the theorem shape that a later certificate must match.
-/
def standardTseitinBSWUrquhartSourcePacket :
    CNFResolution.ResolutionSourceTheoremPacket where
  sourceName := "Ben-Sasson-Wigderson 2001 / Urquhart 1987"
  theoremName := "Tseitin expander resolution size lower bound"
  sourceURL := "https://dl.acm.org/doi/10.1145/375827.375835"
  proofObjectKind := CNFResolution.ResolutionProofObjectKind.dagLike
  sizeMeasureKind := CNFResolution.ResolutionSourceSizeMeasureKind.lineCount
  theoremStatement :=
    "For a 3-regular connected expander G and odd-weight charge f, " ++
    "the standard Tseitin contradiction tau(G,f) has general resolution " ++
    "refutation size S(tau(G,f)) = 2^Omega(|tau(G,f)|)."
  assumptionStatement :=
    "G finite connected 3-regular expander; one distinct Boolean variable " ++
    "per undirected edge; f has odd total charge; each vertex parity " ++
    "constraint is CNF-encoded as the standard Tseitin contradiction."
  thresholdStatement :=
    "Asymptotic: there exist positive constants c and N0 such that for " ++
    "|tau(G,f)| >= N0, every general resolution refutation has line count " ++
    "at least 2^(c * |tau(G,f)|).  Since local derivation trees are " ++
    "line-counted by nodes, the local threshold uses the same source line " ++
    "threshold after explicit size-measure transfer."

def standardTseitinBSWSourceSizeParameterKind :
    CNFResolution.ResolutionSourceSizeParameterKind :=
  CNFResolution.ResolutionSourceSizeParameterKind.formulaSize

/--
Source-boundary target for classical expander Tseitin CNF resolution claims.
External source facts remain propositions until a concrete source match is
supplied.  Incident-row double-counting is now checked for every
`StandardTseitinGraph` by `standardIncidentRowsDoubleCount_of_graph`.
-/
structure StandardTseitinCNFSourceFamilyTarget where
  Index : Type
  graph : Index -> StandardTseitinGraph
  charge : Index -> Nat -> Bool
  threshold : Index -> Nat
  sourceName : String
  sourceStatement : String
  proofSystemMatch : CNFResolution.ResolutionProofSystemMatch
  oneVariablePerUndirectedEdge : Prop
  parityBlockEncoding : Prop
  oddTotalCharge : Index -> Prop
  boundedDegreeFamily : Prop
  expanderFamily : Prop
  thresholdFamilyMatch : Prop

def StandardTseitinCNFSourceFamilyTarget.fromEncodingFamilyWithStandardEdges
    {Index : Type} (enc : Index -> TseitinModel.GraphEncodingData)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (sourceName sourceStatement : String)
    (proofSystemMatch : CNFResolution.ResolutionProofSystemMatch)
    (parityBlockEncoding : Prop)
    (oddTotalCharge : Index -> Prop)
    (boundedDegreeFamily expanderFamily thresholdFamilyMatch : Prop) :
    StandardTseitinCNFSourceFamilyTarget where
  Index := Index
  graph := fun i => standardTseitinGraphOfEncodingData (enc i)
  charge := charge
  threshold := threshold
  sourceName := sourceName
  sourceStatement := sourceStatement
  proofSystemMatch := proofSystemMatch
  oneVariablePerUndirectedEdge := forall i : Index,
    oneListedEdgePerUndirectedEdge (enc i).edges
  parityBlockEncoding := parityBlockEncoding
  oddTotalCharge := oddTotalCharge
  boundedDegreeFamily := boundedDegreeFamily
  expanderFamily := expanderFamily
  thresholdFamilyMatch := thresholdFamilyMatch

def StandardTseitinCNFSourceFamilyTarget.fromStandardGraphFamilyWithStandardEdges
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (sourceName sourceStatement : String)
    (proofSystemMatch : CNFResolution.ResolutionProofSystemMatch)
    (parityBlockEncoding : Prop)
    (oddTotalCharge : Index -> Prop)
    (boundedDegreeFamily expanderFamily thresholdFamilyMatch : Prop) :
    StandardTseitinCNFSourceFamilyTarget where
  Index := Index
  graph := graph
  charge := charge
  threshold := threshold
  sourceName := sourceName
  sourceStatement := sourceStatement
  proofSystemMatch := proofSystemMatch
  oneVariablePerUndirectedEdge := forall i : Index,
    oneListedEdgePerUndirectedEdge (graph i).edges
  parityBlockEncoding := parityBlockEncoding
  oddTotalCharge := oddTotalCharge
  boundedDegreeFamily := boundedDegreeFamily
  expanderFamily := expanderFamily
  thresholdFamilyMatch := thresholdFamilyMatch

/--
External/source-side BSW target constructor.

Unlike the generic constructor, this pins the graph obligations to typed
source-native predicates: 3-regularity, connectedness, constant edge expansion,
and an explicit source-threshold interpretation.
-/
def StandardTseitinCNFSourceFamilyTarget.fromBSWExternalStandardGraphFamily
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (sourceName sourceStatement : String)
    (proofSystemMatch : CNFResolution.ResolutionProofSystemMatch)
    (parityBlockEncoding : Prop)
    (oddTotalCharge : Index -> Prop) :
    StandardTseitinCNFSourceFamilyTarget where
  Index := Index
  graph := graph
  charge := charge
  threshold := threshold
  sourceName := sourceName
  sourceStatement := sourceStatement
  proofSystemMatch := proofSystemMatch
  oneVariablePerUndirectedEdge := forall i : Index,
    oneListedEdgePerUndirectedEdge (graph i).edges
  parityBlockEncoding := parityBlockEncoding
  oddTotalCharge := oddTotalCharge
  boundedDegreeFamily := standardThreeRegularFamily graph
  expanderFamily :=
    standardConnectedFamily graph /\ standardConstantEdgeExpansionFamily graph
  thresholdFamilyMatch :=
    standardTseitinBSWThresholdFamilyMatch graph charge threshold

/--
Finite source-native smoke target for the standard Tseitin graph convention.
It is intentionally not an expander-family target and does not claim source
lower-bound transfer.
-/
def standardFourCycleSourceSmokeTarget :
    StandardTseitinCNFSourceFamilyTarget :=
  StandardTseitinCNFSourceFamilyTarget.fromStandardGraphFamilyWithStandardEdges
    (Index := Unit)
    (fun _ => standardFourCycleGraph)
    (fun _ => standardFourCycleCharge)
    (fun _ => 0)
    "finite standard four-cycle smoke target"
    "Finite non-expander smoke target for source-native standard Tseitin edge conventions."
    (CNFResolution.ResolutionProofSystemMatch.generalSourceToLocalTree
      False True)
    True
    (fun _ => standardOddTotalCharge standardFourCycleGraph standardFourCycleCharge)
    True
    False
    True

theorem standardFourCycleSourceSmokeTarget_oneVariablePerUndirectedEdge :
    standardFourCycleSourceSmokeTarget.oneVariablePerUndirectedEdge := by
  intro i
  cases i
  simpa [standardFourCycleSourceSmokeTarget,
    StandardTseitinCNFSourceFamilyTarget.fromStandardGraphFamilyWithStandardEdges,
    standardFourCycleGraph, standardTseitinGraphOfEdgeList] using
    standardFourCycle_oneListedEdgePerUndirectedEdge

theorem standardFourCycleSourceSmokeTarget_notExpanderFamily :
    Not standardFourCycleSourceSmokeTarget.expanderFamily := by
  simp [standardFourCycleSourceSmokeTarget,
    StandardTseitinCNFSourceFamilyTarget.fromStandardGraphFamilyWithStandardEdges]

theorem standardFourCycleSourceSmokeTarget_noLowerBoundTransfer :
    Not standardFourCycleSourceSmokeTarget.proofSystemMatch.lowerBoundTransfersToLocal := by
  simp [standardFourCycleSourceSmokeTarget,
    StandardTseitinCNFSourceFamilyTarget.fromStandardGraphFamilyWithStandardEdges,
    CNFResolution.ResolutionProofSystemMatch.generalSourceToLocalTree]

def StandardTseitinCNFSourceFamilyTarget.resolutionTarget
    (target : StandardTseitinCNFSourceFamilyTarget) :
    CNFResolution.ResolutionSizeFamilyTarget :=
  StandardTseitinResolutionFamilyTarget target.graph target.charge target.threshold

def StandardTseitinCNFSourceFamilyTarget.encodingFamilyMatch
    (target : StandardTseitinCNFSourceFamilyTarget) : Prop :=
  target.oneVariablePerUndirectedEdge
    /\ target.parityBlockEncoding
    /\ (forall i : target.Index, target.oddTotalCharge i)
    /\ target.boundedDegreeFamily
    /\ target.expanderFamily

def StandardTseitinCNFSourceFamilyTarget.lowerBoundPremise
    (target : StandardTseitinCNFSourceFamilyTarget) : Prop :=
  CNFResolution.ResolutionSizeFamilyLowerBoundPremise target.resolutionTarget

def StandardTseitinCNFSourceFamilyTarget.sourceLineLowerBoundPremise
    (target : StandardTseitinCNFSourceFamilyTarget)
    (sourceLineCount :
      CNFResolution.ResolutionFamilySourceLineCount target.resolutionTarget) :
    Prop :=
  CNFResolution.ResolutionFamilySourceLineLowerBoundPremise
    target.resolutionTarget sourceLineCount

def StandardTseitinCNFSourceFamilyTarget.sourceLineCountTransfersToLocalTree
    (target : StandardTseitinCNFSourceFamilyTarget)
    (sourceLineCount :
      CNFResolution.ResolutionFamilySourceLineCount target.resolutionTarget) :
    Prop :=
  CNFResolution.ResolutionFamilySourceLineCountTransfersToLocalTree
    target.resolutionTarget sourceLineCount

theorem StandardTseitinCNFSourceFamilyTarget.lowerBoundPremise_of_sourceLineLowerBound
    {target : StandardTseitinCNFSourceFamilyTarget}
    {sourceLineCount :
      CNFResolution.ResolutionFamilySourceLineCount target.resolutionTarget}
    (hsource :
      target.sourceLineLowerBoundPremise sourceLineCount)
    (htransfer :
      target.sourceLineCountTransfersToLocalTree sourceLineCount) :
    target.lowerBoundPremise := by
  exact CNFResolution.resolutionSizeFamilyLowerBoundPremise_of_sourceLineLowerBound
    (target:=target.resolutionTarget)
    (sourceLineCount:=sourceLineCount) hsource htransfer

def StandardTseitinCNFSourceFamilyTarget.treeSourceLineCount
    (target : StandardTseitinCNFSourceFamilyTarget) :
    CNFResolution.ResolutionFamilySourceLineCount target.resolutionTarget :=
  CNFResolution.ResolutionFamilyTreeSourceLineCount target.resolutionTarget

theorem StandardTseitinCNFSourceFamilyTarget.treeSourceLineCountTransfersToLocalTree
    (target : StandardTseitinCNFSourceFamilyTarget) :
    target.sourceLineCountTransfersToLocalTree target.treeSourceLineCount := by
  exact CNFResolution.ResolutionFamilyTreeSourceLineCount_transfersToLocalTree
    target.resolutionTarget

def StandardTseitinCNFSourceFamilyTarget.traceLineLowerBoundPremise
    (target : StandardTseitinCNFSourceFamilyTarget) : Prop :=
  CNFResolution.ResolutionFamilyTraceLineLowerBoundPremise
    target.resolutionTarget

theorem StandardTseitinCNFSourceFamilyTarget.sourceLineLowerBoundPremise_of_traceLineLowerBound
    {target : StandardTseitinCNFSourceFamilyTarget}
    (hsource : target.traceLineLowerBoundPremise) :
    target.sourceLineLowerBoundPremise target.treeSourceLineCount := by
  exact CNFResolution.ResolutionFamilySourceLineLowerBoundPremise_of_traceLineLowerBound
    (target:=target.resolutionTarget) hsource

theorem StandardTseitinCNFSourceFamilyTarget.lowerBoundPremise_of_traceLineLowerBound
    {target : StandardTseitinCNFSourceFamilyTarget}
    (hsource : target.traceLineLowerBoundPremise) :
    target.lowerBoundPremise := by
  exact StandardTseitinCNFSourceFamilyTarget.lowerBoundPremise_of_sourceLineLowerBound
    (target:=target)
    (sourceLineCount:=target.treeSourceLineCount)
    (StandardTseitinCNFSourceFamilyTarget.sourceLineLowerBoundPremise_of_traceLineLowerBound
      hsource)
    (StandardTseitinCNFSourceFamilyTarget.treeSourceLineCountTransfersToLocalTree
      target)

def StandardTseitinCNFSourceFamilyTarget.toResolutionBoundary
    (target : StandardTseitinCNFSourceFamilyTarget) :
    CNFResolution.ResolutionFamilySourceBoundaryTarget where
  target := target.resolutionTarget
  sourceName := target.sourceName
  sourceStatement := target.sourceStatement
  proofSystemMatch := target.proofSystemMatch.asProp
  encodingFamilyMatch := target.encodingFamilyMatch
  sizeMeasureMatch := target.proofSystemMatch.sizeMeasureCompatible
  thresholdFamilyMatch := target.thresholdFamilyMatch

structure StandardTseitinCNFSourceFamilyCertificate
    (target : StandardTseitinCNFSourceFamilyTarget) where
  proof_kind_compatible : target.proofSystemMatch.kindCompatible
  lower_bound_transfers_to_local : target.proofSystemMatch.lowerBoundTransfersToLocal
  size_measure_compatible : target.proofSystemMatch.sizeMeasureCompatible
  one_variable_per_undirected_edge : target.oneVariablePerUndirectedEdge
  parity_block_encoding : target.parityBlockEncoding
  odd_total_charge : forall i : target.Index, target.oddTotalCharge i
  bounded_degree_family : target.boundedDegreeFamily
  expander_family : target.expanderFamily
  threshold_family_match : target.thresholdFamilyMatch
  source_trace_line_lower_bound : target.traceLineLowerBoundPremise

def StandardTseitinCNFSourceFamilyCertificate.toResolutionBoundaryCertificate
    {target : StandardTseitinCNFSourceFamilyTarget}
    (cert : StandardTseitinCNFSourceFamilyCertificate target) :
    CNFResolution.ResolutionFamilySourceBoundaryCertificate
      target.toResolutionBoundary where
  proof_system_match :=
    And.intro cert.proof_kind_compatible
      (And.intro cert.lower_bound_transfers_to_local cert.size_measure_compatible)
  encoding_family_match :=
    And.intro cert.one_variable_per_undirected_edge
      (And.intro cert.parity_block_encoding
        (And.intro cert.odd_total_charge
          (And.intro cert.bounded_degree_family cert.expander_family)))
  size_measure_match := cert.size_measure_compatible
  threshold_family_match := cert.threshold_family_match
  lower_bound :=
    StandardTseitinCNFSourceFamilyTarget.lowerBoundPremise_of_traceLineLowerBound
      cert.source_trace_line_lower_bound

theorem resolutionSizeFamilyLowerBoundPremise_of_standardTseitinSourceBoundary
    {target : StandardTseitinCNFSourceFamilyTarget}
    (cert : StandardTseitinCNFSourceFamilyCertificate target) :
    CNFResolution.ResolutionSizeFamilyLowerBoundPremise target.resolutionTarget :=
  StandardTseitinCNFSourceFamilyTarget.lowerBoundPremise_of_traceLineLowerBound
    cert.source_trace_line_lower_bound

/-- Checked local parity-block encoding fact for the standard Tseitin target. -/
def standardTseitinParityBlockEncodingFamily {Index : Type}
    (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat) : Prop :=
  forall i : Index,
    (StandardTseitinResolutionFamilyTarget graph charge threshold).phi i =
      StandardTseitinCNFFormula (graph i) (charge i)

theorem standardTseitinParityBlockEncodingFamily_of_definition
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat) :
    standardTseitinParityBlockEncodingFamily graph charge threshold := by
  intro i
  rfl

/-- Checked local tree-line transfer used by the external BSW assembly target. -/
def standardTseitinTreeLineTransfersToLocal {Index : Type}
    (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat) : Prop :=
  CNFResolution.ResolutionFamilySourceLineCountTransfersToLocalTree
    (StandardTseitinResolutionFamilyTarget graph charge threshold)
    (CNFResolution.ResolutionFamilyTreeSourceLineCount
      (StandardTseitinResolutionFamilyTarget graph charge threshold))

theorem standardTseitinTreeLineTransfersToLocal_of_tree
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat) :
    standardTseitinTreeLineTransfersToLocal graph charge threshold := by
  exact CNFResolution.ResolutionFamilyTreeSourceLineCount_transfersToLocalTree
    (StandardTseitinResolutionFamilyTarget graph charge threshold)

/-- Checked local equality between the chosen source line count and local tree size. -/
def standardTseitinTreeSizeMeasureCompatible {Index : Type}
    (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat) : Prop :=
  forall (i : Index)
    (r : CNFResolution.ResolutionRefutation
      ((StandardTseitinResolutionFamilyTarget graph charge threshold).phi i)),
    CNFResolution.ResolutionRefutationTreeSourceLineCount r =
      CNFResolution.ResolutionRefutationSize r

theorem standardTseitinTreeSizeMeasureCompatible_of_tree
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat) :
    standardTseitinTreeSizeMeasureCompatible graph charge threshold := by
  intro _ r
  exact CNFResolution.ResolutionRefutationTreeSourceLineCount_eq_size r

/--
Proof-system match specialized to the local tree-line source view.  The
proof-object kind compatibility is checked; the transfer and size-measure fields
are the checked local tree-line propositions above.
-/
def standardTseitinExternalBSWProofSystemMatch {Index : Type}
    (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat) :
    CNFResolution.ResolutionProofSystemMatch :=
  CNFResolution.ResolutionProofSystemMatch.generalSourceToLocalTree
    (standardTseitinTreeLineTransfersToLocal graph charge threshold)
    (standardTseitinTreeSizeMeasureCompatible graph charge threshold)

def standardTseitinExternalBSWSourceTarget {Index : Type}
    (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (sourceName sourceStatement : String) :
    StandardTseitinCNFSourceFamilyTarget :=
  StandardTseitinCNFSourceFamilyTarget.fromBSWExternalStandardGraphFamily
    graph charge threshold sourceName sourceStatement
    (standardTseitinExternalBSWProofSystemMatch graph charge threshold)
    (standardTseitinParityBlockEncodingFamily graph charge threshold)
    (fun i => standardOddTotalCharge (graph i) (charge i))

/--
The nonlocal assumptions still needed to assemble the external BSW certificate.
Every field is either a typed source premise or the source trace-line lower
bound; the proof-system, parity encoding, and size-transfer fields are checked
locally by the specialized target.
-/
structure StandardTseitinExternalBSWCertificatePremises {Index : Type}
    (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat) where
  one_variable_per_undirected_edge :
    forall i : Index, oneListedEdgePerUndirectedEdge (graph i).edges
  odd_total_charge :
    forall i : Index, standardOddTotalCharge (graph i) (charge i)
  bsw_graph_family : standardBSWGraphFamilyPremise graph
  threshold_family_match :
    standardTseitinBSWThresholdFamilyMatch graph charge threshold
  source_trace_line_lower_bound :
    CNFResolution.ResolutionFamilyTraceLineLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)

def StandardTseitinExternalBSWCertificatePremises.toSourceFamilyCertificate
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {sourceName sourceStatement : String}
    (prem :
      StandardTseitinExternalBSWCertificatePremises graph charge threshold) :
    StandardTseitinCNFSourceFamilyCertificate
      (standardTseitinExternalBSWSourceTarget
        graph charge threshold sourceName sourceStatement) where
  proof_kind_compatible := by
    exact
      CNFResolution.ResolutionProofSystemMatch.generalSourceToLocalTree_kindCompatible
        (standardTseitinTreeLineTransfersToLocal graph charge threshold)
        (standardTseitinTreeSizeMeasureCompatible graph charge threshold)
  lower_bound_transfers_to_local :=
    standardTseitinTreeLineTransfersToLocal_of_tree graph charge threshold
  size_measure_compatible :=
    standardTseitinTreeSizeMeasureCompatible_of_tree graph charge threshold
  one_variable_per_undirected_edge := prem.one_variable_per_undirected_edge
  parity_block_encoding :=
    standardTseitinParityBlockEncodingFamily_of_definition
      graph charge threshold
  odd_total_charge := prem.odd_total_charge
  bounded_degree_family := prem.bsw_graph_family.1
  expander_family := And.intro prem.bsw_graph_family.2.1 prem.bsw_graph_family.2.2
  threshold_family_match := prem.threshold_family_match
  source_trace_line_lower_bound := prem.source_trace_line_lower_bound

theorem standardTseitinExternalBSWLowerBound_of_certificatePremises
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {sourceName sourceStatement : String}
    (prem :
      StandardTseitinExternalBSWCertificatePremises graph charge threshold) :
    CNFResolution.ResolutionSizeFamilyLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold) := by
  exact resolutionSizeFamilyLowerBoundPremise_of_standardTseitinSourceBoundary
    (StandardTseitinExternalBSWCertificatePremises.toSourceFamilyCertificate
      (sourceName:=sourceName) (sourceStatement:=sourceStatement) prem)

theorem false_of_standardFourCycleExternalBSWCertificatePremises
    {charge : Unit -> Nat -> Bool} {threshold : Unit -> Nat}
    (prem : StandardTseitinExternalBSWCertificatePremises
      (fun _ : Unit => standardFourCycleGraph) charge threshold) :
    False := by
  exact standardFourCycle_not_standardBSWGraphFamilyPremise prem.bsw_graph_family

/-- Descriptive source name for the selected Morgenstern q = 2 witness lane. -/
def standardTseitinMorgensternQ2SourceName : String :=
  "Morgenstern q=2 Ramanujan family / Ben-Sasson-Wigderson Tseitin expander lower bound"

/--
Descriptive source statement for the selected witness shell.

This is intentionally prose metadata.  The mathematical obligations remain the
five typed fields of `StandardTseitinMorgensternQ2SourceFamilyShell`.
-/
def standardTseitinMorgensternQ2SourceStatement : String :=
  "Source-side witness shell: Morgenstern q=2 supplies a 3-regular Ramanujan family; " ++
  "Ben-Sasson-Wigderson applies to standard Tseitin contradictions on " ++
  "3-regular connected expanders with odd charge."

/-- Descriptive source packet for the selected trace-line lower-bound lane. -/
def standardTseitinMorgensternQ2TraceSourceTheoremPacket :
    CNFResolution.ResolutionSourceTheoremPacket where
  sourceName :=
    standardTseitinMorgensternQ2SourceName
  theoremName :=
    "Morgenstern q=2 plus Ben-Sasson-Wigderson Tseitin lower bound"
  sourceURL :=
    "https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/B-SW99/bw00journal.pdf; " ++
    "https://www.cs.ubc.ca/sites/default/files/tr/1991/TR-91-11.pdf"
  proofObjectKind := CNFResolution.ResolutionProofObjectKind.dagLike
  sizeMeasureKind := CNFResolution.ResolutionSourceSizeMeasureKind.lineCount
  theoremStatement :=
    "Standard Tseitin contradictions over the selected q=2 Ramanujan expander " ++
    "family have exponential resolution line-count lower bounds."
  assumptionStatement :=
    "The source family is the Morgenstern q=2 Ramanujan family, converted " ++
    "source-side into 3-regular connected constant-edge expanders with odd " ++
    "Tseitin charges."
  thresholdStatement :=
    "The local family threshold is the source exponential lower-bound threshold " ++
    "interpreted at the source graph-vertex parameter."

/-- Source URL for the Morgenstern q = 2 Ramanujan construction lane. -/
def standardTseitinMorgensternQ2RamanujanSourceURL : String :=
  "https://www.cs.ubc.ca/sites/default/files/tr/1991/TR-91-11.pdf"

/-- Source URL for the Ben-Sasson/Wigderson Tseitin line-count lane. -/
def standardTseitinBSWLineCountSourceURL : String :=
  "https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/B-SW99/final.pdf"

/-- Source URL for the Alon-Milman spectral-to-edge-expansion bridge. -/
def standardTseitinAlonMilmanEdgeExpansionSourceURL : String :=
  "https://web.math.princeton.edu/~nalon/PDFS/Publications2/lambda%20%20isoperimetric%20inequalities%20for%20graphs%20and%20superconcentrators.pdf"

/-- Locator for the selected even-q Morgenstern construction theorem. -/
def standardTseitinMorgensternQ2ConstructionLocator : String :=
  "Morgenstern TR-91-11: abstract and Section 5; Theorem 5.13 with q = 2."

/-- Locator for the source-side Ramanujan-to-expansion bridge. -/
def standardTseitinMorgensternQ2ExpansionLocator : String :=
  "Source-side spectral-expansion bridge applied to the q = 2 Ramanujan family; " ++
  "Morgenstern Theorems 4.10, 4.11, and 5.13 provide the regular/Ramanujan " ++
  "graph-family inputs."

/-- Locator for the Alon-Milman cut-edge expansion inequality. -/
def standardTseitinAlonMilmanCutEdgeLocator : String :=
  "Alon-Milman, lambda_1 isoperimetric inequalities, Section 2: " ++
  "Q = degree matrix minus adjacency, Remark 2.4 / Lemma 2.1 gives at least " ++
  "lambda_1 * |S| * (n - |S|) / n cut edges."

/-- Locator for the BSW Tseitin width lower-bound statement. -/
def standardTseitinBSWTseitinWidthLocator : String :=
  "Ben-Sasson/Wigderson, Short Proofs are Narrow, Section 4.1: " ++
  "Definitions 4.1 and 4.3, Theorem 4.4."

/-- Locator for the BSW width-to-size lower-bound conversion. -/
def standardTseitinBSWSizeWidthLocator : String :=
  "Ben-Sasson/Wigderson, Short Proofs are Narrow, Corollaries 3.4 and 3.6; " ++
  "Tseitin expander size conclusion in Corollary 4.5."

/-- Locator for the source line-count interpretation of the BSW size measure. -/
def standardTseitinBSWLineCountMeasureLocator : String :=
  "Ben-Sasson/Wigderson, Short Proofs are Narrow, abstract and Section 3: " ++
  "resolution proof length/size is the source line-count measure."

/-- Locator for the source-side concrete threshold constants obligation. -/
def standardTseitinBSWConcreteThresholdLocator : String :=
  "Ben-Sasson/Wigderson, Short Proofs are Narrow, Corollary 4.5 and its " ++
  "upstream width/size constants; exact c, d, and n0 remain source-side data."

/-- Locator for the hidden constant in the BSW general-resolution size-width route. -/
def standardTseitinBSWWidthSizeConstantLocator : String :=
  "Ben-Sasson/Wigderson, Short Proofs are Narrow, Theorem 3.5 and " ++
  "Corollary 3.6; extract the hidden constant in the general-resolution " ++
  "size-width exponent."

/-- Locator for the explicit arithmetic target inside the BSW Theorem 3.5 proof. -/
def standardTseitinBSWTheorem35ExplicitArithmeticLocator : String :=
  "Ben-Sasson/Wigderson, Short Proofs are Narrow, Theorem 3.5 proof: " ++
  "d = ceil(sqrt(2*n*ln S(F))) and a = (1 - d/(2*n))^-1."

/--
Source-side extraction target for the explicit arithmetic hidden in the BSW
general-resolution width-size route.

This is not an analytic proof inside Lean.  It records the exact source
obligations needed before the `width_size_constant_source` field of
`StandardTseitinBSWConcreteThresholdDecomposition` can be treated as reduced.
The intentionally conservative forward target is the proof-level inequality
`W <= k + 2*d + 1`, where `d = ceil(sqrt(2*n*ln S(F)))`; the extra `+1`
absorbs the strict `|pi*| < a^b` step when choosing the induction parameter.
-/
structure StandardTseitinBSWWidthSizeExplicitArithmeticExtraction where
  source_url : String
  theorem35_locator : String
  corollary36_locator : String
  proof_parameter_d_formula : String
  proof_parameter_a_formula : String
  forward_width_size_target_statement : String
  inversion_target_statement : String
  side_conditions_statement : String
  forward_width_size_target : Prop
  forward_width_size_target_holds : forward_width_size_target
  inversion_target : Prop
  inversion_target_holds : inversion_target
  base_two_nat_conversion_target : Prop
  base_two_nat_conversion_target_holds : base_two_nat_conversion_target
  eventual_threshold_side_conditions : Prop
  eventual_threshold_side_conditions_holds : eventual_threshold_side_conditions
  width_size_constant_source : Prop
  width_size_constant_source_of_targets :
    forward_width_size_target ->
    inversion_target ->
    base_two_nat_conversion_target ->
    eventual_threshold_side_conditions ->
    width_size_constant_source

def StandardTseitinBSWWidthSizeExplicitArithmeticExtraction.toWidthSizeConstantSource
    (extraction : StandardTseitinBSWWidthSizeExplicitArithmeticExtraction) :
    extraction.width_size_constant_source :=
  extraction.width_size_constant_source_of_targets
    extraction.forward_width_size_target_holds
    extraction.inversion_target_holds
    extraction.base_two_nat_conversion_target_holds
    extraction.eventual_threshold_side_conditions_holds

/-- Locator for the inversion/base-conversion arithmetic following the BSW Theorem 3.5 proof. -/
def standardTseitinBSWWidthSizeInversionBaseConversionLocator : String :=
  "Invert the Stage1728 target W <= k + 2*d + 1 with " ++
  "d = ceil(sqrt(2*n*ln S(F))); track the W-k gap, ceiling/sqrt slack, " ++
  "natural-log to base-2 conversion, Nat floors, and eventual n0."

/--
Source-side inversion/base-conversion shell for the Stage1728 width-size target.

This record does not prove real arithmetic locally.  It makes the contrapositive
constant path auditable: from a minimum required width `W_min`, subtract the
initial width `k`, absorb the `+1` and ceiling slack, square, divide by `2*n`,
then convert the resulting natural-log lower bound into the local base-2 Nat
threshold shape.  The conservative shape recorded for the analytic step is
`ln S >= (gap - 3)^2 / (8*n)` after the required positivity and small-`n`
side conditions.
-/
structure StandardTseitinBSWWidthSizeInversionBaseConversion where
  source_url : String
  theorem35_locator : String
  inversion_base_conversion_locator : String
  forward_width_size_target_statement : String
  width_gap_accounting_statement : String
  ceiling_sqrt_slack_statement : String
  log_lower_bound_statement : String
  exponential_lower_bound_statement : String
  base_two_nat_threshold_statement : String
  constant_shape_decision_statement : String
  side_conditions_statement : String
  forward_width_size_target : Prop
  forward_width_size_target_holds : forward_width_size_target
  width_gap_accounting_target : Prop
  width_gap_accounting_target_holds : width_gap_accounting_target
  ceiling_sqrt_slack_target : Prop
  ceiling_sqrt_slack_target_holds : ceiling_sqrt_slack_target
  log_inversion_target : Prop
  log_inversion_target_holds : log_inversion_target
  base_two_nat_conversion_target : Prop
  base_two_nat_conversion_target_holds : base_two_nat_conversion_target
  eventual_threshold_side_conditions : Prop
  eventual_threshold_side_conditions_holds : eventual_threshold_side_conditions
  width_size_constant_source : Prop
  width_size_constant_source_of_targets :
    forward_width_size_target ->
    width_gap_accounting_target ->
    ceiling_sqrt_slack_target ->
    log_inversion_target ->
    base_two_nat_conversion_target ->
    eventual_threshold_side_conditions ->
    width_size_constant_source

def StandardTseitinBSWWidthSizeInversionBaseConversion.toExplicitArithmeticExtraction
    (conversion : StandardTseitinBSWWidthSizeInversionBaseConversion) :
    StandardTseitinBSWWidthSizeExplicitArithmeticExtraction where
  source_url := conversion.source_url
  theorem35_locator := conversion.theorem35_locator
  corollary36_locator := standardTseitinBSWWidthSizeConstantLocator
  proof_parameter_d_formula := "d = ceil(sqrt(2*n*ln S(F)))"
  proof_parameter_a_formula := "a = (1 - d/(2*n))^-1"
  forward_width_size_target_statement :=
    conversion.forward_width_size_target_statement
  inversion_target_statement :=
    conversion.width_gap_accounting_statement ++ " " ++
    conversion.ceiling_sqrt_slack_statement ++ " " ++
    conversion.log_lower_bound_statement
  side_conditions_statement := conversion.side_conditions_statement
  forward_width_size_target := conversion.forward_width_size_target
  forward_width_size_target_holds := conversion.forward_width_size_target_holds
  inversion_target :=
    conversion.width_gap_accounting_target /\
      conversion.ceiling_sqrt_slack_target /\
      conversion.log_inversion_target
  inversion_target_holds := by
    exact And.intro conversion.width_gap_accounting_target_holds
      (And.intro conversion.ceiling_sqrt_slack_target_holds
        conversion.log_inversion_target_holds)
  base_two_nat_conversion_target := conversion.base_two_nat_conversion_target
  base_two_nat_conversion_target_holds :=
    conversion.base_two_nat_conversion_target_holds
  eventual_threshold_side_conditions :=
    conversion.eventual_threshold_side_conditions
  eventual_threshold_side_conditions_holds :=
    conversion.eventual_threshold_side_conditions_holds
  width_size_constant_source := conversion.width_size_constant_source
  width_size_constant_source_of_targets := by
    intro hforward hinversion hbase heventual
    exact conversion.width_size_constant_source_of_targets
      hforward hinversion.1 hinversion.2.1 hinversion.2.2 hbase heventual

def StandardTseitinBSWWidthSizeInversionBaseConversion.toWidthSizeConstantSource
    (conversion : StandardTseitinBSWWidthSizeInversionBaseConversion) :
    conversion.width_size_constant_source :=
  (conversion.toExplicitArithmeticExtraction).toWidthSizeConstantSource

/--
Conservative width-gap coefficient obtained from a small-side edge-expansion
constant.

If the source bridge turns small-side expansion `c` into BSW middle-cut
expansion at least `c * n / 3`, and the initial 3-regular Tseitin width plus
Stage1729 slack cost six units total, then `c / 6` is the safe eventual linear gap
coefficient after a large-enough cutoff.
-/
def StandardTseitinEdgeExpansionConstant.widthGapCoefficient
    (c : StandardTseitinEdgeExpansionConstant) :
    StandardTseitinEdgeExpansionConstant where
  numerator := c.numerator
  denominator := 6 * c.denominator
  positive := by
    constructor
    · exact c.positive.1
    · exact Nat.mul_pos (by decide) c.positive.2

/-- Conservative eventual cutoff for absorbing the six additive width-gap units. -/
def StandardTseitinEdgeExpansionConstant.widthGapEventualThreshold
    (c : StandardTseitinEdgeExpansionConstant) : Nat :=
  36 * c.denominator

/-- Locator for the Stage1730 width-gap coefficient extraction target. -/
def standardTseitinBSWWidthGapExpansionCoefficientLocator : String :=
  "Combine BSW Definition 4.3 and Theorem 4.4 with the selected small-side " ++
  "edge-expansion constant, 3-regular initial width k <= 3, Stage1729 additive " ++
  "slack, and eventual cutoff; conservative coefficient target is c/6."

/--
Source-side width-gap coefficient shell for the Stage1729 inversion target.

The record exposes the intended coefficient arithmetic without claiming the
source graph-expansion or BSW width theorem locally.  Given a small-side
edge-expansion constant `c`, the conservative candidate for the eventual
linear gap is `c.widthGapCoefficient`, i.e. `c / 6`, after the cutoff
`36 * c.denominator`.
-/
structure StandardTseitinBSWWidthGapExpansionCoefficient where
  source_url : String
  bsw_expansion_definition_locator : String
  bsw_tseitin_width_locator : String
  expansion_rate_constant_locator : String
  formula_width_locator : String
  width_gap_coefficient_locator : String
  edge_expansion_constant : StandardTseitinEdgeExpansionConstant
  width_gap_coefficient : StandardTseitinEdgeExpansionConstant
  width_gap_coefficient_matches_candidate :
    width_gap_coefficient =
      edge_expansion_constant.widthGapCoefficient
  width_gap_eventual_threshold : Nat
  width_gap_eventual_threshold_matches_candidate :
    width_gap_eventual_threshold =
      edge_expansion_constant.widthGapEventualThreshold
  bsw_middle_cut_expansion_statement : String
  tseitin_width_lower_bound_statement : String
  initial_width_loss_statement : String
  additive_slack_absorption_statement : String
  linear_width_gap_target_statement : String
  coefficient_decision_statement : String
  side_conditions_statement : String
  bsw_middle_cut_expansion_source : Prop
  bsw_middle_cut_expansion_source_holds : bsw_middle_cut_expansion_source
  tseitin_width_lower_bound_source : Prop
  tseitin_width_lower_bound_source_holds : tseitin_width_lower_bound_source
  initial_width_loss_source : Prop
  initial_width_loss_source_holds : initial_width_loss_source
  additive_slack_absorption_source : Prop
  additive_slack_absorption_source_holds : additive_slack_absorption_source
  linear_width_gap_target : Prop
  linear_width_gap_target_of_sources :
    bsw_middle_cut_expansion_source ->
    tseitin_width_lower_bound_source ->
    initial_width_loss_source ->
    additive_slack_absorption_source ->
    linear_width_gap_target
  width_gap_accounting_target : Prop
  width_gap_accounting_target_of_linear_gap :
    linear_width_gap_target -> width_gap_accounting_target

def StandardTseitinBSWWidthGapExpansionCoefficient.toLinearWidthGapTarget
    (packet : StandardTseitinBSWWidthGapExpansionCoefficient) :
    packet.linear_width_gap_target :=
  packet.linear_width_gap_target_of_sources
    packet.bsw_middle_cut_expansion_source_holds
    packet.tseitin_width_lower_bound_source_holds
    packet.initial_width_loss_source_holds
    packet.additive_slack_absorption_source_holds

def StandardTseitinBSWWidthGapExpansionCoefficient.toWidthGapAccountingTarget
    (packet : StandardTseitinBSWWidthGapExpansionCoefficient) :
    packet.width_gap_accounting_target :=
  packet.width_gap_accounting_target_of_linear_gap
    packet.toLinearWidthGapTarget

/--
Conservative rational small-side edge-expansion constant selected by the Stage1731
normalization audit.

The source chain gives the real lower bound `(3 - 2 * sqrt 2) / 2` for
3-regular Ramanujan graphs after the Alon-Milman cut-edge bridge.  The rational
`1 / 12` is a strict conservative lower bound because `2 * sqrt 2 <= 17 / 6`.
The local development records the rational constant only; it does not prove the
spectral theorem or real arithmetic locally.
-/
def standardTseitinMorgensternQ2EdgeExpansionConstant :
    StandardTseitinEdgeExpansionConstant where
  numerator := 1
  denominator := 12
  positive := by
    constructor <;> decide

/-- Width-gap coefficient induced by the selected q = 2 expansion constant. -/
def standardTseitinMorgensternQ2WidthGapCoefficient :
    StandardTseitinEdgeExpansionConstant :=
  standardTseitinMorgensternQ2EdgeExpansionConstant.widthGapCoefficient

/-- Eventual cutoff induced by the selected q = 2 expansion constant. -/
def standardTseitinMorgensternQ2WidthGapEventualThreshold : Nat :=
  standardTseitinMorgensternQ2EdgeExpansionConstant.widthGapEventualThreshold

/-- Locator for the Stage1731 q = 2 expansion-constant normalization audit. -/
def standardTseitinMorgensternQ2ExpansionConstantNormalizationLocator : String :=
  "Morgenstern q = 2 gives 3-regular Ramanujan graphs with lambda_2 <= 2*sqrt(2); " ++
  "Alon-Milman gives cut-edge expansion at least (3 - 2*sqrt(2))/2 on small " ++
  "sides; choose conservative rational c = 1/12."

/--
Source-side normalization packet for the selected Morgenstern q = 2 expansion
constant.

This packet records the exact theorem chain needed to use
`standardTseitinMorgensternQ2EdgeExpansionConstant` as the small-side
edge-expansion constant feeding Stage1730.  The source facts remain explicit
propositions; the packet only fixes the rational normalization and its local
downstream coefficient.
-/
structure StandardTseitinMorgensternQ2ExpansionConstantNormalization where
  morgenstern_source_url : String
  alon_milman_source_url : String
  morgenstern_construction_locator : String
  alon_milman_cut_edge_locator : String
  normalization_locator : String
  selected_edge_expansion_constant : StandardTseitinEdgeExpansionConstant
  selected_edge_expansion_constant_matches_candidate :
    selected_edge_expansion_constant =
      standardTseitinMorgensternQ2EdgeExpansionConstant
  selected_width_gap_coefficient : StandardTseitinEdgeExpansionConstant
  selected_width_gap_coefficient_matches_candidate :
    selected_width_gap_coefficient =
      selected_edge_expansion_constant.widthGapCoefficient
  selected_width_gap_eventual_threshold : Nat
  selected_width_gap_eventual_threshold_matches_candidate :
    selected_width_gap_eventual_threshold =
      selected_edge_expansion_constant.widthGapEventualThreshold
  degree_normalization_statement : String
  spectral_bound_statement : String
  laplacian_gap_statement : String
  small_side_cut_statement : String
  rational_slack_statement : String
  local_cut_definition_statement : String
  morgenstern_q2_ramanujan_source : Prop
  morgenstern_q2_ramanujan_source_holds :
    morgenstern_q2_ramanujan_source
  alon_milman_cut_edge_source : Prop
  alon_milman_cut_edge_source_holds :
    alon_milman_cut_edge_source
  rational_slack_source : Prop
  rational_slack_source_holds :
    rational_slack_source
  normalized_edge_expansion_source : Prop
  normalized_edge_expansion_source_of_sources :
    morgenstern_q2_ramanujan_source ->
    alon_milman_cut_edge_source ->
    rational_slack_source ->
    normalized_edge_expansion_source

def StandardTseitinMorgensternQ2ExpansionConstantNormalization.toEdgeExpansionSource
    (packet : StandardTseitinMorgensternQ2ExpansionConstantNormalization) :
    packet.normalized_edge_expansion_source :=
  packet.normalized_edge_expansion_source_of_sources
    packet.morgenstern_q2_ramanujan_source_holds
    packet.alon_milman_cut_edge_source_holds
    packet.rational_slack_source_holds

/--
Source-boundary hardening packet for the selected Morgenstern q = 2 graph
family.

The packet separates four issues that were previously hidden inside
`standardBSWGraphFamilyPremise`: source indexing, q = 2 Ramanujan construction,
spectral-to-edge expansion normalization, and the local `StandardTseitinGraph`
representation/edge convention.  It still carries source facts as explicit
propositions; it only provides the checked local converter to the BSW graph
family premise once those facts and the representation match are supplied.
-/
structure StandardTseitinMorgensternQ2GraphFamilyHardening
    {Index : Type} (graph : Index -> StandardTseitinGraph) where
  morgenstern_source_url : String
  alon_milman_source_url : String
  construction_locator : String
  ramanujan_locator : String
  spectral_to_edge_locator : String
  local_representation_statement : String
  edge_convention_statement : String
  selected_edge_expansion_constant : StandardTseitinEdgeExpansionConstant
  selected_edge_expansion_constant_matches_candidate :
    selected_edge_expansion_constant =
      standardTseitinMorgensternQ2EdgeExpansionConstant
  source_indexing : Prop
  source_indexing_holds : source_indexing
  q2_ramanujan_source : Prop
  q2_ramanujan_source_holds : q2_ramanujan_source
  spectral_to_edge_expansion_source : Prop
  spectral_to_edge_expansion_source_holds :
    spectral_to_edge_expansion_source
  local_representation_match : Prop
  local_representation_match_holds : local_representation_match
  local_graph_family_facts_of_sources :
    source_indexing ->
    q2_ramanujan_source ->
    spectral_to_edge_expansion_source ->
    local_representation_match ->
      (forall i : Index, oneListedEdgePerUndirectedEdge (graph i).edges) /\
      standardThreeRegularFamily graph /\
      standardConnectedFamily graph /\
      (forall i : Index,
        standardEdgeExpansionAtLeast (graph i)
          selected_edge_expansion_constant)

def StandardTseitinMorgensternQ2GraphFamilyHardening.localGraphFamilyFacts
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    (packet : StandardTseitinMorgensternQ2GraphFamilyHardening graph) :
      (forall i : Index, oneListedEdgePerUndirectedEdge (graph i).edges) /\
      standardThreeRegularFamily graph /\
      standardConnectedFamily graph /\
      (forall i : Index,
        standardEdgeExpansionAtLeast (graph i)
          packet.selected_edge_expansion_constant) :=
  packet.local_graph_family_facts_of_sources
    packet.source_indexing_holds
    packet.q2_ramanujan_source_holds
    packet.spectral_to_edge_expansion_source_holds
    packet.local_representation_match_holds

def StandardTseitinMorgensternQ2GraphFamilyHardening.oneVariablePerUndirectedEdge
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    (packet : StandardTseitinMorgensternQ2GraphFamilyHardening graph) :
    forall i : Index, oneListedEdgePerUndirectedEdge (graph i).edges :=
  packet.localGraphFamilyFacts.1

def StandardTseitinMorgensternQ2GraphFamilyHardening.threeRegularFamily
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    (packet : StandardTseitinMorgensternQ2GraphFamilyHardening graph) :
    standardThreeRegularFamily graph :=
  packet.localGraphFamilyFacts.2.1

def StandardTseitinMorgensternQ2GraphFamilyHardening.connectedFamily
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    (packet : StandardTseitinMorgensternQ2GraphFamilyHardening graph) :
    standardConnectedFamily graph :=
  packet.localGraphFamilyFacts.2.2.1

def StandardTseitinMorgensternQ2GraphFamilyHardening.selectedEdgeExpansionFamily
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    (packet : StandardTseitinMorgensternQ2GraphFamilyHardening graph) :
    forall i : Index,
      standardEdgeExpansionAtLeast (graph i)
        packet.selected_edge_expansion_constant :=
  packet.localGraphFamilyFacts.2.2.2

theorem StandardTseitinMorgensternQ2GraphFamilyHardening.selectedCandidateEdgeExpansionFamily
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    (packet : StandardTseitinMorgensternQ2GraphFamilyHardening graph) :
    forall i : Index,
      standardEdgeExpansionAtLeast (graph i)
        standardTseitinMorgensternQ2EdgeExpansionConstant := by
  intro i
  simpa [packet.selected_edge_expansion_constant_matches_candidate] using
    packet.selectedEdgeExpansionFamily i

def StandardTseitinMorgensternQ2GraphFamilyHardening.toConstantEdgeExpansionFamily
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    (packet : StandardTseitinMorgensternQ2GraphFamilyHardening graph) :
    standardConstantEdgeExpansionFamily graph :=
  ⟨packet.selected_edge_expansion_constant,
    packet.selectedEdgeExpansionFamily⟩

def StandardTseitinMorgensternQ2GraphFamilyHardening.toBSWGraphFamilyPremise
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    (packet : StandardTseitinMorgensternQ2GraphFamilyHardening graph) :
    standardBSWGraphFamilyPremise graph :=
  ⟨packet.threeRegularFamily,
    packet.connectedFamily,
    packet.toConstantEdgeExpansionFamily⟩

theorem StandardTseitinMorgensternQ2GraphFamilyHardening.selected_cNum
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    (packet : StandardTseitinMorgensternQ2GraphFamilyHardening graph) :
    packet.selected_edge_expansion_constant.numerator = 1 := by
  rw [packet.selected_edge_expansion_constant_matches_candidate]
  rfl

theorem StandardTseitinMorgensternQ2GraphFamilyHardening.selected_cDen
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    (packet : StandardTseitinMorgensternQ2GraphFamilyHardening graph) :
    packet.selected_edge_expansion_constant.denominator = 12 := by
  rw [packet.selected_edge_expansion_constant_matches_candidate]
  rfl

/--
Local odd-charge packet for the selected q = 2 theorem surface.

This is intentionally not a source theorem packet.  Given nonempty graphs, the
canonical charge that marks vertex zero and no other vertex has odd total
charge.  The packet keeps the nonempty-graph guard explicit until the selected
source graph family is represented locally.
-/
structure StandardTseitinMorgensternQ2OddChargeFamily
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) where
  nonempty_graph_statement : String
  singleton_zero_charge_statement : String
  graph_nonempty : forall i : Index, 0 < (graph i).n
  charge_matches_singleton_zero :
    forall i : Index, charge i = standardSingletonZeroCharge

def StandardTseitinMorgensternQ2OddChargeFamily.oddTotalCharge
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool}
    (packet :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge) :
    forall i : Index, standardOddTotalCharge (graph i) (charge i) := by
  intro i
  simpa [packet.charge_matches_singleton_zero i] using
    standardOddTotalCharge_singletonZero_of_pos
      (G := graph i) (packet.graph_nonempty i)

theorem StandardTseitinMorgensternQ2OddChargeFamily.zeroFlippedEvenTotalCharge
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool}
    (packet :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge) :
    forall i : Index,
      standardEvenTotalCharge (graph i)
        (standardFlipChargeAt (charge i) 0) := by
  intro i
  rw [packet.charge_matches_singleton_zero i]
  exact standardEvenTotalCharge_flip_singletonZero_zero (graph i)

theorem StandardTseitinMorgensternQ2OddChargeFamily.zeroFlippedStandardCNFSatisfiable
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool}
    (packet :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge) :
    forall i : Index,
      Exists fun a : CNFModel.Assignment (graph i).edges.length =>
        CNFModel.cnfSat a
          (StandardTseitinCNFFormula (graph i)
            (standardFlipChargeAt (charge i) 0)) := by
  intro i
  rw [packet.charge_matches_singleton_zero i]
  exact
    exists_cnfSat_standardTseitinCNFFormula_flip_singletonZero_zero
      (graph i)

/-- Numerator of the selected q = 2 width-gap coefficient. -/
theorem standardTseitinMorgensternQ2WidthGapCoefficient_numerator :
    standardTseitinMorgensternQ2WidthGapCoefficient.numerator = 1 := rfl

/-- Denominator of the selected q = 2 width-gap coefficient. -/
theorem standardTseitinMorgensternQ2WidthGapCoefficient_denominator :
    standardTseitinMorgensternQ2WidthGapCoefficient.denominator = 72 := rfl

/-- Eventual cutoff for the selected q = 2 width-gap coefficient. -/
theorem standardTseitinMorgensternQ2WidthGapEventualThreshold_eq :
    standardTseitinMorgensternQ2WidthGapEventualThreshold = 432 := rfl

/--
Consumption packet connecting the Stage1731 normalized q = 2 expansion constant to
the Stage1730 width-gap coefficient surface.

This is the first point where the selected `1 / 12` constant is routed into the
BSW width-gap packet.  The remaining theorem truth stays source-side: the packet
requires a bridge from the normalized edge-expansion source fact to the BSW
middle-cut expansion source fact, plus the BSW width lower-bound, initial-width,
and additive-slack sources already required by Stage1730.
-/
structure StandardTseitinMorgensternQ2NormalizedWidthGapConsumption where
  normalization :
    StandardTseitinMorgensternQ2ExpansionConstantNormalization
  bsw_middle_cut_expansion_source : Prop
  bsw_middle_cut_expansion_source_of_normalized_edge_expansion :
    normalization.normalized_edge_expansion_source ->
      bsw_middle_cut_expansion_source
  tseitin_width_lower_bound_source : Prop
  tseitin_width_lower_bound_source_holds : tseitin_width_lower_bound_source
  initial_width_loss_source : Prop
  initial_width_loss_source_holds : initial_width_loss_source
  additive_slack_absorption_source : Prop
  additive_slack_absorption_source_holds : additive_slack_absorption_source
  linear_width_gap_target : Prop
  linear_width_gap_target_of_sources :
    bsw_middle_cut_expansion_source ->
    tseitin_width_lower_bound_source ->
    initial_width_loss_source ->
    additive_slack_absorption_source ->
    linear_width_gap_target
  width_gap_accounting_target : Prop
  width_gap_accounting_target_of_linear_gap :
    linear_width_gap_target -> width_gap_accounting_target

def StandardTseitinMorgensternQ2NormalizedWidthGapConsumption.toWidthGapExpansionCoefficient
    (packet : StandardTseitinMorgensternQ2NormalizedWidthGapConsumption) :
    StandardTseitinBSWWidthGapExpansionCoefficient where
  source_url :=
    standardTseitinMorgensternQ2RamanujanSourceURL ++ "; " ++
      standardTseitinAlonMilmanEdgeExpansionSourceURL ++ "; " ++
      standardTseitinBSWLineCountSourceURL
  bsw_expansion_definition_locator :=
    standardTseitinBSWTseitinWidthLocator
  bsw_tseitin_width_locator :=
    standardTseitinBSWTseitinWidthLocator
  expansion_rate_constant_locator :=
    standardTseitinMorgensternQ2ExpansionConstantNormalizationLocator
  formula_width_locator :=
    "Standard 3-regular Tseitin clauses have initial clause width at most 3."
  width_gap_coefficient_locator :=
    standardTseitinBSWWidthGapExpansionCoefficientLocator
  edge_expansion_constant :=
    packet.normalization.selected_edge_expansion_constant
  width_gap_coefficient :=
    packet.normalization.selected_edge_expansion_constant.widthGapCoefficient
  width_gap_coefficient_matches_candidate := rfl
  width_gap_eventual_threshold :=
    packet.normalization.selected_edge_expansion_constant.widthGapEventualThreshold
  width_gap_eventual_threshold_matches_candidate := rfl
  bsw_middle_cut_expansion_statement :=
    "Use the normalized q=2 edge-expansion source fact to supply the BSW " ++
    "middle-cut expansion source premise."
  tseitin_width_lower_bound_statement :=
    "Apply BSW Theorem 4.4 after the middle-cut expansion source premise."
  initial_width_loss_statement :=
    "The standard q=2/Morgenstern family is 3-regular, so initial Tseitin " ++
    "clauses have width at most 3."
  additive_slack_absorption_statement :=
    "Absorb Stage1729 additive slack with the Stage1730 cutoff 36 * c.denominator."
  linear_width_gap_target_statement :=
    "With c = 1/12, the source-side eventual width-gap coefficient is 1/72."
  coefficient_decision_statement :=
    "Stage1732 consumes the Stage1731 normalized constant through the Stage1730 width-gap packet."
  side_conditions_statement :=
    "Morgenstern, Alon-Milman, BSW, and eventual-threshold side conditions " ++
    "remain source-side."
  bsw_middle_cut_expansion_source :=
    packet.bsw_middle_cut_expansion_source
  bsw_middle_cut_expansion_source_holds :=
    packet.bsw_middle_cut_expansion_source_of_normalized_edge_expansion
      packet.normalization.toEdgeExpansionSource
  tseitin_width_lower_bound_source :=
    packet.tseitin_width_lower_bound_source
  tseitin_width_lower_bound_source_holds :=
    packet.tseitin_width_lower_bound_source_holds
  initial_width_loss_source :=
    packet.initial_width_loss_source
  initial_width_loss_source_holds :=
    packet.initial_width_loss_source_holds
  additive_slack_absorption_source :=
    packet.additive_slack_absorption_source
  additive_slack_absorption_source_holds :=
    packet.additive_slack_absorption_source_holds
  linear_width_gap_target :=
    packet.linear_width_gap_target
  linear_width_gap_target_of_sources :=
    packet.linear_width_gap_target_of_sources
  width_gap_accounting_target :=
    packet.width_gap_accounting_target
  width_gap_accounting_target_of_linear_gap :=
    packet.width_gap_accounting_target_of_linear_gap

def StandardTseitinMorgensternQ2NormalizedWidthGapConsumption.toWidthGapAccountingTarget
    (packet : StandardTseitinMorgensternQ2NormalizedWidthGapConsumption) :
    packet.width_gap_accounting_target :=
  packet.toWidthGapExpansionCoefficient.toWidthGapAccountingTarget

/-- Positive rational coefficient for natural-log size lower bounds. -/
structure StandardTseitinNaturalLogSizeCoefficient where
  numerator : Nat
  denominator : Nat
  positive : 0 < numerator /\ 0 < denominator

/--
Conservative natural-log size coefficient induced by the selected q = 2
width-gap coefficient.

Stage1732 gives `gamma = 1 / 72`.  Substituting into the Stage1729 inversion shape
`ln S >= (gap - 3)^2 / (8*n)` gives the source-side coefficient
`gamma^2 / 8 = 1 / (72^2 * 8) = 1 / 41472`.
-/
def standardTseitinMorgensternQ2NaturalLogSizeCoefficient :
    StandardTseitinNaturalLogSizeCoefficient where
  numerator := 1
  denominator := 41472
  positive := by
    constructor <;> decide

/-- Numerator of the selected q = 2 natural-log size coefficient. -/
theorem standardTseitinMorgensternQ2NaturalLogSizeCoefficient_numerator :
    standardTseitinMorgensternQ2NaturalLogSizeCoefficient.numerator = 1 := rfl

/-- Denominator of the selected q = 2 natural-log size coefficient. -/
theorem standardTseitinMorgensternQ2NaturalLogSizeCoefficient_denominator :
    standardTseitinMorgensternQ2NaturalLogSizeCoefficient.denominator = 41472 := rfl

/-- Arithmetic denominator check for the Stage1733 log-size coefficient. -/
theorem standardTseitinMorgensternQ2NaturalLogSizeCoefficient_denominator_arithmetic :
    72 * 72 * 8 = 41472 := by
  decide

/-- Locator for the Stage1733 natural-log coefficient extraction. -/
def standardTseitinMorgensternQ2NaturalLogSizeCoefficientLocator : String :=
  "Substitute gamma = 1/72 into the Stage1729 inversion shell " ++
  "ln S >= (gap - 3)^2/(8*n); the conservative natural-log " ++
  "coefficient is 1/(72^2*8) = 1/41472."

/--
Consumption packet connecting the Stage1732 width-gap accounting target to the
Stage1733 natural-log coefficient.

The packet records the coefficient extraction and the source-side arithmetic
obligations only.  It does not prove the BSW real-analysis step locally and it
does not discharge the later base-2, Nat-floor, formula-size, or eventual
threshold conversions.
-/
structure StandardTseitinMorgensternQ2NaturalLogSizeCoefficientExtraction where
  width_gap_consumption :
    StandardTseitinMorgensternQ2NormalizedWidthGapConsumption
  width_gap_coefficient : StandardTseitinEdgeExpansionConstant
  width_gap_coefficient_matches_candidate :
    width_gap_coefficient =
      standardTseitinMorgensternQ2WidthGapCoefficient
  natural_log_size_coefficient : StandardTseitinNaturalLogSizeCoefficient
  natural_log_size_coefficient_matches_candidate :
    natural_log_size_coefficient =
      standardTseitinMorgensternQ2NaturalLogSizeCoefficient
  width_gap_accounting_statement : String
  stage1729_inversion_statement : String
  gamma_square_divide_statement : String
  base_two_nat_blocker_statement : String
  side_conditions_statement : String
  stage1729_inversion_source : Prop
  stage1729_inversion_source_holds : stage1729_inversion_source
  gamma_square_divide_arithmetic_source : Prop
  gamma_square_divide_arithmetic_source_holds :
    gamma_square_divide_arithmetic_source
  natural_log_size_target : Prop
  natural_log_size_target_of_sources :
    width_gap_consumption.width_gap_accounting_target ->
    stage1729_inversion_source ->
    gamma_square_divide_arithmetic_source ->
    natural_log_size_target
  base_two_nat_conversion_target : Prop
  eventual_threshold_side_conditions : Prop

def StandardTseitinMorgensternQ2NaturalLogSizeCoefficientExtraction.toWidthGapAccountingTarget
    (packet :
      StandardTseitinMorgensternQ2NaturalLogSizeCoefficientExtraction) :
    packet.width_gap_consumption.width_gap_accounting_target :=
  packet.width_gap_consumption.toWidthGapAccountingTarget

def StandardTseitinMorgensternQ2NaturalLogSizeCoefficientExtraction.toNaturalLogSizeTarget
    (packet :
      StandardTseitinMorgensternQ2NaturalLogSizeCoefficientExtraction) :
    packet.natural_log_size_target :=
  packet.natural_log_size_target_of_sources
    packet.toWidthGapAccountingTarget
    packet.stage1729_inversion_source_holds
    packet.gamma_square_divide_arithmetic_source_holds

/-- Positive rational coefficient for base-2 Nat exponent lower bounds. -/
structure StandardTseitinBaseTwoNatExponentCoefficient where
  numerator : Nat
  denominator : Nat
  positive : 0 < numerator /\ 0 < denominator

/--
Conservative base-2 Nat exponent coefficient induced by the Stage1733 natural-log
coefficient.

The selected denominator is unchanged from the natural-log coefficient:
`ln 2 <= 1` makes `2^(n/41472)` no larger than `exp(n/41472)`, and the local
Nat exponent shape floors to `(1 * n) / 41472`.
-/
def standardTseitinMorgensternQ2BaseTwoNatExponentCoefficient :
    StandardTseitinBaseTwoNatExponentCoefficient where
  numerator := 1
  denominator := 41472
  positive := by
    constructor <;> decide

/-- Numerator of the selected q = 2 base-2 Nat exponent coefficient. -/
theorem standardTseitinMorgensternQ2BaseTwoNatExponentCoefficient_numerator :
    standardTseitinMorgensternQ2BaseTwoNatExponentCoefficient.numerator = 1 := rfl

/-- Denominator of the selected q = 2 base-2 Nat exponent coefficient. -/
theorem standardTseitinMorgensternQ2BaseTwoNatExponentCoefficient_denominator :
    standardTseitinMorgensternQ2BaseTwoNatExponentCoefficient.denominator = 41472 := rfl

/-- The base-2 coefficient keeps the Stage1733 natural-log denominator. -/
theorem standardTseitinMorgensternQ2BaseTwoNatExponentCoefficient_denominator_eq_log :
    standardTseitinMorgensternQ2BaseTwoNatExponentCoefficient.denominator =
      standardTseitinMorgensternQ2NaturalLogSizeCoefficient.denominator := rfl

/-- Build a formula-size source threshold from a stored base-2 Nat coefficient. -/
def StandardTseitinBaseTwoNatExponentCoefficient.toFormulaSizeThreshold
    (coefficient : StandardTseitinBaseTwoNatExponentCoefficient)
    (n0 : Nat) (threshold : Nat -> Nat) (sourceOmegaStatement : Prop) :
    CNFResolution.ResolutionAsymptoticExponentialThreshold where
  sizeParameterKind := standardTseitinBSWSourceSizeParameterKind
  cNum := coefficient.numerator
  cDen := coefficient.denominator
  n0 := n0
  threshold := threshold
  constantPositive := coefficient.positive
  sourceOmegaStatement := sourceOmegaStatement

/-- Formula-size threshold template for the q = 2 base-2 Nat coefficient. -/
def standardTseitinMorgensternQ2BaseTwoNatFormulaThreshold
    (n0 : Nat) (threshold : Nat -> Nat) (sourceOmegaStatement : Prop) :
    CNFResolution.ResolutionAsymptoticExponentialThreshold :=
  standardTseitinMorgensternQ2BaseTwoNatExponentCoefficient.toFormulaSizeThreshold
    n0 threshold sourceOmegaStatement

theorem standardTseitinMorgensternQ2BaseTwoNatFormulaThreshold_cNum
    (n0 : Nat) (threshold : Nat -> Nat) (sourceOmegaStatement : Prop) :
    (standardTseitinMorgensternQ2BaseTwoNatFormulaThreshold
      n0 threshold sourceOmegaStatement).cNum = 1 := rfl

theorem standardTseitinMorgensternQ2BaseTwoNatFormulaThreshold_cDen
    (n0 : Nat) (threshold : Nat -> Nat) (sourceOmegaStatement : Prop) :
    (standardTseitinMorgensternQ2BaseTwoNatFormulaThreshold
      n0 threshold sourceOmegaStatement).cDen = 41472 := rfl

/-- Locator for the Stage1734 base-2/Nat threshold conversion target. -/
def standardTseitinMorgensternQ2BaseTwoNatThresholdConversionLocator : String :=
  "Convert the Stage1733 natural-log target ln S >= n/41472 to the local " ++
  "base-2 Nat exponent shape 2^((1*n)/41472), using ln 2 <= 1, Nat " ++
  "floor/division monotonicity, and eventual-threshold slack."

/--
Source-side conversion packet from the Stage1733 natural-log coefficient to the
local base-2 Nat threshold shape.

This packet selects the conservative `cNum = 1`, `cDen = 41472` exponent
coefficient and feeds the existing `base_two_nat_conversion_target` exposed by
Stage1733/Stage1729.  The analytic logarithm conversion, Nat floor/division accounting,
and eventual-threshold slack remain explicit source propositions.  The
graph/formula-size rescaling is intentionally left as a separate downstream
target so it is not hidden inside base conversion.
-/
structure StandardTseitinMorgensternQ2BaseTwoNatThresholdConversion where
  natural_log_extraction :
    StandardTseitinMorgensternQ2NaturalLogSizeCoefficientExtraction
  base_two_nat_exponent_coefficient :
    StandardTseitinBaseTwoNatExponentCoefficient
  base_two_nat_exponent_coefficient_matches_candidate :
    base_two_nat_exponent_coefficient =
      standardTseitinMorgensternQ2BaseTwoNatExponentCoefficient
  formula_threshold :
    CNFResolution.ResolutionAsymptoticExponentialThreshold
  formula_threshold_kind_is_formula_size :
    formula_threshold.sizeParameterKind = standardTseitinBSWSourceSizeParameterKind
  formula_threshold_cNum_matches_coefficient :
    formula_threshold.cNum = base_two_nat_exponent_coefficient.numerator
  formula_threshold_cDen_matches_coefficient :
    formula_threshold.cDen = base_two_nat_exponent_coefficient.denominator
  log_to_base_two_statement : String
  nat_floor_division_statement : String
  eventual_threshold_statement : String
  graph_formula_rescaling_deferred_statement : String
  log_to_base_two_source : Prop
  log_to_base_two_source_holds : log_to_base_two_source
  nat_floor_division_source : Prop
  nat_floor_division_source_holds : nat_floor_division_source
  eventual_threshold_source : Prop
  eventual_threshold_source_holds : eventual_threshold_source
  base_two_nat_conversion_target_of_sources :
    natural_log_extraction.natural_log_size_target ->
    log_to_base_two_source ->
    nat_floor_division_source ->
    eventual_threshold_source ->
    natural_log_extraction.base_two_nat_conversion_target
  formula_threshold_concrete_lower_bound_of_base_conversion :
    natural_log_extraction.base_two_nat_conversion_target ->
      formula_threshold.concreteLowerBound
  graph_formula_rescaling_target : Prop

def StandardTseitinMorgensternQ2BaseTwoNatThresholdConversion.toBaseTwoNatConversionTarget
    (packet :
      StandardTseitinMorgensternQ2BaseTwoNatThresholdConversion) :
    packet.natural_log_extraction.base_two_nat_conversion_target :=
  packet.base_two_nat_conversion_target_of_sources
    packet.natural_log_extraction.toNaturalLogSizeTarget
    packet.log_to_base_two_source_holds
    packet.nat_floor_division_source_holds
    packet.eventual_threshold_source_holds

def StandardTseitinMorgensternQ2BaseTwoNatThresholdConversion.toFormulaThresholdConcreteLowerBound
    (packet :
      StandardTseitinMorgensternQ2BaseTwoNatThresholdConversion) :
    packet.formula_threshold.concreteLowerBound :=
  packet.formula_threshold_concrete_lower_bound_of_base_conversion
    packet.toBaseTwoNatConversionTarget

/-- Locator for the expansion-rate constant used by the Tseitin width lower bound. -/
def standardTseitinBSWExpansionRateConstantLocator : String :=
  "Ben-Sasson/Wigderson, Short Proofs are Narrow, Definition 4.3, " ++
  "Theorem 4.4, and Corollary 4.5; combine with the selected q=2 " ++
  "Ramanujan-family expansion constant."

/-- Locator for the formula-size parameter conversion in the Tseitin threshold. -/
def standardTseitinBSWFormulaSizeConversionLocator : String :=
  "Ben-Sasson/Wigderson, Short Proofs are Narrow, Lemma 4.2 and " ++
  "Corollary 4.5; align |tau(G,f)| with the local standard Tseitin " ++
  "formula-size parameter."

/-- Locator for converting the source exponential statement to the local base-2 form. -/
def standardTseitinBSWBaseConversionLocator : String :=
  "Convert BSW exp(Omega(n)) notation into the local base-2 threshold " ++
  "2^((cNum * n) / cDen), preserving explicit constants."

/-- Locator for the eventual threshold required by the concrete lower-bound packet. -/
def standardTseitinBSWEventualThresholdLocator : String :=
  "Extract the large-enough n0 for the combined BSW width-size, expansion, " ++
  "formula-size, and base-conversion inequalities."

/--
Standard graph-vertex threshold interpretation for the Morgenstern q = 2 BSW
lane.

The source asymptotic threshold and eventual applicability facts stay
source-side.  Locally, this constructor fixes the source parameter to the
standard graph vertex count `(graph i).n` and exposes the exact threshold-match
equation required by the trace assembly step.
-/
def standardTseitinMorgensternQ2GraphVertexThresholdInterpretation
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (sourceThreshold : CNFResolution.ResolutionAsymptoticExponentialThreshold)
    (hthreshold :
      forall i : Index,
        threshold i = sourceThreshold.threshold (graph i).n)
    (heventual :
      forall i : Index,
        sourceThreshold.appliesAt (graph i).n) :
    CNFResolution.ResolutionFamilyThresholdInterpretation
      (StandardTseitinResolutionFamilyTarget graph charge threshold) where
  sourceThreshold := sourceThreshold
  parameter := fun i => (graph i).n
  threshold_matches := hthreshold
  parameters_eventual := heventual

theorem standardTseitinMorgensternQ2GraphVertexThresholdInterpretation_parameter
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {sourceThreshold : CNFResolution.ResolutionAsymptoticExponentialThreshold}
    {hthreshold :
      forall i : Index,
        threshold i = sourceThreshold.threshold (graph i).n}
    {heventual :
      forall i : Index,
        sourceThreshold.appliesAt (graph i).n} :
    forall i : Index,
      (standardTseitinMorgensternQ2GraphVertexThresholdInterpretation
        graph charge threshold sourceThreshold hthreshold heventual).parameter i =
      (graph i).n := by
  intro _
  rfl

/--
Parameter-alignment packet for applying a BSW formula-size source threshold at
the selected Morgenstern q = 2 graph-vertex parameter.

The source theorem is recorded as a formula-size bound. The selected local
threshold interpretation uses graph vertex count. This packet keeps the
formula-size/graph-vertex bridge explicit instead of hiding it inside the final
source lower-bound application.
-/
structure StandardTseitinMorgensternQ2ParameterAlignment
    {Index : Type}
    (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (thresholdInterpretation :
      CNFResolution.ResolutionFamilyThresholdInterpretation
        (StandardTseitinResolutionFamilyTarget graph charge threshold)) where
  source_parameter_kind_is_formula_size :
    thresholdInterpretation.sourceThreshold.sizeParameterKind =
      standardTseitinBSWSourceSizeParameterKind
  source_parameter_is_graph_vertex_count :
    forall i : Index, thresholdInterpretation.parameter i = (graph i).n
  formula_size_to_graph_vertex_parameter_bridge : Prop
  formula_size_to_graph_vertex_parameter_bridge_holds :
    formula_size_to_graph_vertex_parameter_bridge

/--
Local clause-count bridge used to relate the BSW formula-size parameter to the
selected graph-vertex parameter for 3-regular standard Tseitin formulas.
-/
def standardTseitinMorgensternQ2FormulaSizeGraphVertexBridge
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) : Prop :=
  forall i : Index,
    (StandardTseitinCNFFormula (graph i) (charge i)).length =
      (graph i).n * 4

theorem standardTseitinMorgensternQ2GraphVertex_le_formulaClauseCount_of_bridge
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool}
    (hbridge :
      standardTseitinMorgensternQ2FormulaSizeGraphVertexBridge graph charge) :
    forall i : Index,
      (graph i).n <= (StandardTseitinCNFFormula (graph i) (charge i)).length := by
  intro i
  calc
    (graph i).n = (graph i).n * 1 := by simp
    _ <= (graph i).n * 4 := Nat.mul_le_mul_left (graph i).n (by decide)
    _ = (StandardTseitinCNFFormula (graph i) (charge i)).length :=
        (hbridge i).symm

theorem standardTseitinMorgensternQ2FormulaSizeGraphVertexBridge_of_threeRegularFamily
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool}
    (hreg : standardThreeRegularFamily graph) :
    standardTseitinMorgensternQ2FormulaSizeGraphVertexBridge graph charge := by
  intro i
  exact StandardTseitinCNFFormula_length_of_standardThreeRegular (hreg i)

def standardTseitinMorgensternQ2ParameterAlignment_of_threeRegularFamily
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {thresholdInterpretation :
      CNFResolution.ResolutionFamilyThresholdInterpretation
        (StandardTseitinResolutionFamilyTarget graph charge threshold)}
    (hkind :
      thresholdInterpretation.sourceThreshold.sizeParameterKind =
        standardTseitinBSWSourceSizeParameterKind)
    (hparameter :
      forall i : Index, thresholdInterpretation.parameter i = (graph i).n)
    (hreg : standardThreeRegularFamily graph) :
    StandardTseitinMorgensternQ2ParameterAlignment graph charge threshold
      thresholdInterpretation where
  source_parameter_kind_is_formula_size := hkind
  source_parameter_is_graph_vertex_count := hparameter
  formula_size_to_graph_vertex_parameter_bridge :=
    standardTseitinMorgensternQ2FormulaSizeGraphVertexBridge graph charge
  formula_size_to_graph_vertex_parameter_bridge_holds :=
    standardTseitinMorgensternQ2FormulaSizeGraphVertexBridge_of_threeRegularFamily
      hreg

/--
Source-side lower-bound premise stated at local formula clause count, before it
is downgraded to the selected graph-vertex threshold.
-/
def StandardTseitinMorgensternQ2FormulaSizeSourceLineLowerBoundPremise
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (thresholdInterpretation :
      CNFResolution.ResolutionFamilyThresholdInterpretation
        (StandardTseitinResolutionFamilyTarget graph charge threshold))
    (sourceLineCount :
      CNFResolution.ResolutionFamilySourceLineCount
        (StandardTseitinResolutionFamilyTarget graph charge threshold)) : Prop :=
  forall (i : Index)
    (r : CNFResolution.ResolutionRefutation
      ((StandardTseitinResolutionFamilyTarget graph charge threshold).phi i)),
    thresholdInterpretation.sourceThreshold.threshold
        ((StandardTseitinCNFFormula (graph i) (charge i)).length) <=
      sourceLineCount i r

/--
Threshold-conservativity packet for applying a formula-size BSW threshold to
the selected graph-vertex interpretation.

The local clause-count bridge proves formula size is `4 * |V|` for the
3-regular standard encoding. This packet records the remaining monotonicity and
eventual-applicability obligations needed to safely use the smaller graph
parameter threshold.
-/
structure StandardTseitinMorgensternQ2ThresholdConservativity
    {Index : Type}
    (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (thresholdInterpretation :
      CNFResolution.ResolutionFamilyThresholdInterpretation
        (StandardTseitinResolutionFamilyTarget graph charge threshold))
    (parameterAlignment :
      StandardTseitinMorgensternQ2ParameterAlignment graph charge threshold
        thresholdInterpretation) where
  formula_size_bridge :
    standardTseitinMorgensternQ2FormulaSizeGraphVertexBridge graph charge
  source_threshold_monotone :
    forall a b : Nat, a <= b ->
      thresholdInterpretation.sourceThreshold.threshold a <=
        thresholdInterpretation.sourceThreshold.threshold b
  source_applies_at_formula_clause_count :
    forall i : Index,
      thresholdInterpretation.sourceThreshold.appliesAt
        ((StandardTseitinCNFFormula (graph i) (charge i)).length)

theorem StandardTseitinMorgensternQ2ThresholdConservativity.toInterpretedSourceLineLowerBound
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {thresholdInterpretation :
      CNFResolution.ResolutionFamilyThresholdInterpretation
        (StandardTseitinResolutionFamilyTarget graph charge threshold)}
    {parameterAlignment :
      StandardTseitinMorgensternQ2ParameterAlignment graph charge threshold
        thresholdInterpretation}
    {sourceLineCount :
      CNFResolution.ResolutionFamilySourceLineCount
        (StandardTseitinResolutionFamilyTarget graph charge threshold)}
    (conservativity :
      StandardTseitinMorgensternQ2ThresholdConservativity graph charge
        threshold thresholdInterpretation parameterAlignment)
    (hformula :
      StandardTseitinMorgensternQ2FormulaSizeSourceLineLowerBoundPremise
        graph charge threshold thresholdInterpretation sourceLineCount) :
    CNFResolution.ResolutionFamilyInterpretedSourceLineLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      thresholdInterpretation
      sourceLineCount := by
  intro i r
  have hparam :
      thresholdInterpretation.parameter i = (graph i).n :=
    parameterAlignment.source_parameter_is_graph_vertex_count i
  have hleFormula :
      thresholdInterpretation.parameter i <=
        (StandardTseitinCNFFormula (graph i) (charge i)).length := by
    rw [hparam]
    exact
      standardTseitinMorgensternQ2GraphVertex_le_formulaClauseCount_of_bridge
        conservativity.formula_size_bridge i
  exact Nat.le_trans
    (conservativity.source_threshold_monotone
      (thresholdInterpretation.parameter i)
      ((StandardTseitinCNFFormula (graph i) (charge i)).length)
      hleFormula)
    (hformula i r)

/--
Graph-vertex threshold obtained by evaluating a formula-size BSW threshold at
the local 3-regular Tseitin clause-count scale.

This is the Stage1704 constants-extraction boundary: it avoids treating
`threshold n` as interchangeable with `threshold (4 * n)` for an arbitrary
threshold function.  The source formula-size theorem remains external; locally
we only make the rescaling explicit.
-/
def standardTseitinMorgensternQ2GraphRescaledThreshold
    (formulaThreshold :
      CNFResolution.ResolutionAsymptoticExponentialThreshold) :
    CNFResolution.ResolutionAsymptoticExponentialThreshold where
  sizeParameterKind :=
    CNFResolution.ResolutionSourceSizeParameterKind.graphVertexCount
  cNum := formulaThreshold.cNum
  cDen := formulaThreshold.cDen
  n0 := formulaThreshold.n0
  threshold := fun n => formulaThreshold.threshold (n * 4)
  constantPositive := formulaThreshold.constantPositive
  sourceOmegaStatement := formulaThreshold.sourceOmegaStatement

theorem standardTseitinMorgensternQ2GraphRescaledThreshold_kind
    (formulaThreshold :
      CNFResolution.ResolutionAsymptoticExponentialThreshold) :
    (standardTseitinMorgensternQ2GraphRescaledThreshold
      formulaThreshold).sizeParameterKind =
      CNFResolution.ResolutionSourceSizeParameterKind.graphVertexCount := by
  rfl

/--
Boundary packet for the Stage1704 graph-rescaled threshold route.  The original
source threshold is still the BSW formula-size threshold; only the derived local
target is indexed by graph vertex count.
-/
structure StandardTseitinMorgensternQ2GraphRescaledThresholdBoundary
    (formulaThreshold :
      CNFResolution.ResolutionAsymptoticExponentialThreshold) where
  formula_threshold_kind_is_formula_size :
    formulaThreshold.sizeParameterKind = standardTseitinBSWSourceSizeParameterKind

theorem standardTseitinMorgensternQ2GraphRescaledThreshold_at
    (formulaThreshold :
      CNFResolution.ResolutionAsymptoticExponentialThreshold) (n : Nat) :
    (standardTseitinMorgensternQ2GraphRescaledThreshold
      formulaThreshold).threshold n =
      formulaThreshold.threshold (n * 4) := by
  rfl

theorem standardTseitinMorgensternQ2GraphRescaledThreshold_formula_appliesAt
    (formulaThreshold :
      CNFResolution.ResolutionAsymptoticExponentialThreshold) {n : Nat}
    (h :
      (standardTseitinMorgensternQ2GraphRescaledThreshold
        formulaThreshold).appliesAt n) :
    formulaThreshold.appliesAt (n * 4) := by
  have hnle : n <= n * 4 := by
    calc
      n = n * 1 := by simp
      _ <= n * 4 := Nat.mul_le_mul_left n (by decide)
  have hn0 : formulaThreshold.n0 <= n := by
    simpa [CNFResolution.ResolutionAsymptoticExponentialThreshold.appliesAt,
      standardTseitinMorgensternQ2GraphRescaledThreshold] using h
  simpa [CNFResolution.ResolutionAsymptoticExponentialThreshold.appliesAt] using
    Nat.le_trans hn0 hnle

theorem standardTseitinMorgensternQ2GraphRescaledThreshold_concreteLowerBound
    (formulaThreshold :
      CNFResolution.ResolutionAsymptoticExponentialThreshold)
    (hconcrete : formulaThreshold.concreteLowerBound) :
    (standardTseitinMorgensternQ2GraphRescaledThreshold
      formulaThreshold).concreteLowerBound := by
  intro n hn
  have hsourceApplies : formulaThreshold.appliesAt (n * 4) :=
    standardTseitinMorgensternQ2GraphRescaledThreshold_formula_appliesAt
      formulaThreshold hn
  have hsource :
      2 ^ ((formulaThreshold.cNum * (n * 4)) / formulaThreshold.cDen) <=
        formulaThreshold.threshold (n * 4) :=
    hconcrete (n * 4) hsourceApplies
  have hnle : n <= n * 4 := by
    calc
      n = n * 1 := by simp
      _ <= n * 4 := Nat.mul_le_mul_left n (by decide)
  have hmul :
      formulaThreshold.cNum * n <= formulaThreshold.cNum * (n * 4) :=
    Nat.mul_le_mul_left formulaThreshold.cNum hnle
  have hdiv :
      (formulaThreshold.cNum * n) / formulaThreshold.cDen <=
        (formulaThreshold.cNum * (n * 4)) / formulaThreshold.cDen :=
    Nat.div_le_div_right hmul
  have hpow :
      2 ^ ((formulaThreshold.cNum * n) / formulaThreshold.cDen) <=
        2 ^ ((formulaThreshold.cNum * (n * 4)) / formulaThreshold.cDen) :=
    Nat.pow_le_pow_right (by decide) hdiv
  exact Nat.le_trans hpow (by
    simpa [standardTseitinMorgensternQ2GraphRescaledThreshold] using hsource)

/--
Selected graph-vertex interpretation whose numeric target is the original
formula-size source threshold evaluated at the checked `4 * |V|` scale.
-/
def standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (formulaThreshold :
      CNFResolution.ResolutionAsymptoticExponentialThreshold)
    (hthreshold :
      forall i : Index,
        threshold i = formulaThreshold.threshold ((graph i).n * 4))
    (heventual :
      forall i : Index,
        (standardTseitinMorgensternQ2GraphRescaledThreshold
          formulaThreshold).appliesAt (graph i).n) :
    CNFResolution.ResolutionFamilyThresholdInterpretation
      (StandardTseitinResolutionFamilyTarget graph charge threshold) where
  sourceThreshold :=
    standardTseitinMorgensternQ2GraphRescaledThreshold formulaThreshold
  parameter := fun i => (graph i).n
  threshold_matches := by
    intro i
    exact hthreshold i
  parameters_eventual := heventual

/-- Locator for the Stage1735 graph/formula threshold rescaling target. -/
def standardTseitinMorgensternQ2GraphFormulaThresholdRescalingLocator : String :=
  "Use the existing graph-rescaled threshold boundary: the source formula-size " ++
  "threshold is evaluated at 4 * graph.n, while the local graph-vertex " ++
  "exponent keeps the selected cNum/cDen under monotonicity of n <= 4*n."

/--
Consumption packet connecting the Stage1734 base-2/Nat conversion to the existing
graph-rescaled threshold boundary.

The existing graph-rescaled theorem proves that a formula-size concrete lower
bound transfers to the threshold `n ↦ formulaThreshold.threshold (n * 4)`
without weakening `cNum/cDen`: the exponent at graph-vertex scale is smaller
than the source exponent at formula-size scale because `n <= n * 4`.  This
packet makes that consumption point explicit and discharges the Stage1734 deferred
`graph_formula_rescaling_target` from the graph-rescaled concrete lower bound.
-/
structure StandardTseitinMorgensternQ2GraphFormulaThresholdRescaling
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat) where
  base_conversion :
    StandardTseitinMorgensternQ2BaseTwoNatThresholdConversion
  graph_rescaling_locator : String
  existing_graph_rescaled_threshold_statement : String
  coefficient_preservation_statement : String
  formula_size_boundary_statement : String
  eventual_threshold_statement : String
  target_threshold_matches_graph_rescaled :
    forall i : Index,
      threshold i =
        base_conversion.formula_threshold.threshold ((graph i).n * 4)
  graph_rescaled_eventual :
    forall i : Index,
      (standardTseitinMorgensternQ2GraphRescaledThreshold
        base_conversion.formula_threshold).appliesAt (graph i).n
  graph_formula_rescaling_target_of_graph_rescaled_concrete_lower_bound :
    (standardTseitinMorgensternQ2GraphRescaledThreshold
      base_conversion.formula_threshold).concreteLowerBound ->
        base_conversion.graph_formula_rescaling_target

def StandardTseitinMorgensternQ2GraphFormulaThresholdRescaling.graphRescaledThreshold
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (packet :
      StandardTseitinMorgensternQ2GraphFormulaThresholdRescaling
        graph charge threshold) :
    CNFResolution.ResolutionAsymptoticExponentialThreshold :=
  standardTseitinMorgensternQ2GraphRescaledThreshold
    packet.base_conversion.formula_threshold

def StandardTseitinMorgensternQ2GraphFormulaThresholdRescaling.thresholdInterpretation
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (packet :
      StandardTseitinMorgensternQ2GraphFormulaThresholdRescaling
        graph charge threshold) :
    CNFResolution.ResolutionFamilyThresholdInterpretation
      (StandardTseitinResolutionFamilyTarget graph charge threshold) :=
  standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
    graph charge threshold packet.base_conversion.formula_threshold
    packet.target_threshold_matches_graph_rescaled
    packet.graph_rescaled_eventual

def StandardTseitinMorgensternQ2GraphFormulaThresholdRescaling.toGraphRescaledConcreteLowerBound
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (packet :
      StandardTseitinMorgensternQ2GraphFormulaThresholdRescaling
        graph charge threshold) :
    packet.graphRescaledThreshold.concreteLowerBound :=
  standardTseitinMorgensternQ2GraphRescaledThreshold_concreteLowerBound
    packet.base_conversion.formula_threshold
    packet.base_conversion.toFormulaThresholdConcreteLowerBound

def StandardTseitinMorgensternQ2GraphFormulaThresholdRescaling.toGraphFormulaRescalingTarget
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (packet :
      StandardTseitinMorgensternQ2GraphFormulaThresholdRescaling
        graph charge threshold) :
    packet.base_conversion.graph_formula_rescaling_target :=
  packet.graph_formula_rescaling_target_of_graph_rescaled_concrete_lower_bound
    packet.toGraphRescaledConcreteLowerBound

theorem StandardTseitinMorgensternQ2GraphFormulaThresholdRescaling.graphRescaled_cNum
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (packet :
      StandardTseitinMorgensternQ2GraphFormulaThresholdRescaling
        graph charge threshold) :
    packet.graphRescaledThreshold.cNum = 1 := by
  change packet.base_conversion.formula_threshold.cNum = 1
  calc
    packet.base_conversion.formula_threshold.cNum =
        packet.base_conversion.base_two_nat_exponent_coefficient.numerator :=
      packet.base_conversion.formula_threshold_cNum_matches_coefficient
    _ = standardTseitinMorgensternQ2BaseTwoNatExponentCoefficient.numerator := by
      rw [packet.base_conversion.base_two_nat_exponent_coefficient_matches_candidate]
    _ = 1 := rfl

theorem StandardTseitinMorgensternQ2GraphFormulaThresholdRescaling.graphRescaled_cDen
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (packet :
      StandardTseitinMorgensternQ2GraphFormulaThresholdRescaling
        graph charge threshold) :
    packet.graphRescaledThreshold.cDen = 41472 := by
  change packet.base_conversion.formula_threshold.cDen = 41472
  calc
    packet.base_conversion.formula_threshold.cDen =
        packet.base_conversion.base_two_nat_exponent_coefficient.denominator :=
      packet.base_conversion.formula_threshold_cDen_matches_coefficient
    _ = standardTseitinMorgensternQ2BaseTwoNatExponentCoefficient.denominator := by
      rw [packet.base_conversion.base_two_nat_exponent_coefficient_matches_candidate]
    _ = 41472 := rfl

/--
Source-line lower-bound premise stated against the original BSW formula-size
threshold, separate from any graph-rescaled target interpretation.
-/
def StandardTseitinMorgensternQ2FormulaThresholdSourceLineLowerBoundPremise
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (formulaThreshold :
      CNFResolution.ResolutionAsymptoticExponentialThreshold)
    (sourceLineCount :
      CNFResolution.ResolutionFamilySourceLineCount
        (StandardTseitinResolutionFamilyTarget graph charge threshold)) : Prop :=
  forall (i : Index)
    (r : CNFResolution.ResolutionRefutation
      ((StandardTseitinResolutionFamilyTarget graph charge threshold).phi i)),
    formulaThreshold.threshold
        ((StandardTseitinCNFFormula (graph i) (charge i)).length) <=
      sourceLineCount i r

theorem standardTseitinMorgensternQ2InterpretedSourceLineLowerBound_of_graphRescaledFormulaThreshold
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {formulaThreshold :
      CNFResolution.ResolutionAsymptoticExponentialThreshold}
    {hthreshold :
      forall i : Index,
        threshold i = formulaThreshold.threshold ((graph i).n * 4)}
    {heventual :
      forall i : Index,
        (standardTseitinMorgensternQ2GraphRescaledThreshold
          formulaThreshold).appliesAt (graph i).n}
    {sourceLineCount :
      CNFResolution.ResolutionFamilySourceLineCount
        (StandardTseitinResolutionFamilyTarget graph charge threshold)}
    (hbridge :
      standardTseitinMorgensternQ2FormulaSizeGraphVertexBridge graph charge)
    (hformula :
      StandardTseitinMorgensternQ2FormulaThresholdSourceLineLowerBoundPremise
        graph charge threshold formulaThreshold sourceLineCount) :
    CNFResolution.ResolutionFamilyInterpretedSourceLineLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold formulaThreshold hthreshold heventual)
      sourceLineCount := by
  intro i r
  have hlen :
      (StandardTseitinCNFFormula (graph i) (charge i)).length =
        (graph i).n * 4 := hbridge i
  simpa [standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation,
    standardTseitinMorgensternQ2GraphRescaledThreshold, hlen] using
    hformula i r

theorem standardTseitinMorgensternQ2TraceLineLowerBound_of_graphRescaledFormulaThreshold
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {formulaThreshold :
      CNFResolution.ResolutionAsymptoticExponentialThreshold}
    {hthreshold :
      forall i : Index,
        threshold i = formulaThreshold.threshold ((graph i).n * 4)}
    {heventual :
      forall i : Index,
        (standardTseitinMorgensternQ2GraphRescaledThreshold
          formulaThreshold).appliesAt (graph i).n}
    (hbridge :
      standardTseitinMorgensternQ2FormulaSizeGraphVertexBridge graph charge)
    (hformula :
      StandardTseitinMorgensternQ2FormulaThresholdSourceLineLowerBoundPremise
        graph charge threshold formulaThreshold
        (CNFResolution.ResolutionFamilyTreeSourceLineCount
          (StandardTseitinResolutionFamilyTarget graph charge threshold))) :
    CNFResolution.ResolutionFamilyTraceLineLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold) := by
  exact
    CNFResolution.ResolutionFamilyTraceLineLowerBoundPremise_of_interpretedTreeSourceLineLowerBound
      (target:=StandardTseitinResolutionFamilyTarget graph charge threshold)
      (interpretation:=
        standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
          graph charge threshold formulaThreshold hthreshold heventual)
      (standardTseitinMorgensternQ2InterpretedSourceLineLowerBound_of_graphRescaledFormulaThreshold
        (graph:=graph)
        (charge:=charge)
        (threshold:=threshold)
        (formulaThreshold:=formulaThreshold)
        (hthreshold:=hthreshold)
        (heventual:=heventual)
        hbridge hformula)

/--
Structured line-count/trace-count alignment packet for the Morgenstern q = 2
BSW lane.

The source theorem packet names ordinary resolution line count.  The local proof
object is tree-shaped and uses the extracted tree-line trace.  This record keeps
those local metadata/transfer facts separate from the source-side BSW theorem
application.
-/
structure StandardTseitinMorgensternQ2LineCountTraceAlignment
    (sourcePacket : CNFResolution.ResolutionSourceTheoremPacket)
    (target : CNFResolution.ResolutionSizeFamilyTarget) where
  source_measure_is_line_count :
    sourcePacket.sizeMeasureKind =
      CNFResolution.ResolutionSourceSizeMeasureKind.lineCount
  source_kind_covers_local_tree :
    CNFResolution.ResolutionProofObjectKind.covers
      sourcePacket.proofObjectKind CNFResolution.localResolutionProofObjectKind
  local_tree_trace_count_transfers :
    CNFResolution.ResolutionFamilySourceLineCountTransfersToLocalTree target
      (CNFResolution.ResolutionFamilyTreeSourceLineCount target)

/--
Constructor for the selected Morgenstern q = 2 alignment packet. Source metadata
and the local tree-count transfer are checked here; source mathematical facts
are carried by `StandardTseitinMorgensternQ2SourceCitationPacket`.
-/
def standardTseitinMorgensternQ2SelectedLineCountTraceAlignment
    (target : CNFResolution.ResolutionSizeFamilyTarget) :
    StandardTseitinMorgensternQ2LineCountTraceAlignment
      standardTseitinMorgensternQ2TraceSourceTheoremPacket target where
  source_measure_is_line_count := rfl
  source_kind_covers_local_tree := by
    trivial
  local_tree_trace_count_transfers :=
    CNFResolution.ResolutionFamilyTreeSourceLineCount_transfersToLocalTree
      target

/--
Source-side citation packet for the Morgenstern q = 2 Ramanujan/expansion
facts.

This remains an external source packet: the local development does not prove
Morgenstern's construction or the spectral-to-edge-expansion conversion.
-/
structure StandardTseitinMorgensternQ2RamanujanSourcePacket where
  source_url : String
  morgenstern_construction_locator : String
  ramanujan_to_edge_expansion_locator : String
  morgenstern_q2_ramanujan_family_source : Prop
  morgenstern_q2_ramanujan_family_source_holds :
    morgenstern_q2_ramanujan_family_source
  ramanujan_spectral_to_edge_expansion_source : Prop
  ramanujan_spectral_to_edge_expansion_source_holds :
    ramanujan_spectral_to_edge_expansion_source

/--
Source-side citation packet for the BSW line-count lower-bound facts.

This keeps the BSW theorem application separate from the Morgenstern/Ramanujan
graph-family source facts.  The local source-line measure metadata is handled
by `StandardTseitinMorgensternQ2LineCountTraceAlignment`.
-/
structure StandardTseitinBSWLineCountSourcePacket where
  source_url : String
  tseitin_width_locator : String
  size_width_locator : String
  line_count_measure_locator : String
  bsw_tseitin_width_size_lower_bound_source : Prop
  bsw_tseitin_width_size_lower_bound_source_holds :
    bsw_tseitin_width_size_lower_bound_source

/--
Source-side concrete threshold packet for the original BSW formula-size
threshold.

This packet is deliberately parameterized by `formulaThreshold`: Stage1705 proved
the local graph-rescaling arithmetic, but the truth of the original formula-size
concrete lower bound remains a source theorem obligation.
-/
structure StandardTseitinBSWConcreteThresholdSourcePacket
    (formulaThreshold :
      CNFResolution.ResolutionAsymptoticExponentialThreshold) where
  source_url : String
  concrete_threshold_locator : String
  source_threshold_kind_is_formula_size :
    formulaThreshold.sizeParameterKind = standardTseitinBSWSourceSizeParameterKind
  source_threshold_concrete_lower_bound :
    formulaThreshold.concreteLowerBound

/--
Decomposed source boundary for the original BSW formula-size concrete
threshold.

This record does not prove constants locally.  It splits the monolithic
`formulaThreshold.concreteLowerBound` source obligation into named source
sub-obligations and one assembly implication, so future gates can reduce or
audit each constant source independently.
-/
structure StandardTseitinBSWConcreteThresholdDecomposition
    (formulaThreshold :
      CNFResolution.ResolutionAsymptoticExponentialThreshold) where
  source_url : String
  concrete_threshold_locator : String
  width_size_constant_locator : String
  expansion_rate_constant_locator : String
  formula_size_conversion_locator : String
  base_conversion_locator : String
  eventual_threshold_locator : String
  source_threshold_kind_is_formula_size :
    formulaThreshold.sizeParameterKind = standardTseitinBSWSourceSizeParameterKind
  width_size_constant_source : Prop
  width_size_constant_source_holds : width_size_constant_source
  expansion_rate_constant_source : Prop
  expansion_rate_constant_source_holds : expansion_rate_constant_source
  formula_size_conversion_source : Prop
  formula_size_conversion_source_holds : formula_size_conversion_source
  base_conversion_source : Prop
  base_conversion_source_holds : base_conversion_source
  eventual_threshold_source : Prop
  eventual_threshold_source_holds : eventual_threshold_source
  concrete_lower_bound_from_subobligations :
    width_size_constant_source ->
    expansion_rate_constant_source ->
    formula_size_conversion_source ->
    base_conversion_source ->
    eventual_threshold_source ->
    formulaThreshold.concreteLowerBound

def StandardTseitinBSWConcreteThresholdDecomposition.toSourcePacket
    {formulaThreshold :
      CNFResolution.ResolutionAsymptoticExponentialThreshold}
    (decomp :
      StandardTseitinBSWConcreteThresholdDecomposition formulaThreshold) :
    StandardTseitinBSWConcreteThresholdSourcePacket formulaThreshold where
  source_url := decomp.source_url
  concrete_threshold_locator := decomp.concrete_threshold_locator
  source_threshold_kind_is_formula_size :=
    decomp.source_threshold_kind_is_formula_size
  source_threshold_concrete_lower_bound :=
    decomp.concrete_lower_bound_from_subobligations
      decomp.width_size_constant_source_holds
      decomp.expansion_rate_constant_source_holds
      decomp.formula_size_conversion_source_holds
      decomp.base_conversion_source_holds
      decomp.eventual_threshold_source_holds

theorem standardTseitinMorgensternQ2GraphRescaledConcreteLowerBound_of_sourcePacket
    (formulaThreshold :
      CNFResolution.ResolutionAsymptoticExponentialThreshold)
    (packet :
      StandardTseitinBSWConcreteThresholdSourcePacket formulaThreshold) :
    (standardTseitinMorgensternQ2GraphRescaledThreshold
      formulaThreshold).concreteLowerBound := by
  exact
    standardTseitinMorgensternQ2GraphRescaledThreshold_concreteLowerBound
      formulaThreshold packet.source_threshold_concrete_lower_bound

/-- Locator for the Stage1736 concrete-threshold reassembly audit. -/
def standardTseitinMorgensternQ2ConcreteThresholdReassemblyLocator : String :=
  "Reassemble the Stage1728-Stage1735 q=2 arithmetic packets against the Stage1726 " ++
  "BSW concrete-threshold decomposition; wrap the existing source packet " ++
  "boundary rather than claiming the external BSW theorem locally."

/--
Stage1736 reassembly record for the explicit q = 2 concrete-threshold lane.

The record keeps the old `StandardTseitinBSWConcreteThresholdDecomposition`
visible as an audit object while routing the checked Stage1728-Stage1735 packet chain
through Stage1735's graph/formula threshold rescaling packet.  This intentionally
wraps the monolithic source packet; it does not remove the remaining
source-side BSW, expansion, real-analysis, base-conversion, or eventual
threshold obligations stored in the nested packets.
-/
structure StandardTseitinMorgensternQ2ConcreteThresholdReassembly
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat) where
  graph_formula_rescaling :
    StandardTseitinMorgensternQ2GraphFormulaThresholdRescaling
      graph charge threshold
  decomposition :
    StandardTseitinBSWConcreteThresholdDecomposition
      graph_formula_rescaling.base_conversion.formula_threshold
  reassembly_locator : String
  width_size_field_mapping : String
  expansion_rate_field_mapping : String
  formula_size_conversion_field_mapping : String
  base_conversion_field_mapping : String
  eventual_threshold_field_mapping : String
  source_packet_policy : String
  remaining_source_obligations_statement : String

def StandardTseitinMorgensternQ2ConcreteThresholdReassembly.formulaThreshold
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (packet :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) :
    CNFResolution.ResolutionAsymptoticExponentialThreshold :=
  packet.graph_formula_rescaling.base_conversion.formula_threshold

def StandardTseitinMorgensternQ2ConcreteThresholdReassembly.toReassembledSourcePacket
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (packet :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) :
    StandardTseitinBSWConcreteThresholdSourcePacket
      packet.formulaThreshold where
  source_url := packet.decomposition.source_url
  concrete_threshold_locator :=
    packet.decomposition.concrete_threshold_locator ++ "; " ++
      packet.reassembly_locator
  source_threshold_kind_is_formula_size :=
    (packet.graph_formula_rescaling.base_conversion).formula_threshold_kind_is_formula_size
  source_threshold_concrete_lower_bound :=
    (packet.graph_formula_rescaling.base_conversion).toFormulaThresholdConcreteLowerBound

def StandardTseitinMorgensternQ2ConcreteThresholdReassembly.toDecompositionSourcePacket
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (packet :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) :
    StandardTseitinBSWConcreteThresholdSourcePacket
      packet.formulaThreshold :=
  packet.decomposition.toSourcePacket

def StandardTseitinMorgensternQ2ConcreteThresholdReassembly.toGraphRescaledConcreteLowerBound
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (packet :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) :
    packet.graph_formula_rescaling.graphRescaledThreshold.concreteLowerBound :=
  packet.graph_formula_rescaling.toGraphRescaledConcreteLowerBound

def StandardTseitinMorgensternQ2ConcreteThresholdReassembly.toThresholdFamilyMatch
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (packet :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) :
    standardTseitinBSWThresholdFamilyMatch graph charge threshold :=
  ⟨packet.graph_formula_rescaling.thresholdInterpretation⟩

theorem StandardTseitinMorgensternQ2ConcreteThresholdReassembly.graphRescaled_cNum
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (packet :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) :
    packet.graph_formula_rescaling.graphRescaledThreshold.cNum = 1 := by
  exact packet.graph_formula_rescaling.graphRescaled_cNum

theorem StandardTseitinMorgensternQ2ConcreteThresholdReassembly.graphRescaled_cDen
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (packet :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) :
    packet.graph_formula_rescaling.graphRescaledThreshold.cDen = 41472 := by
  exact packet.graph_formula_rescaling.graphRescaled_cDen

theorem standardTseitinMorgensternQ2ExplicitExponentialTraceLineLowerBound_of_graphRescaledSourcePacket
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {formulaThreshold :
      CNFResolution.ResolutionAsymptoticExponentialThreshold}
    {hthreshold :
      forall i : Index,
        threshold i = formulaThreshold.threshold ((graph i).n * 4)}
    {heventual :
      forall i : Index,
        (standardTseitinMorgensternQ2GraphRescaledThreshold
          formulaThreshold).appliesAt (graph i).n}
    (hbridge :
      standardTseitinMorgensternQ2FormulaSizeGraphVertexBridge graph charge)
    (hformula :
      StandardTseitinMorgensternQ2FormulaThresholdSourceLineLowerBoundPremise
        graph charge threshold formulaThreshold
        (CNFResolution.ResolutionFamilyTreeSourceLineCount
          (StandardTseitinResolutionFamilyTarget graph charge threshold)))
    (packet :
      StandardTseitinBSWConcreteThresholdSourcePacket formulaThreshold) :
    CNFResolution.ResolutionFamilyExplicitExponentialTraceLineLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold formulaThreshold hthreshold heventual) := by
  exact
    CNFResolution.ResolutionFamilyExplicitExponentialTraceLineLowerBoundPremise_of_traceLineLowerBound
      (target:=StandardTseitinResolutionFamilyTarget graph charge threshold)
      (interpretation:=
        standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
          graph charge threshold formulaThreshold hthreshold heventual)
      (standardTseitinMorgensternQ2TraceLineLowerBound_of_graphRescaledFormulaThreshold
        (graph:=graph)
        (charge:=charge)
        (threshold:=threshold)
        (formulaThreshold:=formulaThreshold)
        (hthreshold:=hthreshold)
        (heventual:=heventual)
        hbridge hformula)
      (standardTseitinMorgensternQ2GraphRescaledConcreteLowerBound_of_sourcePacket
        formulaThreshold packet)

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_graphRescaledSourcePacket
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {formulaThreshold :
      CNFResolution.ResolutionAsymptoticExponentialThreshold}
    {hthreshold :
      forall i : Index,
        threshold i = formulaThreshold.threshold ((graph i).n * 4)}
    {heventual :
      forall i : Index,
        (standardTseitinMorgensternQ2GraphRescaledThreshold
          formulaThreshold).appliesAt (graph i).n}
    (hbridge :
      standardTseitinMorgensternQ2FormulaSizeGraphVertexBridge graph charge)
    (hformula :
      StandardTseitinMorgensternQ2FormulaThresholdSourceLineLowerBoundPremise
        graph charge threshold formulaThreshold
        (CNFResolution.ResolutionFamilyTreeSourceLineCount
          (StandardTseitinResolutionFamilyTarget graph charge threshold)))
    (packet :
      StandardTseitinBSWConcreteThresholdSourcePacket formulaThreshold) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold formulaThreshold hthreshold heventual) := by
  exact
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise_of_explicitTraceLineLowerBound
      (standardTseitinMorgensternQ2ExplicitExponentialTraceLineLowerBound_of_graphRescaledSourcePacket
        (graph:=graph)
        (charge:=charge)
        (threshold:=threshold)
        (formulaThreshold:=formulaThreshold)
        (hthreshold:=hthreshold)
        (heventual:=heventual)
        hbridge hformula packet)

/--
Composite source-side citation packet for the remaining Morgenstern q = 2 plus
BSW theorem application.

This packet carries only bibliographic/source mathematical facts, now split by
source family. Local line-count metadata, proof-object-kind coverage,
tree-trace transfer, and threshold interpretation stay outside it.
-/
structure StandardTseitinMorgensternQ2SourceCitationPacket
    (sourcePacket : CNFResolution.ResolutionSourceTheoremPacket) where
  source_packet_matches_selection :
    sourcePacket = standardTseitinMorgensternQ2TraceSourceTheoremPacket
  ramanujan_source_packet :
    StandardTseitinMorgensternQ2RamanujanSourcePacket
  bsw_line_count_source_packet :
    StandardTseitinBSWLineCountSourcePacket

/--
Source-side decomposition of the remaining Morgenstern q = 2 trace-line lower
bound.

This record does not prove Morgenstern, Ramanujan expansion, or the BSW theorem
locally. It names the source facts and requires one source-side assembly
implication from the source citation packet, structured line-count/trace-count
alignment packet, graph-vertex parameter match, and threshold-conservativity
packet to the formula-size source-line bound. The checked Stage1703 route then
downgrades that formula-size threshold to the interpreted graph-vertex
threshold expected by the Stage1695 conversion route.
-/
structure StandardTseitinMorgensternQ2SourceTracePremiseDecomposition
    {Index : Type}
    (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat) where
  source_packet : CNFResolution.ResolutionSourceTheoremPacket
  source_citation_packet :
    StandardTseitinMorgensternQ2SourceCitationPacket source_packet
  line_count_trace_alignment :
    StandardTseitinMorgensternQ2LineCountTraceAlignment source_packet
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
  threshold_interpretation :
    CNFResolution.ResolutionFamilyThresholdInterpretation
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
  parameter_alignment :
    StandardTseitinMorgensternQ2ParameterAlignment graph charge threshold
      threshold_interpretation
  threshold_conservativity :
    StandardTseitinMorgensternQ2ThresholdConservativity graph charge threshold
      threshold_interpretation parameter_alignment
  source_formula_size_source_line_lower_bound :
    StandardTseitinMorgensternQ2SourceCitationPacket source_packet ->
    StandardTseitinMorgensternQ2LineCountTraceAlignment source_packet
      (StandardTseitinResolutionFamilyTarget graph charge threshold) ->
    StandardTseitinMorgensternQ2ParameterAlignment graph charge threshold
      threshold_interpretation ->
    StandardTseitinMorgensternQ2ThresholdConservativity graph charge threshold
      threshold_interpretation parameter_alignment ->
    StandardTseitinMorgensternQ2FormulaSizeSourceLineLowerBoundPremise
      graph charge threshold threshold_interpretation
      (CNFResolution.ResolutionFamilyTreeSourceLineCount
        (StandardTseitinResolutionFamilyTarget graph charge threshold))

def StandardTseitinMorgensternQ2SourceTracePremiseDecomposition.toTraceLineLowerBound
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (decomp :
      StandardTseitinMorgensternQ2SourceTracePremiseDecomposition
        graph charge threshold) :
    CNFResolution.ResolutionFamilyTraceLineLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold) := by
  exact
    CNFResolution.ResolutionFamilyTraceLineLowerBoundPremise_of_interpretedTreeSourceLineLowerBound
      (target:=StandardTseitinResolutionFamilyTarget graph charge threshold)
      (interpretation:=decomp.threshold_interpretation)
      (decomp.threshold_conservativity.toInterpretedSourceLineLowerBound
        (decomp.source_formula_size_source_line_lower_bound
          decomp.source_citation_packet
          decomp.line_count_trace_alignment
          decomp.parameter_alignment
          decomp.threshold_conservativity))

/--
Reduced source-trace packet for the graph-rescaled q = 2 route.

Once Stage1736 reassembly fixes the graph-rescaled threshold, the preferred route
does not need the fully general source-trace decomposition fields for an
arbitrary threshold interpretation.  The selected source packet and
line-count/trace-count alignment are local metadata, and the graph/formula
threshold interpretation is already determined by `reassembly`.

The remaining source-side mathematical obligation is therefore the BSW
formula-threshold source-line lower bound for the selected Morgenstern q = 2
family, exposed as an implication from the source citation packet, selected
alignment, graph-family hardening, and odd-charge packet.
-/
structure StandardTseitinMorgensternQ2GraphRescaledSourceTracePremise
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) where
  source_citation_packet :
    StandardTseitinMorgensternQ2SourceCitationPacket
      standardTseitinMorgensternQ2TraceSourceTheoremPacket
  field_reduction_statement : String
  threshold_binding_statement : String
  remaining_source_obligation_statement : String
  source_formula_threshold_source_line_lower_bound :
    StandardTseitinMorgensternQ2SourceCitationPacket
      standardTseitinMorgensternQ2TraceSourceTheoremPacket ->
    StandardTseitinMorgensternQ2LineCountTraceAlignment
      standardTseitinMorgensternQ2TraceSourceTheoremPacket
      (StandardTseitinResolutionFamilyTarget graph charge threshold) ->
    StandardTseitinMorgensternQ2GraphFamilyHardening graph ->
    StandardTseitinMorgensternQ2OddChargeFamily graph charge ->
    StandardTseitinMorgensternQ2FormulaThresholdSourceLineLowerBoundPremise
      graph charge threshold reassembly.formulaThreshold
      (CNFResolution.ResolutionFamilyTreeSourceLineCount
        (StandardTseitinResolutionFamilyTarget graph charge threshold))

def StandardTseitinMorgensternQ2GraphRescaledSourceTracePremise.toFormulaThresholdSourceLineLowerBound
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2GraphRescaledSourceTracePremise
        graph charge threshold reassembly)
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge) :
    StandardTseitinMorgensternQ2FormulaThresholdSourceLineLowerBoundPremise
      graph charge threshold reassembly.formulaThreshold
      (CNFResolution.ResolutionFamilyTreeSourceLineCount
        (StandardTseitinResolutionFamilyTarget graph charge threshold)) :=
  packet.source_formula_threshold_source_line_lower_bound
    packet.source_citation_packet
    (standardTseitinMorgensternQ2SelectedLineCountTraceAlignment
      (StandardTseitinResolutionFamilyTarget graph charge threshold))
    graph_hardening odd_charge

def StandardTseitinMorgensternQ2GraphRescaledSourceTracePremise.toTraceLineLowerBound
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2GraphRescaledSourceTracePremise
        graph charge threshold reassembly)
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge) :
    CNFResolution.ResolutionFamilyTraceLineLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold) := by
  exact
    standardTseitinMorgensternQ2TraceLineLowerBound_of_graphRescaledFormulaThreshold
      (graph:=graph)
      (charge:=charge)
      (threshold:=threshold)
      (formulaThreshold:=reassembly.formulaThreshold)
      (hthreshold:=
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled)
      (heventual:=reassembly.graph_formula_rescaling.graph_rescaled_eventual)
      (standardTseitinMorgensternQ2FormulaSizeGraphVertexBridge_of_threeRegularFamily
        graph_hardening.threeRegularFamily)
      (packet.toFormulaThresholdSourceLineLowerBound
        graph_hardening odd_charge)

/--
Stage1742 source-boundary packet for the selected Morgenstern q = 2 BSW
formula-threshold source-line lower bound.

The graph-family, odd-charge, selected line-count alignment, local encoding,
proof-system, and threshold-reassembly prerequisites are supplied by existing
local packets.  The remaining field is the external BSW theorem application
itself: from the cited source facts and those checked prerequisites, derive the
formula-size threshold lower bound for the local tree-line source count.
-/
structure StandardTseitinMorgensternQ2FormulaThresholdSourceLineBoundSource
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) where
  source_citation_packet :
    StandardTseitinMorgensternQ2SourceCitationPacket
      standardTseitinMorgensternQ2TraceSourceTheoremPacket
  bsw_source_statement : String
  source_locator_statement : String
  graph_prerequisites_statement : String
  charge_prerequisite_statement : String
  local_encoding_statement : String
  local_proof_system_statement : String
  threshold_statement : String
  prerequisite_classification_statement : String
  remaining_source_obligation_statement : String
  bsw_formula_threshold_source_line_bound_source : Prop
  bsw_formula_threshold_source_line_bound_source_holds :
    bsw_formula_threshold_source_line_bound_source
  formula_threshold_source_line_lower_bound_of_sources :
    StandardTseitinMorgensternQ2SourceCitationPacket
      standardTseitinMorgensternQ2TraceSourceTheoremPacket ->
    StandardTseitinMorgensternQ2LineCountTraceAlignment
      standardTseitinMorgensternQ2TraceSourceTheoremPacket
      (StandardTseitinResolutionFamilyTarget graph charge threshold) ->
    StandardTseitinMorgensternQ2GraphFamilyHardening graph ->
    StandardTseitinMorgensternQ2OddChargeFamily graph charge ->
    StandardTseitinMorgensternQ2ConcreteThresholdReassembly
      graph charge threshold ->
    bsw_formula_threshold_source_line_bound_source ->
    StandardTseitinMorgensternQ2FormulaThresholdSourceLineLowerBoundPremise
      graph charge threshold reassembly.formulaThreshold
      (CNFResolution.ResolutionFamilyTreeSourceLineCount
        (StandardTseitinResolutionFamilyTarget graph charge threshold))

def StandardTseitinMorgensternQ2FormulaThresholdSourceLineBoundSource.toFormulaThresholdSourceLineLowerBound
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2FormulaThresholdSourceLineBoundSource
        graph charge threshold reassembly)
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge) :
    StandardTseitinMorgensternQ2FormulaThresholdSourceLineLowerBoundPremise
      graph charge threshold reassembly.formulaThreshold
      (CNFResolution.ResolutionFamilyTreeSourceLineCount
        (StandardTseitinResolutionFamilyTarget graph charge threshold)) :=
  packet.formula_threshold_source_line_lower_bound_of_sources
    packet.source_citation_packet
    (standardTseitinMorgensternQ2SelectedLineCountTraceAlignment
      (StandardTseitinResolutionFamilyTarget graph charge threshold))
    graph_hardening
    odd_charge
    reassembly
    packet.bsw_formula_threshold_source_line_bound_source_holds

def StandardTseitinMorgensternQ2FormulaThresholdSourceLineBoundSource.toGraphRescaledSourceTracePremise
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2FormulaThresholdSourceLineBoundSource
        graph charge threshold reassembly) :
    StandardTseitinMorgensternQ2GraphRescaledSourceTracePremise
      graph charge threshold reassembly where
  source_citation_packet := packet.source_citation_packet
  field_reduction_statement :=
    "Stage1742: graph, charge, selected alignment, local formula encoding, " ++
    "proof-system match, and threshold reassembly are supplied by existing " ++
    "packets; only the BSW formula-threshold source theorem application " ++
    "remains external."
  threshold_binding_statement := packet.threshold_statement
  remaining_source_obligation_statement :=
    packet.remaining_source_obligation_statement
  source_formula_threshold_source_line_lower_bound := by
    intro source_citation alignment graph_hardening odd_charge
    exact
      packet.formula_threshold_source_line_lower_bound_of_sources
        source_citation
        alignment
        graph_hardening
        odd_charge
        reassembly
        packet.bsw_formula_threshold_source_line_bound_source_holds

/--
Stage1743 decomposition of the final BSW theorem-application source proposition.

This packet does not prove any BSW subtheorem locally.  It records the smallest
useful source split found by the obstruction audit: the Tseitin width lower
bound, the BSW size-width conversion, and the formula-threshold instantiation
are separate source obligations, while the local graph/charge/encoding/proof
system/threshold packets are passed to one assembly implication.
-/
structure StandardTseitinMorgensternQ2BSWSourceTheoremApplicationDecomposition
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) where
  source_citation_packet :
    StandardTseitinMorgensternQ2SourceCitationPacket
      standardTseitinMorgensternQ2TraceSourceTheoremPacket
  bsw_hypothesis_map_statement : String
  local_model_match_statement : String
  width_lower_bound_locator : String
  size_width_conversion_locator : String
  formula_threshold_instantiation_locator : String
  decomposition_obstruction_statement : String
  bsw_tseitin_width_lower_bound_source : Prop
  bsw_tseitin_width_lower_bound_source_holds :
    bsw_tseitin_width_lower_bound_source
  bsw_size_width_conversion_source : Prop
  bsw_size_width_conversion_source_holds :
    bsw_size_width_conversion_source
  bsw_formula_threshold_instantiation_source : Prop
  bsw_formula_threshold_instantiation_source_holds :
    bsw_formula_threshold_instantiation_source
  formula_threshold_source_line_lower_bound_of_decomposed_sources :
    StandardTseitinMorgensternQ2SourceCitationPacket
      standardTseitinMorgensternQ2TraceSourceTheoremPacket ->
    StandardTseitinMorgensternQ2LineCountTraceAlignment
      standardTseitinMorgensternQ2TraceSourceTheoremPacket
      (StandardTseitinResolutionFamilyTarget graph charge threshold) ->
    StandardTseitinMorgensternQ2GraphFamilyHardening graph ->
    StandardTseitinMorgensternQ2OddChargeFamily graph charge ->
    StandardTseitinMorgensternQ2ConcreteThresholdReassembly
      graph charge threshold ->
    bsw_tseitin_width_lower_bound_source ->
    bsw_size_width_conversion_source ->
    bsw_formula_threshold_instantiation_source ->
    StandardTseitinMorgensternQ2FormulaThresholdSourceLineLowerBoundPremise
      graph charge threshold reassembly.formulaThreshold
      (CNFResolution.ResolutionFamilyTreeSourceLineCount
        (StandardTseitinResolutionFamilyTarget graph charge threshold))

def StandardTseitinMorgensternQ2BSWSourceTheoremApplicationDecomposition.toFormulaThresholdSourceLineBoundSource
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2BSWSourceTheoremApplicationDecomposition
        graph charge threshold reassembly) :
    StandardTseitinMorgensternQ2FormulaThresholdSourceLineBoundSource
      graph charge threshold reassembly where
  source_citation_packet := packet.source_citation_packet
  bsw_source_statement :=
    "Stage1743 decomposed BSW source application: Tseitin width lower bound, " ++
    "size-width conversion, and formula-threshold instantiation."
  source_locator_statement :=
    packet.width_lower_bound_locator ++ "; " ++
    packet.size_width_conversion_locator ++ "; " ++
    packet.formula_threshold_instantiation_locator
  graph_prerequisites_statement := packet.bsw_hypothesis_map_statement
  charge_prerequisite_statement :=
    "Odd total charge is supplied by StandardTseitinMorgensternQ2OddChargeFamily."
  local_encoding_statement := packet.local_model_match_statement
  local_proof_system_statement :=
    "Selected line-count alignment and local tree-line transfer are supplied " ++
    "by standardTseitinMorgensternQ2SelectedLineCountTraceAlignment."
  threshold_statement :=
    "Formula threshold is supplied by q=2 concrete threshold reassembly."
  prerequisite_classification_statement :=
    "Stage1743 splits only the external source proposition; local prerequisites " ++
    "remain supplied by Stage1739-Stage1742 packets."
  remaining_source_obligation_statement :=
    packet.decomposition_obstruction_statement
  bsw_formula_threshold_source_line_bound_source :=
    packet.bsw_tseitin_width_lower_bound_source /\
    packet.bsw_size_width_conversion_source /\
    packet.bsw_formula_threshold_instantiation_source
  bsw_formula_threshold_source_line_bound_source_holds :=
    ⟨packet.bsw_tseitin_width_lower_bound_source_holds,
      packet.bsw_size_width_conversion_source_holds,
      packet.bsw_formula_threshold_instantiation_source_holds⟩
  formula_threshold_source_line_lower_bound_of_sources := by
    intro source_citation alignment graph_hardening odd_charge reassembly hsource
    exact
      packet.formula_threshold_source_line_lower_bound_of_decomposed_sources
        source_citation
        alignment
        graph_hardening
        odd_charge
        reassembly
        hsource.1
        hsource.2.1
        hsource.2.2

/--
Stage1744 decomposition of the BSW Tseitin width lower-bound source fact.

This keeps BSW Theorem 4.4 external, but splits the width source proposition
into the BSW Tseitin-formula definition match, the BSW expansion-definition
match, and the Theorem 4.4 width lower-bound application.  The graph,
charge, representation, and local formula prerequisites still flow through the
existing graph-hardening and odd-charge packets.
-/
structure StandardTseitinMorgensternQ2BSWWidthLowerBoundSourceDecomposition
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) where
  source_citation_packet :
    StandardTseitinMorgensternQ2SourceCitationPacket
      standardTseitinMorgensternQ2TraceSourceTheoremPacket
  tseitin_formula_definition_locator : String
  expansion_definition_locator : String
  theorem44_width_locator : String
  size_width_conversion_locator : String
  formula_threshold_instantiation_locator : String
  graph_convention_map_statement : String
  connectedness_map_statement : String
  expansion_map_statement : String
  edge_variable_map_statement : String
  initial_width_map_statement : String
  odd_charge_map_statement : String
  remaining_width_obstruction_statement : String
  bsw_tseitin_formula_definition_source : Prop
  bsw_tseitin_formula_definition_source_holds :
    bsw_tseitin_formula_definition_source
  bsw_expansion_definition_source : Prop
  bsw_expansion_definition_source_holds :
    bsw_expansion_definition_source
  bsw_theorem44_width_lower_bound_source : Prop
  bsw_theorem44_width_lower_bound_source_holds :
    bsw_theorem44_width_lower_bound_source
  bsw_size_width_conversion_source : Prop
  bsw_size_width_conversion_source_holds :
    bsw_size_width_conversion_source
  bsw_formula_threshold_instantiation_source : Prop
  bsw_formula_threshold_instantiation_source_holds :
    bsw_formula_threshold_instantiation_source
  formula_threshold_source_line_lower_bound_of_width_decomposed_sources :
    StandardTseitinMorgensternQ2SourceCitationPacket
      standardTseitinMorgensternQ2TraceSourceTheoremPacket ->
    StandardTseitinMorgensternQ2LineCountTraceAlignment
      standardTseitinMorgensternQ2TraceSourceTheoremPacket
      (StandardTseitinResolutionFamilyTarget graph charge threshold) ->
    StandardTseitinMorgensternQ2GraphFamilyHardening graph ->
    StandardTseitinMorgensternQ2OddChargeFamily graph charge ->
    StandardTseitinMorgensternQ2ConcreteThresholdReassembly
      graph charge threshold ->
    (bsw_tseitin_formula_definition_source /\
      bsw_expansion_definition_source /\
      bsw_theorem44_width_lower_bound_source) ->
    bsw_size_width_conversion_source ->
    bsw_formula_threshold_instantiation_source ->
    StandardTseitinMorgensternQ2FormulaThresholdSourceLineLowerBoundPremise
      graph charge threshold reassembly.formulaThreshold
      (CNFResolution.ResolutionFamilyTreeSourceLineCount
        (StandardTseitinResolutionFamilyTarget graph charge threshold))

def StandardTseitinMorgensternQ2BSWWidthLowerBoundSourceDecomposition.toBSWSourceTheoremApplicationDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2BSWWidthLowerBoundSourceDecomposition
        graph charge threshold reassembly) :
    StandardTseitinMorgensternQ2BSWSourceTheoremApplicationDecomposition
      graph charge threshold reassembly where
  source_citation_packet := packet.source_citation_packet
  bsw_hypothesis_map_statement :=
    packet.connectedness_map_statement ++ "; " ++
    packet.expansion_map_statement ++ "; " ++
    packet.odd_charge_map_statement
  local_model_match_statement :=
    packet.graph_convention_map_statement ++ "; " ++
    packet.edge_variable_map_statement ++ "; " ++
    packet.initial_width_map_statement
  width_lower_bound_locator :=
    packet.tseitin_formula_definition_locator ++ "; " ++
    packet.expansion_definition_locator ++ "; " ++
    packet.theorem44_width_locator
  size_width_conversion_locator := packet.size_width_conversion_locator
  formula_threshold_instantiation_locator :=
    packet.formula_threshold_instantiation_locator
  decomposition_obstruction_statement :=
    packet.remaining_width_obstruction_statement
  bsw_tseitin_width_lower_bound_source :=
    packet.bsw_tseitin_formula_definition_source /\
    packet.bsw_expansion_definition_source /\
    packet.bsw_theorem44_width_lower_bound_source
  bsw_tseitin_width_lower_bound_source_holds :=
    And.intro packet.bsw_tseitin_formula_definition_source_holds
      (And.intro packet.bsw_expansion_definition_source_holds
        packet.bsw_theorem44_width_lower_bound_source_holds)
  bsw_size_width_conversion_source := packet.bsw_size_width_conversion_source
  bsw_size_width_conversion_source_holds :=
    packet.bsw_size_width_conversion_source_holds
  bsw_formula_threshold_instantiation_source :=
    packet.bsw_formula_threshold_instantiation_source
  bsw_formula_threshold_instantiation_source_holds :=
    packet.bsw_formula_threshold_instantiation_source_holds
  formula_threshold_source_line_lower_bound_of_decomposed_sources := by
    intro source_citation alignment graph_hardening odd_charge reassembly
      hwidth hsize hthreshold
    exact
      packet.formula_threshold_source_line_lower_bound_of_width_decomposed_sources
        source_citation
        alignment
        graph_hardening
        odd_charge
        reassembly
        hwidth
        hsize
        hthreshold

/--
Stage1748 decomposition of the BSW Theorem 4.4 width source fact.

The theorem-application layer is locally saturated, so the next useful source
split moves inside the remaining BSW Theorem 4.4 truth.  This packet records
the Section 5/6.1 proof-kernel shape: the general width/expansion strategy,
Tseitin contradiction and parity facts, axiom compatibility, proper-subset
satisfiability, and boundary-to-graph-expansion matching.  The assembly
implication remains source-side.
-/
structure StandardTseitinMorgensternQ2BSWTheorem44WidthKernelSourceDecomposition
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) where
  width_source :
    StandardTseitinMorgensternQ2BSWWidthLowerBoundSourceDecomposition
      graph charge threshold reassembly
  width_expansion_strategy_locator : String
  tseitin_specialization_locator : String
  contradiction_locator : String
  parity_sensitivity_locator : String
  compatibility_locator : String
  proper_subset_satisfiability_locator : String
  boundary_expansion_locator : String
  width_kernel_statement : String
  tseitin_specialization_statement : String
  remaining_width_kernel_obstruction_statement : String
  bsw_width_expansion_strategy_source : Prop
  bsw_width_expansion_strategy_source_holds :
    bsw_width_expansion_strategy_source
  bsw_tseitin_contradiction_source : Prop
  bsw_tseitin_contradiction_source_holds :
    bsw_tseitin_contradiction_source
  bsw_parity_sensitivity_source : Prop
  bsw_parity_sensitivity_source_holds :
    bsw_parity_sensitivity_source
  bsw_tseitin_axiom_compatibility_source : Prop
  bsw_tseitin_axiom_compatibility_source_holds :
    bsw_tseitin_axiom_compatibility_source
  bsw_tseitin_proper_subset_satisfiability_source : Prop
  bsw_tseitin_proper_subset_satisfiability_source_holds :
    bsw_tseitin_proper_subset_satisfiability_source
  bsw_tseitin_boundary_expansion_source : Prop
  bsw_tseitin_boundary_expansion_source_holds :
    bsw_tseitin_boundary_expansion_source
  bsw_theorem44_width_lower_bound_source : Prop
  bsw_theorem44_width_lower_bound_source_of_kernel :
    bsw_width_expansion_strategy_source ->
    bsw_tseitin_contradiction_source ->
    bsw_parity_sensitivity_source ->
    bsw_tseitin_axiom_compatibility_source ->
    bsw_tseitin_proper_subset_satisfiability_source ->
    bsw_tseitin_boundary_expansion_source ->
    bsw_theorem44_width_lower_bound_source
  bsw_theorem44_width_lower_bound_source_to_width_source :
    bsw_theorem44_width_lower_bound_source ->
    width_source.bsw_theorem44_width_lower_bound_source

def StandardTseitinMorgensternQ2BSWTheorem44WidthKernelSourceDecomposition.toBSWWidthLowerBoundSourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2BSWTheorem44WidthKernelSourceDecomposition
        graph charge threshold reassembly) :
    StandardTseitinMorgensternQ2BSWWidthLowerBoundSourceDecomposition
      graph charge threshold reassembly :=
  { packet.width_source with
    theorem44_width_locator :=
      packet.width_expansion_strategy_locator ++ "; " ++
      packet.tseitin_specialization_locator ++ "; " ++
      packet.contradiction_locator ++ "; " ++
      packet.parity_sensitivity_locator ++ "; " ++
      packet.compatibility_locator ++ "; " ++
      packet.proper_subset_satisfiability_locator ++ "; " ++
      packet.boundary_expansion_locator
    remaining_width_obstruction_statement :=
      packet.width_source.remaining_width_obstruction_statement ++
      "; " ++ packet.remaining_width_kernel_obstruction_statement
    bsw_theorem44_width_lower_bound_source :=
      packet.bsw_theorem44_width_lower_bound_source
    bsw_theorem44_width_lower_bound_source_holds :=
      packet.bsw_theorem44_width_lower_bound_source_of_kernel
        packet.bsw_width_expansion_strategy_source_holds
        packet.bsw_tseitin_contradiction_source_holds
        packet.bsw_parity_sensitivity_source_holds
        packet.bsw_tseitin_axiom_compatibility_source_holds
        packet.bsw_tseitin_proper_subset_satisfiability_source_holds
        packet.bsw_tseitin_boundary_expansion_source_holds
    formula_threshold_source_line_lower_bound_of_width_decomposed_sources := by
      intro source_citation alignment graph_hardening odd_charge reassembly
        hwidth hsize hthreshold
      exact
        packet.width_source.formula_threshold_source_line_lower_bound_of_width_decomposed_sources
          source_citation
          alignment
          graph_hardening
          odd_charge
          reassembly
          (And.intro hwidth.1
            (And.intro hwidth.2.1
              (packet.bsw_theorem44_width_lower_bound_source_to_width_source
                hwidth.2.2)))
          hsize
          hthreshold }

/--
Stage1750 decomposition of the BSW Section 6.1 proper-subset satisfiability and
odd-charge contradiction source facts.

The first reducible branch below the Stage1748 Theorem 4.4 width kernel is the
Tseitin-specific parity-subfamily lane.  This packet keeps the BSW Section 5
and other Section 6.1 obligations unchanged while splitting the contradiction
and proper-subset satisfiability facts into the source components used by the
standard Section 6.1 argument.
-/
structure StandardTseitinMorgensternQ2BSWProperSubsetSatisfiabilitySourceDecomposition
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) where
  width_kernel_source :
    StandardTseitinMorgensternQ2BSWTheorem44WidthKernelSourceDecomposition
      graph charge threshold reassembly
  odd_charge_inconsistency_locator : String
  charge_flip_outside_subset_locator : String
  flipped_instance_satisfiability_locator : String
  proper_subfamily_restriction_locator : String
  parity_subfamily_statement : String
  contradiction_statement : String
  proper_subset_satisfiability_statement : String
  remaining_parity_subfamily_obstruction_statement : String
  bsw_odd_charge_global_inconsistency_source : Prop
  bsw_odd_charge_global_inconsistency_source_holds :
    bsw_odd_charge_global_inconsistency_source
  bsw_charge_flip_outside_subset_source : Prop
  bsw_charge_flip_outside_subset_source_holds :
    bsw_charge_flip_outside_subset_source
  bsw_flipped_charge_full_instance_satisfiability_source : Prop
  bsw_flipped_charge_full_instance_satisfiability_source_holds :
    bsw_flipped_charge_full_instance_satisfiability_source
  bsw_proper_subfamily_restriction_source : Prop
  bsw_proper_subfamily_restriction_source_holds :
    bsw_proper_subfamily_restriction_source
  bsw_tseitin_contradiction_source : Prop
  bsw_tseitin_contradiction_source_of_odd_charge :
    bsw_odd_charge_global_inconsistency_source ->
    bsw_tseitin_contradiction_source
  bsw_tseitin_proper_subset_satisfiability_source : Prop
  bsw_tseitin_proper_subset_satisfiability_source_of_sources :
    bsw_charge_flip_outside_subset_source ->
    bsw_flipped_charge_full_instance_satisfiability_source ->
    bsw_proper_subfamily_restriction_source ->
    bsw_tseitin_proper_subset_satisfiability_source
  bsw_tseitin_contradiction_source_to_width_kernel_source :
    bsw_tseitin_contradiction_source ->
    width_kernel_source.bsw_tseitin_contradiction_source
  bsw_tseitin_proper_subset_satisfiability_source_to_width_kernel_source :
    bsw_tseitin_proper_subset_satisfiability_source ->
    width_kernel_source.bsw_tseitin_proper_subset_satisfiability_source

def StandardTseitinMorgensternQ2BSWProperSubsetSatisfiabilitySourceDecomposition.toBSWTheorem44WidthKernelSourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2BSWProperSubsetSatisfiabilitySourceDecomposition
        graph charge threshold reassembly) :
    StandardTseitinMorgensternQ2BSWTheorem44WidthKernelSourceDecomposition
      graph charge threshold reassembly :=
  { packet.width_kernel_source with
    contradiction_locator :=
      packet.width_kernel_source.contradiction_locator ++ "; " ++
      packet.odd_charge_inconsistency_locator
    proper_subset_satisfiability_locator :=
      packet.charge_flip_outside_subset_locator ++ "; " ++
      packet.flipped_instance_satisfiability_locator ++ "; " ++
      packet.proper_subfamily_restriction_locator
    tseitin_specialization_statement :=
      packet.width_kernel_source.tseitin_specialization_statement ++
      "; " ++ packet.parity_subfamily_statement
    remaining_width_kernel_obstruction_statement :=
      packet.width_kernel_source.remaining_width_kernel_obstruction_statement ++
      "; " ++ packet.remaining_parity_subfamily_obstruction_statement
    bsw_tseitin_contradiction_source :=
      packet.bsw_tseitin_contradiction_source
    bsw_tseitin_contradiction_source_holds :=
      packet.bsw_tseitin_contradiction_source_of_odd_charge
        packet.bsw_odd_charge_global_inconsistency_source_holds
    bsw_tseitin_proper_subset_satisfiability_source :=
      packet.bsw_tseitin_proper_subset_satisfiability_source
    bsw_tseitin_proper_subset_satisfiability_source_holds :=
      packet.bsw_tseitin_proper_subset_satisfiability_source_of_sources
        packet.bsw_charge_flip_outside_subset_source_holds
        packet.bsw_flipped_charge_full_instance_satisfiability_source_holds
        packet.bsw_proper_subfamily_restriction_source_holds
    bsw_theorem44_width_lower_bound_source_of_kernel := by
      intro hstrategy hcontradiction hsensitivity hcompatibility hproper
        hboundary
      exact
        packet.width_kernel_source.bsw_theorem44_width_lower_bound_source_of_kernel
          hstrategy
          (packet.bsw_tseitin_contradiction_source_to_width_kernel_source
            hcontradiction)
          hsensitivity
          hcompatibility
          (packet.bsw_tseitin_proper_subset_satisfiability_source_to_width_kernel_source
            hproper)
          hboundary }

/--
Stage1751 decomposition of the BSW odd-charge inconsistency source fact.

The local Lean side proves that an odd total charge makes the standard Tseitin
CNF unsatisfiable by folding all vertex equations and using double-counted
edge incidence.  This packet narrows the remaining source boundary to the
model-match step from that local standard-CNF unsatisfiability statement to
the BSW Section 6.1 odd-charge inconsistency fact consumed by Stage1750.
-/
structure StandardTseitinMorgensternQ2BSWOddChargeInconsistencySourceDecomposition
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) where
  proper_subset_source :
    StandardTseitinMorgensternQ2BSWProperSubsetSatisfiabilitySourceDecomposition
      graph charge threshold reassembly
  local_standard_unsat_locator : String
  bsw_model_match_locator : String
  local_parity_sum_statement : String
  bsw_model_match_statement : String
  remaining_odd_charge_obstruction_statement : String
  bsw_odd_charge_global_inconsistency_source : Prop
  bsw_odd_charge_global_inconsistency_source_of_local_standard_unsat :
    (forall i : Index,
      Not (Exists fun a : CNFModel.Assignment (graph i).edges.length =>
        CNFModel.cnfSat a (StandardTseitinCNFFormula (graph i) (charge i)))) ->
    bsw_odd_charge_global_inconsistency_source
  bsw_odd_charge_global_inconsistency_source_to_proper_subset_source :
    bsw_odd_charge_global_inconsistency_source ->
    proper_subset_source.bsw_odd_charge_global_inconsistency_source

def StandardTseitinMorgensternQ2BSWOddChargeInconsistencySourceDecomposition.toBSWProperSubsetSatisfiabilitySourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2BSWOddChargeInconsistencySourceDecomposition
        graph charge threshold reassembly)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge) :
    StandardTseitinMorgensternQ2BSWProperSubsetSatisfiabilitySourceDecomposition
      graph charge threshold reassembly :=
  { packet.proper_subset_source with
    odd_charge_inconsistency_locator :=
      packet.local_standard_unsat_locator ++ "; " ++
      packet.bsw_model_match_locator
    parity_subfamily_statement :=
      packet.proper_subset_source.parity_subfamily_statement ++
      "; " ++ packet.local_parity_sum_statement
    contradiction_statement :=
      packet.proper_subset_source.contradiction_statement ++
      "; " ++ packet.bsw_model_match_statement
    remaining_parity_subfamily_obstruction_statement :=
      packet.proper_subset_source.remaining_parity_subfamily_obstruction_statement ++
      "; " ++ packet.remaining_odd_charge_obstruction_statement
    bsw_odd_charge_global_inconsistency_source :=
      packet.bsw_odd_charge_global_inconsistency_source
    bsw_odd_charge_global_inconsistency_source_holds :=
      packet.bsw_odd_charge_global_inconsistency_source_of_local_standard_unsat
        (fun i =>
          not_cnfSat_standardTseitinCNFFormula_of_graph
            (G := graph i) (charge := charge i)
            (odd_charge.oddTotalCharge i))
    bsw_tseitin_contradiction_source_of_odd_charge := by
      intro hodd
      exact
        packet.proper_subset_source.bsw_tseitin_contradiction_source_of_odd_charge
          (packet.bsw_odd_charge_global_inconsistency_source_to_proper_subset_source
            hodd) }

/--
Stage1752 decomposition of the BSW charge-flip source fact.

The local Lean side now records the charge-update arithmetic used by the
selected singleton-zero q = 2 charge packet: flipping vertex zero turns the
local total charge even.  This packet keeps the BSW-specific outside-subset
choice and model-match step explicit, rather than pretending that the local
zero-flip theorem is already the full Section 6.1 charge-flip construction.
-/
structure StandardTseitinMorgensternQ2BSWChargeFlipSourceDecomposition
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) where
  odd_charge_source :
    StandardTseitinMorgensternQ2BSWOddChargeInconsistencySourceDecomposition
      graph charge threshold reassembly
  local_charge_flip_locator : String
  bsw_outside_subset_choice_locator : String
  bsw_charge_flip_model_match_locator : String
  local_charge_flip_statement : String
  outside_subset_choice_statement : String
  bsw_charge_flip_model_match_statement : String
  remaining_charge_flip_obstruction_statement : String
  bsw_charge_flip_outside_subset_source : Prop
  bsw_charge_flip_outside_subset_source_of_local_zero_flip_even :
    (forall i : Index,
      standardEvenTotalCharge (graph i)
        (standardFlipChargeAt (charge i) 0)) ->
    bsw_charge_flip_outside_subset_source
  bsw_charge_flip_outside_subset_source_to_proper_subset_source :
    bsw_charge_flip_outside_subset_source ->
    odd_charge_source.proper_subset_source.bsw_charge_flip_outside_subset_source

def StandardTseitinMorgensternQ2BSWChargeFlipSourceDecomposition.toBSWOddChargeInconsistencySourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2BSWChargeFlipSourceDecomposition
        graph charge threshold reassembly)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge) :
    StandardTseitinMorgensternQ2BSWOddChargeInconsistencySourceDecomposition
      graph charge threshold reassembly :=
  { packet.odd_charge_source with
    proper_subset_source :=
      { packet.odd_charge_source.proper_subset_source with
        charge_flip_outside_subset_locator :=
          packet.local_charge_flip_locator ++ "; " ++
          packet.bsw_outside_subset_choice_locator ++ "; " ++
          packet.bsw_charge_flip_model_match_locator
        parity_subfamily_statement :=
          packet.odd_charge_source.proper_subset_source.parity_subfamily_statement ++
          "; " ++ packet.local_charge_flip_statement
        proper_subset_satisfiability_statement :=
          packet.odd_charge_source.proper_subset_source.proper_subset_satisfiability_statement ++
          "; " ++ packet.outside_subset_choice_statement ++
          "; " ++ packet.bsw_charge_flip_model_match_statement
        remaining_parity_subfamily_obstruction_statement :=
          packet.odd_charge_source.proper_subset_source.remaining_parity_subfamily_obstruction_statement ++
          "; " ++ packet.remaining_charge_flip_obstruction_statement
        bsw_charge_flip_outside_subset_source :=
          packet.bsw_charge_flip_outside_subset_source
        bsw_charge_flip_outside_subset_source_holds :=
          packet.bsw_charge_flip_outside_subset_source_of_local_zero_flip_even
            odd_charge.zeroFlippedEvenTotalCharge
        bsw_tseitin_proper_subset_satisfiability_source_of_sources := by
          intro hflip hsat hrestrict
          exact
            packet.odd_charge_source.proper_subset_source.bsw_tseitin_proper_subset_satisfiability_source_of_sources
              (packet.bsw_charge_flip_outside_subset_source_to_proper_subset_source
                hflip)
              hsat
              hrestrict } }

/--
Stage1753 decomposition of the BSW flipped-instance satisfiability source fact.

For the selected singleton-zero q = 2 charge packet, the zero-flipped local
instance is the all-false charge instance, and the all-false edge assignment
satisfies the local standard Tseitin CNF.  The packet keeps the BSW Section 6.1
model-match step explicit instead of claiming a general even-charge
satisfiability theorem.
-/
structure StandardTseitinMorgensternQ2BSWFlippedInstanceSatisfiabilitySourceDecomposition
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) where
  charge_flip_source :
    StandardTseitinMorgensternQ2BSWChargeFlipSourceDecomposition
      graph charge threshold reassembly
  local_zero_flip_satisfiability_locator : String
  bsw_flipped_instance_model_match_locator : String
  local_zero_flip_satisfiability_statement : String
  bsw_flipped_instance_model_match_statement : String
  remaining_flipped_instance_obstruction_statement : String
  bsw_flipped_charge_full_instance_satisfiability_source : Prop
  bsw_flipped_charge_full_instance_satisfiability_source_of_local_zero_flip_sat :
    (forall i : Index,
      Exists fun a : CNFModel.Assignment (graph i).edges.length =>
        CNFModel.cnfSat a
          (StandardTseitinCNFFormula (graph i)
            (standardFlipChargeAt (charge i) 0))) ->
    bsw_flipped_charge_full_instance_satisfiability_source
  bsw_flipped_charge_full_instance_satisfiability_source_to_proper_subset_source :
    bsw_flipped_charge_full_instance_satisfiability_source ->
    charge_flip_source.odd_charge_source.proper_subset_source.bsw_flipped_charge_full_instance_satisfiability_source

def StandardTseitinMorgensternQ2BSWFlippedInstanceSatisfiabilitySourceDecomposition.toBSWChargeFlipSourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2BSWFlippedInstanceSatisfiabilitySourceDecomposition
        graph charge threshold reassembly)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge) :
    StandardTseitinMorgensternQ2BSWChargeFlipSourceDecomposition
      graph charge threshold reassembly :=
  { packet.charge_flip_source with
    odd_charge_source :=
      { packet.charge_flip_source.odd_charge_source with
        proper_subset_source :=
          { packet.charge_flip_source.odd_charge_source.proper_subset_source with
            flipped_instance_satisfiability_locator :=
              packet.local_zero_flip_satisfiability_locator ++ "; " ++
              packet.bsw_flipped_instance_model_match_locator
            proper_subset_satisfiability_statement :=
              packet.charge_flip_source.odd_charge_source.proper_subset_source.proper_subset_satisfiability_statement ++
              "; " ++ packet.local_zero_flip_satisfiability_statement ++
              "; " ++ packet.bsw_flipped_instance_model_match_statement
            remaining_parity_subfamily_obstruction_statement :=
              packet.charge_flip_source.odd_charge_source.proper_subset_source.remaining_parity_subfamily_obstruction_statement ++
              "; " ++ packet.remaining_flipped_instance_obstruction_statement
            bsw_flipped_charge_full_instance_satisfiability_source :=
              packet.bsw_flipped_charge_full_instance_satisfiability_source
            bsw_flipped_charge_full_instance_satisfiability_source_holds :=
              packet.bsw_flipped_charge_full_instance_satisfiability_source_of_local_zero_flip_sat
                odd_charge.zeroFlippedStandardCNFSatisfiable
            bsw_tseitin_proper_subset_satisfiability_source_of_sources := by
              intro hflip hsat hrestrict
              exact
                packet.charge_flip_source.odd_charge_source.proper_subset_source.bsw_tseitin_proper_subset_satisfiability_source_of_sources
                  hflip
                  (packet.bsw_flipped_charge_full_instance_satisfiability_source_to_proper_subset_source
                    hsat)
                  hrestrict } } }

/--
Stage1754 decomposition of the BSW proper-subfamily restriction source fact.

The local Lean side can show ordinary CNF-satisfaction monotonicity: any
assignment satisfying a full clause list also satisfies a clause subfamily.  The
packet keeps the BSW Section 6.1 choice of the proper subfamily and its
model-match bridge explicit.
-/
structure StandardTseitinMorgensternQ2BSWProperSubfamilyRestrictionSourceDecomposition
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) where
  flipped_instance_source :
    StandardTseitinMorgensternQ2BSWFlippedInstanceSatisfiabilitySourceDecomposition
      graph charge threshold reassembly
  local_cnf_restriction_locator : String
  bsw_proper_subfamily_model_match_locator : String
  local_cnf_restriction_statement : String
  bsw_proper_subfamily_model_match_statement : String
  remaining_proper_subfamily_obstruction_statement : String
  proper_subfamily_cnf :
    (i : Index) -> CNFModel.CNF (graph i).edges.length
  proper_subfamily_clause_subset :
    forall i : Index,
      forall c : CNFModel.Clause (graph i).edges.length,
        List.Mem c (proper_subfamily_cnf i) ->
          List.Mem c
            (StandardTseitinCNFFormula (graph i)
              (standardFlipChargeAt (charge i) 0))
  bsw_proper_subfamily_restriction_source : Prop
  bsw_proper_subfamily_restriction_source_of_local_restriction :
    (forall i : Index,
      Exists fun a : CNFModel.Assignment (graph i).edges.length =>
        CNFModel.cnfSat a (proper_subfamily_cnf i)) ->
    bsw_proper_subfamily_restriction_source
  bsw_proper_subfamily_restriction_source_to_proper_subset_source :
    bsw_proper_subfamily_restriction_source ->
    flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source.bsw_proper_subfamily_restriction_source

theorem StandardTseitinMorgensternQ2BSWProperSubfamilyRestrictionSourceDecomposition.localProperSubfamilyCNFSatisfiable
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2BSWProperSubfamilyRestrictionSourceDecomposition
        graph charge threshold reassembly)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge) :
    forall i : Index,
      Exists fun a : CNFModel.Assignment (graph i).edges.length =>
        CNFModel.cnfSat a (packet.proper_subfamily_cnf i) := by
  intro i
  exact
    exists_cnfSat_of_clause_subset
      (odd_charge.zeroFlippedStandardCNFSatisfiable i)
      (packet.proper_subfamily_clause_subset i)

def StandardTseitinMorgensternQ2BSWProperSubfamilyRestrictionSourceDecomposition.toBSWFlippedInstanceSatisfiabilitySourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2BSWProperSubfamilyRestrictionSourceDecomposition
        graph charge threshold reassembly)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge) :
    StandardTseitinMorgensternQ2BSWFlippedInstanceSatisfiabilitySourceDecomposition
      graph charge threshold reassembly :=
  { packet.flipped_instance_source with
    charge_flip_source :=
      { packet.flipped_instance_source.charge_flip_source with
        odd_charge_source :=
          { packet.flipped_instance_source.charge_flip_source.odd_charge_source with
            proper_subset_source :=
              { packet.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source with
                proper_subfamily_restriction_locator :=
                  packet.local_cnf_restriction_locator ++ "; " ++
                  packet.bsw_proper_subfamily_model_match_locator
                proper_subset_satisfiability_statement :=
                  packet.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source.proper_subset_satisfiability_statement ++
                  "; " ++ packet.local_cnf_restriction_statement ++
                  "; " ++ packet.bsw_proper_subfamily_model_match_statement
                remaining_parity_subfamily_obstruction_statement :=
                  packet.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source.remaining_parity_subfamily_obstruction_statement ++
                  "; " ++ packet.remaining_proper_subfamily_obstruction_statement
                bsw_proper_subfamily_restriction_source :=
                  packet.bsw_proper_subfamily_restriction_source
                bsw_proper_subfamily_restriction_source_holds :=
                  packet.bsw_proper_subfamily_restriction_source_of_local_restriction
                    (packet.localProperSubfamilyCNFSatisfiable odd_charge)
                bsw_tseitin_proper_subset_satisfiability_source_of_sources := by
                  intro hflip hsat hrestrict
                  exact
                    packet.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source.bsw_tseitin_proper_subset_satisfiability_source_of_sources
                      hflip
                      hsat
                      (packet.bsw_proper_subfamily_restriction_source_to_proper_subset_source
                        hrestrict) } } } }

/--
Stage1755 decomposition of the BSW parity-sensitivity source fact.

The local Lean side proves target sensitivity for the standard Tseitin vertex
CNF: any assignment satisfying a vertex parity target cannot satisfy the same
vertex clauses with the opposite target.  This packet keeps the BSW
sensitive-function and model-match bridge explicit.
-/
structure StandardTseitinMorgensternQ2BSWParitySensitivitySourceDecomposition
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) where
  proper_subfamily_source :
    StandardTseitinMorgensternQ2BSWProperSubfamilyRestrictionSourceDecomposition
      graph charge threshold reassembly
  local_parity_target_sensitivity_locator : String
  bsw_parity_sensitivity_model_match_locator : String
  local_parity_target_sensitivity_statement : String
  bsw_parity_sensitivity_model_match_statement : String
  remaining_parity_sensitivity_obstruction_statement : String
  bsw_parity_sensitivity_source : Prop
  bsw_parity_sensitivity_source_of_local_target_sensitivity :
    (forall i : Index,
      standardLocalParityTargetSensitive (graph i) (charge i)) ->
    bsw_parity_sensitivity_source
  bsw_parity_sensitivity_source_to_width_kernel_source :
    bsw_parity_sensitivity_source ->
    proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source.width_kernel_source.bsw_parity_sensitivity_source

def StandardTseitinMorgensternQ2BSWParitySensitivitySourceDecomposition.toBSWProperSubfamilyRestrictionSourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2BSWParitySensitivitySourceDecomposition
        graph charge threshold reassembly) :
    StandardTseitinMorgensternQ2BSWProperSubfamilyRestrictionSourceDecomposition
      graph charge threshold reassembly :=
  { packet.proper_subfamily_source with
    flipped_instance_source :=
      { packet.proper_subfamily_source.flipped_instance_source with
        charge_flip_source :=
          { packet.proper_subfamily_source.flipped_instance_source.charge_flip_source with
            odd_charge_source :=
              { packet.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source with
                proper_subset_source :=
                  { packet.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source with
                    width_kernel_source :=
                      { packet.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source.width_kernel_source with
                        parity_sensitivity_locator :=
                          packet.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source.width_kernel_source.parity_sensitivity_locator ++
                          "; " ++
                          packet.local_parity_target_sensitivity_locator ++
                          "; " ++
                          packet.bsw_parity_sensitivity_model_match_locator
                        tseitin_specialization_statement :=
                          packet.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source.width_kernel_source.tseitin_specialization_statement ++
                          "; " ++
                          packet.local_parity_target_sensitivity_statement ++
                          "; " ++
                          packet.bsw_parity_sensitivity_model_match_statement
                        remaining_width_kernel_obstruction_statement :=
                          packet.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source.width_kernel_source.remaining_width_kernel_obstruction_statement ++
                          "; " ++
                          packet.remaining_parity_sensitivity_obstruction_statement
                        bsw_parity_sensitivity_source :=
                          packet.bsw_parity_sensitivity_source
                        bsw_parity_sensitivity_source_holds :=
                          packet.bsw_parity_sensitivity_source_of_local_target_sensitivity
                            (fun i =>
                              standardLocalParityTargetSensitive_of_graph
                                (graph i) (charge i))
                        bsw_theorem44_width_lower_bound_source_of_kernel := by
                          intro hstrategy hcontradiction hsensitivity
                            hcompatibility hproper hboundary
                          exact
                            packet.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source.width_kernel_source.bsw_theorem44_width_lower_bound_source_of_kernel
                              hstrategy
                              hcontradiction
                              (packet.bsw_parity_sensitivity_source_to_width_kernel_source
                                hsensitivity)
                              hcompatibility
                              hproper
                              hboundary } } } } } }

/--
Stage1756 decomposition of the BSW Tseitin axiom-compatibility source fact.

The local Lean side proves that each standard vertex parity clause is present
in the direct Res(oplus) parity formula and is semantically equivalent, under
the same assignment, to the expanded CNF clauses for that vertex.  This packet
keeps the BSW axiom object and model-match bridge explicit.
-/
structure StandardTseitinMorgensternQ2BSWAxiomCompatibilitySourceDecomposition
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) where
  parity_sensitivity_source :
    StandardTseitinMorgensternQ2BSWParitySensitivitySourceDecomposition
      graph charge threshold reassembly
  local_tseitin_axiom_compatibility_locator : String
  bsw_axiom_compatibility_model_match_locator : String
  local_tseitin_axiom_compatibility_statement : String
  bsw_axiom_compatibility_model_match_statement : String
  remaining_axiom_compatibility_obstruction_statement : String
  bsw_tseitin_axiom_compatibility_source : Prop
  bsw_tseitin_axiom_compatibility_source_of_local_axiom_compatibility :
    (forall i : Index,
      standardLocalTseitinAxiomCompatible (graph i) (charge i)) ->
    bsw_tseitin_axiom_compatibility_source
  bsw_tseitin_axiom_compatibility_source_to_width_kernel_source :
    bsw_tseitin_axiom_compatibility_source ->
    parity_sensitivity_source.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source.width_kernel_source.bsw_tseitin_axiom_compatibility_source

def StandardTseitinMorgensternQ2BSWAxiomCompatibilitySourceDecomposition.toBSWParitySensitivitySourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2BSWAxiomCompatibilitySourceDecomposition
        graph charge threshold reassembly) :
    StandardTseitinMorgensternQ2BSWParitySensitivitySourceDecomposition
      graph charge threshold reassembly :=
  let oldWidthKernel :=
    packet.parity_sensitivity_source.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source.width_kernel_source
  let widthKernelSource :=
    { oldWidthKernel with
      compatibility_locator :=
        oldWidthKernel.compatibility_locator ++ "; " ++
        packet.local_tseitin_axiom_compatibility_locator ++ "; " ++
        packet.bsw_axiom_compatibility_model_match_locator
      tseitin_specialization_statement :=
        oldWidthKernel.tseitin_specialization_statement ++ "; " ++
        packet.local_tseitin_axiom_compatibility_statement ++ "; " ++
        packet.bsw_axiom_compatibility_model_match_statement
      remaining_width_kernel_obstruction_statement :=
        oldWidthKernel.remaining_width_kernel_obstruction_statement ++ "; " ++
        packet.remaining_axiom_compatibility_obstruction_statement
      bsw_tseitin_axiom_compatibility_source :=
        packet.bsw_tseitin_axiom_compatibility_source
      bsw_tseitin_axiom_compatibility_source_holds :=
        packet.bsw_tseitin_axiom_compatibility_source_of_local_axiom_compatibility
          (fun i =>
            standardLocalTseitinAxiomCompatible_of_graph (graph i) (charge i))
      bsw_theorem44_width_lower_bound_source_of_kernel := by
        intro hstrategy hcontradiction hsensitivity hcompatibility hproper
          hboundary
        exact
          oldWidthKernel.bsw_theorem44_width_lower_bound_source_of_kernel
            hstrategy
            hcontradiction
            hsensitivity
            (packet.bsw_tseitin_axiom_compatibility_source_to_width_kernel_source
              hcompatibility)
            hproper
            hboundary }
  let oldProperSubset :=
    packet.parity_sensitivity_source.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source
  let properSubsetSource :=
    { oldProperSubset with
      width_kernel_source := widthKernelSource }
  let oldOddCharge :=
    packet.parity_sensitivity_source.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source
  let oddChargeSource :=
    { oldOddCharge with
      proper_subset_source := properSubsetSource }
  let oldChargeFlip :=
    packet.parity_sensitivity_source.proper_subfamily_source.flipped_instance_source.charge_flip_source
  let chargeFlipSource :=
    { oldChargeFlip with
      odd_charge_source := oddChargeSource }
  let oldFlippedInstance :=
    packet.parity_sensitivity_source.proper_subfamily_source.flipped_instance_source
  let flippedInstanceSource :=
    { oldFlippedInstance with
      charge_flip_source := chargeFlipSource }
  let properSubfamilySource :=
    { packet.parity_sensitivity_source.proper_subfamily_source with
      flipped_instance_source := flippedInstanceSource }
  { packet.parity_sensitivity_source with
    proper_subfamily_source := properSubfamilySource }

/--
Stage1757 decomposition of the BSW boundary-expansion source fact.

The local Lean side supplies the selected q = 2 edge-expansion family through
`StandardTseitinMorgensternQ2GraphFamilyHardening`.  This packet keeps the BSW
boundary-set and model-match bridge explicit.
-/
structure StandardTseitinMorgensternQ2BSWBoundaryExpansionSourceDecomposition
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) where
  axiom_compatibility_source :
    StandardTseitinMorgensternQ2BSWAxiomCompatibilitySourceDecomposition
      graph charge threshold reassembly
  local_edge_expansion_locator : String
  bsw_boundary_expansion_model_match_locator : String
  local_edge_expansion_statement : String
  bsw_boundary_expansion_model_match_statement : String
  remaining_boundary_expansion_obstruction_statement : String
  bsw_tseitin_boundary_expansion_source : Prop
  bsw_tseitin_boundary_expansion_source_of_local_edge_expansion :
    (forall i : Index,
      standardEdgeExpansionAtLeast (graph i)
        standardTseitinMorgensternQ2EdgeExpansionConstant) ->
    bsw_tseitin_boundary_expansion_source
  bsw_tseitin_boundary_expansion_source_to_width_kernel_source :
    bsw_tseitin_boundary_expansion_source ->
    axiom_compatibility_source.parity_sensitivity_source.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source.width_kernel_source.bsw_tseitin_boundary_expansion_source

def StandardTseitinMorgensternQ2BSWBoundaryExpansionSourceDecomposition.toBSWAxiomCompatibilitySourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (packet :
      StandardTseitinMorgensternQ2BSWBoundaryExpansionSourceDecomposition
        graph charge threshold reassembly) :
    StandardTseitinMorgensternQ2BSWAxiomCompatibilitySourceDecomposition
      graph charge threshold reassembly :=
  let oldWidthKernel :=
    packet.axiom_compatibility_source.parity_sensitivity_source.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source.width_kernel_source
  let widthKernelSource :=
    { oldWidthKernel with
      boundary_expansion_locator :=
        oldWidthKernel.boundary_expansion_locator ++ "; " ++
        packet.local_edge_expansion_locator ++ "; " ++
        packet.bsw_boundary_expansion_model_match_locator
      tseitin_specialization_statement :=
        oldWidthKernel.tseitin_specialization_statement ++ "; " ++
        packet.local_edge_expansion_statement ++ "; " ++
        packet.bsw_boundary_expansion_model_match_statement
      remaining_width_kernel_obstruction_statement :=
        oldWidthKernel.remaining_width_kernel_obstruction_statement ++ "; " ++
        packet.remaining_boundary_expansion_obstruction_statement
      bsw_tseitin_boundary_expansion_source :=
        packet.bsw_tseitin_boundary_expansion_source
      bsw_tseitin_boundary_expansion_source_holds :=
        packet.bsw_tseitin_boundary_expansion_source_of_local_edge_expansion
          graph_hardening.selectedCandidateEdgeExpansionFamily
      bsw_theorem44_width_lower_bound_source_of_kernel := by
        intro hstrategy hcontradiction hsensitivity hcompatibility hproper
          hboundary
        exact
          oldWidthKernel.bsw_theorem44_width_lower_bound_source_of_kernel
            hstrategy
            hcontradiction
            hsensitivity
            hcompatibility
            hproper
            (packet.bsw_tseitin_boundary_expansion_source_to_width_kernel_source
              hboundary) }
  let oldProperSubset :=
    packet.axiom_compatibility_source.parity_sensitivity_source.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source
  let properSubsetSource :=
    { oldProperSubset with
      width_kernel_source := widthKernelSource }
  let oldOddCharge :=
    packet.axiom_compatibility_source.parity_sensitivity_source.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source
  let oddChargeSource :=
    { oldOddCharge with
      proper_subset_source := properSubsetSource }
  let oldChargeFlip :=
    packet.axiom_compatibility_source.parity_sensitivity_source.proper_subfamily_source.flipped_instance_source.charge_flip_source
  let chargeFlipSource :=
    { oldChargeFlip with
      odd_charge_source := oddChargeSource }
  let oldFlippedInstance :=
    packet.axiom_compatibility_source.parity_sensitivity_source.proper_subfamily_source.flipped_instance_source
  let flippedInstanceSource :=
    { oldFlippedInstance with
      charge_flip_source := chargeFlipSource }
  let properSubfamilySource :=
    { packet.axiom_compatibility_source.parity_sensitivity_source.proper_subfamily_source with
      flipped_instance_source := flippedInstanceSource }
  let paritySensitivitySource :=
    { packet.axiom_compatibility_source.parity_sensitivity_source with
      proper_subfamily_source := properSubfamilySource }
  { packet.axiom_compatibility_source with
    parity_sensitivity_source := paritySensitivitySource }

/--
Stage1758 audit of the BSW width-expansion strategy source fact.

After Stage1750-Stage1757, the Tseitin-specific sibling obligations in the BSW
Theorem 4.4 width kernel have local decomposition packets.  The remaining
`bsw_width_expansion_strategy_source` is still the source-side Section 5 proof
strategy rather than a local Tseitin semantic fact.  This packet records that
boundary explicitly and forwards it unchanged into the width-kernel packet.
-/
structure StandardTseitinMorgensternQ2BSWWidthExpansionStrategySourceBoundary
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) where
  boundary_expansion_source :
    StandardTseitinMorgensternQ2BSWBoundaryExpansionSourceDecomposition
      graph charge threshold reassembly
  bsw_section5_strategy_locator : String
  decomposed_sibling_sources_locator : String
  bsw_section5_strategy_statement : String
  decomposed_sibling_sources_statement : String
  remaining_strategy_obstruction_statement : String
  bsw_width_expansion_strategy_source : Prop
  bsw_width_expansion_strategy_source_holds :
    bsw_width_expansion_strategy_source
  bsw_width_expansion_strategy_source_to_width_kernel_source :
    bsw_width_expansion_strategy_source ->
    boundary_expansion_source.axiom_compatibility_source.parity_sensitivity_source.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source.width_kernel_source.bsw_width_expansion_strategy_source

def StandardTseitinMorgensternQ2BSWWidthExpansionStrategySourceBoundary.toBSWBoundaryExpansionSourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2BSWWidthExpansionStrategySourceBoundary
        graph charge threshold reassembly) :
    StandardTseitinMorgensternQ2BSWBoundaryExpansionSourceDecomposition
      graph charge threshold reassembly :=
  let oldWidthKernel :=
    packet.boundary_expansion_source.axiom_compatibility_source.parity_sensitivity_source.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source.width_kernel_source
  let widthKernelSource :=
    { oldWidthKernel with
      width_expansion_strategy_locator :=
        oldWidthKernel.width_expansion_strategy_locator ++ "; " ++
        packet.bsw_section5_strategy_locator ++ "; " ++
        packet.decomposed_sibling_sources_locator
      width_kernel_statement :=
        oldWidthKernel.width_kernel_statement ++ "; " ++
        packet.bsw_section5_strategy_statement ++ "; " ++
        packet.decomposed_sibling_sources_statement
      remaining_width_kernel_obstruction_statement :=
        oldWidthKernel.remaining_width_kernel_obstruction_statement ++ "; " ++
        packet.remaining_strategy_obstruction_statement
      bsw_width_expansion_strategy_source :=
        packet.bsw_width_expansion_strategy_source
      bsw_width_expansion_strategy_source_holds :=
        packet.bsw_width_expansion_strategy_source_holds
      bsw_theorem44_width_lower_bound_source_of_kernel := by
        intro hstrategy hcontradiction hsensitivity hcompatibility hproper
          hboundary
        exact
          oldWidthKernel.bsw_theorem44_width_lower_bound_source_of_kernel
            (packet.bsw_width_expansion_strategy_source_to_width_kernel_source
              hstrategy)
            hcontradiction
            hsensitivity
            hcompatibility
            hproper
            hboundary }
  let oldProperSubset :=
    packet.boundary_expansion_source.axiom_compatibility_source.parity_sensitivity_source.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source.proper_subset_source
  let properSubsetSource :=
    { oldProperSubset with
      width_kernel_source := widthKernelSource }
  let oldOddCharge :=
    packet.boundary_expansion_source.axiom_compatibility_source.parity_sensitivity_source.proper_subfamily_source.flipped_instance_source.charge_flip_source.odd_charge_source
  let oddChargeSource :=
    { oldOddCharge with
      proper_subset_source := properSubsetSource }
  let oldChargeFlip :=
    packet.boundary_expansion_source.axiom_compatibility_source.parity_sensitivity_source.proper_subfamily_source.flipped_instance_source.charge_flip_source
  let chargeFlipSource :=
    { oldChargeFlip with
      odd_charge_source := oddChargeSource }
  let oldFlippedInstance :=
    packet.boundary_expansion_source.axiom_compatibility_source.parity_sensitivity_source.proper_subfamily_source.flipped_instance_source
  let flippedInstanceSource :=
    { oldFlippedInstance with
      charge_flip_source := chargeFlipSource }
  let properSubfamilySource :=
    { packet.boundary_expansion_source.axiom_compatibility_source.parity_sensitivity_source.proper_subfamily_source with
      flipped_instance_source := flippedInstanceSource }
  let paritySensitivitySource :=
    { packet.boundary_expansion_source.axiom_compatibility_source.parity_sensitivity_source with
      proper_subfamily_source := properSubfamilySource }
  let axiomCompatibilitySource :=
    { packet.boundary_expansion_source.axiom_compatibility_source with
      parity_sensitivity_source := paritySensitivitySource }
  { packet.boundary_expansion_source with
    axiom_compatibility_source := axiomCompatibilitySource }

/--
Stage1745 decomposition of the BSW size-width conversion source fact.

The selected q = 2 lane continues to use the general-resolution BSW
Theorem 3.5/Corollary 3.6 route already stored in the concrete-threshold
reassembly packet.  The exact tree-like Corollary 3.4 route is recorded as an
alternative source proposition, but it is not consumed by this packet because
using it would change the proof-system route.
-/
structure StandardTseitinMorgensternQ2BSWSizeWidthConversionSourceDecomposition
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) where
  source_citation_packet :
    StandardTseitinMorgensternQ2SourceCitationPacket
      standardTseitinMorgensternQ2TraceSourceTheoremPacket
  tseitin_formula_definition_locator : String
  expansion_definition_locator : String
  theorem44_width_locator : String
  size_measure_definition_locator : String
  tree_like_size_width_locator : String
  general_size_width_locator : String
  formula_threshold_instantiation_locator : String
  selected_size_width_route_statement : String
  local_tree_line_count_map_statement : String
  reassembly_width_size_map_statement : String
  tree_like_route_policy_statement : String
  graph_convention_map_statement : String
  connectedness_map_statement : String
  expansion_map_statement : String
  edge_variable_map_statement : String
  initial_width_map_statement : String
  odd_charge_map_statement : String
  remaining_size_width_obstruction_statement : String
  bsw_tseitin_formula_definition_source : Prop
  bsw_tseitin_formula_definition_source_holds :
    bsw_tseitin_formula_definition_source
  bsw_expansion_definition_source : Prop
  bsw_expansion_definition_source_holds :
    bsw_expansion_definition_source
  bsw_theorem44_width_lower_bound_source : Prop
  bsw_theorem44_width_lower_bound_source_holds :
    bsw_theorem44_width_lower_bound_source
  bsw_source_size_measure_definition_source : Prop
  bsw_source_size_measure_definition_source_holds :
    bsw_source_size_measure_definition_source
  bsw_tree_like_size_width_alternative_source : Prop
  bsw_size_width_conversion_source : Prop
  bsw_size_width_conversion_source_of_general_reassembly :
    bsw_source_size_measure_definition_source ->
    reassembly.decomposition.width_size_constant_source ->
    bsw_size_width_conversion_source
  bsw_formula_threshold_instantiation_source : Prop
  bsw_formula_threshold_instantiation_source_holds :
    bsw_formula_threshold_instantiation_source
  formula_threshold_source_line_lower_bound_of_size_decomposed_sources :
    StandardTseitinMorgensternQ2SourceCitationPacket
      standardTseitinMorgensternQ2TraceSourceTheoremPacket ->
    StandardTseitinMorgensternQ2LineCountTraceAlignment
      standardTseitinMorgensternQ2TraceSourceTheoremPacket
      (StandardTseitinResolutionFamilyTarget graph charge threshold) ->
    StandardTseitinMorgensternQ2GraphFamilyHardening graph ->
    StandardTseitinMorgensternQ2OddChargeFamily graph charge ->
    StandardTseitinMorgensternQ2ConcreteThresholdReassembly
      graph charge threshold ->
    (bsw_tseitin_formula_definition_source /\
      bsw_expansion_definition_source /\
      bsw_theorem44_width_lower_bound_source) ->
    bsw_size_width_conversion_source ->
    bsw_formula_threshold_instantiation_source ->
    StandardTseitinMorgensternQ2FormulaThresholdSourceLineLowerBoundPremise
      graph charge threshold reassembly.formulaThreshold
      (CNFResolution.ResolutionFamilyTreeSourceLineCount
        (StandardTseitinResolutionFamilyTarget graph charge threshold))

def StandardTseitinMorgensternQ2BSWSizeWidthConversionSourceDecomposition.toBSWWidthLowerBoundSourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2BSWSizeWidthConversionSourceDecomposition
        graph charge threshold reassembly) :
    StandardTseitinMorgensternQ2BSWWidthLowerBoundSourceDecomposition
      graph charge threshold reassembly where
  source_citation_packet := packet.source_citation_packet
  tseitin_formula_definition_locator := packet.tseitin_formula_definition_locator
  expansion_definition_locator := packet.expansion_definition_locator
  theorem44_width_locator := packet.theorem44_width_locator
  size_width_conversion_locator :=
    packet.size_measure_definition_locator ++ "; " ++
    packet.general_size_width_locator ++ "; " ++
    packet.reassembly_width_size_map_statement
  formula_threshold_instantiation_locator :=
    packet.formula_threshold_instantiation_locator
  graph_convention_map_statement := packet.graph_convention_map_statement
  connectedness_map_statement := packet.connectedness_map_statement
  expansion_map_statement := packet.expansion_map_statement
  edge_variable_map_statement := packet.edge_variable_map_statement
  initial_width_map_statement :=
    packet.initial_width_map_statement ++ "; " ++
    packet.local_tree_line_count_map_statement
  odd_charge_map_statement := packet.odd_charge_map_statement
  remaining_width_obstruction_statement :=
    packet.remaining_size_width_obstruction_statement ++ "; " ++
    packet.tree_like_route_policy_statement
  bsw_tseitin_formula_definition_source :=
    packet.bsw_tseitin_formula_definition_source
  bsw_tseitin_formula_definition_source_holds :=
    packet.bsw_tseitin_formula_definition_source_holds
  bsw_expansion_definition_source := packet.bsw_expansion_definition_source
  bsw_expansion_definition_source_holds :=
    packet.bsw_expansion_definition_source_holds
  bsw_theorem44_width_lower_bound_source :=
    packet.bsw_theorem44_width_lower_bound_source
  bsw_theorem44_width_lower_bound_source_holds :=
    packet.bsw_theorem44_width_lower_bound_source_holds
  bsw_size_width_conversion_source :=
    packet.bsw_size_width_conversion_source
  bsw_size_width_conversion_source_holds :=
    packet.bsw_size_width_conversion_source_of_general_reassembly
      packet.bsw_source_size_measure_definition_source_holds
      reassembly.decomposition.width_size_constant_source_holds
  bsw_formula_threshold_instantiation_source :=
    packet.bsw_formula_threshold_instantiation_source
  bsw_formula_threshold_instantiation_source_holds :=
    packet.bsw_formula_threshold_instantiation_source_holds
  formula_threshold_source_line_lower_bound_of_width_decomposed_sources := by
    intro source_citation alignment graph_hardening odd_charge reassembly
      hwidth hsize hthreshold
    exact
      packet.formula_threshold_source_line_lower_bound_of_size_decomposed_sources
        source_citation
        alignment
        graph_hardening
        odd_charge
        reassembly
        hwidth
        hsize
        hthreshold

/--
Stage1746 decomposition of the BSW formula-threshold instantiation source fact.

The selected theorem-application lane should not carry a fresh threshold fact
when the q = 2 concrete-threshold reassembly packet already records the
source-side expansion-rate, formula-size conversion, base-conversion, eventual
threshold, and graph/formula rescaling obligations.  This packet replaces the
standalone `bsw_formula_threshold_instantiation_source` witness by an explicit
mapping from those existing reassembly obligations.
-/
structure StandardTseitinMorgensternQ2BSWFormulaThresholdInstantiationSourceDecomposition
    {Index : Type} (graph : Index -> StandardTseitinGraph)
    (charge : Index -> Nat -> Bool) (threshold : Index -> Nat)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) where
  size_width_source :
    StandardTseitinMorgensternQ2BSWSizeWidthConversionSourceDecomposition
      graph charge threshold reassembly
  formula_threshold_kind_locator : String
  expansion_rate_constant_locator : String
  formula_size_conversion_locator : String
  base_conversion_locator : String
  eventual_threshold_locator : String
  graph_formula_rescaling_locator : String
  source_threshold_kind_statement : String
  formula_threshold_instantiation_statement : String
  graph_rescaled_threshold_statement : String
  remaining_formula_threshold_obstruction_statement : String
  bsw_formula_threshold_instantiation_source : Prop
  bsw_formula_threshold_instantiation_source_of_reassembly :
    reassembly.decomposition.expansion_rate_constant_source ->
    reassembly.decomposition.formula_size_conversion_source ->
    reassembly.decomposition.base_conversion_source ->
    reassembly.decomposition.eventual_threshold_source ->
    reassembly.graph_formula_rescaling.base_conversion.graph_formula_rescaling_target ->
    bsw_formula_threshold_instantiation_source
  bsw_formula_threshold_instantiation_source_to_size_width_source :
    bsw_formula_threshold_instantiation_source ->
    size_width_source.bsw_formula_threshold_instantiation_source

def StandardTseitinMorgensternQ2BSWFormulaThresholdInstantiationSourceDecomposition.toBSWSizeWidthConversionSourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    {reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold}
    (packet :
      StandardTseitinMorgensternQ2BSWFormulaThresholdInstantiationSourceDecomposition
        graph charge threshold reassembly) :
    StandardTseitinMorgensternQ2BSWSizeWidthConversionSourceDecomposition
      graph charge threshold reassembly :=
  { packet.size_width_source with
    formula_threshold_instantiation_locator :=
      packet.formula_threshold_kind_locator ++ "; " ++
      packet.expansion_rate_constant_locator ++ "; " ++
      packet.formula_size_conversion_locator ++ "; " ++
      packet.base_conversion_locator ++ "; " ++
      packet.eventual_threshold_locator ++ "; " ++
      packet.graph_formula_rescaling_locator
    remaining_size_width_obstruction_statement :=
      packet.size_width_source.remaining_size_width_obstruction_statement ++
      "; " ++ packet.remaining_formula_threshold_obstruction_statement
    bsw_formula_threshold_instantiation_source :=
      packet.bsw_formula_threshold_instantiation_source
    bsw_formula_threshold_instantiation_source_holds :=
      packet.bsw_formula_threshold_instantiation_source_of_reassembly
        reassembly.decomposition.expansion_rate_constant_source_holds
        reassembly.decomposition.formula_size_conversion_source_holds
        reassembly.decomposition.base_conversion_source_holds
        reassembly.decomposition.eventual_threshold_source_holds
        reassembly.graph_formula_rescaling.toGraphFormulaRescalingTarget
    formula_threshold_source_line_lower_bound_of_size_decomposed_sources := by
      intro source_citation alignment graph_hardening odd_charge reassembly
        hwidth hsize hthreshold
      exact
        packet.size_width_source.formula_threshold_source_line_lower_bound_of_size_decomposed_sources
          source_citation
          alignment
          graph_hardening
          odd_charge
          reassembly
          hwidth
          hsize
          (packet.bsw_formula_threshold_instantiation_source_to_size_width_source
            hthreshold) }

/--
Narrow source-side shell for the selected Morgenstern q = 2 BSW witness lane.

The shell carries source-side graph data directly as `StandardTseitinGraph`,
avoiding the old `GraphEncodingData` convention.  Its proof obligations are
exactly the five remaining fields from the Stage1688 external BSW certificate
premise record; no extra lower-bound proposition is introduced here.
-/
structure StandardTseitinMorgensternQ2SourceFamilyShell where
  Index : Type
  graph : Index -> StandardTseitinGraph
  charge : Index -> Nat -> Bool
  threshold : Index -> Nat
  one_variable_per_undirected_edge :
    forall i : Index, oneListedEdgePerUndirectedEdge (graph i).edges
  odd_total_charge :
    forall i : Index, standardOddTotalCharge (graph i) (charge i)
  bsw_graph_family : standardBSWGraphFamilyPremise graph
  threshold_family_match :
    standardTseitinBSWThresholdFamilyMatch graph charge threshold
  source_trace_line_lower_bound :
    CNFResolution.ResolutionFamilyTraceLineLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)

def StandardTseitinMorgensternQ2SourceFamilyShell.toExternalBSWCertificatePremises
    (shell : StandardTseitinMorgensternQ2SourceFamilyShell) :
    StandardTseitinExternalBSWCertificatePremises
      (Index := shell.Index) shell.graph shell.charge shell.threshold where
  one_variable_per_undirected_edge := shell.one_variable_per_undirected_edge
  odd_total_charge := shell.odd_total_charge
  bsw_graph_family := shell.bsw_graph_family
  threshold_family_match := shell.threshold_family_match
  source_trace_line_lower_bound := shell.source_trace_line_lower_bound

def StandardTseitinMorgensternQ2SourceFamilyShell.toSourceFamilyCertificate
    (shell : StandardTseitinMorgensternQ2SourceFamilyShell) :
    StandardTseitinCNFSourceFamilyCertificate
      (standardTseitinExternalBSWSourceTarget
        (Index := shell.Index)
        shell.graph shell.charge shell.threshold
        standardTseitinMorgensternQ2SourceName
        standardTseitinMorgensternQ2SourceStatement) :=
  StandardTseitinExternalBSWCertificatePremises.toSourceFamilyCertificate
    (sourceName:=standardTseitinMorgensternQ2SourceName)
    (sourceStatement:=standardTseitinMorgensternQ2SourceStatement)
    (StandardTseitinMorgensternQ2SourceFamilyShell.toExternalBSWCertificatePremises
      shell)

theorem standardTseitinMorgensternQ2LowerBound_of_sourceFamilyShell
    (shell : StandardTseitinMorgensternQ2SourceFamilyShell) :
    CNFResolution.ResolutionSizeFamilyLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget
        (Index := shell.Index) shell.graph shell.charge shell.threshold) := by
  exact standardTseitinExternalBSWLowerBound_of_certificatePremises
    (sourceName:=standardTseitinMorgensternQ2SourceName)
    (sourceStatement:=standardTseitinMorgensternQ2SourceStatement)
    (StandardTseitinMorgensternQ2SourceFamilyShell.toExternalBSWCertificatePremises
      shell)

def StandardTseitinMorgensternQ2SourceFamilyShell.fromTracePremiseDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (hone :
      forall i : Index, oneListedEdgePerUndirectedEdge (graph i).edges)
    (hodd : forall i : Index, standardOddTotalCharge (graph i) (charge i))
    (hbsw : standardBSWGraphFamilyPremise graph)
    (hthreshold :
      standardTseitinBSWThresholdFamilyMatch graph charge threshold)
    (htrace :
      StandardTseitinMorgensternQ2SourceTracePremiseDecomposition
        graph charge threshold) :
    StandardTseitinMorgensternQ2SourceFamilyShell where
  Index := Index
  graph := graph
  charge := charge
  threshold := threshold
  one_variable_per_undirected_edge := hone
  odd_total_charge := hodd
  bsw_graph_family := hbsw
  threshold_family_match := hthreshold
  source_trace_line_lower_bound :=
    StandardTseitinMorgensternQ2SourceTracePremiseDecomposition.toTraceLineLowerBound
      htrace

/--
High-level graph-rescaled explicit source shell.

This wraps the existing Morgenstern q = 2 source-family shell with the additional
data needed for the explicit exponential size surface: the original formula-size
threshold, its graph-rescaled target equality, eventual applicability at graph
vertices, and the concrete-threshold source packet.
-/
structure StandardTseitinMorgensternQ2GraphRescaledExplicitSourceFamilyShell where
  source_shell : StandardTseitinMorgensternQ2SourceFamilyShell
  formulaThreshold : CNFResolution.ResolutionAsymptoticExponentialThreshold
  graph_rescaled_threshold_matches :
    forall i : source_shell.Index,
      source_shell.threshold i =
        formulaThreshold.threshold ((source_shell.graph i).n * 4)
  graph_rescaled_parameters_eventual :
    forall i : source_shell.Index,
      (standardTseitinMorgensternQ2GraphRescaledThreshold
        formulaThreshold).appliesAt (source_shell.graph i).n
  concrete_threshold_source_packet :
    StandardTseitinBSWConcreteThresholdSourcePacket formulaThreshold

def StandardTseitinMorgensternQ2GraphRescaledExplicitSourceFamilyShell.resolutionTarget
    (shell : StandardTseitinMorgensternQ2GraphRescaledExplicitSourceFamilyShell) :
    CNFResolution.ResolutionSizeFamilyTarget :=
  StandardTseitinResolutionFamilyTarget
    (Index:=shell.source_shell.Index)
    shell.source_shell.graph shell.source_shell.charge
    shell.source_shell.threshold

def StandardTseitinMorgensternQ2GraphRescaledExplicitSourceFamilyShell.thresholdInterpretation
    (shell : StandardTseitinMorgensternQ2GraphRescaledExplicitSourceFamilyShell) :
    CNFResolution.ResolutionFamilyThresholdInterpretation
      shell.resolutionTarget :=
  standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
    (Index:=shell.source_shell.Index)
    shell.source_shell.graph shell.source_shell.charge
    shell.source_shell.threshold shell.formulaThreshold
    shell.graph_rescaled_threshold_matches
    shell.graph_rescaled_parameters_eventual

def StandardTseitinMorgensternQ2GraphRescaledExplicitSourceFamilyShell.fromTracePremiseDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (hone :
      forall i : Index, oneListedEdgePerUndirectedEdge (graph i).edges)
    (hodd : forall i : Index, standardOddTotalCharge (graph i) (charge i))
    (hbsw : standardBSWGraphFamilyPremise graph)
    (hthreshold :
      standardTseitinBSWThresholdFamilyMatch graph charge threshold)
    (htrace :
      StandardTseitinMorgensternQ2SourceTracePremiseDecomposition
        graph charge threshold)
    (formulaThreshold :
      CNFResolution.ResolutionAsymptoticExponentialThreshold)
    (hgraphThreshold :
      forall i : Index,
        threshold i = formulaThreshold.threshold ((graph i).n * 4))
    (heventual :
      forall i : Index,
        (standardTseitinMorgensternQ2GraphRescaledThreshold
          formulaThreshold).appliesAt (graph i).n)
    (packet :
      StandardTseitinBSWConcreteThresholdSourcePacket formulaThreshold) :
    StandardTseitinMorgensternQ2GraphRescaledExplicitSourceFamilyShell where
  source_shell :=
    StandardTseitinMorgensternQ2SourceFamilyShell.fromTracePremiseDecomposition
      hone hodd hbsw hthreshold htrace
  formulaThreshold := formulaThreshold
  graph_rescaled_threshold_matches := hgraphThreshold
  graph_rescaled_parameters_eventual := heventual
  concrete_threshold_source_packet := packet

def StandardTseitinMorgensternQ2GraphRescaledExplicitSourceFamilyShell.fromConcreteThresholdReassembly
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (hone :
      forall i : Index, oneListedEdgePerUndirectedEdge (graph i).edges)
    (hodd : forall i : Index, standardOddTotalCharge (graph i) (charge i))
    (hbsw : standardBSWGraphFamilyPremise graph)
    (hthreshold :
      standardTseitinBSWThresholdFamilyMatch graph charge threshold)
    (htrace :
      StandardTseitinMorgensternQ2SourceTracePremiseDecomposition
        graph charge threshold)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) :
    StandardTseitinMorgensternQ2GraphRescaledExplicitSourceFamilyShell :=
  StandardTseitinMorgensternQ2GraphRescaledExplicitSourceFamilyShell.fromTracePremiseDecomposition
    hone hodd hbsw hthreshold htrace
    reassembly.formulaThreshold
    reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
    reassembly.graph_formula_rescaling.graph_rescaled_eventual
    reassembly.toReassembledSourcePacket

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_explicitSourceFamilyShell
    (shell :
      StandardTseitinMorgensternQ2GraphRescaledExplicitSourceFamilyShell) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      shell.resolutionTarget shell.thresholdInterpretation := by
  have hsource :
      CNFResolution.ResolutionFamilyTraceLineLowerBoundPremise
        shell.resolutionTarget := by
    change CNFResolution.ResolutionFamilyTraceLineLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget
        (Index:=shell.source_shell.Index)
        shell.source_shell.graph shell.source_shell.charge
        shell.source_shell.threshold)
    exact shell.source_shell.source_trace_line_lower_bound
  have hconcrete :
      shell.thresholdInterpretation.sourceThreshold.concreteLowerBound := by
    change (standardTseitinMorgensternQ2GraphRescaledThreshold
      shell.formulaThreshold).concreteLowerBound
    exact standardTseitinMorgensternQ2GraphRescaledConcreteLowerBound_of_sourcePacket
      shell.formulaThreshold shell.concrete_threshold_source_packet
  exact
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise_of_traceLineLowerBound
      (target:=shell.resolutionTarget)
      (interpretation:=shell.thresholdInterpretation)
      hsource hconcrete

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_concreteThresholdReassembly
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (hone :
      forall i : Index, oneListedEdgePerUndirectedEdge (graph i).edges)
    (hodd : forall i : Index, standardOddTotalCharge (graph i) (charge i))
    (hbsw : standardBSWGraphFamilyPremise graph)
    (hthreshold :
      standardTseitinBSWThresholdFamilyMatch graph charge threshold)
    (htrace :
      StandardTseitinMorgensternQ2SourceTracePremiseDecomposition
        graph charge threshold)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  let shell :=
    StandardTseitinMorgensternQ2GraphRescaledExplicitSourceFamilyShell.fromConcreteThresholdReassembly
      hone hodd hbsw hthreshold htrace reassembly
  change CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
    shell.resolutionTarget shell.thresholdInterpretation
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_explicitSourceFamilyShell
      shell

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_concreteThresholdReassemblyNoThresholdPremise
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (hone :
      forall i : Index, oneListedEdgePerUndirectedEdge (graph i).edges)
    (hodd : forall i : Index, standardOddTotalCharge (graph i) (charge i))
    (hbsw : standardBSWGraphFamilyPremise graph)
    (htrace :
      StandardTseitinMorgensternQ2SourceTracePremiseDecomposition
        graph charge threshold)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_concreteThresholdReassembly
      hone hodd hbsw reassembly.toThresholdFamilyMatch htrace reassembly

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_graphFamilyHardening
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (hodd : forall i : Index, standardOddTotalCharge (graph i) (charge i))
    (htrace :
      StandardTseitinMorgensternQ2SourceTracePremiseDecomposition
        graph charge threshold)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_concreteThresholdReassemblyNoThresholdPremise
      graph_hardening.oneVariablePerUndirectedEdge
      hodd graph_hardening.toBSWGraphFamilyPremise htrace reassembly

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_graphFamilyHardeningAndOddCharge
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge)
    (htrace :
      StandardTseitinMorgensternQ2SourceTracePremiseDecomposition
        graph charge threshold)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_graphFamilyHardening
      graph_hardening odd_charge.oddTotalCharge htrace reassembly

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_graphRescaledSourceTrace
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold)
    (source_trace :
      StandardTseitinMorgensternQ2GraphRescaledSourceTracePremise
        graph charge threshold reassembly) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_graphRescaledSourcePacket
      (graph:=graph)
      (charge:=charge)
      (threshold:=threshold)
      (formulaThreshold:=reassembly.formulaThreshold)
      (hthreshold:=
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled)
      (heventual:=reassembly.graph_formula_rescaling.graph_rescaled_eventual)
      (standardTseitinMorgensternQ2FormulaSizeGraphVertexBridge_of_threeRegularFamily
        graph_hardening.threeRegularFamily)
      (source_trace.toFormulaThresholdSourceLineLowerBound
        graph_hardening odd_charge)
      reassembly.toReassembledSourcePacket

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_formulaThresholdSourceLineBoundSource
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold)
    (source_line :
      StandardTseitinMorgensternQ2FormulaThresholdSourceLineBoundSource
        graph charge threshold reassembly) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_graphRescaledSourceTrace
      graph_hardening
      odd_charge
      reassembly
      source_line.toGraphRescaledSourceTracePremise

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswSourceTheoremApplicationDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold)
    (source_application :
      StandardTseitinMorgensternQ2BSWSourceTheoremApplicationDecomposition
        graph charge threshold reassembly) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_formulaThresholdSourceLineBoundSource
      graph_hardening
      odd_charge
      reassembly
      source_application.toFormulaThresholdSourceLineBoundSource

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswWidthLowerBoundSourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold)
    (width_source :
      StandardTseitinMorgensternQ2BSWWidthLowerBoundSourceDecomposition
        graph charge threshold reassembly) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswSourceTheoremApplicationDecomposition
      graph_hardening
      odd_charge
      reassembly
      width_source.toBSWSourceTheoremApplicationDecomposition

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswTheorem44WidthKernelSourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold)
    (width_kernel_source :
      StandardTseitinMorgensternQ2BSWTheorem44WidthKernelSourceDecomposition
        graph charge threshold reassembly) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswWidthLowerBoundSourceDecomposition
      graph_hardening
      odd_charge
      reassembly
      width_kernel_source.toBSWWidthLowerBoundSourceDecomposition

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswProperSubsetSatisfiabilitySourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold)
    (proper_subset_source :
      StandardTseitinMorgensternQ2BSWProperSubsetSatisfiabilitySourceDecomposition
        graph charge threshold reassembly) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswTheorem44WidthKernelSourceDecomposition
      graph_hardening
      odd_charge
      reassembly
      proper_subset_source.toBSWTheorem44WidthKernelSourceDecomposition

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswOddChargeInconsistencySourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold)
    (odd_charge_source :
      StandardTseitinMorgensternQ2BSWOddChargeInconsistencySourceDecomposition
        graph charge threshold reassembly) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswProperSubsetSatisfiabilitySourceDecomposition
      graph_hardening
      odd_charge
      reassembly
      (odd_charge_source.toBSWProperSubsetSatisfiabilitySourceDecomposition
        odd_charge)

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswChargeFlipSourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold)
    (charge_flip_source :
      StandardTseitinMorgensternQ2BSWChargeFlipSourceDecomposition
        graph charge threshold reassembly) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswOddChargeInconsistencySourceDecomposition
      graph_hardening
      odd_charge
      reassembly
      (charge_flip_source.toBSWOddChargeInconsistencySourceDecomposition
        odd_charge)

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswFlippedInstanceSatisfiabilitySourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold)
    (flipped_instance_source :
      StandardTseitinMorgensternQ2BSWFlippedInstanceSatisfiabilitySourceDecomposition
        graph charge threshold reassembly) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswChargeFlipSourceDecomposition
      graph_hardening
      odd_charge
      reassembly
      (flipped_instance_source.toBSWChargeFlipSourceDecomposition
        odd_charge)

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswProperSubfamilyRestrictionSourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold)
    (proper_subfamily_source :
      StandardTseitinMorgensternQ2BSWProperSubfamilyRestrictionSourceDecomposition
        graph charge threshold reassembly) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswFlippedInstanceSatisfiabilitySourceDecomposition
      graph_hardening
      odd_charge
      reassembly
      (proper_subfamily_source.toBSWFlippedInstanceSatisfiabilitySourceDecomposition
        odd_charge)

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswParitySensitivitySourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold)
    (parity_sensitivity_source :
      StandardTseitinMorgensternQ2BSWParitySensitivitySourceDecomposition
        graph charge threshold reassembly) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswProperSubfamilyRestrictionSourceDecomposition
      graph_hardening
      odd_charge
      reassembly
      parity_sensitivity_source.toBSWProperSubfamilyRestrictionSourceDecomposition

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswAxiomCompatibilitySourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold)
    (axiom_compatibility_source :
      StandardTseitinMorgensternQ2BSWAxiomCompatibilitySourceDecomposition
        graph charge threshold reassembly) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswParitySensitivitySourceDecomposition
      graph_hardening
      odd_charge
      reassembly
      axiom_compatibility_source.toBSWParitySensitivitySourceDecomposition

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswBoundaryExpansionSourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold)
    (boundary_expansion_source :
      StandardTseitinMorgensternQ2BSWBoundaryExpansionSourceDecomposition
        graph charge threshold reassembly) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswAxiomCompatibilitySourceDecomposition
      graph_hardening
      odd_charge
      reassembly
      (boundary_expansion_source.toBSWAxiomCompatibilitySourceDecomposition
        graph_hardening)

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswWidthExpansionStrategySourceBoundary
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold)
    (strategy_source :
      StandardTseitinMorgensternQ2BSWWidthExpansionStrategySourceBoundary
        graph charge threshold reassembly) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswBoundaryExpansionSourceDecomposition
      graph_hardening
      odd_charge
      reassembly
      strategy_source.toBSWBoundaryExpansionSourceDecomposition

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswSizeWidthConversionSourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold)
    (size_width_source :
      StandardTseitinMorgensternQ2BSWSizeWidthConversionSourceDecomposition
        graph charge threshold reassembly) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswWidthLowerBoundSourceDecomposition
      graph_hardening
      odd_charge
      reassembly
      size_width_source.toBSWWidthLowerBoundSourceDecomposition

theorem standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswFormulaThresholdInstantiationSourceDecomposition
    {Index : Type} {graph : Index -> StandardTseitinGraph}
    {charge : Index -> Nat -> Bool} {threshold : Index -> Nat}
    (graph_hardening :
      StandardTseitinMorgensternQ2GraphFamilyHardening graph)
    (odd_charge :
      StandardTseitinMorgensternQ2OddChargeFamily graph charge)
    (reassembly :
      StandardTseitinMorgensternQ2ConcreteThresholdReassembly
        graph charge threshold)
    (formula_threshold_source :
      StandardTseitinMorgensternQ2BSWFormulaThresholdInstantiationSourceDecomposition
        graph charge threshold reassembly) :
    CNFResolution.ResolutionFamilyExplicitExponentialSizeLowerBoundPremise
      (StandardTseitinResolutionFamilyTarget graph charge threshold)
      (standardTseitinMorgensternQ2GraphRescaledThresholdInterpretation
        graph charge threshold reassembly.formulaThreshold
        reassembly.graph_formula_rescaling.target_threshold_matches_graph_rescaled
        reassembly.graph_formula_rescaling.graph_rescaled_eventual) := by
  exact
    standardTseitinMorgensternQ2ExplicitExponentialSizeLowerBound_of_bswSizeWidthConversionSourceDecomposition
      graph_hardening
      odd_charge
      reassembly
      formula_threshold_source.toBSWSizeWidthConversionSourceDecomposition

/-- Edge at index i (requires length agreement). -/
def edgeAt (G : TseitinModel.Graph) (hm : G.m = G.edges.length) (i : Fin G.m) :
    TseitinModel.UEdge :=
  G.edges.get (Fin.cast hm i)

/-- Incident edge indices for a vertex (requires length agreement). -/
def incidentIndices (G : TseitinModel.Graph) (hm : G.m = G.edges.length) (v : Nat) :
    List (Fin G.m) :=
  (allFin G.m).filter (fun i => TseitinModel.UEdge.incident (edgeAt G hm i) v)

/-- Mapping `edgeAt` over all finite edge indices reconstructs the graph edge list. -/
theorem edgeAt_allFin_map_eq_edges
    (G : TseitinModel.Graph) (hm : G.m = G.edges.length) :
    List.map (fun i : Fin G.m => edgeAt G hm i) (allFin G.m) = G.edges := by
  cases G with
  | mk n m edges undirected no_self endpoints =>
      simp at hm
      subst m
      simpa [edgeAt] using allFin_map_get edges

/--
The local finite-index incident list has the same length as the graph-level
incident edge list.  This is the reusable locality bridge behind the Stage1776
uniform cycle accounting theorem.
-/
theorem incidentIndices_length_eq_degree
    (G : TseitinModel.Graph) (hm : G.m = G.edges.length) (v : Nat) :
    (incidentIndices G hm v).length = TseitinModel.degree G v := by
  let f := fun i : Fin G.m => edgeAt G hm i
  let q := fun e : TseitinModel.UEdge => TseitinModel.UEdge.incident e v
  have hmap : List.map f (allFin G.m) = G.edges := by
    simpa [f] using edgeAt_allFin_map_eq_edges G hm
  calc
    (incidentIndices G hm v).length
        = (List.filter (fun i : Fin G.m => q (f i)) (allFin G.m)).length := by
            rfl
    _ = (List.map f
          (List.filter (fun i : Fin G.m => q (f i)) (allFin G.m))).length := by
            simp
    _ = (List.filter q (List.map f (allFin G.m))).length := by
            rw [List.filter_map]
            rfl
    _ = (List.filter q G.edges).length := by
            rw [hmap]
    _ = TseitinModel.degree G v := by
            rfl

/-- Tseitin CNFData built from a TseitinModel.Graph's incident structure. -/
def TseitinDataFromModel (G : TseitinModel.Graph) (hm : G.m = G.edges.length)
    (charge : Nat -> Bool) : CNFData.CNFData :=
  TseitinDataFromIncident G.n G.m (incidentIndices G hm) charge

/-- Tseitin CNFData built from a concrete graph encoding. -/
def TseitinDataFromEncoding (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool) : CNFData.CNFData :=
  TseitinDataFromModel (TseitinModel.GraphEncodingData.toGraph enc)
    (TseitinModel.m_eq_edges_length_of_encoding enc) charge

/-- Explicit CNF formula built from a TseitinModel.Graph's incident structure. -/
def TseitinCNFFormulaFromModel (G : TseitinModel.Graph)
    (hm : G.m = G.edges.length) (charge : Nat -> Bool) :
    CNFModel.CNF G.m :=
  tseitinClausesFromIncident G.n G.m (incidentIndices G hm) charge

/-- Explicit CNF formula built from a graph encoding, typed for CNF-resolution. -/
def TseitinCNFFormulaFromEncoding (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool) :
    CNFModel.CNF (TseitinModel.GraphEncodingData.toGraph enc).m :=
  TseitinCNFFormulaFromModel (TseitinModel.GraphEncodingData.toGraph enc)
    (TseitinModel.m_eq_edges_length_of_encoding enc) charge

theorem tseitinCNFFormulaFromEncoding_eq_data_clauses
    (enc : TseitinModel.GraphEncodingData) (charge : Nat -> Bool) :
    TseitinCNFFormulaFromEncoding enc charge =
      (TseitinDataFromEncoding enc charge).clauses := by
  rfl

/-- Convenience: Tseitin CNFData for the three-cycle encoding with a charge function. -/
def TseitinDataThreeCycle (charge : Nat -> Bool) : CNFData.CNFData :=
  TseitinDataFromEncoding TseitinModel.encoding_three_cycle charge

/-- Tseitin parity CNF formula from a concrete graph encoding (direct parity clauses). -/
def TseitinParityFormulaFromEncoding (enc : TseitinModel.GraphEncodingData)
    (charge : Nat -> Bool) :
    ResoplusPDT.CNFFormula (Basic.CNF.mk (TseitinModel.GraphEncodingData.toGraph enc).m) :=
  let G := TseitinModel.GraphEncodingData.toGraph enc
  let hme := TseitinModel.m_eq_edges_length_of_encoding enc
  tseitinParityFormulaFromIncident G.n G.m (incidentIndices G hme) charge

/-- Parity-clause Tseitin CNF formula for the three-cycle encoding. -/
def TseitinParityFormulaThreeCycle (charge : Nat -> Bool) :
    ResoplusPDT.CNFFormula
      (Basic.CNF.mk (TseitinModel.GraphEncodingData.toGraph
        TseitinModel.encoding_three_cycle).m) :=
  TseitinParityFormulaFromEncoding TseitinModel.encoding_three_cycle charge

/-- Concrete odd charge for three-cycle: vertex 0 has charge true. -/
def threeCycleCharge (v : Nat) : Bool :=
  v = 0

def TseitinDataThreeCycleCharge : CNFData.CNFData :=
  TseitinDataThreeCycle threeCycleCharge

def TseitinParityFormulaThreeCycleCharge :
    ResoplusPDT.CNFFormula
      (Basic.CNF.mk (TseitinModel.GraphEncodingData.toGraph
        TseitinModel.encoding_three_cycle).m) :=
  TseitinParityFormulaThreeCycle threeCycleCharge

/-- Convenience: Tseitin CNFData for a four-cycle encoding with a charge function. -/
def TseitinDataFourCycle (charge : Nat -> Bool) : CNFData.CNFData :=
  TseitinDataFromEncoding (TseitinModel.encoding_cycle_derived 4 (by decide)) charge

/-- Parity-clause Tseitin CNF formula for the four-cycle encoding. -/
def TseitinParityFormulaFourCycle (charge : Nat -> Bool) :
    ResoplusPDT.CNFFormula
      (Basic.CNF.mk (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived 4 (by decide))).m) :=
  TseitinParityFormulaFromEncoding (TseitinModel.encoding_cycle_derived 4 (by decide)) charge

/-- Concrete odd charge for four-cycle: vertex 0 has charge true. -/
def fourCycleCharge (v : Nat) : Bool :=
  v = 0

def TseitinDataFourCycleCharge : CNFData.CNFData :=
  TseitinDataFourCycle fourCycleCharge

/-- Parity-clause Tseitin CNF formula for the four-cycle with fixed odd charge. -/
def TseitinParityFormulaFourCycleCharge :
    ResoplusPDT.CNFFormula
      (Basic.CNF.mk (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived 4 (by decide))).m) :=
  TseitinParityFormulaFourCycle fourCycleCharge

def TseitinClausesThreeCycleCharge : CNFModel.CNF (TseitinDataThreeCycleCharge.base.vcount) :=
  TseitinDataThreeCycleCharge.clauses

def TseitinClausesFourCycleCharge : CNFModel.CNF (TseitinDataFourCycleCharge.base.vcount) :=
  TseitinDataFourCycleCharge.clauses

def TseitinClausesThreeCycleChargeRepr : String :=
  toString (repr TseitinClausesThreeCycleCharge)

abbrev threeCycleGraph : TseitinModel.Graph :=
  TseitinModel.GraphEncodingData.toGraph TseitinModel.encoding_three_cycle

abbrev threeCycleHm : threeCycleGraph.m = threeCycleGraph.edges.length :=
  TseitinModel.m_eq_edges_length_of_encoding TseitinModel.encoding_three_cycle

abbrev fourCycleGraph : TseitinModel.Graph :=
  TseitinModel.GraphEncodingData.toGraph (TseitinModel.encoding_cycle_derived 4 (by decide))

abbrev fourCycleHm : fourCycleGraph.m = fourCycleGraph.edges.length :=
  TseitinModel.m_eq_edges_length_of_encoding (TseitinModel.encoding_cycle_derived 4 (by decide))

def TseitinCNFFormulaThreeCycleCharge : CNFModel.CNF threeCycleGraph.m :=
  TseitinCNFFormulaFromEncoding TseitinModel.encoding_three_cycle threeCycleCharge

def TseitinCNFFormulaFourCycleCharge : CNFModel.CNF fourCycleGraph.m :=
  TseitinCNFFormulaFromEncoding (TseitinModel.encoding_cycle_derived 4 (by decide))
    fourCycleCharge

theorem threeCycle_cnfResolution_formula_eq_data_clauses :
    TseitinCNFFormulaThreeCycleCharge = TseitinClausesThreeCycleCharge := by
  rfl

theorem fourCycle_cnfResolution_formula_eq_data_clauses :
    TseitinCNFFormulaFourCycleCharge = TseitinClausesFourCycleCharge := by
  rfl

/--
Stage1761 first structural-simplification smoke target.

The concrete three-cycle Tseitin CNF has no empty clause, no unit clause, and
no pure literal under the computable `CNFModel` cheap-simplification signal.
This is a finite candidate-killer test for structural SAT simplification, not
a hardness or general SAT-collapse claim.
-/
theorem threeCycle_tseitin_noCheapSimplificationSignal :
    CNFModel.NoCheapSimplificationSignal TseitinCNFFormulaThreeCycleCharge := by
  change CNFModel.noCheapSimplificationSignal TseitinCNFFormulaThreeCycleCharge = true
  native_decide

/--
Stage1761 symmetric finite smoke target for the four-cycle Tseitin CNF.

The same cheap simplification signal is absent here as well, giving the general SAT-collapse
algorithmic lane a second concrete adversarial input before any asymptotic
claims are considered.
-/
theorem fourCycle_tseitin_noCheapSimplificationSignal :
    CNFModel.NoCheapSimplificationSignal TseitinCNFFormulaFourCycleCharge := by
  change CNFModel.noCheapSimplificationSignal TseitinCNFFormulaFourCycleCharge = true
  native_decide

/--
Stage1763 first structural-simplifier fixed-point certificate for the concrete
three-cycle Tseitin CNF.  Duplicate-literal deletion plus tautological-clause
deletion makes no progress on this smoke input.
-/
theorem threeCycle_tseitin_branchFreeCleanupFixedPoint :
    CNFModel.BranchFreeCleanupFixedPoint TseitinCNFFormulaThreeCycleCharge := by
  change
    CNFModel.branchFreeCleanupFixedPointSignal
      TseitinCNFFormulaThreeCycleCharge = true
  native_decide

/--
Stage1763 first structural-simplifier fixed-point certificate for the concrete
four-cycle Tseitin CNF.  This symmetric smoke input is also already fixed by
the branch-free cleanup pass.
-/
theorem fourCycle_tseitin_branchFreeCleanupFixedPoint :
    CNFModel.BranchFreeCleanupFixedPoint TseitinCNFFormulaFourCycleCharge := by
  change
    CNFModel.branchFreeCleanupFixedPointSignal
      TseitinCNFFormulaFourCycleCharge = true
  native_decide

/-!
Stage1765 recognized GF(2) normalization candidate.

This is deliberately not an arbitrary-CNF SAT algorithm.  The operation is
guarded by recognition: for Tseitin instances whose graph encoding is known,
the expanded CNF vertex clauses are represented by the compact parity-equation
formula already present in the local Res(oplus) layer.  The first measurable
test is whether this algebraic representation makes progress on the Stage1761/Stage1763
smoke inputs where syntactic cleanup was fixed.
-/

/-- A recognized algebraic normalization surface for a CNF with a compact GF(2) view. -/
structure RecognizedGF2NormalizationSurface (m : Nat) where
  expandedCNF : CNFModel.CNF m
  compactGF2 : ResoplusPDT.CNFFormula (Basic.CNF.mk m)

/-- Expanded CNF resource measure: number of ordinary CNF clauses. -/
def RecognizedGF2NormalizationSurface.expandedClauseCount {m : Nat}
    (s : RecognizedGF2NormalizationSurface m) : Nat :=
  s.expandedCNF.length

/-- Compact algebraic resource measure: number of GF(2) equations. -/
def RecognizedGF2NormalizationSurface.equationCount {m : Nat}
    (s : RecognizedGF2NormalizationSurface m) : Nat :=
  s.compactGF2.length

/--
Correctness invariant required of the recognized GF(2) normalization surface.

Stage1765 records this as the semantic standard: compact equations must preserve
the satisfiability semantics of the expanded CNF for every assignment.  Concrete
compression below is a progress test; a future gate should push more of this
invariant into reusable checked theorems for broader recognized families.
-/
def RecognizedGF2NormalizationSurface.correctnessInvariant {m : Nat}
    (s : RecognizedGF2NormalizationSurface m) : Prop :=
  forall a : CNFModel.Assignment m,
    CNFModel.cnfSat a s.expandedCNF <->
      ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a s.compactGF2

/-- The recognized algebraic representation is smaller than the expanded CNF. -/
def RecognizedGF2NormalizationSurface.compressionProgress {m : Nat}
    (s : RecognizedGF2NormalizationSurface m) : Prop :=
  s.equationCount < s.expandedClauseCount

/-- Recognized Tseitin normalization from expanded CNF clauses to parity equations. -/
def recognizedTseitinGF2SurfaceFromEncoding
    (enc : TseitinModel.GraphEncodingData) (charge : Nat -> Bool) :
    RecognizedGF2NormalizationSurface
      (TseitinModel.GraphEncodingData.toGraph enc).m :=
  { expandedCNF := TseitinCNFFormulaFromEncoding enc charge
    compactGF2 := TseitinParityFormulaFromEncoding enc charge }

/-- Stage1765 GF(2) surface for the three-cycle smoke input. -/
def threeCycleGF2NormalizationSurface :
    RecognizedGF2NormalizationSurface threeCycleGraph.m :=
  recognizedTseitinGF2SurfaceFromEncoding
    TseitinModel.encoding_three_cycle threeCycleCharge

/-- Stage1765 GF(2) surface for the four-cycle smoke input. -/
def fourCycleGF2NormalizationSurface :
    RecognizedGF2NormalizationSurface fourCycleGraph.m :=
  recognizedTseitinGF2SurfaceFromEncoding
    (TseitinModel.encoding_cycle_derived 4 (by decide)) fourCycleCharge

/--
The three-cycle expanded Tseitin CNF compresses from 24 ordinary clauses to
3 parity equations under the recognized GF(2) surface.
-/
theorem threeCycle_tseitin_gf2CompressionCounts :
    threeCycleGF2NormalizationSurface.expandedClauseCount = 24 ∧
      threeCycleGF2NormalizationSurface.equationCount = 3 := by
  native_decide

/--
The four-cycle expanded Tseitin CNF compresses from 32 ordinary clauses to
4 parity equations under the recognized GF(2) surface.
-/
theorem fourCycle_tseitin_gf2CompressionCounts :
    fourCycleGF2NormalizationSurface.expandedClauseCount = 32 ∧
      fourCycleGF2NormalizationSurface.equationCount = 4 := by
  native_decide

/-- The recognized GF(2) surface makes resource progress on the three-cycle smoke input. -/
theorem threeCycle_tseitin_gf2CompressionProgress :
    threeCycleGF2NormalizationSurface.compressionProgress := by
  unfold RecognizedGF2NormalizationSurface.compressionProgress
  native_decide

/-- The recognized GF(2) surface makes resource progress on the four-cycle smoke input. -/
theorem fourCycle_tseitin_gf2CompressionProgress :
    fourCycleGF2NormalizationSurface.compressionProgress := by
  unfold RecognizedGF2NormalizationSurface.compressionProgress
  native_decide

/-!
Stage1766 semantic-preservation gate.

Compression is only useful as an algorithmic candidate if the compact GF(2)
view agrees with the expanded CNF under the same assignments.  The following
lemmas discharge that invariant for recognized Tseitin encodings by assembling
the existing vertex-level parity/CNF equivalence over the full incident list.
-/

/-- A recognized Tseitin vertex block has the same semantics as its parity equation. -/
theorem tseitinVertexBlock_gf2SemanticPreservation
    {m : Nat} (a : CNFModel.Assignment m) {vars : List (Fin m)}
    {charge : Bool} :
    CNFModel.cnfSat a (clausesForVertex vars charge) <->
      ResoplusPDT.ClauseSat
        (F := Basic.CNF.mk m) a (parityClauseForVertex vars charge) := by
  exact Iff.symm (clauseSat_parityClauseForVertex_iff_cnfSat_clausesForVertex a)

/--
The expanded Tseitin CNF assembled from incident lists has the same assignment
semantics as the compact GF(2) formula assembled from the same incident lists.
-/
theorem tseitinIncident_gf2SemanticPreservation
    {n m : Nat} (a : CNFModel.Assignment m)
    (incident : Nat -> List (Fin m)) (charge : Nat -> Bool) :
    CNFModel.cnfSat a (tseitinClausesFromIncident n m incident charge) <->
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk m) a
        (tseitinParityFormulaFromIncident n m incident charge) := by
  constructor
  · intro hcnf c hc
    unfold tseitinParityFormulaFromIncident at hc
    rcases List.mem_map.1 hc with ⟨v, hv, hcv⟩
    subst hcv
    exact
      (tseitinVertexBlock_gf2SemanticPreservation
        (m := m) a
        (vars := incident v) (charge := charge v)).1
        (cnfSat_clausesForVertex_of_cnfSat_tseitinClausesFromIncident
          (n := n) (m := m) (incident := incident) (charge := charge)
          (a := a) hv hcnf)
  · intro hgf2
    unfold tseitinClausesFromIncident
    apply cnfSat_foldl_append_of_sat_items
    · intro c hc
      cases hc
    · intro v hv
      exact
        (tseitinVertexBlock_gf2SemanticPreservation
          (m := m) a
          (vars := incident v) (charge := charge v)).2
          (hgf2
            (parityClauseForVertex (incident v) (charge v))
            (parityClauseForVertex_mem_tseitinParityFormulaFromIncident
              (n := n) (m := m) (incident := incident) (charge := charge) hv))

/-- Every recognized Tseitin GF(2) surface preserves assignment semantics. -/
theorem recognizedTseitinGF2SurfaceFromEncoding_correctnessInvariant
    (enc : TseitinModel.GraphEncodingData) (charge : Nat -> Bool) :
    (recognizedTseitinGF2SurfaceFromEncoding enc charge).correctnessInvariant := by
  intro a
  dsimp [RecognizedGF2NormalizationSurface.correctnessInvariant,
    recognizedTseitinGF2SurfaceFromEncoding, TseitinCNFFormulaFromEncoding,
    TseitinCNFFormulaFromModel, TseitinParityFormulaFromEncoding]
  exact
    tseitinIncident_gf2SemanticPreservation
      (n := (TseitinModel.GraphEncodingData.toGraph enc).n)
      (m := (TseitinModel.GraphEncodingData.toGraph enc).m)
      a
      (incidentIndices
        (TseitinModel.GraphEncodingData.toGraph enc)
        (TseitinModel.m_eq_edges_length_of_encoding enc))
      charge

/-- The three-cycle recognized GF(2) surface preserves assignment semantics. -/
theorem threeCycle_tseitin_gf2SemanticPreservation :
    threeCycleGF2NormalizationSurface.correctnessInvariant := by
  dsimp [threeCycleGF2NormalizationSurface]
  exact
    recognizedTseitinGF2SurfaceFromEncoding_correctnessInvariant
      TseitinModel.encoding_three_cycle threeCycleCharge

/-- The four-cycle recognized GF(2) surface preserves assignment semantics. -/
theorem fourCycle_tseitin_gf2SemanticPreservation :
    fourCycleGF2NormalizationSurface.correctnessInvariant := by
  dsimp [fourCycleGF2NormalizationSurface]
  exact
    recognizedTseitinGF2SurfaceFromEncoding_correctnessInvariant
      (TseitinModel.encoding_cycle_derived 4 (by decide)) fourCycleCharge

/-!
Stage1767 GF(2) elimination witness gate.

After Stage1765 compressed recognized Tseitin CNFs into parity equations and Stage1766
proved assignment-level preservation, this gate records the first checked
algorithmic output contract.  The operation is deliberately narrow: sum all
GF(2) equations.  If the variable side cancels to zero while the right-hand
side is odd, the compact parity formula is unsatisfiable, and semantic
preservation transfers the contradiction back to the expanded CNF surface.
-/

/-- Flatten all variables appearing in a compact GF(2) parity formula. -/
def gf2FormulaFlattenedVars {F : Basic.CNF}
    (phi : ResoplusPDT.CNFFormula F) : List (Fin F.vcount) :=
  phi.bind (fun c => c.vars)

/-- Assignment rows induced by all variables in a compact GF(2) parity formula. -/
def gf2FormulaAssignmentRows {F : Basic.CNF}
    (a : ResoplusPDT.Assignment F)
    (phi : ResoplusPDT.CNFFormula F) : List Bool :=
  phi.bind (fun c => c.vars.map a)

/-- XOR of all right-hand sides in a compact GF(2) parity formula. -/
def gf2FormulaRhsParity {F : Basic.CNF}
    (phi : ResoplusPDT.CNFFormula F) : Bool :=
  parity (phi.map (fun c => c.rhs))

/-- Linear resource measure for the all-equations GF(2) contradiction scan. -/
def gf2AllEquationsContradictionSize {F : Basic.CNF}
    (phi : ResoplusPDT.CNFFormula F) : Nat :=
  phi.length + (gf2FormulaFlattenedVars phi).length

/--
If every clause in a parity formula is satisfied by an assignment, the XOR of
all left-hand sides equals the XOR of all right-hand sides.
-/
theorem gf2FormulaParitySound_of_cnfSat
    {F : Basic.CNF} (a : ResoplusPDT.Assignment F)
    (phi : ResoplusPDT.CNFFormula F)
    (hsat : ResoplusPDT.CNFSat (F := F) a phi) :
    parity (gf2FormulaAssignmentRows a phi) = gf2FormulaRhsParity phi := by
  unfold gf2FormulaAssignmentRows gf2FormulaRhsParity
  exact
    parity_bind_eq_parity_map_of_parity_eq
      phi
      (fun c => c.vars.map a)
      (fun c => c.rhs)
      (by
        intro c hc
        have hbeq :
            (ResoplusPDT.parity (c.vars.map a) == c.rhs) = true := by
          simpa [ResoplusPDT.ClauseSat, ResoplusPDT.clauseEval] using
            hsat c hc
        have hres : ResoplusPDT.parity (c.vars.map a) = c.rhs :=
          bool_eq_of_beq_true hbeq
        simpa [resoplusParity_eq_parity] using hres)

/--
Checked output of the all-equations GF(2) contradiction operation.  It is a
certificate that the variable side cancels for every assignment and the
right-hand side has odd parity.
-/
structure GF2AllEquationsContradictionOutput {F : Basic.CNF}
    (phi : ResoplusPDT.CNFFormula F) where
  variableRowsCancel :
    forall a : ResoplusPDT.Assignment F,
      parity (gf2FormulaAssignmentRows a phi) = false
  rhsOdd : gf2FormulaRhsParity phi = true

/-- The resource size attached to a checked GF(2) all-equations output. -/
def GF2AllEquationsContradictionOutput.sizeMeasure
    {F : Basic.CNF} {phi : ResoplusPDT.CNFFormula F}
    (_out : GF2AllEquationsContradictionOutput phi) : Nat :=
  gf2AllEquationsContradictionSize phi

/-- Correctness: a checked all-equations GF(2) contradiction output proves unsat. -/
theorem GF2AllEquationsContradictionOutput.unsat
    {F : Basic.CNF} {phi : ResoplusPDT.CNFFormula F}
    (out : GF2AllEquationsContradictionOutput phi) :
    ResoplusPDT.CNFUnsat phi := by
  intro a hsat
  have hpar : false = true := by
    calc
      false = parity (gf2FormulaAssignmentRows a phi) := (out.variableRowsCancel a).symm
      _ = gf2FormulaRhsParity phi := gf2FormulaParitySound_of_cnfSat a phi hsat
      _ = true := out.rhsOdd
  cases hpar

/--
If the flattened variable side is a permutation of duplicate variable pairs,
then the left-hand side of the all-equations sum cancels for every assignment.
-/
theorem gf2FormulaAssignmentRows_cancel_of_flattenedVars_perm_dup
    {m : Nat} {phi : ResoplusPDT.CNFFormula (Basic.CNF.mk m)}
    (hperm :
      List.Perm (gf2FormulaFlattenedVars phi)
        ((allFin m).bind (fun v => [v, v]))) :
    forall a : ResoplusPDT.Assignment (Basic.CNF.mk m),
      parity (gf2FormulaAssignmentRows a phi) = false := by
  intro a
  calc
    parity (gf2FormulaAssignmentRows a phi)
        = parity ((gf2FormulaFlattenedVars phi).map a) := by
          simp [gf2FormulaAssignmentRows, gf2FormulaFlattenedVars, List.map_bind]
    _ = parity (((allFin m).bind (fun v => [v, v])).map a) := by
          exact parity_perm (hperm.map a)
    _ = parity ((allFin m).bind (fun v => [a v, a v])) := by
          simp [List.map_bind]
    _ = false := parity_bind_pairs_false a (allFin m)

/-- Three-cycle compact formula has duplicate-pair variable cancellation. -/
theorem threeCycle_tseitin_gf2FlattenedVarsPermDup :
    List.Perm
      (gf2FormulaFlattenedVars TseitinParityFormulaThreeCycleCharge)
      ((allFin threeCycleGraph.m).bind (fun v => [v, v])) := by
  native_decide

/-- Four-cycle compact formula has duplicate-pair variable cancellation. -/
theorem fourCycle_tseitin_gf2FlattenedVarsPermDup :
    List.Perm
      (gf2FormulaFlattenedVars TseitinParityFormulaFourCycleCharge)
      ((allFin fourCycleGraph.m).bind (fun v => [v, v])) := by
  native_decide

/-- The three-cycle compact formula has odd RHS parity. -/
theorem threeCycle_tseitin_gf2RhsOdd :
    gf2FormulaRhsParity TseitinParityFormulaThreeCycleCharge = true := by
  native_decide

/-- The four-cycle compact formula has odd RHS parity. -/
theorem fourCycle_tseitin_gf2RhsOdd :
    gf2FormulaRhsParity TseitinParityFormulaFourCycleCharge = true := by
  native_decide

/-- Checked GF(2) all-equations contradiction output for the three-cycle smoke input. -/
def threeCycle_tseitin_gf2ContradictionOutput :
    GF2AllEquationsContradictionOutput TseitinParityFormulaThreeCycleCharge where
  variableRowsCancel :=
    gf2FormulaAssignmentRows_cancel_of_flattenedVars_perm_dup
      threeCycle_tseitin_gf2FlattenedVarsPermDup
  rhsOdd := threeCycle_tseitin_gf2RhsOdd

/-- Checked GF(2) all-equations contradiction output for the four-cycle smoke input. -/
def fourCycle_tseitin_gf2ContradictionOutput :
    GF2AllEquationsContradictionOutput TseitinParityFormulaFourCycleCharge where
  variableRowsCancel :=
    gf2FormulaAssignmentRows_cancel_of_flattenedVars_perm_dup
      fourCycle_tseitin_gf2FlattenedVarsPermDup
  rhsOdd := fourCycle_tseitin_gf2RhsOdd

/-- Three-cycle contradiction scan uses 3 equations and 12 variable occurrences. -/
theorem threeCycle_tseitin_gf2ContradictionSize :
    gf2AllEquationsContradictionSize TseitinParityFormulaThreeCycleCharge = 15 := by
  native_decide

/-- Four-cycle contradiction scan uses 4 equations and 16 variable occurrences. -/
theorem fourCycle_tseitin_gf2ContradictionSize :
    gf2AllEquationsContradictionSize TseitinParityFormulaFourCycleCharge = 20 := by
  native_decide

/-- The three-cycle compact GF(2) formula is unsatisfiable by all-equations cancellation. -/
theorem threeCycle_tseitin_gf2ContradictionUnsat :
    ResoplusPDT.CNFUnsat TseitinParityFormulaThreeCycleCharge :=
  GF2AllEquationsContradictionOutput.unsat
    threeCycle_tseitin_gf2ContradictionOutput

/-- The four-cycle compact GF(2) formula is unsatisfiable by all-equations cancellation. -/
theorem fourCycle_tseitin_gf2ContradictionUnsat :
    ResoplusPDT.CNFUnsat TseitinParityFormulaFourCycleCharge :=
  GF2AllEquationsContradictionOutput.unsat
    fourCycle_tseitin_gf2ContradictionOutput

/--
Semantic transfer: a checked contradiction on the compact GF(2) surface refutes
the expanded CNF of any recognized surface that preserves assignments.
-/
theorem RecognizedGF2NormalizationSurface.unsatExpanded_of_gf2Contradiction
    {m : Nat} {s : RecognizedGF2NormalizationSurface m}
    (hsem : s.correctnessInvariant)
    (out : GF2AllEquationsContradictionOutput s.compactGF2) :
    Not (Exists fun a : CNFModel.Assignment m =>
      CNFModel.cnfSat a s.expandedCNF) := by
  rintro ⟨a, hsat⟩
  exact (GF2AllEquationsContradictionOutput.unsat out) a ((hsem a).1 hsat)

/-- Three-cycle expanded CNF is refuted through the checked compact GF(2) output. -/
theorem threeCycle_tseitin_expandedCNFUnsat_from_gf2Contradiction :
    Not (Exists fun a : CNFModel.Assignment threeCycleGraph.m =>
      CNFModel.cnfSat a threeCycleGF2NormalizationSurface.expandedCNF) :=
  RecognizedGF2NormalizationSurface.unsatExpanded_of_gf2Contradiction
    threeCycle_tseitin_gf2SemanticPreservation
    threeCycle_tseitin_gf2ContradictionOutput

/-- Four-cycle expanded CNF is refuted through the checked compact GF(2) output. -/
theorem fourCycle_tseitin_expandedCNFUnsat_from_gf2Contradiction :
    Not (Exists fun a : CNFModel.Assignment fourCycleGraph.m =>
      CNFModel.cnfSat a fourCycleGF2NormalizationSurface.expandedCNF) :=
  RecognizedGF2NormalizationSurface.unsatExpanded_of_gf2Contradiction
    fourCycle_tseitin_gf2SemanticPreservation
    fourCycle_tseitin_gf2ContradictionOutput

/-!
Stage1768 GF(2) recognition and hybrid-boundary gate.

Stage1765-Stage1767 prove that known Tseitin parity structure can be compressed,
preserved, and refuted by a compact GF(2) contradiction scan.  This gate
separates that useful subroutine from arbitrary-CNF claims: recognition now
starts from CNF blocks certified as permutations of parity-generated blocks,
and a hybrid decomposition records any residual ordinary CNF clauses that are
not solved by the GF(2) core.
-/

/-- CNF satisfaction is invariant under clause-list permutation. -/
theorem cnfSat_iff_of_perm
    {m : Nat} {a : CNFModel.Assignment m} {f g : CNFModel.CNF m}
    (hperm : List.Perm f g) :
    CNFModel.cnfSat a f <-> CNFModel.cnfSat a g := by
  constructor
  · intro hsat c hc
    exact hsat c (hperm.symm.subset hc)
  · intro hsat c hc
    exact hsat c (hperm.subset hc)

/-- Clause satisfaction is invariant under literal-list permutation. -/
theorem clauseSat_iff_of_literal_perm
    {m : Nat} {a : CNFModel.Assignment m}
    {c d : CNFModel.Clause m}
    (hperm : List.Perm c d) :
    CNFModel.clauseSat a c <-> CNFModel.clauseSat a d := by
  constructor
  · rintro ⟨l, hl, hval⟩
    exact ⟨l, hperm.subset hl, hval⟩
  · rintro ⟨l, hl, hval⟩
    exact ⟨l, hperm.symm.subset hl, hval⟩

/-- Reversing the literal order of one clause preserves satisfaction. -/
theorem clauseSat_reverse_iff
    {m : Nat} (a : CNFModel.Assignment m)
    (c : CNFModel.Clause m) :
    CNFModel.clauseSat a c.reverse <-> CNFModel.clauseSat a c := by
  exact clauseSat_iff_of_literal_perm (a := a) c.reverse_perm

/-- CNF satisfaction over appended clause lists splits into the two sides. -/
theorem cnfSat_append_iff
    {m : Nat} (a : CNFModel.Assignment m)
    (f g : CNFModel.CNF m) :
    CNFModel.cnfSat a (f ++ g) <->
      CNFModel.cnfSat a f /\ CNFModel.cnfSat a g := by
  constructor
  · intro hsat
    constructor
    · intro c hc
      exact hsat c (List.mem_append_left g hc)
    · intro c hc
      exact hsat c (List.mem_append_right f hc)
  · intro hsat c hc
    rcases List.mem_append.1 hc with hf | hg
    · exact hsat.1 c hf
    · exact hsat.2 c hg

/--
A recognized parity CNF block is an input-side certificate: the ordinary CNF
block is a permutation of the local parity-block expansion for some variables
and charge.  The certificate does not import a full graph encoding.
-/
structure RecognizedParityCNFBlock (m : Nat) where
  blockCNF : CNFModel.CNF m
  vars : List (Fin m)
  charge : Bool
  block_perm : List.Perm blockCNF (clausesForVertex vars charge)

/-- Compact GF(2) equation associated with a recognized parity CNF block. -/
def RecognizedParityCNFBlock.compactGF2 {m : Nat}
    (b : RecognizedParityCNFBlock m) :
    ResoplusPDT.ParityClause (Basic.CNF.mk m) :=
  parityClauseForVertex b.vars b.charge

/-- Expanded clause count for one recognized parity CNF block. -/
def RecognizedParityCNFBlock.expandedClauseCount {m : Nat}
    (b : RecognizedParityCNFBlock m) : Nat :=
  b.blockCNF.length

/-- Compact equation count for one recognized parity CNF block. -/
def RecognizedParityCNFBlock.equationCount {m : Nat}
    (_b : RecognizedParityCNFBlock m) : Nat :=
  1

/-- Input-scan size proxy for a recognized parity CNF block. -/
def RecognizedParityCNFBlock.recognitionScanSize {m : Nat}
    (b : RecognizedParityCNFBlock m) : Nat :=
  b.blockCNF.length + CNFModel.cnfLiteralCount b.blockCNF + b.vars.length

/-- A recognized input-side parity block preserves semantics as one GF(2) equation. -/
theorem RecognizedParityCNFBlock.semanticPreservation
    {m : Nat} (b : RecognizedParityCNFBlock m)
    (a : CNFModel.Assignment m) :
    CNFModel.cnfSat a b.blockCNF <->
      ResoplusPDT.ClauseSat (F := Basic.CNF.mk m) a b.compactGF2 := by
  exact
    Iff.trans
      (cnfSat_iff_of_perm (a := a) b.block_perm)
      (tseitinVertexBlock_gf2SemanticPreservation
        (m := m) a (vars := b.vars) (charge := b.charge))

/-- Ordinary CNF core represented by a list of recognized parity blocks. -/
def recognizedParityBlockCNF {m : Nat}
    (blocks : List (RecognizedParityCNFBlock m)) : CNFModel.CNF m :=
  blocks.bind (fun b => b.blockCNF)

/-- Compact GF(2) core represented by a list of recognized parity blocks. -/
def recognizedParityBlockGF2 {m : Nat}
    (blocks : List (RecognizedParityCNFBlock m)) :
    ResoplusPDT.CNFFormula (Basic.CNF.mk m) :=
  blocks.map (fun b => b.compactGF2)

/-- Recognition scan-size proxy for a list of recognized parity blocks. -/
def recognizedParityBlocksScanSize {m : Nat}
    (blocks : List (RecognizedParityCNFBlock m)) : Nat :=
  blocks.foldl (fun acc b => acc + b.recognitionScanSize) 0

/-- A list of recognized parity blocks preserves semantics as a compact GF(2) core. -/
theorem recognizedParityBlocks_semanticPreservation
    {m : Nat} (blocks : List (RecognizedParityCNFBlock m))
    (a : CNFModel.Assignment m) :
    CNFModel.cnfSat a (recognizedParityBlockCNF blocks) <->
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk m) a (recognizedParityBlockGF2 blocks) := by
  constructor
  · intro hcnf c hc
    rcases List.mem_map.1 hc with ⟨b, hb, hbc⟩
    have hblock : CNFModel.cnfSat a b.blockCNF := by
      intro d hd
      exact hcnf d (List.mem_bind.2 ⟨b, hb, hd⟩)
    have hsat :
        ResoplusPDT.ClauseSat
          (F := Basic.CNF.mk m) a b.compactGF2 :=
      (RecognizedParityCNFBlock.semanticPreservation b a).1 hblock
    simpa [recognizedParityBlockGF2, hbc] using hsat
  · intro hgf2 c hc
    rcases List.mem_bind.1 hc with ⟨b, hb, hcblock⟩
    have hclause :
        ResoplusPDT.ClauseSat
          (F := Basic.CNF.mk m) a b.compactGF2 := by
      exact
        hgf2 b.compactGF2
          (List.mem_map.2 ⟨b, hb, rfl⟩)
    have hblock : CNFModel.cnfSat a b.blockCNF :=
      (RecognizedParityCNFBlock.semanticPreservation b a).2 hclause
    exact hblock c hcblock

/--
Hybrid decomposition candidate: recognized parity blocks form a GF(2) core,
while any ordinary CNF clauses that were not recognized remain explicit
residual constraints.
-/
structure GF2HybridDecomposition (m : Nat) where
  blocks : List (RecognizedParityCNFBlock m)
  residualCNF : CNFModel.CNF m

/-- Ordinary CNF part covered by the recognized GF(2) core. -/
def GF2HybridDecomposition.coreCNF {m : Nat}
    (d : GF2HybridDecomposition m) : CNFModel.CNF m :=
  recognizedParityBlockCNF d.blocks

/-- Compact GF(2) equations for the recognized core. -/
def GF2HybridDecomposition.coreGF2 {m : Nat}
    (d : GF2HybridDecomposition m) :
    ResoplusPDT.CNFFormula (Basic.CNF.mk m) :=
  recognizedParityBlockGF2 d.blocks

/-- Full expanded ordinary CNF represented by the hybrid decomposition. -/
def GF2HybridDecomposition.expandedCNF {m : Nat}
    (d : GF2HybridDecomposition m) : CNFModel.CNF m :=
  d.coreCNF ++ d.residualCNF

/-- Expanded clause count covered by the recognized GF(2) core. -/
def GF2HybridDecomposition.coreExpandedClauseCount {m : Nat}
    (d : GF2HybridDecomposition m) : Nat :=
  d.coreCNF.length

/-- Compact equation count in the recognized GF(2) core. -/
def GF2HybridDecomposition.coreEquationCount {m : Nat}
    (d : GF2HybridDecomposition m) : Nat :=
  d.coreGF2.length

/-- Number of ordinary CNF clauses left outside the GF(2) core. -/
def GF2HybridDecomposition.residualClauseCount {m : Nat}
    (d : GF2HybridDecomposition m) : Nat :=
  d.residualCNF.length

/-- Full recognition/decomposition size proxy, including residual CNF literals. -/
def GF2HybridDecomposition.recognitionScanSize {m : Nat}
    (d : GF2HybridDecomposition m) : Nat :=
  recognizedParityBlocksScanSize d.blocks +
    d.residualClauseCount + CNFModel.cnfLiteralCount d.residualCNF

/-- Predicate for the case where the GF(2) core covers the whole input. -/
def GF2HybridDecomposition.hasEmptyResidual {m : Nat}
    (d : GF2HybridDecomposition m) : Prop :=
  d.residualCNF = []

/-- The recognized GF(2) core of any hybrid decomposition preserves semantics. -/
theorem GF2HybridDecomposition.coreSemanticPreservation
    {m : Nat} (d : GF2HybridDecomposition m)
    (a : CNFModel.Assignment m) :
    CNFModel.cnfSat a d.coreCNF <->
      ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a d.coreGF2 :=
  recognizedParityBlocks_semanticPreservation d.blocks a

/-- If there is no residual CNF, the whole decomposition preserves GF(2) semantics. -/
theorem GF2HybridDecomposition.emptyResidualSemanticPreservation
    {m : Nat} (d : GF2HybridDecomposition m)
    (hres : d.hasEmptyResidual)
    (a : CNFModel.Assignment m) :
    CNFModel.cnfSat a d.expandedCNF <->
      ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a d.coreGF2 := by
  unfold GF2HybridDecomposition.expandedCNF
  rw [hres, List.append_nil]
  exact GF2HybridDecomposition.coreSemanticPreservation d a

/-- Three-cycle smoke-pair blocks recognized from parity-block CNF certificates. -/
def threeCycle_tseitin_inputRecognizedBlocks :
    List (RecognizedParityCNFBlock threeCycleGraph.m) :=
  [
    { blockCNF :=
        clausesForVertex
          (incidentIndices threeCycleGraph threeCycleHm 0)
          (threeCycleCharge 0)
      vars := incidentIndices threeCycleGraph threeCycleHm 0
      charge := threeCycleCharge 0
      block_perm := List.Perm.refl _ },
    { blockCNF :=
        clausesForVertex
          (incidentIndices threeCycleGraph threeCycleHm 1)
          (threeCycleCharge 1)
      vars := incidentIndices threeCycleGraph threeCycleHm 1
      charge := threeCycleCharge 1
      block_perm := List.Perm.refl _ },
    { blockCNF :=
        clausesForVertex
          (incidentIndices threeCycleGraph threeCycleHm 2)
          (threeCycleCharge 2)
      vars := incidentIndices threeCycleGraph threeCycleHm 2
      charge := threeCycleCharge 2
      block_perm := List.Perm.refl _ }
  ]

/-- Four-cycle smoke-pair blocks recognized from parity-block CNF certificates. -/
def fourCycle_tseitin_inputRecognizedBlocks :
    List (RecognizedParityCNFBlock fourCycleGraph.m) :=
  [
    { blockCNF :=
        clausesForVertex
          (incidentIndices fourCycleGraph fourCycleHm 0)
          (fourCycleCharge 0)
      vars := incidentIndices fourCycleGraph fourCycleHm 0
      charge := fourCycleCharge 0
      block_perm := List.Perm.refl _ },
    { blockCNF :=
        clausesForVertex
          (incidentIndices fourCycleGraph fourCycleHm 1)
          (fourCycleCharge 1)
      vars := incidentIndices fourCycleGraph fourCycleHm 1
      charge := fourCycleCharge 1
      block_perm := List.Perm.refl _ },
    { blockCNF :=
        clausesForVertex
          (incidentIndices fourCycleGraph fourCycleHm 2)
          (fourCycleCharge 2)
      vars := incidentIndices fourCycleGraph fourCycleHm 2
      charge := fourCycleCharge 2
      block_perm := List.Perm.refl _ },
    { blockCNF :=
        clausesForVertex
          (incidentIndices fourCycleGraph fourCycleHm 3)
          (fourCycleCharge 3)
      vars := incidentIndices fourCycleGraph fourCycleHm 3
      charge := fourCycleCharge 3
      block_perm := List.Perm.refl _ }
  ]

/-- Three-cycle input-recognized GF(2) hybrid decomposition has no residual CNF. -/
def threeCycle_tseitin_inputRecognizedDecomposition :
    GF2HybridDecomposition threeCycleGraph.m where
  blocks := threeCycle_tseitin_inputRecognizedBlocks
  residualCNF := []

/-- Four-cycle input-recognized GF(2) hybrid decomposition has no residual CNF. -/
def fourCycle_tseitin_inputRecognizedDecomposition :
    GF2HybridDecomposition fourCycleGraph.m where
  blocks := fourCycle_tseitin_inputRecognizedBlocks
  residualCNF := []

/-- Three-cycle recognized input blocks preserve semantics as a compact GF(2) core. -/
theorem threeCycle_tseitin_inputRecognizedSemanticPreservation
    (a : CNFModel.Assignment threeCycleGraph.m) :
    CNFModel.cnfSat a
        threeCycle_tseitin_inputRecognizedDecomposition.expandedCNF <->
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk threeCycleGraph.m) a
        threeCycle_tseitin_inputRecognizedDecomposition.coreGF2 :=
  GF2HybridDecomposition.emptyResidualSemanticPreservation
    threeCycle_tseitin_inputRecognizedDecomposition rfl a

/-- Four-cycle recognized input blocks preserve semantics as a compact GF(2) core. -/
theorem fourCycle_tseitin_inputRecognizedSemanticPreservation
    (a : CNFModel.Assignment fourCycleGraph.m) :
    CNFModel.cnfSat a
        fourCycle_tseitin_inputRecognizedDecomposition.expandedCNF <->
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk fourCycleGraph.m) a
        fourCycle_tseitin_inputRecognizedDecomposition.coreGF2 :=
  GF2HybridDecomposition.emptyResidualSemanticPreservation
    fourCycle_tseitin_inputRecognizedDecomposition rfl a

/-- Three-cycle resource accounting for the input-recognized GF(2) decomposition. -/
theorem threeCycle_tseitin_inputRecognizedResourceCounts :
    And
      (threeCycle_tseitin_inputRecognizedDecomposition.coreExpandedClauseCount = 24)
      (And
        (threeCycle_tseitin_inputRecognizedDecomposition.coreEquationCount = 3)
        (And
          (threeCycle_tseitin_inputRecognizedDecomposition.residualClauseCount = 0)
          (threeCycle_tseitin_inputRecognizedDecomposition.recognitionScanSize = 132))) := by
  native_decide

/-- Four-cycle resource accounting for the input-recognized GF(2) decomposition. -/
theorem fourCycle_tseitin_inputRecognizedResourceCounts :
    And
      (fourCycle_tseitin_inputRecognizedDecomposition.coreExpandedClauseCount = 32)
      (And
        (fourCycle_tseitin_inputRecognizedDecomposition.coreEquationCount = 4)
        (And
          (fourCycle_tseitin_inputRecognizedDecomposition.residualClauseCount = 0)
          (fourCycle_tseitin_inputRecognizedDecomposition.recognitionScanSize = 176))) := by
  native_decide

/-- Negative residual-control case: no parity block recognizes this empty-clause residual. -/
def gf2ResidualControlDecomposition (m : Nat) :
    GF2HybridDecomposition m where
  blocks := []
  residualCNF := [[]]

/-- The residual-control case has no GF(2) core equations. -/
theorem gf2ResidualControl_coreEquationCount (m : Nat) :
    (gf2ResidualControlDecomposition m).coreEquationCount = 0 := by
  rfl

/-- The residual-control case leaves one ordinary CNF clause outside the GF(2) core. -/
theorem gf2ResidualControl_residualClauseCount (m : Nat) :
    (gf2ResidualControlDecomposition m).residualClauseCount = 1 := by
  rfl

/-- The residual-control case is not covered by the empty-residual theorem. -/
theorem gf2ResidualControl_not_emptyResidual (m : Nat) :
    Not ((gf2ResidualControlDecomposition m).hasEmptyResidual) := by
  intro hres
  cases hres

/--
Residual CNF cannot be ignored: the empty GF(2) core is vacuously satisfied,
but the residual empty clause makes the expanded CNF unsatisfied.
-/
theorem gf2ResidualControl_coreDoesNotDecideExpanded (m : Nat) :
    Not (forall a : CNFModel.Assignment m,
      CNFModel.cnfSat a (gf2ResidualControlDecomposition m).expandedCNF <->
        ResoplusPDT.CNFSat
          (F := Basic.CNF.mk m) a
          (gf2ResidualControlDecomposition m).coreGF2) := by
  intro hsem
  let a : CNFModel.Assignment m := fun _ => false
  have hgf2 :
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk m) a
        (gf2ResidualControlDecomposition m).coreGF2 := by
    intro c hc
    cases hc
  have hcnf :
      CNFModel.cnfSat a (gf2ResidualControlDecomposition m).expandedCNF :=
    (hsem a).2 hgf2
  have hempty :
      ([] : CNFModel.Clause m) ∈
        (gf2ResidualControlDecomposition m).expandedCNF := by
    simp [GF2HybridDecomposition.expandedCNF,
      GF2HybridDecomposition.coreCNF, recognizedParityBlockCNF,
      gf2ResidualControlDecomposition]
  rcases hcnf [] hempty with ⟨l, hl, _hval⟩
  cases hl

/-!
Stage1769 computable parity-block syntactic recognizer gate.

Stage1768 accepted parity-block certificates.  This gate adds the first computable
recognition signal: given a candidate CNF block and a candidate parity support,
check whether the block is a clause-list permutation of the parity-generated
CNF expansion.  Successful recognition produces the Stage1768 certificate, while
unrecognized or out-of-scope clauses remain explicit residual CNF.
-/

/-- Syntactic target for a candidate parity-block recognizer. -/
structure ParityBlockSyntacticSpec (m : Nat) where
  vars : List (Fin m)
  charge : Bool

/-- Expanded CNF expected from a candidate parity-block spec. -/
def ParityBlockSyntacticSpec.expandedCNF {m : Nat}
    (spec : ParityBlockSyntacticSpec m) : CNFModel.CNF m :=
  clausesForVertex spec.vars spec.charge

/--
Computable block-level recognizer: does this ordinary CNF block match the
expanded parity-block syntax, up to harmless clause ordering?
-/
def parityBlockRecognitionSignal {m : Nat}
    (blockCNF : CNFModel.CNF m)
    (spec : ParityBlockSyntacticSpec m) : Bool :=
  decide (List.Perm blockCNF spec.expandedCNF)

/-- Soundness of the computable parity-block recognition signal. -/
theorem parityBlockRecognitionSignal_sound
    {m : Nat} {blockCNF : CNFModel.CNF m}
    {spec : ParityBlockSyntacticSpec m}
    (h : parityBlockRecognitionSignal blockCNF spec = true) :
    List.Perm blockCNF spec.expandedCNF := by
  unfold parityBlockRecognitionSignal at h
  exact of_decide_eq_true h

/-- A syntactically recognized block packages the computable signal and its proof. -/
structure SyntacticRecognizedParityBlock (m : Nat) where
  blockCNF : CNFModel.CNF m
  spec : ParityBlockSyntacticSpec m
  recognitionSignal : parityBlockRecognitionSignal blockCNF spec = true

/-- A syntactically recognized block induces the Stage1768 certificate object. -/
def SyntacticRecognizedParityBlock.toRecognized {m : Nat}
    (b : SyntacticRecognizedParityBlock m) :
    RecognizedParityCNFBlock m :=
  { blockCNF := b.blockCNF
    vars := b.spec.vars
    charge := b.spec.charge
    block_perm := by
      simpa [ParityBlockSyntacticSpec.expandedCNF] using
        parityBlockRecognitionSignal_sound b.recognitionSignal }

/-- Recognition scan-size proxy for a syntactically recognized parity block. -/
def SyntacticRecognizedParityBlock.recognitionScanSize {m : Nat}
    (b : SyntacticRecognizedParityBlock m) : Nat :=
  b.blockCNF.length + CNFModel.cnfLiteralCount b.blockCNF + b.spec.vars.length

/-- Syntactically recognized parity blocks preserve semantics as GF(2) equations. -/
theorem SyntacticRecognizedParityBlock.semanticPreservation
    {m : Nat} (b : SyntacticRecognizedParityBlock m)
    (a : CNFModel.Assignment m) :
    CNFModel.cnfSat a b.blockCNF <->
      ResoplusPDT.ClauseSat
        (F := Basic.CNF.mk m) a b.toRecognized.compactGF2 :=
  RecognizedParityCNFBlock.semanticPreservation b.toRecognized a

/--
Syntactic GF(2) hybrid decomposition: recognized blocks are backed by a
computable recognition signal, while all other clauses stay residual.
-/
structure SyntacticGF2HybridDecomposition (m : Nat) where
  blocks : List (SyntacticRecognizedParityBlock m)
  residualCNF : CNFModel.CNF m

/-- Convert a syntactic decomposition into the Stage1768 semantic decomposition. -/
def SyntacticGF2HybridDecomposition.toGF2HybridDecomposition {m : Nat}
    (d : SyntacticGF2HybridDecomposition m) :
    GF2HybridDecomposition m where
  blocks := d.blocks.map (fun b => b.toRecognized)
  residualCNF := d.residualCNF

/-- Full ordinary CNF represented by a syntactic hybrid decomposition. -/
def SyntacticGF2HybridDecomposition.expandedCNF {m : Nat}
    (d : SyntacticGF2HybridDecomposition m) : CNFModel.CNF m :=
  d.toGF2HybridDecomposition.expandedCNF

/-- Compact GF(2) core represented by a syntactic hybrid decomposition. -/
def SyntacticGF2HybridDecomposition.coreGF2 {m : Nat}
    (d : SyntacticGF2HybridDecomposition m) :
    ResoplusPDT.CNFFormula (Basic.CNF.mk m) :=
  d.toGF2HybridDecomposition.coreGF2

/-- Core expanded clause count for syntactically recognized parity blocks. -/
def SyntacticGF2HybridDecomposition.coreExpandedClauseCount {m : Nat}
    (d : SyntacticGF2HybridDecomposition m) : Nat :=
  d.toGF2HybridDecomposition.coreExpandedClauseCount

/-- Core GF(2) equation count for syntactically recognized parity blocks. -/
def SyntacticGF2HybridDecomposition.coreEquationCount {m : Nat}
    (d : SyntacticGF2HybridDecomposition m) : Nat :=
  d.toGF2HybridDecomposition.coreEquationCount

/-- Residual ordinary CNF clause count for a syntactic hybrid decomposition. -/
def SyntacticGF2HybridDecomposition.residualClauseCount {m : Nat}
    (d : SyntacticGF2HybridDecomposition m) : Nat :=
  d.residualCNF.length

/-- Recognition scan-size proxy for a syntactic hybrid decomposition. -/
def SyntacticGF2HybridDecomposition.recognitionScanSize {m : Nat}
    (d : SyntacticGF2HybridDecomposition m) : Nat :=
  d.blocks.foldl (fun acc b => acc + b.recognitionScanSize) 0 +
    d.residualClauseCount + CNFModel.cnfLiteralCount d.residualCNF

/-- Predicate for the case where syntactic recognition covers the whole input. -/
def SyntacticGF2HybridDecomposition.hasEmptyResidual {m : Nat}
    (d : SyntacticGF2HybridDecomposition m) : Prop :=
  d.residualCNF = []

/-- The recognized core of a syntactic hybrid decomposition preserves semantics. -/
theorem SyntacticGF2HybridDecomposition.coreSemanticPreservation
    {m : Nat} (d : SyntacticGF2HybridDecomposition m)
    (a : CNFModel.Assignment m) :
    CNFModel.cnfSat a d.toGF2HybridDecomposition.coreCNF <->
      ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a d.coreGF2 :=
  GF2HybridDecomposition.coreSemanticPreservation
    d.toGF2HybridDecomposition a

/-- If syntactic recognition leaves no residual CNF, it preserves full semantics. -/
theorem SyntacticGF2HybridDecomposition.emptyResidualSemanticPreservation
    {m : Nat} (d : SyntacticGF2HybridDecomposition m)
    (hres : d.hasEmptyResidual)
    (a : CNFModel.Assignment m) :
    CNFModel.cnfSat a d.expandedCNF <->
      ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a d.coreGF2 :=
  GF2HybridDecomposition.emptyResidualSemanticPreservation
    d.toGF2HybridDecomposition hres a

/-- Three-cycle syntactic recognizer smoke test: reordered clauses and block order. -/
def threeCycle_tseitin_syntacticRecognizedBlocks :
    List (SyntacticRecognizedParityBlock threeCycleGraph.m) :=
  [
    { blockCNF :=
        (clausesForVertex
          (incidentIndices threeCycleGraph threeCycleHm 2)
          (threeCycleCharge 2)).reverse
      spec :=
        { vars := incidentIndices threeCycleGraph threeCycleHm 2
          charge := threeCycleCharge 2 }
      recognitionSignal := by native_decide },
    { blockCNF :=
        (clausesForVertex
          (incidentIndices threeCycleGraph threeCycleHm 1)
          (threeCycleCharge 1)).reverse
      spec :=
        { vars := incidentIndices threeCycleGraph threeCycleHm 1
          charge := threeCycleCharge 1 }
      recognitionSignal := by native_decide },
    { blockCNF :=
        (clausesForVertex
          (incidentIndices threeCycleGraph threeCycleHm 0)
          (threeCycleCharge 0)).reverse
      spec :=
        { vars := incidentIndices threeCycleGraph threeCycleHm 0
          charge := threeCycleCharge 0 }
      recognitionSignal := by native_decide }
  ]

/-- Four-cycle syntactic recognizer smoke test: reordered clauses and block order. -/
def fourCycle_tseitin_syntacticRecognizedBlocks :
    List (SyntacticRecognizedParityBlock fourCycleGraph.m) :=
  [
    { blockCNF :=
        (clausesForVertex
          (incidentIndices fourCycleGraph fourCycleHm 3)
          (fourCycleCharge 3)).reverse
      spec :=
        { vars := incidentIndices fourCycleGraph fourCycleHm 3
          charge := fourCycleCharge 3 }
      recognitionSignal := by native_decide },
    { blockCNF :=
        (clausesForVertex
          (incidentIndices fourCycleGraph fourCycleHm 2)
          (fourCycleCharge 2)).reverse
      spec :=
        { vars := incidentIndices fourCycleGraph fourCycleHm 2
          charge := fourCycleCharge 2 }
      recognitionSignal := by native_decide },
    { blockCNF :=
        (clausesForVertex
          (incidentIndices fourCycleGraph fourCycleHm 1)
          (fourCycleCharge 1)).reverse
      spec :=
        { vars := incidentIndices fourCycleGraph fourCycleHm 1
          charge := fourCycleCharge 1 }
      recognitionSignal := by native_decide },
    { blockCNF :=
        (clausesForVertex
          (incidentIndices fourCycleGraph fourCycleHm 0)
          (fourCycleCharge 0)).reverse
      spec :=
        { vars := incidentIndices fourCycleGraph fourCycleHm 0
          charge := fourCycleCharge 0 }
      recognitionSignal := by native_decide }
  ]

/-- Three-cycle syntactic GF(2) decomposition leaves no residual CNF. -/
def threeCycle_tseitin_syntacticRecognizerDecomposition :
    SyntacticGF2HybridDecomposition threeCycleGraph.m where
  blocks := threeCycle_tseitin_syntacticRecognizedBlocks
  residualCNF := []

/-- Four-cycle syntactic GF(2) decomposition leaves no residual CNF. -/
def fourCycle_tseitin_syntacticRecognizerDecomposition :
    SyntacticGF2HybridDecomposition fourCycleGraph.m where
  blocks := fourCycle_tseitin_syntacticRecognizedBlocks
  residualCNF := []

/-- Three-cycle syntactic recognition preserves full semantics with no residual CNF. -/
theorem threeCycle_tseitin_syntacticRecognizerSemanticPreservation
    (a : CNFModel.Assignment threeCycleGraph.m) :
    CNFModel.cnfSat a
        threeCycle_tseitin_syntacticRecognizerDecomposition.expandedCNF <->
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk threeCycleGraph.m) a
        threeCycle_tseitin_syntacticRecognizerDecomposition.coreGF2 :=
  SyntacticGF2HybridDecomposition.emptyResidualSemanticPreservation
    threeCycle_tseitin_syntacticRecognizerDecomposition rfl a

/-- Four-cycle syntactic recognition preserves full semantics with no residual CNF. -/
theorem fourCycle_tseitin_syntacticRecognizerSemanticPreservation
    (a : CNFModel.Assignment fourCycleGraph.m) :
    CNFModel.cnfSat a
        fourCycle_tseitin_syntacticRecognizerDecomposition.expandedCNF <->
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk fourCycleGraph.m) a
        fourCycle_tseitin_syntacticRecognizerDecomposition.coreGF2 :=
  SyntacticGF2HybridDecomposition.emptyResidualSemanticPreservation
    fourCycle_tseitin_syntacticRecognizerDecomposition rfl a

/-- Three-cycle syntactic recognizer resource accounting. -/
theorem threeCycle_tseitin_syntacticRecognizerResourceCounts :
    (threeCycle_tseitin_syntacticRecognizerDecomposition.coreExpandedClauseCount = 24) /\
      (threeCycle_tseitin_syntacticRecognizerDecomposition.coreEquationCount = 3) /\
      (threeCycle_tseitin_syntacticRecognizerDecomposition.residualClauseCount = 0) /\
      (threeCycle_tseitin_syntacticRecognizerDecomposition.recognitionScanSize = 132) := by
  native_decide

/-- Four-cycle syntactic recognizer resource accounting. -/
theorem fourCycle_tseitin_syntacticRecognizerResourceCounts :
    (fourCycle_tseitin_syntacticRecognizerDecomposition.coreExpandedClauseCount = 32) /\
      (fourCycle_tseitin_syntacticRecognizerDecomposition.coreEquationCount = 4) /\
      (fourCycle_tseitin_syntacticRecognizerDecomposition.residualClauseCount = 0) /\
      (fourCycle_tseitin_syntacticRecognizerDecomposition.recognitionScanSize = 176) := by
  native_decide

/-- Syntactic residual-control case: no recognized blocks and one residual empty clause. -/
def syntacticGF2ResidualControlDecomposition (m : Nat) :
    SyntacticGF2HybridDecomposition m where
  blocks := []
  residualCNF := [[]]

/-- The syntactic residual-control case leaves one residual clause and no GF(2) core. -/
theorem syntacticGF2ResidualControlCounts (m : Nat) :
    (syntacticGF2ResidualControlDecomposition m).coreEquationCount = 0 /\
      (syntacticGF2ResidualControlDecomposition m).residualClauseCount = 1 := by
  constructor
  next => rfl
  next => rfl

/-- The syntactic residual-control case is not an empty-residual decomposition. -/
theorem syntacticGF2ResidualControl_not_emptyResidual (m : Nat) :
    Not ((syntacticGF2ResidualControlDecomposition m).hasEmptyResidual) := by
  intro hres
  cases hres

/-- Residual CNF still cannot be ignored by the syntactic recognizer. -/
theorem syntacticGF2ResidualControl_coreDoesNotDecideExpanded (m : Nat) :
    Not (forall a : CNFModel.Assignment m,
      CNFModel.cnfSat a (syntacticGF2ResidualControlDecomposition m).expandedCNF <->
        ResoplusPDT.CNFSat
          (F := Basic.CNF.mk m) a
          (syntacticGF2ResidualControlDecomposition m).coreGF2) := by
  intro hsem
  let a : CNFModel.Assignment m := fun _ => false
  have hgf2 :
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk m) a
        (syntacticGF2ResidualControlDecomposition m).coreGF2 := by
    intro c hc
    cases hc
  have hcnf :
      CNFModel.cnfSat a
        (syntacticGF2ResidualControlDecomposition m).expandedCNF :=
    (hsem a).2 hgf2
  have hempty :
      ([] : CNFModel.Clause m) ∈
        (syntacticGF2ResidualControlDecomposition m).expandedCNF := by
    simp [SyntacticGF2HybridDecomposition.expandedCNF,
      SyntacticGF2HybridDecomposition.toGF2HybridDecomposition,
      GF2HybridDecomposition.expandedCNF, GF2HybridDecomposition.coreCNF,
      recognizedParityBlockCNF, syntacticGF2ResidualControlDecomposition]
  rcases hcnf [] hempty with ⟨l, hl, _hval⟩
  cases hl

/-!
Stage1770 support-inference and residual-splitter gate.

Stage1769 recognizes a supplied block/support/charge.  This gate adds a first
formula-level splitter: scan the input in fixed eight-clause windows, infer a
candidate support from the first clause of each window, try both parity charges,
and keep every failed window or leftover clause as explicit residual CNF.
-/

/-- Computable variable-support extraction from one ordinary CNF clause. -/
def clauseVariableSupport {m : Nat}
    (c : CNFModel.Clause m) : List (Fin m) :=
  (c.map (fun l => l.var)).eraseDups

/-- Candidate support inferred from the first clause of a candidate CNF block. -/
def parityCandidateSupportFromBlock {m : Nat}
    (blockCNF : CNFModel.CNF m) : List (Fin m) :=
  match blockCNF with
  | [] => []
  | c :: _ => clauseVariableSupport c

/-- Candidate parity-block spec inferred from a CNF block and a proposed charge. -/
def inferredParityBlockSpec {m : Nat}
    (blockCNF : CNFModel.CNF m) (charge : Bool) :
    ParityBlockSyntacticSpec m :=
  { vars := parityCandidateSupportFromBlock blockCNF
    charge := charge }

/-- Try one charge for a support-inferred candidate parity block. -/
def inferParityBlockFromWindowWithCharge {m : Nat}
    (blockCNF : CNFModel.CNF m) (charge : Bool) :
    Option (SyntacticRecognizedParityBlock m) :=
  let spec := inferredParityBlockSpec blockCNF charge
  if h : parityBlockRecognitionSignal blockCNF spec = true then
    some
      { blockCNF := blockCNF
        spec := spec
        recognitionSignal := h }
  else
    none

/--
Try both parity charges for one fixed-window candidate block.  This is a
syntactic GF(2) recognition attempt, not assignment-space branching.
-/
def inferParityBlockFromWindow {m : Nat}
    (blockCNF : CNFModel.CNF m) :
    Option (SyntacticRecognizedParityBlock m) :=
  match inferParityBlockFromWindowWithCharge blockCNF false with
  | some b => some b
  | none => inferParityBlockFromWindowWithCharge blockCNF true

/-- Concatenate the ordinary CNF blocks represented by syntactic recognitions. -/
def syntacticRecognizedBlocksCNF {m : Nat}
    (blocks : List (SyntacticRecognizedParityBlock m)) : CNFModel.CNF m :=
  blocks.bind (fun b => b.blockCNF)

/--
First fixed-arity parity splitter.  It scans eight-clause windows, recognizes
arity-four parity blocks when possible, and preserves failures as residual CNF.
-/
def splitArityFourParityWindows {m : Nat} :
    CNFModel.CNF m -> SyntacticGF2HybridDecomposition m
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest =>
      let block : CNFModel.CNF m := [c0, c1, c2, c3, c4, c5, c6, c7]
      let tail := splitArityFourParityWindows rest
      match inferParityBlockFromWindow block with
      | some b =>
          { blocks := b :: tail.blocks
            residualCNF := tail.residualCNF }
      | none =>
          { blocks := tail.blocks
            residualCNF := block ++ tail.residualCNF }
  | residual =>
      { blocks := []
        residualCNF := residual }

/-- Full-CNF input used for the three-cycle support-inference smoke test. -/
def threeCycle_tseitin_supportInferenceInputCNF :
    CNFModel.CNF threeCycleGraph.m :=
  syntacticRecognizedBlocksCNF threeCycle_tseitin_syntacticRecognizedBlocks

/-- Full-CNF input used for the four-cycle support-inference smoke test. -/
def fourCycle_tseitin_supportInferenceInputCNF :
    CNFModel.CNF fourCycleGraph.m :=
  syntacticRecognizedBlocksCNF fourCycle_tseitin_syntacticRecognizedBlocks

/-- Three-cycle support-inferred decomposition from a full CNF input. -/
def threeCycle_tseitin_supportInferredDecomposition :
    SyntacticGF2HybridDecomposition threeCycleGraph.m :=
  splitArityFourParityWindows threeCycle_tseitin_supportInferenceInputCNF

/-- Four-cycle support-inferred decomposition from a full CNF input. -/
def fourCycle_tseitin_supportInferredDecomposition :
    SyntacticGF2HybridDecomposition fourCycleGraph.m :=
  splitArityFourParityWindows fourCycle_tseitin_supportInferenceInputCNF

/-- Three-cycle support inference preserves semantics when no residual CNF remains. -/
theorem threeCycle_tseitin_supportInferredSemanticPreservation
    (a : CNFModel.Assignment threeCycleGraph.m) :
    CNFModel.cnfSat a
        threeCycle_tseitin_supportInferredDecomposition.expandedCNF <->
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk threeCycleGraph.m) a
        threeCycle_tseitin_supportInferredDecomposition.coreGF2 := by
  have hres :
      threeCycle_tseitin_supportInferredDecomposition.residualCNF = [] := by
    native_decide
  exact
    SyntacticGF2HybridDecomposition.emptyResidualSemanticPreservation
      threeCycle_tseitin_supportInferredDecomposition hres a

/-- Four-cycle support inference preserves semantics when no residual CNF remains. -/
theorem fourCycle_tseitin_supportInferredSemanticPreservation
    (a : CNFModel.Assignment fourCycleGraph.m) :
    CNFModel.cnfSat a
        fourCycle_tseitin_supportInferredDecomposition.expandedCNF <->
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk fourCycleGraph.m) a
        fourCycle_tseitin_supportInferredDecomposition.coreGF2 := by
  have hres :
      fourCycle_tseitin_supportInferredDecomposition.residualCNF = [] := by
    native_decide
  exact
    SyntacticGF2HybridDecomposition.emptyResidualSemanticPreservation
      fourCycle_tseitin_supportInferredDecomposition hres a

/-- Three-cycle support-inference resource accounting. -/
theorem threeCycle_tseitin_supportInferredResourceCounts :
    (threeCycle_tseitin_supportInferredDecomposition.coreExpandedClauseCount = 24) /\
      (threeCycle_tseitin_supportInferredDecomposition.coreEquationCount = 3) /\
      (threeCycle_tseitin_supportInferredDecomposition.residualClauseCount = 0) /\
      (threeCycle_tseitin_supportInferredDecomposition.recognitionScanSize = 132) := by
  native_decide

/-- Four-cycle support-inference resource accounting. -/
theorem fourCycle_tseitin_supportInferredResourceCounts :
    (fourCycle_tseitin_supportInferredDecomposition.coreExpandedClauseCount = 32) /\
      (fourCycle_tseitin_supportInferredDecomposition.coreEquationCount = 4) /\
      (fourCycle_tseitin_supportInferredDecomposition.residualClauseCount = 0) /\
      (fourCycle_tseitin_supportInferredDecomposition.recognitionScanSize = 176) := by
  native_decide

/-- Noisy full-CNF input: recognized three-cycle parity blocks plus one residual clause. -/
def threeCycle_tseitin_supportInferenceNoisyInputCNF :
    CNFModel.CNF threeCycleGraph.m :=
  threeCycle_tseitin_supportInferenceInputCNF ++ [[]]

/-- The fixed-window splitter leaves the noisy leftover clause as explicit residual CNF. -/
def threeCycle_tseitin_supportInferredNoisyDecomposition :
    SyntacticGF2HybridDecomposition threeCycleGraph.m :=
  splitArityFourParityWindows threeCycle_tseitin_supportInferenceNoisyInputCNF

/-- Noisy-input resource accounting: the extra clause remains residual. -/
theorem threeCycle_tseitin_supportInferredNoisyResourceCounts :
    (threeCycle_tseitin_supportInferredNoisyDecomposition.coreEquationCount = 3) /\
      (threeCycle_tseitin_supportInferredNoisyDecomposition.residualClauseCount = 1) := by
  native_decide

/-- The noisy support-inference smoke input is not covered by the empty-residual theorem. -/
theorem threeCycle_tseitin_supportInferredNoisy_not_emptyResidual :
    Not (threeCycle_tseitin_supportInferredNoisyDecomposition.hasEmptyResidual) := by
  change Not (threeCycle_tseitin_supportInferredNoisyDecomposition.residualCNF = [])
  native_decide

/--
Failed fixed windows are residualized: eight empty clauses do not infer an
arity-four parity block and are returned as ordinary residual CNF.
-/
def arityFourFailedWindowResidualControl (m : Nat) :
    SyntacticGF2HybridDecomposition m :=
  splitArityFourParityWindows
    ([[], [], [], [], [], [], [], []] : CNFModel.CNF m)

/-- Failed-window residual-control accounting on the three-cycle variable domain. -/
theorem arityFourFailedWindowResidualControlCounts_threeCycle :
    (arityFourFailedWindowResidualControl threeCycleGraph.m).coreEquationCount = 0 /\
      (arityFourFailedWindowResidualControl threeCycleGraph.m).residualClauseCount = 8 := by
  native_decide

/-!
Stage1771 support-grouping recognizer gate.

Stage1770 still assumed fixed eight-clause windows.  This gate groups clauses by
their inferred support key across the whole input, attempts arity-four parity
recognition on each complete support group, and returns every failed group as
explicit residual CNF.
-/

/-- Support-key alias for grouping ordinary CNF clauses. -/
abbrev ClauseSupportKey (m : Nat) := List (Fin m)

/-- A group of ordinary CNF clauses sharing the same inferred support key. -/
abbrev SupportClauseGroup (m : Nat) :=
  ClauseSupportKey m × CNFModel.CNF m

/-- Computable support key for one ordinary CNF clause. -/
def clauseSupportKey {m : Nat}
    (c : CNFModel.Clause m) : ClauseSupportKey m :=
  clauseVariableSupport c

/-- Insert one clause into the first support group with the same key. -/
def insertClauseBySupport {m : Nat}
    (c : CNFModel.Clause m) :
    List (SupportClauseGroup m) -> List (SupportClauseGroup m)
  | [] => [(clauseSupportKey c, [c])]
  | g :: rest =>
      if clauseSupportKey c = g.1 then
        (g.1, g.2 ++ [c]) :: rest
      else
        g :: insertClauseBySupport c rest

/-- Group all clauses in a CNF by their computable support key. -/
def groupClausesBySupport {m : Nat}
    (f : CNFModel.CNF m) : List (SupportClauseGroup m) :=
  f.foldl (fun groups c => insertClauseBySupport c groups) []

/-- Split support groups into syntactically recognized GF(2) blocks and residual CNF. -/
def splitSupportClauseGroups {m : Nat} :
    List (SupportClauseGroup m) -> SyntacticGF2HybridDecomposition m
  | [] =>
      { blocks := []
        residualCNF := [] }
  | g :: rest =>
      let tail := splitSupportClauseGroups rest
      match inferParityBlockFromWindow g.2 with
      | some b =>
          { blocks := b :: tail.blocks
            residualCNF := tail.residualCNF }
      | none =>
          { blocks := tail.blocks
            residualCNF := g.2 ++ tail.residualCNF }

/-- Full-CNF splitter that recognizes arity-four parity groups by inferred support. -/
def splitArityFourParitySupportGroups {m : Nat}
    (f : CNFModel.CNF m) : SyntacticGF2HybridDecomposition m :=
  splitSupportClauseGroups (groupClausesBySupport f)

/-- Interleave three lists, preserving each list's internal order. -/
def interleave3 {α : Type} : List α -> List α -> List α -> List α
  | a :: as, b :: bs, c :: cs => a :: b :: c :: interleave3 as bs cs
  | as, bs, cs => as ++ bs ++ cs

/-- Interleave four lists, preserving each list's internal order. -/
def interleave4 {α : Type} : List α -> List α -> List α -> List α -> List α
  | a :: as, b :: bs, c :: cs, d :: ds =>
      a :: b :: c :: d :: interleave4 as bs cs ds
  | as, bs, cs, ds => as ++ bs ++ cs ++ ds

/-- Three-cycle smoke input with parity blocks interleaved by clause position. -/
def threeCycle_tseitin_supportGroupingInterleavedInputCNF :
    CNFModel.CNF threeCycleGraph.m :=
  match threeCycle_tseitin_syntacticRecognizedBlocks with
  | b0 :: b1 :: b2 :: _ => interleave3 b0.blockCNF b1.blockCNF b2.blockCNF
  | _ => []

/-- Four-cycle smoke input with parity blocks interleaved by clause position. -/
def fourCycle_tseitin_supportGroupingInterleavedInputCNF :
    CNFModel.CNF fourCycleGraph.m :=
  match fourCycle_tseitin_syntacticRecognizedBlocks with
  | b0 :: b1 :: b2 :: b3 :: _ =>
      interleave4 b0.blockCNF b1.blockCNF b2.blockCNF b3.blockCNF
  | _ => []

/-- Three-cycle decomposition recovered by support grouping, not fixed windows. -/
def threeCycle_tseitin_supportGroupedDecomposition :
    SyntacticGF2HybridDecomposition threeCycleGraph.m :=
  splitArityFourParitySupportGroups
    threeCycle_tseitin_supportGroupingInterleavedInputCNF

/-- Four-cycle decomposition recovered by support grouping, not fixed windows. -/
def fourCycle_tseitin_supportGroupedDecomposition :
    SyntacticGF2HybridDecomposition fourCycleGraph.m :=
  splitArityFourParitySupportGroups
    fourCycle_tseitin_supportGroupingInterleavedInputCNF

/-- Three-cycle support grouping preserves semantics when all groups are recognized. -/
theorem threeCycle_tseitin_supportGroupedSemanticPreservation
    (a : CNFModel.Assignment threeCycleGraph.m) :
    CNFModel.cnfSat a
        threeCycle_tseitin_supportGroupedDecomposition.expandedCNF <->
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk threeCycleGraph.m) a
        threeCycle_tseitin_supportGroupedDecomposition.coreGF2 := by
  have hres :
      threeCycle_tseitin_supportGroupedDecomposition.residualCNF = [] := by
    native_decide
  exact
    SyntacticGF2HybridDecomposition.emptyResidualSemanticPreservation
      threeCycle_tseitin_supportGroupedDecomposition hres a

/-- Four-cycle support grouping preserves semantics when all groups are recognized. -/
theorem fourCycle_tseitin_supportGroupedSemanticPreservation
    (a : CNFModel.Assignment fourCycleGraph.m) :
    CNFModel.cnfSat a
        fourCycle_tseitin_supportGroupedDecomposition.expandedCNF <->
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk fourCycleGraph.m) a
        fourCycle_tseitin_supportGroupedDecomposition.coreGF2 := by
  have hres :
      fourCycle_tseitin_supportGroupedDecomposition.residualCNF = [] := by
    native_decide
  exact
    SyntacticGF2HybridDecomposition.emptyResidualSemanticPreservation
      fourCycle_tseitin_supportGroupedDecomposition hres a

/-- Three-cycle support grouping preserves the input clauses up to permutation. -/
theorem threeCycle_tseitin_supportGroupedInputPermutation :
    List.Perm
      threeCycle_tseitin_supportGroupedDecomposition.expandedCNF
      threeCycle_tseitin_supportGroupingInterleavedInputCNF := by
  native_decide

/-- Four-cycle support grouping preserves the input clauses up to permutation. -/
theorem fourCycle_tseitin_supportGroupedInputPermutation :
    List.Perm
      fourCycle_tseitin_supportGroupedDecomposition.expandedCNF
      fourCycle_tseitin_supportGroupingInterleavedInputCNF := by
  native_decide

/-- Three-cycle support-grouping resource accounting. -/
theorem threeCycle_tseitin_supportGroupedResourceCounts :
    (threeCycle_tseitin_supportGroupedDecomposition.coreExpandedClauseCount = 24) /\
      (threeCycle_tseitin_supportGroupedDecomposition.coreEquationCount = 3) /\
      (threeCycle_tseitin_supportGroupedDecomposition.residualClauseCount = 0) /\
      (threeCycle_tseitin_supportGroupedDecomposition.recognitionScanSize = 132) := by
  native_decide

/-- Four-cycle support-grouping resource accounting. -/
theorem fourCycle_tseitin_supportGroupedResourceCounts :
    (fourCycle_tseitin_supportGroupedDecomposition.coreExpandedClauseCount = 32) /\
      (fourCycle_tseitin_supportGroupedDecomposition.coreEquationCount = 4) /\
      (fourCycle_tseitin_supportGroupedDecomposition.residualClauseCount = 0) /\
      (fourCycle_tseitin_supportGroupedDecomposition.recognitionScanSize = 176) := by
  native_decide

/-- One-clause incomplete two-variable support group for the support-grouping noisy smoke input. -/
def threeCycle_tseitin_supportGroupingPartialNoiseClause :
    CNFModel.Clause threeCycleGraph.m :=
  [
    { var := Fin.mk 0 (by decide), sign := true },
    { var := Fin.mk 1 (by decide), sign := true }
  ]

/-- Interleaved three-cycle input plus one incomplete residual support group. -/
def threeCycle_tseitin_supportGroupingPartialNoiseInputCNF :
    CNFModel.CNF threeCycleGraph.m :=
  threeCycle_tseitin_supportGroupingInterleavedInputCNF ++
    [threeCycle_tseitin_supportGroupingPartialNoiseClause]

/-- Support-grouped noisy three-cycle decomposition. -/
def threeCycle_tseitin_supportGroupedPartialNoiseDecomposition :
    SyntacticGF2HybridDecomposition threeCycleGraph.m :=
  splitArityFourParitySupportGroups
    threeCycle_tseitin_supportGroupingPartialNoiseInputCNF

/-- The noisy partial group is residualized while the complete parity groups remain core. -/
theorem threeCycle_tseitin_supportGroupedPartialNoiseResourceCounts :
    (threeCycle_tseitin_supportGroupedPartialNoiseDecomposition.coreEquationCount = 3) /\
      (threeCycle_tseitin_supportGroupedPartialNoiseDecomposition.residualClauseCount = 1) := by
  native_decide

/-- The noisy support-grouping input is not an empty-residual decomposition. -/
theorem threeCycle_tseitin_supportGroupedPartialNoise_not_emptyResidual :
    Not (threeCycle_tseitin_supportGroupedPartialNoiseDecomposition.hasEmptyResidual) := by
  change Not (threeCycle_tseitin_supportGroupedPartialNoiseDecomposition.residualCNF = [])
  native_decide

/-- Support grouping preserves noisy input clauses up to permutation. -/
theorem threeCycle_tseitin_supportGroupedPartialNoiseInputPermutation :
    List.Perm
      threeCycle_tseitin_supportGroupedPartialNoiseDecomposition.expandedCNF
      threeCycle_tseitin_supportGroupingPartialNoiseInputCNF := by
  native_decide

/-!
Stage1772 canonical support-key and fingerprint recognizer gate.

Stage1771 groups by first-occurrence support keys and uses `List.Perm` as the
executable block recognizer.  This gate adds canonical support keys and
canonical clause/block fingerprints.  The fingerprint recognizer is the scalable
executable surface; the older permutation recognizer remains available as the
proof-producing bridge for inputs whose literal order already matches the
generated parity clauses.
-/

/-- Insert an item into a list sorted by a boolean preorder. -/
def insertSortedBy {alpha : Type} (le : alpha -> alpha -> Bool)
    (x : alpha) : List alpha -> List alpha
  | [] => [x]
  | y :: ys =>
      if le x y then
        x :: y :: ys
      else
        y :: insertSortedBy le x ys

/-- Insertion sort by a boolean preorder. -/
def sortByBool {alpha : Type} (le : alpha -> alpha -> Bool) :
    List alpha -> List alpha
  | [] => []
  | x :: xs => insertSortedBy le x (sortByBool le xs)

/-- Boolean natural-number order for canonical fingerprints. -/
def natFingerprintLE (a b : Nat) : Bool :=
  decide (a <= b)

/-- Sort a list of natural-number fingerprint atoms. -/
def sortNatFingerprintAtoms (xs : List Nat) : List Nat :=
  sortByBool natFingerprintLE xs

/-- Boolean lexicographic order on natural-number lists. -/
def natListLexLE : List Nat -> List Nat -> Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
      if x < y then
        true
      else if y < x then
        false
      else
        natListLexLE xs ys

/-- Sort canonical clause fingerprints lexicographically. -/
def sortClauseFingerprints (xs : List (List Nat)) : List (List Nat) :=
  sortByBool natListLexLE xs

/-- Canonical support key used for clause grouping. -/
abbrev CanonicalClauseSupportKey := List Nat

/-- Sort variables by their finite index. -/
def sortFinByVal {m : Nat} (xs : List (Fin m)) : List (Fin m) :=
  sortByBool (fun a b => decide (a.val <= b.val)) xs

/-- Canonical variable support for one ordinary CNF clause. -/
def canonicalClauseSupportVars {m : Nat}
    (c : CNFModel.Clause m) : List (Fin m) :=
  (sortFinByVal (c.map (fun l => l.var))).eraseDups

/--
Canonical support key for one ordinary CNF clause.  Unlike Stage1771's
first-occurrence key, this key is invariant under literal reordering inside the
clause.
-/
def canonicalClauseSupportKey {m : Nat}
    (c : CNFModel.Clause m) : CanonicalClauseSupportKey :=
  (canonicalClauseSupportVars c).map (fun v => v.val)

/-- Encode a signed literal as a natural-number atom. -/
def canonicalLiteralAtom {m : Nat} (l : CNFModel.Literal m) : Nat :=
  2 * l.var.val + if l.sign then 1 else 0

/-- Canonical fingerprint for one clause: sorted signed-literal atoms. -/
def canonicalClauseFingerprint {m : Nat}
    (c : CNFModel.Clause m) : List Nat :=
  sortNatFingerprintAtoms (c.map canonicalLiteralAtom)

/-- Canonical fingerprint for a CNF block: sorted canonical clause fingerprints. -/
def canonicalBlockFingerprint {m : Nat}
    (f : CNFModel.CNF m) : List (List Nat) :=
  sortClauseFingerprints (f.map canonicalClauseFingerprint)

/--
Executable canonical parity-block recognizer.  This avoids `List.Perm` as the
primary executable check by comparing sorted fingerprints of the candidate block
and the generated parity block.
-/
def canonicalParityBlockRecognitionSignal {m : Nat}
    (blockCNF : CNFModel.CNF m)
    (spec : ParityBlockSyntacticSpec m) : Bool :=
  decide (canonicalBlockFingerprint blockCNF =
    canonicalBlockFingerprint spec.expandedCNF)

/-- A parity block recognized by canonical fingerprints. -/
structure CanonicalFingerprintRecognizedParityBlock (m : Nat) where
  blockCNF : CNFModel.CNF m
  spec : ParityBlockSyntacticSpec m
  fingerprintSignal :
    canonicalParityBlockRecognitionSignal blockCNF spec = true

/-- Scan-size proxy for canonical fingerprint recognition. -/
def CanonicalFingerprintRecognizedParityBlock.recognitionScanSize {m : Nat}
    (b : CanonicalFingerprintRecognizedParityBlock m) : Nat :=
  b.blockCNF.length + CNFModel.cnfLiteralCount b.blockCNF + b.spec.vars.length

/--
Optional bridge from canonical fingerprint recognition to the older syntactic
certificate, available when literal order also matches the generated CNF up to
clause permutation.
-/
def CanonicalFingerprintRecognizedParityBlock.toSyntactic? {m : Nat}
    (b : CanonicalFingerprintRecognizedParityBlock m) :
    Option (SyntacticRecognizedParityBlock m) :=
  if h : parityBlockRecognitionSignal b.blockCNF b.spec = true then
    some
      { blockCNF := b.blockCNF
        spec := b.spec
        recognitionSignal := h }
  else
    none

/-- Canonical-fingerprint decomposition with explicit residual CNF. -/
structure CanonicalFingerprintGF2Decomposition (m : Nat) where
  blocks : List (CanonicalFingerprintRecognizedParityBlock m)
  residualCNF : CNFModel.CNF m

/-- Core expanded clause count for canonical-fingerprint recognized blocks. -/
def CanonicalFingerprintGF2Decomposition.coreExpandedClauseCount {m : Nat}
    (d : CanonicalFingerprintGF2Decomposition m) : Nat :=
  d.blocks.foldl (fun acc b => acc + b.blockCNF.length) 0

/-- Core equation count for canonical-fingerprint recognized blocks. -/
def CanonicalFingerprintGF2Decomposition.coreEquationCount {m : Nat}
    (d : CanonicalFingerprintGF2Decomposition m) : Nat :=
  d.blocks.length

/-- Residual ordinary CNF clause count for a canonical-fingerprint decomposition. -/
def CanonicalFingerprintGF2Decomposition.residualClauseCount {m : Nat}
    (d : CanonicalFingerprintGF2Decomposition m) : Nat :=
  d.residualCNF.length

/-- Recognition scan-size proxy for a canonical-fingerprint decomposition. -/
def CanonicalFingerprintGF2Decomposition.recognitionScanSize {m : Nat}
    (d : CanonicalFingerprintGF2Decomposition m) : Nat :=
  d.blocks.foldl (fun acc b => acc + b.recognitionScanSize) 0 +
    d.residualClauseCount + CNFModel.cnfLiteralCount d.residualCNF

/-- Predicate for the case where canonical recognition covers the whole input. -/
def CanonicalFingerprintGF2Decomposition.hasEmptyResidual {m : Nat}
    (d : CanonicalFingerprintGF2Decomposition m) : Prop :=
  d.residualCNF = []

/-- Compact GF(2) equation associated with a canonical-fingerprint block. -/
def CanonicalFingerprintRecognizedParityBlock.compactGF2 {m : Nat}
    (b : CanonicalFingerprintRecognizedParityBlock m) :
    ResoplusPDT.ParityClause (Basic.CNF.mk m) :=
  parityClauseForVertex b.spec.vars b.spec.charge

/-- Ordinary CNF covered by a list of canonical-fingerprint blocks. -/
def canonicalFingerprintRecognizedBlocksCNF {m : Nat}
    (blocks : List (CanonicalFingerprintRecognizedParityBlock m)) :
    CNFModel.CNF m :=
  blocks.bind (fun b => b.blockCNF)

/-- Compact GF(2) core represented by canonical-fingerprint blocks. -/
def canonicalFingerprintRecognizedBlocksGF2 {m : Nat}
    (blocks : List (CanonicalFingerprintRecognizedParityBlock m)) :
    ResoplusPDT.CNFFormula (Basic.CNF.mk m) :=
  blocks.map (fun b => b.compactGF2)

/-- Ordinary CNF part covered by the canonical-fingerprint core. -/
def CanonicalFingerprintGF2Decomposition.coreCNF {m : Nat}
    (d : CanonicalFingerprintGF2Decomposition m) : CNFModel.CNF m :=
  canonicalFingerprintRecognizedBlocksCNF d.blocks

/-- Compact GF(2) core represented by a canonical-fingerprint decomposition. -/
def CanonicalFingerprintGF2Decomposition.coreGF2 {m : Nat}
    (d : CanonicalFingerprintGF2Decomposition m) :
    ResoplusPDT.CNFFormula (Basic.CNF.mk m) :=
  canonicalFingerprintRecognizedBlocksGF2 d.blocks

/-- Full ordinary CNF represented by a canonical-fingerprint decomposition. -/
def CanonicalFingerprintGF2Decomposition.expandedCNF {m : Nat}
    (d : CanonicalFingerprintGF2Decomposition m) : CNFModel.CNF m :=
  d.coreCNF ++ d.residualCNF

/-- Candidate support inferred canonically from the first clause of a block. -/
def parityCandidateCanonicalSupportFromBlock {m : Nat}
    (blockCNF : CNFModel.CNF m) : List (Fin m) :=
  match blockCNF with
  | [] => []
  | c :: _ => canonicalClauseSupportVars c

/-- Candidate parity-block spec inferred from canonical support and charge. -/
def inferredCanonicalParityBlockSpec {m : Nat}
    (blockCNF : CNFModel.CNF m) (charge : Bool) :
    ParityBlockSyntacticSpec m :=
  { vars := parityCandidateCanonicalSupportFromBlock blockCNF
    charge := charge }

/-- Try one charge for a canonical-fingerprint candidate parity block. -/
def inferCanonicalParityBlockWithCharge {m : Nat}
    (blockCNF : CNFModel.CNF m) (charge : Bool) :
    Option (CanonicalFingerprintRecognizedParityBlock m) :=
  let spec := inferredCanonicalParityBlockSpec blockCNF charge
  if h : canonicalParityBlockRecognitionSignal blockCNF spec = true then
    some
      { blockCNF := blockCNF
        spec := spec
        fingerprintSignal := h }
  else
    none

/-- Try both parity charges for a canonical-fingerprint candidate block. -/
def inferCanonicalParityBlock {m : Nat}
    (blockCNF : CNFModel.CNF m) :
    Option (CanonicalFingerprintRecognizedParityBlock m) :=
  match inferCanonicalParityBlockWithCharge blockCNF false with
  | some b => some b
  | none => inferCanonicalParityBlockWithCharge blockCNF true

/-- A group of ordinary CNF clauses sharing the same canonical support key. -/
abbrev CanonicalSupportClauseGroup (m : Nat) :=
  Prod CanonicalClauseSupportKey (CNFModel.CNF m)

/-- Insert one clause into the first canonical support group with the same key. -/
def insertClauseByCanonicalSupport {m : Nat}
    (c : CNFModel.Clause m) :
    List (CanonicalSupportClauseGroup m) ->
      List (CanonicalSupportClauseGroup m)
  | [] => [(canonicalClauseSupportKey c, [c])]
  | g :: rest =>
      if canonicalClauseSupportKey c = g.1 then
        (g.1, g.2 ++ [c]) :: rest
      else
        g :: insertClauseByCanonicalSupport c rest

/-- Group all clauses in a CNF by canonical support key. -/
def groupClausesByCanonicalSupport {m : Nat}
    (f : CNFModel.CNF m) : List (CanonicalSupportClauseGroup m) :=
  f.foldl (fun groups c => insertClauseByCanonicalSupport c groups) []

/-- Split canonical support groups into recognized blocks and residual CNF. -/
def splitCanonicalSupportClauseGroups {m : Nat} :
    List (CanonicalSupportClauseGroup m) ->
      CanonicalFingerprintGF2Decomposition m
  | [] =>
      { blocks := []
        residualCNF := [] }
  | g :: rest =>
      let tail := splitCanonicalSupportClauseGroups rest
      match inferCanonicalParityBlock g.2 with
      | some b =>
          { blocks := b :: tail.blocks
            residualCNF := tail.residualCNF }
      | none =>
          { blocks := tail.blocks
            residualCNF := g.2 ++ tail.residualCNF }

/-- Full-CNF splitter using canonical support grouping and fingerprints. -/
def splitArityFourParityCanonicalSupportGroups {m : Nat}
    (f : CNFModel.CNF m) : CanonicalFingerprintGF2Decomposition m :=
  splitCanonicalSupportClauseGroups (groupClausesByCanonicalSupport f)

/-- Reverse literal order inside every clause of a CNF. -/
def reverseClauseLiterals {m : Nat}
    (f : CNFModel.CNF m) : CNFModel.CNF m :=
  f.map (fun c => c.reverse)

/-- Reversing literal order inside every clause preserves CNF satisfaction. -/
theorem cnfSat_reverseClauseLiterals_iff
    {m : Nat} (a : CNFModel.Assignment m)
    (f : CNFModel.CNF m) :
    CNFModel.cnfSat a (reverseClauseLiterals f) <->
      CNFModel.cnfSat a f := by
  unfold reverseClauseLiterals
  constructor
  · intro hsat c hc
    have hrev : c.reverse ∈ f.map (fun c => c.reverse) :=
      List.mem_map.2 ⟨c, hc, rfl⟩
    exact (clauseSat_reverse_iff a c).1 (hsat c.reverse hrev)
  · intro hsat c hc
    rcases List.mem_map.1 hc with ⟨orig, horig, hco⟩
    subst hco
    exact (clauseSat_reverse_iff a orig).2 (hsat orig horig)

/-- First clause of a CNF, with empty fallback for closed smoke controls. -/
def firstClauseOrEmpty {m : Nat}
    (f : CNFModel.CNF m) : CNFModel.Clause m :=
  match f with
  | c :: _ => c
  | [] => []

/-- Drop the first clause of a CNF, with empty fallback for closed smoke controls. -/
def dropFirstClause {m : Nat}
    (f : CNFModel.CNF m) : CNFModel.CNF m :=
  match f with
  | _ :: rest => rest
  | [] => []

/-- First opposite-charge parity clause for a recognized block, used as conflict noise. -/
def firstOppositeChargeClause {m : Nat}
    (b : SyntacticRecognizedParityBlock m) : CNFModel.Clause m :=
  match clausesForVertex b.spec.vars (!b.spec.charge) with
  | c :: _ => c
  | [] => []

/-- Three-cycle input with literal order reversed inside every clause. -/
def threeCycle_tseitin_canonicalLiteralReorderedInputCNF :
    CNFModel.CNF threeCycleGraph.m :=
  reverseClauseLiterals threeCycle_tseitin_supportGroupingInterleavedInputCNF

/-- Four-cycle input with literal order reversed inside every clause. -/
def fourCycle_tseitin_canonicalLiteralReorderedInputCNF :
    CNFModel.CNF fourCycleGraph.m :=
  reverseClauseLiterals fourCycle_tseitin_supportGroupingInterleavedInputCNF

/-- Canonical decomposition of the literal-reordered three-cycle input. -/
def threeCycle_tseitin_canonicalLiteralReorderedDecomposition :
    CanonicalFingerprintGF2Decomposition threeCycleGraph.m :=
  splitArityFourParityCanonicalSupportGroups
    threeCycle_tseitin_canonicalLiteralReorderedInputCNF

/-- Canonical decomposition of the literal-reordered four-cycle input. -/
def fourCycle_tseitin_canonicalLiteralReorderedDecomposition :
    CanonicalFingerprintGF2Decomposition fourCycleGraph.m :=
  splitArityFourParityCanonicalSupportGroups
    fourCycle_tseitin_canonicalLiteralReorderedInputCNF

/-- Literal-reordered three-cycle canonical resource accounting. -/
theorem threeCycle_tseitin_canonicalLiteralReorderedResourceCounts :
    (threeCycle_tseitin_canonicalLiteralReorderedDecomposition.coreExpandedClauseCount = 24) /\
      (threeCycle_tseitin_canonicalLiteralReorderedDecomposition.coreEquationCount = 3) /\
      (threeCycle_tseitin_canonicalLiteralReorderedDecomposition.residualClauseCount = 0) /\
      (threeCycle_tseitin_canonicalLiteralReorderedDecomposition.recognitionScanSize = 132) := by
  native_decide

/-- Literal-reordered four-cycle canonical resource accounting. -/
theorem fourCycle_tseitin_canonicalLiteralReorderedResourceCounts :
    (fourCycle_tseitin_canonicalLiteralReorderedDecomposition.coreExpandedClauseCount = 32) /\
      (fourCycle_tseitin_canonicalLiteralReorderedDecomposition.coreEquationCount = 4) /\
      (fourCycle_tseitin_canonicalLiteralReorderedDecomposition.residualClauseCount = 0) /\
      (fourCycle_tseitin_canonicalLiteralReorderedDecomposition.recognitionScanSize = 176) := by
  native_decide

/-- Existing proof bridge still succeeds on the non-literal-reordered Stage1771 input. -/
def threeCycle_tseitin_canonicalBridgeableDecomposition :
    SyntacticGF2HybridDecomposition threeCycleGraph.m :=
  splitArityFourParitySupportGroups
    threeCycle_tseitin_supportGroupingInterleavedInputCNF

/--
The proof-producing Stage1769 bridge remains available for canonical-grouped input
whose literal order is already compatible with generated parity clauses.
-/
theorem threeCycle_tseitin_canonicalBridgeableResourceCounts :
    (threeCycle_tseitin_canonicalBridgeableDecomposition.coreEquationCount = 3) /\
      (threeCycle_tseitin_canonicalBridgeableDecomposition.residualClauseCount = 0) := by
  native_decide

/-- Canonical decomposition with the Stage1771 incomplete two-variable residual group. -/
def threeCycle_tseitin_canonicalPartialNoiseDecomposition :
    CanonicalFingerprintGF2Decomposition threeCycleGraph.m :=
  splitArityFourParityCanonicalSupportGroups
    (threeCycle_tseitin_canonicalLiteralReorderedInputCNF ++
      [threeCycle_tseitin_supportGroupingPartialNoiseClause])

/-- Incomplete support groups remain residual under canonical recognition. -/
theorem threeCycle_tseitin_canonicalPartialNoiseResourceCounts :
    (threeCycle_tseitin_canonicalPartialNoiseDecomposition.coreEquationCount = 3) /\
      (threeCycle_tseitin_canonicalPartialNoiseDecomposition.residualClauseCount = 1) := by
  native_decide

/-- Three-cycle input with one clause removed from a support group. -/
def threeCycle_tseitin_canonicalMissingClauseInputCNF :
    CNFModel.CNF threeCycleGraph.m :=
  dropFirstClause threeCycle_tseitin_canonicalLiteralReorderedInputCNF

/-- Canonical decomposition with an incomplete seven-clause support group. -/
def threeCycle_tseitin_canonicalMissingClauseDecomposition :
    CanonicalFingerprintGF2Decomposition threeCycleGraph.m :=
  splitArityFourParityCanonicalSupportGroups
    threeCycle_tseitin_canonicalMissingClauseInputCNF

/-- Missing-clause groups are residualized rather than accepted. -/
theorem threeCycle_tseitin_canonicalMissingClauseResourceCounts :
    (threeCycle_tseitin_canonicalMissingClauseDecomposition.coreExpandedClauseCount = 16) /\
      (threeCycle_tseitin_canonicalMissingClauseDecomposition.coreEquationCount = 2) /\
      (threeCycle_tseitin_canonicalMissingClauseDecomposition.residualClauseCount = 7) := by
  native_decide

/-- Three-cycle input with a duplicate clause added to one support group. -/
def threeCycle_tseitin_canonicalDuplicateClauseInputCNF :
    CNFModel.CNF threeCycleGraph.m :=
  threeCycle_tseitin_canonicalLiteralReorderedInputCNF ++
    [firstClauseOrEmpty threeCycle_tseitin_canonicalLiteralReorderedInputCNF]

/-- Canonical decomposition with a duplicate/oversized support group. -/
def threeCycle_tseitin_canonicalDuplicateClauseDecomposition :
    CanonicalFingerprintGF2Decomposition threeCycleGraph.m :=
  splitArityFourParityCanonicalSupportGroups
    threeCycle_tseitin_canonicalDuplicateClauseInputCNF

/-- Duplicate/oversized support groups are residualized rather than accepted. -/
theorem threeCycle_tseitin_canonicalDuplicateClauseResourceCounts :
    (threeCycle_tseitin_canonicalDuplicateClauseDecomposition.coreExpandedClauseCount = 16) /\
      (threeCycle_tseitin_canonicalDuplicateClauseDecomposition.coreEquationCount = 2) /\
      (threeCycle_tseitin_canonicalDuplicateClauseDecomposition.residualClauseCount = 9) := by
  native_decide

/-- Opposite-charge conflict clause in the support of the first three-cycle block. -/
def threeCycle_tseitin_canonicalConflictingSupportClause :
    CNFModel.Clause threeCycleGraph.m :=
  match threeCycle_tseitin_syntacticRecognizedBlocks with
  | b :: _ => reverseClauseLiterals [firstOppositeChargeClause b] |>.head?.getD []
  | [] => []

/-- Three-cycle input with an opposite-charge conflict in one support group. -/
def threeCycle_tseitin_canonicalConflictingSupportInputCNF :
    CNFModel.CNF threeCycleGraph.m :=
  threeCycle_tseitin_canonicalLiteralReorderedInputCNF ++
    [threeCycle_tseitin_canonicalConflictingSupportClause]

/-- Canonical decomposition with a conflicting/oversized support group. -/
def threeCycle_tseitin_canonicalConflictingSupportDecomposition :
    CanonicalFingerprintGF2Decomposition threeCycleGraph.m :=
  splitArityFourParityCanonicalSupportGroups
    threeCycle_tseitin_canonicalConflictingSupportInputCNF

/-- Conflicting support groups are residualized rather than accepted. -/
theorem threeCycle_tseitin_canonicalConflictingSupportResourceCounts :
    (threeCycle_tseitin_canonicalConflictingSupportDecomposition.coreExpandedClauseCount = 16) /\
      (threeCycle_tseitin_canonicalConflictingSupportDecomposition.coreEquationCount = 2) /\
      (threeCycle_tseitin_canonicalConflictingSupportDecomposition.residualClauseCount = 9) := by
  native_decide

/-- Unary parity clause discovered during the Stage1771 noisy-control correction. -/
def threeCycle_tseitin_canonicalUnaryParityClause :
    CNFModel.Clause threeCycleGraph.m :=
  [{ var := Fin.mk 0 (by decide), sign := true }]

/-- Canonical decomposition of a standalone unary parity clause. -/
def threeCycle_tseitin_canonicalUnaryParityDecomposition :
    CanonicalFingerprintGF2Decomposition threeCycleGraph.m :=
  splitArityFourParityCanonicalSupportGroups
    [threeCycle_tseitin_canonicalUnaryParityClause]

/-- A one-literal clause is recognized as a unary parity equation, not residual noise. -/
theorem threeCycle_tseitin_canonicalUnaryParityResourceCounts :
    (threeCycle_tseitin_canonicalUnaryParityDecomposition.coreExpandedClauseCount = 1) /\
      (threeCycle_tseitin_canonicalUnaryParityDecomposition.coreEquationCount = 1) /\
      (threeCycle_tseitin_canonicalUnaryParityDecomposition.residualClauseCount = 0) := by
  native_decide

/-!
Stage1773 canonical-fingerprint semantic bridge gate.

Stage1772 made canonical fingerprints the executable recognition surface, but a
fingerprint match alone is not a semantic theorem.  This gate adds a
proof-producing bridge object: a canonical-fingerprint block can feed the GF(2)
semantic stack only when it also carries a direct block-level semantic
certificate.  The first certified path is intentionally narrow and linear: take
an existing Stage1769 syntactic certificate, reverse literal order inside every
clause, and use the generic literal-reversal theorem above.
-/

/-- Linear certificate-size proxy for a literal-order semantic bridge. -/
def literalOrderBridgeCertificateSize {m : Nat}
    (f : CNFModel.CNF m) : Nat :=
  f.length + CNFModel.cnfLiteralCount f

/--
Canonical-fingerprint block with the additional proof needed to use it
semantically.  The fingerprint signal is executable evidence; the
`blockSemanticPreservation` field is the proof-producing bridge.
-/
structure CanonicalSemanticCertifiedParityBlock (m : Nat) where
  canonicalBlock : CanonicalFingerprintRecognizedParityBlock m
  blockSemanticPreservation :
    forall a : CNFModel.Assignment m,
      CNFModel.cnfSat a canonicalBlock.blockCNF <->
        CNFModel.cnfSat a canonicalBlock.spec.expandedCNF
  bridgeCertificateSize : Nat

/-- Ordinary CNF carried by a canonical semantic certificate block. -/
def CanonicalSemanticCertifiedParityBlock.blockCNF {m : Nat}
    (b : CanonicalSemanticCertifiedParityBlock m) : CNFModel.CNF m :=
  b.canonicalBlock.blockCNF

/-- Parity-block spec carried by a canonical semantic certificate block. -/
def CanonicalSemanticCertifiedParityBlock.spec {m : Nat}
    (b : CanonicalSemanticCertifiedParityBlock m) :
    ParityBlockSyntacticSpec m :=
  b.canonicalBlock.spec

/-- Compact GF(2) equation associated with a certified canonical block. -/
def CanonicalSemanticCertifiedParityBlock.compactGF2 {m : Nat}
    (b : CanonicalSemanticCertifiedParityBlock m) :
    ResoplusPDT.ParityClause (Basic.CNF.mk m) :=
  parityClauseForVertex b.spec.vars b.spec.charge

/-- A certified canonical block preserves semantics as one GF(2) equation. -/
theorem CanonicalSemanticCertifiedParityBlock.semanticPreservation
    {m : Nat} (b : CanonicalSemanticCertifiedParityBlock m)
    (a : CNFModel.Assignment m) :
    CNFModel.cnfSat a b.blockCNF <->
      ResoplusPDT.ClauseSat
        (F := Basic.CNF.mk m) a b.compactGF2 := by
  exact
    Iff.trans
      (b.blockSemanticPreservation a)
      (tseitinVertexBlock_gf2SemanticPreservation
        (m := m) a (vars := b.spec.vars) (charge := b.spec.charge))

/--
Turn an existing syntactic certificate into a canonical semantic certificate
after reversing literal order inside every clause.  The caller supplies the
canonical fingerprint signal; the semantic proof is structural and does not
enumerate assignments.
-/
def reverseLiteralCanonicalCertifiedBlockOfSyntactic {m : Nat}
    (b : SyntacticRecognizedParityBlock m)
    (hfp :
      canonicalParityBlockRecognitionSignal
        (reverseClauseLiterals b.blockCNF) b.spec = true) :
    CanonicalSemanticCertifiedParityBlock m :=
  { canonicalBlock :=
      { blockCNF := reverseClauseLiterals b.blockCNF
        spec := b.spec
        fingerprintSignal := hfp }
    blockSemanticPreservation := by
      intro a
      exact
        Iff.trans
          (cnfSat_reverseClauseLiterals_iff a b.blockCNF)
          (cnfSat_iff_of_perm (a := a)
            (by
              simpa [ParityBlockSyntacticSpec.expandedCNF] using
                parityBlockRecognitionSignal_sound b.recognitionSignal))
    bridgeCertificateSize :=
      b.recognitionScanSize + literalOrderBridgeCertificateSize b.blockCNF }

/-- Ordinary CNF covered by certified canonical blocks. -/
def canonicalSemanticCertifiedBlocksCNF {m : Nat}
    (blocks : List (CanonicalSemanticCertifiedParityBlock m)) :
    CNFModel.CNF m :=
  blocks.bind (fun b => b.blockCNF)

/-- Compact GF(2) formula represented by certified canonical blocks. -/
def canonicalSemanticCertifiedBlocksGF2 {m : Nat}
    (blocks : List (CanonicalSemanticCertifiedParityBlock m)) :
    ResoplusPDT.CNFFormula (Basic.CNF.mk m) :=
  blocks.map (fun b => b.compactGF2)

/-- Certificate-size proxy for a list of certified canonical blocks. -/
def canonicalSemanticCertifiedBlocksBridgeCertificateSize {m : Nat}
    (blocks : List (CanonicalSemanticCertifiedParityBlock m)) : Nat :=
  blocks.foldl (fun acc b => acc + b.bridgeCertificateSize) 0

/-- Certified canonical GF(2) decomposition with explicit residual CNF. -/
structure CanonicalSemanticCertifiedGF2Decomposition (m : Nat) where
  blocks : List (CanonicalSemanticCertifiedParityBlock m)
  residualCNF : CNFModel.CNF m

/-- Ordinary CNF part covered by the certified canonical core. -/
def CanonicalSemanticCertifiedGF2Decomposition.coreCNF {m : Nat}
    (d : CanonicalSemanticCertifiedGF2Decomposition m) : CNFModel.CNF m :=
  canonicalSemanticCertifiedBlocksCNF d.blocks

/-- Compact GF(2) core represented by a certified canonical decomposition. -/
def CanonicalSemanticCertifiedGF2Decomposition.coreGF2 {m : Nat}
    (d : CanonicalSemanticCertifiedGF2Decomposition m) :
    ResoplusPDT.CNFFormula (Basic.CNF.mk m) :=
  canonicalSemanticCertifiedBlocksGF2 d.blocks

/-- Full ordinary CNF represented by a certified canonical decomposition. -/
def CanonicalSemanticCertifiedGF2Decomposition.expandedCNF {m : Nat}
    (d : CanonicalSemanticCertifiedGF2Decomposition m) : CNFModel.CNF m :=
  d.coreCNF ++ d.residualCNF

/-- Core expanded clause count for a certified canonical decomposition. -/
def CanonicalSemanticCertifiedGF2Decomposition.coreExpandedClauseCount {m : Nat}
    (d : CanonicalSemanticCertifiedGF2Decomposition m) : Nat :=
  d.coreCNF.length

/-- Core equation count for a certified canonical decomposition. -/
def CanonicalSemanticCertifiedGF2Decomposition.coreEquationCount {m : Nat}
    (d : CanonicalSemanticCertifiedGF2Decomposition m) : Nat :=
  d.coreGF2.length

/-- Residual ordinary CNF clause count for a certified canonical decomposition. -/
def CanonicalSemanticCertifiedGF2Decomposition.residualClauseCount {m : Nat}
    (d : CanonicalSemanticCertifiedGF2Decomposition m) : Nat :=
  d.residualCNF.length

/-- Bridge certificate-size proxy for a certified canonical decomposition. -/
def CanonicalSemanticCertifiedGF2Decomposition.bridgeCertificateSize {m : Nat}
    (d : CanonicalSemanticCertifiedGF2Decomposition m) : Nat :=
  canonicalSemanticCertifiedBlocksBridgeCertificateSize d.blocks +
    d.residualClauseCount + CNFModel.cnfLiteralCount d.residualCNF

/-- Predicate for the case where the certified canonical core covers the input. -/
def CanonicalSemanticCertifiedGF2Decomposition.hasEmptyResidual {m : Nat}
    (d : CanonicalSemanticCertifiedGF2Decomposition m) : Prop :=
  d.residualCNF = []

/-- Certified canonical blocks preserve semantics as a compact GF(2) core. -/
theorem canonicalSemanticCertifiedBlocks_semanticPreservation
    {m : Nat} (blocks : List (CanonicalSemanticCertifiedParityBlock m))
    (a : CNFModel.Assignment m) :
    CNFModel.cnfSat a (canonicalSemanticCertifiedBlocksCNF blocks) <->
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk m) a
        (canonicalSemanticCertifiedBlocksGF2 blocks) := by
  constructor
  · intro hcnf c hc
    rcases List.mem_map.1 hc with ⟨b, hb, hbc⟩
    have hblock : CNFModel.cnfSat a b.blockCNF := by
      intro d hd
      exact hcnf d (List.mem_bind.2 ⟨b, hb, hd⟩)
    have hsat :
        ResoplusPDT.ClauseSat
          (F := Basic.CNF.mk m) a b.compactGF2 :=
      (CanonicalSemanticCertifiedParityBlock.semanticPreservation b a).1 hblock
    simpa [canonicalSemanticCertifiedBlocksGF2, hbc] using hsat
  · intro hgf2 c hc
    rcases List.mem_bind.1 hc with ⟨b, hb, hcblock⟩
    have hclause :
        ResoplusPDT.ClauseSat
          (F := Basic.CNF.mk m) a b.compactGF2 := by
      exact
        hgf2 b.compactGF2
          (List.mem_map.2 ⟨b, hb, rfl⟩)
    have hblock : CNFModel.cnfSat a b.blockCNF :=
      (CanonicalSemanticCertifiedParityBlock.semanticPreservation b a).2 hclause
    exact hblock c hcblock

/-- The certified canonical core preserves semantics. -/
theorem CanonicalSemanticCertifiedGF2Decomposition.coreSemanticPreservation
    {m : Nat} (d : CanonicalSemanticCertifiedGF2Decomposition m)
    (a : CNFModel.Assignment m) :
    CNFModel.cnfSat a d.coreCNF <->
      ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a d.coreGF2 :=
  canonicalSemanticCertifiedBlocks_semanticPreservation d.blocks a

/-- If no residual CNF remains, certified canonical recognition preserves full semantics. -/
theorem CanonicalSemanticCertifiedGF2Decomposition.emptyResidualSemanticPreservation
    {m : Nat} (d : CanonicalSemanticCertifiedGF2Decomposition m)
    (hres : d.hasEmptyResidual)
    (a : CNFModel.Assignment m) :
    CNFModel.cnfSat a d.expandedCNF <->
      ResoplusPDT.CNFSat (F := Basic.CNF.mk m) a d.coreGF2 := by
  unfold CanonicalSemanticCertifiedGF2Decomposition.expandedCNF
  rw [hres, List.append_nil]
  exact CanonicalSemanticCertifiedGF2Decomposition.coreSemanticPreservation d a

/-- Vertex-2 reversed-literal canonical certificate for the three-cycle smoke input. -/
def threeCycle_tseitin_canonicalLiteralReorderedCertifiedBlock2 :
    CanonicalSemanticCertifiedParityBlock threeCycleGraph.m :=
  reverseLiteralCanonicalCertifiedBlockOfSyntactic
    { blockCNF :=
        (clausesForVertex
          (incidentIndices threeCycleGraph threeCycleHm 2)
          (threeCycleCharge 2)).reverse
      spec :=
        { vars := incidentIndices threeCycleGraph threeCycleHm 2
          charge := threeCycleCharge 2 }
      recognitionSignal := by native_decide }
    (by native_decide)

/-- Vertex-1 reversed-literal canonical certificate for the three-cycle smoke input. -/
def threeCycle_tseitin_canonicalLiteralReorderedCertifiedBlock1 :
    CanonicalSemanticCertifiedParityBlock threeCycleGraph.m :=
  reverseLiteralCanonicalCertifiedBlockOfSyntactic
    { blockCNF :=
        (clausesForVertex
          (incidentIndices threeCycleGraph threeCycleHm 1)
          (threeCycleCharge 1)).reverse
      spec :=
        { vars := incidentIndices threeCycleGraph threeCycleHm 1
          charge := threeCycleCharge 1 }
      recognitionSignal := by native_decide }
    (by native_decide)

/-- Vertex-0 reversed-literal canonical certificate for the three-cycle smoke input. -/
def threeCycle_tseitin_canonicalLiteralReorderedCertifiedBlock0 :
    CanonicalSemanticCertifiedParityBlock threeCycleGraph.m :=
  reverseLiteralCanonicalCertifiedBlockOfSyntactic
    { blockCNF :=
        (clausesForVertex
          (incidentIndices threeCycleGraph threeCycleHm 0)
          (threeCycleCharge 0)).reverse
      spec :=
        { vars := incidentIndices threeCycleGraph threeCycleHm 0
          charge := threeCycleCharge 0 }
      recognitionSignal := by native_decide }
    (by native_decide)

/-- Certified canonical decomposition for the literal-reordered three-cycle input. -/
def threeCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition :
    CanonicalSemanticCertifiedGF2Decomposition threeCycleGraph.m where
  blocks :=
    [ threeCycle_tseitin_canonicalLiteralReorderedCertifiedBlock2
    , threeCycle_tseitin_canonicalLiteralReorderedCertifiedBlock1
    , threeCycle_tseitin_canonicalLiteralReorderedCertifiedBlock0 ]
  residualCNF := []

/-- Certified canonical three-cycle recognition preserves semantics. -/
theorem threeCycle_tseitin_canonicalLiteralReorderedCertifiedSemanticPreservation
    (a : CNFModel.Assignment threeCycleGraph.m) :
    CNFModel.cnfSat a
        threeCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.expandedCNF <->
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk threeCycleGraph.m) a
        threeCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.coreGF2 :=
  CanonicalSemanticCertifiedGF2Decomposition.emptyResidualSemanticPreservation
    threeCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition rfl a

/-- The certified three-cycle bridge covers the Stage1772 splitter output up to clause order. -/
theorem threeCycle_tseitin_canonicalLiteralReorderedCertifiedMatchesSplitter :
    List.Perm
      threeCycle_tseitin_canonicalLiteralReorderedDecomposition.expandedCNF
      threeCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.expandedCNF := by
  native_decide

/-- The Stage1772 canonical three-cycle splitter output has checked certified GF(2) semantics. -/
theorem threeCycle_tseitin_canonicalLiteralReorderedSplitterSemanticPreservation
    (a : CNFModel.Assignment threeCycleGraph.m) :
    CNFModel.cnfSat a
        threeCycle_tseitin_canonicalLiteralReorderedDecomposition.expandedCNF <->
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk threeCycleGraph.m) a
        threeCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.coreGF2 := by
  exact
    Iff.trans
      (cnfSat_iff_of_perm (a := a)
        threeCycle_tseitin_canonicalLiteralReorderedCertifiedMatchesSplitter)
      (threeCycle_tseitin_canonicalLiteralReorderedCertifiedSemanticPreservation a)

/-- The certified three-cycle bridge preserves the literal-reordered input up to clause order. -/
theorem threeCycle_tseitin_canonicalLiteralReorderedCertifiedInputPermutation :
    List.Perm
      threeCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.expandedCNF
      threeCycle_tseitin_canonicalLiteralReorderedInputCNF := by
  native_decide

/-- Three-cycle Stage1773 bridge accounting. -/
theorem threeCycle_tseitin_canonicalLiteralReorderedCertifiedResourceCounts :
    (threeCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.coreExpandedClauseCount = 24) /\
      (threeCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.coreEquationCount = 3) /\
      (threeCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.residualClauseCount = 0) /\
      (threeCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.bridgeCertificateSize = 252) := by
  native_decide

/-- Vertex-3 reversed-literal canonical certificate for the four-cycle smoke input. -/
def fourCycle_tseitin_canonicalLiteralReorderedCertifiedBlock3 :
    CanonicalSemanticCertifiedParityBlock fourCycleGraph.m :=
  reverseLiteralCanonicalCertifiedBlockOfSyntactic
    { blockCNF :=
        (clausesForVertex
          (incidentIndices fourCycleGraph fourCycleHm 3)
          (fourCycleCharge 3)).reverse
      spec :=
        { vars := incidentIndices fourCycleGraph fourCycleHm 3
          charge := fourCycleCharge 3 }
      recognitionSignal := by native_decide }
    (by native_decide)

/-- Vertex-2 reversed-literal canonical certificate for the four-cycle smoke input. -/
def fourCycle_tseitin_canonicalLiteralReorderedCertifiedBlock2 :
    CanonicalSemanticCertifiedParityBlock fourCycleGraph.m :=
  reverseLiteralCanonicalCertifiedBlockOfSyntactic
    { blockCNF :=
        (clausesForVertex
          (incidentIndices fourCycleGraph fourCycleHm 2)
          (fourCycleCharge 2)).reverse
      spec :=
        { vars := incidentIndices fourCycleGraph fourCycleHm 2
          charge := fourCycleCharge 2 }
      recognitionSignal := by native_decide }
    (by native_decide)

/-- Vertex-1 reversed-literal canonical certificate for the four-cycle smoke input. -/
def fourCycle_tseitin_canonicalLiteralReorderedCertifiedBlock1 :
    CanonicalSemanticCertifiedParityBlock fourCycleGraph.m :=
  reverseLiteralCanonicalCertifiedBlockOfSyntactic
    { blockCNF :=
        (clausesForVertex
          (incidentIndices fourCycleGraph fourCycleHm 1)
          (fourCycleCharge 1)).reverse
      spec :=
        { vars := incidentIndices fourCycleGraph fourCycleHm 1
          charge := fourCycleCharge 1 }
      recognitionSignal := by native_decide }
    (by native_decide)

/-- Vertex-0 reversed-literal canonical certificate for the four-cycle smoke input. -/
def fourCycle_tseitin_canonicalLiteralReorderedCertifiedBlock0 :
    CanonicalSemanticCertifiedParityBlock fourCycleGraph.m :=
  reverseLiteralCanonicalCertifiedBlockOfSyntactic
    { blockCNF :=
        (clausesForVertex
          (incidentIndices fourCycleGraph fourCycleHm 0)
          (fourCycleCharge 0)).reverse
      spec :=
        { vars := incidentIndices fourCycleGraph fourCycleHm 0
          charge := fourCycleCharge 0 }
      recognitionSignal := by native_decide }
    (by native_decide)

/-- Certified canonical decomposition for the literal-reordered four-cycle input. -/
def fourCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition :
    CanonicalSemanticCertifiedGF2Decomposition fourCycleGraph.m where
  blocks :=
    [ fourCycle_tseitin_canonicalLiteralReorderedCertifiedBlock3
    , fourCycle_tseitin_canonicalLiteralReorderedCertifiedBlock2
    , fourCycle_tseitin_canonicalLiteralReorderedCertifiedBlock1
    , fourCycle_tseitin_canonicalLiteralReorderedCertifiedBlock0 ]
  residualCNF := []

/-- Certified canonical four-cycle recognition preserves semantics. -/
theorem fourCycle_tseitin_canonicalLiteralReorderedCertifiedSemanticPreservation
    (a : CNFModel.Assignment fourCycleGraph.m) :
    CNFModel.cnfSat a
        fourCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.expandedCNF <->
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk fourCycleGraph.m) a
        fourCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.coreGF2 :=
  CanonicalSemanticCertifiedGF2Decomposition.emptyResidualSemanticPreservation
    fourCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition rfl a

/-- The certified four-cycle bridge covers the Stage1772 splitter output up to clause order. -/
theorem fourCycle_tseitin_canonicalLiteralReorderedCertifiedMatchesSplitter :
    List.Perm
      fourCycle_tseitin_canonicalLiteralReorderedDecomposition.expandedCNF
      fourCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.expandedCNF := by
  native_decide

/-- The Stage1772 canonical four-cycle splitter output has checked certified GF(2) semantics. -/
theorem fourCycle_tseitin_canonicalLiteralReorderedSplitterSemanticPreservation
    (a : CNFModel.Assignment fourCycleGraph.m) :
    CNFModel.cnfSat a
        fourCycle_tseitin_canonicalLiteralReorderedDecomposition.expandedCNF <->
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk fourCycleGraph.m) a
        fourCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.coreGF2 := by
  exact
    Iff.trans
      (cnfSat_iff_of_perm (a := a)
        fourCycle_tseitin_canonicalLiteralReorderedCertifiedMatchesSplitter)
      (fourCycle_tseitin_canonicalLiteralReorderedCertifiedSemanticPreservation a)

/-- The certified four-cycle bridge preserves the literal-reordered input up to clause order. -/
theorem fourCycle_tseitin_canonicalLiteralReorderedCertifiedInputPermutation :
    List.Perm
      fourCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.expandedCNF
      fourCycle_tseitin_canonicalLiteralReorderedInputCNF := by
  native_decide

/-- Four-cycle Stage1773 bridge accounting. -/
theorem fourCycle_tseitin_canonicalLiteralReorderedCertifiedResourceCounts :
    (fourCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.coreExpandedClauseCount = 32) /\
      (fourCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.coreEquationCount = 4) /\
      (fourCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.residualClauseCount = 0) /\
      (fourCycle_tseitin_canonicalLiteralReorderedCertifiedDecomposition.bridgeCertificateSize = 336) := by
  native_decide

/-- Incomplete residual groups remain outside the Stage1773 empty-residual bridge. -/
theorem threeCycle_tseitin_canonicalPartialNoise_not_emptyResidual :
    Not (threeCycle_tseitin_canonicalPartialNoiseDecomposition.hasEmptyResidual) := by
  change Not (threeCycle_tseitin_canonicalPartialNoiseDecomposition.residualCNF = [])
  native_decide

/-- Missing-clause residual groups remain outside the Stage1773 empty-residual bridge. -/
theorem threeCycle_tseitin_canonicalMissingClause_not_emptyResidual :
    Not (threeCycle_tseitin_canonicalMissingClauseDecomposition.hasEmptyResidual) := by
  change Not (threeCycle_tseitin_canonicalMissingClauseDecomposition.residualCNF = [])
  native_decide

/-- Duplicate-clause residual groups remain outside the Stage1773 empty-residual bridge. -/
theorem threeCycle_tseitin_canonicalDuplicateClause_not_emptyResidual :
    Not (threeCycle_tseitin_canonicalDuplicateClauseDecomposition.hasEmptyResidual) := by
  change Not (threeCycle_tseitin_canonicalDuplicateClauseDecomposition.residualCNF = [])
  native_decide

/-- Conflicting-support residual groups remain outside the Stage1773 empty-residual bridge. -/
theorem threeCycle_tseitin_canonicalConflictingSupport_not_emptyResidual :
    Not (threeCycle_tseitin_canonicalConflictingSupportDecomposition.hasEmptyResidual) := by
  change Not (threeCycle_tseitin_canonicalConflictingSupportDecomposition.residualCNF = [])
  native_decide

/-!
Stage1774 canonical-fingerprint certificate extraction gate.

Stage1773 proved that a canonical block can feed the GF(2) stack once it carries an
explicit semantic certificate.  This gate adds the first bounded extractor for
such certificates.  The extractor checks canonical block fingerprints as a
guard, then validates clause-level and literal-level coverage by finite scans.
It does not treat fingerprint equality alone as a theorem and it does not call
`List.Perm` as the hidden scaling mechanism.
-/

/-- Bounded literal-membership scan used by Stage1774 certificate extraction. -/
def literalMemSignal {m : Nat}
    (l : CNFModel.Literal m) : CNFModel.Clause m -> Bool
  | [] => false
  | r :: rs =>
      if l = r then
        true
      else
        literalMemSignal l rs

/-- Soundness of the bounded literal-membership scan. -/
theorem literalMemSignal_sound
    {m : Nat} {l : CNFModel.Literal m} {c : CNFModel.Clause m}
    (h : literalMemSignal l c = true) :
    l ∈ c := by
  induction c with
  | nil =>
      simp [literalMemSignal] at h
  | cons r rs ih =>
      by_cases heq : l = r
      · simp [literalMemSignal, heq]
      · have htail : literalMemSignal l rs = true := by
          simpa [literalMemSignal, heq] using h
        exact List.mem_cons_of_mem r (ih htail)

/-- Bounded subset scan for the literal set of one clause. -/
def clauseLiteralSubsetSignal {m : Nat} :
    CNFModel.Clause m -> CNFModel.Clause m -> Bool
  | [], _ => true
  | l :: ls, target =>
      if literalMemSignal l target then
        clauseLiteralSubsetSignal ls target
      else
        false

/-- Soundness of the bounded clause-literal subset scan. -/
theorem clauseLiteralSubsetSignal_sound
    {m : Nat} {source target : CNFModel.Clause m}
    (h : clauseLiteralSubsetSignal source target = true) :
    forall l : CNFModel.Literal m, l ∈ source -> l ∈ target := by
  induction source with
  | nil =>
      intro l hl
      cases hl
  | cons head tail ih =>
      intro l hl
      cases hmem : literalMemSignal head target with
      | false =>
          simp [clauseLiteralSubsetSignal, hmem] at h
      | true =>
          have htail : clauseLiteralSubsetSignal tail target = true := by
            simpa [clauseLiteralSubsetSignal, hmem] using h
          have hl' : l = head ∨ l ∈ tail := by
            simpa [List.mem_cons] using hl
          rcases hl' with rfl | htailmem
          · exact literalMemSignal_sound hmem
          · exact ih htail l htailmem

/--
Clause-level fingerprint/membership match signal.  The fingerprint equality is
kept as an executable guard, while the two subset scans are the semantic
certificate payload.
-/
def clauseFingerprintMatchSignal {m : Nat}
    (source target : CNFModel.Clause m) : Bool :=
  if canonicalClauseFingerprint source = canonicalClauseFingerprint target then
    if clauseLiteralSubsetSignal source target then
      clauseLiteralSubsetSignal target source
    else
      false
  else
    false

/-- A successful clause fingerprint/membership match preserves clause semantics. -/
theorem clauseFingerprintMatchSignal_semanticPreservation
    {m : Nat} {source target : CNFModel.Clause m}
    (h : clauseFingerprintMatchSignal source target = true)
    (a : CNFModel.Assignment m) :
    CNFModel.clauseSat a source <->
      CNFModel.clauseSat a target := by
  unfold clauseFingerprintMatchSignal at h
  by_cases hfp :
      canonicalClauseFingerprint source = canonicalClauseFingerprint target
  · cases hst : clauseLiteralSubsetSignal source target with
    | false =>
        simp [hfp, hst] at h
    | true =>
        have hts : clauseLiteralSubsetSignal target source = true := by
          simpa [hfp, hst] using h
        constructor
        · rintro ⟨l, hl, hval⟩
          exact
            ⟨l, clauseLiteralSubsetSignal_sound hst l hl, hval⟩
        · rintro ⟨l, hl, hval⟩
          exact
            ⟨l, clauseLiteralSubsetSignal_sound hts l hl, hval⟩
  · simp [hfp] at h

/-- Does one source clause have a bounded fingerprint/membership match in a target CNF? -/
def clauseHasFingerprintMatchSignal {m : Nat}
    (source : CNFModel.Clause m) : CNFModel.CNF m -> Bool
  | [] => false
  | target :: rest =>
      if clauseFingerprintMatchSignal source target then
        true
      else
        clauseHasFingerprintMatchSignal source rest

/-- Soundness of the bounded clause-match search. -/
theorem clauseHasFingerprintMatchSignal_sound
    {m : Nat} {source : CNFModel.Clause m} {targets : CNFModel.CNF m}
    (h : clauseHasFingerprintMatchSignal source targets = true) :
    Exists fun target : CNFModel.Clause m =>
      target ∈ targets /\
        forall a : CNFModel.Assignment m,
          CNFModel.clauseSat a source <->
            CNFModel.clauseSat a target := by
  induction targets with
  | nil =>
      simp [clauseHasFingerprintMatchSignal] at h
  | cons target rest ih =>
      cases hmatch : clauseFingerprintMatchSignal source target with
      | false =>
          have hrest : clauseHasFingerprintMatchSignal source rest = true := by
            simpa [clauseHasFingerprintMatchSignal, hmatch] using h
          rcases ih hrest with ⟨w, hwmem, hwsem⟩
          exact
            ⟨w, List.mem_cons_of_mem target hwmem, hwsem⟩
      | true =>
          exact
            ⟨target, List.mem_cons_self target rest,
              fun a =>
                clauseFingerprintMatchSignal_semanticPreservation
                  hmatch a⟩

/-- Every clause on the source side has a bounded fingerprint/membership match on the target side. -/
def blockClauseCoverageSignal {m : Nat} :
    CNFModel.CNF m -> CNFModel.CNF m -> Bool
  | [], _ => true
  | source :: rest, targets =>
      if clauseHasFingerprintMatchSignal source targets then
        blockClauseCoverageSignal rest targets
      else
        false

/-- Soundness of the bounded block-coverage scan. -/
theorem blockClauseCoverageSignal_sound
    {m : Nat} {source target : CNFModel.CNF m}
    (h : blockClauseCoverageSignal source target = true) :
    forall c : CNFModel.Clause m, c ∈ source ->
      Exists fun d : CNFModel.Clause m =>
        d ∈ target /\
          forall a : CNFModel.Assignment m,
            CNFModel.clauseSat a c <->
              CNFModel.clauseSat a d := by
  induction source with
  | nil =>
      intro c hc
      cases hc
  | cons c rest ih =>
      intro q hq
      cases hmatch : clauseHasFingerprintMatchSignal c target with
      | false =>
          simp [blockClauseCoverageSignal, hmatch] at h
      | true =>
          have hrest : blockClauseCoverageSignal rest target = true := by
            simpa [blockClauseCoverageSignal, hmatch] using h
          have hq' : q = c ∨ q ∈ rest := by
            simpa [List.mem_cons] using hq
          rcases hq' with rfl | htail
          · exact clauseHasFingerprintMatchSignal_sound hmatch
          · exact ih hrest q htail

/--
Two-sided bounded clause coverage proves direct CNF semantic preservation.
This is the Stage1774 replacement for treating fingerprint equality as a theorem.
-/
theorem cnfSat_iff_of_blockClauseCoverageSignals
    {m : Nat} {source target : CNFModel.CNF m}
    (hst : blockClauseCoverageSignal source target = true)
    (hts : blockClauseCoverageSignal target source = true)
    (a : CNFModel.Assignment m) :
    CNFModel.cnfSat a source <-> CNFModel.cnfSat a target := by
  constructor
  · intro hsource c hc
    rcases blockClauseCoverageSignal_sound hts c hc with
      ⟨d, hd, hsem⟩
    exact (hsem a).2 (hsource d hd)
  · intro htarget c hc
    rcases blockClauseCoverageSignal_sound hst c hc with
      ⟨d, hd, hsem⟩
    exact (hsem a).2 (htarget d hd)

/-- Size proxy for a bounded canonical block certificate. -/
def canonicalBlockFingerprintCertificateSize {m : Nat}
    (source target : CNFModel.CNF m) : Nat :=
  source.length + target.length +
    CNFModel.cnfLiteralCount source + CNFModel.cnfLiteralCount target

/--
Bounded certificate that a canonical block and target block have direct CNF
semantic equivalence.  The block fingerprint equality is recorded, but the
proof uses the explicit two-sided coverage signals.
-/
structure CanonicalBlockFingerprintCertificate {m : Nat}
    (source target : CNFModel.CNF m) where
  blockFingerprintEq :
    canonicalBlockFingerprint source = canonicalBlockFingerprint target
  sourceCoverageSignal :
    blockClauseCoverageSignal source target = true
  targetCoverageSignal :
    blockClauseCoverageSignal target source = true
  certificateSize : Nat

/-- A bounded canonical block certificate preserves CNF semantics. -/
theorem CanonicalBlockFingerprintCertificate.semanticPreservation
    {m : Nat} {source target : CNFModel.CNF m}
    (cert : CanonicalBlockFingerprintCertificate source target)
    (a : CNFModel.Assignment m) :
    CNFModel.cnfSat a source <-> CNFModel.cnfSat a target :=
  cnfSat_iff_of_blockClauseCoverageSignals
    cert.sourceCoverageSignal cert.targetCoverageSignal a

/--
Extract a bounded semantic certificate for two canonical blocks.  Failure means
the block must remain residual or unproved; success is not based on `List.Perm`.
-/
def extractCanonicalBlockFingerprintCertificate? {m : Nat}
    (source target : CNFModel.CNF m) :
    Option (CanonicalBlockFingerprintCertificate source target) :=
  if hfp :
      canonicalBlockFingerprint source = canonicalBlockFingerprint target then
    if hst : blockClauseCoverageSignal source target = true then
      if hts : blockClauseCoverageSignal target source = true then
        some
          { blockFingerprintEq := hfp
            sourceCoverageSignal := hst
            targetCoverageSignal := hts
            certificateSize :=
              canonicalBlockFingerprintCertificateSize source target }
      else
        none
    else
      none
  else
    none

/-- Try to extract the Stage1774 semantic certificate for one canonical-fingerprint block. -/
def CanonicalFingerprintRecognizedParityBlock.extractSemanticCertified? {m : Nat}
    (b : CanonicalFingerprintRecognizedParityBlock m) :
    Option (CanonicalSemanticCertifiedParityBlock m) :=
  match extractCanonicalBlockFingerprintCertificate? b.blockCNF b.spec.expandedCNF with
  | some cert =>
      some
        { canonicalBlock := b
          blockSemanticPreservation := by
            intro a
            exact cert.semanticPreservation a
          bridgeCertificateSize :=
            b.recognitionScanSize + cert.certificateSize }
  | none => none

/-- Try to certify a list of canonical-fingerprint blocks. -/
def extractCanonicalSemanticCertifiedBlocks? {m : Nat} :
    List (CanonicalFingerprintRecognizedParityBlock m) ->
      Option (List (CanonicalSemanticCertifiedParityBlock m))
  | [] => some []
  | b :: rest =>
      match b.extractSemanticCertified?,
        extractCanonicalSemanticCertifiedBlocks? rest with
      | some cb, some crest => some (cb :: crest)
      | _, _ => none

/-- Try to certify every canonical block in a decomposition while preserving residual CNF. -/
def CanonicalFingerprintGF2Decomposition.extractSemanticCertified? {m : Nat}
    (d : CanonicalFingerprintGF2Decomposition m) :
    Option (CanonicalSemanticCertifiedGF2Decomposition m) :=
  match extractCanonicalSemanticCertifiedBlocks? d.blocks with
  | some blocks =>
      some
        { blocks := blocks
          residualCNF := d.residualCNF }
  | none => none

/--
Total fallback for failed extraction: if certification fails, keep the whole
canonical representation as residual ordinary CNF rather than accepting it.
-/
def CanonicalFingerprintGF2Decomposition.extractSemanticCertifiedOrResidual {m : Nat}
    (d : CanonicalFingerprintGF2Decomposition m) :
    CanonicalSemanticCertifiedGF2Decomposition m :=
  match d.extractSemanticCertified? with
  | some certified => certified
  | none =>
      { blocks := []
        residualCNF := d.expandedCNF }

/-- Stage1774 extraction succeeds on the Stage1772 literal-reordered three-cycle splitter output. -/
theorem threeCycle_tseitin_canonicalLiteralReorderedExtractionSucceeds :
    (threeCycle_tseitin_canonicalLiteralReorderedDecomposition.extractSemanticCertified?).isSome =
      true := by
  native_decide

/-- Stage1774 extracted certified decomposition for the literal-reordered three-cycle output. -/
def threeCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition :
    CanonicalSemanticCertifiedGF2Decomposition threeCycleGraph.m :=
  threeCycle_tseitin_canonicalLiteralReorderedDecomposition.extractSemanticCertifiedOrResidual

/-- Stage1774 extracted three-cycle certified decomposition preserves GF(2) semantics. -/
theorem threeCycle_tseitin_canonicalLiteralReorderedExtractedSemanticPreservation
    (a : CNFModel.Assignment threeCycleGraph.m) :
    CNFModel.cnfSat a
        threeCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition.expandedCNF <->
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk threeCycleGraph.m) a
        threeCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition.coreGF2 := by
  have hres :
      threeCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition.hasEmptyResidual := by
    change
      threeCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition.residualCNF =
        []
    native_decide
  exact
    CanonicalSemanticCertifiedGF2Decomposition.emptyResidualSemanticPreservation
      threeCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition hres a

/-- Stage1774 extracted three-cycle certificate accounting. -/
theorem threeCycle_tseitin_canonicalLiteralReorderedExtractedResourceCounts :
    (threeCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition.coreExpandedClauseCount = 24) /\
      (threeCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition.coreEquationCount = 3) /\
      (threeCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition.residualClauseCount = 0) /\
      (threeCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition.bridgeCertificateSize = 372) := by
  native_decide

/-- Stage1774 extraction succeeds on the Stage1772 literal-reordered four-cycle splitter output. -/
theorem fourCycle_tseitin_canonicalLiteralReorderedExtractionSucceeds :
    (fourCycle_tseitin_canonicalLiteralReorderedDecomposition.extractSemanticCertified?).isSome =
      true := by
  native_decide

/-- Stage1774 extracted certified decomposition for the literal-reordered four-cycle output. -/
def fourCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition :
    CanonicalSemanticCertifiedGF2Decomposition fourCycleGraph.m :=
  fourCycle_tseitin_canonicalLiteralReorderedDecomposition.extractSemanticCertifiedOrResidual

/-- Stage1774 extracted four-cycle certified decomposition preserves GF(2) semantics. -/
theorem fourCycle_tseitin_canonicalLiteralReorderedExtractedSemanticPreservation
    (a : CNFModel.Assignment fourCycleGraph.m) :
    CNFModel.cnfSat a
        fourCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition.expandedCNF <->
      ResoplusPDT.CNFSat
        (F := Basic.CNF.mk fourCycleGraph.m) a
        fourCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition.coreGF2 := by
  have hres :
      fourCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition.hasEmptyResidual := by
    change
      fourCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition.residualCNF =
        []
    native_decide
  exact
    CanonicalSemanticCertifiedGF2Decomposition.emptyResidualSemanticPreservation
      fourCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition hres a

/-- Stage1774 extracted four-cycle certificate accounting. -/
theorem fourCycle_tseitin_canonicalLiteralReorderedExtractedResourceCounts :
    (fourCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition.coreExpandedClauseCount = 32) /\
      (fourCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition.coreEquationCount = 4) /\
      (fourCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition.residualClauseCount = 0) /\
      (fourCycle_tseitin_canonicalLiteralReorderedExtractedCertifiedDecomposition.bridgeCertificateSize = 496) := by
  native_decide

/-- Extracted certification preserves the partial-noise residual clause. -/
def threeCycle_tseitin_canonicalPartialNoiseExtractedCertifiedDecomposition :
    CanonicalSemanticCertifiedGF2Decomposition threeCycleGraph.m :=
  threeCycle_tseitin_canonicalPartialNoiseDecomposition.extractSemanticCertifiedOrResidual

/-- Partial-noise extraction keeps the residual explicit. -/
theorem threeCycle_tseitin_canonicalPartialNoiseExtractedResourceCounts :
    (threeCycle_tseitin_canonicalPartialNoiseExtractedCertifiedDecomposition.coreEquationCount = 3) /\
      (threeCycle_tseitin_canonicalPartialNoiseExtractedCertifiedDecomposition.residualClauseCount = 1) := by
  native_decide

/-- Extracted certification preserves the missing-clause residual group. -/
def threeCycle_tseitin_canonicalMissingClauseExtractedCertifiedDecomposition :
    CanonicalSemanticCertifiedGF2Decomposition threeCycleGraph.m :=
  threeCycle_tseitin_canonicalMissingClauseDecomposition.extractSemanticCertifiedOrResidual

/-- Missing-clause extraction keeps the residual explicit. -/
theorem threeCycle_tseitin_canonicalMissingClauseExtractedResourceCounts :
    (threeCycle_tseitin_canonicalMissingClauseExtractedCertifiedDecomposition.coreEquationCount = 2) /\
      (threeCycle_tseitin_canonicalMissingClauseExtractedCertifiedDecomposition.residualClauseCount = 7) := by
  native_decide

/-- Extracted certification preserves the duplicate/oversized residual group. -/
def threeCycle_tseitin_canonicalDuplicateClauseExtractedCertifiedDecomposition :
    CanonicalSemanticCertifiedGF2Decomposition threeCycleGraph.m :=
  threeCycle_tseitin_canonicalDuplicateClauseDecomposition.extractSemanticCertifiedOrResidual

/-- Duplicate-clause extraction keeps the residual explicit. -/
theorem threeCycle_tseitin_canonicalDuplicateClauseExtractedResourceCounts :
    (threeCycle_tseitin_canonicalDuplicateClauseExtractedCertifiedDecomposition.coreEquationCount = 2) /\
      (threeCycle_tseitin_canonicalDuplicateClauseExtractedCertifiedDecomposition.residualClauseCount = 9) := by
  native_decide

/-- Extracted certification preserves the conflicting-support residual group. -/
def threeCycle_tseitin_canonicalConflictingSupportExtractedCertifiedDecomposition :
    CanonicalSemanticCertifiedGF2Decomposition threeCycleGraph.m :=
  threeCycle_tseitin_canonicalConflictingSupportDecomposition.extractSemanticCertifiedOrResidual

/-- Conflicting-support extraction keeps the residual explicit. -/
theorem threeCycle_tseitin_canonicalConflictingSupportExtractedResourceCounts :
    (threeCycle_tseitin_canonicalConflictingSupportExtractedCertifiedDecomposition.coreEquationCount = 2) /\
      (threeCycle_tseitin_canonicalConflictingSupportExtractedCertifiedDecomposition.residualClauseCount = 9) := by
  native_decide

/-- Root charge used for the cycle-family CNF-resolution candidate. -/
def cycleRootCharge (v : Nat) : Bool :=
  v = 0

def TseitinCycleCNFFormula (n : Nat) (hn : 1 < n) :
    CNFModel.CNF
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived n hn)).m :=
  TseitinCNFFormulaFromEncoding (TseitinModel.encoding_cycle_derived n hn)
    cycleRootCharge

/-- Uniform direct GF(2) normalization surface for the derived directed cycle family. -/
def TseitinCycleGF2NormalizationSurface (n : Nat) (hn : 1 < n) :
    RecognizedGF2NormalizationSurface
      (TseitinModel.GraphEncodingData.toGraph
        (TseitinModel.encoding_cycle_derived n hn)).m :=
  recognizedTseitinGF2SurfaceFromEncoding
    (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge

/--
Uniform semantic preservation for the direct cycle GF(2) surface.

This theorem is structural: it instantiates the generic recognized-Tseitin
semantic bridge for every cycle prefix instead of checking 3/4/5 by evaluation.
-/
theorem TseitinCycleGF2NormalizationSurface_correctnessInvariant
    (n : Nat) (hn : 1 < n) :
    (TseitinCycleGF2NormalizationSurface n hn).correctnessInvariant := by
  dsimp [TseitinCycleGF2NormalizationSurface]
  exact
    recognizedTseitinGF2SurfaceFromEncoding_correctnessInvariant
      (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge

/-- Uniform clause count for the derived directed cycle Tseitin CNF. -/
theorem TseitinCycleCNFFormula_length (n : Nat) (hn : 1 < n) :
    (TseitinCycleCNFFormula n hn).length = n * 8 := by
  unfold TseitinCycleCNFFormula TseitinCNFFormulaFromEncoding TseitinCNFFormulaFromModel
  apply tseitinClausesFromIncident_length_of_const_vertex_clause_count
  intro v hv
  apply clausesForVertex_length_of_length_four
  have hvlt : v < n := List.mem_range.mp hv
  have hdeg :
      TseitinModel.degree
        (TseitinModel.GraphEncodingData.toGraph
          (TseitinModel.encoding_cycle_derived n hn)) v = 4 := by
    apply TseitinModel.cycle_degree_eq_four
    simpa [TseitinModel.encoding_cycle_derived, TseitinModel.encoding_cycle_nle,
      TseitinModel.encoding_cycle, TseitinModel.GraphEncodingData.toGraph] using hvlt
  have hlen := incidentIndices_length_eq_degree
    (TseitinModel.GraphEncodingData.toGraph
      (TseitinModel.encoding_cycle_derived n hn))
    (TseitinModel.m_eq_edges_length_of_encoding
      (TseitinModel.encoding_cycle_derived n hn)) v
  exact hlen.trans hdeg

/-- Uniform equation count for any direct Tseitin parity formula from an encoding. -/
theorem TseitinParityFormulaFromEncoding_length
    (enc : TseitinModel.GraphEncodingData) (charge : Nat -> Bool) :
    (TseitinParityFormulaFromEncoding enc charge).length =
      (TseitinModel.GraphEncodingData.toGraph enc).n := by
  dsimp [TseitinParityFormulaFromEncoding, tseitinParityFormulaFromIncident]
  simp

/--
Uniform resource accounting for the direct cycle GF(2) surface:
the directed cycle encoding contributes eight ordinary CNF clauses and one
compact parity equation per vertex.
-/
theorem TseitinCycleGF2NormalizationSurface_resourceCounts
    (n : Nat) (hn : 1 < n) :
    (TseitinCycleGF2NormalizationSurface n hn).expandedClauseCount = n * 8 /\
      (TseitinCycleGF2NormalizationSurface n hn).equationCount = n := by
  constructor
  · change (TseitinCycleCNFFormula n hn).length = n * 8
    exact TseitinCycleCNFFormula_length n hn
  · change
      (TseitinParityFormulaFromEncoding
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge).length = n
    simpa [TseitinModel.encoding_cycle_derived, TseitinModel.encoding_cycle_nle,
      TseitinModel.encoding_cycle, TseitinModel.GraphEncodingData.toGraph] using
      TseitinParityFormulaFromEncoding_length
        (TseitinModel.encoding_cycle_derived n hn) cycleRootCharge


def TseitinCycleResolutionFamilyTarget
    (threshold : (i : {n : Nat // 1 < n}) -> Nat) :
    CNFResolution.ResolutionSizeFamilyTarget where
  Index := {n : Nat // 1 < n}
  n := fun i =>
    (TseitinModel.GraphEncodingData.toGraph
      (TseitinModel.encoding_cycle_derived i.1 i.2)).m
  phi := fun i =>
    TseitinCycleCNFFormula i.1 i.2
  threshold := threshold

private lemma allFin_six :
    allFin 6 =
      [Fin.mk 0 (by decide), Fin.mk 1 (by decide), Fin.mk 2 (by decide),
       Fin.mk 3 (by decide), Fin.mk 4 (by decide), Fin.mk 5 (by decide)] := by
  simp [allFin, List.range]

private lemma allFin_eight :
    allFin 8 =
      [Fin.mk 0 (by decide), Fin.mk 1 (by decide), Fin.mk 2 (by decide),
       Fin.mk 3 (by decide), Fin.mk 4 (by decide), Fin.mk 5 (by decide),
       Fin.mk 6 (by decide), Fin.mk 7 (by decide)] := by
  simp [allFin, List.range]

private lemma incidentIndices_three_cycle_0 :
    incidentIndices threeCycleGraph threeCycleHm 0 =
      [Fin.mk 0 (by decide), Fin.mk 1 (by decide), Fin.mk 4 (by decide), Fin.mk 5 (by decide)] := by
  classical
  simpa [incidentIndices, edgeAt, threeCycleGraph, threeCycleHm, TseitinModel.UEdge.incident,
    TseitinModel.encoding_three_cycle, TseitinModel.GraphEncodingData.toGraph, allFin_six] using
    (by decide : incidentIndices threeCycleGraph threeCycleHm 0 =
      [Fin.mk 0 (by decide), Fin.mk 1 (by decide), Fin.mk 4 (by decide), Fin.mk 5 (by decide)])

private lemma incidentIndices_three_cycle_1 :
    incidentIndices threeCycleGraph threeCycleHm 1 =
      [Fin.mk 0 (by decide), Fin.mk 1 (by decide), Fin.mk 2 (by decide), Fin.mk 3 (by decide)] := by
  classical
  simpa [incidentIndices, edgeAt, threeCycleGraph, threeCycleHm, TseitinModel.UEdge.incident,
    TseitinModel.encoding_three_cycle, TseitinModel.GraphEncodingData.toGraph, allFin_six] using
    (by decide : incidentIndices threeCycleGraph threeCycleHm 1 =
      [Fin.mk 0 (by decide), Fin.mk 1 (by decide), Fin.mk 2 (by decide), Fin.mk 3 (by decide)])

private lemma incidentIndices_three_cycle_2 :
    incidentIndices threeCycleGraph threeCycleHm 2 =
      [Fin.mk 2 (by decide), Fin.mk 3 (by decide), Fin.mk 4 (by decide), Fin.mk 5 (by decide)] := by
  classical
  simpa [incidentIndices, edgeAt, threeCycleGraph, threeCycleHm, TseitinModel.UEdge.incident,
    TseitinModel.encoding_three_cycle, TseitinModel.GraphEncodingData.toGraph, allFin_six] using
    (by decide : incidentIndices threeCycleGraph threeCycleHm 2 =
      [Fin.mk 2 (by decide), Fin.mk 3 (by decide), Fin.mk 4 (by decide), Fin.mk 5 (by decide)])

private lemma incidentIndices_four_cycle_0 :
    incidentIndices fourCycleGraph fourCycleHm 0 =
      [Fin.mk 0 (by decide), Fin.mk 1 (by decide), Fin.mk 6 (by decide), Fin.mk 7 (by decide)] := by
  classical
  simpa [incidentIndices, edgeAt, fourCycleGraph, fourCycleHm, TseitinModel.UEdge.incident,
    TseitinModel.GraphEncodingData.toGraph, allFin_eight] using
    (by decide : incidentIndices fourCycleGraph fourCycleHm 0 =
      [Fin.mk 0 (by decide), Fin.mk 1 (by decide), Fin.mk 6 (by decide), Fin.mk 7 (by decide)])

private lemma incidentIndices_four_cycle_1 :
    incidentIndices fourCycleGraph fourCycleHm 1 =
      [Fin.mk 0 (by decide), Fin.mk 1 (by decide), Fin.mk 2 (by decide), Fin.mk 3 (by decide)] := by
  classical
  simpa [incidentIndices, edgeAt, fourCycleGraph, fourCycleHm, TseitinModel.UEdge.incident,
    TseitinModel.GraphEncodingData.toGraph, allFin_eight] using
    (by decide : incidentIndices fourCycleGraph fourCycleHm 1 =
      [Fin.mk 0 (by decide), Fin.mk 1 (by decide), Fin.mk 2 (by decide), Fin.mk 3 (by decide)])

private lemma incidentIndices_four_cycle_2 :
    incidentIndices fourCycleGraph fourCycleHm 2 =
      [Fin.mk 2 (by decide), Fin.mk 3 (by decide), Fin.mk 4 (by decide), Fin.mk 5 (by decide)] := by
  classical
  simpa [incidentIndices, edgeAt, fourCycleGraph, fourCycleHm, TseitinModel.UEdge.incident,
    TseitinModel.GraphEncodingData.toGraph, allFin_eight] using
    (by decide : incidentIndices fourCycleGraph fourCycleHm 2 =
      [Fin.mk 2 (by decide), Fin.mk 3 (by decide), Fin.mk 4 (by decide), Fin.mk 5 (by decide)])

private lemma incidentIndices_four_cycle_3 :
    incidentIndices fourCycleGraph fourCycleHm 3 =
      [Fin.mk 4 (by decide), Fin.mk 5 (by decide), Fin.mk 6 (by decide), Fin.mk 7 (by decide)] := by
  classical
  simpa [incidentIndices, edgeAt, fourCycleGraph, fourCycleHm, TseitinModel.UEdge.incident,
    TseitinModel.GraphEncodingData.toGraph, allFin_eight] using
    (by decide : incidentIndices fourCycleGraph fourCycleHm 3 =
      [Fin.mk 4 (by decide), Fin.mk 5 (by decide), Fin.mk 6 (by decide), Fin.mk 7 (by decide)])

theorem threeCycle_incident_concat_perm_dupList :
    List.Perm
      ((incidentIndices threeCycleGraph threeCycleHm 0) ++
          (incidentIndices threeCycleGraph threeCycleHm 1) ++
          (incidentIndices threeCycleGraph threeCycleHm 2))
      (List.bind (allFin threeCycleGraph.m) (fun v => [v, v])) := by
  -- reduce both sides to explicit lists and decide the permutation
  simp [incidentIndices_three_cycle_0, incidentIndices_three_cycle_1,
    incidentIndices_three_cycle_2, allFin_six]
  decide

theorem threeCycle_incident_concat_perm_dupVarClauseList :
    List.Perm
      ((incidentIndices threeCycleGraph threeCycleHm 0) ++
          (incidentIndices threeCycleGraph threeCycleHm 1) ++
          (incidentIndices threeCycleGraph threeCycleHm 2))
      ((ResoplusPDT.dupVarClauseList
          (ResoplusPDT.falseClause (Basic.CNF.mk threeCycleGraph.m))
          (allFin threeCycleGraph.m)).vars) := by
  simpa [ResoplusPDT.dupVarClauseList_vars] using
    (threeCycle_incident_concat_perm_dupList)

theorem threeCycle_parity_refutation :
    ResoplusPDT.ResoplusDerivesFromTree
      (ResoplusPDT.xorTree3
        (parityClauseForVertex (incidentIndices threeCycleGraph threeCycleHm 0)
          (threeCycleCharge 0))
        (parityClauseForVertex (incidentIndices threeCycleGraph threeCycleHm 1)
          (threeCycleCharge 1))
        (parityClauseForVertex (incidentIndices threeCycleGraph threeCycleHm 2)
          (threeCycleCharge 2)))
      (ResoplusPDT.falseClause (Basic.CNF.mk threeCycleGraph.m)) := by
  let c0 := parityClauseForVertex (incidentIndices threeCycleGraph threeCycleHm 0)
    (threeCycleCharge 0)
  let c1 := parityClauseForVertex (incidentIndices threeCycleGraph threeCycleHm 1)
    (threeCycleCharge 1)
  let c2 := parityClauseForVertex (incidentIndices threeCycleGraph threeCycleHm 2)
    (threeCycleCharge 2)
  have hperm :
      List.Perm (c0.vars ++ c1.vars ++ c2.vars)
        (ResoplusPDT.dupVarClauseList
          (ResoplusPDT.falseClause (Basic.CNF.mk threeCycleGraph.m))
          (allFin threeCycleGraph.m)).vars := by
    simpa [c0, c1, c2, parityClauseForVertex] using
      (threeCycle_incident_concat_perm_dupVarClauseList)
  have hrhs : Bool.xor c0.rhs (Bool.xor c1.rhs c2.rhs) = true := by
    simp [c0, c1, c2, parityClauseForVertex, threeCycleCharge]
  simpa [c0, c1, c2] using
    (ResoplusPDT.derives_false_of_three_parity
      (c0:=c0) (c1:=c1) (c2:=c2) (vs:=allFin threeCycleGraph.m) hperm hrhs)

def threeCycle_parity_refutation_tree :
    ResoplusPDT.ResoplusRefutation
      (Basic.CNF.mk threeCycleGraph.m)
      (TseitinParityFormulaThreeCycleCharge) := by
  let F := Basic.CNF.mk threeCycleGraph.m
  let c0 := parityClauseForVertex (incidentIndices threeCycleGraph threeCycleHm 0)
    (threeCycleCharge 0)
  let c1 := parityClauseForVertex (incidentIndices threeCycleGraph threeCycleHm 1)
    (threeCycleCharge 1)
  let c2 := parityClauseForVertex (incidentIndices threeCycleGraph threeCycleHm 2)
    (threeCycleCharge 2)
  have h0 : List.Mem c0 TseitinParityFormulaThreeCycleCharge := by
    dsimp [TseitinParityFormulaThreeCycleCharge, TseitinParityFormulaThreeCycle,
      TseitinParityFormulaFromEncoding, tseitinParityFormulaFromIncident]
    refine List.mem_map.2 ?_
    have h0mem : List.Mem 0 (List.range threeCycleGraph.n) := by
      exact (List.mem_range).2 (by decide)
    exact Exists.intro 0 (And.intro h0mem (by
      simp [c0, parityClauseForVertex, threeCycleCharge, threeCycleGraph,
        TseitinModel.encoding_three_cycle]))
  have h1 : List.Mem c1 TseitinParityFormulaThreeCycleCharge := by
    dsimp [TseitinParityFormulaThreeCycleCharge, TseitinParityFormulaThreeCycle,
      TseitinParityFormulaFromEncoding, tseitinParityFormulaFromIncident]
    refine List.mem_map.2 ?_
    have h1mem : List.Mem 1 (List.range threeCycleGraph.n) := by
      exact (List.mem_range).2 (by decide)
    exact Exists.intro 1 (And.intro h1mem (by
      simp [c1, parityClauseForVertex, threeCycleCharge, threeCycleGraph,
        TseitinModel.encoding_three_cycle]))
  have h2 : List.Mem c2 TseitinParityFormulaThreeCycleCharge := by
    dsimp [TseitinParityFormulaThreeCycleCharge, TseitinParityFormulaThreeCycle,
      TseitinParityFormulaFromEncoding, tseitinParityFormulaFromIncident]
    refine List.mem_map.2 ?_
    have h2mem : List.Mem 2 (List.range threeCycleGraph.n) := by
      exact (List.mem_range).2 (by decide)
    exact Exists.intro 2 (And.intro h2mem (by
      simp [c2, parityClauseForVertex, threeCycleCharge, threeCycleGraph,
        TseitinModel.encoding_three_cycle]))

  refine {
    tree := ResoplusPDT.xorTree3 c0 c1 c2
    , leaves_in := by
        simp [ResoplusPDT.ResoplusDerivTree.AllLeaves,
          ResoplusPDT.xorTree3, ResoplusPDT.xorTree, h0, h1, h2]
    , derives_false := by
        simpa [c0, c1, c2] using (threeCycle_parity_refutation)
    }

def fourCycle_parity_refutation_tree :
    ResoplusPDT.ResoplusRefutation
      (Basic.CNF.mk fourCycleGraph.m)
      (TseitinParityFormulaFourCycleCharge) := by
  let c0 := parityClauseForVertex (incidentIndices fourCycleGraph fourCycleHm 0)
    (fourCycleCharge 0)
  let c1 := parityClauseForVertex (incidentIndices fourCycleGraph fourCycleHm 1)
    (fourCycleCharge 1)
  let c2 := parityClauseForVertex (incidentIndices fourCycleGraph fourCycleHm 2)
    (fourCycleCharge 2)
  let c3 := parityClauseForVertex (incidentIndices fourCycleGraph fourCycleHm 3)
    (fourCycleCharge 3)
  have h0 : List.Mem c0 TseitinParityFormulaFourCycleCharge := by
    dsimp [TseitinParityFormulaFourCycleCharge, TseitinParityFormulaFourCycle,
      TseitinParityFormulaFromEncoding, tseitinParityFormulaFromIncident]
    refine List.mem_map.2 ?_
    have h0mem : List.Mem 0 (List.range fourCycleGraph.n) := by
      exact (List.mem_range).2 (by decide)
    exact Exists.intro 0 (And.intro h0mem (by
      simp [c0, parityClauseForVertex, fourCycleCharge, fourCycleGraph,
        incidentIndices_four_cycle_0]))
  have h1 : List.Mem c1 TseitinParityFormulaFourCycleCharge := by
    dsimp [TseitinParityFormulaFourCycleCharge, TseitinParityFormulaFourCycle,
      TseitinParityFormulaFromEncoding, tseitinParityFormulaFromIncident]
    refine List.mem_map.2 ?_
    have h1mem : List.Mem 1 (List.range fourCycleGraph.n) := by
      exact (List.mem_range).2 (by decide)
    exact Exists.intro 1 (And.intro h1mem (by
      simp [c1, parityClauseForVertex, fourCycleCharge, fourCycleGraph,
        incidentIndices_four_cycle_1]))
  have h2 : List.Mem c2 TseitinParityFormulaFourCycleCharge := by
    dsimp [TseitinParityFormulaFourCycleCharge, TseitinParityFormulaFourCycle,
      TseitinParityFormulaFromEncoding, tseitinParityFormulaFromIncident]
    refine List.mem_map.2 ?_
    have h2mem : List.Mem 2 (List.range fourCycleGraph.n) := by
      exact (List.mem_range).2 (by decide)
    exact Exists.intro 2 (And.intro h2mem (by
      simp [c2, parityClauseForVertex, fourCycleCharge, fourCycleGraph,
        incidentIndices_four_cycle_2]))
  have h3 : List.Mem c3 TseitinParityFormulaFourCycleCharge := by
    dsimp [TseitinParityFormulaFourCycleCharge, TseitinParityFormulaFourCycle,
      TseitinParityFormulaFromEncoding, tseitinParityFormulaFromIncident]
    refine List.mem_map.2 ?_
    have h3mem : List.Mem 3 (List.range fourCycleGraph.n) := by
      exact (List.mem_range).2 (by decide)
    exact Exists.intro 3 (And.intro h3mem (by
      simp [c3, parityClauseForVertex, fourCycleCharge, fourCycleGraph,
        incidentIndices_four_cycle_3]))
  have hperm : List.Perm (c0.vars ++ c1.vars ++ c2.vars ++ c3.vars)
      (ResoplusPDT.dupVarClauseList
        (ResoplusPDT.falseClause (Basic.CNF.mk fourCycleGraph.m))
        (allFin fourCycleGraph.m)).vars := by
    simp [incidentIndices_four_cycle_0, incidentIndices_four_cycle_1,
      incidentIndices_four_cycle_2, incidentIndices_four_cycle_3, c0, c1, c2, c3,
      parityClauseForVertex, allFin_eight]
    decide
  have hrhs : Bool.xor c0.rhs (Bool.xor c1.rhs (Bool.xor c2.rhs c3.rhs)) = true := by
    simp [c0, c1, c2, c3, parityClauseForVertex, fourCycleCharge]
  refine {
    tree := ResoplusPDT.xorTree4 c0 c1 c2 c3
    , leaves_in := by
        simp [ResoplusPDT.ResoplusDerivTree.AllLeaves,
          ResoplusPDT.xorTree4, ResoplusPDT.xorTree, h0, h1, h2, h3]
    , derives_false := by
        simpa [c0, c1, c2, c3] using
          (ResoplusPDT.derives_false_of_four_parity
            (c0:=c0) (c1:=c1) (c2:=c2) (c3:=c3)
            (vs:=allFin fourCycleGraph.m) hperm hrhs)
    }

def fourCycle_parity_tree_witness :
    ResoplusPDT.ResoplusTreeWitness
      (ResoplusPDT.cnfSearchRel
        (F:=Basic.CNF.mk fourCycleGraph.m)
        TseitinParityFormulaFourCycleCharge) :=
  ResoplusPDT.tree_witness_of_refutation fourCycle_parity_refutation_tree

theorem fourCycle_parity_size_measure_compatible_left :
    ResoplusPDT.SizeMeasureCompatibleLeft
      (F:=Basic.CNF.mk fourCycleGraph.m)
      (W:=ResoplusPDT.ParityClause (Basic.CNF.mk fourCycleGraph.m))
      (ResoplusPDT.cnfSearchRel
        (F:=Basic.CNF.mk fourCycleGraph.m)
        TseitinParityFormulaFourCycleCharge) := by
  exact ResoplusPDT.size_measure_compatible_left_of_tree_witness
    (F:=Basic.CNF.mk fourCycleGraph.m)
    (SR:=ResoplusPDT.cnfSearchRel
      (F:=Basic.CNF.mk fourCycleGraph.m)
      TseitinParityFormulaFourCycleCharge)
    fourCycle_parity_tree_witness

theorem fourCycle_parity_resoplus_to_pdt_size :
    Exists fun (pi : ResoplusPDT.ResoplusProof (Basic.CNF.mk fourCycleGraph.m)
      (ResoplusPDT.ParityClause (Basic.CNF.mk fourCycleGraph.m))
      (ResoplusPDT.cnfSearchRel
        (F:=Basic.CNF.mk fourCycleGraph.m)
        TseitinParityFormulaFourCycleCharge)) =>
      Exists fun (t : ResoplusPDT.PDT (Basic.CNF.mk fourCycleGraph.m)
        (ResoplusPDT.ParityClause (Basic.CNF.mk fourCycleGraph.m))) =>
        ResoplusPDT.PDTsize t <= ResoplusPDT.ResoplusSize
          (SR:=ResoplusPDT.cnfSearchRel
            (F:=Basic.CNF.mk fourCycleGraph.m)
            TseitinParityFormulaFourCycleCharge) pi := by
  exact ResoplusPDT.resoplus_to_pdt_size_transfer
    (F:=Basic.CNF.mk fourCycleGraph.m)
    (W:=ResoplusPDT.ParityClause (Basic.CNF.mk fourCycleGraph.m))
    (ResoplusPDT.cnfSearchRel
      (F:=Basic.CNF.mk fourCycleGraph.m)
      TseitinParityFormulaFourCycleCharge)
    fourCycle_parity_size_measure_compatible_left

def threeCycle_parity_tree_witness :
    ResoplusPDT.ResoplusTreeWitness
      (ResoplusPDT.cnfSearchRel
        (F:=Basic.CNF.mk threeCycleGraph.m)
        TseitinParityFormulaThreeCycleCharge) :=
  ResoplusPDT.tree_witness_of_refutation threeCycle_parity_refutation_tree

theorem threeCycle_parity_size_measure_compatible_left :
    ResoplusPDT.SizeMeasureCompatibleLeft
      (F:=Basic.CNF.mk threeCycleGraph.m)
      (W:=ResoplusPDT.ParityClause (Basic.CNF.mk threeCycleGraph.m))
      (ResoplusPDT.cnfSearchRel
        (F:=Basic.CNF.mk threeCycleGraph.m)
        TseitinParityFormulaThreeCycleCharge) := by
  exact ResoplusPDT.size_measure_compatible_left_of_tree_witness
    (F:=Basic.CNF.mk threeCycleGraph.m)
    (SR:=ResoplusPDT.cnfSearchRel
      (F:=Basic.CNF.mk threeCycleGraph.m)
      TseitinParityFormulaThreeCycleCharge)
    threeCycle_parity_tree_witness

theorem threeCycle_parity_resoplus_to_pdt_size :
    Exists fun (pi : ResoplusPDT.ResoplusProof (Basic.CNF.mk threeCycleGraph.m)
      (ResoplusPDT.ParityClause (Basic.CNF.mk threeCycleGraph.m))
      (ResoplusPDT.cnfSearchRel
        (F:=Basic.CNF.mk threeCycleGraph.m)
        TseitinParityFormulaThreeCycleCharge)) =>
      Exists fun (t : ResoplusPDT.PDT (Basic.CNF.mk threeCycleGraph.m)
        (ResoplusPDT.ParityClause (Basic.CNF.mk threeCycleGraph.m))) =>
        ResoplusPDT.PDTsize t <= ResoplusPDT.ResoplusSize
          (SR:=ResoplusPDT.cnfSearchRel
            (F:=Basic.CNF.mk threeCycleGraph.m)
            TseitinParityFormulaThreeCycleCharge) pi := by
  exact ResoplusPDT.resoplus_to_pdt_size_transfer
    (F:=Basic.CNF.mk threeCycleGraph.m)
    (W:=ResoplusPDT.ParityClause (Basic.CNF.mk threeCycleGraph.m))
    (ResoplusPDT.cnfSearchRel
      (F:=Basic.CNF.mk threeCycleGraph.m)
      TseitinParityFormulaThreeCycleCharge)
    threeCycle_parity_size_measure_compatible_left

/-- One satisfying search witness for the three-cycle parity formula's old transfer interface. -/
theorem threeCycle_parity_search_total :
    ResoplusPDT.SearchTotal (Basic.CNF.mk threeCycleGraph.m)
      (ResoplusPDT.cnfSearchRel
        (F:=Basic.CNF.mk threeCycleGraph.m)
        TseitinParityFormulaThreeCycleCharge) := by
  refine Exists.intro (fun _ => false : ResoplusPDT.Assignment (Basic.CNF.mk threeCycleGraph.m)) ?_
  refine Exists.intro
    (parityClauseForVertex (incidentIndices threeCycleGraph threeCycleHm 1)
      (threeCycleCharge 1)) ?_
  constructor
  · dsimp [TseitinParityFormulaThreeCycleCharge, TseitinParityFormulaThreeCycle,
      TseitinParityFormulaFromEncoding, tseitinParityFormulaFromIncident]
    refine List.mem_map.2 ?_
    have h1mem : List.Mem 1 (List.range threeCycleGraph.n) := by
      exact (List.mem_range).2 (by decide)
    exact Exists.intro 1 (And.intro h1mem (by
      simp [parityClauseForVertex, threeCycleCharge, threeCycleGraph,
        TseitinModel.encoding_three_cycle]))
  · simp [ResoplusPDT.ClauseSat, ResoplusPDT.clauseEval, parityClauseForVertex,
      threeCycleCharge, incidentIndices_three_cycle_1, ResoplusPDT.parity]

/-- One satisfying search witness for the four-cycle parity formula's old transfer interface. -/
theorem fourCycle_parity_search_total :
    ResoplusPDT.SearchTotal (Basic.CNF.mk fourCycleGraph.m)
      (ResoplusPDT.cnfSearchRel
        (F:=Basic.CNF.mk fourCycleGraph.m)
        TseitinParityFormulaFourCycleCharge) := by
  refine Exists.intro (fun _ => false : ResoplusPDT.Assignment (Basic.CNF.mk fourCycleGraph.m)) ?_
  refine Exists.intro
    (parityClauseForVertex (incidentIndices fourCycleGraph fourCycleHm 1)
      (fourCycleCharge 1)) ?_
  constructor
  · dsimp [TseitinParityFormulaFourCycleCharge, TseitinParityFormulaFourCycle,
      TseitinParityFormulaFromEncoding, tseitinParityFormulaFromIncident]
    refine List.mem_map.2 ?_
    have h1mem : List.Mem 1 (List.range fourCycleGraph.n) := by
      exact (List.mem_range).2 (by decide)
    exact Exists.intro 1 (And.intro h1mem (by
      simp [parityClauseForVertex, fourCycleCharge, fourCycleGraph,
        incidentIndices_four_cycle_1]))
  · simp [ResoplusPDT.ClauseSat, ResoplusPDT.clauseEval, parityClauseForVertex,
      fourCycleCharge, incidentIndices_four_cycle_1, ResoplusPDT.parity]

def threeCycle_refuted_cnf :
    ResoplusPDT.RefutedCNF (Basic.CNF.mk threeCycleGraph.m) where
  formula := TseitinParityFormulaThreeCycleCharge
  refutation := threeCycle_parity_refutation_tree

def fourCycle_refuted_cnf :
    ResoplusPDT.RefutedCNF (Basic.CNF.mk fourCycleGraph.m) where
  formula := TseitinParityFormulaFourCycleCharge
  refutation := fourCycle_parity_refutation_tree

noncomputable def threeCycle_refuted_certificate :
    ResoplusPDT.RefutedCNFCertificate (Basic.CNF.mk threeCycleGraph.m) :=
  ResoplusPDT.refuted_cnf_certificate threeCycle_refuted_cnf

noncomputable def fourCycle_refuted_certificate :
    ResoplusPDT.RefutedCNFCertificate (Basic.CNF.mk fourCycleGraph.m) :=
  ResoplusPDT.refuted_cnf_certificate fourCycle_refuted_cnf

noncomputable def threeCycle_transfer_certified_cnf :
    ResoplusPDT.TransferCertifiedCNF (Basic.CNF.mk threeCycleGraph.m) where
  certificate := threeCycle_refuted_certificate
  search_total := threeCycle_parity_search_total

noncomputable def fourCycle_transfer_certified_cnf :
    ResoplusPDT.TransferCertifiedCNF (Basic.CNF.mk fourCycleGraph.m) where
  certificate := fourCycle_refuted_certificate
  search_total := fourCycle_parity_search_total

def threeCycle_transfer_normalization :
    ResoplusPDT.TransferNormalization
      (F:=Basic.CNF.mk threeCycleGraph.m)
      (W:=ResoplusPDT.ParityClause (Basic.CNF.mk threeCycleGraph.m))
      (ResoplusPDT.cnfSearchRel
        (F:=Basic.CNF.mk threeCycleGraph.m)
        TseitinParityFormulaThreeCycleCharge) where
  size_eq_tree_assumed := True
  derivation_rules_match_model := True
  pdt_extraction_matches_model := True

def fourCycle_transfer_normalization :
    ResoplusPDT.TransferNormalization
      (F:=Basic.CNF.mk fourCycleGraph.m)
      (W:=ResoplusPDT.ParityClause (Basic.CNF.mk fourCycleGraph.m))
      (ResoplusPDT.cnfSearchRel
        (F:=Basic.CNF.mk fourCycleGraph.m)
        TseitinParityFormulaFourCycleCharge) where
  size_eq_tree_assumed := True
  derivation_rules_match_model := True
  pdt_extraction_matches_model := True

noncomputable def threeCycle_normalized_transfer_certified_cnf :
    ResoplusPDT.NormalizedTransferCertifiedCNF (Basic.CNF.mk threeCycleGraph.m) where
  base := threeCycle_transfer_certified_cnf
  normalization := threeCycle_transfer_normalization

noncomputable def fourCycle_normalized_transfer_certified_cnf :
    ResoplusPDT.NormalizedTransferCertifiedCNF (Basic.CNF.mk fourCycleGraph.m) where
  base := fourCycle_transfer_certified_cnf
  normalization := fourCycle_transfer_normalization

noncomputable def threeCycle_transfer_certified_certificate :
    ResoplusPDT.TransferCertifiedCNFCertificate (Basic.CNF.mk threeCycleGraph.m) :=
  ResoplusPDT.transfer_certified_cnf_certificate threeCycle_transfer_certified_cnf

noncomputable def fourCycle_transfer_certified_certificate :
    ResoplusPDT.TransferCertifiedCNFCertificate (Basic.CNF.mk fourCycleGraph.m) :=
  ResoplusPDT.transfer_certified_cnf_certificate fourCycle_transfer_certified_cnf

noncomputable def threeCycle_normalized_transfer_certified_certificate :
    ResoplusPDT.NormalizedTransferCertifiedCNFCertificate (Basic.CNF.mk threeCycleGraph.m) :=
  ResoplusPDT.normalized_transfer_certified_cnf_certificate
    threeCycle_normalized_transfer_certified_cnf

noncomputable def fourCycle_normalized_transfer_certified_certificate :
    ResoplusPDT.NormalizedTransferCertifiedCNFCertificate (Basic.CNF.mk fourCycleGraph.m) :=
  ResoplusPDT.normalized_transfer_certified_cnf_certificate
    fourCycle_normalized_transfer_certified_cnf

noncomputable def threeCycle_transfer_certified_compatibility_certificate :
    ResoplusPDT.TransferCertifiedCompatibilityCertificate (Basic.CNF.mk threeCycleGraph.m) :=
  ResoplusPDT.transfer_certified_compatibility_certificate
    threeCycle_transfer_certified_certificate

noncomputable def fourCycle_transfer_certified_compatibility_certificate :
    ResoplusPDT.TransferCertifiedCompatibilityCertificate (Basic.CNF.mk fourCycleGraph.m) :=
  ResoplusPDT.transfer_certified_compatibility_certificate
    fourCycle_transfer_certified_certificate

noncomputable def threeCycle_normalized_transfer_certified_compatibility_certificate :
    ResoplusPDT.NormalizedTransferCertifiedCompatibilityCertificate
      (Basic.CNF.mk threeCycleGraph.m) :=
  ResoplusPDT.normalized_transfer_certified_compatibility_certificate
    threeCycle_normalized_transfer_certified_certificate

noncomputable def fourCycle_normalized_transfer_certified_compatibility_certificate :
    ResoplusPDT.NormalizedTransferCertifiedCompatibilityCertificate
      (Basic.CNF.mk fourCycleGraph.m) :=
  ResoplusPDT.normalized_transfer_certified_compatibility_certificate
    fourCycle_normalized_transfer_certified_certificate

noncomputable def threeCycle_transfer_certified_compatibility_full_certificate :
    ResoplusPDT.TransferCertifiedCompatibilityFullCertificate
      (Basic.CNF.mk threeCycleGraph.m) :=
  ResoplusPDT.transfer_certified_compatibility_full_certificate
    threeCycle_transfer_certified_compatibility_certificate

noncomputable def fourCycle_transfer_certified_compatibility_full_certificate :
    ResoplusPDT.TransferCertifiedCompatibilityFullCertificate
      (Basic.CNF.mk fourCycleGraph.m) :=
  ResoplusPDT.transfer_certified_compatibility_full_certificate
    fourCycle_transfer_certified_compatibility_certificate

noncomputable def threeCycle_normalized_transfer_certified_compatibility_full_certificate :
    ResoplusPDT.NormalizedTransferCertifiedCompatibilityFullCertificate
      (Basic.CNF.mk threeCycleGraph.m) :=
  ResoplusPDT.normalized_transfer_certified_compatibility_full_certificate
    threeCycle_normalized_transfer_certified_compatibility_certificate

noncomputable def fourCycle_normalized_transfer_certified_compatibility_full_certificate :
    ResoplusPDT.NormalizedTransferCertifiedCompatibilityFullCertificate
      (Basic.CNF.mk fourCycleGraph.m) :=
  ResoplusPDT.normalized_transfer_certified_compatibility_full_certificate
    fourCycle_normalized_transfer_certified_compatibility_certificate

section LiftParityHelpers

variable {F F' : Basic.CNF}
variable (vm : ResoplusPDT.VarMap F F')

def liftParityClause (c : ResoplusPDT.ParityClause F) : ResoplusPDT.ParityClause F' :=
  { vars := ResoplusPDT.mapVars vm c.vars
    rhs := c.rhs }

lemma liftParityClause_xor (c1 c2 : ResoplusPDT.ParityClause F) :
    liftParityClause vm (ResoplusPDT.xorClause c1 c2) =
      ResoplusPDT.xorClause (liftParityClause vm c1) (liftParityClause vm c2) := by
  simp [liftParityClause, ResoplusPDT.xorClause, ResoplusPDT.mapVars, List.map_append]

lemma liftParityClause_dup (c : ResoplusPDT.ParityClause F) (v : Fin F.vcount) :
    liftParityClause vm (ResoplusPDT.dupVarClause c v) =
      ResoplusPDT.dupVarClause (liftParityClause vm c) (vm.map v) := by
  simp [liftParityClause, ResoplusPDT.dupVarClause, ResoplusPDT.mapVars, List.map_append]

lemma liftParityClause_perm (c : ResoplusPDT.ParityClause F)
    (vars' : List (Fin F.vcount)) :
    liftParityClause vm (ResoplusPDT.permuteVarsClause c vars') =
      ResoplusPDT.permuteVarsClause (liftParityClause vm c)
        (ResoplusPDT.mapVars vm vars') := by
  rfl

lemma liftParityClause_vars (c : ResoplusPDT.ParityClause F) :
    (liftParityClause vm c).vars = ResoplusPDT.mapVars vm c.vars := by
  rfl

lemma allLeaves_mapTree (tree : ResoplusPDT.ResoplusDerivTree F)
    (formula : ResoplusPDT.CNFFormula F) :
    ResoplusPDT.ResoplusDerivTree.AllLeaves
      tree (fun c => List.Mem c formula) ->
    ResoplusPDT.ResoplusDerivTree.AllLeaves
      (ResoplusPDT.mapTree' (liftParityClause vm) tree)
      (fun c => List.Mem c (List.map (liftParityClause vm) formula)) := by
  intro h
  revert h
  induction tree with
  | leaf c =>
      intro h
      have hm :
          List.Mem (liftParityClause vm c)
            (List.map (liftParityClause vm) formula) :=
        List.mem_map.2 (Exists.intro c (And.intro h rfl))
      simpa [ResoplusPDT.ResoplusDerivTree.AllLeaves] using hm
  | xor c1 c2 t1 t2 ih1 ih2 =>
      intro h
      cases h with
      | intro h1 h2 =>
          exact And.intro (ih1 h1) (ih2 h2)

def liftParityFormula (formula : ResoplusPDT.CNFFormula F) :
    ResoplusPDT.CNFFormula F' :=
  List.map (liftParityClause vm) formula

def liftParityRefutation
    (formula : ResoplusPDT.CNFFormula F)
    (ref : ResoplusPDT.ResoplusRefutation F formula) :
    ResoplusPDT.ResoplusRefutation F' (liftParityFormula vm formula) := by
  let f := liftParityClause vm
  have hderiv :
      ResoplusPDT.ResoplusDerivesFromTree
        (ResoplusPDT.mapTree' f ref.tree)
        (f (ResoplusPDT.falseClause F)) :=
    ResoplusPDT.derives_mapTree'
      (F:=F) (F':=F') (t:=ref.tree) (c:=ResoplusPDT.falseClause F) f vm
      (by intro c1 c2; simpa using (liftParityClause_xor vm (c1:=c1) (c2:=c2)))
      (by intro c v; simpa using (liftParityClause_dup vm (c:=c) (v:=v)))
      (by intro c vars'; simpa using (liftParityClause_perm vm (c:=c) (vars':=vars')))
      (by intro c vars' hperm; simpa [liftParityClause_vars vm (c:=c)] using hperm)
      (by intro c; simpa using (liftParityClause_vars vm (c:=c)))
      ref.derives_false
  have hleaves :
      ResoplusPDT.ResoplusDerivTree.AllLeaves
        (ResoplusPDT.mapTree' f ref.tree)
        (fun c => List.Mem c (List.map f formula)) := by
    simpa using (allLeaves_mapTree vm ref.tree formula ref.leaves_in)
  have hfalse :
      ResoplusPDT.ResoplusDerivesFromTree
        (ResoplusPDT.mapTree' f ref.tree)
        (f (ResoplusPDT.falseClause F)) := by
    simpa [f, liftParityClause, ResoplusPDT.falseClause] using hderiv
  exact ResoplusPDT.ResoplusRefutation.mk
    (tree := ResoplusPDT.mapTree' f ref.tree)
    (leaves_in := hleaves)
    (derives_false := hfalse)

end LiftParityHelpers


private def threeCycle_base_cnf : Basic.CNF :=
  Basic.CNF.mk threeCycleGraph.m

private def threeCycle_lifted_cnf : Basic.CNF :=
  Basic.Lift threeCycle_base_cnf Basic.IP4

private def threeCycle_varMap :
    ResoplusPDT.VarMap threeCycle_base_cnf threeCycle_lifted_cnf := by
  refine { map := ?_ }
  intro v
  refine (Fin.mk (v.1 * Basic.IP4.b) ?_)
  have hb : 0 < Basic.IP4.b := by decide
  have hv : v.1 < threeCycle_base_cnf.vcount := v.is_lt
  have hlt : v.1 * Basic.IP4.b < threeCycle_base_cnf.vcount * Basic.IP4.b :=
    Nat.mul_lt_mul_of_pos_right hv hb
  simpa [threeCycle_lifted_cnf, Basic.Lift, Nat.mul_comm] using hlt

def threeCycle_lifted_parity_formula :
    ResoplusPDT.CNFFormula threeCycle_lifted_cnf :=
  liftParityFormula threeCycle_varMap TseitinParityFormulaThreeCycleCharge

def threeCycle_lifted_parity_refutation_tree :
    ResoplusPDT.ResoplusRefutation
      threeCycle_lifted_cnf
      threeCycle_lifted_parity_formula :=
  liftParityRefutation threeCycle_varMap
    TseitinParityFormulaThreeCycleCharge
    threeCycle_parity_refutation_tree

private def fourCycle_base_cnf : Basic.CNF :=
  Basic.CNF.mk fourCycleGraph.m

private def fourCycle_lifted_cnf : Basic.CNF :=
  Basic.Lift fourCycle_base_cnf Basic.IP4

private def fourCycle_varMap :
    ResoplusPDT.VarMap fourCycle_base_cnf fourCycle_lifted_cnf := by
  refine { map := ?_ }
  intro v
  refine (Fin.mk (v.1 * Basic.IP4.b) ?_)
  have hb : 0 < Basic.IP4.b := by decide
  have hv : v.1 < fourCycle_base_cnf.vcount := v.is_lt
  have hlt : v.1 * Basic.IP4.b < fourCycle_base_cnf.vcount * Basic.IP4.b :=
    Nat.mul_lt_mul_of_pos_right hv hb
  simpa [fourCycle_lifted_cnf, Basic.Lift, Nat.mul_comm] using hlt

def fourCycle_lifted_parity_formula :
    ResoplusPDT.CNFFormula fourCycle_lifted_cnf :=
  liftParityFormula fourCycle_varMap TseitinParityFormulaFourCycleCharge

def fourCycle_lifted_parity_refutation_tree :
    ResoplusPDT.ResoplusRefutation
      fourCycle_lifted_cnf
      fourCycle_lifted_parity_formula :=
  liftParityRefutation fourCycle_varMap
    TseitinParityFormulaFourCycleCharge
    fourCycle_parity_refutation_tree



/-- Tseitin CNFData built from a mapping into the TseitinModel graph. -/
def TseitinDataFromMapping (G : Basic.Graph) (c : Charge)
    (hm : TseitinModel.Mapping)
    (hme : TseitinModel.m_eq_edges_length (hm.map_graph G)) : CNFData.CNFData :=
  TseitinDataFromModel (hm.map_graph G) hme (hm.map_charge c)

/-- Tseitin CNFData from mapping with `base := Basic.Tseitin G c` and incident clauses. -/
def TseitinDataFromMappingBase (G : Basic.Graph) (c : Charge)
    (hm : TseitinModel.Mapping)
    (hme : TseitinModel.m_eq_edges_length (hm.map_graph G)) : CNFData.CNFData :=
  let Gm := hm.map_graph G
  let hmg : Gm.m = G.m := hm.graph_m_matches G
  let incident : Nat -> List (Fin G.m) :=
    fun v => (incidentIndices Gm hme v).map (fun i => Fin.cast hmg i)
  { base := Basic.Tseitin G c
    clauses := tseitinClausesFromIncident Gm.n G.m incident (hm.map_charge c) }

/-- Optional CNF bundle using mapping-based incident clauses (no default instance). -/
def TseitinBundleFromMapping (G : Basic.Graph) (c : Charge)
    (hm : TseitinModel.Mapping)
    (hme : TseitinModel.m_eq_edges_length (hm.map_graph G)) :
    DecisionTreeSearch.CNFBundle :=
  { data := TseitinDataFromMappingBase G c hm hme }

/-- Provide bundle semantics for the basic Tseitin CNF. -/
instance (G : Basic.Graph) (c : Charge) : DecisionTreeSearch.CNFBundleProvider (Basic.Tseitin G c) where
  bundle := { data := TseitinData G c }
  base_eq := by simp [TseitinData]

/-- Preferred CNF satisfiability for Tseitin via CNFData bundle semantics. -/
def TseitinCNFSatPreferred (G : Basic.Graph) (c : Charge)
    (a : DecisionTreeSearch.Assignment (Basic.Tseitin G c).vcount) : Prop :=
  DecisionTreeSearch.CNFSatPreferred (Basic.Tseitin G c) a

/-- Preferred search correctness for Tseitin via CNFData bundle semantics. -/
def TseitinSearchCorrectPreferred (G : Basic.Graph) (c : Charge)
    (a : DecisionTreeSearch.Assignment (Basic.Tseitin G c).vcount)
    (out : DecisionTreeSearch.SearchOutput) : Prop :=
  DecisionTreeSearch.SearchCorrectPreferred (Basic.Tseitin G c) a out

/-- CNF satisfiability via a mapping-based incident bundle (explicit opt-in). -/
def TseitinCNFSatFromMapping (G : Basic.Graph) (c : Charge)
    (hm : TseitinModel.Mapping)
    (hme : TseitinModel.m_eq_edges_length (hm.map_graph G))
    (a : DecisionTreeSearch.Assignment (Basic.Tseitin G c).vcount) : Prop :=
  let B := TseitinBundleFromMapping G c hm hme
  DecisionTreeSearch.CNFSatBundle B a

/-- Search correctness via a mapping-based incident bundle (explicit opt-in). -/
def TseitinSearchCorrectFromMapping (G : Basic.Graph) (c : Charge)
    (hm : TseitinModel.Mapping)
    (hme : TseitinModel.m_eq_edges_length (hm.map_graph G))
    (a : DecisionTreeSearch.Assignment (Basic.Tseitin G c).vcount)
    (out : DecisionTreeSearch.SearchOutput) : Prop :=
  let B := TseitinBundleFromMapping G c hm hme
  DecisionTreeSearch.SearchCorrectOfBundle B a out

/-- Search relation for mapping-based Tseitin CNF bundle via parity-clause bridge. -/
def TseitinSearchRelFromMapping (G : Basic.Graph) (c : Charge)
    (hm : TseitinModel.Mapping)
    (hme : TseitinModel.m_eq_edges_length (hm.map_graph G)) :
    ResoplusPDT.SearchRel (Basic.Tseitin G c)
      (ResoplusPDT.ParityClause (Basic.Tseitin G c)) :=
  let B := TseitinBundleFromMapping G c hm hme
  CNFModelParityBridge.cnfModelSearchRel B.data.clauses

/-- Search relation for the lifted Tseitin CNF using the mapping-based bundle and IP4 lift. -/
def TseitinLiftedSearchRelFromMapping (G : Basic.Graph) (c : Charge)
    (hm : TseitinModel.Mapping)
    (hme : TseitinModel.m_eq_edges_length (hm.map_graph G)) :
    ResoplusPDT.SearchRel (Basic.Lift (Basic.Tseitin G c) Basic.IP4)
      (ResoplusPDT.ParityClause (Basic.Lift (Basic.Tseitin G c) Basic.IP4)) :=
  let B := TseitinBundleFromMapping G c hm hme
  CNFModelLiftBridge.cnfModelLiftSearchRel (n:=(Basic.Tseitin G c).vcount)
    (b:=Basic.IP4.b) (by decide) B.data.clauses

end TseitinCNFData
end PvNP
