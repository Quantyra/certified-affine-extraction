import Std
import Mathlib.Data.List.Perm.Basic
import CertifiedAffine.BasicDefs

namespace CertifiedAffine
namespace ResoplusPDT

open Basic

abbrev CNF := Basic.CNF

variable {W : Type}

def Assignment (F : CNF) := Fin F.vcount -> Bool

/-- Parity clause over variables of `F`. -/
structure ParityClause (F : CNF) where
  vars : List (Fin F.vcount)
  rhs : Bool

@[ext] theorem ParityClause.ext {F : CNF} {c d : ParityClause F}
    (hvars : c.vars = d.vars) (hrhs : c.rhs = d.rhs) : c = d := by
  cases c
  cases d
  cases hvars
  cases hrhs
  rfl

/-- XOR parity of a list of booleans. -/
def parity (xs : List Bool) : Bool :=
  List.foldl Bool.xor false xs

theorem foldl_xor_acc (b : Bool) (xs : List Bool) :
    List.foldl Bool.xor b xs = Bool.xor b (List.foldl Bool.xor false xs) := by
  induction xs generalizing b with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.foldl]
      have ih1 := ih (b := Bool.xor b x)
      have ih2 := ih (b := x)
      rw [ih1, ih2]
      simp [Bool.xor_assoc]

theorem parity_append (xs ys : List Bool) :
    parity (xs ++ ys) = Bool.xor (parity xs) (parity ys) := by
  unfold parity
  simpa [List.foldl_append] using
    (foldl_xor_acc (b := List.foldl Bool.xor false xs) (xs := ys))

/-- Boolean evaluation of a parity clause. -/
def clauseEval {F : CNF} (a : Assignment F) (c : ParityClause F) : Bool :=
  parity (c.vars.map a) == c.rhs

/-- Clause satisfaction as a Prop. -/
def ClauseSat {F : CNF} (a : Assignment F) (c : ParityClause F) : Prop :=
  clauseEval a c = true

def trueClause (F : CNF) : ParityClause F :=
  ParityClause.mk (F:=F) [] false

def falseClause (F : CNF) : ParityClause F :=
  ParityClause.mk (F:=F) [] true

theorem clauseSat_falseClause {F : CNF} (a : Assignment F) :
    ClauseSat a (falseClause F) = False := by
  simp [ClauseSat, clauseEval, falseClause, parity]

theorem clauseSat_trueClause {F : CNF} (a : Assignment F) :
    ClauseSat a (trueClause F) := by
  simp [ClauseSat, clauseEval, trueClause, parity]

/-! Minimal CNF semantics for parity clauses. -/
def CNFFormula (F : CNF) : Type := List (ParityClause F)

def CNFSat {F : CNF} (a : Assignment F) (phi : CNFFormula F) : Prop :=
  forall c, List.Mem c phi -> ClauseSat a c

def CNFUnsat {F : CNF} (phi : CNFFormula F) : Prop :=
  forall a, Not (CNFSat a phi)

structure SearchRel (F : CNF) (W : Type) where
  holds : Assignment F -> W -> Prop

/-- Standard search relation for parity clauses. -/
abbrev SR_F (F : CNF) : Type := SearchRel F (ParityClause F)

/-!
Canonical search relation: witness is a parity clause satisfied by assignment.
This is a lightweight placeholder; a full CNF search relation can be layered later.
-/
def canonicalSR (F : CNF) : SearchRel F (ParityClause F) :=
  SearchRel.mk (fun a c => ClauseSat a c)

/-!
CNF-scoped search relation: witness is a clause in the formula satisfied
by the assignment. This connects CNF semantics to `SearchRel`.
-/
def cnfSearchRel {F : CNF} (phi : CNFFormula F) : SearchRel F (ParityClause F) :=
  SearchRel.mk (fun a c => List.Mem c phi /\ ClauseSat a c)

def cnfViolationSearchRel {F : CNF} (phi : CNFFormula F) :
    SearchRel F (ParityClause F) :=
  SearchRel.mk (fun a c => List.Mem c phi /\ Not (ClauseSat a c))

theorem cnfSearchRel_holds_of_mem {F : CNF} {phi : CNFFormula F}
    {a : Assignment F} {c : ParityClause F} (hsat : CNFSat a phi) (hmem : List.Mem c phi) :
    (cnfSearchRel phi).holds a c := by
  exact And.intro hmem (hsat c hmem)

theorem cnfViolationSearchRel_holds_of_mem_not_sat {F : CNF}
    {phi : CNFFormula F} {a : Assignment F} {c : ParityClause F}
    (hmem : List.Mem c phi) (hnot : Not (ClauseSat a c)) :
    (cnfViolationSearchRel phi).holds a c := by
  exact And.intro hmem hnot

/-!
Minimal tree-like Res(oplus) derivation tree (placeholder).
This can be used to define a concrete extraction to PDTs.
-/
inductive ResoplusDerivTree (F : CNF) : Type where
  | leaf : ParityClause F -> ResoplusDerivTree F
  | xor : ParityClause F -> ParityClause F ->
      ResoplusDerivTree F -> ResoplusDerivTree F -> ResoplusDerivTree F

def xorClause {F : CNF} (c1 c2 : ParityClause F) : ParityClause F :=
  { vars := c1.vars ++ c2.vars, rhs := Bool.xor c1.rhs c2.rhs }

def permuteVarsClause {F : CNF} (c : ParityClause F) (vars' : List (Fin F.vcount)) :
    ParityClause F :=
  { vars := vars', rhs := c.rhs }

def dupVarClause {F : CNF} (c : ParityClause F) (v : Fin F.vcount) : ParityClause F :=
  { vars := c.vars ++ [v, v], rhs := c.rhs }

instance : RightCommutative Bool.xor := by
  refine ⟨?right_comm⟩
  intro b a1 a2
  cases b <;> cases a1 <;> cases a2 <;> rfl

theorem parity_pair (b : Bool) : parity [b, b] = false := by
  cases b <;> simp [parity, List.foldl]

theorem xorClause_sound {F : CNF} (a : Assignment F) (c1 c2 : ParityClause F) :
    ClauseSat a c1 -> ClauseSat a c2 -> ClauseSat a (xorClause c1 c2) := by
  intro h1 h2
  have h1' : parity (c1.vars.map a) = c1.rhs := by
    simpa [ClauseSat, clauseEval] using h1
  have h2' : parity (c2.vars.map a) = c2.rhs := by
    simpa [ClauseSat, clauseEval] using h2
  simp [ClauseSat, clauseEval, xorClause, List.map_append, parity_append, h1', h2']

theorem dupVarClause_sound {F : CNF} (a : Assignment F) (c : ParityClause F)
    (v : Fin F.vcount) : ClauseSat a c -> ClauseSat a (dupVarClause c v) := by
  intro h
  cases c with
  | mk vars rhs =>
      -- reduce to a concrete boolean equality
      have h' : parity (vars.map a) = rhs := by
        simpa [ClauseSat, clauseEval] using h
      have hpair : parity ([a v, a v]) = false := by
        simp [parity_pair]
      -- parity of appended duplicate pair is unchanged
      simp [ClauseSat, clauseEval, dupVarClause, List.map_append, parity_append,
        h', hpair]

theorem dupVarClause_sound_rev {F : CNF} (a : Assignment F) (c : ParityClause F)
    (v : Fin F.vcount) : ClauseSat a (dupVarClause c v) -> ClauseSat a c := by
  intro h
  cases c with
  | mk vars rhs =>
      have h' : parity ((vars ++ [v, v]).map a) = rhs := by
        simpa [ClauseSat, clauseEval, dupVarClause] using h
      have hpair : parity ([a v, a v]) = false := by
        simp [parity_pair]
      -- remove duplicate pair
      have hpar : parity (vars.map a) = rhs := by
        -- parity(vars ++ [v,v]) = parity(vars) xor parity([v,v]) = parity(vars)
        simpa [List.map_append, parity_append, hpair] using h'
      simpa [ClauseSat, clauseEval] using hpar

theorem clauseSat_perm {F : CNF} (a : Assignment F) (c : ParityClause F)
    (vars' : List (Fin F.vcount)) (hperm : List.Perm c.vars vars') :
    ClauseSat a c -> ClauseSat a (permuteVarsClause c vars') := by
  intro h
  have h' : parity (c.vars.map a) = c.rhs := by
    simpa [ClauseSat, clauseEval] using h
  have hperm' : List.Perm (c.vars.map a) (vars'.map a) := hperm.map _
  have hpar : parity (c.vars.map a) = parity (vars'.map a) := by
    have hfold := (List.Perm.foldl_eq (f:=Bool.xor) (p:=hperm')) false
    simpa [parity] using hfold
  have h'' : parity (vars'.map a) = c.rhs := by
    simpa [hpar] using h'
  simpa [ClauseSat, clauseEval, permuteVarsClause] using h''

def ResoplusDerivTree.size {F : CNF} : ResoplusDerivTree F -> Nat
  | ResoplusDerivTree.leaf _ => 1
  | ResoplusDerivTree.xor _ _ t1 t2 => 1 + ResoplusDerivTree.size t1 + ResoplusDerivTree.size t2

def ResoplusDerivTree.AllLeaves {F : CNF} (t : ResoplusDerivTree F)
    (p : ParityClause F -> Prop) : Prop :=
  match t with
  | ResoplusDerivTree.leaf c => p c
  | ResoplusDerivTree.xor _ _ t1 t2 =>
      And (ResoplusDerivTree.AllLeaves t1 p) (ResoplusDerivTree.AllLeaves t2 p)

theorem allLeaves_mono {F : CNF} {t : ResoplusDerivTree F}
    {p q : ParityClause F -> Prop}
    (himp : forall c, p c -> q c) :
    ResoplusDerivTree.AllLeaves t p ->
    ResoplusDerivTree.AllLeaves t q := by
  intro h
  induction t with
  | leaf c =>
      exact himp c h
  | xor _ _ t1 t2 ih1 ih2 =>
      cases h with
      | intro h1 h2 =>
          exact And.intro (ih1 h1) (ih2 h2)

theorem allLeaves_clauseSat_of_cnfSat {F : CNF} {phi : CNFFormula F}
    {t : ResoplusDerivTree F} {a : Assignment F} :
    ResoplusDerivTree.AllLeaves t (fun c => List.Mem c phi) ->
    CNFSat a phi ->
    ResoplusDerivTree.AllLeaves t (fun c => ClauseSat a c) := by
  intro hleaves hsat
  revert hleaves
  induction t with
  | leaf c =>
      intro hleaves
      simpa using (hsat c hleaves)
  | xor c1 c2 t1 t2 ih1 ih2 =>
      intro hleaves
      cases hleaves with
      | intro h1 h2 =>
          exact And.intro (ih1 h1) (ih2 h2)

inductive ResoplusDerivesFromTree {F : CNF} :
    ResoplusDerivTree F -> ParityClause F -> Prop where
  | leaf {c} : ResoplusDerivesFromTree (ResoplusDerivTree.leaf c) c
  | xor_root {c1 c2 t1 t2} :
      ResoplusDerivesFromTree t1 c1 ->
      ResoplusDerivesFromTree t2 c2 ->
      ResoplusDerivesFromTree (ResoplusDerivTree.xor c1 c2 t1 t2) (xorClause c1 c2)
  | left {c c1 c2 t1 t2} :
      ResoplusDerivesFromTree t1 c ->
      ResoplusDerivesFromTree (ResoplusDerivTree.xor c1 c2 t1 t2) c
  | right {c c1 c2 t1 t2} :
      ResoplusDerivesFromTree t2 c ->
      ResoplusDerivesFromTree (ResoplusDerivTree.xor c1 c2 t1 t2) c
  | dup_var {t c} (v : Fin F.vcount) :
      ResoplusDerivesFromTree t c ->
      ResoplusDerivesFromTree t (dupVarClause c v)
  | dup_var_rev {t c} (v : Fin F.vcount) :
      ResoplusDerivesFromTree t (dupVarClause c v) ->
      ResoplusDerivesFromTree t c
  | permute_vars {t c} (vars' : List (Fin F.vcount)) (hperm : List.Perm c.vars vars') :
      ResoplusDerivesFromTree t c ->
      ResoplusDerivesFromTree t (permuteVarsClause c vars')

def mapTree {F : CNF} (f : ParityClause F -> ParityClause F) :
    ResoplusDerivTree F -> ResoplusDerivTree F
  | ResoplusDerivTree.leaf c => ResoplusDerivTree.leaf (f c)
  | ResoplusDerivTree.xor c1 c2 t1 t2 =>
      ResoplusDerivTree.xor (f c1) (f c2) (mapTree f t1) (mapTree f t2)

def mapTree' {F F' : CNF} (f : ParityClause F -> ParityClause F') :
    ResoplusDerivTree F -> ResoplusDerivTree F'
  | ResoplusDerivTree.leaf c => ResoplusDerivTree.leaf (f c)
  | ResoplusDerivTree.xor c1 c2 t1 t2 =>
      ResoplusDerivTree.xor (f c1) (f c2) (mapTree' f t1) (mapTree' f t2)

theorem mapTree'_size {F F' : CNF} (f : ParityClause F -> ParityClause F')
    (t : ResoplusDerivTree F) :
    ResoplusDerivTree.size (mapTree' f t) = ResoplusDerivTree.size t := by
  induction t with
  | leaf _ =>
      simp [mapTree', ResoplusDerivTree.size]
  | xor _ _ _ _ ih1 ih2 =>
      simp [mapTree', ResoplusDerivTree.size, ih1, ih2]

structure VarMap (F F' : CNF) : Type where
  map : Fin F.vcount -> Fin F'.vcount

def mapVars {F F' : CNF} (vm : VarMap F F') (vars : List (Fin F.vcount)) :
    List (Fin F'.vcount) :=
  vars.map vm.map

theorem derives_mapTree' {F F' : CNF} {t : ResoplusDerivTree F} {c : ParityClause F}
    (f : ParityClause F -> ParityClause F')
    (vm : VarMap F F')
    (hxor : forall c1 c2, f (xorClause c1 c2) = xorClause (f c1) (f c2))
    (hdup : forall c v, f (dupVarClause c v) = dupVarClause (f c) (vm.map v))
    (hperm : forall c vars', f (permuteVarsClause c vars') =
        permuteVarsClause (f c) (mapVars vm vars'))
    (hperm_vars : forall c vars', List.Perm (mapVars vm c.vars) (mapVars vm vars') ->
        List.Perm (f c).vars (mapVars vm vars'))
    (hvars : forall c, (f c).vars = mapVars vm c.vars) :
    ResoplusDerivesFromTree t c ->
    ResoplusDerivesFromTree (mapTree' f t) (f c) := by
  intro h
  induction h with
  | leaf =>
      exact ResoplusDerivesFromTree.leaf
  | xor_root h1 h2 ih1 ih2 =>
      rename_i c1 c2 t1 t2
      have hx :
          ResoplusDerivesFromTree
            (ResoplusDerivTree.xor (f c1) (f c2) (mapTree' f t1) (mapTree' f t2))
            (xorClause (f c1) (f c2)) :=
        ResoplusDerivesFromTree.xor_root ih1 ih2
      simpa [mapTree', hxor] using hx
  | left h ih =>
      rename_i c c1 c2 t1 t2
      simpa [mapTree'] using (ResoplusDerivesFromTree.left ih)
  | right h ih =>
      rename_i c c1 c2 t1 t2
      simpa [mapTree'] using (ResoplusDerivesFromTree.right ih)
  | dup_var v h ih =>
      rename_i t c
      have hx :
          ResoplusDerivesFromTree (mapTree' f t) (dupVarClause (f c) (vm.map v)) :=
        ResoplusDerivesFromTree.dup_var (vm.map v) ih
      simpa [hdup] using hx
  | dup_var_rev v h ih =>
      rename_i t c
      have hx :
          ResoplusDerivesFromTree (mapTree' f t) (dupVarClause (f c) (vm.map v)) := by
        simpa [hdup] using ih
      exact ResoplusDerivesFromTree.dup_var_rev (vm.map v) hx
  | permute_vars vars' hperm0 h ih =>
      rename_i t c
      have hperm' : List.Perm (f c).vars (mapVars vm vars') := by
        have hperm_base : List.Perm (mapVars vm c.vars) (mapVars vm vars') := by
          simpa using List.Perm.map vm.map hperm0
        exact hperm_vars c vars' hperm_base
      have hx :
          ResoplusDerivesFromTree (mapTree' f t) (permuteVarsClause (f c) (mapVars vm vars')) :=
        ResoplusDerivesFromTree.permute_vars (vars':=mapVars vm vars') hperm' ih
      simpa [hperm] using hx

theorem derives_mapTree {F : CNF} {t : ResoplusDerivTree F} {c : ParityClause F}
    (f : ParityClause F -> ParityClause F)
    (hxor : forall c1 c2, f (xorClause c1 c2) = xorClause (f c1) (f c2))
    (hdup : forall c v, f (dupVarClause c v) = dupVarClause (f c) v)
    (hperm : forall c vars', f (permuteVarsClause c vars') = permuteVarsClause (f c) vars')
    (hvars : forall c, (f c).vars = c.vars) :
    ResoplusDerivesFromTree t c ->
    ResoplusDerivesFromTree (mapTree f t) (f c) := by
  intro h
  induction h with
  | leaf =>
      exact ResoplusDerivesFromTree.leaf
  | xor_root h1 h2 ih1 ih2 =>
      rename_i c1 c2 t1 t2
      have hx :
          ResoplusDerivesFromTree
            (ResoplusDerivTree.xor (f c1) (f c2) (mapTree f t1) (mapTree f t2))
            (xorClause (f c1) (f c2)) :=
        ResoplusDerivesFromTree.xor_root ih1 ih2
      simpa [mapTree, hxor] using hx
  | left h ih =>
      rename_i c c1 c2 t1 t2
      simpa [mapTree] using (ResoplusDerivesFromTree.left ih)
  | right h ih =>
      rename_i c c1 c2 t1 t2
      simpa [mapTree] using (ResoplusDerivesFromTree.right ih)
  | dup_var v h ih =>
      rename_i t c
      have hx :
          ResoplusDerivesFromTree (mapTree f t) (dupVarClause (f c) v) :=
        ResoplusDerivesFromTree.dup_var v ih
      simpa [hdup] using hx
  | dup_var_rev v h ih =>
      rename_i t c
      have hx :
          ResoplusDerivesFromTree (mapTree f t) (dupVarClause (f c) v) := by
        simpa [hdup] using ih
      exact ResoplusDerivesFromTree.dup_var_rev v hx
  | permute_vars vars' hperm0 h ih =>
      rename_i t c
      have hperm' : List.Perm (f c).vars vars' := by
        simpa [hvars c] using hperm0
      have hx :
          ResoplusDerivesFromTree (mapTree f t) (permuteVarsClause (f c) vars') :=
        ResoplusDerivesFromTree.permute_vars (vars':=vars') hperm' ih
      simpa [hperm] using hx

structure ResoplusProofTree (F : CNF) (phi : CNFFormula F) : Type where
  tree : ResoplusDerivTree F
  derived : ParityClause F
  derives : ResoplusDerivesFromTree tree derived
  leaves_in : ResoplusDerivTree.AllLeaves tree (fun c => List.Mem c phi)

structure ResoplusRefutation (F : CNF) (phi : CNFFormula F) : Type where
  tree : ResoplusDerivTree F
  leaves_in : ResoplusDerivTree.AllLeaves tree (fun c => List.Mem c phi)
  derives_false : ResoplusDerivesFromTree tree (falseClause F)

structure RefutedCNF (F : CNF) : Type where
  formula : CNFFormula F
  refutation : ResoplusRefutation F formula

structure ResoplusProof (F : CNF) (W : Type) (SR : SearchRel F W) where
  size : Nat
  tree : ResoplusDerivTree F

/--
Canonical proof object for the constructive transfer path: size is determined
by the derivation tree rather than stored as an independent field.
-/
structure CanonicalResoplusProof (F : CNF) (W : Type) (SR : SearchRel F W) where
  tree : ResoplusDerivTree F

def ResoplusProof.ofTree {F : CNF} {W : Type} (SR : SearchRel F W)
    (t : ResoplusDerivTree F) : ResoplusProof F W SR :=
  { size := ResoplusDerivTree.size t
    tree := t }

def CanonicalResoplusProof.toProof {F : CNF} {W : Type} {SR : SearchRel F W}
    (pi : CanonicalResoplusProof F W SR) : ResoplusProof F W SR :=
  ResoplusProof.ofTree SR pi.tree

def CanonicalResoplusSize {F : CNF} {W : Type} {SR : SearchRel F W}
    (pi : CanonicalResoplusProof F W SR) : Nat :=
  ResoplusDerivTree.size pi.tree

def ResoplusProof.size_eq_tree {F : CNF} {W : Type} {SR : SearchRel F W}
    (pi : ResoplusProof F W SR) : Prop :=
  pi.size = ResoplusDerivTree.size pi.tree

theorem ResoplusProof.size_eq_tree_ofTree {F : CNF} {W : Type} {SR : SearchRel F W}
    (t : ResoplusDerivTree F) :
    ResoplusProof.size_eq_tree (F:=F) (W:=W) (SR:=SR) (ResoplusProof.ofTree SR t) := by
  rfl

theorem resoplus_tree_size_le {F : CNF} {W : Type} {SR : SearchRel F W}
    (pi : ResoplusProof F W SR) (h : ResoplusProof.size_eq_tree (F:=F) (W:=W) (SR:=SR) pi) :
    ResoplusDerivTree.size pi.tree <= pi.size := by
  dsimp [ResoplusProof.size_eq_tree] at h
  simp [h]

/-- Tree-structured PDT with parity-clause queries. -/
inductive PDT (F : CNF) (W : Type) where
  | leaf : W -> PDT F W
  | query : ParityClause F -> PDT F W -> PDT F W -> PDT F W

/-- Evaluate a PDT under assignment `a`. -/
def PDT.eval {F : CNF} {W : Type} (t : PDT F W) (a : Assignment F) : W :=
  match t with
  | PDT.leaf w => w
  | PDT.query c tT tF =>
      if clauseEval a c then PDT.eval tT a else PDT.eval tF a

/-- Predicate that evaluation yields a witness. -/
def PDTEval {F : CNF} {W : Type} (t : PDT F W) (a : Assignment F) (w : W) : Prop :=
  PDT.eval t a = w

/--
Strong PDT correctness for a search relation: every assignment is routed to
a witness accepted by the relation. This is stronger than the older
`PDTSoundFor`, which only records that some witness exists somewhere.
-/
def PDTCorrectFor (F : CNF) (SR : SearchRel F W) (t : PDT F W) : Prop :=
  forall a : Assignment F, SR.holds a (PDT.eval t a)

def SearchComplete (F : CNF) (SR : SearchRel F W) : Prop :=
  forall a : Assignment F, Exists fun w => SR.holds a w

theorem searchComplete_cnfViolationSearchRel_of_unsat {F : CNF}
    {phi : CNFFormula F} (hunsat : CNFUnsat phi) :
    SearchComplete F (cnfViolationSearchRel phi) := by
  classical
  intro a
  by_contra hnone
  have hsat : CNFSat a phi := by
    intro c hmem
    by_contra hnot
    exact hnone (Exists.intro c (And.intro hmem hnot))
  exact (hunsat a) hsat

def NoWitnessAtAssignment (F : CNF) (SR : SearchRel F W) : Prop :=
  Exists fun a : Assignment F => forall w : W, Not (SR.holds a w)

def CNFAllClausesFalseAt {F : CNF} (phi : CNFFormula F) (a : Assignment F) : Prop :=
  forall c : ParityClause F, List.Mem c phi -> Not (ClauseSat a c)

def NoUniversalWitness (F : CNF) (SR : SearchRel F W) : Prop :=
  forall w : W, Exists fun a : Assignment F => Not (SR.holds a w)

def NoDepthOneWitness (F : CNF) (SR : SearchRel F W) : Prop :=
  forall q wT wF, Exists fun a : Assignment F =>
    if clauseEval a q then Not (SR.holds a wT) else Not (SR.holds a wF)

def ClauseNonUniversal {F : CNF} (c : ParityClause F) : Prop :=
  Exists fun a : Assignment F => Not (ClauseSat a c)

def ClauseSatisfiable {F : CNF} (c : ParityClause F) : Prop :=
  Exists fun a : Assignment F => ClauseSat a c

def CNFAllClausesNonUniversal {F : CNF} (phi : CNFFormula F) : Prop :=
  forall c : ParityClause F, List.Mem c phi -> ClauseNonUniversal c

def CNFAllClausesSatisfiable {F : CNF} (phi : CNFFormula F) : Prop :=
  forall c : ParityClause F, List.Mem c phi -> ClauseSatisfiable c

def CNFDepthOneAdversary {F : CNF} (phi : CNFFormula F) : Prop :=
  forall q wT wF, Exists fun a : Assignment F =>
    if clauseEval a q then Not (List.Mem wT phi /\ ClauseSat a wT)
    else Not (List.Mem wF phi /\ ClauseSat a wF)

def CNFViolationDepthOneAdversary {F : CNF} (phi : CNFFormula F) : Prop :=
  forall q wT wF, Exists fun a : Assignment F =>
    if clauseEval a q then Not (List.Mem wT phi /\ Not (ClauseSat a wT))
    else Not (List.Mem wF phi /\ Not (ClauseSat a wF))

def CNFPairwiseJointNonUniversal {F : CNF} (phi : CNFFormula F) : Prop :=
  forall c d, List.Mem c phi -> List.Mem d phi ->
    Exists fun a : Assignment F => Not (ClauseSat a c) /\ Not (ClauseSat a d)

def CNFPairwiseJointSatisfiable {F : CNF} (phi : CNFFormula F) : Prop :=
  forall c d, List.Mem c phi -> List.Mem d phi ->
    Exists fun a : Assignment F => ClauseSat a c /\ ClauseSat a d

theorem search_complete_of_pdt_correct_for {F : CNF} {SR : SearchRel F W}
    {t : PDT F W} (h : PDTCorrectFor F SR t) :
    SearchComplete F SR := by
  intro a
  exact Exists.intro (PDT.eval t a) (h a)

theorem not_search_complete_of_no_witness_at_assignment {F : CNF}
    {SR : SearchRel F W} (hdead : NoWitnessAtAssignment F SR) :
    Not (SearchComplete F SR) := by
  intro hcomplete
  rcases hdead with ⟨a, ha⟩
  rcases hcomplete a with ⟨w, hw⟩
  exact ha w hw

theorem noWitnessAtAssignment_cnfSearchRel_of_all_clauses_false_at {F : CNF}
    {phi : CNFFormula F} {a : Assignment F}
    (hfalse : CNFAllClausesFalseAt phi a) :
    NoWitnessAtAssignment F (cnfSearchRel phi) := by
  refine Exists.intro a ?_
  intro w hw
  exact hfalse w hw.1 hw.2

theorem not_search_complete_cnfSearchRel_of_all_clauses_false_at {F : CNF}
    {phi : CNFFormula F} {a : Assignment F}
    (hfalse : CNFAllClausesFalseAt phi a) :
    Not (SearchComplete F (cnfSearchRel phi)) := by
  exact not_search_complete_of_no_witness_at_assignment
    (F:=F) (SR:=cnfSearchRel phi)
    (noWitnessAtAssignment_cnfSearchRel_of_all_clauses_false_at hfalse)

theorem pdt_correct_for_leaf_iff {F : CNF} {SR : SearchRel F W} (w : W) :
    PDTCorrectFor F SR (PDT.leaf w) <->
      forall a : Assignment F, SR.holds a w := by
  rfl

theorem not_pdt_correct_leaf_of_no_universal_witness {F : CNF}
    {SR : SearchRel F W} (hnu : NoUniversalWitness F SR) (w : W) :
    Not (PDTCorrectFor F SR (PDT.leaf w)) := by
  intro hcorrect
  rcases hnu w with ⟨a, ha⟩
  exact ha (hcorrect a)

theorem not_pdt_correct_depth_one_of_no_depth_one_witness {F : CNF}
    {SR : SearchRel F W} (hdepth : NoDepthOneWitness F SR)
    (q : ParityClause F) (wT wF : W) :
    Not (PDTCorrectFor F SR (PDT.query q (PDT.leaf wT) (PDT.leaf wF))) := by
  intro hcorrect
  rcases hdepth q wT wF with ⟨a, ha⟩
  by_cases hq : clauseEval a q = true
  · have hrejected : Not (SR.holds a wT) := by
      simpa [hq] using ha
    have hholds : SR.holds a wT := by
      simpa [PDT.eval, hq] using hcorrect a
    exact hrejected hholds
  · have hqFalse : clauseEval a q = false := Bool.eq_false_iff.mpr hq
    have hrejected : Not (SR.holds a wF) := by
      simpa [hqFalse] using ha
    have hholds : SR.holds a wF := by
      simpa [PDT.eval, hqFalse] using hcorrect a
    exact hrejected hholds

theorem canonical_trueClause_leaf_correct (F : CNF) :
    PDTCorrectFor F (canonicalSR F) (PDT.leaf (trueClause F)) := by
  intro a
  exact clauseSat_trueClause (a := a)

theorem not_noUniversalWitness_canonicalSR (F : CNF) :
    Not (NoUniversalWitness F (canonicalSR F)) := by
  intro h
  rcases h (trueClause F) with ⟨a, ha⟩
  exact ha (clauseSat_trueClause (a := a))

theorem noUniversalWitness_cnfSearchRel_of_all_clauses_nonuniversal {F : CNF}
    {phi : CNFFormula F} (h : CNFAllClausesNonUniversal phi) :
    NoUniversalWitness F (cnfSearchRel phi) := by
  intro w
  by_cases hmem : List.Mem w phi
  · rcases h w hmem with ⟨a, ha⟩
    refine Exists.intro a ?_
    intro hw
    exact ha hw.2
  · refine Exists.intro (fun _ => false : Assignment F) ?_
    intro hw
    exact hmem hw.1

theorem cnfAllClausesSatisfiable_of_pairwise_joint_satisfiable {F : CNF}
    {phi : CNFFormula F} (h : CNFPairwiseJointSatisfiable phi) :
    CNFAllClausesSatisfiable phi := by
  intro c hc
  rcases h c c hc hc with ⟨a, hsat, _⟩
  exact Exists.intro a hsat

theorem noUniversalWitness_cnfViolationSearchRel_of_all_clauses_satisfiable
    {F : CNF} {phi : CNFFormula F} (h : CNFAllClausesSatisfiable phi) :
    NoUniversalWitness F (cnfViolationSearchRel phi) := by
  intro w
  by_cases hmem : List.Mem w phi
  · rcases h w hmem with ⟨a, hsat⟩
    refine Exists.intro a ?_
    intro hw
    exact hw.2 hsat
  · refine Exists.intro (fun _ => false : Assignment F) ?_
    intro hw
    exact hmem hw.1

theorem not_noUniversalWitness_cnfSearchRel_of_trueClause_mem {F : CNF}
    {phi : CNFFormula F} (hmem : List.Mem (trueClause F) phi) :
    Not (NoUniversalWitness F (cnfSearchRel phi)) := by
  intro h
  rcases h (trueClause F) with ⟨a, ha⟩
  exact ha (And.intro hmem (clauseSat_trueClause (a := a)))

theorem falseClause_nonuniversal (F : CNF) :
    ClauseNonUniversal (falseClause F) := by
  refine Exists.intro (fun _ => false : Assignment F) ?_
  intro hsat
  exact (clauseSat_falseClause (a := (fun _ => false : Assignment F)) (F := F)).mp hsat

theorem noUniversalWitness_cnfSearchRel_empty (F : CNF) :
    NoUniversalWitness F (cnfSearchRel (F := F) []) := by
  apply noUniversalWitness_cnfSearchRel_of_all_clauses_nonuniversal
  intro c hmem
  cases hmem

theorem noDepthOneWitness_cnfSearchRel_of_depth_one_adversary {F : CNF}
    {phi : CNFFormula F} (h : CNFDepthOneAdversary phi) :
    NoDepthOneWitness F (cnfSearchRel phi) := by
  intro q wT wF
  exact h q wT wF

theorem noDepthOneWitness_cnfViolationSearchRel_of_depth_one_adversary
    {F : CNF} {phi : CNFFormula F} (h : CNFViolationDepthOneAdversary phi) :
    NoDepthOneWitness F (cnfViolationSearchRel phi) := by
  intro q wT wF
  exact h q wT wF

theorem depthOneAdversary_of_pairwise_joint_nonuniversal {F : CNF}
    {phi : CNFFormula F} (h : CNFPairwiseJointNonUniversal phi) :
    CNFDepthOneAdversary phi := by
  intro q wT wF
  by_cases hT : List.Mem wT phi
  · by_cases hF : List.Mem wF phi
    · rcases h wT wF hT hF with ⟨a, hnotT, hnotF⟩
      refine Exists.intro a ?_
      by_cases hq : clauseEval a q = true
      · have hreject : Not (List.Mem wT phi /\ ClauseSat a wT) := by
          intro hw
          exact hnotT hw.2
        simpa [hq] using hreject
      · have hqFalse : clauseEval a q = false := Bool.eq_false_iff.mpr hq
        have hreject : Not (List.Mem wF phi /\ ClauseSat a wF) := by
          intro hw
          exact hnotF hw.2
        simpa [hqFalse] using hreject
    · rcases h wT wT hT hT with ⟨a, hnotT, _⟩
      refine Exists.intro a ?_
      by_cases hq : clauseEval a q = true
      · have hreject : Not (List.Mem wT phi /\ ClauseSat a wT) := by
          intro hw
          exact hnotT hw.2
        simpa [hq] using hreject
      · have hqFalse : clauseEval a q = false := Bool.eq_false_iff.mpr hq
        have hreject : Not (List.Mem wF phi /\ ClauseSat a wF) := by
          intro hw
          exact hF hw.1
        simpa [hqFalse] using hreject
  · by_cases hF : List.Mem wF phi
    · rcases h wF wF hF hF with ⟨a, hnotF, _⟩
      refine Exists.intro a ?_
      by_cases hq : clauseEval a q = true
      · have hreject : Not (List.Mem wT phi /\ ClauseSat a wT) := by
          intro hw
          exact hT hw.1
        simpa [hq] using hreject
      · have hqFalse : clauseEval a q = false := Bool.eq_false_iff.mpr hq
        have hreject : Not (List.Mem wF phi /\ ClauseSat a wF) := by
          intro hw
          exact hnotF hw.2
        simpa [hqFalse] using hreject
    · refine Exists.intro (fun _ => false : Assignment F) ?_
      by_cases hq : clauseEval (fun _ => false : Assignment F) q = true
      · have hreject : Not (List.Mem wT phi /\ ClauseSat (fun _ => false : Assignment F) wT) := by
          intro hw
          exact hT hw.1
        simpa [hq] using hreject
      · have hqFalse : clauseEval (fun _ => false : Assignment F) q = false :=
          Bool.eq_false_iff.mpr hq
        have hreject : Not (List.Mem wF phi /\ ClauseSat (fun _ => false : Assignment F) wF) := by
          intro hw
          exact hF hw.1
        simpa [hqFalse] using hreject

theorem violationDepthOneAdversary_of_pairwise_joint_satisfiable {F : CNF}
    {phi : CNFFormula F} (h : CNFPairwiseJointSatisfiable phi) :
    CNFViolationDepthOneAdversary phi := by
  intro q wT wF
  by_cases hT : List.Mem wT phi
  · by_cases hF : List.Mem wF phi
    · rcases h wT wF hT hF with ⟨a, hsatT, hsatF⟩
      refine Exists.intro a ?_
      by_cases hq : clauseEval a q = true
      · have hreject : Not (List.Mem wT phi /\ Not (ClauseSat a wT)) := by
          intro hw
          exact hw.2 hsatT
        simpa [hq] using hreject
      · have hqFalse : clauseEval a q = false := Bool.eq_false_iff.mpr hq
        have hreject : Not (List.Mem wF phi /\ Not (ClauseSat a wF)) := by
          intro hw
          exact hw.2 hsatF
        simpa [hqFalse] using hreject
    · rcases h wT wT hT hT with ⟨a, hsatT, _⟩
      refine Exists.intro a ?_
      by_cases hq : clauseEval a q = true
      · have hreject : Not (List.Mem wT phi /\ Not (ClauseSat a wT)) := by
          intro hw
          exact hw.2 hsatT
        simpa [hq] using hreject
      · have hqFalse : clauseEval a q = false := Bool.eq_false_iff.mpr hq
        have hreject : Not (List.Mem wF phi /\ Not (ClauseSat a wF)) := by
          intro hw
          exact hF hw.1
        simpa [hqFalse] using hreject
  · by_cases hF : List.Mem wF phi
    · rcases h wF wF hF hF with ⟨a, hsatF, _⟩
      refine Exists.intro a ?_
      by_cases hq : clauseEval a q = true
      · have hreject : Not (List.Mem wT phi /\ Not (ClauseSat a wT)) := by
          intro hw
          exact hT hw.1
        simpa [hq] using hreject
      · have hqFalse : clauseEval a q = false := Bool.eq_false_iff.mpr hq
        have hreject : Not (List.Mem wF phi /\ Not (ClauseSat a wF)) := by
          intro hw
          exact hw.2 hsatF
        simpa [hqFalse] using hreject
    · refine Exists.intro (fun _ => false : Assignment F) ?_
      by_cases hq : clauseEval (fun _ => false : Assignment F) q = true
      · have hreject :
            Not (List.Mem wT phi /\
              Not (ClauseSat (fun _ => false : Assignment F) wT)) := by
          intro hw
          exact hT hw.1
        simpa [hq] using hreject
      · have hqFalse : clauseEval (fun _ => false : Assignment F) q = false :=
          Bool.eq_false_iff.mpr hq
        have hreject :
            Not (List.Mem wF phi /\
              Not (ClauseSat (fun _ => false : Assignment F) wF)) := by
          intro hw
          exact hF hw.1
        simpa [hqFalse] using hreject

/-- All leaves satisfy a predicate. -/
def PDT.AllLeaves {F : CNF} {W : Type} (t : PDT F W) (p : W -> Prop) : Prop :=
  match t with
  | PDT.leaf w => p w
  | PDT.query _ tT tF => And (PDT.AllLeaves tT p) (PDT.AllLeaves tF p)

structure SRWitness (F : CNF) (SR : SearchRel F W) where
  assignment : Assignment F
  witness : W
  holds : SR.holds assignment witness

abbrev SR_FWitness (F : CNF) (SR : SR_F F) : Type := SRWitness F SR

def ResoplusSize {F} {W : Type} {SR : SearchRel F W} (pi : ResoplusProof F W SR) : Nat :=
  pi.size

def PDTsize {F} {W : Type} (t : PDT F W) : Nat :=
  match t with
  | PDT.leaf _ => 1
  | PDT.query _ tT tF => 1 + PDTsize tT + PDTsize tF

/--
Sequential violated-clause search tree for a nonempty formula represented as
`pre ++ [last]`. It queries prefix clauses in order, returns the first
violated one, and falls through to `last`.
-/
def violationSequentialPDT {F : CNF}
    (pre : List (ParityClause F)) (last : ParityClause F) :
    PDT F (ParityClause F) :=
  match pre with
  | [] => PDT.leaf last
  | c :: rest => PDT.query c (violationSequentialPDT rest last) (PDT.leaf c)

theorem violationSequentialPDT_size {F : CNF}
    (pre : List (ParityClause F)) (last : ParityClause F) :
    PDTsize (violationSequentialPDT pre last) = 2 * pre.length + 1 := by
  induction pre with
  | nil =>
      simp [violationSequentialPDT, PDTsize]
  | cons _ rest ih =>
      simp [violationSequentialPDT, PDTsize, ih]
      omega

theorem violationSequentialPDT_holds_of_not_cnf_sat {F : CNF}
    {pre : List (ParityClause F)} {last : ParityClause F}
    {a : Assignment F} (hnot : Not (CNFSat a (pre ++ [last]))) :
    (cnfViolationSearchRel (pre ++ [last])).holds a
      (PDT.eval (violationSequentialPDT pre last) a) := by
  induction pre with
  | nil =>
      have hnotLast : Not (ClauseSat a last) := by
        intro hlast
        apply hnot
        intro c hmem
        cases hmem with
        | head =>
            simpa using hlast
        | tail _ htail =>
            cases htail
      exact And.intro (by
        change List.Mem last [last]
        exact List.mem_cons_self last []) hnotLast
  | cons c rest ih =>
      by_cases hc : clauseEval a c = true
      · have htail : Not (CNFSat a (rest ++ [last])) := by
          intro hsatTail
          apply hnot
          intro d hmem
          cases hmem with
          | head =>
              simpa [ClauseSat] using hc
          | tail _ htailMem =>
              exact hsatTail d htailMem
        have hrec := ih htail
        have hholds :
            (cnfViolationSearchRel (c :: rest ++ [last])).holds a
              (PDT.eval (violationSequentialPDT rest last) a) := And.intro (by
          exact List.mem_cons_of_mem c hrec.1) hrec.2
        simpa [violationSequentialPDT, PDT.eval, cnfViolationSearchRel, hc] using hholds
      · have hnotC : Not (ClauseSat a c) := by
          intro hsatC
          exact hc (by simpa [ClauseSat] using hsatC)
        have hholds :
            (cnfViolationSearchRel (c :: rest ++ [last])).holds a c :=
          And.intro (List.mem_cons_self c (rest ++ [last])) hnotC
        simpa [violationSequentialPDT, PDT.eval, cnfViolationSearchRel, hc] using hholds

theorem violationSequentialPDT_correct_of_unsat {F : CNF}
    {pre : List (ParityClause F)} {last : ParityClause F}
    (hunsat : CNFUnsat (pre ++ [last])) :
    PDTCorrectFor F
      (cnfViolationSearchRel (pre ++ [last]))
      (violationSequentialPDT pre last) := by
  intro a
  exact violationSequentialPDT_holds_of_not_cnf_sat
    (a:=a) (hnot:=hunsat a)

def NoSmallPDTWitnessBelow (F : CNF) (SR : SearchRel F W) (n : Nat) : Prop :=
  forall t : PDT F W, PDTsize t < n ->
    Exists fun a : Assignment F => Not (SR.holds a (PDT.eval t a))

def CNFSmallPDTAdversaryBelow {F : CNF} (phi : CNFFormula F) (n : Nat) : Prop :=
  NoSmallPDTWitnessBelow F (cnfSearchRel phi) n

def CNFViolationSmallPDTAdversaryBelow {F : CNF} (phi : CNFFormula F) (n : Nat) :
    Prop :=
  NoSmallPDTWitnessBelow F (cnfViolationSearchRel phi) n

theorem noSmallPDTWitnessBelow_of_no_witness_at_assignment {F : CNF}
    {SR : SearchRel F W} {n : Nat}
    (hdead : NoWitnessAtAssignment F SR) :
    NoSmallPDTWitnessBelow F SR n := by
  intro t _hlt
  rcases hdead with ⟨a, ha⟩
  exact Exists.intro a (ha (PDT.eval t a))

theorem cnfSmallPDTAdversaryBelow_of_all_clauses_false_at {F : CNF}
    {phi : CNFFormula F} {a : Assignment F} {n : Nat}
    (hfalse : CNFAllClausesFalseAt phi a) :
    CNFSmallPDTAdversaryBelow phi n := by
  exact noSmallPDTWitnessBelow_of_no_witness_at_assignment
    (F:=F) (SR:=cnfSearchRel phi)
    (noWitnessAtAssignment_cnfSearchRel_of_all_clauses_false_at hfalse)

theorem pdtsize_pos {F : CNF} {W : Type} (t : PDT F W) : 1 <= PDTsize t := by
  induction t with
  | leaf _ =>
      simp [PDTsize]
  | query _ tT tF ihT ihF =>
      simpa [PDTsize, Nat.add_assoc] using Nat.succ_le_succ (Nat.zero_le (PDTsize tT + PDTsize tF))

theorem not_pdt_correct_of_no_small_pdt_witness_below {F : CNF}
    {SR : SearchRel F W} {n : Nat} (hsmall : NoSmallPDTWitnessBelow F SR n)
    {t : PDT F W} (hlt : PDTsize t < n) :
    Not (PDTCorrectFor F SR t) := by
  intro hcorrect
  rcases hsmall t hlt with ⟨a, ha⟩
  exact ha (hcorrect a)

theorem not_noSmallPDTWitnessBelow_of_correct_small_pdt {F : CNF}
    {SR : SearchRel F W} {n : Nat} {t : PDT F W}
    (hlt : PDTsize t < n) (hcorrect : PDTCorrectFor F SR t) :
    Not (NoSmallPDTWitnessBelow F SR n) := by
  intro hsmall
  exact (not_pdt_correct_of_no_small_pdt_witness_below
    (F:=F) (SR:=SR) hsmall hlt) hcorrect

theorem two_le_pdtsize_of_no_universal_witness {F : CNF} {SR : SearchRel F W}
    {t : PDT F W} (hnu : NoUniversalWitness F SR)
    (hcorrect : PDTCorrectFor F SR t) :
    2 <= PDTsize t := by
  cases t with
  | leaf w =>
      exact False.elim ((not_pdt_correct_leaf_of_no_universal_witness
        (F:=F) (SR:=SR) hnu w) hcorrect)
  | query _ tT tF =>
      have hposT : 1 <= PDTsize tT := pdtsize_pos tT
      have htwo : 2 <= 1 + PDTsize tT := by
        simpa [Nat.add_comm] using Nat.succ_le_succ hposT
      have hle : 1 + PDTsize tT <= 1 + PDTsize tT + PDTsize tF :=
        Nat.le_add_right _ _
      simpa [PDTsize, Nat.add_assoc] using le_trans htwo hle

theorem le_pdtsize_of_no_small_pdt_witness_below {F : CNF}
    {SR : SearchRel F W} {n : Nat} {t : PDT F W}
    (hsmall : NoSmallPDTWitnessBelow F SR n)
    (hcorrect : PDTCorrectFor F SR t) :
    n <= PDTsize t := by
  by_cases hlt : PDTsize t < n
  · exact False.elim
      ((not_pdt_correct_of_no_small_pdt_witness_below
        (F:=F) (SR:=SR) hsmall hlt) hcorrect)
  · exact Nat.le_of_not_lt hlt

theorem le_pdtsize_cnfSearchRel_of_small_pdt_adversary_below
    {F : CNF} {phi : CNFFormula F} {n : Nat}
    {t : PDT F (ParityClause F)}
    (hsmall : CNFSmallPDTAdversaryBelow phi n)
    (hcorrect : PDTCorrectFor F (cnfSearchRel phi) t) :
    n <= PDTsize t := by
  exact le_pdtsize_of_no_small_pdt_witness_below
    (F:=F) (SR:=cnfSearchRel phi) hsmall hcorrect

theorem le_pdtsize_cnfViolationSearchRel_of_small_pdt_adversary_below
    {F : CNF} {phi : CNFFormula F} {n : Nat}
    {t : PDT F (ParityClause F)}
    (hsmall : CNFViolationSmallPDTAdversaryBelow phi n)
    (hcorrect : PDTCorrectFor F (cnfViolationSearchRel phi) t) :
    n <= PDTsize t := by
  exact le_pdtsize_of_no_small_pdt_witness_below
    (F:=F) (SR:=cnfViolationSearchRel phi) hsmall hcorrect

theorem not_cnfViolationSmallPDTAdversaryBelow_of_unsat_sequential_size_lt
    {F : CNF} {pre : List (ParityClause F)} {last : ParityClause F} {n : Nat}
    (hunsat : CNFUnsat (pre ++ [last]))
    (hlt : 2 * pre.length + 1 < n) :
    Not (CNFViolationSmallPDTAdversaryBelow (pre ++ [last]) n) := by
  exact not_noSmallPDTWitnessBelow_of_correct_small_pdt
    (F:=F)
    (SR:=cnfViolationSearchRel (pre ++ [last]))
    (n:=n)
    (t:=violationSequentialPDT pre last)
    (by simpa [violationSequentialPDT_size] using hlt)
    (violationSequentialPDT_correct_of_unsat hunsat)

/--
Any valid repaired violation-search bounded-small-PDT threshold for an
unsatisfiable nonempty formula must sit at or below the sequential
clause-checking upper bound.
-/
theorem le_sequential_size_of_cnfViolationSmallPDTAdversaryBelow_unsat
    {F : CNF} {pre : List (ParityClause F)} {last : ParityClause F} {n : Nat}
    (hunsat : CNFUnsat (pre ++ [last]))
    (hsmall : CNFViolationSmallPDTAdversaryBelow (pre ++ [last]) n) :
    n <= 2 * pre.length + 1 := by
  by_contra hnot
  have hlt : 2 * pre.length + 1 < n := Nat.lt_of_not_ge hnot
  exact (not_cnfViolationSmallPDTAdversaryBelow_of_unsat_sequential_size_lt
    (F:=F) (pre:=pre) (last:=last) (n:=n) hunsat hlt) hsmall

theorem three_le_pdtsize_query {F : CNF} {W : Type}
    (q : ParityClause F) (tT tF : PDT F W) :
    3 <= PDTsize (PDT.query q tT tF) := by
  have hT : 1 <= PDTsize tT := pdtsize_pos tT
  have hF : 1 <= PDTsize tF := pdtsize_pos tF
  have htwo : 2 <= 1 + PDTsize tT := by
    simpa [Nat.add_comm] using Nat.succ_le_succ hT
  have hthree : 3 <= 1 + PDTsize tT + PDTsize tF := by
    have h := Nat.add_le_add htwo hF
    simpa [Nat.add_assoc] using h
  simpa [PDTsize, Nat.add_assoc] using hthree

theorem four_le_pdtsize_query_of_three_le_left {F : CNF} {W : Type}
    (q : ParityClause F) (tT tF : PDT F W) (hT : 3 <= PDTsize tT) :
    4 <= PDTsize (PDT.query q tT tF) := by
  have hroot : 4 <= 1 + PDTsize tT := by
    simpa [Nat.add_comm] using Nat.succ_le_succ hT
  have hle : 1 + PDTsize tT <= 1 + PDTsize tT + PDTsize tF :=
    Nat.le_add_right _ _
  simpa [PDTsize, Nat.add_assoc] using le_trans hroot hle

theorem four_le_pdtsize_query_of_three_le_right {F : CNF} {W : Type}
    (q : ParityClause F) (tT tF : PDT F W) (hF : 3 <= PDTsize tF) :
    4 <= PDTsize (PDT.query q tT tF) := by
  have hroot : 4 <= 1 + PDTsize tF := by
    simpa [Nat.add_comm] using Nat.succ_le_succ hF
  have hle : 1 + PDTsize tF <= 1 + PDTsize tT + PDTsize tF := by
    exact Nat.add_le_add_right (Nat.le_add_right 1 (PDTsize tT)) (PDTsize tF)
  simpa [PDTsize, Nat.add_assoc] using le_trans hroot hle

theorem four_le_pdtsize_of_no_universal_and_no_depth_one {F : CNF}
    {SR : SearchRel F W} {t : PDT F W}
    (hnu : NoUniversalWitness F SR) (hdepth : NoDepthOneWitness F SR)
    (hcorrect : PDTCorrectFor F SR t) :
    4 <= PDTsize t := by
  cases t with
  | leaf w =>
      exact False.elim ((not_pdt_correct_leaf_of_no_universal_witness
        (F:=F) (SR:=SR) hnu w) hcorrect)
  | query q tT tF =>
      cases tT with
      | leaf wT =>
          cases tF with
          | leaf wF =>
              exact False.elim ((not_pdt_correct_depth_one_of_no_depth_one_witness
                (F:=F) (SR:=SR) hdepth q wT wF) hcorrect)
          | query qF tFT tFF =>
              exact four_le_pdtsize_query_of_three_le_right
                q (PDT.leaf wT) (PDT.query qF tFT tFF)
                (three_le_pdtsize_query qF tFT tFF)
      | query qT tTT tTF =>
          exact four_le_pdtsize_query_of_three_le_left
            q (PDT.query qT tTT tTF) tF
            (three_le_pdtsize_query qT tTT tTF)

theorem four_le_pdtsize_cnfSearchRel_of_all_clauses_nonuniversal_and_depth_one
    {F : CNF} {phi : CNFFormula F}
    {t : PDT F (ParityClause F)}
    (hnu : CNFAllClausesNonUniversal phi)
    (hdepth : CNFDepthOneAdversary phi)
    (hcorrect : PDTCorrectFor F (cnfSearchRel phi) t) :
    4 <= PDTsize t := by
  exact four_le_pdtsize_of_no_universal_and_no_depth_one
    (F:=F) (SR:=cnfSearchRel phi)
    (noUniversalWitness_cnfSearchRel_of_all_clauses_nonuniversal hnu)
    (noDepthOneWitness_cnfSearchRel_of_depth_one_adversary hdepth)
    hcorrect

theorem four_le_pdtsize_cnfViolationSearchRel_of_all_clauses_satisfiable_and_depth_one
    {F : CNF} {phi : CNFFormula F}
    {t : PDT F (ParityClause F)}
    (hnu : CNFAllClausesSatisfiable phi)
    (hdepth : CNFViolationDepthOneAdversary phi)
    (hcorrect : PDTCorrectFor F (cnfViolationSearchRel phi) t) :
    4 <= PDTsize t := by
  exact four_le_pdtsize_of_no_universal_and_no_depth_one
    (F:=F) (SR:=cnfViolationSearchRel phi)
    (noUniversalWitness_cnfViolationSearchRel_of_all_clauses_satisfiable hnu)
    (noDepthOneWitness_cnfViolationSearchRel_of_depth_one_adversary hdepth)
    hcorrect

/-!
Res(oplus) derivations are not formalized yet. We keep the derivation relation
axiomatic and only state its intended soundness against parity-clause semantics.
-/
def ResoplusDerives {F} {W : Type} {SR : SearchRel F W}
    (pi : ResoplusProof F W SR) (c : ParityClause F) : Prop :=
  ResoplusDerivesFromTree pi.tree c

theorem mem_cons_of_mem {α} {a b : α} {l : List α} : List.Mem a l -> List.Mem a (b :: l) := by
  intro h
  exact List.mem_cons_of_mem b h

theorem mem_cons_self' {α} (a : α) (l : List α) : List.Mem a (a :: l) := by
  exact List.mem_cons_self a l

-- Helper to chain xor_root derivations with minimal boilerplate.
def xorTree {F : CNF} (c1 c2 : ParityClause F)
    (t1 t2 : ResoplusDerivTree F) : ResoplusDerivTree F :=
  ResoplusDerivTree.xor c1 c2 t1 t2

theorem derives_xor_root {F : CNF} {c1 c2 : ParityClause F} {t1 t2 : ResoplusDerivTree F} :
    ResoplusDerivesFromTree t1 c1 ->
    ResoplusDerivesFromTree t2 c2 ->
    ResoplusDerivesFromTree (xorTree c1 c2 t1 t2) (xorClause c1 c2) := by
  intro h1 h2
  exact ResoplusDerivesFromTree.xor_root h1 h2

/-!
Tree merge: combine two derivation subtrees under xor.
This is a lightweight operator for assembling larger derivations from pieces.
-/
def mergeTree {F : CNF} (t1 t2 : ResoplusDerivTree F)
    (c1 c2 : ParityClause F) : ResoplusDerivTree F :=
  ResoplusDerivTree.xor c1 c2 t1 t2

theorem derives_mergeTree {F : CNF} {t1 t2 : ResoplusDerivTree F}
    {c1 c2 : ParityClause F} :
    ResoplusDerivesFromTree t1 c1 ->
    ResoplusDerivesFromTree t2 c2 ->
    ResoplusDerivesFromTree (mergeTree t1 t2 c1 c2) (xorClause c1 c2) := by
  intro h1 h2
  exact ResoplusDerivesFromTree.xor_root h1 h2

theorem derives_mergeTree_left {F : CNF} {t1 t2 : ResoplusDerivTree F}
    {c c1 c2 : ParityClause F} :
    ResoplusDerivesFromTree t1 c ->
    ResoplusDerivesFromTree (mergeTree t1 t2 c1 c2) c := by
  intro h
  exact ResoplusDerivesFromTree.left h

theorem derives_mergeTree_right {F : CNF} {t1 t2 : ResoplusDerivTree F}
    {c c1 c2 : ParityClause F} :
    ResoplusDerivesFromTree t2 c ->
    ResoplusDerivesFromTree (mergeTree t1 t2 c1 c2) c := by
  intro h
  exact ResoplusDerivesFromTree.right h

-- Duplicate-variable helper (list fold).
def dupVarClauseList {F : CNF} (c : ParityClause F) (vs : List (Fin F.vcount)) :
    ParityClause F :=
  vs.foldl (fun acc v => dupVarClause acc v) c

theorem dupVarClauseList_vars {F : CNF} (c : ParityClause F) (vs : List (Fin F.vcount)) :
    (dupVarClauseList c vs).vars = c.vars ++ vs.bind (fun v => [v, v]) := by
  induction vs generalizing c with
  | nil =>
      simp [dupVarClauseList]
  | cons v vs ih =>
      have ih' := ih (c := dupVarClause c v)
      simpa [dupVarClauseList, dupVarClause, List.append_assoc] using ih'

theorem dupVarClauseList_rhs {F : CNF} (c : ParityClause F) (vs : List (Fin F.vcount)) :
    (dupVarClauseList c vs).rhs = c.rhs := by
  induction vs generalizing c with
  | nil =>
      simp [dupVarClauseList]
  | cons v vs ih =>
      simpa [dupVarClauseList, dupVarClause] using (ih (c := dupVarClause c v))

theorem derives_dup_list {F : CNF} {t : ResoplusDerivTree F} {c : ParityClause F}
    (vs : List (Fin F.vcount)) :
    ResoplusDerivesFromTree t c ->
    ResoplusDerivesFromTree t (dupVarClauseList c vs) := by
  intro h
  induction vs generalizing c with
  | nil =>
      simpa [dupVarClauseList]
  | cons v vs ih =>
      have h' : ResoplusDerivesFromTree t (dupVarClause c v) :=
        ResoplusDerivesFromTree.dup_var v h
      simpa [dupVarClauseList] using (ih (c:=dupVarClause c v) h')

theorem derives_dup_list_rev {F : CNF} {t : ResoplusDerivTree F} {c : ParityClause F}
    (vs : List (Fin F.vcount)) :
    ResoplusDerivesFromTree t (dupVarClauseList c vs) ->
    ResoplusDerivesFromTree t c := by
  intro h
  induction vs generalizing c with
  | nil =>
      simpa [dupVarClauseList] using h
  | cons v vs ih =>
      -- peel one duplicate via foldl structure
      have h' : ResoplusDerivesFromTree t (dupVarClauseList (dupVarClause c v) vs) := by
        simpa [dupVarClauseList] using h
      have h'' : ResoplusDerivesFromTree t (dupVarClause c v) :=
        ih (c:=dupVarClause c v) h'
      exact ResoplusDerivesFromTree.dup_var_rev v h''

def xorTree3 {F : CNF} (c0 c1 c2 : ParityClause F) : ResoplusDerivTree F :=
  xorTree c0 (xorClause c1 c2)
    (ResoplusDerivTree.leaf c0)
    (xorTree c1 c2 (ResoplusDerivTree.leaf c1) (ResoplusDerivTree.leaf c2))

def xorTree4 {F : CNF} (c0 c1 c2 c3 : ParityClause F) : ResoplusDerivTree F :=
  xorTree c0 (xorClause c1 (xorClause c2 c3))
    (ResoplusDerivTree.leaf c0)
    (xorTree c1 (xorClause c2 c3)
      (ResoplusDerivTree.leaf c1)
      (xorTree c2 c3 (ResoplusDerivTree.leaf c2) (ResoplusDerivTree.leaf c3)))

theorem xorTree3_size {F : CNF} (c0 c1 c2 : ParityClause F) :
    ResoplusDerivTree.size (xorTree3 c0 c1 c2) = 5 := by
  simp [xorTree3, xorTree, ResoplusDerivTree.size]

theorem xorTree4_size {F : CNF} (c0 c1 c2 c3 : ParityClause F) :
    ResoplusDerivTree.size (xorTree4 c0 c1 c2 c3) = 7 := by
  simp [xorTree4, xorTree, ResoplusDerivTree.size]

theorem derives_false_of_three_parity
    {F : CNF} (c0 c1 c2 : ParityClause F) (vs : List (Fin F.vcount))
    (hperm :
      List.Perm (c0.vars ++ c1.vars ++ c2.vars)
        (dupVarClauseList (falseClause F) vs).vars)
    (hrhs : Bool.xor c0.rhs (Bool.xor c1.rhs c2.rhs) = true) :
    ResoplusDerivesFromTree (xorTree3 c0 c1 c2) (falseClause F) := by
  let c12 : ParityClause F := xorClause c1 c2
  let c012 : ParityClause F := xorClause c0 c12
  have h1 : ResoplusDerivesFromTree (ResoplusDerivTree.leaf c0) c0 :=
    ResoplusDerivesFromTree.leaf
  have h2 : ResoplusDerivesFromTree (ResoplusDerivTree.leaf c1) c1 :=
    ResoplusDerivesFromTree.leaf
  have h3 : ResoplusDerivesFromTree (ResoplusDerivTree.leaf c2) c2 :=
    ResoplusDerivesFromTree.leaf
  have h12 : ResoplusDerivesFromTree (xorTree c1 c2 (ResoplusDerivTree.leaf c1)
      (ResoplusDerivTree.leaf c2)) c12 :=
    derives_xor_root h2 h3
  have h012 : ResoplusDerivesFromTree (xorTree3 c0 c1 c2) c012 :=
    derives_xor_root h1 h12
  have hperm' : List.Perm c012.vars (dupVarClauseList (falseClause F) vs).vars := by
    simpa [c012, c12, xorClause, List.append_assoc] using hperm
  have hpermDer : ResoplusDerivesFromTree (xorTree3 c0 c1 c2)
      (permuteVarsClause c012 (dupVarClauseList (falseClause F) vs).vars) :=
    ResoplusDerivesFromTree.permute_vars (vars' := (dupVarClauseList (falseClause F) vs).vars)
      hperm' h012
  have h_eq :
      permuteVarsClause c012 (dupVarClauseList (falseClause F) vs).vars =
        dupVarClauseList (falseClause F) vs := by
    ext <;> simp [permuteVarsClause, dupVarClauseList_rhs, falseClause,
      c012, c12, xorClause, hrhs]
  have hdup : ResoplusDerivesFromTree (xorTree3 c0 c1 c2)
      (dupVarClauseList (falseClause F) vs) := by
    simpa [h_eq] using hpermDer
  exact derives_dup_list_rev (t:=xorTree3 c0 c1 c2) (c:=falseClause F) (vs:=vs) hdup

theorem derives_false_of_four_parity
    {F : CNF} (c0 c1 c2 c3 : ParityClause F) (vs : List (Fin F.vcount))
    (hperm :
      List.Perm (c0.vars ++ c1.vars ++ c2.vars ++ c3.vars)
        (dupVarClauseList (falseClause F) vs).vars)
    (hrhs : Bool.xor c0.rhs (Bool.xor c1.rhs (Bool.xor c2.rhs c3.rhs)) = true) :
    ResoplusDerivesFromTree (xorTree4 c0 c1 c2 c3) (falseClause F) := by
  let c23 : ParityClause F := xorClause c2 c3
  let c123 : ParityClause F := xorClause c1 c23
  let c0123 : ParityClause F := xorClause c0 c123
  have h1 : ResoplusDerivesFromTree (ResoplusDerivTree.leaf c0) c0 :=
    ResoplusDerivesFromTree.leaf
  have h2 : ResoplusDerivesFromTree (ResoplusDerivTree.leaf c1) c1 :=
    ResoplusDerivesFromTree.leaf
  have h3 : ResoplusDerivesFromTree (ResoplusDerivTree.leaf c2) c2 :=
    ResoplusDerivesFromTree.leaf
  have h4 : ResoplusDerivesFromTree (ResoplusDerivTree.leaf c3) c3 :=
    ResoplusDerivesFromTree.leaf
  have h23 : ResoplusDerivesFromTree
      (xorTree c2 c3 (ResoplusDerivTree.leaf c2) (ResoplusDerivTree.leaf c3)) c23 :=
    derives_xor_root h3 h4
  have h123 : ResoplusDerivesFromTree
      (xorTree c1 c23 (ResoplusDerivTree.leaf c1)
        (xorTree c2 c3 (ResoplusDerivTree.leaf c2) (ResoplusDerivTree.leaf c3))) c123 :=
    derives_xor_root h2 h23
  have h0123 : ResoplusDerivesFromTree (xorTree4 c0 c1 c2 c3) c0123 :=
    derives_xor_root h1 h123
  have hperm' : List.Perm c0123.vars (dupVarClauseList (falseClause F) vs).vars := by
    simpa [c0123, c123, c23, xorClause, List.append_assoc] using hperm
  have hpermDer : ResoplusDerivesFromTree (xorTree4 c0 c1 c2 c3)
      (permuteVarsClause c0123 (dupVarClauseList (falseClause F) vs).vars) :=
    ResoplusDerivesFromTree.permute_vars (vars':=(dupVarClauseList (falseClause F) vs).vars)
      hperm' h0123
  have h_eq :
      permuteVarsClause c0123 (dupVarClauseList (falseClause F) vs).vars =
        dupVarClauseList (falseClause F) vs := by
    ext <;> simp [permuteVarsClause, dupVarClauseList_rhs, falseClause,
      c0123, c123, c23, xorClause, hrhs]
  have hdup : ResoplusDerivesFromTree (xorTree4 c0 c1 c2 c3)
      (dupVarClauseList (falseClause F) vs) := by
    simpa [h_eq] using hpermDer
  exact derives_dup_list_rev (t:=xorTree4 c0 c1 c2 c3) (c:=falseClause F) (vs:=vs) hdup

-- Folded XOR over a list of clauses.
def xorClauseList {F : CNF} : List (ParityClause F) -> ParityClause F
  | [] => trueClause F
  | c :: cs => xorClause c (xorClauseList cs)

-- Folded XOR over a nonempty list, preserving the singleton clause exactly.
def xorClauseFold {F : CNF} (c : ParityClause F) :
    List (ParityClause F) -> ParityClause F
  | [] => c
  | d :: ds => xorClause c (xorClauseFold d ds)

def xorTreeFold {F : CNF} (c : ParityClause F) :
    List (ParityClause F) -> ResoplusDerivTree F
  | [] => ResoplusDerivTree.leaf c
  | d :: ds =>
      xorTree c (xorClauseFold d ds)
        (ResoplusDerivTree.leaf c)
        (xorTreeFold d ds)

theorem xorClauseFold_vars {F : CNF} (c : ParityClause F)
    (cs : List (ParityClause F)) :
    (xorClauseFold c cs).vars = c.vars ++ cs.bind (fun d => d.vars) := by
  induction cs generalizing c with
  | nil =>
      simp [xorClauseFold]
  | cons d ds ih =>
      simpa [xorClauseFold, xorClause, ih, List.append_assoc]

theorem derives_xorTreeFold {F : CNF} (c : ParityClause F)
    (cs : List (ParityClause F)) :
    ResoplusDerivesFromTree (xorTreeFold c cs) (xorClauseFold c cs) := by
  induction cs generalizing c with
  | nil =>
      simpa [xorTreeFold, xorClauseFold] using
        (ResoplusDerivesFromTree.leaf (c:=c))
  | cons d ds ih =>
      have hleft :
          ResoplusDerivesFromTree (ResoplusDerivTree.leaf c) c :=
        ResoplusDerivesFromTree.leaf
      have hright :
          ResoplusDerivesFromTree (xorTreeFold d ds) (xorClauseFold d ds) :=
        ih d
      simpa [xorTreeFold, xorClauseFold] using
        (derives_xor_root hleft hright)

theorem xorTreeFold_size {F : CNF} (c : ParityClause F)
    (cs : List (ParityClause F)) :
    ResoplusDerivTree.size (xorTreeFold c cs) = 2 * cs.length + 1 := by
  induction cs generalizing c with
  | nil =>
      simp [xorTreeFold, ResoplusDerivTree.size]
  | cons d ds ih =>
      simp [xorTreeFold, xorTree, ResoplusDerivTree.size, ih,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add]

theorem xorTreeFold_allLeaves_mem {F : CNF} (c : ParityClause F)
    (cs : List (ParityClause F)) :
    ResoplusDerivTree.AllLeaves (xorTreeFold c cs)
      (fun d => List.Mem d (c :: cs)) := by
  induction cs generalizing c with
  | nil =>
      change List.Mem c [c]
      exact List.mem_cons_self c []
  | cons d ds ih =>
      have hright :
          ResoplusDerivTree.AllLeaves (xorTreeFold d ds)
            (fun e => List.Mem e (d :: ds)) :=
        ih d
      have hright' :
          ResoplusDerivTree.AllLeaves (xorTreeFold d ds)
            (fun e => List.Mem e (c :: d :: ds)) :=
        allLeaves_mono
          (t:=xorTreeFold d ds)
          (p:=fun e => List.Mem e (d :: ds))
          (q:=fun e => List.Mem e (c :: d :: ds))
          (fun e he => List.mem_cons_of_mem c he)
          hright
      change List.Mem c (c :: d :: ds) ∧
        ResoplusDerivTree.AllLeaves (xorTreeFold d ds)
          (fun e => List.Mem e (c :: d :: ds))
      exact And.intro (List.mem_cons_self c (d :: ds)) hright'

theorem derives_false_of_parity_clause_fold
    {F : CNF} (c : ParityClause F) (cs : List (ParityClause F))
    (vs : List (Fin F.vcount))
    (hperm :
      List.Perm (xorClauseFold c cs).vars
        (dupVarClauseList (falseClause F) vs).vars)
    (hrhs : (xorClauseFold c cs).rhs = true) :
    ResoplusDerivesFromTree (xorTreeFold c cs) (falseClause F) := by
  have hfold : ResoplusDerivesFromTree (xorTreeFold c cs) (xorClauseFold c cs) :=
    derives_xorTreeFold c cs
  have hpermDer : ResoplusDerivesFromTree (xorTreeFold c cs)
      (permuteVarsClause (xorClauseFold c cs)
        (dupVarClauseList (falseClause F) vs).vars) :=
    ResoplusDerivesFromTree.permute_vars
      (vars' := (dupVarClauseList (falseClause F) vs).vars) hperm hfold
  have h_eq :
      permuteVarsClause (xorClauseFold c cs)
          (dupVarClauseList (falseClause F) vs).vars =
        dupVarClauseList (falseClause F) vs := by
    ext <;> simp [permuteVarsClause, dupVarClauseList_rhs, falseClause, hrhs]
  have hdup : ResoplusDerivesFromTree (xorTreeFold c cs)
      (dupVarClauseList (falseClause F) vs) := by
    simpa [h_eq] using hpermDer
  exact derives_dup_list_rev (t:=xorTreeFold c cs) (c:=falseClause F) (vs:=vs) hdup

def parityClauseFoldRefutation
    {F : CNF} (c : ParityClause F) (cs : List (ParityClause F))
    (vs : List (Fin F.vcount))
    (hperm :
      List.Perm (xorClauseFold c cs).vars
        (dupVarClauseList (falseClause F) vs).vars)
    (hrhs : (xorClauseFold c cs).rhs = true) :
    ResoplusRefutation F (c :: cs) :=
  { tree := xorTreeFold c cs
    leaves_in := xorTreeFold_allLeaves_mem c cs
    derives_false := derives_false_of_parity_clause_fold c cs vs hperm hrhs
  }


def ResoplusSound (F : CNF) (SR : SearchRel F W) : Prop :=
  Exists fun pi =>
    Exists fun c =>
      ResoplusDerives (F:=F) (SR:=SR) pi c -> Exists fun a => ClauseSat a c

theorem resoplus_derives_sound_of_all_leaves
    {F : CNF} {t : ResoplusDerivTree F}
    {a : Assignment F} {c : ParityClause F}
    (h : ResoplusDerivTree.AllLeaves t (fun d => ClauseSat a d))
    (hd : ResoplusDerivesFromTree t c) : ClauseSat a c := by
  induction hd with
  | leaf =>
      simp [ResoplusDerivTree.AllLeaves] at h
      simpa using h
  | xor_root _h1 _h2 ih1 ih2 =>
      cases h with
      | intro ha hb =>
          exact xorClause_sound a _ _ (ih1 ha) (ih2 hb)
  | left _hsub ih =>
      cases h with
      | intro h1 _h2 =>
          exact ih h1
  | right _hsub ih =>
      cases h with
      | intro _h1 h2 =>
          exact ih h2
  | dup_var v _hsub ih =>
      exact dupVarClause_sound a _ v (ih h)
  | permute_vars vars' hperm _hsub ih =>
      exact clauseSat_perm a _ vars' hperm (ih h)
  | dup_var_rev v _hsub ih =>
      exact dupVarClause_sound_rev a _ v (ih h)

theorem resoplus_proof_tree_sound {F : CNF} {phi : CNFFormula F}
    (pt : ResoplusProofTree F phi) {a : Assignment F} :
    CNFSat a phi -> ClauseSat a pt.derived := by
  intro hsat
  have hleaves : ResoplusDerivTree.AllLeaves pt.tree (fun d => ClauseSat a d) :=
    allLeaves_clauseSat_of_cnfSat (t:=pt.tree) (a:=a) pt.leaves_in hsat
  exact resoplus_derives_sound_of_all_leaves hleaves pt.derives

theorem resoplus_refutation_unsat {F : CNF} {phi : CNFFormula F}
    (r : ResoplusRefutation F phi) : CNFUnsat phi := by
  intro a hsat
  have hleaves : ResoplusDerivTree.AllLeaves r.tree (fun d => ClauseSat a d) :=
    allLeaves_clauseSat_of_cnfSat (t:=r.tree) (a:=a) r.leaves_in hsat
  have hfalse : ClauseSat a (falseClause F) :=
    resoplus_derives_sound_of_all_leaves hleaves r.derives_false
  have hcontra : False := by
    have hfalse' : ClauseSat a (falseClause F) := hfalse
    have eq : ClauseSat a (falseClause F) = False :=
      clauseSat_falseClause (a:=a) (F:=F)
    exact eq.mp hfalse'
  exact hcontra

/-!
Tiny unsat CNF and refutation: `phi = [falseClause]`.
This provides a concrete, sound derivation tree instance for wiring validation.
-/
def tinyUnsatCNF (F : CNF) : CNFFormula F := [falseClause F]

def tinyUnsatRefutation (F : CNF) : ResoplusRefutation F (tinyUnsatCNF F) :=
  { tree := ResoplusDerivTree.leaf (falseClause F)
    leaves_in := by
      -- AllLeaves for leaf reduces to membership.
      dsimp [ResoplusDerivTree.AllLeaves, tinyUnsatCNF]
      exact List.mem_cons_self _ _
    derives_false := by
      -- leaf derives its clause.
      simpa using (ResoplusDerivesFromTree.leaf (c:=falseClause F))
  }

/-!
Tiny hand-encoded CNF with two clauses that refute to false by XOR.
We use: phi = [c0, c1] where c0 has rhs=false, c1 has rhs=true with no vars.
Then xorClause c0 c1 is falseClause.
-/
def tinyCNF2 (F : CNF) : CNFFormula F :=
  [{ vars := [], rhs := false }, { vars := [], rhs := true }]

def tinyCNF2_refutation (F : CNF) : ResoplusRefutation F (tinyCNF2 F) :=
  let c0 : ParityClause F := ParityClause.mk (F:=F) [] false
  let c1 : ParityClause F := ParityClause.mk (F:=F) [] true
  { tree := ResoplusDerivTree.xor c0 c1
      (ResoplusDerivTree.leaf c0)
      (ResoplusDerivTree.leaf c1)
    leaves_in := by
      -- both leaves are members of the CNF
      constructor
      · exact List.mem_cons_self _ _
      · exact List.mem_cons_of_mem _ (List.mem_cons_self _ _)
    derives_false := by
      -- xor of false/true yields falseClause
      have h1 : ResoplusDerivesFromTree (ResoplusDerivTree.leaf c0) c0 :=
        ResoplusDerivesFromTree.leaf
      have h2 : ResoplusDerivesFromTree (ResoplusDerivTree.leaf c1) c1 :=
        ResoplusDerivesFromTree.leaf
      have hx : ResoplusDerivesFromTree
          (ResoplusDerivTree.xor c0 c1 (ResoplusDerivTree.leaf c0) (ResoplusDerivTree.leaf c1))
          (xorClause c0 c1) :=
        ResoplusDerivesFromTree.xor_root h1 h2
      -- xor of empty-parity clauses is falseClause
      have hxf : xorClause c0 c1 = falseClause F := by
        simp [xorClause, falseClause]
      simpa [hxf] using hx
  }

def extractPDT {F : CNF} : ResoplusDerivTree F -> PDT F (ParityClause F)
  | ResoplusDerivTree.leaf c => PDT.leaf c
  | ResoplusDerivTree.xor c1 _ t1 t2 => PDT.query c1 (extractPDT t1) (extractPDT t2)

theorem extractPDT_size_bound {F : CNF} (t : ResoplusDerivTree F) :
  PDTsize (extractPDT t) <= ResoplusDerivTree.size t := by
  induction t with
  | leaf _c =>
      simp [extractPDT, PDTsize, ResoplusDerivTree.size]
  | xor c1 c2 t1 t2 ih1 ih2 =>
      have hsum : PDTsize (extractPDT t1) + PDTsize (extractPDT t2) <=
          ResoplusDerivTree.size t1 + ResoplusDerivTree.size t2 :=
        Nat.add_le_add ih1 ih2
      -- close by rewriting the goal via simp
      simpa [extractPDT, PDTsize, ResoplusDerivTree.size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-!
Non-vacuous Res(oplus)->PDT size transfer from a concrete derivation tree.
This removes the generic compatibility assumption by using the extracted PDT.
-/
theorem resoplus_to_pdt_size_transfer_tree
    {F : CNF} (SR : SearchRel F (ParityClause F)) (t : ResoplusDerivTree F) :
    Exists fun (pi : ResoplusProof F (ParityClause F) SR) =>
      Exists fun (T : PDT F (ParityClause F)) =>
        PDTsize T <= ResoplusSize (SR:=SR) pi := by
  refine Exists.intro (ResoplusProof.ofTree SR t) ?_
  refine Exists.intro (extractPDT t) ?_
  -- `ResoplusProof.ofTree` stores the tree size by definition.
  simpa [ResoplusSize, ResoplusProof.ofTree] using (extractPDT_size_bound t)

theorem size_measure_compatible_left_of_tree
    {F : CNF} (SR : SearchRel F (ParityClause F)) (t : ResoplusDerivTree F) :
    Exists fun (pi : ResoplusProof F (ParityClause F) SR) =>
      Exists fun (T : PDT F (ParityClause F)) =>
        PDTsize T <= ResoplusSize (SR:=SR) pi := by
  exact resoplus_to_pdt_size_transfer_tree SR t

/-- PDT soundness, phrased via evaluation. -/
def PDTSoundFor (F : CNF) (SR : SearchRel F W) (_t : PDT F W) : Prop :=
  Exists fun a => Exists fun w => SR.holds a w

def PDTSound (F : CNF) (SR : SearchRel F W) : Prop :=
  Exists fun t => PDTSoundFor (F:=F) (SR:=SR) t

theorem pdt_sound_for_of_all_leaves {F : CNF} {SR : SearchRel F W} (t : PDT F W)
    (h : PDT.AllLeaves t (fun w => Exists fun a => SR.holds a w)) :
    PDTSoundFor (F:=F) (SR:=SR) t := by
  induction t with
  | leaf w =>
      rcases h with ⟨a, ha⟩
      refine Exists.intro a ?_
      refine Exists.intro w ?_
      exact ha
  | query c tT tF ihT _ihF =>
      rcases h with ⟨hT, _hF⟩
      -- existence of a witness is enough; pick the left branch witness
      exact ihT hT

def SearchTotal (F : CNF) (SR : SearchRel F W) : Prop :=
  Exists fun a => Exists fun w => SR.holds a w

theorem cnfSearchRel_total_of_sat_nonempty {F : CNF} {phi : CNFFormula F}
    {a : Assignment F} (hsat : CNFSat a phi) (hne : phi ≠ []) :
    SearchTotal F (cnfSearchRel phi) := by
  rcases List.exists_mem_of_ne_nil (l:=phi) hne with ⟨c, hc⟩
  refine Exists.intro a ?_
  refine Exists.intro c ?_
  exact cnfSearchRel_holds_of_mem (F:=F) (phi:=phi) (a:=a) (c:=c) hsat hc

theorem resoplus_sound_trivial {F : CNF} {W : Type} (SR : SearchRel F W) :
    ResoplusSound F SR := by
  refine Exists.intro (ResoplusProof.ofTree SR (ResoplusDerivTree.leaf (falseClause F))) ?_
  refine Exists.intro (trueClause F) ?_
  intro _hder
  refine Exists.intro (fun _ => false) ?_
  exact clauseSat_trueClause (a := fun _ => false)

theorem pdt_sound_of_search_total {F : CNF} {W : Type} {SR : SearchRel F W}
    (htotal : SearchTotal F SR) :
    PDTSound F SR := by
  rcases htotal with ⟨a, w, hw⟩
  refine Exists.intro (PDT.leaf w) ?_
  refine Exists.intro a ?_
  exact Exists.intro w hw

def SizeMeasureCompatibleLeft {F : CNF} {W : Type} (SR : SearchRel F W) : Prop :=
  Exists fun (pi : ResoplusProof F W SR) =>
    Exists fun (t : PDT F W) =>
      PDTsize t <= ResoplusSize (SR:=SR) pi

/--
Weaker constructive transfer payload: enough to certify the existential
`SizeMeasureCompatibleLeft` boundary, without claiming a uniform proof-to-PDT
map for every proof.
-/
structure ExistentialSimulation {F : CNF} {W : Type} (SR : SearchRel F W) where
  proof_witness : ResoplusProof F W SR
  pdt_witness : PDT F W
  size_bound : PDTsize pdt_witness <= ResoplusSize (SR:=SR) proof_witness

structure Simulation {F : CNF} {W : Type} (SR : SearchRel F W) where
  proof_witness : ResoplusProof F W SR
  toPDT : ResoplusProof F W SR -> PDT F W
  size_bound : forall pi, PDTsize (toPDT pi) <= ResoplusSize (SR:=SR) pi

def zero_size_proof {F : CNF} {W : Type} (SR : SearchRel F W) :
    ResoplusProof F W SR :=
  { size := 0
    tree := ResoplusDerivTree.leaf (falseClause F) }

theorem simulation_impossible {F : CNF} {W : Type} {SR : SearchRel F W}
    (sim : Simulation (F:=F) (W:=W) SR) : False := by
  let pi := zero_size_proof (F:=F) (W:=W) SR
  have hsize : PDTsize (sim.toPDT pi) <= 0 := by
    simpa [pi, zero_size_proof, ResoplusSize] using sim.size_bound pi
  have hpos : 1 <= PDTsize (sim.toPDT pi) :=
    pdtsize_pos (sim.toPDT pi)
  exact Nat.not_succ_le_zero 0 (le_trans hpos hsize)

theorem no_simulation {F : CNF} {W : Type} (SR : SearchRel F W) :
    IsEmpty (Simulation (F:=F) (W:=W) SR) := by
  refine ⟨?_⟩
  intro sim
  exact simulation_impossible sim

/--
Honest proof domain for the current lightweight model: the stored size agrees
with the size of the derivation tree.
-/
structure TreeSizedProof {F : CNF} {W : Type} (SR : SearchRel F W) where
  proof : ResoplusProof F W SR
  size_eq_tree :
    ResoplusProof.size_eq_tree (F:=F) (W:=W) (SR:=SR) proof

def TreeSizedProof.ofTree {F : CNF} {W : Type} (SR : SearchRel F W)
    (t : ResoplusDerivTree F) : TreeSizedProof (F:=F) (W:=W) SR :=
  { proof := ResoplusProof.ofTree SR t
    size_eq_tree := ResoplusProof.size_eq_tree_ofTree
      (F:=F) (W:=W) (SR:=SR) t }

theorem tree_sized_proof_pos {F : CNF} {W : Type} {SR : SearchRel F W}
    (pi : TreeSizedProof (F:=F) (W:=W) SR) :
    1 <= ResoplusSize (SR:=SR) pi.proof := by
  cases pi with
  | mk proof h =>
      cases proof with
      | mk size tree =>
          dsimp [ResoplusProof.size_eq_tree] at h
          dsimp [ResoplusSize]
          rw [h]
          cases tree with
          | leaf _ =>
              simp [ResoplusDerivTree.size]
          | xor _ _ t1 t2 =>
              simpa [ResoplusDerivTree.size, Nat.add_assoc] using
                (Nat.succ_le_succ (Nat.zero_le (ResoplusDerivTree.size t1 + ResoplusDerivTree.size t2)))

/--
Broader honest proof domain: the stored proof size only needs to dominate the
size of the derivation tree.
-/
structure TreeBoundedProof {F : CNF} {W : Type} (SR : SearchRel F W) where
  proof : ResoplusProof F W SR
  tree_size_le : ResoplusDerivTree.size proof.tree <= ResoplusSize (SR:=SR) proof

def TreeSizedProof.toTreeBoundedProof {F : CNF} {W : Type} {SR : SearchRel F W}
    (pi : TreeSizedProof (F:=F) (W:=W) SR) :
    TreeBoundedProof (F:=F) (W:=W) SR :=
  { proof := pi.proof
    tree_size_le := resoplus_tree_size_le pi.proof pi.size_eq_tree }

def TreeBoundedProof.ofTree {F : CNF} {W : Type} (SR : SearchRel F W)
    (t : ResoplusDerivTree F) : TreeBoundedProof (F:=F) (W:=W) SR :=
  (TreeSizedProof.ofTree SR t).toTreeBoundedProof

theorem tree_bounded_proof_pos {F : CNF} {W : Type} {SR : SearchRel F W}
    (pi : TreeBoundedProof (F:=F) (W:=W) SR) :
    1 <= ResoplusSize (SR:=SR) pi.proof := by
  have htree : 1 <= ResoplusDerivTree.size pi.proof.tree := by
    cases pi.proof.tree with
    | leaf _ =>
        simp [ResoplusDerivTree.size]
    | xor _ _ t1 t2 =>
        simpa [ResoplusDerivTree.size, Nat.add_assoc] using
          (Nat.succ_le_succ (Nat.zero_le (ResoplusDerivTree.size t1 + ResoplusDerivTree.size t2)))
  exact le_trans htree pi.tree_size_le

/--
Uniform simulation over the strengthened proof domain where proof sizes are
honest by construction.
-/
structure SimulationOnTreeSizedDomain {F : CNF}
    (SR : SearchRel F (ParityClause F)) where
  toPDT :
    TreeSizedProof (F:=F) (W:=ParityClause F) SR ->
      PDT F (ParityClause F)
  size_bound : forall pi,
    PDTsize (toPDT pi) <= ResoplusSize (SR:=SR) pi.proof

 /-
def SimulationOnTreeSizedDomain.toSimulationOnTreeSizedProofs
    {F : CNF} {SR : SearchRel F (ParityClause F)}
    (sim : SimulationOnTreeSizedDomain (F:=F) SR) :
    SimulationOnTreeSizedProofs (F:=F) SR :=
  { proof_witness := (TreeSizedProof.ofTree SR (ResoplusDerivTree.leaf (falseClause F))).proof
    proof_witness_size_eq_tree :=
      (TreeSizedProof.ofTree SR (ResoplusDerivTree.leaf (falseClause F))).size_eq_tree
    toPDT := fun pi hpi => sim.toPDT ⟨pi, hpi⟩
    size_bound := by
      intro pi hpi
      exact sim.size_bound ⟨pi, hpi⟩ }

theorem size_measure_compatible_left_of_simulation_on_tree_sized_domain
    {F : CNF} {SR : SearchRel F (ParityClause F)} :
    SimulationOnTreeSizedDomain (F:=F) SR ->
    SizeMeasureCompatibleLeft (F:=F) (W:=ParityClause F) SR := by
  intro sim
  exact size_measure_compatible_left_of_simulation_on_tree_sized_proofs
    sim.toSimulationOnTreeSizedProofs

-/
def simulation_on_tree_sized_domain {F : CNF}
    (SR : SearchRel F (ParityClause F)) :
    SimulationOnTreeSizedDomain (F:=F) SR :=
  { toPDT := fun pi => extractPDT pi.proof.tree
    size_bound := by
      intro pi
      exact Nat.le_trans (extractPDT_size_bound pi.proof.tree)
        (resoplus_tree_size_le pi.proof pi.size_eq_tree) }

/--
Uniform simulation over the wider proof domain where the stored size only needs
to upper-bound the derivation-tree size.
-/
structure SimulationOnTreeBoundedDomain {F : CNF}
    (SR : SearchRel F (ParityClause F)) where
  toPDT :
    TreeBoundedProof (F:=F) (W:=ParityClause F) SR ->
      PDT F (ParityClause F)
  size_bound : forall pi,
    PDTsize (toPDT pi) <= ResoplusSize (SR:=SR) pi.proof

def simulation_on_tree_bounded_domain {F : CNF}
    (SR : SearchRel F (ParityClause F)) :
    SimulationOnTreeBoundedDomain (F:=F) SR :=
  { toPDT := fun pi => extractPDT pi.proof.tree
    size_bound := by
      intro pi
      exact Nat.le_trans (extractPDT_size_bound pi.proof.tree) pi.tree_size_le }

theorem size_measure_compatible_left_of_simulation_on_tree_bounded_domain
    {F : CNF} {SR : SearchRel F (ParityClause F)} :
    SimulationOnTreeBoundedDomain (F:=F) SR ->
    SizeMeasureCompatibleLeft (F:=F) (W:=ParityClause F) SR := by
  intro sim
  let pi : TreeBoundedProof (F:=F) (W:=ParityClause F) SR :=
    TreeBoundedProof.ofTree SR (ResoplusDerivTree.leaf (falseClause F))
  refine Exists.intro pi.proof ?_
  refine Exists.intro (sim.toPDT pi) ?_
  exact sim.size_bound pi

/--
Proof domain carrying exactly the extraction-side bound needed by the transfer
theorem, without mentioning tree-size equality or tree-size domination
explicitly.
-/
structure ExtractBoundedProof {F : CNF} {W : Type} (SR : SearchRel F W) where
  proof : ResoplusProof F W SR
  extract_bound :
    PDTsize (extractPDT proof.tree) <= ResoplusSize (SR:=SR) proof

def TreeBoundedProof.toExtractBoundedProof {F : CNF} {W : Type} {SR : SearchRel F W}
    (pi : TreeBoundedProof (F:=F) (W:=W) SR) :
    ExtractBoundedProof (F:=F) (W:=W) SR :=
  { proof := pi.proof
    extract_bound := Nat.le_trans (extractPDT_size_bound pi.proof.tree) pi.tree_size_le }

def ExtractBoundedProof.ofTree {F : CNF} {W : Type} (SR : SearchRel F W)
    (t : ResoplusDerivTree F) : ExtractBoundedProof (F:=F) (W:=W) SR :=
  (TreeBoundedProof.ofTree SR t).toExtractBoundedProof

def CanonicalResoplusProof.toExtractBoundedProof
    {F : CNF} {W : Type} {SR : SearchRel F W}
    (pi : CanonicalResoplusProof F W SR) :
    ExtractBoundedProof (F:=F) (W:=W) SR :=
  ExtractBoundedProof.ofTree SR pi.tree

/--
Uniform simulation over the proof domain defined by the direct extraction-size
bound.
-/
structure SimulationOnExtractBoundedDomain {F : CNF}
    (SR : SearchRel F (ParityClause F)) where
  toPDT :
    ExtractBoundedProof (F:=F) (W:=ParityClause F) SR ->
      PDT F (ParityClause F)
  size_bound : forall pi,
    PDTsize (toPDT pi) <= ResoplusSize (SR:=SR) pi.proof

def simulation_on_extract_bounded_domain {F : CNF}
    (SR : SearchRel F (ParityClause F)) :
    SimulationOnExtractBoundedDomain (F:=F) SR :=
  { toPDT := fun pi => extractPDT pi.proof.tree
    size_bound := by
      intro pi
      exact pi.extract_bound }

theorem size_measure_compatible_left_of_simulation_on_extract_bounded_domain
    {F : CNF} {SR : SearchRel F (ParityClause F)} :
    SimulationOnExtractBoundedDomain (F:=F) SR ->
    SizeMeasureCompatibleLeft (F:=F) (W:=ParityClause F) SR := by
  intro sim
  let pi : ExtractBoundedProof (F:=F) (W:=ParityClause F) SR :=
    ExtractBoundedProof.ofTree SR (ResoplusDerivTree.leaf (falseClause F))
  refine Exists.intro pi.proof ?_
  refine Exists.intro (sim.toPDT pi) ?_
  exact sim.size_bound pi

/--
Uniform simulation over the canonical proof model with no independent stored
size field.
-/
structure CanonicalSimulation {F : CNF}
    (SR : SearchRel F (ParityClause F)) where
  toPDT :
    CanonicalResoplusProof F (ParityClause F) SR ->
      PDT F (ParityClause F)
  size_bound : forall pi,
    PDTsize (toPDT pi) <= CanonicalResoplusSize pi

def canonical_simulation {F : CNF}
    (SR : SearchRel F (ParityClause F)) :
    CanonicalSimulation (F:=F) SR :=
  { toPDT := fun pi => extractPDT pi.tree
    size_bound := by
      intro pi
      simpa [CanonicalResoplusSize] using (extractPDT_size_bound pi.tree) }

theorem size_measure_compatible_left_of_canonical_simulation
    {F : CNF} {SR : SearchRel F (ParityClause F)} :
    CanonicalSimulation (F:=F) SR ->
    SizeMeasureCompatibleLeft (F:=F) (W:=ParityClause F) SR := by
  intro sim
  let pi : CanonicalResoplusProof F (ParityClause F) SR :=
    { tree := ResoplusDerivTree.leaf (falseClause F) }
  refine Exists.intro pi.toProof ?_
  refine Exists.intro (sim.toPDT pi) ?_
  simpa [CanonicalResoplusProof.toProof, ResoplusSize, CanonicalResoplusSize] using
    sim.size_bound pi

/--
Uniform simulation over the honest proof subdomain: proofs whose stored size
matches the size of their derivation tree. This is the strongest current
uniform boundary that is compatible with the lightweight placeholder proof
model.
-/
structure SimulationOnTreeSizedProofs {F : CNF}
    (SR : SearchRel F (ParityClause F)) where
  proof_witness : ResoplusProof F (ParityClause F) SR
  proof_witness_size_eq_tree :
    ResoplusProof.size_eq_tree (F:=F) (W:=ParityClause F) (SR:=SR) proof_witness
  toPDT : (pi : ResoplusProof F (ParityClause F) SR) ->
    ResoplusProof.size_eq_tree (F:=F) (W:=ParityClause F) (SR:=SR) pi ->
      PDT F (ParityClause F)
  size_bound : forall pi hpi,
    PDTsize (toPDT pi hpi) <= ResoplusSize (SR:=SR) pi

theorem size_measure_compatible_left_of_simulation_on_tree_sized_proofs
    {F : CNF} {SR : SearchRel F (ParityClause F)} :
    SimulationOnTreeSizedProofs (F:=F) SR ->
    SizeMeasureCompatibleLeft (F:=F) (W:=ParityClause F) SR := by
  intro sim
  refine Exists.intro sim.proof_witness ?_
  refine Exists.intro (sim.toPDT sim.proof_witness sim.proof_witness_size_eq_tree) ?_
  exact sim.size_bound sim.proof_witness sim.proof_witness_size_eq_tree

def simulation_on_tree_sized_proofs {F : CNF}
    (SR : SearchRel F (ParityClause F)) :
    SimulationOnTreeSizedProofs (F:=F) SR :=
  { proof_witness := ResoplusProof.ofTree SR (ResoplusDerivTree.leaf (falseClause F))
    proof_witness_size_eq_tree := ResoplusProof.size_eq_tree_ofTree
        (F:=F) (W:=ParityClause F) (SR:=SR) (ResoplusDerivTree.leaf (falseClause F))
    toPDT := fun pi _ => extractPDT pi.tree
    size_bound := by
      intro pi hpi
      exact Nat.le_trans (extractPDT_size_bound pi.tree) (resoplus_tree_size_le pi hpi) }

def SimulationOnTreeSizedDomain.toSimulationOnTreeSizedProofs
    {F : CNF} {SR : SearchRel F (ParityClause F)}
    (sim : SimulationOnTreeSizedDomain (F:=F) SR) :
    SimulationOnTreeSizedProofs (F:=F) SR :=
  { proof_witness := (TreeSizedProof.ofTree SR (ResoplusDerivTree.leaf (falseClause F))).proof
    proof_witness_size_eq_tree :=
      (TreeSizedProof.ofTree SR (ResoplusDerivTree.leaf (falseClause F))).size_eq_tree
    toPDT := fun pi hpi => sim.toPDT { proof := pi, size_eq_tree := hpi }
    size_bound := by
      intro pi hpi
      exact sim.size_bound { proof := pi, size_eq_tree := hpi } }

theorem size_measure_compatible_left_of_simulation_on_tree_sized_domain
    {F : CNF} {SR : SearchRel F (ParityClause F)} :
    SimulationOnTreeSizedDomain (F:=F) SR ->
    SizeMeasureCompatibleLeft (F:=F) (W:=ParityClause F) SR := by
  intro sim
  exact size_measure_compatible_left_of_simulation_on_tree_sized_proofs
    sim.toSimulationOnTreeSizedProofs

/-!
Named simulation stub: use to explicitly assume a Res(⊕)→PDT size simulation.
Compatibility-only assumption wrapper: prefer a concrete derivation tree or an
explicit `Simulation` in live proof work. This keeps the transfer assumption
localized and avoids global axioms.
-/
structure SimulationStub {F : CNF} {W : Type} (SR : SearchRel F W) : Type where
  witness : ResoplusProof F W SR
  toPDT : ResoplusProof F W SR -> PDT F W
  size_bound : forall pi, PDTsize (toPDT pi) <= ResoplusSize (SR:=SR) pi

/-!
Explicit witness for tree-based Res(oplus)->PDT transfer.
This localizes the remaining assumption to a concrete derivation tree.
-/
structure ResoplusTreeWitness {F : CNF} (SR : SearchRel F (ParityClause F)) : Type where
  tree : ResoplusDerivTree F

def tree_witness_of_refutation {F : CNF} {phi : CNFFormula F}
    (r : ResoplusRefutation F phi) :
    ResoplusTreeWitness (ResoplusPDT.cnfSearchRel (F:=F) phi) :=
  { tree := r.tree }

theorem size_measure_compatible_left_of_existential_simulation
    {F : CNF} {W : Type} {SR : SearchRel F W} :
    ExistentialSimulation (F:=F) (W:=W) SR ->
    SizeMeasureCompatibleLeft (F:=F) (W:=W) SR := by
  intro sim
  refine Exists.intro sim.proof_witness ?_
  refine Exists.intro sim.pdt_witness ?_
  exact sim.size_bound

def existential_simulation_of_tree_witness
    {F : CNF} {SR : SearchRel F (ParityClause F)} :
    ResoplusTreeWitness (F:=F) SR ->
    ExistentialSimulation (F:=F) (W:=ParityClause F) SR
  | w =>
      { proof_witness := ResoplusProof.ofTree SR w.tree
        pdt_witness := extractPDT w.tree
        size_bound := by
          simpa [ResoplusSize, ResoplusProof.ofTree] using (extractPDT_size_bound w.tree) }

def existential_simulation_of_refutation {F : CNF} {phi : CNFFormula F}
    (r : ResoplusRefutation F phi) :
    ExistentialSimulation (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) phi) :=
  existential_simulation_of_tree_witness (tree_witness_of_refutation r)

def tree_sized_simulation_of_refutation {F : CNF} {phi : CNFFormula F}
    (r : ResoplusRefutation F phi) :
    SimulationOnTreeSizedProofs (F:=F)
      (cnfSearchRel (F:=F) phi) :=
  { proof_witness :=
      ResoplusProof.ofTree (cnfSearchRel (F:=F) phi) r.tree
    proof_witness_size_eq_tree :=
      ResoplusProof.size_eq_tree_ofTree
        (F:=F) (W:=ParityClause F) (SR:=cnfSearchRel (F:=F) phi) r.tree
    toPDT := fun pi _ => extractPDT pi.tree
    size_bound := by
      intro pi hpi
      exact Nat.le_trans (extractPDT_size_bound pi.tree) (resoplus_tree_size_le pi hpi) }

def canonical_proof_of_refutation {F : CNF} {phi : CNFFormula F}
    (r : ResoplusRefutation F phi) :
    CanonicalResoplusProof F (ParityClause F) (cnfSearchRel (F:=F) phi) :=
  { tree := r.tree }

def RefutationSize {F : CNF} {phi : CNFFormula F}
    (r : ResoplusRefutation F phi) : Nat :=
  ResoplusDerivTree.size r.tree

def RefutationSizeLowerBoundPremise {F : CNF} (phi : CNFFormula F) (n : Nat) :
    Prop :=
  forall r : ResoplusRefutation F phi, n <= RefutationSize r

theorem le_refutationSize_of_refutationSizeLowerBoundPremise
    {F : CNF} {phi : CNFFormula F} {n : Nat}
    (h : RefutationSizeLowerBoundPremise phi n)
    (r : ResoplusRefutation F phi) :
    n <= RefutationSize r :=
  h r

theorem not_refutationSizeLowerBoundPremise_of_small_refutation
    {F : CNF} {phi : CNFFormula F} {n : Nat}
    (r : ResoplusRefutation F phi) (hsmall : RefutationSize r < n) :
    Not (RefutationSizeLowerBoundPremise phi n) := by
  intro h
  exact (Nat.not_le_of_gt hsmall)
    (le_refutationSize_of_refutationSizeLowerBoundPremise h r)

structure RefutationSizeFamilyTarget where
  Index : Type
  F : Index -> CNF
  phi : (i : Index) -> CNFFormula (F i)
  threshold : Index -> Nat

def RefutationSizeFamilyLowerBoundPremise
    (target : RefutationSizeFamilyTarget) : Prop :=
  forall i : target.Index,
    RefutationSizeLowerBoundPremise (target.phi i) (target.threshold i)

theorem le_refutationSize_of_familyLowerBoundPremise
    (target : RefutationSizeFamilyTarget)
    (h : RefutationSizeFamilyLowerBoundPremise target)
    (i : target.Index)
    (r : ResoplusRefutation (target.F i) (target.phi i)) :
    target.threshold i <= RefutationSize r :=
  h i r

theorem not_refutationSizeFamilyLowerBoundPremise_of_small_refutation
    (target : RefutationSizeFamilyTarget) (i : target.Index)
    (r : ResoplusRefutation (target.F i) (target.phi i))
    (hsmall : RefutationSize r < target.threshold i) :
    Not (RefutationSizeFamilyLowerBoundPremise target) := by
  intro h
  exact (not_refutationSizeLowerBoundPremise_of_small_refutation r hsmall) (h i)

theorem parityClauseFoldRefutation_size
    {F : CNF} (c : ParityClause F) (cs : List (ParityClause F))
    (vs : List (Fin F.vcount))
    (hperm :
      List.Perm (xorClauseFold c cs).vars
        (dupVarClauseList (falseClause F) vs).vars)
    (hrhs : (xorClauseFold c cs).rhs = true) :
    RefutationSize (parityClauseFoldRefutation c cs vs hperm hrhs) =
      2 * cs.length + 1 := by
  simp [RefutationSize, parityClauseFoldRefutation, xorTreeFold_size]

theorem not_refutationSizeLowerBoundPremise_of_xor_fold_size_lt
    {F : CNF} (c : ParityClause F) (cs : List (ParityClause F))
    (vs : List (Fin F.vcount))
    (hperm :
      List.Perm (xorClauseFold c cs).vars
        (dupVarClauseList (falseClause F) vs).vars)
    (hrhs : (xorClauseFold c cs).rhs = true)
    {n : Nat} (hsmall : 2 * cs.length + 1 < n) :
    Not (RefutationSizeLowerBoundPremise (c :: cs) n) := by
  exact not_refutationSizeLowerBoundPremise_of_small_refutation
    (parityClauseFoldRefutation c cs vs hperm hrhs)
    (by simpa [parityClauseFoldRefutation_size] using hsmall)

def RefutedCNFSize {F : CNF} (rf : RefutedCNF F) : Nat :=
  RefutationSize rf.refutation

structure RefutedCNFConsequences {F : CNF} (rf : RefutedCNF F) : Type where
  unsat : CNFUnsat rf.formula
  pdt : PDT F (ParityClause F)
  size_bound : PDTsize pdt <= RefutedCNFSize rf

structure RefutedCNFCanonicalConsequences {F : CNF} (rf : RefutedCNF F) : Type where
  unsat : CNFUnsat rf.formula
  proof : CanonicalResoplusProof F (ParityClause F) (cnfSearchRel (F:=F) rf.formula)
  pdt : PDT F (ParityClause F)
  size_bound : PDTsize pdt <= CanonicalResoplusSize proof

structure RefutedCNFProofConsequences {F : CNF} (rf : RefutedCNF F) : Type where
  unsat : CNFUnsat rf.formula
  proof : ResoplusProof F (ParityClause F) (cnfSearchRel (F:=F) rf.formula)
  pdt : PDT F (ParityClause F)
  size_bound : PDTsize pdt <= ResoplusSize proof

structure RefutedCNFFullConsequences {F : CNF} (rf : RefutedCNF F) : Type where
  unsat : CNFUnsat rf.formula
  canonical_proof :
    CanonicalResoplusProof F (ParityClause F) (cnfSearchRel (F:=F) rf.formula)
  proof : ResoplusProof F (ParityClause F) (cnfSearchRel (F:=F) rf.formula)
  pdt : PDT F (ParityClause F)
  canonical_size_bound : PDTsize pdt <= CanonicalResoplusSize canonical_proof
  proof_size_bound : PDTsize pdt <= ResoplusSize proof

structure RefutedCNFTotalConsequences {F : CNF} (rf : RefutedCNF F) : Type where
  unsat : CNFUnsat rf.formula
  canonical_proof :
    CanonicalResoplusProof F (ParityClause F) (cnfSearchRel (F:=F) rf.formula)
  proof : ResoplusProof F (ParityClause F) (cnfSearchRel (F:=F) rf.formula)
  pdt : PDT F (ParityClause F)
  refutation_size_bound : PDTsize pdt <= RefutedCNFSize rf
  canonical_size_bound : PDTsize pdt <= CanonicalResoplusSize canonical_proof
  proof_size_bound : PDTsize pdt <= ResoplusSize proof

structure RefutedCNFCertificate (F : CNF) : Type where
  formula : CNFFormula F
  refutation : ResoplusRefutation F formula
  unsat : CNFUnsat formula
  canonical_proof :
    CanonicalResoplusProof F (ParityClause F) (cnfSearchRel (F:=F) formula)
  proof : ResoplusProof F (ParityClause F) (cnfSearchRel (F:=F) formula)
  pdt : PDT F (ParityClause F)
  refutation_size_bound : PDTsize pdt <= RefutationSize refutation
  canonical_size_bound : PDTsize pdt <= CanonicalResoplusSize canonical_proof
  proof_size_bound : PDTsize pdt <= ResoplusSize proof

/--
Uniform transfer over concrete refutations, with the size measure taken
directly from the refutation tree.
-/
structure SimulationOnRefutationDomain {F : CNF} (phi : CNFFormula F) where
  toPDT : ResoplusRefutation F phi -> PDT F (ParityClause F)
  size_bound : forall r, PDTsize (toPDT r) <= RefutationSize r

def simulation_on_refutation_domain {F : CNF} (phi : CNFFormula F) :
    SimulationOnRefutationDomain (F:=F) phi :=
  { toPDT := fun r => extractPDT r.tree
    size_bound := by
      intro r
      simpa [RefutationSize] using (extractPDT_size_bound r.tree) }

theorem pdt_size_transfer_of_refutation
    {F : CNF} {phi : CNFFormula F}
    (r : ResoplusRefutation F phi) :
    Exists fun (t : PDT F (ParityClause F)) =>
      PDTsize t <= RefutationSize r := by
  refine Exists.intro ((simulation_on_refutation_domain (F:=F) phi).toPDT r) ?_
  exact (simulation_on_refutation_domain (F:=F) phi).size_bound r

def simulation_on_refuted_cnf_domain {F : CNF} :
    RefutedCNF F -> PDT F (ParityClause F)
  | rf => (simulation_on_refutation_domain (F:=F) rf.formula).toPDT rf.refutation

theorem pdt_size_transfer_of_refuted_cnf
    {F : CNF} (rf : RefutedCNF F) :
    Exists fun (t : PDT F (ParityClause F)) =>
      PDTsize t <= RefutedCNFSize rf := by
  rcases pdt_size_transfer_of_refutation (F:=F) (phi:=rf.formula) rf.refutation with
    ⟨t, hsize⟩
  refine Exists.intro t ?_
  simpa [RefutedCNFSize] using hsize

theorem refuted_cnf_unsat
    {F : CNF} (rf : RefutedCNF F) :
    CNFUnsat rf.formula := by
  exact resoplus_refutation_unsat rf.refutation

theorem refuted_cnf_unsat_and_pdt_transfer
    {F : CNF} (rf : RefutedCNF F) :
    CNFUnsat rf.formula ∧
      Exists fun (t : PDT F (ParityClause F)) =>
        PDTsize t <= RefutedCNFSize rf := by
  refine And.intro ?_ ?_
  exact refuted_cnf_unsat rf
  exact pdt_size_transfer_of_refuted_cnf rf

noncomputable def refuted_cnf_consequences
    {F : CNF} (rf : RefutedCNF F) :
    RefutedCNFConsequences rf := by
  let htransfer := pdt_size_transfer_of_refuted_cnf rf
  let t := Classical.choose htransfer
  let hsize := Classical.choose_spec htransfer
  exact
    { unsat := refuted_cnf_unsat rf
      pdt := t
      size_bound := hsize }

theorem canonical_resoplus_to_pdt_size_transfer_of_refutation
    {F : CNF} {phi : CNFFormula F}
    (r : ResoplusRefutation F phi) :
    Exists fun (pi :
      CanonicalResoplusProof F (ParityClause F) (cnfSearchRel (F:=F) phi)) =>
      Exists fun (t : PDT F (ParityClause F)) =>
        PDTsize t <= CanonicalResoplusSize pi := by
  refine Exists.intro (canonical_proof_of_refutation (F:=F) (phi:=phi) r) ?_
  rcases pdt_size_transfer_of_refutation (F:=F) (phi:=phi) r with ⟨t, hsize⟩
  refine Exists.intro t ?_
  simpa [canonical_proof_of_refutation, CanonicalResoplusSize, RefutationSize] using hsize

theorem resoplus_to_pdt_size_transfer_of_refutation
    {F : CNF} {phi : CNFFormula F}
    (r : ResoplusRefutation F phi) :
    Exists fun (pi : ResoplusProof F (ParityClause F) (cnfSearchRel (F:=F) phi)) =>
      Exists fun (t : PDT F (ParityClause F)) =>
        PDTsize t <= ResoplusSize (SR:=cnfSearchRel (F:=F) phi) pi := by
  rcases canonical_resoplus_to_pdt_size_transfer_of_refutation (F:=F) (phi:=phi) r with
    ⟨pi, t, hsize⟩
  refine Exists.intro pi.toProof ?_
  refine Exists.intro t ?_
  simpa [CanonicalResoplusProof.toProof, ResoplusSize, CanonicalResoplusSize] using hsize

noncomputable def refuted_cnf_canonical_consequences
    {F : CNF} (rf : RefutedCNF F) :
    RefutedCNFCanonicalConsequences rf := by
  let htransfer :=
    canonical_resoplus_to_pdt_size_transfer_of_refutation
      (F:=F) (phi:=rf.formula) rf.refutation
  let pi := Classical.choose htransfer
  let ht := Classical.choose_spec htransfer
  let t := Classical.choose ht
  let hsize := Classical.choose_spec ht
  exact
    { unsat := refuted_cnf_unsat rf
      proof := pi
      pdt := t
      size_bound := hsize }

noncomputable def refuted_cnf_proof_consequences
    {F : CNF} (rf : RefutedCNF F) :
    RefutedCNFProofConsequences rf := by
  let htransfer :=
    resoplus_to_pdt_size_transfer_of_refutation
      (F:=F) (phi:=rf.formula) rf.refutation
  let pi := Classical.choose htransfer
  let ht := Classical.choose_spec htransfer
  let t := Classical.choose ht
  let hsize := Classical.choose_spec ht
  exact
    { unsat := refuted_cnf_unsat rf
      proof := pi
      pdt := t
      size_bound := hsize }

noncomputable def refuted_cnf_full_consequences
    {F : CNF} (rf : RefutedCNF F) :
    RefutedCNFFullConsequences rf := by
  let htransfer :=
    canonical_resoplus_to_pdt_size_transfer_of_refutation
      (F:=F) (phi:=rf.formula) rf.refutation
  let pi := Classical.choose htransfer
  let ht := Classical.choose_spec htransfer
  let t := Classical.choose ht
  let hsize := Classical.choose_spec ht
  exact
    { unsat := refuted_cnf_unsat rf
      canonical_proof := pi
      proof := pi.toProof
      pdt := t
      canonical_size_bound := hsize
      proof_size_bound := by
        simpa [CanonicalResoplusProof.toProof, ResoplusSize, CanonicalResoplusSize] using hsize }

noncomputable def refuted_cnf_total_consequences
    {F : CNF} (rf : RefutedCNF F) :
    RefutedCNFTotalConsequences rf := by
  let htransfer :=
    pdt_size_transfer_of_refutation
      (F:=F) (phi:=rf.formula) rf.refutation
  let t := Classical.choose htransfer
  let hsize := Classical.choose_spec htransfer
  let pi := canonical_proof_of_refutation (F:=F) (phi:=rf.formula) rf.refutation
  exact
    { unsat := refuted_cnf_unsat rf
      canonical_proof := pi
      proof := pi.toProof
      pdt := t
      refutation_size_bound := by
        simpa [RefutedCNFSize, RefutationSize] using hsize
      canonical_size_bound := by
        simpa [pi, canonical_proof_of_refutation, CanonicalResoplusSize, RefutationSize] using hsize
      proof_size_bound := by
        simpa [pi, canonical_proof_of_refutation, CanonicalResoplusProof.toProof,
          ResoplusSize, CanonicalResoplusSize, RefutationSize] using hsize }

noncomputable def refuted_cnf_certificate
    {F : CNF} (rf : RefutedCNF F) :
    RefutedCNFCertificate F := by
  let hc := refuted_cnf_total_consequences rf
  exact
    { formula := rf.formula
      refutation := rf.refutation
      unsat := hc.unsat
      canonical_proof := hc.canonical_proof
      proof := hc.proof
      pdt := hc.pdt
      refutation_size_bound := by
        simpa [RefutedCNFSize] using hc.refutation_size_bound
      canonical_size_bound := hc.canonical_size_bound
      proof_size_bound := hc.proof_size_bound }

theorem certificate_unsat
    {F : CNF} (cert : RefutedCNFCertificate F) :
    CNFUnsat cert.formula := by
  exact cert.unsat

theorem certificate_pdt_transfer
    {F : CNF} (cert : RefutedCNFCertificate F) :
    Exists fun (t : PDT F (ParityClause F)) =>
      PDTsize t <= RefutationSize cert.refutation := by
  refine Exists.intro cert.pdt ?_
  exact cert.refutation_size_bound

theorem certificate_canonical_transfer
    {F : CNF} (cert : RefutedCNFCertificate F) :
    Exists fun (pi :
      CanonicalResoplusProof F (ParityClause F) (cnfSearchRel (F:=F) cert.formula)) =>
      Exists fun (t : PDT F (ParityClause F)) =>
        PDTsize t <= CanonicalResoplusSize pi := by
  refine Exists.intro cert.canonical_proof ?_
  refine Exists.intro cert.pdt ?_
  exact cert.canonical_size_bound

theorem certificate_proof_transfer
    {F : CNF} (cert : RefutedCNFCertificate F) :
    Exists fun (pi :
      ResoplusProof F (ParityClause F) (cnfSearchRel (F:=F) cert.formula)) =>
      Exists fun (t : PDT F (ParityClause F)) =>
        PDTsize t <= ResoplusSize pi := by
  refine Exists.intro cert.proof ?_
  refine Exists.intro cert.pdt ?_
  exact cert.proof_size_bound

theorem certificate_unsat_and_transfer
    {F : CNF} (cert : RefutedCNFCertificate F) :
    CNFUnsat cert.formula ∧
      Exists fun (t : PDT F (ParityClause F)) =>
        PDTsize t <= RefutationSize cert.refutation := by
  exact And.intro (certificate_unsat cert) (certificate_pdt_transfer cert)

def RefutedCNFCertificate.toRefutedCNF
    {F : CNF} (cert : RefutedCNFCertificate F) :
    RefutedCNF F :=
  { formula := cert.formula
    refutation := cert.refutation }

noncomputable def RefutedCNFCertificate.toTotalConsequences
    {F : CNF} (cert : RefutedCNFCertificate F) :
    RefutedCNFTotalConsequences cert.toRefutedCNF :=
  { unsat := cert.unsat
    canonical_proof := cert.canonical_proof
    proof := cert.proof
    pdt := cert.pdt
    refutation_size_bound := by
      simpa [RefutedCNFCertificate.toRefutedCNF, RefutedCNFSize, RefutationSize]
        using cert.refutation_size_bound
    canonical_size_bound := cert.canonical_size_bound
    proof_size_bound := cert.proof_size_bound }

noncomputable def RefutedCNFCertificate.toConsequences
    {F : CNF} (cert : RefutedCNFCertificate F) :
    RefutedCNFConsequences cert.toRefutedCNF :=
  { unsat := cert.unsat
    pdt := cert.pdt
    size_bound := by
      simpa [RefutedCNFCertificate.toRefutedCNF, RefutedCNFSize, RefutationSize]
        using cert.refutation_size_bound }

noncomputable def RefutedCNFCertificate.toExistentialSimulation
    {F : CNF} (cert : RefutedCNFCertificate F) :
    ExistentialSimulation (cnfSearchRel (F:=F) cert.formula) :=
  { proof_witness := cert.proof
    pdt_witness := cert.pdt
    size_bound := cert.proof_size_bound }

theorem certificate_size_measure_compatible_left
    {F : CNF} (cert : RefutedCNFCertificate F) :
    SizeMeasureCompatibleLeft (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) cert.formula) := by
  exact size_measure_compatible_left_of_existential_simulation
    cert.toExistentialSimulation

theorem size_measure_compatible_left_of_tree_witness
    {F : CNF} {SR : SearchRel F (ParityClause F)} :
    ResoplusTreeWitness (F:=F) SR ->
    SizeMeasureCompatibleLeft (F:=F) (W:=ParityClause F) SR := by
  intro w
  exact size_measure_compatible_left_of_existential_simulation
    (existential_simulation_of_tree_witness (F:=F) (SR:=SR) w)

theorem size_measure_compatible_left_of_simulation
    {F : CNF} {W : Type} {SR : SearchRel F W} :
    Simulation (F:=F) (W:=W) SR ->
    SizeMeasureCompatibleLeft (F:=F) (W:=W) SR := by
  intro sim
  refine Exists.intro sim.proof_witness ?_
  refine Exists.intro (sim.toPDT sim.proof_witness) ?_
  exact sim.size_bound sim.proof_witness

theorem size_measure_compatible_left_of_stub
    {F : CNF} {W : Type} {SR : SearchRel F W} :
    SimulationStub (F:=F) (W:=W) SR ->
    SizeMeasureCompatibleLeft (F:=F) (W:=W) SR := by
  -- Compatibility-only wrapper from an assumed simulation stub.
  intro sim
  refine Exists.intro sim.witness ?_
  refine Exists.intro (sim.toPDT sim.witness) ?_
  exact sim.size_bound sim.witness

def SizeMeasureCompatibleRight {F : CNF} {W : Type} (SR : SearchRel F W) : Prop :=
  Exists fun (pi : ResoplusProof F W SR) =>
    Exists fun (t : PDT F W) =>
      ResoplusSize (SR:=SR) pi <= PDTsize t

def SizeMeasureCompatible {F : CNF} {W : Type} (SR : SearchRel F W) : Prop :=
  Or (SizeMeasureCompatibleLeft (F:=F) (W:=W) SR)
     (SizeMeasureCompatibleRight (F:=F) (W:=W) SR)

structure TransferAssumptions {F : CNF} {W : Type} (SR : SearchRel F W) : Prop where
  resoplus_sound : ResoplusSound F SR
  pdt_sound : PDTSound F SR
  search_total : SearchTotal F SR
  size_measure_compatible_left : SizeMeasureCompatibleLeft (F:=F) (W:=W) SR

theorem certificate_transfer_assumptions_of_search_total
    {F : CNF} (cert : RefutedCNFCertificate F)
    (htotal : SearchTotal F (cnfSearchRel (F:=F) cert.formula)) :
    TransferAssumptions (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) cert.formula) := by
  refine
    { resoplus_sound := resoplus_sound_trivial (cnfSearchRel (F:=F) cert.formula)
      pdt_sound := pdt_sound_of_search_total htotal
      search_total := htotal
      size_measure_compatible_left := certificate_size_measure_compatible_left cert }

structure TransferCertifiedCNF (F : CNF) : Type where
  certificate : RefutedCNFCertificate F
  search_total : SearchTotal F (cnfSearchRel (F:=F) certificate.formula)

def TransferCertifiedCNF.toTransferAssumptions
    {F : CNF} (tc : TransferCertifiedCNF F) :
    TransferAssumptions (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) tc.certificate.formula) :=
  certificate_transfer_assumptions_of_search_total tc.certificate tc.search_total

theorem transfer_certified_cnf_unsat
    {F : CNF} (tc : TransferCertifiedCNF F) :
    CNFUnsat tc.certificate.formula := by
  exact tc.certificate.unsat

theorem transfer_certified_cnf_size_transfer
    {F : CNF} (tc : TransferCertifiedCNF F) :
    Exists fun (pi :
      ResoplusProof F (ParityClause F)
        (cnfSearchRel (F:=F) tc.certificate.formula)) =>
      Exists fun (t : PDT F (ParityClause F)) =>
        PDTsize t <= ResoplusSize
          (SR:=cnfSearchRel (F:=F) tc.certificate.formula) pi := by
  exact tc.toTransferAssumptions.size_measure_compatible_left

/-!
Normalization placeholders for the Res(oplus)->PDT transfer.
These capture the interface obligations needed to avoid misuse.
-/
structure TransferNormalization {F : CNF} {W : Type} (SR : SearchRel F W) : Type where
  size_eq_tree_assumed : Prop
  derivation_rules_match_model : Prop
  pdt_extraction_matches_model : Prop

theorem resoplus_to_pdt_size_transfer
  {F : CNF} {W : Type} (SR : SearchRel F W) :
  SizeMeasureCompatibleLeft (F:=F) (W:=W) SR ->
  Exists fun (pi : ResoplusProof F W SR) =>
    Exists fun (T : PDT F W) => PDTsize T <= ResoplusSize (SR:=SR) pi := by
  intro h
  exact h

theorem resoplus_to_pdt_size_transfer_normalized
  {F : CNF} {W : Type} (SR : SearchRel F W) :
  SizeMeasureCompatibleLeft (F:=F) (W:=W) SR ->
  TransferNormalization (F:=F) (W:=W) SR ->
  Exists fun (pi : ResoplusProof F W SR) =>
    Exists fun (T : PDT F W) => PDTsize T <= ResoplusSize (SR:=SR) pi := by
  intro h hn
  have _ := hn.size_eq_tree_assumed
  have _ := hn.derivation_rules_match_model
  have _ := hn.pdt_extraction_matches_model
  exact resoplus_to_pdt_size_transfer (F:=F) (W:=W) SR h

structure NormalizedTransferCertifiedCNF (F : CNF) : Type where
  base : TransferCertifiedCNF F
  normalization : TransferNormalization (F:=F) (W:=ParityClause F)
    (cnfSearchRel (F:=F) base.certificate.formula)

structure TransferCertifiedCNFConsequences {F : CNF}
    (tc : TransferCertifiedCNF F) : Type where
  unsat : CNFUnsat tc.certificate.formula
  proof :
    ResoplusProof F (ParityClause F)
      (cnfSearchRel (F:=F) tc.certificate.formula)
  pdt : PDT F (ParityClause F)
  size_bound : PDTsize pdt <= ResoplusSize proof

theorem normalized_transfer_certified_cnf_unsat
    {F : CNF} (ntc : NormalizedTransferCertifiedCNF F) :
    CNFUnsat ntc.base.certificate.formula := by
  exact ntc.base.certificate.unsat

theorem normalized_transfer_certified_cnf_size_transfer
    {F : CNF} (ntc : NormalizedTransferCertifiedCNF F) :
    Exists fun (pi :
      ResoplusProof F (ParityClause F)
        (cnfSearchRel (F:=F) ntc.base.certificate.formula)) =>
      Exists fun (t : PDT F (ParityClause F)) =>
        PDTsize t <= ResoplusSize
          (SR:=cnfSearchRel (F:=F) ntc.base.certificate.formula) pi := by
  exact resoplus_to_pdt_size_transfer_normalized
    (F:=F) (W:=ParityClause F)
    (cnfSearchRel (F:=F) ntc.base.certificate.formula)
    ntc.base.toTransferAssumptions.size_measure_compatible_left
    ntc.normalization

/-!
Blocker: A real derivation of `SizeMeasureCompatibleLeft` requires a constructive
simulation from a Res(⊕) refutation to a parity decision tree for the search
relation `SR`, together with a size bound. This depends on formalizing:
- Res(⊕) inference rules and soundness for parity clauses.
- A concrete search relation (e.g., canonical search for CNFs).
- The tree-like simulation that maps a refutation to a PDT.
- A size accounting lemma relating proof size to PDT size.
-/

noncomputable def transfer_certified_cnf_consequences
    {F : CNF} (tc : TransferCertifiedCNF F) :
    TransferCertifiedCNFConsequences tc := by
  let htransfer := transfer_certified_cnf_size_transfer tc
  let pi := Classical.choose htransfer
  let ht := Classical.choose_spec htransfer
  let t := Classical.choose ht
  let hsize := Classical.choose_spec ht
  exact
    { unsat := transfer_certified_cnf_unsat tc
      proof := pi
      pdt := t
      size_bound := hsize }

structure NormalizedTransferCertifiedCNFConsequences {F : CNF}
    (ntc : NormalizedTransferCertifiedCNF F) : Type where
  unsat : CNFUnsat ntc.base.certificate.formula
  proof :
    ResoplusProof F (ParityClause F)
      (cnfSearchRel (F:=F) ntc.base.certificate.formula)
  pdt : PDT F (ParityClause F)
  size_bound : PDTsize pdt <= ResoplusSize proof

noncomputable def normalized_transfer_certified_cnf_consequences
    {F : CNF} (ntc : NormalizedTransferCertifiedCNF F) :
    NormalizedTransferCertifiedCNFConsequences ntc := by
  let htransfer := normalized_transfer_certified_cnf_size_transfer ntc
  let pi := Classical.choose htransfer
  let ht := Classical.choose_spec htransfer
  let t := Classical.choose ht
  let hsize := Classical.choose_spec ht
  exact
    { unsat := normalized_transfer_certified_cnf_unsat ntc
      proof := pi
      pdt := t
      size_bound := hsize }

structure TransferCertifiedCNFTotalConsequences {F : CNF}
    (tc : TransferCertifiedCNF F) : Type where
  assumptions :
    TransferAssumptions (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) tc.certificate.formula)
  unsat : CNFUnsat tc.certificate.formula
  proof :
    ResoplusProof F (ParityClause F)
      (cnfSearchRel (F:=F) tc.certificate.formula)
  pdt : PDT F (ParityClause F)
  size_bound : PDTsize pdt <= ResoplusSize proof

noncomputable def transfer_certified_cnf_total_consequences
    {F : CNF} (tc : TransferCertifiedCNF F) :
    TransferCertifiedCNFTotalConsequences tc := by
  let hcons := transfer_certified_cnf_consequences tc
  exact
    { assumptions := tc.toTransferAssumptions
      unsat := hcons.unsat
      proof := hcons.proof
      pdt := hcons.pdt
      size_bound := hcons.size_bound }

structure NormalizedTransferCertifiedCNFTotalConsequences {F : CNF}
    (ntc : NormalizedTransferCertifiedCNF F) : Type where
  assumptions :
    TransferAssumptions (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) ntc.base.certificate.formula)
  normalization :
    TransferNormalization (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) ntc.base.certificate.formula)
  unsat : CNFUnsat ntc.base.certificate.formula
  proof :
    ResoplusProof F (ParityClause F)
      (cnfSearchRel (F:=F) ntc.base.certificate.formula)
  pdt : PDT F (ParityClause F)
  size_bound : PDTsize pdt <= ResoplusSize proof

noncomputable def normalized_transfer_certified_cnf_total_consequences
    {F : CNF} (ntc : NormalizedTransferCertifiedCNF F) :
    NormalizedTransferCertifiedCNFTotalConsequences ntc := by
  let hcons := normalized_transfer_certified_cnf_consequences ntc
  exact
    { assumptions := ntc.base.toTransferAssumptions
      normalization := ntc.normalization
      unsat := hcons.unsat
      proof := hcons.proof
      pdt := hcons.pdt
      size_bound := hcons.size_bound }

structure TransferCertifiedCNFCertificate (F : CNF) : Type where
  certificate : RefutedCNFCertificate F
  search_total : SearchTotal F (cnfSearchRel (F:=F) certificate.formula)
  assumptions :
    TransferAssumptions (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) certificate.formula)
  proof :
    ResoplusProof F (ParityClause F)
      (cnfSearchRel (F:=F) certificate.formula)
  pdt : PDT F (ParityClause F)
  size_bound : PDTsize pdt <= ResoplusSize proof

noncomputable def transfer_certified_cnf_certificate
    {F : CNF} (tc : TransferCertifiedCNF F) :
    TransferCertifiedCNFCertificate F := by
  let htot := transfer_certified_cnf_total_consequences tc
  exact
    { certificate := tc.certificate
      search_total := tc.search_total
      assumptions := htot.assumptions
      proof := htot.proof
      pdt := htot.pdt
      size_bound := htot.size_bound }

structure NormalizedTransferCertifiedCNFCertificate (F : CNF) : Type where
  base : TransferCertifiedCNFCertificate F
  normalization :
    TransferNormalization (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) base.certificate.formula)

noncomputable def normalized_transfer_certified_cnf_certificate
    {F : CNF} (ntc : NormalizedTransferCertifiedCNF F) :
    NormalizedTransferCertifiedCNFCertificate F := by
  let htot := normalized_transfer_certified_cnf_total_consequences ntc
  exact
    { base :=
        { certificate := ntc.base.certificate
          search_total := ntc.base.search_total
          assumptions := htot.assumptions
          proof := htot.proof
          pdt := htot.pdt
          size_bound := htot.size_bound }
      normalization := htot.normalization }

theorem transfer_certified_certificate_unsat
    {F : CNF} (cert : TransferCertifiedCNFCertificate F) :
    CNFUnsat cert.certificate.formula := by
  exact cert.certificate.unsat

theorem transfer_certified_certificate_transfer
    {F : CNF} (cert : TransferCertifiedCNFCertificate F) :
    Exists fun (pi :
      ResoplusProof F (ParityClause F)
        (cnfSearchRel (F:=F) cert.certificate.formula)) =>
      Exists fun (t : PDT F (ParityClause F)) =>
        PDTsize t <= ResoplusSize pi := by
  refine Exists.intro cert.proof ?_
  refine Exists.intro cert.pdt ?_
  exact cert.size_bound

theorem transfer_certified_certificate_unsat_and_transfer
    {F : CNF} (cert : TransferCertifiedCNFCertificate F) :
    CNFUnsat cert.certificate.formula ∧
      Exists fun (pi :
        ResoplusProof F (ParityClause F)
          (cnfSearchRel (F:=F) cert.certificate.formula)) =>
        Exists fun (t : PDT F (ParityClause F)) =>
          PDTsize t <= ResoplusSize pi := by
  exact And.intro
    (transfer_certified_certificate_unsat cert)
    (transfer_certified_certificate_transfer cert)

theorem transfer_certified_certificate_transfer_assumptions
    {F : CNF} (cert : TransferCertifiedCNFCertificate F) :
    TransferAssumptions (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) cert.certificate.formula) := by
  exact cert.assumptions

theorem transfer_certified_certificate_size_measure_compatible_left
    {F : CNF} (cert : TransferCertifiedCNFCertificate F) :
    SizeMeasureCompatibleLeft (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) cert.certificate.formula) := by
  exact cert.assumptions.size_measure_compatible_left

theorem normalized_transfer_certified_certificate_unsat
    {F : CNF} (cert : NormalizedTransferCertifiedCNFCertificate F) :
    CNFUnsat cert.base.certificate.formula := by
  exact cert.base.certificate.unsat

theorem normalized_transfer_certified_certificate_transfer
    {F : CNF} (cert : NormalizedTransferCertifiedCNFCertificate F) :
    Exists fun (pi :
      ResoplusProof F (ParityClause F)
        (cnfSearchRel (F:=F) cert.base.certificate.formula)) =>
      Exists fun (t : PDT F (ParityClause F)) =>
        PDTsize t <= ResoplusSize pi := by
  refine Exists.intro cert.base.proof ?_
  refine Exists.intro cert.base.pdt ?_
  exact cert.base.size_bound

theorem normalized_transfer_certified_certificate_transfer_assumptions
    {F : CNF} (cert : NormalizedTransferCertifiedCNFCertificate F) :
    TransferAssumptions (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) cert.base.certificate.formula) := by
  exact cert.base.assumptions

theorem normalized_transfer_certified_certificate_transfer_normalized
    {F : CNF} (cert : NormalizedTransferCertifiedCNFCertificate F) :
    Exists fun (pi :
      ResoplusProof F (ParityClause F)
        (cnfSearchRel (F:=F) cert.base.certificate.formula)) =>
      Exists fun (t : PDT F (ParityClause F)) =>
        PDTsize t <= ResoplusSize pi := by
  exact resoplus_to_pdt_size_transfer_normalized
    (F:=F) (W:=ParityClause F)
    (cnfSearchRel (F:=F) cert.base.certificate.formula)
    cert.base.assumptions.size_measure_compatible_left
    cert.normalization

def TransferCertifiedCNFCertificate.toTransferCertifiedCNF
    {F : CNF} (cert : TransferCertifiedCNFCertificate F) :
    TransferCertifiedCNF F :=
  { certificate := cert.certificate
    search_total := cert.search_total }

noncomputable def TransferCertifiedCNFCertificate.toConsequences
    {F : CNF} (cert : TransferCertifiedCNFCertificate F) :
    TransferCertifiedCNFConsequences cert.toTransferCertifiedCNF := by
  exact
    { unsat := transfer_certified_certificate_unsat cert
      proof := cert.proof
      pdt := cert.pdt
      size_bound := cert.size_bound }

noncomputable def TransferCertifiedCNFCertificate.toTotalConsequences
    {F : CNF} (cert : TransferCertifiedCNFCertificate F) :
    TransferCertifiedCNFTotalConsequences cert.toTransferCertifiedCNF := by
  exact
    { assumptions := cert.assumptions
      unsat := transfer_certified_certificate_unsat cert
      proof := cert.proof
      pdt := cert.pdt
      size_bound := cert.size_bound }

def NormalizedTransferCertifiedCNFCertificate.toNormalizedTransferCertifiedCNF
    {F : CNF} (cert : NormalizedTransferCertifiedCNFCertificate F) :
    NormalizedTransferCertifiedCNF F :=
  { base := cert.base.toTransferCertifiedCNF
    normalization := cert.normalization }

noncomputable def NormalizedTransferCertifiedCNFCertificate.toConsequences
    {F : CNF} (cert : NormalizedTransferCertifiedCNFCertificate F) :
    NormalizedTransferCertifiedCNFConsequences
      cert.toNormalizedTransferCertifiedCNF := by
  exact
    { unsat := normalized_transfer_certified_certificate_unsat cert
      proof := cert.base.proof
      pdt := cert.base.pdt
      size_bound := cert.base.size_bound }

noncomputable def NormalizedTransferCertifiedCNFCertificate.toTotalConsequences
    {F : CNF} (cert : NormalizedTransferCertifiedCNFCertificate F) :
    NormalizedTransferCertifiedCNFTotalConsequences
      cert.toNormalizedTransferCertifiedCNF := by
  exact
    { assumptions := cert.base.assumptions
      normalization := cert.normalization
      unsat := normalized_transfer_certified_certificate_unsat cert
      proof := cert.base.proof
      pdt := cert.base.pdt
      size_bound := cert.base.size_bound }

structure TransferCertifiedCompatibilityCertificate (F : CNF) : Type where
  certificate : RefutedCNFCertificate F
  search_total : SearchTotal F (cnfSearchRel (F:=F) certificate.formula)
  assumptions :
    TransferAssumptions (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) certificate.formula)

def transfer_certified_compatibility_certificate
    {F : CNF} (cert : TransferCertifiedCNFCertificate F) :
    TransferCertifiedCompatibilityCertificate F :=
  { certificate := cert.certificate
    search_total := cert.search_total
    assumptions := cert.assumptions }

structure NormalizedTransferCertifiedCompatibilityCertificate (F : CNF) : Type where
  base : TransferCertifiedCompatibilityCertificate F
  normalization :
    TransferNormalization (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) base.certificate.formula)

def normalized_transfer_certified_compatibility_certificate
    {F : CNF} (cert : NormalizedTransferCertifiedCNFCertificate F) :
    NormalizedTransferCertifiedCompatibilityCertificate F :=
  { base :=
      { certificate := cert.base.certificate
        search_total := cert.base.search_total
        assumptions := cert.base.assumptions }
    normalization := cert.normalization }

def TransferCertifiedCompatibilityCertificate.toTransferCertifiedCNF
    {F : CNF} (cert : TransferCertifiedCompatibilityCertificate F) :
    TransferCertifiedCNF F :=
  { certificate := cert.certificate
    search_total := cert.search_total }

def NormalizedTransferCertifiedCompatibilityCertificate.toNormalizedTransferCertifiedCNF
    {F : CNF} (cert : NormalizedTransferCertifiedCompatibilityCertificate F) :
    NormalizedTransferCertifiedCNF F :=
  { base := cert.base.toTransferCertifiedCNF
    normalization := cert.normalization }

theorem transfer_certified_compatibility_certificate_unsat
    {F : CNF} (cert : TransferCertifiedCompatibilityCertificate F) :
    CNFUnsat cert.certificate.formula := by
  exact cert.certificate.unsat

theorem transfer_certified_compatibility_certificate_transfer_assumptions
    {F : CNF} (cert : TransferCertifiedCompatibilityCertificate F) :
    TransferAssumptions (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) cert.certificate.formula) := by
  exact cert.assumptions

theorem transfer_certified_compatibility_certificate_size_measure_compatible_left
    {F : CNF} (cert : TransferCertifiedCompatibilityCertificate F) :
    SizeMeasureCompatibleLeft (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) cert.certificate.formula) := by
  exact cert.assumptions.size_measure_compatible_left

theorem normalized_transfer_certified_compatibility_certificate_unsat
    {F : CNF} (cert : NormalizedTransferCertifiedCompatibilityCertificate F) :
    CNFUnsat cert.base.certificate.formula := by
  exact cert.base.certificate.unsat

theorem normalized_transfer_certified_compatibility_certificate_transfer_assumptions
    {F : CNF} (cert : NormalizedTransferCertifiedCompatibilityCertificate F) :
    TransferAssumptions (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) cert.base.certificate.formula) := by
  exact cert.base.assumptions

theorem normalized_transfer_certified_compatibility_certificate_size_measure_compatible_left
    {F : CNF} (cert : NormalizedTransferCertifiedCompatibilityCertificate F) :
    SizeMeasureCompatibleLeft (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) cert.base.certificate.formula) := by
  exact cert.base.assumptions.size_measure_compatible_left

structure TransferCertifiedCompatibilityConsequences {F : CNF}
    (cert : TransferCertifiedCompatibilityCertificate F) : Type where
  unsat : CNFUnsat cert.certificate.formula
  proof :
    ResoplusProof F (ParityClause F)
      (cnfSearchRel (F:=F) cert.certificate.formula)
  pdt : PDT F (ParityClause F)
  size_bound : PDTsize pdt <= ResoplusSize proof

noncomputable def transfer_certified_compatibility_consequences
    {F : CNF} (cert : TransferCertifiedCompatibilityCertificate F) :
    TransferCertifiedCompatibilityConsequences cert := by
  let htransfer := resoplus_to_pdt_size_transfer
    (F:=F) (W:=ParityClause F)
    (cnfSearchRel (F:=F) cert.certificate.formula)
    cert.assumptions.size_measure_compatible_left
  let pi := Classical.choose htransfer
  let ht := Classical.choose_spec htransfer
  let t := Classical.choose ht
  let hsize := Classical.choose_spec ht
  exact
    { unsat := cert.certificate.unsat
      proof := pi
      pdt := t
      size_bound := hsize }

structure NormalizedTransferCertifiedCompatibilityConsequences {F : CNF}
    (cert : NormalizedTransferCertifiedCompatibilityCertificate F) : Type where
  unsat : CNFUnsat cert.base.certificate.formula
  proof :
    ResoplusProof F (ParityClause F)
      (cnfSearchRel (F:=F) cert.base.certificate.formula)
  pdt : PDT F (ParityClause F)
  size_bound : PDTsize pdt <= ResoplusSize proof

noncomputable def normalized_transfer_certified_compatibility_consequences
    {F : CNF} (cert : NormalizedTransferCertifiedCompatibilityCertificate F) :
    NormalizedTransferCertifiedCompatibilityConsequences cert := by
  let htransfer := resoplus_to_pdt_size_transfer_normalized
    (F:=F) (W:=ParityClause F)
    (cnfSearchRel (F:=F) cert.base.certificate.formula)
    cert.base.assumptions.size_measure_compatible_left
    cert.normalization
  let pi := Classical.choose htransfer
  let ht := Classical.choose_spec htransfer
  let t := Classical.choose ht
  let hsize := Classical.choose_spec ht
  exact
    { unsat := cert.base.certificate.unsat
      proof := pi
      pdt := t
      size_bound := hsize }

structure TransferCertifiedCompatibilityTotalConsequences {F : CNF}
    (cert : TransferCertifiedCompatibilityCertificate F) : Type where
  assumptions :
    TransferAssumptions (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) cert.certificate.formula)
  unsat : CNFUnsat cert.certificate.formula
  proof :
    ResoplusProof F (ParityClause F)
      (cnfSearchRel (F:=F) cert.certificate.formula)
  pdt : PDT F (ParityClause F)
  size_bound : PDTsize pdt <= ResoplusSize proof

noncomputable def transfer_certified_compatibility_total_consequences
    {F : CNF} (cert : TransferCertifiedCompatibilityCertificate F) :
    TransferCertifiedCompatibilityTotalConsequences cert := by
  let hcons := transfer_certified_compatibility_consequences cert
  exact
    { assumptions := cert.assumptions
      unsat := hcons.unsat
      proof := hcons.proof
      pdt := hcons.pdt
      size_bound := hcons.size_bound }

structure NormalizedTransferCertifiedCompatibilityTotalConsequences {F : CNF}
    (cert : NormalizedTransferCertifiedCompatibilityCertificate F) : Type where
  assumptions :
    TransferAssumptions (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) cert.base.certificate.formula)
  normalization :
    TransferNormalization (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) cert.base.certificate.formula)
  unsat : CNFUnsat cert.base.certificate.formula
  proof :
    ResoplusProof F (ParityClause F)
      (cnfSearchRel (F:=F) cert.base.certificate.formula)
  pdt : PDT F (ParityClause F)
  size_bound : PDTsize pdt <= ResoplusSize proof

noncomputable def normalized_transfer_certified_compatibility_total_consequences
    {F : CNF} (cert : NormalizedTransferCertifiedCompatibilityCertificate F) :
    NormalizedTransferCertifiedCompatibilityTotalConsequences cert := by
  let hcons := normalized_transfer_certified_compatibility_consequences cert
  exact
    { assumptions := cert.base.assumptions
      normalization := cert.normalization
      unsat := hcons.unsat
      proof := hcons.proof
      pdt := hcons.pdt
      size_bound := hcons.size_bound }

structure TransferCertifiedCompatibilityFullCertificate (F : CNF) : Type where
  base : TransferCertifiedCompatibilityCertificate F
  proof :
    ResoplusProof F (ParityClause F)
      (cnfSearchRel (F:=F) base.certificate.formula)
  pdt : PDT F (ParityClause F)
  size_bound : PDTsize pdt <= ResoplusSize proof

noncomputable def transfer_certified_compatibility_full_certificate
    {F : CNF} (cert : TransferCertifiedCompatibilityCertificate F) :
    TransferCertifiedCompatibilityFullCertificate F := by
  let htot := transfer_certified_compatibility_total_consequences cert
  exact
    { base := cert
      proof := htot.proof
      pdt := htot.pdt
      size_bound := htot.size_bound }

structure NormalizedTransferCertifiedCompatibilityFullCertificate
    (F : CNF) : Type where
  base : TransferCertifiedCompatibilityFullCertificate F
  normalization :
    TransferNormalization (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) base.base.certificate.formula)

noncomputable def normalized_transfer_certified_compatibility_full_certificate
    {F : CNF} (cert : NormalizedTransferCertifiedCompatibilityCertificate F) :
    NormalizedTransferCertifiedCompatibilityFullCertificate F := by
  let htot := normalized_transfer_certified_compatibility_total_consequences cert
  exact
    { base :=
        { base := cert.base
          proof := htot.proof
          pdt := htot.pdt
          size_bound := htot.size_bound }
      normalization := htot.normalization }

theorem transfer_certified_compatibility_full_certificate_unsat
    {F : CNF} (cert : TransferCertifiedCompatibilityFullCertificate F) :
    CNFUnsat cert.base.certificate.formula := by
  exact cert.base.certificate.unsat

theorem transfer_certified_compatibility_full_certificate_transfer
    {F : CNF} (cert : TransferCertifiedCompatibilityFullCertificate F) :
    Exists fun (pi :
      ResoplusProof F (ParityClause F)
        (cnfSearchRel (F:=F) cert.base.certificate.formula)) =>
      Exists fun (t : PDT F (ParityClause F)) =>
        PDTsize t <= ResoplusSize pi := by
  refine Exists.intro cert.proof ?_
  refine Exists.intro cert.pdt ?_
  exact cert.size_bound

theorem transfer_certified_compatibility_full_certificate_unsat_and_transfer
    {F : CNF} (cert : TransferCertifiedCompatibilityFullCertificate F) :
    CNFUnsat cert.base.certificate.formula ∧
      Exists fun (pi :
        ResoplusProof F (ParityClause F)
          (cnfSearchRel (F:=F) cert.base.certificate.formula)) =>
        Exists fun (t : PDT F (ParityClause F)) =>
          PDTsize t <= ResoplusSize pi := by
  exact And.intro
    (transfer_certified_compatibility_full_certificate_unsat cert)
    (transfer_certified_compatibility_full_certificate_transfer cert)

theorem transfer_certified_compatibility_full_certificate_transfer_assumptions
    {F : CNF} (cert : TransferCertifiedCompatibilityFullCertificate F) :
    TransferAssumptions (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) cert.base.certificate.formula) := by
  exact cert.base.assumptions

theorem transfer_certified_compatibility_full_certificate_size_measure_compatible_left
    {F : CNF} (cert : TransferCertifiedCompatibilityFullCertificate F) :
    SizeMeasureCompatibleLeft (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) cert.base.certificate.formula) := by
  exact cert.base.assumptions.size_measure_compatible_left

noncomputable def TransferCertifiedCompatibilityFullCertificate.certifiedDTdepth
    {F : CNF} (cert : TransferCertifiedCompatibilityFullCertificate F) : Nat :=
  PDTsize cert.pdt

theorem TransferCertifiedCompatibilityFullCertificate.certifiedDTdepth_le_resoplusSize
    {F : CNF} (cert : TransferCertifiedCompatibilityFullCertificate F) :
    cert.certifiedDTdepth <= ResoplusSize cert.proof := by
  exact cert.size_bound

theorem normalized_transfer_certified_compatibility_full_certificate_unsat
    {F : CNF} (cert : NormalizedTransferCertifiedCompatibilityFullCertificate F) :
    CNFUnsat cert.base.base.certificate.formula := by
  exact cert.base.base.certificate.unsat

theorem normalized_transfer_certified_compatibility_full_certificate_transfer
    {F : CNF} (cert : NormalizedTransferCertifiedCompatibilityFullCertificate F) :
    Exists fun (pi :
      ResoplusProof F (ParityClause F)
        (cnfSearchRel (F:=F) cert.base.base.certificate.formula)) =>
      Exists fun (t : PDT F (ParityClause F)) =>
        PDTsize t <= ResoplusSize pi := by
  refine Exists.intro cert.base.proof ?_
  refine Exists.intro cert.base.pdt ?_
  exact cert.base.size_bound

theorem normalized_transfer_certified_compatibility_full_certificate_transfer_assumptions
    {F : CNF} (cert : NormalizedTransferCertifiedCompatibilityFullCertificate F) :
    TransferAssumptions (F:=F) (W:=ParityClause F)
      (cnfSearchRel (F:=F) cert.base.base.certificate.formula) := by
  exact cert.base.base.assumptions

theorem normalized_transfer_certified_compatibility_full_certificate_transfer_normalized
    {F : CNF} (cert : NormalizedTransferCertifiedCompatibilityFullCertificate F) :
    Exists fun (pi :
      ResoplusProof F (ParityClause F)
        (cnfSearchRel (F:=F) cert.base.base.certificate.formula)) =>
      Exists fun (t : PDT F (ParityClause F)) =>
        PDTsize t <= ResoplusSize pi := by
  exact resoplus_to_pdt_size_transfer_normalized
    (F:=F) (W:=ParityClause F)
    (cnfSearchRel (F:=F) cert.base.base.certificate.formula)
    cert.base.base.assumptions.size_measure_compatible_left
    cert.normalization

def TransferCertifiedCompatibilityFullCertificate.toTransferCertifiedCompatibilityCertificate
    {F : CNF} (cert : TransferCertifiedCompatibilityFullCertificate F) :
    TransferCertifiedCompatibilityCertificate F :=
  cert.base

noncomputable def TransferCertifiedCompatibilityFullCertificate.toConsequences
    {F : CNF} (cert : TransferCertifiedCompatibilityFullCertificate F) :
    TransferCertifiedCompatibilityConsequences
      cert.toTransferCertifiedCompatibilityCertificate := by
  exact
    { unsat := transfer_certified_compatibility_full_certificate_unsat cert
      proof := cert.proof
      pdt := cert.pdt
      size_bound := cert.size_bound }

noncomputable def TransferCertifiedCompatibilityFullCertificate.toTotalConsequences
    {F : CNF} (cert : TransferCertifiedCompatibilityFullCertificate F) :
    TransferCertifiedCompatibilityTotalConsequences
      cert.toTransferCertifiedCompatibilityCertificate := by
  exact
    { assumptions := cert.base.assumptions
      unsat := transfer_certified_compatibility_full_certificate_unsat cert
      proof := cert.proof
      pdt := cert.pdt
      size_bound := cert.size_bound }

def
    NormalizedTransferCertifiedCompatibilityFullCertificate.toNormalizedTransferCertifiedCompatibilityCertificate
    {F : CNF} (cert : NormalizedTransferCertifiedCompatibilityFullCertificate F) :
    NormalizedTransferCertifiedCompatibilityCertificate F :=
  { base := cert.base.base
    normalization := cert.normalization }

noncomputable def NormalizedTransferCertifiedCompatibilityFullCertificate.toConsequences
    {F : CNF} (cert : NormalizedTransferCertifiedCompatibilityFullCertificate F) :
    NormalizedTransferCertifiedCompatibilityConsequences
      cert.toNormalizedTransferCertifiedCompatibilityCertificate := by
  exact
    { unsat := normalized_transfer_certified_compatibility_full_certificate_unsat cert
      proof := cert.base.proof
      pdt := cert.base.pdt
      size_bound := cert.base.size_bound }

noncomputable def NormalizedTransferCertifiedCompatibilityFullCertificate.toTotalConsequences
    {F : CNF} (cert : NormalizedTransferCertifiedCompatibilityFullCertificate F) :
    NormalizedTransferCertifiedCompatibilityTotalConsequences
      cert.toNormalizedTransferCertifiedCompatibilityCertificate := by
  exact
    { assumptions := cert.base.base.assumptions
      normalization := cert.normalization
      unsat := normalized_transfer_certified_compatibility_full_certificate_unsat cert
      proof := cert.base.proof
      pdt := cert.base.pdt
      size_bound := cert.base.size_bound }

noncomputable def TransferCertifiedCompatibilityFullCertificate.toTransferCertifiedCNFCertificate
    {F : CNF} (cert : TransferCertifiedCompatibilityFullCertificate F) :
    TransferCertifiedCNFCertificate F := by
  exact
    { certificate := cert.base.certificate
      search_total := cert.base.search_total
      assumptions := cert.base.assumptions
      proof := cert.proof
      pdt := cert.pdt
      size_bound := cert.size_bound }

noncomputable def
    NormalizedTransferCertifiedCompatibilityFullCertificate.toNormalizedTransferCertifiedCNFCertificate
    {F : CNF} (cert : NormalizedTransferCertifiedCompatibilityFullCertificate F) :
    NormalizedTransferCertifiedCNFCertificate F := by
  exact
    { base := cert.base.toTransferCertifiedCNFCertificate
      normalization := cert.normalization }

def TransferCertifiedCompatibilityFullCertificate.toTransferCertifiedCNF
    {F : CNF} (cert : TransferCertifiedCompatibilityFullCertificate F) :
    TransferCertifiedCNF F :=
  { certificate := cert.base.certificate
    search_total := cert.base.search_total }

def
    NormalizedTransferCertifiedCompatibilityFullCertificate.toNormalizedTransferCertifiedCNF
    {F : CNF} (cert : NormalizedTransferCertifiedCompatibilityFullCertificate F) :
    NormalizedTransferCertifiedCNF F :=
  { base := cert.base.toTransferCertifiedCNF
    normalization := cert.normalization }

noncomputable def TransferCertifiedCompatibilityCertificate.toTransferCertifiedCNFCertificate
    {F : CNF} (cert : TransferCertifiedCompatibilityCertificate F) :
    TransferCertifiedCNFCertificate F := by
  let htot := transfer_certified_compatibility_total_consequences cert
  exact
    { certificate := cert.certificate
      search_total := cert.search_total
      assumptions := htot.assumptions
      proof := htot.proof
      pdt := htot.pdt
      size_bound := htot.size_bound }

noncomputable def
    NormalizedTransferCertifiedCompatibilityCertificate.toNormalizedTransferCertifiedCNFCertificate
    {F : CNF} (cert : NormalizedTransferCertifiedCompatibilityCertificate F) :
    NormalizedTransferCertifiedCNFCertificate F := by
  let htot := normalized_transfer_certified_compatibility_total_consequences cert
  exact
    { base :=
        { certificate := cert.base.certificate
          search_total := cert.base.search_total
          assumptions := htot.assumptions
          proof := htot.proof
          pdt := htot.pdt
          size_bound := htot.size_bound }
      normalization := htot.normalization }

end ResoplusPDT
end CertifiedAffine

